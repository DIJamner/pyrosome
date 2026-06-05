#!/usr/bin/env python3
"""Glob-based dependency closure analysis.

Finds definitions reachable from a given root (default: egraph_sound in
Pyrosome.Tools.EGraph.Automation), then reports which branch-added
definitions are NOT in that reachable set (= dead relative to the root).
"""
import os, re, sys, subprocess, bisect, collections

ROOT_MOD = "Pyrosome.Tools.EGraph.Automation"
ROOT_NAME = "egraph_sound"
BASE = "new_state_sound"
BRANCH = "long_horizon"

# kinds in glob we treat as graph nodes (things that can be referenced)
DEF_KINDS = {"def","prf","thm","ind","constr","var","ax","inst","prfax",
             "scheme","coe","proj","class","rec","defax","prfdef","meth",
             "exind","exdef","not","abbrev","ind1","field","syndef"}

# kinds that can OWN references (top-level commands); excludes local binders,
# section vars, and sub-objects (constructors/fields/projections/methods)
OWNER_KINDS = {"def","prf","thm","ind","inst","ax","prfax","scheme","coe",
               "class","rec","defax","prfdef","exind","exdef","not","abbrev",
               "ind1","syndef"}

def parse_glob(path):
    """Return (modpath, defs, refs).
    defs: list of (startbyte, name, kind) sorted by startbyte
    refs: list of (startbyte, refmod, refname)
    """
    modpath = None
    defs = []
    refs = []
    with open(path, errors="replace") as f:
        for line in f:
            line = line.rstrip("\n")
            if not line: continue
            if line.startswith("F"):
                modpath = line[1:].strip()
                continue
            parts = line.split(" ")
            tag = parts[0]
            if line[0] == "R" and len(line) > 1 and line[1].isdigit():
                # R<start>:<end> <mod> <secpath> <name> <kind>
                m = re.match(r"R(\d+):(\d+)", line)
                if not m: continue
                start = int(m.group(1))
                # fields after the range
                rest = line[m.end():].strip().split(" ")
                if len(rest) < 4: continue
                refmod = rest[0]
                # secpath rest[1], name rest[2], kind rest[3]
                refname = rest[2]
                if refname == "<>": refname = rest[1]
                refs.append((start, refmod, refname))
            elif tag in DEF_KINDS or re.match(r"^[a-z]+$", tag):
                # <kind> <start>:<end> <secpath> <name>
                m = re.match(r"(\S+) (\d+):(\d+) (\S+) (.+)$", line)
                if not m: continue
                kind = m.group(1)
                start = int(m.group(2))
                name = m.group(5).strip()
                if kind in ("sec",):  # sections aren't nodes but bound owners? skip
                    continue
                defs.append((start, name, kind))
    defs.sort()
    return modpath, defs, refs

def build_graph(globs):
    # node key = (modpath, name)
    node_kind = {}
    file_defs = {}   # modpath -> sorted list of (start, name)
    edges = collections.defaultdict(set)
    raw = {}
    for g in globs:
        modpath, defs, refs = parse_glob(g)
        if modpath is None: continue
        raw[modpath] = (defs, refs)
        owner_defs = [d for d in defs if d[2] in OWNER_KINDS]
        starts = [d[0] for d in owner_defs]
        names  = [(d[1],d[2]) for d in owner_defs]
        file_defs[modpath] = (starts, names)
        for start, name, kind in defs:
            node_kind[(modpath,name)] = kind
    # assign refs to owner def, build edges
    for modpath,(defs,refs) in raw.items():
        starts, names = file_defs[modpath]
        for rpos, refmod, refname in refs:
            i = bisect.bisect_right(starts, rpos) - 1
            if i < 0:
                owner = None
            else:
                owner = (modpath, names[i][0])
            tgt = (refmod, refname)
            if tgt in node_kind and owner is not None and owner != tgt:
                edges[owner].add(tgt)
    return node_kind, edges

def reachable(edges, root):
    seen = set([root])
    stack = [root]
    while stack:
        n = stack.pop()
        for m in edges.get(n, ()):
            if m not in seen:
                seen.add(m); stack.append(m)
    return seen

def reverse_edges(edges):
    rev = collections.defaultdict(set)
    for src, tgts in edges.items():
        for t in tgts:
            rev[t].add(src)
    return rev

def git(*args):
    return subprocess.check_output(["git",*args], text=True)

# map a .v file path to its Coq modpath using _CoqProject logical names
def path_to_modpath(vpath):
    # vpath like src/Pyrosome/Tools/EGraph/Automation.v
    p = vpath
    if p.startswith("src/Utils/"):
        rel = p[len("src/Utils/"):]
        prefix = "Utils"
    elif p.startswith("src/Pyrosome/"):
        rel = p[len("src/Pyrosome/"):]
        prefix = "Pyrosome"
    else:
        return None
    rel = rel[:-2] if rel.endswith(".v") else rel  # strip .v
    return prefix + "." + rel.replace("/",".")

DEF_RE = re.compile(r"^\s*(?:Local\s+|Global\s+|#\[[^\]]*\]\s*)*(Lemma|Theorem|Definition|Corollary|Fixpoint|CoFixpoint|Instance|Fact|Remark|Proposition|Example|Inductive|Record|Variant)\s+([A-Za-z_][A-Za-z0-9_']*)")

LEMMA_KINDS = {"Lemma","Theorem","Corollary","Fact","Remark","Proposition","Example"}

def def_names(content):
    """Return dict name -> kindword for top-level defs in a .v source."""
    out = {}
    for line in content.splitlines():
        m = DEF_RE.match(line)
        if m:
            out[m.group(2)] = m.group(1)
    return out

def changed_v_files():
    out = git("diff","--name-only",f"{BASE}..{BRANCH}","--","src/").split()
    return [p for p in out if p.endswith(".v")]

def branch_added_defs():
    """dict modpath -> dict name->kindword, for defs present on BRANCH but not BASE."""
    added = {}
    for vpath in changed_v_files():
        mod = path_to_modpath(vpath)
        if mod is None: continue
        try:
            branch_c = git("show", f"{BRANCH}:{vpath}")
        except subprocess.CalledProcessError:
            continue
        try:
            base_c = git("show", f"{BASE}:{vpath}")
        except subprocess.CalledProcessError:
            base_c = ""  # new file
        bn = def_names(branch_c)
        on = def_names(base_c)
        new = {n:k for n,k in bn.items() if n not in on}
        if new:
            added[mod] = new
    return added

def main():
    import json
    globs = []
    for base in ("src","coqutil","canonical-binary-tries"):
        for dirp,_,files in os.walk(base):
            for fn in files:
                if fn.endswith(".glob"):
                    globs.append(os.path.join(dirp,fn))
    node_kind, edges = build_graph(globs)
    rev = reverse_edges(edges)
    root = (ROOT_MOD, ROOT_NAME)
    if root not in node_kind:
        print(f"ROOT {root} not found in globs!", file=sys.stderr)
    reach = reachable(edges, root)
    print(f"# total nodes: {len(node_kind)}; reachable from {ROOT_NAME}: {len(reach)}")

    added = branch_added_defs()
    total_added = sum(len(v) for v in added.values())
    print(f"# branch-added defs: {total_added} across {len(added)} files\n")

    # classify
    dead = {}      # (mod,nm)->kindword   (added, not reachable from egraph_sound)
    live = []
    unknown = collections.defaultdict(list)  # added name not a glob node (notation/unbuilt)
    for mod, names in added.items():
        for nm, kw in names.items():
            key = (mod, nm)
            if kw == "Instance":
                # typeclass instances are resolved implicitly (no glob edge) and
                # may be declared inside proofs; never auto-remove them.
                continue
            if key not in node_kind:
                unknown[mod].append((nm,kw))
            elif key in reach:
                live.append(key)
            else:
                dead[key] = kw

    # Safe-removal fixpoint: a dead candidate is removable only if every node
    # that references it is also being removed. Iterate to fixpoint.
    S = set(dead)
    changed = True
    while changed:
        changed = False
        for c in list(S):
            referrers = rev.get(c, ())
            if any(r not in S for r in referrers):
                S.discard(c); changed = True
    blocked = set(dead) - S  # dead but referenced by kept code

    nl = len(live); nd = len(dead); nu = sum(len(v) for v in unknown.values())
    print(f"# LIVE  added defs (used by {ROOT_NAME}):            {nl}")
    print(f"# DEAD  added defs (NOT reachable):                  {nd}")
    print(f"#   -> SAFE to remove (no kept referrers):           {len(S)}")
    print(f"#   -> BLOCKED (referenced by kept code):            {len(blocked)}")
    print(f"# UNKNOWN (added name not a glob node):              {nu}")
    print("#   (unknown = notation/section-local/unbuilt-file; reviewed separately)\n")

    # emit machine-readable removable set
    out = collections.defaultdict(dict)
    for (mod,nm) in S:
        out[mod][nm] = dead[(mod,nm)]
    with open("/tmp/removable.json","w") as f:
        json.dump(out, f, indent=1)

    def show(title, items):
        bymod = collections.defaultdict(list)
        for (mod,nm) in items:
            bymod[mod].append((nm, dead[(mod,nm)]))
        print(f"===== {title} =====")
        for mod in sorted(bymod):
            print(f"\n## {mod}  ({len(bymod[mod])})")
            for nm,kw in sorted(bymod[mod]):
                print(f"   {kw:11} {nm}")
        print()

    show("SAFE TO REMOVE", S)
    show("BLOCKED (dead but referenced by kept code)", blocked)
    print("===== UNKNOWN per file =====")
    for mod in sorted(unknown):
        print(f"\n## {mod}  ({len(unknown[mod])})")
        for nm,kw in sorted(unknown[mod]):
            print(f"   {kw:11} {nm}")

if __name__ == "__main__":
    main()
