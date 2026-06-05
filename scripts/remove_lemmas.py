#!/usr/bin/env python3
"""Remove dead definition blocks listed in /tmp/removable.json (or arg path).

For each (modpath -> {name: kindword}) locate the top-level command
`Kind name ...` and delete it.  Two block shapes are handled safely:
  * proof block: ends at the first Qed/Defined/Admitted/Abort line.
  * flat command (Definition/Fixpoint/Record/Notation/flat Instance): ends at
    the last non-blank line before the NEXT top-level command (must end in '.').
The forward scan is BOUNDED by the next top-level command, so a flat command
never swallows following lemmas.  Comment regions are tracked so keywords
inside (* ... *) are ignored.

Usage: remove_lemmas.py [removable.json] [--apply]   (default: DRY RUN)
"""
import os, re, sys, json

TERM_RE = re.compile(r"(?<![\w'])(Qed|Defined|Admitted|Abort)\s*\.\s*$")
VERNAC_RE = re.compile(
    r"^\s*(?:Local\s+|Global\s+|#\[[^\]]*\]\s*)*"
    r"(Lemma|Theorem|Definition|Corollary|Fixpoint|CoFixpoint|Instance|Fact|"
    r"Remark|Proposition|Example|Inductive|Record|Variant|Notation|Hint|"
    r"Arguments|Section|End|Module|Context|Ltac|Axiom|Parameter|Class|"
    r"Existing|Canonical|Coercion|Scheme|Goal)\b")

def modpath_to_path(mod):
    if mod.startswith("Utils."):
        return "src/Utils/" + mod[len("Utils."):].replace(".","/") + ".v"
    if mod.startswith("Pyrosome."):
        return "src/Pyrosome/" + mod[len("Pyrosome."):].replace(".","/") + ".v"
    return None

def start_re(name):
    return re.compile(r"^\s*(?:Local\s+|Global\s+|#\[[^\]]*\]\s*)*"
                      r"(Lemma|Theorem|Definition|Corollary|Fixpoint|CoFixpoint|"
                      r"Instance|Fact|Remark|Proposition|Example|Inductive|Record|"
                      r"Variant)\s+"
                      + re.escape(name) + r"(?![\w'])")

def code_only_lines(lines):
    """Return per-line copy with (* ... *) comment spans blanked to spaces
    (nesting + multi-line aware). Lets us detect vernac/terminators on real code."""
    inside = 0
    out = []
    for l in lines:
        chars = list(l)
        i = 0
        while i < len(l):
            two = l[i:i+2]
            if inside == 0 and two == "(*":
                chars[i]=' '; chars[i+1]=' '; inside += 1; i += 2; continue
            if inside > 0 and two == "(*":
                chars[i]=' '; chars[i+1]=' '; inside += 1; i += 2; continue
            if inside > 0 and two == "*)":
                chars[i]=' '; chars[i+1]=' '; inside -= 1; i += 2; continue
            if inside > 0:
                if chars[i] != '\n': chars[i]=' '
                i += 1; continue
            i += 1
        out.append("".join(chars))
    return out

PROOF_START_RE = re.compile(r"^\s*(Proof\b|Next\s+Obligation\b)")

def in_proof_flags(code):
    """Per-line: True if the line sits strictly inside an open Proof...Qed.
    Used to refuse removing defs/instances declared inside a proof body."""
    flags = [False]*len(code)
    inproof = False
    for i,l in enumerate(code):
        if not inproof and PROOF_START_RE.match(l):
            # a single-line `Proof. ... Qed.` opens+closes on same line
            if TERM_RE.search(l):
                continue
            inproof = True
            continue
        if inproof:
            flags[i] = True
            if TERM_RE.search(l):
                inproof = False
    return flags

def find_block(lines, code, start):
    """Given start line index of the command, return (end_inclusive, kind)."""
    n = len(lines)
    for j in range(start+1, n):
        if code[j].strip()=="":
            continue
        if TERM_RE.search(code[j]):
            return j, "proof"
        if VERNAC_RE.match(code[j]):
            k = j-1
            while k > start and code[k].strip()=="":
                k -= 1
            return k, "flat"
    k = n-1
    while k > start and code[k].strip()=="":
        k -= 1
    return k, "flat-eof"

def process(path, names, apply):
    with open(path) as f:
        lines = f.readlines()
    code = code_only_lines(lines)
    inproof = in_proof_flags(code)
    blocks = []
    skipped = []
    used = set()
    # sort names by their start line to make consumption deterministic
    located = []
    for name in names:
        sr = start_re(name)
        found = None
        for i,l in enumerate(code):
            if sr.match(l):
                found = i; break
        if found is None:
            skipped.append((name,"start-not-found")); continue
        if inproof[found]:
            skipped.append((name,f"inside-proof@{found+1}")); continue
        located.append((found,name))
    located.sort()
    for found,name in located:
        if found in used:
            skipped.append((name,"overlaps-earlier-block")); continue
        end, kind = find_block(lines, code, found)
        # sanity: flat block last line should end with '.'
        if kind.startswith("flat"):
            if not code[end].rstrip().endswith("."):
                skipped.append((name,f"flat-block-no-dot-end@{end+1}")); continue
        for k in range(found,end+1): used.add(k)
        blocks.append((found,end,name,kind))
    delete = set()
    for s,e,_,_ in blocks:
        for k in range(s,e+1): delete.add(k)
        if e+1 < len(lines) and lines[e+1].strip()=="":
            delete.add(e+1)
    newlines = [l for i,l in enumerate(lines) if i not in delete]
    if apply and blocks:
        with open(path,"w") as f:
            f.writelines(newlines)
    return blocks, skipped, len(lines)-len(newlines)

def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    apply = "--apply" in sys.argv
    jpath = args[0] if args else "/tmp/removable.json"
    data = json.load(open(jpath))
    tot_blocks = tot_lines = 0
    all_skipped = []
    for mod, names in sorted(data.items()):
        path = modpath_to_path(mod)
        if not path or not os.path.exists(path):
            print(f"!! {mod}: file not found ({path})"); continue
        blocks, skipped, dl = process(path, names, apply)
        tot_blocks += len(blocks); tot_lines += dl
        kinds = {}
        for *_,k in blocks: kinds[k]=kinds.get(k,0)+1
        print(f"{'APPLIED' if apply else 'DRY'} {path}: {len(blocks)}/{len(names)} blocks {dict(kinds)}, {dl} lines")
        for nm,reason in skipped:
            all_skipped.append((mod,nm,reason))
    print(f"\nTOTAL: {tot_blocks} blocks, {tot_lines} lines ({'APPLIED' if apply else 'dry-run'})")
    if all_skipped:
        print(f"\nSKIPPED ({len(all_skipped)}):")
        for mod,nm,reason in all_skipped:
            print(f"   {mod}.{nm}: {reason}")

if __name__ == "__main__":
    main()
