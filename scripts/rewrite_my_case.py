#!/usr/bin/env python3
"""Rewrite `my_case <ID> (<expr>)` -> `destruct (<expr>) eqn:<ID>` with balanced parens.

Skips occurrences inside Coq comments. Coq comments are nestable `(* ... *)`.
"""
import re
import sys
from pathlib import Path

ID_RE = re.compile(r"my_case\s+([A-Za-z_][A-Za-z_0-9']*)\s*\(")


def strip_in_comment(text):
    """Return list of (i, in_comment) tells whether each position is inside `(* ... *)`."""
    n = len(text)
    in_comment = [False] * n
    depth = 0
    i = 0
    while i < n:
        if not depth and text[i] == '(' and i + 1 < n and text[i+1] == '*':
            depth += 1
            in_comment[i] = True
            in_comment[i+1] = True
            i += 2
            continue
        if depth and text[i] == '(' and i + 1 < n and text[i+1] == '*':
            depth += 1
            in_comment[i] = True
            in_comment[i+1] = True
            i += 2
            continue
        if depth and text[i] == '*' and i + 1 < n and text[i+1] == ')':
            in_comment[i] = True
            in_comment[i+1] = True
            depth -= 1
            i += 2
            continue
        in_comment[i] = depth > 0
        i += 1
    return in_comment


def find_balanced_close(text, open_idx):
    """Given index of `(`, return index of matching `)` or -1."""
    depth = 1
    i = open_idx + 1
    n = len(text)
    while i < n:
        c = text[i]
        if c == '(':
            # could be a comment start; but we'd only get here in non-comment context;
            # however an inner `(*` should still be balanced as a comment.
            if i + 1 < n and text[i+1] == '*':
                # skip to end of comment
                cd = 1
                j = i + 2
                while j < n and cd > 0:
                    if text[j] == '(' and j+1 < n and text[j+1] == '*':
                        cd += 1
                        j += 2
                    elif text[j] == '*' and j+1 < n and text[j+1] == ')':
                        cd -= 1
                        j += 2
                    else:
                        j += 1
                i = j
                continue
            depth += 1
        elif c == ')':
            depth -= 1
            if depth == 0:
                return i
        i += 1
    return -1


def rewrite(text):
    in_comment = strip_in_comment(text)
    out = []
    pos = 0
    count = 0
    while True:
        m = ID_RE.search(text, pos)
        if not m:
            break
        start = m.start()
        if in_comment[start]:
            out.append(text[pos:m.end()])
            pos = m.end()
            continue
        ident = m.group(1)
        open_paren = m.end() - 1  # position of '('
        close_paren = find_balanced_close(text, open_paren)
        if close_paren < 0:
            # malformed; skip
            out.append(text[pos:m.end()])
            pos = m.end()
            continue
        expr = text[open_paren+1:close_paren]
        out.append(text[pos:start])
        out.append(f"destruct ({expr}) eqn:{ident}")
        pos = close_paren + 1
        count += 1
    out.append(text[pos:])
    return ''.join(out), count


def main():
    total = 0
    for path in sys.argv[1:]:
        p = Path(path)
        s = p.read_text()
        new, n = rewrite(s)
        if n > 0:
            p.write_text(new)
            print(f"{path}: {n} rewrites")
            total += n
    print(f"TOTAL: {total}")


if __name__ == '__main__':
    main()
