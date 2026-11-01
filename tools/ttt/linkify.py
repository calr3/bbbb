#!/usr/bin/env python3
"""Link every TT / TTT machine in Markdown files to the Turmite Explorer.

usage: linkify.py FILE.md...      (rewrites the files in place; running it again changes nothing)

A machine is TT notation in backticks, e.g. `1TB0PA_0PC1PC_1PA0PB` or `1TA2PA3PA4PA---;A4`
(moves P/T only, so BB-form machines such as `0RB1LB_1LA1RB` are left alone).  When the toot
transition is given right after it -- `M` (C1), `M` toot C1, `M` (toot C1, ...) -- the link
opens the TTT M;C1.  Code blocks (fenced or indented) and machines already in a link are skipped.
"""
import re, sys

SITE = 'https://calr3.github.io/bbbb/explore/'
CELL = r'(?:[0-9][PT][A-Z]|---)'
MACH = rf'{CELL}+(?:_{CELL}+)*'
# `M` or `M;X1`, not already inside [..](..), optionally followed by a toot annotation
PAT = re.compile(
    rf'(?<!\[)`(?P<m>{MACH})(?:;(?P<t0>[A-Z][0-9]))?`(?!\]\()'
    rf'(?P<after>(?:\s*\((?:toot\s+)?(?P<t1>[A-Z][0-9])\b[^)]*\)|\s+toot\s+(?P<t2>[A-Z][0-9])\b)?)')


def link(mt):
    m, toot = mt.group('m'), mt.group('t0') or mt.group('t1') or mt.group('t2')
    # a machine needs more than one transition to be worth linking (avoids e.g. `1PZ`)
    if len(m.replace('_', '')) < 6:
        return mt.group(0)
    url = SITE + m + (';' + toot if toot else '')
    shown = m + (';' + mt.group('t0') if mt.group('t0') else '')
    return f'[`{shown}`]({url}){mt.group("after")}'


def process(text):
    out, fenced = [], False
    for line in text.split('\n'):
        if line.lstrip().startswith('```'):
            fenced = not fenced
            out.append(line); continue
        if fenced or line.startswith('    ') or line.startswith('\t'):
            out.append(line); continue
        out.append(PAT.sub(link, line))
    return '\n'.join(out)


if __name__ == '__main__':
    for path in sys.argv[1:]:
        s = open(path).read()
        t = process(s)
        if t != s:
            open(path, 'w').write(t)
            print(f'{path}: {sum(1 for _ in re.finditer(re.escape(SITE), t)) - s.count(SITE)} links added')
