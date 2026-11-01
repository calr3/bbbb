#!/usr/bin/env python3
"""Link every TT / TTT machine in Markdown files to the Turmite Explorer (and every BB-form
machine, with L/R moves, to the fiery.pages.dev Turing machine explorer).

usage: linkify.py FILE.md...      (rewrites the files in place; running it again changes nothing)

A machine is TT notation in backticks, e.g. `1TB0PA_0PC1PC_1PA0PB` or `1TA2PA3PA4PA---;A4`
(moves P/T only, so BB-form machines such as `0RB1LB_1LA1RB` are left alone).  When the toot
transition is given right after it -- `M` (C1), `M` toot C1, `M` (toot C1, ...) -- the link
opens the TTT M;C1.  BB-form machines (L/R moves) link to fiery.pages.dev, without beep/boop
annotations.  Code blocks (fenced or indented) and machines already in a link are skipped.
"""
import re, sys

SITE = 'https://calr3.github.io/bbbb/explore/'
BBSITE = 'https://fiery.pages.dev/turing/explore/'
BBCELL = r'(?:[0-9][LR][A-Z]|---)'
BBMACH = rf'{BBCELL}+(?:_{BBCELL}+)*'
BBPAT = re.compile(rf'(?<!\[)`(?P<m>{BBMACH})`(?!\]\()')
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
        line = PAT.sub(link, line)
        line = BBPAT.sub(lambda mt: mt.group(0) if len(mt.group('m').replace('_', '')) < 6 or
                         not re.search(r'[LR]', mt.group('m'))
                         else f'[`{mt.group("m")}`]({BBSITE}{mt.group("m")})', line)
        out.append(line)
    return '\n'.join(out)


if __name__ == '__main__':
    for path in sys.argv[1:]:
        s = open(path).read()
        t = process(s)
        if t != s:
            open(path, 'w').write(t)
            n = t.count(SITE) + t.count(BBSITE) - s.count(SITE) - s.count(BBSITE)
            print(f'{path}: {n} links added')
