#!/usr/bin/env python3
"""Exploration: recheck heuristic g estimates at two run lengths (a genuine g is stable)."""
import sys, collections, numpy as np
def run(name, NSYM, n):
    M={}
    for st,part in enumerate(name.split('_')):
        for b in range(NSYM):
            t=part[3*b:3*b+3]; M[(st,b)]=(int(t[0]),1 if t[1]=='R' else -1,'ABC'.index(t[2]))
    tape=collections.defaultdict(int);h=0;s=0;labs=[]
    for _ in range(n):
        b=tape[h];labs.append(f"{'ABC'[s]}{b}");w,d,q=M[(s,b)];tape[h]=w;h+=d;s=q
    return labs
for name,NSYM,B,O in [('1RB1LA_1RC1RB_1LC0LA',2,['A1','B1','C0'],['A0','C1']),
                      ('2RB0LA2LA_1LA1RB2RB',3,['A1','A2','B1'],['B0']),
                      ('1RB1LB_0RC1LB_1LC0LA',2,['A0'],['B1'])]:
    for n in (20000,40000):
        labs=run(name,NSYM,n)
        bo=[k for k,l in enumerate(labs) if l in O]
        pre=[0]
        for l in labs: pre.append(pre[-1]+(l in B))
        ints=[(b+1,pre[b]-pre[a+1]) for a,b in zip(bo,bo[1:])]
        c=collections.Counter(v for e,v in ints if e>n//2); late={v for v,k in c.items() if k>=3}
        g=next((e for e,v in ints if v in late),None)
        print(name,n,'g~',g,'first values',[v for e,v in ints[:14]])
