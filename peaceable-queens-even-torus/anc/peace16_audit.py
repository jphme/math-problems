#!/usr/bin/env python3
"""Independent audit for the computer-assisted proof t(16)=32."""
from __future__ import annotations
import csv
import hashlib
import itertools
from collections import Counter
from pathlib import Path

N=16; H=8; TARGET=33
BASE=Path(__file__).resolve().parent


def da_intersection(d0,d1,a0,a1): return 2*(d0*a0+d1*a1)

def profile_ok(p):
    r,c,d0,d1,a0,a1=p; d=d0+d1; a=a0+a1
    if sum(p)>32:return False
    for x,y in [(r,c),(r,d),(r,a),(c,d),(c,a)]:
        if x*y<TARGET:return False
    if da_intersection(d0,d1,a0,a1)<TARGET:return False
    rr=N-r;cc=N-c;dd=N-d;aa=N-a
    for x,y in [(rr,cc),(rr,dd),(rr,aa),(cc,dd),(cc,aa)]:
        if x*y<TARGET:return False
    if 2*((H-d0)*(H-a0)+(H-d1)*(H-a1))<TARGET:return False
    def simple(x,y,z): return N*N-N*(x+y+z)+x*y+x*z+y*z
    if simple(r,c,d)<2*TARGET or simple(r,c,a)<2*TARGET:return False
    I=da_intersection(d0,d1,a0,a1)
    for x in (r,c):
        if N*N-N*(x+d+a)+x*d+x*a+I<2*TARGET:return False
    return True

def transforms(p):
    r,c,d0,d1,a0,a1=p
    return [
        (c,r,d0,d1,a0,a1),
        (r,c,a0,a1,d0,d1),
        (r,c,d1,d0,a1,a0),
    ]

def canon(p):
    seen={p}; todo=[p]
    while todo:
        q=todo.pop()
        for z in transforms(q):
            if z not in seen: seen.add(z);todo.append(z)
    return min(seen)

def audit_profiles():
    ordered=[]
    canonical=set()
    for r in range(17):
      for c in range(17):
       for d0,d1,a0,a1 in itertools.product(range(9),repeat=4):
        p=(r,c,d0,d1,a0,a1)
        if profile_ok(p):
            ordered.append(p);canonical.add(canon(p))
    strata=Counter(map(sum,canonical))
    expected={24:13,25:41,26:101,27:120,28:57,29:10}
    assert len(ordered)==1898, len(ordered)
    assert len(canonical)==342, len(canonical)
    assert dict(sorted(strata.items()))==expected, strata
    return len(ordered),len(canonical),expected


def invariant_subset_counts(mult,shift):
    perm=[(mult*x+shift)%N for x in range(N)]
    seen=[False]*N;lens=[]
    for x in range(N):
        if not seen[x]:
            y=x;l=0
            while not seen[y]:
                seen[y]=True;l+=1;y=perm[y]
            lens.append(l)
    dp=[0]*(N+1);dp[0]=1
    for l in lens:
        for k in range(N,l-1,-1):dp[k]+=dp[k-l]
    return dp

UNITS=(1,3,5,7,9,11,13,15)
FIX={(u,a):invariant_subset_counts(u,a) for u in UNITS for a in range(N)}

def burnside_pair_orbits(r,c,relative_sign):
    eps=(1,-1) if relative_sign else (1,)
    total=0
    for u in UNITS:
      for e in eps:
       v=(e*u)%N
       for a in range(N):
        fr=FIX[u,a][r]
        for b in range(N): total+=fr*FIX[v,b][c]
    order=8*len(eps)*N*N
    if r==c:
        for u in UNITS:
          for e in eps:
           m=(e*u*u)%N
           for a in range(N):
            for b in range(N):
                total+=FIX[m,(u*b+a)%N][r]
        order*=2
    assert total%order==0
    return total//order

EXPECTED_ORBITS={
(5,7,0):24985,(5,7,1):14225,(5,8,0):28365,(5,8,1):16655,
(6,6,0):16496,(6,6,1):10132,(6,7,0):45996,(6,7,1):26876,
(6,8,0):52292,(6,8,1):31484,(7,7,0):32666,(7,7,1):18076,
(7,8,0):73663,(7,8,1):42103,
}

def audit_orbits():
    got={k:burnside_pair_orbits(k[0],k[1],bool(k[2])) for k in EXPECTED_ORBITS}
    assert got==EXPECTED_ORBITS,(got,EXPECTED_ORBITS)
    return got


def homogeneous(R,C,D,A):
    b=w=0
    for r in range(N):
      for c in range(N):
        d=(r-c)%N;a=(r+c)%N
        br=(R>>r)&1;bc=(C>>c)&1;bd=(D>>d)&1;ba=(A>>a)&1
        b+=bool(br and bc and bd and ba)
        w+=bool(not br and not bc and not bd and not ba)
    return b,w

def audit_plaid():
    R=sum(1<<x for x in (5,7,9,11,13,15))
    C=R
    D=sum(1<<x for x in range(0,16,2))
    A=D
    assert homogeneous(R,C,D,A)==(36,32)
    return R,C,D,A


def audit_lifts():
    for d in range(N):
      for a in range(N):
        direct={(r,c) for r in range(N) for c in range(N)
                if (r-c)%N==d and (r+c)%N==a}
        if (d^a)&1:
            calc=set()
        else:
            r0=(((a+d)%N)//2)%H
            c0=(((a-d)%N)//2)%H
            if (r0-c0)%N==d and (r0+c0)%N==a:
                calc={(r0,c0),(r0+H,c0+H)}
            else:
                calc={(r0+H,c0),(r0,c0+H)}
        assert calc==direct,(d,a,calc,direct)


def read_certificate(path):
    with open(path,newline='') as f:
        return list(csv.DictReader((line for line in f if not line.startswith('#')),delimiter='\t'))

def audit_certificates():
    p1=BASE/'peace16_certificate.tsv';p2=BASE/'peace16_certificate_bruteforce.tsv'
    a=read_certificate(p1);b=read_certificate(p2)
    assert len(a)==len(b)==677
    stable=[x for x in a[0] if x!='seconds']
    assert [[r[k] for k in stable] for r in a]==[[r[k] for k in stable] for r in b]
    for rows in (a,b):
        assert {r['result'] for r in rows}=={'UNSAT'}
        assert sum(int(r['A_checked']) for r in rows)==13_163_028_768
        assert sum(int(r['triple_pass']) for r in rows)==17_834
    used={(int(r['r']),int(r['c']),int(r['sign'])):int(r['pair_orbits']) for r in a}
    assert used==EXPECTED_ORBITS
    return len(a),13_163_028_768,17_834

def sha256(path):
    h=hashlib.sha256()
    with open(path,'rb') as f:
        for block in iter(lambda:f.read(1<<20),b''):h.update(block)
    return h.hexdigest()

def main():
    print('profiles',audit_profiles())
    print('orbits',audit_orbits())
    print('plaid_masks',audit_plaid())
    audit_lifts();print('lift_map OK')
    print('certificates',audit_certificates())
    for name in ['peace16_solver.cpp','peace16_solver_bruteforce.cpp','peace16_certificate.tsv','peace16_certificate_bruteforce.tsv']:
        print(sha256(BASE/name),name)
    print('AUDIT_OK')
if __name__=='__main__':main()
