#!/usr/bin/env python3
"""Independent audit for peace16_union_enum.cpp.

The C++ enumerator and this Python audit share only the mathematical
description.  The audit regenerates the profile domain, proves closure under
the quotient symmetries, computes the seven orbit counts by Burnside's lemma,
regenerates the exact pair-transversal hashes, and checks all certificate
arithmetic.
"""
from __future__ import annotations
import argparse
import csv
import hashlib
import itertools
import math
from collections import defaultdict
from pathlib import Path

N=16; H=8; TARGET=33
UNITS=(1,3,5,7,9,11,13,15)
MASK64=(1<<64)-1
FNV_OFFSET=14695981039346656037
FNV_PRIME=1099511628211

def profile_ok(p):
    r,c,d0,d1,a0,a1=p; d=d0+d1; a=a0+a1
    if sum(p)>32:return False
    for x,y in ((r,c),(r,d),(r,a),(c,d),(c,a)):
        if x*y<TARGET:return False
    if 2*(d0*a0+d1*a1)<TARGET:return False
    rr=N-r;cc=N-c;dd=N-d;aa=N-a
    for x,y in ((rr,cc),(rr,dd),(rr,aa),(cc,dd),(cc,aa)):
        if x*y<TARGET:return False
    if 2*((H-d0)*(H-a0)+(H-d1)*(H-a1))<TARGET:return False
    def tri(x,y,z):return N*N-N*(x+y+z)+x*y+x*z+y*z
    if tri(r,c,d)<2*TARGET or tri(r,c,a)<2*TARGET:return False
    da=2*(d0*a0+d1*a1)
    for x in (r,c):
        if N*N-N*(x+d+a)+x*d+x*a+da<2*TARGET:return False
    return True

def profile_domain():
    profiles=set()
    domain=defaultdict(lambda:defaultdict(set))
    for p in itertools.product(range(17),range(17),range(9),range(9),range(9),range(9)):
        if not profile_ok(p):continue
        profiles.add(p)
        r,c,d0,d1,a0,a1=p
        if r>c:r,c=c,r
        domain[(r,c)][(a0,a1)].add((d0,d1))
    assert len(profiles)==1898
    expected={(5,7),(5,8),(6,6),(6,7),(6,8),(7,7),(7,8)}
    assert set(domain)==expected

    # These are exactly the operations that make the union-domain quotient
    # avoid the submitted solver's parity-orientation case distinction.
    for r,c,d0,d1,a0,a1 in profiles:
        assert (c,r,d0,d1,a0,a1) in profiles
        assert (r,c,a0,a1,d0,d1) in profiles
        assert (r,c,d1,d0,a1,a0) in profiles
    return domain

def invariant_counts(mult,shift):
    perm=[(mult*x+shift)%N for x in range(N)]
    seen=[False]*N;lens=[]
    for x in range(N):
        if seen[x]:continue
        y=x;l=0
        while not seen[y]:
            seen[y]=True;l+=1;y=perm[y]
        lens.append(l)
    dp=[0]*(N+1);dp[0]=1
    for l in lens:
        for k in range(N,l-1,-1):dp[k]+=dp[k-l]
    return dp

FIX={(u,a):invariant_counts(u,a) for u in UNITS for a in range(N)}

def burnside(r,c):
    total=0
    for u in UNITS:
      for e in (1,-1):
       v=(e*u)%N
       for a in range(N):
        fr=FIX[(u,a)][r]
        for b in range(N):
            total+=fr*FIX[(v,b)][c]
    order=8*2*N*N
    if r==c:
      for u in UNITS:
       for e in (1,-1):
        m=(e*u*u)%N
        for a in range(N):
         for b in range(N):
            total+=FIX[(m,(u*b+a)%N)][r]
      order*=2
    assert total%order==0
    return total//order

def rot(m,s):
    return m if not s else ((m<<s)|(m>>(16-s)))&0xffff

def mul(m,u):
    out=0
    while m:
        bit=m&-m;x=bit.bit_length()-1
        out|=1<<((u*x)&15);m-=bit
    return out

def mask_tables():
    normal=[min(rot(m,s) for s in range(16)) for m in range(65536)]
    scaled={u:[normal[mul(m,u)] for m in range(65536)] for u in UNITS}
    necklaces={k:[m for m in range(65536) if m.bit_count()==k and normal[m]==m]
               for k in range(5,9)}
    return scaled,necklaces

def canon_pair(R,C,equal,scaled):
    best=(0xffff,0xffff)
    for u in UNITS:
        Ru=scaled[u][R];Cu=scaled[u][C];Cm=scaled[(N-u)&15][C]
        best=min(best,(Ru,Cu),(Ru,Cm))
        if equal:best=min(best,(Cu,Ru),(Cm,Ru))
    return best

def fnv_word(h,x):
    h^=x&255;h=(h*FNV_PRIME)&MASK64
    h^=(x>>8)&255;h=(h*FNV_PRIME)&MASK64
    return h

def transversals(types):
    scaled,necklaces=mask_tables()
    result={}
    for r,c in sorted(types):
        count=0;h=FNV_OFFSET
        for R in necklaces[r]:
         for C in necklaces[c]:
          if canon_pair(R,C,r==c,scaled)==(R,C):
            count+=1;h=fnv_word(h,R);h=fnv_word(h,C)
        result[(r,c)]=(count,f"{h:016x}")
    return result

def read_cert(path):
    with open(path,newline="") as f:
        return list(csv.DictReader((x for x in f if not x.startswith("#")),delimiter="\t"))

def sha256(path):
    h=hashlib.sha256()
    with open(path,"rb") as f:
        for block in iter(lambda:f.read(1<<20),b""):h.update(block)
    return h.hexdigest()

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--certificate",type=Path,default=Path("peace16_union_certificate.tsv"))
    ap.add_argument("--source",type=Path,default=Path("peace16_union_enum.cpp"))
    args=ap.parse_args()

    domain=profile_domain()
    transversal=transversals(domain)
    rows=read_cert(args.certificate)
    assert len(rows)==7
    rows={(int(x["r"]),int(x["c"])):x for x in rows}
    assert set(rows)==set(domain)

    totals=[0]*7 # reps, logical_A, A_tested, scalar, d_cases, logical_D, D_tested
    for key in sorted(domain):
        row=rows[key]
        orbit=burnside(*key)
        count,pair_hash=transversal[key]
        assert orbit==count==int(row["pair_reps"])
        assert pair_hash==row["pair_hash"]

        a_pairs=domain[key]
        masks_per_pair=sum(math.comb(8,a0)*math.comb(8,a1) for a0,a1 in a_pairs)
        logical_A=orbit*masks_per_pair
        assert len(a_pairs)==int(row["A_count_pairs"])
        assert logical_A==int(row["logical_A"])==int(row["A_tested"])
        assert row["result"]=="UNSAT"
        assert int(row["logical_D"])==int(row["D_tested"])

        vals=(orbit,logical_A,int(row["A_tested"]),int(row["scalar_survivors"]),
              int(row["d_count_cases"]),int(row["logical_D"]),int(row["D_tested"]))
        totals=[a+b for a,b in zip(totals,vals)]

    expected=(159_551,3_226_530_570,3_226_530_570,2_951,29_768,38_830_322,38_830_322)
    assert tuple(totals)==expected,totals

    print("UNION_AUDIT_OK")
    print("ordered_profiles=1898")
    print(f"pair_representatives={totals[0]}")
    print(f"A_masks_tested={totals[2]}")
    print(f"scalar_survivors={totals[3]}")
    print(f"diagonal_count_cases={totals[4]}")
    print(f"D_masks_tested={totals[6]}")
    print(f"source_sha256={sha256(args.source)}")
    print(f"certificate_sha256={sha256(args.certificate)}")

if __name__=="__main__":
    main()
