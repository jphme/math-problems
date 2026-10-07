import sys, gzip
from common import *
sys.setrecursionlimit(10000)
def main(path):
    op = gzip.open if path.endswith('.gz') else open
    W=H=None; shape=None; budget=None; table={}; kind=None; ended=False; opening=None
    with op(path,'rt') as f:
        for line in f:
            t=line.split()
            if not t or t[0]=='#': continue
            if t[0]=='board': W,H=int(t[1]),int(t[2])
            elif t[0]=='shape': shape=parse_shape(t[1:])
            elif t[0]=='kind': kind=t[1]
            elif t[0]=='budget': budget=int(t[1])
            elif t[0]=='opening': opening=t[1:]
            elif t[0]=='end': ended=True
            elif t[0]=='X':
                key=(int(t[1],16),int(t[2],16))
                assert key not in table, 'duplicate position'
                table[key]=int(t[3])
            else: raise SystemExit('unknown line '+line[:40])
    assert ended and kind=='strongwin' and opening==[], (ended,kind,opening)
    P=placements(shape,W,H); N=W*H; FULL=(1<<N)-1
    byc=[[p for p in P if p>>c&1] for c in range(N)]
    print(path,'board',W,H,'placements',len(P),'budget',budget,'table',len(table))
    used=set(); stats={'maxX':0}
    def completes(mask,c): return any(p&mask==p for p in byc[c])
    def check(X,O):
        # X to move; return None if ok else failure string
        key=(X,O)
        if key in used: return None
        if key not in table: return 'missing position X=%x O=%x'%key
        c=table[key]
        if not (0<=c<N) or (X|O)>>c&1: return 'illegal move'
        X2=X|1<<c
        nx=bin(X2).count('1'); stats['maxX']=max(stats['maxX'],nx)
        if nx>budget: return 'budget exceeded'
        if completes(X2,c): used.add(key); return None   # X wins first
        if nx==budget: return 'budget exhausted without copy'
        free=FULL&~(X2|O)
        if not free: return 'draw (board full)'
        f=free
        while f:
            b=f&-f; f^=b; o=b.bit_length()-1
            O2=O|b
            if completes(O2,o): return 'O completes first at %d after X=%x O=%x'%(o,X2,O)
            r=check(X2,O2)
            if r: return r
        used.add(key); return None
    r=check(0,0)
    print('RESULT', 'PASS' if r is None else 'FAIL: '+r, 'positions visited',len(used),'of',len(table),'max X moves',stats['maxX'])
main(sys.argv[1])
