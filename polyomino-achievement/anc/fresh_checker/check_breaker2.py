import sys
from common import *
sys.setrecursionlimit(100000)
def main(path, relaxed_ok=True):
    nodes={}; hdr={}; shape=None
    for line in open(path):
        t=line.split()
        if not t or t[0]=='#': continue
        k=t[0]
        if k=='board': hdr['W'],hdr['H']=int(t[1]),int(t[2])
        elif k=='shape': shape=parse_shape(t[1:])
        elif k=='kind': hdr['kind']=t[1]
        elif k=='budget': hdr['budget']=int(t[1])
        elif k=='opening': hdr['opening']=[int(x) for x in t[1:]]
        elif k=='root': hdr['root']=int(t[1])
        elif k=='end': hdr['end']=True
        elif k in 'mbPDZ' and len(k)==1:
            i=int(t[1]); assert i not in nodes,'dup id'
            nodes[i]=(k,t[2:])
        else: raise SystemExit('unknown '+line[:30])
    assert hdr['kind']=='breakerwin' and hdr.get('end')
    W,H=hdr['W'],hdr['H']; N=W*H; FULL=(1<<N)-1
    d0=None if hdr['budget']<0 else hdr['budget']
    PL=placements(shape,W,H)
    M=B=0
    for j,c in enumerate(hdr['opening']):
        if j%2==0: M|=1<<c
        else: B|=1<<c
    print(path,'board',W,H,'placements',len(PL),'budget',d0,'nodes',len(nodes),'opening',hdr['opening'])
    pc=lambda x: bin(x).count('1')
    st={'P_strict':0,'P_relaxed':0,'m':0,'b':0,'D':0,'Z':0,'visits':0}
    memo=set()
    def live(M,B): return [p for p in PL if p&B==0]
    def relevant(M,B,d):
        R=0
        for p in PL:
            if p&B==0 and (d is None or pc(p&~M)<=d): R|=p&~M
        return R
    def maker_done(M,B): return any(p&B==0 and p&M==p for p in PL)
    def go(i,M,B,d,maker_turn):
        key=(i,M,B,d,maker_turn)
        if key in memo: return
        st['visits']+=1
        k,a=nodes[i]
        assert not maker_done(M,B),'Maker already has a copy at node %d'%i
        if maker_turn or k in 'PDZ':
            assert (k in 'mPDZ' if maker_turn else k in 'PDZ'),'node %d kind %s at Maker turn'%(i,k)
            R=relevant(M,B,d)
            if k=='Z':
                assert d==0; st['Z']+=1
            elif k=='D':
                assert R==0,'D node %d but relevant cells exist'%i; st['D']+=1
            elif k=='P':
                prs=[int(x) for x in a]; assert len(prs)%2==0
                cells=prs; assert len(set(cells))==len(cells),'pairs not disjoint'
                fr=FULL&~(M|B)
                for c in cells: assert fr>>c&1,'pair cell not free'
                pm=[(1<<prs[j])|(1<<prs[j+1]) for j in range(0,len(prs),2)]
                strict=all(any(p&q==q for q in pm) for p in PL if p&B==0)
                if strict: st['P_strict']+=1
                else:
                    assert relaxed_ok and all(any(p&q==q for q in pm) for p in PL if p&B==0 and (d is None or pc(p&~M)<=d)),'pairing fails at node %d'%i
                    st['P_relaxed']+=1
            else:
                st['m']+=1
                assert d is None or d>=1
                ch={}; passc=None
                passc=None if a[0]=='-' else int(a[0])
                for x in a[1:]:
                    c,n=x.split(':'); c=int(c); assert c not in ch; ch[c]=int(n)
                fr=FULL&~(M|B)
                relcells={c for c in range(N) if R>>c&1}
                for c in ch: assert fr>>c&1,'maker cell not free'
                assert relcells<=set(ch),'uncovered relevant cell at node %d: %s'%(i,sorted(relcells-set(ch)))
                if fr&~R:
                    assert passc is not None and (d is None or d>=1),'irrelevant free cells need pass child, node %d'%i
                    st['pass']=st.get('pass',0)+1
                    go(passc,M,B,None if d is None else d-1,False)
                for c,n in ch.items():
                    M2=M|1<<c
                    assert not maker_done(M2,B),'Maker completes copy'
                    go(n,M2,B,None if d is None else d-1,False)
        else:
            assert k=='b','node %d kind %s at Breaker turn'%(i,k)
            st['b']+=1
            c=int(a[0]); n=int(a[1])
            R=relevant(M,B,d)
            assert FULL&~(M|B)>>c&1 and R>>c&1,'Breaker cell %d not free/relevant at node %d'%(c,i)
            go(n,M,B|1<<c,d,True)
        memo.add(key)
    # root is Maker-turn when opening has even length
    mt=(len(hdr['opening'])%2==0)
    go(hdr['root'],M,B,d0,mt)
    print('RESULT PASS',st)
main(sys.argv[1])
