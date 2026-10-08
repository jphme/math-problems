def num(x,y):
    d=x+y; return d*(d+1)//2+y
syms=[lambda x,y:(x,y),lambda x,y:(-x,y),lambda x,y:(x,-y),lambda x,y:(-x,-y),lambda x,y:(y,x),lambda x,y:(-y,x),lambda x,y:(y,-x),lambda x,y:(-y,-x)]
def norm(c):
    mx=min(x for x,_ in c);my=min(y for _,y in c); return frozenset((x-mx,y-my) for x,y in c)
polys={1:{norm([(0,0)])}}
for n in range(2,6):
    s=set()
    for p in polys[n-1]:
        for x,y in p:
            for dx,dy in((1,0),(-1,0),(0,1),(0,-1)):
                q=(x+dx,y+dy)
                if q not in p: s.add(norm(list(p)+[q]))
    polys[n]=s
def code(p): return sum(1<<num(x,y) for x,y in p)
def mincode(p): return min(code(norm([s(x,y) for x,y in p])) for s in syms)
seq=[0]
for n in range(1,6): seq+=sorted(set(mincode(p) for p in polys[n]))
print('first terms',seq[:30])
import os
bfile=os.path.join(os.path.dirname(os.path.abspath(__file__)),'..','oeis_data','b246521.txt')
ref=[int(l.split()[1]) for l in open(bfile) if l.strip() and not l.startswith('#')]
print('matches saved A246521 data for',len(seq[:len(ref)]),'terms (sizes<=5 part):',seq[:22]==ref[:22], 'len',len(seq))
for name,sh in [('I4',[(0,0),(1,0),(2,0),(3,0)]),('L5',[(0,0),(0,1),(0,2),(0,3),(1,0)]),('Y5',[(0,0),(1,0),(2,0),(1,1),(3,0)]),('N5',[(1,0),(0,1),(2,0),(1,1),(3,0)])]:
    k=seq.index(mincode(norm(sh)))+1
    print(name,'= A246521(%d) -> A380597/8 index n=%d'%(k,k-1))
