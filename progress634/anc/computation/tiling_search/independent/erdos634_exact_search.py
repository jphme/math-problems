#!/usr/bin/env python3
"""Exact corner-filling search for tilings of a triangle by congruent triangles.

All coordinates are rational after the affine change (x,y)->(x,y/sqrt(D)),
where D is the Heron discriminant of the tile.  The physical metric is
    ||(x,y)||^2 = x^2 + D y^2.

This is a proof-oriented exact search.  It never assumes edge-to-edge.
At each state it chooses a convex corner of a remainder component and enumerates
all placements having a tile vertex at the corner and one incident tile edge
flush with either adjacent boundary ray.  A flush edge may pass a later reflex
boundary vertex; exact containment decides admissibility.  Containment,
subtraction, and all predicates are exact.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as F
from functools import cmp_to_key, lru_cache
from math import isqrt
from typing import Iterable, Iterator, Sequence
import argparse
import json
import sys
import time
import faulthandler

Point = tuple[F, F]
Segment = tuple[Point, Point]
Cycle = tuple[Point, ...]
State = tuple[Cycle, ...]


def P(x=0, y=0) -> Point:
    return (F(x), F(y))


def add(a: Point, b: Point) -> Point:
    return (a[0] + b[0], a[1] + b[1])


def sub(a: Point, b: Point) -> Point:
    return (a[0] - b[0], a[1] - b[1])


def mul(k: F, a: Point) -> Point:
    return (k * a[0], k * a[1])


def cross(a: Point, b: Point) -> F:
    return a[0] * b[1] - a[1] * b[0]


def orient(a: Point, b: Point, c: Point) -> F:
    return cross(sub(b, a), sub(c, a))


def dotD(a: Point, b: Point, D: int) -> F:
    return a[0] * b[0] + F(D) * a[1] * b[1]


def norm2D(a: Point, D: int) -> F:
    return dotD(a, a, D)


def sqrt_fraction(q: F) -> F:
    if q < 0:
        raise ValueError(f"negative square {q}")
    rn, rd = isqrt(q.numerator), isqrt(q.denominator)
    if rn * rn != q.numerator or rd * rd != q.denominator:
        raise ValueError(f"not a rational square: {q}")
    return F(rn, rd)


def metric_length(a: Point, D: int) -> F:
    return sqrt_fraction(norm2D(a, D))


def polygon_area2(cyc: Sequence[Point]) -> F:
    return sum(cross(cyc[i], cyc[(i + 1) % len(cyc)]) for i in range(len(cyc)))


def triangle_discriminant(side01: int, side12: int, side20: int) -> int:
    # 16 Area^2 = 2x^2y^2+2y^2z^2+2z^2x^2-x^4-y^4-z^4.
    x, y, z = side01, side12, side20
    D = 2*x*x*y*y + 2*y*y*z*z + 2*z*z*x*x - x**4 - y**4 - z**4
    if D <= 0:
        raise ValueError("degenerate side lengths")
    return D


def triangle_coords(side01: int, side12: int, side20: int, Dscale: int) -> Cycle:
    """CCW coordinates for sides |01|, |12|, |20| in the Dscale metric."""
    c = F(side01)
    # P0=(0,0), P1=(c,0), |P0P2|=side20, |P1P2|=side12.
    x = F(side20*side20 + side01*side01 - side12*side12, 2*side01)
    y2_phys = F(side20*side20) - x*x
    y_scaled = sqrt_fraction(y2_phys / F(Dscale))
    return (P(0, 0), P(c, 0), (x, y_scaled))


def point_on_segment(p: Point, a: Point, b: Point) -> bool:
    if orient(a, b, p) != 0:
        return False
    return (min(a[0], b[0]) <= p[0] <= max(a[0], b[0]) and
            min(a[1], b[1]) <= p[1] <= max(a[1], b[1]))


def segment_param(p: Point, a: Point, b: Point) -> F:
    d = sub(b, a)
    if d[0] != 0:
        return (p[0] - a[0]) / d[0]
    if d[1] != 0:
        return (p[1] - a[1]) / d[1]
    raise ValueError("zero segment")


def line_intersection(a: Point, b: Point, c: Point, d: Point) -> Point | None:
    r, s = sub(b, a), sub(d, c)
    den = cross(r, s)
    if den == 0:
        return None
    t = cross(sub(c, a), s) / den
    return add(a, mul(t, r))


def segment_intersection_points(a: Point, b: Point, c: Point, d: Point) -> set[Point]:
    """All endpoint/intersection points needed to split two closed segments."""
    out: set[Point] = set()
    o1, o2, o3, o4 = orient(a,b,c), orient(a,b,d), orient(c,d,a), orient(c,d,b)
    if o1 == 0 and o2 == 0 and o3 == 0 and o4 == 0:
        for p in (a,b,c,d):
            if point_on_segment(p,a,b) and point_on_segment(p,c,d):
                out.add(p)
        return out
    p = line_intersection(a,b,c,d)
    if p is not None and point_on_segment(p,a,b) and point_on_segment(p,c,d):
        out.add(p)
    return out


def proper_segments_cross(a: Point, b: Point, c: Point, d: Point) -> bool:
    o1, o2, o3, o4 = orient(a,b,c), orient(a,b,d), orient(c,d,a), orient(c,d,b)
    return ((o1 > 0 and o2 < 0 or o1 < 0 and o2 > 0) and
            (o3 > 0 and o4 < 0 or o3 < 0 and o4 > 0))


def point_in_cycle(p: Point, cyc: Sequence[Point], boundary=True) -> bool:
    # Exact ray crossing to +x, with half-open y convention.
    n = len(cyc)
    for i in range(n):
        if point_on_segment(p, cyc[i], cyc[(i+1)%n]):
            return boundary
    inside = False
    x, y = p
    for i in range(n):
        a, b = cyc[i], cyc[(i+1)%n]
        ay, by = a[1], b[1]
        if (ay > y) != (by > y):
            xint = a[0] + (y-ay) * (b[0]-a[0]) / (by-ay)
            if xint > x:
                inside = not inside
    return inside


def segment_contained_in_cycle(a: Point, b: Point, cyc: Sequence[Point]) -> bool:
    # Split at all boundary intersections and test every open interval midpoint.
    ts = {F(0), F(1)}
    n = len(cyc)
    for i in range(n):
        c, d = cyc[i], cyc[(i+1)%n]
        for p in segment_intersection_points(a,b,c,d):
            ts.add(segment_param(p,a,b))
    vals = sorted(t for t in ts if 0 <= t <= 1)
    direction = sub(b,a)
    for u,v in zip(vals, vals[1:]):
        if u < v:
            m = add(a, mul((u+v)/2, direction))
            if not point_in_cycle(m, cyc, boundary=True):
                return False
    return True


def triangle_contained(tri: Sequence[Point], cyc: Sequence[Point]) -> bool:
    for p in tri:
        if not point_in_cycle(p, cyc, boundary=True):
            return False
    n = len(cyc)
    for i in range(3):
        a,b = tri[i], tri[(i+1)%3]
        if not segment_contained_in_cycle(a,b,cyc):
            return False
    centroid = (sum(p[0] for p in tri)/3, sum(p[1] for p in tri)/3)
    return point_in_cycle(centroid,cyc,boundary=True)


def remove_collinear(cyc: Sequence[Point]) -> Cycle:
    pts = list(cyc)
    changed = True
    while changed and len(pts) >= 3:
        changed = False
        out=[]
        n=len(pts)
        for i,p in enumerate(pts):
            prev, nxt = pts[(i-1)%n], pts[(i+1)%n]
            if orient(prev,p,nxt)==0 and point_on_segment(p,prev,nxt):
                changed=True
            else:
                out.append(p)
        pts=out
    return tuple(pts)


def polar_half(v: Point) -> int:
    # upper half including +x first
    return 0 if (v[1] > 0 or (v[1] == 0 and v[0] >= 0)) else 1


def polar_cmp(u: Point, v: Point) -> int:
    hu,hv=polar_half(u),polar_half(v)
    if hu != hv:
        return -1 if hu < hv else 1
    cr=cross(u,v)
    if cr>0: return -1
    if cr<0: return 1
    # same ray; shorter first for deterministic order
    nu=u[0]*u[0]+u[1]*u[1]; nv=v[0]*v[0]+v[1]*v[1]
    return -1 if nu<nv else (1 if nu>nv else 0)


def extract_cycles(directed_edges: list[Segment]) -> list[Cycle] | None:
    """Trace faces with interior on the left from a balanced directed planar graph."""
    outgoing: dict[Point,list[Point]]={}
    incoming_count: dict[Point,int]={}
    for a,b in directed_edges:
        if a==b: continue
        outgoing.setdefault(a,[]).append(b)
        incoming_count[b]=incoming_count.get(b,0)+1
    vertices=set(outgoing)|set(incoming_count)
    for v in vertices:
        if len(outgoing.get(v,[])) != incoming_count.get(v,0):
            return None
        outgoing[v].sort(key=cmp_to_key(lambda p,q: polar_cmp(sub(p,v),sub(q,v))))
    unused=set(directed_edges)
    cycles=[]
    while unused:
        start=min(unused)
        a,b=start
        cyc=[a]
        edge=start
        guard=0
        while True:
            guard+=1
            if guard>len(directed_edges)+5:
                return None
            if edge not in unused:
                return None
            unused.remove(edge)
            u,v=edge
            if v==cyc[0]:
                break
            cyc.append(v)
            outs=outgoing.get(v,[])
            if not outs:
                return None
            # choose outgoing immediately clockwise from reverse incoming vector.
            rev=sub(u,v)
            # sort candidates plus sentinel rev; choose predecessor of rev in CCW order.
            allvec=[(sub(w,v),w) for w in outs]
            # Find candidate with minimal clockwise angle from rev = maximal CCW angle < rev.
            # Use a combined polar sort and predecessor.
            tagged=allvec+[(rev,None)]
            tagged.sort(key=cmp_to_key(lambda A,B: polar_cmp(A[0],B[0])))
            idx=next(i for i,x in enumerate(tagged) if x[1] is None)
            j=(idx-1)%len(tagged)
            while tagged[j][1] is None:
                j=(j-1)%len(tagged)
            w=tagged[j][1]
            edge=(v,w)
        c=remove_collinear(cyc)
        if len(c)<3:
            return None
        ar=polygon_area2(c)
        if ar==0:
            return None
        if ar<0:
            # A CW cycle would be a hole. Corner-removal placements should not create holes;
            # reject rather than silently mishandle them.
            return None
        cycles.append(c)
    return cycles


def subtract_triangle(cyc: Cycle, tri_ccw: Cycle) -> list[Cycle] | None:
    """Exact boundary symmetric difference for cyc minus tri; tri must be contained."""
    segs: list[Segment]=[]
    for i in range(len(cyc)):
        segs.append((cyc[i],cyc[(i+1)%len(cyc)]))
    # Add triangle boundary clockwise.
    tri=list(tri_ccw)
    for i in range(3):
        segs.append((tri[(i+1)%3],tri[i]))
    splitsets=[{a,b} for a,b in segs]
    for i in range(len(segs)):
        a,b=segs[i]
        for j in range(i+1,len(segs)):
            c,d=segs[j]
            pts=segment_intersection_points(a,b,c,d)
            if pts:
                splitsets[i].update(pts); splitsets[j].update(pts)
    coeff: dict[tuple[Point,Point],int]={}
    for (a,b),pts in zip(segs,splitsets):
        ordered=sorted(pts,key=lambda p: segment_param(p,a,b))
        for p,q in zip(ordered,ordered[1:]):
            if p==q: continue
            if p<q:
                key=(p,q); sgn=1
            else:
                key=(q,p); sgn=-1
            coeff[key]=coeff.get(key,0)+sgn
    directed=[]
    for (p,q),c in coeff.items():
        if c==0: continue
        if c==1: directed.append((p,q))
        elif c==-1: directed.append((q,p))
        else: return None
    return extract_cycles(directed)


def normalize_cycle(cyc: Cycle) -> Cycle:
    c=remove_collinear(cyc)
    if polygon_area2(c)<0:
        c=tuple(reversed(c))
    n=len(c)
    rots=[c[i:]+c[:i] for i in range(n)]
    return min(rots)


def normalize_state(cycles: Iterable[Cycle], translation=True) -> State:
    cs=[normalize_cycle(c) for c in cycles]
    if not cs:
        return ()
    if translation:
        minp=min(p for c in cs for p in c)
        cs=[tuple(sub(p,minp) for p in c) for c in cs]
        cs=[normalize_cycle(c) for c in cs]
    return tuple(sorted(cs))


def semigroup_reachable(limit: int, sides: Sequence[int]) -> list[bool]:
    reach=[False]*(limit+1); reach[0]=True
    for n in range(limit+1):
        if reach[n]:
            for s in sides:
                if n+s<=limit: reach[n+s]=True
    return reach


@dataclass
class SearchStats:
    nodes:int=0
    memo_hits:int=0
    placements:int=0
    contained:int=0
    pruned_semigroup:int=0
    bad_subtractions:int=0
    max_depth:int=0
    start:float=0.0


class ExactTilingSearch:
    def __init__(self, tile_sides: tuple[int,int,int], target_sides: tuple[int,int,int], N:int,
                 node_limit:int|None=None, progress_every:int=10000):
        # sides are cyclic edge lengths (01,12,20); congruence doesn't depend on ordering.
        self.tile_sides=tile_sides
        self.target_sides=target_sides
        self.N=N
        self.D=triangle_discriminant(*tile_sides)
        self.tile=triangle_coords(*tile_sides,self.D)
        self.target=triangle_coords(*target_sides,self.D)
        # Verify area ratio exactly in transformed coordinates.
        at=polygon_area2(self.tile); aT=polygon_area2(self.target)
        if aT != N*at:
            raise ValueError(f"area ratio mismatch: target/tile={aT/at}, expected {N}")
        self.tile_area2=at
        self.node_limit=node_limit
        self.progress_every=progress_every
        self.stats=SearchStats(start=time.time())
        self.memo:set[State]=set()
        self.solution:list[Cycle]=[]
        self._source_variants=self._make_source_variants()
        max_target=max(target_sides)
        self.reach=semigroup_reachable(max_target+max(tile_sides)*2,sorted(set(tile_sides)))
        # Original support lines, represented by target oriented edges.
        self.support_edges=[(self.target[i],self.target[(i+1)%3]) for i in range(3)]

    def _make_source_variants(self):
        # For each vertex and each incident edge, include original and reflected source shape.
        base=self.tile
        variants=[]
        for refl in (False,True):
            pts=tuple((x,-y) if refl else (x,y) for x,y in base)
            for v in range(3):
                others=[i for i in range(3) if i!=v]
                for oi in others:
                    variants.append((pts,v,oi))
        return variants

    def rotate_map_edge(self, pts: Cycle, v:int, oi:int, corner:Point, ray:Point) -> Cycle:
        src0=pts[v]; e=sub(pts[oi],src0)
        s=metric_length(e,self.D)
        L=metric_length(ray,self.D)
        target_vec=mul(s/L,ray)
        # Rational transformed-coordinate rotation mapping e to target_vec.
        cos=dotD(e,target_vec,self.D)/(s*s)
        cr=cross(e,target_vec)
        sin_over_sqrtD=cr/(s*s)
        # Matrix [[cos, -D*sin/sqrtD],[sin/sqrtD, cos]]
        def R(q:Point)->Point:
            return (cos*q[0]-F(self.D)*sin_over_sqrtD*q[1],
                    sin_over_sqrtD*q[0]+cos*q[1])
        out=tuple(add(corner,R(sub(p,src0))) for p in pts)
        # Ensure CCW for subtraction boundary.
        if polygon_area2(out)<0:
            out=tuple(reversed(out))
        return out

    def component_area_count(self, cyc:Cycle) -> F:
        return polygon_area2(cyc)/self.tile_area2

    def is_convex(self, cyc:Cycle, i:int)->bool:
        n=len(cyc)
        return orient(cyc[(i-1)%n],cyc[i],cyc[(i+1)%n])>0

    def choose_corner(self,state:State):
        candidates=[]
        for ci,cyc in enumerate(state):
            n=len(cyc)
            for i,p in enumerate(cyc):
                if self.is_convex(cyc,i):
                    prev,nxt=cyc[(i-1)%n],cyc[(i+1)%n]
                    lp=norm2D(sub(prev,p),self.D); ln=norm2D(sub(nxt,p),self.D)
                    candidates.append((min(lp,ln),max(lp,ln),p,ci,i))
        if not candidates:
            return None
        return min(candidates)[3:]

    def length_semigroup_ok(self, length:F)->bool:
        if length.denominator!=1: return False
        n=length.numerator
        return n>=0 and n<len(self.reach) and self.reach[n]

    def semigroup_prune(self,state:State)->bool:
        # Each component must have integral tile area.
        for cyc in state:
            q=self.component_area_count(cyc)
            if q.denominator!=1 or q<0:
                return False
        # Maximal boundary segments lying on an original support line must be sums of tile edges.
        for cyc in state:
            n=len(cyc)
            for i in range(n):
                a,b=cyc[i],cyc[(i+1)%n]
                v=sub(b,a)
                check=False
                for s0,s1 in self.support_edges:
                    if orient(s0,s1,a)==0 and orient(s0,s1,b)==0:
                        check=True; break
                # Also safe if both endpoints are convex corners of this component.
                if self.is_convex(cyc,i) and self.is_convex(cyc,(i+1)%n):
                    check=True
                if check:
                    try: L=metric_length(v,self.D)
                    except ValueError: return False
                    if not self.length_semigroup_ok(L):
                        return False
        return True

    def enumerate_placements(self,cyc:Cycle,i:int)->Iterator[Cycle]:
        n=len(cyc); corner=cyc[i]
        rays=[sub(cyc[(i-1)%n],corner),sub(cyc[(i+1)%n],corner)]
        seen=set()
        for ray in rays:
            if ray==(F(0),F(0)): continue
            for pts,v,oi in self._source_variants:
                tri=self.rotate_map_edge(pts,v,oi,corner,ray)
                key=normalize_cycle(tri)
                if key in seen: continue
                seen.add(key)
                yield tri

    def search(self)->bool:
        initial=normalize_state((self.target,),translation=False)
        self.path=[]
        result=self._dfs(initial,0)
        return result

    def _dfs(self,state:State,depth:int)->bool:
        st=self.stats; st.nodes+=1; st.max_depth=max(st.max_depth,depth)
        if self.node_limit and st.nodes>self.node_limit:
            raise RuntimeError("node limit")
        if self.progress_every and st.nodes%self.progress_every==0:
            print(json.dumps({"nodes":st.nodes,"depth":depth,"memo":len(self.memo),
                              "placements":st.placements,"contained":st.contained,
                              "elapsed":round(time.time()-st.start,2),"cycles":len(state),"verts":sum(len(c) for c in state),"maxverts":max(map(len,state)) if state else 0}),flush=True)
        if not state:
            if depth==self.N:
                self.solution=list(self.path); return True
            return False
        if depth>=self.N:
            return False
        # area determines remaining count exactly
        rem=sum(self.component_area_count(c) for c in state)
        if rem != self.N-depth:
            return False
        key=normalize_state(state,translation=True)
        if key in self.memo:
            st.memo_hits+=1; return False
        if not self.semigroup_prune(state):
            st.pruned_semigroup+=1; self.memo.add(key); return False
        choice=self.choose_corner(state)
        if choice is None:
            self.memo.add(key); return False
        ci,i=choice; cyc=state[ci]
        for tri in self.enumerate_placements(cyc,i):
            st.placements+=1
            if not triangle_contained(tri,cyc):
                continue
            st.contained+=1
            newcycles=subtract_triangle(cyc,tri)
            if newcycles is None:
                st.bad_subtractions+=1; continue
            allcycles=list(state[:ci])+newcycles+list(state[ci+1:])
            newstate=normalize_state(allcycles,translation=False)
            self.path.append(tri)
            if self._dfs(newstate,depth+1): return True
            self.path.pop()
        self.memo.add(key)
        return False


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--tile',nargs=3,type=int,required=True,metavar=('S01','S12','S20'))
    ap.add_argument('--target',nargs=3,type=int,required=True,metavar=('S01','S12','S20'))
    ap.add_argument('-N',type=int,required=True)
    ap.add_argument('--node-limit',type=int)
    ap.add_argument('--progress-every',type=int,default=10000)
    ap.add_argument('--out')
    ap.add_argument(
        '--debug-stacks',
        action='store_true',
        help='emit a Python stack dump every 30 seconds while the search runs',
    )
    args=ap.parse_args()
    if args.debug_stacks:
        faulthandler.enable()
        faulthandler.dump_traceback_later(30, repeat=True)
    S=ExactTilingSearch(tuple(args.tile),tuple(args.target),args.N,args.node_limit,args.progress_every)
    ok=S.search()
    result={"tile":args.tile,"target":args.target,"N":args.N,"tile_discriminant":S.D,
            "result":"TILING" if ok else "EXHAUSTED_NO_TILING",
            "stats":{**S.stats.__dict__,"elapsed":time.time()-S.stats.start,"memo":len(S.memo)}}
    if ok:
        result['solution']=[[[str(x),str(y)] for x,y in tri] for tri in S.solution]
    print(json.dumps(result,indent=2),flush=True)
    if args.out:
        with open(args.out,'w') as f: json.dump(result,f,indent=2)

if __name__=='__main__':
    main()
