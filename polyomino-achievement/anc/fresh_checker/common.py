import sys
def parse_shape(tokens):
    return [tuple(map(int, t.split(','))) for t in tokens]
def placements(shape, W, H):
    """All images of shape under the 8 dihedral maps, translated into WxH board; as bitmasks (cell=y*W+x)."""
    syms = [lambda x,y:(x,y), lambda x,y:(-x,y), lambda x,y:(x,-y), lambda x,y:(-x,-y),
            lambda x,y:(y,x), lambda x,y:(-y,x), lambda x,y:(y,-x), lambda x,y:(-y,-x)]
    seen=set(); out=set()
    for s in syms:
        c=[s(x,y) for x,y in shape]
        mx=min(x for x,_ in c); my=min(y for _,y in c)
        c=tuple(sorted((x-mx,y-my) for x,y in c))
        if c in seen: continue
        seen.add(c)
        w=max(x for x,_ in c)+1; h=max(y for _,y in c)+1
        for ox in range(W-w+1):
            for oy in range(H-h+1):
                m=0
                for x,y in c: m|=1<<((y+oy)*W+x+ox)
                out.add(m)
    return sorted(out)
