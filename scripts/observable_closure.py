"""Compare invariant span synthesis with independent state refinement."""
from collections import deque
from collections import Counter
from itertools import product


def span(rows):
    vals={0}
    for r in rows:
        vals |= {r^x for x in vals}
    return frozenset(vals)


def dot(x,y):
    return (x&y).bit_count() % 2


def state(m,x):
    out=0
    for i,col in enumerate(m):
        if (x>>i)&1:
            out ^= col
    return out


def dual(m,v):
    return sum(dot(v,col)<<i for i,col in enumerate(m))


def synth(mats,seeds):
    # Coordinates and word witnesses are retained so the certificate itself can be replayed.
    expr={0:0}
    basis=[]
    work=deque((v,(),i) for i,v in enumerate(seeds))
    tests=0
    while work:
        v,word,seed=work.popleft()
        tests+=1
        if v in expr:
            continue
        bit=1<<len(basis)
        expr.update({x^v:c^bit for x,c in expr.items()})
        basis.append((v,word,seed))
        for a,m in enumerate(mats):
            work.append((dual(m,v),word+(a,),seed))
    for v,word,i in basis:
        y=seeds[i]
        for a in word:
            y=dual(mats[a],y)
        assert y==v
    for m in mats:
        for v,_,_ in basis:
            mask=expr[dual(m,v)]
            for x in range(1<<len(m)):
                reduced=sum(dot(x,b[0])<<i for i,b in enumerate(basis))
                assert dot(reduced,mask)==dot(state(m,x),v)
    return [b[0] for b in basis],tests


def quotient(mats,seeds,n):
    # Independent Moore refinement on state pairs, without linear algebra or dual maps.
    states=range(1<<n)
    ids=[tuple(dot(x,s) for s in seeds) for x in states]
    while True:
        table={}
        new=[]
        for x in states:
            sig=(ids[x],tuple(ids[state(m,x)] for m in mats))
            new.append(table.setdefault(sig,len(table)))
        if len(set(new))==len(set(ids)):
            return new
        ids=new


def closure_cases(n,letters):
    mats=list(product(range(1<<n),repeat=n))
    by_dimension=Counter()
    side=0
    for actions in product(mats,repeat=letters):
        for seed in range(1<<n):
            basis,tests=synth(actions,[seed])
            q=quotient(actions,[seed],n)
            assert 1+letters*len(basis)==tests
            by_dimension[len(basis)]+=1
            for x,y in product(range(1<<n),repeat=2):
                assert (q[x]==q[y])==all(dot(x^y,b)==0 for b in basis)
            if n==2:
                for p in [(),(1,),(2,),(3,),(1,2)]:
                    fibers={}
                    for x in range(1<<n):
                        key=tuple(dot(x,b) for b in p)
                        fibers.setdefault(key,set()).add(q[x])
                    assert {len(t) for t in fibers.values()}=={len(span(basis+list(p)))//len(span(p))}
                    side+=1
    return {"inputs":sum(by_dimension.values()),"state_dimension":dict(by_dimension),"side_tests":side}


if __name__ == "__main__":
    print(closure_cases(2,2))
    print(closure_cases(3,1))
