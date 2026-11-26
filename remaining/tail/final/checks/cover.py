# Exact covering of the parameter polygon of a tuple by engine certificates.
# A constraint is ((cw,cu,cy), strict): cw*w + cu*u + cy*y >= 0 (or > 0). We work at w = 1.
# A piece is a list of constraints (an intersection of half-planes, some open).
import sys, json, time
from fractions import Fraction as Fr
from engine import System, Prover, normcon

def val(f, u, y): return f[0] + f[1] * u + f[2] * y

BOX = None
def closure_poly(cons):
    """vertices of the closed polygon {f >= 0 for all f}, clipped to BOX."""
    P = list(BOX)
    for (f, s) in cons:
        if not P: break
        Q = []
        n = len(P)
        for t in range(n):
            A = P[t]; B = P[(t + 1) % n]
            va, vb = val(f, *A), val(f, *B)
            if va >= 0: Q.append(A)
            if (va > 0 and vb < 0) or (va < 0 and vb > 0):
                lam = va / (va - vb)
                Q.append((A[0] + lam * (B[0] - A[0]), A[1] + lam * (B[1] - A[1])))
        # dedupe consecutive equal points
        R = []
        for p in Q:
            if not R or R[-1] != p: R.append(p)
        if len(R) > 1 and R[0] == R[-1]: R.pop()
        P = R
    return P

def area2(P):
    return sum(P[t][0] * P[(t + 1) % len(P)][1] - P[(t + 1) % len(P)][0] * P[t][1] for t in range(len(P)))

def sample(cons):
    """a point of the set, or None if empty."""
    P = closure_poly(cons)
    if not P: return None
    if len(P) >= 3 and area2(P) != 0:
        cx = sum(p[0] for p in P) / len(P); cy = sum(p[1] for p in P) / len(P)
        pt = (cx, cy)
    elif len(P) >= 2:
        # segment: take extreme points
        pts = sorted(set(P))
        A, B = pts[0], pts[-1]
        pt = ((A[0] + B[0]) / 2, (A[1] + B[1]) / 2)
    else:
        pt = P[0]
    for f, s in cons:
        v = val(f, *pt)
        if v < 0 or (s and v == 0): return None
    return pt

def implied(cons, c):
    """is constraint c true on the whole set given by cons?"""
    f, s = c
    neg = (tuple(-a for a in f), not s)  # negation of c
    return sample(cons + [neg]) is None

def derivation(pr):
    """used relations, windows (topologically ordered) and global steps"""
    W = pr.W; need = set(); stack = list(pr.gsteps)
    while stack:
        n = stack.pop()
        if n in need: continue
        need.add(n)
        prov = W[n][4]
        if prov[0] == 'pair': stack += [prov[1], prov[2]]
    order = sorted(need)  # parents always have smaller indices
    ren = {n: t for t, n in enumerate(order)}
    rels = sorted({W[n][4][1] for n in order if W[n][4][0] == 'rel'})
    rren = {r: t for t, r in enumerate(rels)}
    wins = []
    for n in order:
        lo, hi, B, dep, prov = W[n]
        if prov[0] == 'rel': pv = ['rel', rren[prov[1]], prov[2], prov[3]]
        else: pv = ['pair', ren[prov[1]], ren[prov[2]], prov[3], {k: (list(v) if isinstance(v, tuple) else v) for k, v in prov[4].items()}]
        wins.append({'lo': list(lo), 'hi': list(hi), 'B': [list(b) for b in B], 'prov': pv})
    return {'rels': [[list(pr.R[r][0]), list(pr.R[r][1]), list(pr.R[r][2])] for r in rels],
            'wins': wins, 'gsteps': [ren[n] for n in pr.gsteps],
            'ginfo': [{k: (list(v) if isinstance(v, tuple) else v) for k, v in g.items()} for g in pr.ginfo]}

def run(i, k, l, Ymax, logfile, maxpieces=200000):
    global BOX
    S = System(i, k, l)
    c = i + l - 2
    umax = Fr(S.kap, c)
    BOX = [(Fr(0), Fr(0)), (umax, Fr(0)), (umax, Ymax), (Fr(0), Ymax)]
    R0 = [((0, 1, 0), True), ((S.kap, -c, 0), True), ((0, 0, 1), True),
          ((Ymax, 0, -1), True)]
    todo = [R0]; certs = []; failures = []; n = 0; t0 = time.time()
    while todo:
        Q = todo.pop()
        pt = sample(Q)
        if pt is None: continue
        n += 1
        if n > maxpieces: print('too many pieces'); break
        pr = Prover(S, (1, pt[0], pt[1]))
        r, Bg, dep = pr.run()
        if r is None:
            V = closure_poly(Q)
            import random
            rnd = random.Random(n)
            zs = [f for f, s_ in Q if not s_ and any(normcon(tuple(-a for a in f), False) == normcon(g, False) for g, t_ in Q if not t_)]
            if zs:
                pr = Prover(S, (1, pt[0], pt[1]), zeros=zs); r, Bg, dep = pr.run()
            for _ in range(8 if (len(V) > 1 and r is None) else 0):
                wts = [Fr(rnd.randint(1, 1000)) for _ in V]; tw = sum(wts)
                q = (sum(a * v[0] for a, v in zip(wts, V)) / tw, sum(a * v[1] for a, v in zip(wts, V)) / tw)
                if not all((val(f, *q) > 0) if s_ else (val(f, *q) >= 0) for f, s_ in Q): continue
                pr = Prover(S, (1, q[0], q[1])); r, Bg, dep = pr.run()
                if r is not None: pt = q; break
        if r is None:
            V = closure_poly(Q)
            failures.append((pt, Q, len(set(V)))); continue
        dep = [cn for cn in dep if any(cn[0])]
        certs.append({'pt': [str(pt[0]), str(pt[1])], 'kind': r, 'Bg': Bg, 'zeros': [list(z) for z in pr.zeros],
                      'cons': [[list(f), s] for f, s in dep], 'deriv': derivation(pr)})
        # Q \ K  as disjoint pieces
        need = [cn for cn in dep if not implied(Q, cn)]
        acc = list(Q)
        for (f, s) in need:
            negc = (tuple(-a for a in f), not s)
            piece = acc + [negc]
            if sample(piece) is not None: todo.append(piece)
            acc = acc + [(f, s)]
        if n % 50 == 0:
            print(n, 'certs', len(certs), 'todo', len(todo), 'fail', len(failures), round(time.time() - t0), flush=True)
    json.dump({'tuple': [i, k, l], 'Ymax': str(Ymax), 'certs': certs,
               'failures': [[[str(a) for a in p], [[[str(a) for a in f], s] for f, s in q], dim] for p, q, dim in failures]},
              open(logfile, 'w'))
    print('done', (i, k, l), 'certs', len(certs), 'failures', len(failures), 'time', round(time.time() - t0))
    for p, q, dim in failures[:40]: print(' fail at', p, 'closure vertices', dim)
    return certs, failures

if __name__ == '__main__':
    i, k, l = map(int, sys.argv[1:4]); Ymax = Fr(sys.argv[4])
    run(i, k, l, Ymax, sys.argv[5])
