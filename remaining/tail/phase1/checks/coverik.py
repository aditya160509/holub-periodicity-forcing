# Exact covering in three projective dimensions: variables (d,u,y,D), normalized D = 1.
# A constraint ((cd,cu,cy,cD), strict) means cd*d + cu*u + cy*y + cD >= 0 (> 0 if strict).
import sys, json, time, random
from fractions import Fraction as Fr
from itertools import combinations
import engine_n as E
from sysik import SysIK, region

def val(f, p): return f[0] * p[0] + f[1] * p[1] + f[2] * p[2] + f[3]

def solve3(f, g, h):
    M = [[f[0], f[1], f[2]], [g[0], g[1], g[2]], [h[0], h[1], h[2]]]
    b = [-f[3], -g[3], -h[3]]
    det = (M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1]) - M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0])
           + M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]))
    if det == 0: return None
    def rep(c):
        A = [row[:] for row in M]
        for r in range(3): A[r][c] = b[r]
        return (A[0][0] * (A[1][1] * A[2][2] - A[1][2] * A[2][1]) - A[0][1] * (A[1][0] * A[2][2] - A[1][2] * A[2][0])
                + A[0][2] * (A[1][0] * A[2][1] - A[1][1] * A[2][0]))
    return (Fr(rep(0), det), Fr(rep(1), det), Fr(rep(2), det))

def vertices(cons):
    fs = []
    for f, s in cons:
        if not any(f[:3]):
            if f[3] < 0 or (s and f[3] == 0): return []
            continue
        if f not in fs: fs.append(f)
    V = set()
    for a, b, c in combinations(fs, 3):
        p = solve3(a, b, c)
        if p is None: continue
        if all(val(f, p) >= 0 for f in fs): V.add(p)
    return list(V)

def prune(cons):
    V = vertices(cons)
    if not V: return None, V
    out = []
    for f, s in cons:
        vs = [val(f, v) for v in V]
        if all(x > 0 for x in vs): continue
        out.append((f, s))
    return out, V

def sample(cons, V=None):
    if V is None: V = vertices(cons)
    if not V: return None
    n = len(V)
    p = (sum(v[0] for v in V) / n, sum(v[1] for v in V) / n, sum(v[2] for v in V) / n)
    for f, s in cons:
        x = val(f, p)
        if x < 0 or (s and x == 0): return None
    return p

def implied(cons, V, c):
    f, s = c
    vs = [val(f, v) for v in V]
    if any(x < 0 for x in vs): return False
    if not s: return True
    Z = [v for v, x in zip(V, vs) if x == 0]
    if not Z: return True
    if len(Z) == len(V): return False
    return any(st and all(val(g, z) == 0 for z in Z) for g, st in cons)

def neg(c): f, s = c; return (tuple(-a for a in f), not s)

def dim(V):
    if not V: return -1
    if len(V) == 1: return 0
    o = V[0]; vecs = [tuple(v[i] - o[i] for i in range(3)) for v in V[1:]]
    # rank of vecs
    rows = [list(v) for v in vecs]; r = 0
    for col in range(3):
        piv = next((row for row in rows if row[col] != 0), None)
        if piv is None: continue
        rows.remove(piv); r += 1
        rows = [[a - row[col] / piv[col] * b for a, b in zip(row, piv)] for row in rows]
    return r

def to4(c):  # engine forms are homogeneous in (d,u,y,D): identical coefficient vector
    return c

def run(i, k, l0, logfile, n0=3, maxpieces=400000, seed=1):
    S = SysIK(i, k, l0, n0)
    dmax = Fr(3, i + k + l0)
    box = [((1, 0, 0, 0), False), ((-1, 0, 0, dmax), False), ((0, 1, 0, 0), False), ((0, -1, 0, dmax / (i + l0 - 2)), False),
           ((0, 0, 1, 0), False), ((0, 0, -1, 1), False)]
    R0 = region(i, k, l0)
    todo = [R0]; certs = []; fails = []; n = 0; t0 = time.time(); rnd = random.Random(seed)
    while todo:
        Q = todo.pop()
        Qp, V = prune(Q + box)
        if Qp is None: continue
        Q = [c for c in Qp if c not in box] + [c for c in Q if c in Qp and c in box]
        pt = sample(Qp, V)
        if pt is None: continue
        n += 1
        recent = getattr(run, 'recent', []); recent.append(float(pt[0])); run.recent = recent[-200:]
        if n > maxpieces: print('too many'); break
        zs = []
        for f, s in Qp:
            if not s and (tuple(-a for a in f), False) in Qp and tuple(-a for a in f) not in zs: zs.append(f)
        P4 = (pt[0], pt[1], pt[2], Fr(1))
        pr = E.Prover(S, P4, zeros=[tuple(z) for z in zs], uniform=True)
        try:
            r, Bg, dep = pr.run(budget=6)
        except AssertionError:
            r = None
        if r is None and len(V) > 1:
            for _ in range(3):
                w = [Fr(rnd.randint(1, 1000)) for _ in V]; tw = sum(w)
                q = tuple(sum(a * v[i] for a, v in zip(w, V)) / tw for i in range(3))
                if not all((val(f, q) > 0) if s else (val(f, q) >= 0) for f, s in Qp): continue
                pr = E.Prover(S, (q[0], q[1], q[2], Fr(1)), zeros=[tuple(z) for z in zs], uniform=True)
                r, Bg, dep = pr.run(budget=4)
                if r: pt = q; break
        if r is None:
            fails.append((pt, Qp, dim(V))); continue
        dep = [c for c in dep if any(c[0])]
        certs.append({'pt': [str(a) for a in pt], 'kind': r, 'Bg': Bg, 'zeros': [list(z) for z in pr.zeros],
                      'cons': [[list(f), s] for f, s in dep], 'deriv': derivation(pr)})
        need = [c for c in dep if not implied(Qp, V, c)]
        acc = list(Q)
        for c in need:
            todo.append(acc + [neg(c)])
            acc = acc + [c]
        if n % 200 == 0:
            print(n, 'certs', len(certs), 'todo', len(todo), 'fail', len(fails), round(time.time() - t0), 'min d/D recent %.2e' % min(run.recent), flush=True)
    json.dump({'family': [i, k], 'l0': l0, 'n0': n0, 'certs': certs,
               'failures': [[[str(a) for a in p], [[[str(a) for a in f], s] for f, s in q], dd] for p, q, dd in fails]},
              open(logfile, 'w'), default=str)
    print('done', (i, k), 'l0', l0, 'certs', len(certs), 'failures', len(fails), 'time', round(time.time() - t0))
    for p, q, dd in fails[:30]: print(' fail', [float(a) for a in p], 'dim', dd)

def derivation(pr):
    W = pr.W; need = set(); stack = list(pr.gsteps)
    while stack:
        m = stack.pop()
        if m in need: continue
        need.add(m)
        if W[m][4][0] == 'pair': stack += [W[m][4][1], W[m][4][2]]
    order = sorted(need); ren = {m: t for t, m in enumerate(order)}
    rels = sorted({W[m][4][1] for m in order if W[m][4][0] == 'rel'}); rren = {r: t for t, r in enumerate(rels)}
    tl = lambda v: list(v) if isinstance(v, tuple) else v
    wins = []
    for m in order:
        lo, hi, B, dep, prov = W[m]
        if prov[0] == 'rel': pv = ['rel', rren[prov[1]], prov[2], prov[3]]
        else: pv = ['pair', ren[prov[1]], ren[prov[2]], tl(prov[3]), {k: tl(v) for k, v in prov[4].items()}, prov[5]]
        wins.append({'lo': list(lo), 'hi': list(hi), 'B': [list(b) for b in B], 'prov': pv})
    return {'rels': [[list(pr.R[r][0]), list(pr.R[r][1]), list(pr.R[r][2])] for r in rels], 'wins': wins,
            'gsteps': [ren[m] for m in pr.gsteps],
            'ginfo': [{k: tl(v) for k, v in g.items()} for g in pr.ginfo]}

if __name__ == '__main__':
    run(int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4])
