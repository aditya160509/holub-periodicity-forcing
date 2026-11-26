# Independent checker for the certificates written by cover.py.
# It does not import engine.py or cover.py. It re-derives the equal-factor relations from the
# four word identities, re-verifies every window and Fine--Wilf step as a linear inequality
# implied on the certificate's cell, and then verifies that the cells cover the parameter polygon.
#
# Coordinates: forms are integer vectors (cw,cu,cy) meaning cw*w+cu*u+cy*y, with d = kap*w.
# Cells live in the plane w = 1. A constraint (f, strict) means f >= 0 (strict: f > 0).
import sys, json
from fractions import Fraction as F
from itertools import product
from math import gcd

# ---------------- linear algebra over Z (written independently of engine.py) ----------------
def vadd(a, b): return tuple(p + q for p, q in zip(a, b))
def vsub(a, b): return tuple(p - q for p, q in zip(a, b))
def vmul(c, a): return tuple(c * p for p in a)
Z3 = (0, 0, 0)

def echelon(vs):
    """integer row echelon basis (lower-triangular style elimination by Euclid on each column)"""
    rows = [list(v) for v in vs if any(v)]
    out = []
    for col in range(3):
        while True:
            nz = [r for r in rows if r[col] != 0]
            if len(nz) <= 1: break
            nz.sort(key=lambda r: abs(r[col]))
            p = nz[0]
            for r in nz[1:]:
                q = r[col] // p[col]
                for t in range(3): r[t] -= q * p[t]
        nz = [r for r in rows if r[col] != 0]
        if nz:
            p = nz[0]
            if p[col] < 0: p = [-a for a in p]
            out.append(tuple(p)); rows = [r for r in rows if r is not nz[0] and any(r)]
            rows = [r for r in rows if r[col] == 0 and any(r)]
    return out

def in_lattice(basis, t):
    t = list(t)
    for r in basis:
        c = next(j for j in range(3) if r[j])
        if any(t[j] for j in range(c)): return False
        if t[c] % r[c]: return False
        q = t[c] // r[c]
        t = [a - q * b for a, b in zip(t, r)]
    return not any(t)

def lat_sub(B1, B2): return all(in_lattice(B2, r) for r in B1)

# ---------------- geometry of a cell ----------------
def val(f, p): return f[0] + f[1] * p[0] + f[2] * p[1]

class Cell:
    def __init__(self, cons, box):
        self.cons = cons
        V = list(box)
        for f, s in cons:
            V = clip(V, f)
            if not V: break
        self.V = dedupe(V)
        self.nonempty = self._nonempty()

    def _nonempty(self):
        V = self.V
        if not V: return False
        for f, s in self.cons:
            if s and all(val(f, v) == 0 for v in V): return False
        if len(V) == 1:
            return all(val(f, V[0]) > 0 for f, s in self.cons if s)
        return True

    def implies(self, f, strict):
        if not any(f): return not strict
        vs = [val(f, v) for v in self.V]
        if any(x < 0 for x in vs): return False
        if not strict: return True
        Zs = [v for v, x in zip(self.V, vs) if x == 0]
        if not Zs: return True
        if len(Zs) == len(self.V): return False  # f vanishes on the whole (nonempty) cell
        return any(s and all(val(g, z) == 0 for z in Zs) for g, s in self.cons)

    def contains(self, p):
        return all((val(f, p) > 0) if s else (val(f, p) >= 0) for f, s in self.cons)

def clip(V, f):
    out = []; n = len(V)
    for t in range(n):
        A, B = V[t], V[(t + 1) % n]
        a, b = val(f, A), val(f, B)
        if a >= 0: out.append(A)
        if a * b < 0:
            lam = a / (a - b)
            out.append((A[0] + lam * (B[0] - A[0]), A[1] + lam * (B[1] - A[1])))
    return out

def dedupe(V):
    W = []
    for p in V:
        if p not in W: W.append(p)
    # drop collinear middle points (keep the polygon's corners)
    changed = True
    while changed and len(W) > 2:
        changed = False
        for t in range(len(W)):
            A, B, C = W[t - 1], W[t], W[(t + 1) % len(W)]
            if (B[0] - A[0]) * (C[1] - A[1]) - (B[1] - A[1]) * (C[0] - A[0]) == 0:
                # B is between A and C on a line (convex polygon): remove it
                W.pop(t); changed = True; break
    return W

# ---------------- the reduced system, derived afresh ----------------
class Tup:
    def __init__(self, i, k, l):
        self.i, self.k, self.l = i, k, l
        S = i + k + l; self.kap = 3 if S % 3 else 1; kap = self.kap
        self.x = (kap, 1, 0); self.dd = (kap, 0, 0)
        self.Dl = S * kap // 3
        self.h = ((i + l) * kap - self.Dl, 0, 0)
        self.a = (self.Dl - i * kap, 0, 0)
        self.g = (l * kap - self.Dl, 0, 0)
        m = i + l - 2 * k
        self.p = (m * kap // 3, 0, 0)
        self.c = i + l - 2
        assert (m * kap) % 3 == 0

    def relations(self, pt, need):
        """need: list of constraints that must be implied on the cell for this derivation"""
        i, k, l = self.i, self.k, self.l
        x = self.x; u = (0, 1, 0); y = (0, 0, 1)
        def cmp(f):  # sign at the point, recording why
            v = val(f, pt)
            if not any(f): return 0
            if v > 0: need.append((f, True)); return 1
            if v < 0: need.append((vmul(-1, f), True)); return -1
            need.append((f, False)); need.append((vmul(-1, f), False)); return 0
        Xb = (Z3, x)
        Ub = (Z3, u) if i > 0 else (vsub(x, u), u)
        Cb = (vmul(i, u), vmul(i, self.dd))
        Hb = (Z3, self.h); Ab = (self.h, self.a)
        blocks = lambda L: [b for b in L if any(b[1])]
        AC = blocks([Ab, Cb])
        # Y = prefix of (AC)^omega of length y
        D = vadd(self.a, vmul(i, self.dd))
        q = 0
        while cmp(vsub(y, vmul(q + 1, D))) >= 0: q += 1
        # now q*D <= y < (q+1)*D  (the case y == (q+1)D was absorbed: then loop continued)
        Y = AC * q; rem = vsub(y, vmul(q, D))
        Y += prefix(AC, rem, cmp)
        G = prefix(Y + [Hb], self.g, cmp)
        eqs = [([Xb] * i, [Ub] * i + blocks([Cb])),
               ([Xb] * l, [Hb, Ab] + [Ub] * l),
               (Y + [Hb], G + blocks([Cb]) + Y),
               (Y + [Xb] * k + G, blocks([Ab, Cb]) + Y + [Ab] + [Ub] * k)]
        base = list(need)
        out = []
        for L, R in eqs:
            req = list(base)
            def cmp2(f, req=req):
                v = val(f, pt)
                if not any(f): return 0
                if v > 0: req.append((f, True)); return 1
                if v < 0: req.append((vmul(-1, f), True)); return -1
                req.append((f, False)); req.append((vmul(-1, f), False)); return 0
            out.append((refine(L, R, cmp2, x), req))
        return out

def prefix(bl, n, cmp):
    out = []; acc = Z3
    for s, L in bl:
        r = vsub(n, acc)
        if cmp(r) <= 0: break
        c = cmp(vsub(L, r))
        if c >= 0:
            out.append((s, r)); acc = n; break
        out.append((s, L)); acc = vadd(acc, L)
    return out

def refine(L, R, cmp, x):
    """common refinement of two block sequences of equal total length -> relations (a,b,len)"""
    def cuts(bl):
        c = [Z3]
        for s, Ln in bl: c.append(vadd(c[-1], Ln))
        return c
    cl, cr = cuts(L), cuts(R)
    # merge the breakpoints in order
    pts = []
    il = ir = 0
    rels = []
    pos = Z3
    while il < len(L) and ir < len(R):
        el, er = cl[il + 1], cr[ir + 1]
        sgn = cmp(vsub(el, er))
        nxt = el if sgn < 0 else er
        ln = vsub(nxt, pos)
        a = vadd(L[il][0], vsub(pos, cl[il])); b = vadd(R[ir][0], vsub(pos, cr[ir]))
        rels.append((a, b, ln))
        pos = nxt
        if sgn <= 0: il += 1
        if sgn >= 0: ir += 1
    # merge pieces that continue each other modulo x
    def xmul(f):
        if f[1] % x[1]: return None
        j = f[1] // x[1]
        return j if vmul(j, x) == f else None
    out = []
    for a, b, ln in rels:
        if out:
            a0, b0, l0 = out[-1]
            if xmul(vsub(a, vadd(a0, l0))) is not None and xmul(vsub(b, vadd(b0, l0))) is not None:
                out[-1] = (a0, b0, vadd(l0, ln)); continue
        out.append((a, b, ln))
    return out

# ---------------- certificate verification ----------------
class Fail(Exception): pass

def xmult(f, x):
    if f[1] % x[1]: return None
    j = f[1] // x[1]
    return j if vmul(j, x) == f else None

def check_cert(T, C, box):
    cons = [(tuple(f), s) for f, s in C['cons']]
    cell = Cell(cons, box)
    if not cell.nonempty: raise Fail('empty cell')
    pt = (F(C['pt'][0]), F(C['pt'][1]))
    if not cell.contains(pt): raise Fail('point not in cell')
    cell.fpt = (float(pt[0]), float(pt[1]))
    def need(f, s, why):
        if not cell.implies(tuple(f), s): raise Fail('not implied: %s %s %s' % (why, f, s))
    # relations, derived afresh
    req = []
    byeq = T.relations(pt, req)
    D = C['deriv']; x = T.x
    R = [(tuple(a), tuple(b), tuple(L)) for a, b, L in D['rels']]
    def same(f, g): return cell.implies(vsub(f, g), False) and cell.implies(vsub(g, f), False)
    checked_eq = set()
    def zero_on_cell(f): return cell.implies(f, False) and cell.implies(vmul(-1, f), False)
    def subrel(r, r2):
        a, b, L = r; a2, b2, L2 = r2
        if r == r2: return True
        for j1 in range(-3, 4):
            t0 = vsub(vsub(a, a2), vmul(j1, x))
            if not cell.implies(t0, False): continue
            if not cell.implies(vsub(vsub(L2, t0), L), False): continue
            for j2 in range(-3, 4):
                if zero_on_cell(vsub(vsub(vsub(b, b2), vmul(j2, x)), t0)): return True
        return False
    for r in R:
        a, b, L = r
        if any(zero_on_cell(vsub(vsub(b, a), vmul(j, x))) for j in range(-6, 7)):
            continue  # trivially true by x-periodicity on this cell
        ok = False
        for e, (rels, rq) in enumerate(byeq):
            if not any(subrel(r, r2) for r2 in rels): continue
            if all(cell.implies(f, s) for f, s in rq): ok = True; break
        if not ok: raise Fail('relation not derived on the whole cell: %s' % (r,))
    Zs = [tuple(z) for z in C.get('zeros', [])]
    for z in Zs:
        need(z, False, 'zero form'); need(vmul(-1, z), False, 'zero form')
    def lat_eq(B1, B2): return lat_sub(B1, B2) and lat_sub(B2, B1)
    def bound_ok(B, b):
        """b must lie in Lambda(B u Z) and be positive on the cell (then gcd(B) <= b there)"""
        b = tuple(b)
        if not in_lattice(echelon(list(B) + Zs), b): raise Fail('bound not in lattice')
        need(b, True, 'bound positive')
        return b
    def threshold(B1, B2, info):
        """recompute the threshold from the stored bound forms, verifying each claim"""
        cs = info['case']
        B1z = echelon(list(B1) + Zs); B2z = echelon(list(B2) + Zs)
        if cs == 'sub2':
            if not lat_sub(B2z, B1z): raise Fail('sub2 inclusion')
            return bound_ok(B2, info['b2'])
        if cs == 'sub1':
            if not lat_sub(B1z, B2z): raise Fail('sub1 inclusion')
            return bound_ok(B1, info['b1'])
        if cs == 'cmult':
            Ba, Bb = (B1, B2) if info['which'] == 'b1' else (B2, B1)
            fa = tuple(info['fa']); cm = info['cm']
            if len(Zs) > 1: raise Fail('cmult with several zeros')
            if not lat_eq(echelon(list(Ba) + Zs), echelon([fa] + Zs)): raise Fail('cmult rank one')
            need(fa, True, 'cmult generator positive')
            if not in_lattice(echelon(list(Bb) + Zs), vmul(cm, fa)): raise Fail('cmult multiple')
            bb = bound_ok(Bb, info['bb'])
            return ('scaled', vadd(vmul(cm, fa), vmul(cm - 1, bb)), cm)
        t = vadd(bound_ok(B1, info['b1']), bound_ok(B2, info['b2']))
        if cs == 'gen': return t
        if cs == 'rank1':
            f = tuple(info['f'])
            if len(Zs) > 1: raise Fail('rank1 with several zero forms')
            if not lat_eq(echelon(list(B1) + list(B2) + Zs), echelon([f] + Zs)): raise Fail('rank1 lattice')
            need(f, True, 'rank1 generator positive')
            return vsub(t, f)
        raise Fail('unknown case')
    W = []
    for w in D['wins']:
        lo, hi = tuple(w['lo']), tuple(w['hi']); B = echelon([tuple(b) for b in w['B']])
        pv = w['prov']
        if pv[0] == 'rel':
            a, b, L = R[pv[1]]
            s2 = vsub(vsub(b, a), vmul(pv[2], x))
            if pv[3] > 0:
                need(s2, True, 'shift sign'); lo0, hi0, per = a, vadd(vadd(a, L), s2), s2
            else:
                need(vmul(-1, s2), True, 'shift sign'); lo0, hi0, per = vadd(a, s2), vadd(a, L), vmul(-1, s2)
            q = xmult(vsub(lo, lo0), x)
            if q is None or vsub(hi, hi0) != vmul(q, x): raise Fail('window endpoints')
            Bp = echelon([per])
            if not (lat_sub(B, Bp) and lat_sub(Bp, B)): raise Fail('window period')
        else:
            lo1, hi1, B1 = W[pv[1]]; lo2, hi2, B2 = W[pv[2]]
            lo2 = vadd(lo2, vmul(pv[3], x)); hi2 = vadd(hi2, vmul(pv[3], x))
            Tm = threshold(B1, B2, pv[4])
            sc_ = 1
            if isinstance(Tm, tuple) and Tm and Tm[0] == 'scaled': sc_ = Tm[2]; Tm = Tm[1]
            for hh in (hi1, hi2):
                for ll in (lo1, lo2):
                    need(vsub(vmul(sc_, vsub(hh, ll)), Tm), False, 'overlap')
            ok = False
            for q in range(-6, 7):
                lq, hq = vsub(lo, vmul(-q, x)), vsub(hi, vmul(-q, x))
                if lq in (lo1, lo2) and hq in (hi1, hi2): ok = True; break
            if not ok: raise Fail('union endpoints')
            NB = echelon(list(B1) + list(B2))
            if not (lat_sub(B, NB) and lat_sub(NB, B)): raise Fail('union period')
        W.append((lo, hi, B))
    Bg = echelon([x])
    for n, info in zip(D['gsteps'], D['ginfo']):
        lo, hi, B = W[n]
        Tm = threshold(B, Bg, info); sc_ = 1
        if isinstance(Tm, tuple) and Tm and Tm[0] == 'scaled': sc_ = Tm[2]; Tm = Tm[1]
        need(vsub(vmul(sc_, vsub(hi, lo)), Tm), False, 'global step')
        Bg = echelon(list(Bg) + list(B))
    Bz = echelon(list(Bg) + Zs)
    if C['kind'] == 'u':
        if not in_lattice(Bz, (0, 1, 0)): raise Fail('final u')
    elif C['kind'] == 'p':
        if not in_lattice(Bz, T.p): raise Fail('final p')
    else: raise Fail('kind')
    return cell

# ---------------- covering ----------------
def covering(cells, region, box, extra_points):
    """verify region subset of union of cells (and of the explicitly handled points)."""
    todo = [region]; n = 0
    while todo:
        Q = todo.pop(); n += 1
        cq = Cell(Q, box)
        if not cq.nonempty: continue
        p = interior_point(cq)
        hit = None
        fp = (float(p[0]), float(p[1]))
        order = sorted(range(len(cells)), key=lambda t: (cells[t].fpt[0] - fp[0]) ** 2 + (cells[t].fpt[1] - fp[1]) ** 2)
        for t in order:
            if cells[t].contains(p): hit = cells[t]; break
        if hit is None:
            if len(cq.V) == 1 and cq.V[0] in extra_points: continue
            if p in extra_points:
                # the sample point is closed exactly; split the piece through it and continue
                for f in ((-p[0].numerator, p[0].denominator, 0), (-p[1].numerator, 0, p[1].denominator)):
                    f = (f[0] * (1 if f[1] or f[2] else 1), f[1], f[2])
                    g = (f[0], f[1], f[2]) if f[1] else (f[0] * 1, 0, f[2])
                    if any(val(g, v) != 0 for v in cq.V):
                        todo.append(Q + [(g, True)]); todo.append(Q + [(vmul(-1, g), True)])
                        break
                else:
                    raise Fail('cannot split at closed point %s' % (p,))
                continue
            raise Fail('uncovered point %s' % (p,))
        acc = list(Q)
        for f, s in hit.cons:
            neg = (vmul(-1, f), not s)
            piece = acc + [neg]
            if Cell(piece, box).nonempty: todo.append(piece)
            acc = acc + [(f, s)]
    return n

def interior_point(cq):
    V = cq.V
    p = (sum(v[0] for v in V) / len(V), sum(v[1] for v in V) / len(V))
    if cq.contains(p): return p
    raise Fail('no interior point')

def forced_period_bfs(i, k, l, d, u, y):
    """connected components of the position graph by BFS (independent of points.py)."""
    S = i + k + l; D = S * d // 3; x = u + d; h = (i + l) * d - D; a = D - i * d; gl = l * d - D
    rng = lambda lo, n: [(lo + t) % x for t in range(n)]
    Uw = rng(0, u) if i > 0 else rng(x - u, u)
    Cw = rng(i * u, i * d); Hw = rng(0, h); Aw = rng(h, a)
    ACw = Aw + Cw; Yw = [ACw[t % len(ACw)] for t in range(y)]; Gw = (Yw + Hw)[:gl]
    adj = [[] for _ in range(x)]
    for P, Q in [(rng(0, i * x), Uw * i + Cw), (rng(0, l * x), Hw + Aw + Uw * l), (Yw + Hw, Gw + Cw + Yw),
                 (Yw + rng(0, k * x) + Gw, Aw + Cw + Yw + Aw + Uw * k)]:
        if len(P) != len(Q): raise Fail('length mismatch in point check')
        for p, q in zip(P, Q): adj[p].append(q); adj[q].append(p)
    comp = [-1] * x; c = 0
    for s0 in range(x):
        if comp[s0] >= 0: continue
        comp[s0] = c; st = [s0]
        while st:
            v = st.pop()
            for t in adj[v]:
                if comp[t] < 0: comp[t] = c; st.append(t)
        c += 1
    for g in range(1, x + 1):
        if x % g == 0 and all(comp[t] == comp[(t + g) % x] for t in range(x)): return g, x

def check_point(T, p):
    u, y = F(p[0]), F(p[1])
    w0, u0, y0 = p[2]
    if gcd(gcd(w0, u0), y0) != 1 or F(u0, w0) != u or F(y0, w0) != y: raise Fail('bad primitive vector')
    d0 = T.kap * w0
    g0, x0 = forced_period_bfs(T.i, T.k, T.l, d0, u0, y0)
    p0 = (T.i + T.l - 2 * T.k) * d0 // 3
    if u0 % g0 and p0 % g0: raise Fail('point not closed %s' % (p,))
    return (u, y)

def main(fn):
    Dd = json.load(open(fn)); i, k, l = Dd['tuple']; Ymax = F(Dd['Ymax'])
    T = Tup(i, k, l)
    umax = F(T.kap, T.c)
    box = [(F(0), F(0)), (umax, F(0)), (umax, Ymax), (F(0), Ymax)]
    cells = []
    for n, C in enumerate(Dd['certs']):
        try:
            cells.append(check_cert(T, C, box))
        except Fail as e:
            print('CERT', n, 'FAILED:', e); return False
    region = [((0, 1, 0), True), ((T.kap, -T.c, 0), True), ((0, 0, 1), True), ((int(Ymax.numerator), 0, -int(Ymax.denominator)), True)]
    extra = set()
    for p in Dd.get('points', []):
        extra.add(check_point(T, p))
    # sort cells so that the cell of each certificate point is found quickly
    pieces = covering(cells, region, box, extra)
    print((i, k, l), 'certificates verified:', len(cells), 'covering pieces:', pieces, 'extra points:', len(extra), 'OK')
    return True

if __name__ == '__main__':
    for fn in sys.argv[1:]: main(fn)
