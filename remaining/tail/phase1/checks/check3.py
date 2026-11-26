# Independent checker for the (0,1,l), l >= l0, certificates written by cover3.py.
# Imports nothing from engine_n.py, sys01.py or cover3.py.
# Variables (d,u,y,D); cells are checked in the section D = 1 (a compact 3-dimensional polytope).
import sys, json
from fractions import Fraction as F
from itertools import product, combinations

NV = 4
Z4 = (0, 0, 0, 0)
def vadd(a, b): return tuple(p + q for p, q in zip(a, b))
def vsub(a, b): return tuple(p - q for p, q in zip(a, b))
def vmul(c, a): return tuple(c * p for p in a)

# ---------- integer lattices ----------
def echelon(vs):
    rows = [list(v) for v in vs if any(v)]
    out = []
    for col in range(NV):
        while True:
            nz = [r for r in rows if r[col] != 0]
            if len(nz) <= 1: break
            nz.sort(key=lambda r: abs(r[col])); p = nz[0]
            for r in nz[1:]:
                q = r[col] // p[col]
                for t in range(NV): r[t] -= q * p[t]
        nz = [r for r in rows if r[col] != 0]
        if nz:
            p = nz[0]
            if p[col] < 0: p = [-a for a in p]
            out.append(tuple(p))
        rows = [r for r in rows if r[col] == 0 and any(r)]
    return out

def in_lattice(B, t):
    t = list(t)
    for r in B:
        c = next(j for j in range(NV) if r[j])
        if any(t[j] for j in range(c)): return False
        if t[c] % r[c]: return False
        q = t[c] // r[c]; t = [a - q * b for a, b in zip(t, r)]
    return not any(t)

def lat_sub(B1, B2): return all(in_lattice(B2, r) for r in B1)
def lat_eq(B1, B2): return lat_sub(B1, B2) and lat_sub(B2, B1)

# ---------- geometry in the section D = 1 ----------
def val(f, p): return f[0] * p[0] + f[1] * p[1] + f[2] * p[2] + f[3]

def det3(M):
    return (M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1]) - M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0])
            + M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]))

def meet(f, g, h):
    M = [list(f[:3]), list(g[:3]), list(h[:3])]; b = [-f[3], -g[3], -h[3]]
    dt = det3(M)
    if dt == 0: return None
    sol = []
    for c in range(3):  # Cramer
        A = [row[:] for row in M]
        for r in range(3): A[r][c] = b[r]
        sol.append(F(det3(A), dt))
    return tuple(sol)

class Cell:
    def __init__(self, cons, box):
        self.cons = cons
        planes = []
        for f, s in list(cons) + list(box):
            if any(f[:3]) and f not in planes: planes.append(f)
        allc = [f for f, s in cons] + [f for f, s in box]
        V = set()
        for a, b, c in combinations(planes, 3):
            p = meet(a, b, c)
            if p is not None and all(val(f, p) >= 0 for f in allc): V.add(p)
        self.V = list(V)
        self.nonempty = bool(self.V) and all(not (s and all(val(f, v) == 0 for v in self.V)) for f, s in cons)
        if self.nonempty and len(self.V) == 1:
            self.nonempty = all(val(f, self.V[0]) > 0 for f, s in cons if s)

    def implies(self, f, strict):
        if not any(f): return not strict
        vs = [val(f, v) for v in self.V]
        if any(x < 0 for x in vs): return False
        if not strict: return True
        Zv = [v for v, x in zip(self.V, vs) if x == 0]
        if not Zv: return True
        if len(Zv) == len(self.V): return False
        return any(s and all(val(g, z) == 0 for z in Zv) for g, s in self.cons)

    def contains(self, p):
        return all((val(f, p) > 0) if s else (val(f, p) >= 0) for f, s in self.cons)

# ---------- the weakened (0,1,l) system, derived afresh ----------
class Fam:
    def __init__(self, l0, n0):
        self.l0, self.n0 = l0, n0
        self.x = (1, 1, 0, 0); self.u = (0, 1, 0, 0); self.y = (0, 0, 1, 0); self.D = (0, 0, 0, 1)
        self.h = (-1, 0, 0, 2); self.p = (-1, 0, 0, 1); self.d = (1, 0, 0, 0)

    def relations(self, pt):
        """returns [(relations of an identity, sign conditions it needs)]"""
        x, u, y, D, h = self.x, self.u, self.y, self.D, self.h
        base = []
        def mkcmp(req):
            def cmp(f):
                v = val(f, pt)
                if not any(f): return 0
                if v > 0: req.append((f, True)); return 1
                if v < 0: req.append((vmul(-1, f), True)); return -1
                req.append((f, False)); req.append((vmul(-1, f), False)); return 0
            return cmp
        cmp0 = mkcmp(base)
        A = (h, D); H = (Z4, h); X = (Z4, x); U = (self.d, u)
        # Y = prefix of A^omega of length y
        q = 0
        while cmp0(vsub(y, vmul(q + 1, D))) >= 0: q += 1
        Y = [A] * q + prefix([A], vsub(y, vmul(q, D)), cmp0)
        G = prefix(Y + [H], h, cmp0)
        n0 = self.n0
        eqs = [([(vmul(-n0, u), vmul(n0 - 1, u))], [(vmul(-(n0 - 1), u), vmul(n0 - 1, u))]),
               (Y + [H], G + Y),
               (Y + [X] + G, [A] + Y + [A, U])]
        out = []
        for L, R in eqs:
            req = list(base)
            out.append((refine(L, R, mkcmp(req), x), req))
        return out

def prefix(bl, n, cmp):
    out = []; acc = Z4
    for s, L in bl:
        r = vsub(n, acc)
        if cmp(r) <= 0: break
        if cmp(vsub(L, r)) >= 0: out.append((s, r)); break
        out.append((s, L)); acc = vadd(acc, L)
    return out

def refine(L, R, cmp, x):
    cl = [Z4]; cr = [Z4]
    for s, n in L: cl.append(vadd(cl[-1], n))
    for s, n in R: cr.append(vadd(cr[-1], n))
    il = ir = 0; pos = Z4; rels = []
    while il < len(L) and ir < len(R):
        el, er = cl[il + 1], cr[ir + 1]
        sg = cmp(vsub(el, er))
        nxt = el if sg < 0 else er
        rels.append((vadd(L[il][0], vsub(pos, cl[il])), vadd(R[ir][0], vsub(pos, cr[ir])), vsub(nxt, pos)))
        pos = nxt
        if sg <= 0: il += 1
        if sg >= 0: ir += 1
    def xm(f):
        if f[1] % x[1]: return None
        j = f[1] // x[1]
        return j if vmul(j, x) == f else None
    out = []
    for a, b, n in rels:
        if out:
            a0, b0, n0 = out[-1]
            if xm(vsub(a, vadd(a0, n0))) is not None and xm(vsub(b, vadd(b0, n0))) is not None:
                out[-1] = (a0, b0, vadd(n0, n)); continue
        out.append((a, b, n))
    return out

class Fail(Exception): pass

def xmult(f, x):
    if f[1] % x[1]: return None
    j = f[1] // x[1]
    return j if vmul(j, x) == f else None

def check_cert(T, C, box):
    cons = [(tuple(F(a) for a in f), s) for f, s in C['cons']]
    cons = [(tuple(int(a) if a.denominator == 1 else a for a in f), s) for f, s in cons]
    cell = Cell(cons, box)
    if not cell.nonempty: raise Fail('empty cell')
    pt = tuple(F(a) for a in C['pt'])
    if not cell.contains(pt): raise Fail('point not in cell')
    def need(f, s, why):
        if not cell.implies(tuple(f), s): raise Fail('not implied: %s %s %s' % (why, f, s))
    byeq = T.relations(pt)
    D = C['deriv']; x = T.x
    R = [(tuple(a), tuple(b), tuple(L)) for a, b, L in D['rels']]
    def zero_on_cell(f): return cell.implies(f, False) and cell.implies(vmul(-1, f), False)
    def subrel(r, r2):
        a, b, L = r; a2, b2, L2 = r2
        if r == r2: return True
        for j1 in range(-3, 4):
            t0 = vsub(vsub(a, a2), vmul(j1, x))
            if not cell.implies(t0, False) or not cell.implies(vsub(vsub(L2, t0), L), False): continue
            for j2 in range(-3, 4):
                if zero_on_cell(vsub(vsub(vsub(b, b2), vmul(j2, x)), t0)): return True
        return False
    for r in R:
        a, b, L = r
        if any(zero_on_cell(vsub(vsub(b, a), vmul(j, x))) for j in range(-6, 7)): continue
        ok = False
        for rels, rq in byeq:
            if any(subrel(r, r2) for r2 in rels) and all(cell.implies(f, s) for f, s in rq): ok = True; break
        if not ok: raise Fail('relation not derived on the whole cell: %s' % (r,))
    Zs = [tuple(z) for z in C.get('zeros', [])]
    for z in Zs: need(z, False, 'zero'); need(vmul(-1, z), False, 'zero')
    def bound_ok(B, b):
        b = tuple(b)
        if not in_lattice(echelon(list(B) + Zs), b): raise Fail('bound not in lattice')
        need(b, True, 'bound positive'); return b
    def threshold(B1, B2, info):
        cs = info['case']
        B1z = echelon(list(B1) + Zs); B2z = echelon(list(B2) + Zs)
        if cs == 'sub2':
            if not lat_sub(B2z, B1z): raise Fail('sub2')
            return bound_ok(B2, info['b2'])
        if cs == 'sub1':
            if not lat_sub(B1z, B2z): raise Fail('sub1')
            return bound_ok(B1, info['b1'])
        t = vadd(bound_ok(B1, info['b1']), bound_ok(B2, info['b2']))
        if cs == 'gen': return t
        if cs == 'rank1':
            f = tuple(info['f'])
            if len(Zs) > 1: raise Fail('rank1 with several zeros')
            if not lat_eq(echelon(list(B1) + list(B2) + Zs), echelon([f] + Zs)): raise Fail('rank1 lattice')
            need(f, True, 'rank1 generator'); return vsub(t, f)
        raise Fail('case')
    W = []
    Bg = echelon([x]); gi = 0; gsteps = list(zip(D['gsteps'], D['ginfo']))
    def apply_global(k):
        nonlocal Bg, gi
        while gi < k:
            n, info = gsteps[gi]
            lo, hi, B = W[n]
            need(vsub(vsub(hi, lo), threshold(B, Bg, info)), False, 'global')
            Bg = echelon(list(Bg) + list(B)); gi += 1
    for w in D['wins']:
        lo, hi = tuple(w['lo']), tuple(w['hi']); B = echelon([tuple(b) for b in w['B']]); pv = w['prov']
        if pv[0] == 'rel':
            a, b, L = R[pv[1]]
            s2 = vsub(vsub(b, a), vmul(pv[2], x))
            if pv[3] > 0: need(s2, True, 'shift'); lo0, hi0, per = a, vadd(vadd(a, L), s2), s2
            else: need(vmul(-1, s2), True, 'shift'); lo0, hi0, per = vadd(a, s2), vadd(a, L), vmul(-1, s2)
            q = xmult(vsub(lo, lo0), x)
            if q is None or vsub(hi, hi0) != vmul(q, x): raise Fail('window endpoints')
            if not lat_eq(B, echelon([per])): raise Fail('window period')
        else:
            lo1, hi1, B1 = W[pv[1]]; lo2, hi2, B2 = W[pv[2]]
            if isinstance(pv[3], list):
                # uniform mode: shift by an element of the global lattice known at this point
                apply_global(pv[5])
                j = tuple(pv[3])
                if any(j) and not in_lattice(Bg, j): raise Fail('shift not in global lattice')
                lo2 = vadd(lo2, j); hi2 = vadd(hi2, j)
            else:
                lo2 = vadd(lo2, vmul(pv[3], x)); hi2 = vadd(hi2, vmul(pv[3], x))
            Tm = threshold(B1, B2, pv[4])
            for hh in (hi1, hi2):
                for ll in (lo1, lo2): need(vsub(vsub(hh, ll), Tm), False, 'overlap')
            if not any(vadd(lo, vmul(q, x)) in (lo1, lo2) and vadd(hi, vmul(q, x)) in (hi1, hi2) for q in range(-6, 7)):
                raise Fail('union endpoints')
            if not lat_eq(B, echelon(list(B1) + list(B2))): raise Fail('union period')
        W.append((lo, hi, B))
    apply_global(len(gsteps))
    Bz = echelon(list(Bg) + Zs)
    if C['kind'] == 'u' and not in_lattice(Bz, T.u): raise Fail('final u')
    if C['kind'] == 'p' and not in_lattice(Bz, T.p): raise Fail('final p')
    if C['kind'] not in ('u', 'p'): raise Fail('kind')
    cell.fpt = tuple(float(a) for a in pt)
    return cell

def covering(cells, region, box, admissible_ok):
    todo = [region]; n = 0; skipped = []
    while todo:
        Q = todo.pop(); cq = Cell(Q, box)
        if not cq.nonempty: continue
        n += 1
        V = cq.V; p = tuple(sum(v[i] for v in V) / len(V) for i in range(3))
        if not cq.contains(p): raise Fail('centroid not in piece')
        fp = tuple(float(a) for a in p)
        hit = None
        for c in sorted(cells, key=lambda c: sum((c.fpt[i] - fp[i]) ** 2 for i in range(3))):
            if c.contains(p): hit = c; break
        if hit is None:
            if admissible_ok(cq): skipped.append(cq); continue
            raise Fail('uncovered piece near %s' % (fp,))
        acc = list(Q)
        for f, s in hit.cons:
            todo.append(acc + [(vmul(-1, f), not s)]); acc = acc + [(f, s)]
    return n, skipped

def main(fn):
    Dd = json.load(open(fn)); l0, n0 = Dd['l0'], Dd['n0']
    T = Fam(l0, n0)
    dmax = F(3, l0 + 1)
    box = [((1, 0, 0, 0), False), ((-1, 0, 0, dmax), False), ((0, 1, 0, 0), False), ((0, -1, 0, dmax / (l0 - 2)), False),
           ((0, 0, 1, 0), False), ((0, 0, -1, 1), False)]
    cells = []
    for i, C in enumerate(Dd['certs']):
        try: cells.append(check_cert(T, C, box))
        except Fail as e: print('CERT', i, 'FAILED', e); return
    region = [((1, 0, 0, 0), True), ((0, 1, 0, 0), True), ((0, 0, 1, 0), True), ((0, 0, -1, 1), True),
              ((-(l0 + 1), 0, 0, 3), False), ((1, -(l0 - 2), 0, 0), True)]
    # pieces left uncovered must contain no admissible point (d = 3/(l+1), l >= l0 integer); listed separately
    from math import gcd
    def classes01(l, d, u, y):
        D_ = (l + 1) * d // 3; x_ = u + d; h_ = 2 * D_ - d; a_ = D_; gl_ = h_
        par = list(range(x_))
        def f(p):
            while par[p] != p: par[p] = par[par[p]]; p = par[p]
            return p
        W_ = lambda lo, n: [(lo + t) % x_ for t in range(n)]
        U_ = W_(x_ - u, u); H_ = W_(0, h_); A_ = W_(h_, a_)
        Y_ = [A_[t % len(A_)] for t in range(y)]; G_ = (Y_ + H_)[:gl_]
        for P_, Q_ in [(W_(0, l * x_), H_ + A_ + U_ * l), (Y_ + H_, G_ + Y_), (Y_ + W_(0, x_) + G_, A_ + Y_ + A_ + U_)]:
            if len(P_) != len(Q_): raise Fail('length')
            for p_, q_ in zip(P_, Q_): par[f(p_)] = f(q_)
        cl = [f(p_) for p_ in range(x_)]
        for g in range(1, x_ + 1):
            if x_ % g == 0 and all(cl[t] == cl[(t + g) % x_] for t in range(x_)): return g
    points = []
    def leftover_ok(cq):
        ds = [v[0] for v in cq.V]; lo, hi = min(ds), max(ds)
        if lo <= 0: return False
        if len(cq.V) > 2: return False      # only points and segments may be left over
        for l in range(l0, int(3 / lo) + 2):
            dl = F(3, l + 1)
            if not (lo <= dl <= hi): continue
            sec = Cell(cq.cons + [((1, 0, 0, -dl), False), ((-1, 0, 0, dl), False)], box)
            if not sec.nonempty: continue
            if len(sec.V) != 1: return False
            d_, u_, y_ = sec.V[0]
            if not ((l - 2) * u_ < d_): continue          # excluded by the true outer bound
            L = 1
            for c_ in (d_, u_, y_): L = L * c_.denominator // gcd(L, c_.denominator)
            iv = [int(c_ * L) for c_ in (d_, u_, y_, F(1))]
            g_ = 0
            for c_ in iv: g_ = gcd(g_, c_)
            d0, u0, y0, D0 = [c_ // g_ for c_ in iv]
            if 3 * D0 != (l + 1) * d0: return False
            g0 = classes01(l, d0, u0, y0)
            if u0 % g0 and ((l - 2) * d0 // 3 if ((l - 2) * d0) % 3 == 0 else 1) % g0:
                return False
            points.append((l, d0, u0, y0, g0))
        return True
    def no_admissible(cq):
        ds = [v[0] for v in cq.V]; lo, hi = min(ds), max(ds)
        # admissible d values in [lo,hi]: 3/(l+1)
        if lo == 0: return False
        lmin = max(l0, int(3 / hi) - 1 - 1); lmax = int(3 / lo) + 1
        for l in range(lmin, lmax + 1):
            dl = F(3, l + 1)
            if lo <= dl <= hi and l >= l0:
                sec = Cell(cq.cons + [((1, 0, 0, -dl), False), ((-1, 0, 0, dl), False)], box)
                if sec.nonempty: return False
        return True
    n, skipped = covering(cells, region, box, leftover_ok)
    for pnt in points: print('  closed by union-find + dilation: l=%d (d,u,y)=(%d,%d,%d), forced period %d' % pnt)
    print('(0,1,l), l >=', l0, ': certificates verified', len(cells), 'covering pieces', n,
          'pieces without admissible points', len(skipped), 'OK')

if __name__ == '__main__':
    main(sys.argv[1])
