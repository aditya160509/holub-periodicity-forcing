# Tracing Fine--Wilf engine for the reduced tail system of (i,0,k,l).
# Every length is a homogeneous integer linear form in (w,u,y), with d = kap*w
# (kap = 3 if 3 does not divide S, else 1). The engine runs at a rational point
# and records, for every derived fact, the set of linear inequalities it used.
# A fact derived this way holds at every integer point satisfying those inequalities.
from fractions import Fraction as Fr
from math import gcd
from itertools import product

def add(f, g): return tuple(a + b for a, b in zip(f, g))
def sub(f, g): return tuple(a - b for a, b in zip(f, g))
def sc(k, f): return tuple(k * a for a in f)
def neg(f): return tuple(-a for a in f)
def iszero(f): return not any(f)
NV = 3
def setdim(n):
    global NV, ZERO
    NV = n; ZERO = (0,) * n
ZERO = (0, 0, 0)

def normcon(f, strict):
    g = 0
    for a in f: g = gcd(g, abs(a))
    if g == 0: return (ZERO, False)
    return (tuple(a // g for a in f), strict)

class Infeasible(Exception): pass

class Pt:
    def __init__(self, pt): self.pt = tuple(Fr(a) for a in pt)
    def ev(self, f): return sum(c * p for c, p in zip(f, self.pt))
    def sign(self, f, C):
        """sign of f at the point; adds the constraint making it so to C"""
        if iszero(f): return 0
        v = self.ev(f)
        if v > 0: C.add(normcon(f, True)); return 1
        if v < 0: C.add(normcon(neg(f), True)); return -1
        C.add(normcon(f, False)); C.add(normcon(neg(f), False)); return 0

# ---------- integer lattices of forms ----------
def hnf(gens):
    rows = [list(g) for g in gens if any(g)]
    basis = []
    for col in range(NV):
        piv = [r for r in rows if r[col] != 0]; rest = [r for r in rows if r[col] == 0]
        while len(piv) > 1:
            piv.sort(key=lambda r: abs(r[col])); p = piv[0]; new = [p]
            for r in piv[1:]:
                q = r[col] // p[col]; r2 = [a - q * b for a, b in zip(r, p)]
                (new if r2[col] != 0 else rest).append(r2)
            piv = new
        if piv:
            p = piv[0]
            if p[col] < 0: p = [-a for a in p]
            basis.append(tuple(p))
        rows = [r for r in rest if any(r)]
    return tuple(basis)

def pivcol(r):
    for c in range(NV):
        if r[c]: return c

def contains(basis, t):
    t = list(t)
    for r in basis:
        c = pivcol(r)
        if t[c] % r[c]: return False
        q = t[c] // r[c]; t = [a - q * b for a, b in zip(t, r)]
    return not any(t)

def subset(B1, B2):  # lattice(B1) inside lattice(B2)
    return all(contains(B2, r) for r in B1)

def egcd(a, b):
    if b == 0: return (a, 1, 0) if a >= 0 else (-a, -1, 0)
    g, x, y = egcd(b, a % b)
    return g, y, x - (a // b) * y

def rank1_mod(J, z):
    """J: hnf basis of a lattice containing the primitive vector z, of rank 2.
    Returns f with lattice = Z f + Z z, or None."""
    if len(J) != 2: return None
    b1, b2 = J
    # solve z = al*b1 + be*b2 over Q, check integrality
    import fractions
    M = [[b1[c], b2[c]] for c in range(NV)]
    sol = None
    for r1 in range(NV):
        for r2 in range(r1 + 1, NV):
            det = M[r1][0] * M[r2][1] - M[r1][1] * M[r2][0]
            if det:
                al = fractions.Fraction(z[r1] * M[r2][1] - M[r1][1] * z[r2], det)
                be = fractions.Fraction(M[r1][0] * z[r2] - z[r1] * M[r2][0], det)
                sol = (al, be); break
        if sol: break
    al, be = sol
    if al.denominator != 1 or be.denominator != 1: return None
    al, be = int(al), int(be)
    if add(sc(al, b1), sc(be, b2)) != tuple(z): return None
    g, ga, gb = egcd(al, be)
    if g != 1: return None
    # basis change: [[al,be],[-gb,ga]] has determinant al*ga+be*gb = 1
    return add(sc(-gb, b1), sc(ga, b2))

# ---------- the reduced system ----------
class System:
    def __init__(self, i, k, l):
        self.i, self.k, self.l = i, k, l
        S = i + k + l; self.S = S
        self.kap = 3 if S % 3 else 1
        kap = self.kap
        d = (kap, 0, 0); self.d = d
        self.x = (kap, 1, 0)
        self.D = (S * kap // 3, 0, 0)
        self.h = ((i + l) * kap - S * kap // 3, 0, 0)
        self.a = (S * kap // 3 - i * kap, 0, 0)
        self.gl = (l * kap - S * kap // 3, 0, 0)
        m = i + l - 2 * k
        self.p = (m * kap // 3, 0, 0) if (m * kap) % 3 == 0 else None
        self.m = m

    def relations(self, P):
        i, k, l = self.i, self.k, self.l
        x, u = self.x, (0, 1, 0); yv = (0, 0, 1)
        C0 = set()
        def seg(s, L):
            return [(s, L)] if not iszero(L) else []
        def ln(w):
            t = ZERO
            for a, L in w: t = add(t, L)
            return t
        def cut(w, n, C):
            out = []
            for a, L in w:
                if P.sign(n, C) <= 0: break
                s = P.sign(sub(L, n), C)
                t = n if s > 0 else L
                if s == 0: t = L
                out.append((a, t)); n = sub(n, t)
            return out
        X = seg(ZERO, x)
        U = seg(ZERO, u) if i > 0 else seg(sub(x, u), u)
        C = seg(sc(i, u), sc(i, self.d))
        H = seg(ZERO, self.h); A = seg(self.h, self.a)
        T = A + C
        Y = []
        while P.sign(sub(yv, ln(Y)), C0) > 0: Y = Y + T
        Y = cut(Y, yv, C0)
        G = cut(Y + H, self.gl, C0)
        eqs = [(X * i, U * i + C), (X * l, H + A + U * l), (Y + H, G + C + Y),
               (Y + X * k + G, A + C + Y + A + U * k)]
        R = []
        eqs = [e for n, e in enumerate(eqs) if n not in getattr(self, 'drop', ())]
        for lhs, rhs in eqs:
            Ce = set(C0)
            rr = self.align(lhs, rhs, P, Ce)
            R += [(a, b, L, frozenset(Ce)) for a, b, L in rr]
        return R

    def align(self, lhs, rhs, P, C):
        R = []; ii = jj = 0; oi = oj = ZERO
        while ii < len(lhs) and jj < len(rhs):
            a, La = lhs[ii]; b, Lb = rhs[jj]
            ra, rb = sub(La, oi), sub(Lb, oj)
            s = P.sign(sub(ra, rb), C)
            t = rb if s >= 0 else ra
            R.append((add(a, oi), add(b, oj), t))
            oi = add(oi, t); oj = add(oj, t)
            if s <= 0: ii += 1; oi = ZERO
            if s >= 0: jj += 1; oj = ZERO
        # merge consecutive pieces whose positions are contiguous modulo x
        out = []
        for a, b, L in R:
            if out:
                a0, b0, L0 = out[-1]
                if self.multx(sub(a, add(a0, L0))) is not None and self.multx(sub(b, add(b0, L0))) is not None:
                    out[-1] = (a0, b0, add(L0, L)); continue
            out.append((a, b, L))
        return out

    def multx(self, f):  # f == j*x identically?
        x = self.x
        if f[1] % x[1]: return None
        j = f[1] // x[1]
        return j if sc(j, x) == f else None


class Prover:
    def __init__(self, sysm, pt, maxwin=3000, rounds=8, shifts=(-2, -1, 0, 1, 2), zeros=(), uniform=False):
        self.uniform = uniform
        self.S = sysm; self.P = Pt(pt); self.maxwin = maxwin; self.rounds = rounds; self.shifts = shifts
        self.zeros = tuple(zeros)  # forms vanishing on the piece under consideration
        for z in self.zeros: assert self.P.ev(z) == 0
        self.ubcache = {}

    def ub(self, B, C):
        """a lattice element f with 0 < value; gcd(B) <= f. Adds f>0 to C."""
        P = self.P
        key = B
        if key not in self.ubcache:
            B = hnf(B + self.zeros) if self.zeros else B
            best = None
            rng = range(-3, 4)
            for co in product(rng, repeat=len(B)):
                f = ZERO
                for c, r in zip(co, B): f = add(f, sc(c, r))
                v = P.ev(f)
                if v > 0 and (best is None or v < best[0]): best = (v, f)
            self.ubcache[key] = best[1] if best else None
            B = key
        f = self.ubcache[B]
        if f is None: raise Infeasible
        C.add(normcon(f, True))
        return f

    def threshold(self, B1, B2, C, info=None):
        """form T with: overlap >= T implies Fine-Wilf for periods gcd(B1), gcd(B2)."""
        if info is None: info = {}
        Z = self.zeros
        B1z, B2z = hnf(B1 + Z), hnf(B2 + Z)
        if subset(B2z, B1z):  # gcd(B1) | gcd(B2)
            b = self.ub(B2, C); info.update(case='sub2', b2=b); return b
        if subset(B1z, B2z):
            b = self.ub(B1, C); info.update(case='sub1', b1=b); return b
        J = hnf(B1 + B2 + Z)
        # c-multiple case: one lattice is (mod Z) rank one, generated by f, and c*f lies in the other
        for (Ba, Bb, ka, kb) in ((B1, B2, 'b1', 'b2'), (B2, B1, 'b2', 'b1')):
            Baz = hnf(Ba + Z)
            fa = None
            if len(Z) == 0 and len(Baz) == 1: fa = Baz[0]
            elif len(Z) == 1: fa = rank1_mod(Baz, Z[0]) if len(Baz) == 2 else None
            if fa is None: continue
            Bbz = hnf(Bb + Z)
            for cm in range(2, 41):
                if contains(Bbz, sc(cm, fa)):
                    sa = self.P.sign(fa, C)
                    if sa == 0: break
                    fa_pos = sc(sa, fa)          # exact period of Ba
                    bb = self.ub(Bb, C)
                    # P_a + P_b - gcd <= f_a + (1 - 1/cm) * b_b ; scale by cm
                    info.update(case='cmult', fa=fa_pos, bb=bb, cm=cm, which=ka)
                    self._scale = cm
                    return ('scaled', add(sc(cm, fa_pos), sc(cm - 1, bb)), cm)
        b1, b2 = self.ub(B1, C), self.ub(B2, C)
        t = add(b1, b2); info.update(case='gen', b1=b1, b2=b2)
        f = None
        if len(Z) == 0 and len(J) == 1: f = J[0]
        elif len(Z) == 1: f = rank1_mod(J, Z[0])
        if f is not None:
            s = self.P.sign(f, C)
            if s: t = sub(t, sc(s, f)); info.update(case='rank1', f=sc(s, f))
        return t

    def windows_from(self, R):
        P = self.P; x = self.S.x; W = []
        xv = P.ev(x)
        for ri, (a, b, L, dep) in enumerate(R):
            s = sub(b, a)
            j0 = int((P.ev(s) / xv).__floor__())
            for j in ((-1, 0, 1, 2) if self.uniform else (j0, j0 + 1)):
                C = set(dep)
                s2 = sub(s, sc(j, x))
                sg = P.sign(s2, C)
                if sg == 0: continue
                if sg > 0: lo, hi, per = a, add(add(a, L), s2), s2
                else: lo, hi, per = add(a, s2), add(a, L), neg(s2)
                if P.ev(sub(hi, lo)) <= P.ev(per): continue
                W.append(self.normwin(lo, hi, hnf([per]), frozenset(C)) + (('rel', ri, j, sg),))
        return W

    def normwin(self, lo, hi, B, dep):
        if self.uniform: return (lo, hi, B, dep)
        x = self.S.x; q = int((self.P.ev(lo) / self.P.ev(x)).__floor__())
        return (sub(lo, sc(q, x)), sub(hi, sc(q, x)), B, dep)

    def shiftlist(self, Bg):
        if not self.uniform: return self.shifts
        key = Bg
        if getattr(self, '_slk', None) != key:
            out = {ZERO}
            for co in product(range(-1, 2), repeat=len(Bg)):
                f = ZERO
                for c, r in zip(co, Bg): f = add(f, sc(c, r))
                out.add(f)
            self._slk = key; self._sl = sorted(out)
        return self._sl

    def done(self, Bg):
        S = self.S
        B = hnf(Bg + self.zeros)
        if contains(B, S.uvec): return 'u'
        if S.p is not None and contains(B, S.p): return 'p'
        return None

    def run(self, budget=20.0):
        import time
        t_end = time.time() + budget
        P = self.P; S = self.S
        R = S.relations(P)
        W = self.windows_from(R)
        Bg = hnf([S.x]); gdep = frozenset()
        seen = set(); self.R = R; self.W = W; self.gsteps = []; self.ginfo = []
        for rnd in range(self.rounds):
            ch = True
            while ch:
                ch = False
                for wi, (lo, hi, B, dep, prov) in enumerate(W):
                    if subset(B, hnf(Bg + self.zeros)): continue
                    C = set(dep); info = {}
                    try: T = self.threshold(B, Bg, C, info)
                    except Infeasible: continue
                    L_ = sub(hi, lo)
                    if isinstance(T, tuple) and T and T[0] == 'scaled': L_ = sc(T[2], L_); T = T[1]
                    if P.ev(sub(L_, T)) >= 0:
                        C.add(normcon(sub(L_, T), False))
                        Bg = hnf(Bg + B); gdep = gdep | frozenset(C); ch = True
                        self.gsteps.append(wi); self.ginfo.append(info)
                        r = self.done(Bg)
                        if r:
                            for z in self.zeros:
                                gdep = gdep | {normcon(z, False), normcon(neg(z), False)}
                            return r, Bg, gdep
            Bgz = hnf(Bg + self.zeros)
            Wl = [(n,) + w for n, w in enumerate(W) if not subset(w[2], Bgz)]
            new = []
            for n1 in range(len(Wl)):
                id1, lo1, hi1, B1, d1, _ = Wl[n1]
                if time.time() > t_end: return None, Bg, gdep
                for n2 in range(n1 + 1, len(Wl)):
                    id2, lo2_, hi2_, B2, d2, _ = Wl[n2]
                    if subset(B1, B2) and subset(B2, B1):
                        pass
                    for j in self.shiftlist(Bg):
                        if self.uniform:
                            lo2 = add(lo2_, j); hi2 = add(hi2_, j)
                            C = set(d1) | set(d2) | (set(gdep) if any(j) else set())
                        else:
                            lo2 = add(lo2_, sc(j, S.x)); hi2 = add(hi2_, sc(j, S.x))
                            C = set(d1) | set(d2)
                        lo = lo1 if P.ev(lo1) >= P.ev(lo2) else lo2
                        hi = hi1 if P.ev(hi1) <= P.ev(hi2) else hi2
                        ov = sub(hi, lo)
                        if P.ev(ov) <= 0: continue
                        info = {}
                        try: T = self.threshold(B1, B2, C, info)
                        except Infeasible: continue
                        if isinstance(T, tuple) and T and T[0] == 'scaled':
                            cmv = T[2]; T = T[1]
                            ov = sub(sc(cmv, hi), sc(cmv, lo))
                        if P.ev(sub(ov, T)) < 0: continue
                        # record the needed facts
                        C.add(normcon(sub(lo, lo1), False)); C.add(normcon(sub(lo, lo2), False))
                        C.add(normcon(sub(hi1, hi), False)); C.add(normcon(sub(hi2, hi), False))
                        C.add(normcon(sub(ov, T), False))
                        nlo = lo1 if P.ev(lo1) <= P.ev(lo2) else lo2
                        nhi = hi1 if P.ev(hi1) >= P.ev(hi2) else hi2
                        C.add(normcon(sub(lo1, nlo), False)); C.add(normcon(sub(lo2, nlo), False))
                        C.add(normcon(sub(nhi, hi1), False)); C.add(normcon(sub(nhi, hi2), False))
                        NB = hnf(B1 + B2)
                        key = (nlo, nhi, NB)
                        if key in seen: continue
                        seen.add(key)
                        new.append(self.normwin(nlo, nhi, NB, frozenset(c for c in C if any(c[0]))) + (('pair', id1, id2, j, info, len(self.gsteps)),))
                if len(new) > self.maxwin: break
            if not new: break
            W = W + new; self.W = W
            if len(W) > self.maxwin: break
        return None, Bg, gdep
