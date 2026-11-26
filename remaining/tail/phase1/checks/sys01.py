# The family (0,1,l), l >= l0, as one system in the integer variables (d, u, y, D).
# Lengths: x = d+u, |A| = D, |H| = |G| = h = 2D-d, p = D-d, l*d = 3D-d.
# The suffix U^l of X^l is used only through its last n0 <= l0 copies (linear in u).
# Region (projective): d>0, u>0, y>0, y<D (Lemma tail:astar), 3D-d >= l0*d, (l0-2)u < d.
import engine_n as E
from engine_n import add, sub, sc, neg, iszero

E.setdim(4)

class Sys01(E.System):
    def __init__(self, l0, n0=3):
        self.l0, self.n0 = l0, n0
        self.i, self.k = 0, 1
        self.d = (1, 0, 0, 0)
        self.x = (1, 1, 0, 0)
        self.uvec = (0, 1, 0, 0)
        self.yv = (0, 0, 1, 0)
        self.D = (0, 0, 0, 1)
        self.h = (-1, 0, 0, 2)
        self.a = self.D
        self.gl = self.h
        self.p = (-1, 0, 0, 1)

    def relations(self, P):
        x, u, yv = self.x, self.uvec, self.yv
        C0 = set()
        def ln(w):
            t = E.ZERO
            for a, L in w: t = add(t, L)
            return t
        def cut(w, n, C):
            out = []
            for a, L in w:
                if P.sign(n, C) <= 0: break
                s = P.sign(sub(L, n), C)
                t = n if s > 0 else L
                out.append((a, t)); n = sub(n, t)
            return out
        X = [(E.ZERO, x)]
        U = [(self.d, u)]                       # U = Pi[x-u, x) = Pi[d, d+u)
        H = [(E.ZERO, self.h)]; A = [(self.h, self.D)]
        Y = []
        while P.sign(sub(yv, ln(Y)), C0) > 0: Y = Y + A
        Y = cut(Y, yv, C0)
        G = cut(Y + H, self.gl, C0)
        n0 = self.n0
        # suffix U^{n0} of X^l: Pi[-n0*u + t] = Pi[-(n0-1)*u + t], t < (n0-1)*u
        eqU = ([(sc(-n0, u), sc(n0 - 1, u))], [(sc(-(n0 - 1), u), sc(n0 - 1, u))])
        eqs = [eqU, (Y + H, G + Y), (Y + X + G, A + Y + A + U)]
        R = []
        for lhs, rhs in eqs:
            Ce = set(C0)
            rr = self.align(lhs, rhs, P, Ce)
            R += [(a, b, L, frozenset(Ce)) for a, b, L in rr]
        return R

def region(l0):
    """constraints (form, strict) in (d,u,y,D)"""
    return [((1, 0, 0, 0), True), ((0, 1, 0, 0), True), ((0, 0, 1, 0), True),
            ((0, 0, -1, 1), True),                    # y < D
            ((-(l0 + 1), 0, 0, 3), False),            # 3D >= (l0+1) d
            ((1, -(l0 - 2), 0, 0), True)]             # (l0-2) u < d
