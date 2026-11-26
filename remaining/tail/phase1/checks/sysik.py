# The family (i,k,l) for fixed i,k and all l >= l0, as one system in (d, u, y, D).
# l*d = 3D - (i+k)d, |C| = id, |A| = D - id, h = 2D - kd, |G| = 2D - (i+k)d, p = D - kd.
# The suffix U^l is used only through its last n0 <= l0 copies.
# Region: d,u,y > 0; y < D - id (Lemma tail:astar, needs m >= 0); 3D >= (i+k+l0)d; (i+l0-2)u < d.
import engine_n as E
from engine_n import add, sub, sc

E.setdim(4)

class SysIK(E.System):
    def __init__(self, i, k, l0, n0=3):
        self.i, self.k, self.l0, self.n0 = i, k, l0, n0
        self.d = (1, 0, 0, 0); self.x = (1, 1, 0, 0); self.uvec = (0, 1, 0, 0); self.yv = (0, 0, 1, 0)
        self.D = (0, 0, 0, 1)
        self.h = (-k, 0, 0, 2)
        self.a = (-i, 0, 0, 1)
        self.gl = (-(i + k), 0, 0, 2)
        self.p = (-k, 0, 0, 1)

    def relations(self, P):
        i, k, n0 = self.i, self.k, self.n0
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
        U = [(E.ZERO, u)] if i > 0 else [(self.d, u)]
        C = [(sc(i, u), sc(i, self.d))] if i > 0 else []
        H = [(E.ZERO, self.h)]; A = [(self.h, self.a)]
        T = A + C
        Y = []
        while P.sign(sub(yv, ln(Y)), C0) > 0: Y = Y + T
        Y = cut(Y, yv, C0)
        G = cut(Y + H, self.gl, C0)
        eqs = [(X * i, U * i + C)] if i > 0 else []
        eqs.append(([(sc(-n0, u), sc(n0, u))], U * n0))           # suffix U^{n0} of X^l
        eqs += [(Y + H, G + C + Y), (Y + X * k + G, A + C + Y + A + U * k)]
        R = []
        for lhs, rhs in eqs:
            Ce = set(C0)
            R += [(a, b, L, frozenset(Ce)) for a, b, L in self.align(lhs, rhs, P, Ce)]
        return R

def region(i, k, l0):
    return [((1, 0, 0, 0), True), ((0, 1, 0, 0), True), ((0, 0, 1, 0), True),
            ((-i, 0, -1, 1), True),                       # y < D - id
            ((-(i + k + l0), 0, 0, 3), False),            # 3D >= (i+k+l0) d
            ((1, -(i + l0 - 2), 0, 0), True)]             # (i+l0-2) u < d
