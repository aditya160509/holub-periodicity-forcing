# Close the isolated failure points of a covering by exact union-find at the primitive
# integer length vector on the ray (dilation lemma: the generic solution at t*P0 is t
# interleaved copies of the generic solution at P0, so a forced period g0 at P0 becomes t*g0).
import sys, json
from fractions import Fraction as F
from math import gcd

def classes(i, k, l, d, u, y):
    S = i + k + l; D = S * d // 3; x = u + d; h = (i + l) * d - D; a = D - i * d; gl = l * d - D
    par = list(range(x))
    def f(p):
        r = p
        while par[r] != r: r = par[r]
        while par[p] != r: par[p], p = r, par[p]
        return r
    def un(p, q): par[f(p)] = f(q)
    W = lambda lo, n: [(lo + t) % x for t in range(n)]
    U = W(0, u) if i > 0 else W(x - u, u)
    C = W(i * u, i * d); H = W(0, h); A = W(h, a)
    T = A + C; Y = [T[t % len(T)] for t in range(y)]; G = (Y + H)[:gl]
    for P, Q in [(W(0, i * x), U * i + C), (W(0, l * x), H + A + U * l), (Y + H, G + C + Y),
                 (Y + W(0, k * x) + G, A + C + Y + A + U * k)]:
        assert len(P) == len(Q)
        for p, q in zip(P, Q): un(p, q)
    return [f(p) for p in range(x)], x

def min_period(cl, x):
    for g in range(1, x + 1):
        if x % g == 0 and all(cl[t] == cl[(t + g) % x] for t in range(x)): return g

def close_point(i, k, l, u, y):
    S = i + k + l; kap = 3 if S % 3 else 1
    L = u.denominator * y.denominator // gcd(u.denominator, y.denominator)
    w0, u0, y0 = L, int(u * L), int(y * L)
    g = gcd(gcd(w0, u0), y0); w0, u0, y0 = w0 // g, u0 // g, y0 // g
    d0 = kap * w0
    cl, x0 = classes(i, k, l, d0, u0, y0)
    g0 = min_period(cl, x0)
    p0 = (i + l - 2 * k) * d0 // 3
    kind = 'u' if u0 % g0 == 0 else ('p' if p0 % g0 == 0 else None)
    return (w0, u0, y0), g0, kind

if __name__ == '__main__':
    for fn in sys.argv[1:]:
        Dd = json.load(open(fn)); i, k, l = Dd['tuple']
        pts = []; bad = 0
        for p, q, dim in Dd['failures']:
            u, y = F(p[0]), F(p[1])
            if dim != 1:
                print(fn, 'failure piece of dimension >0 at', p, 'closure vertices', dim); bad += 1; continue
            P0, g0, kind = close_point(i, k, l, u, y)
            print(fn, 'point', (str(u), str(y)), 'primitive', P0, 'forced period', g0, '->', kind)
            if kind is None: bad += 1
            else: pts.append([str(u), str(y), list(P0), g0, kind])
        Dd['points'] = pts
        json.dump(Dd, open(fn, 'w'))
        print(fn, 'points closed', len(pts), 'unresolved', bad)
