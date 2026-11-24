"""Exact fixed-length word-equation test. No string enumeration in the solver."""

from itertools import combinations, product
import unittest


def pattern(q):
    return "b".join("a" * n for n in q)


def image(p, a, b):
    return "".join(a if c == "a" else b for c in p)


def counterexample(p, lengths):
    """Return a concrete binary witness, or None if this length tuple forces."""
    x, y, u, v = lengths
    if x == u and y == v and "a" in p and "b" in p:
        return None
    if p.count("a") * (x - u) != p.count("b") * (v - y):
        raise ValueError("unequal expansion lengths")
    words = []
    start = 0
    for n in lengths:
        words.append(list(range(start, start + n)))
        start += n
    parent = list(range(start))

    def root(i):
        while parent[i] != i:
            parent[i] = parent[parent[i]]
            i = parent[i]
        return i

    def refs(side):
        return (i for c in p for i in words[side + int(c == "b")])

    for i, j in zip(refs(0), refs(2)):
        parent[root(i)] = root(j)
    words = [[root(i) for i in w] for w in words]
    for a, b in combinations(words, 2):
        for i, j in zip(a + b, b + a):
            if i != j:
                ones = {i}
                if x == u and y == v:
                    unequal = next(
                        (
                            (s, t)
                            for left, right in ((0, 2), (1, 3))
                            for s, t in zip(words[left], words[right])
                            if s != t
                        ),
                        None,
                    )
                    if unequal is None:
                        continue
                    s, t = unequal
                    if s not in ones and t not in ones:
                        ones.add(s if s != j else t)
                witness = tuple(
                    "".join("1" if k in ones else "0" for k in w) for w in words
                )
                X, Y, U, V = witness
                assert image(p, X, Y) == image(p, U, V)
                assert (X, Y) != (U, V)
                assert any(A + B != B + A for A, B in combinations(witness, 2))
                return witness
    return None


def witnesses(bound=12):
    results = {}
    for q in product(range(3), repeat=4):
        s = sum(q)
        if s > 2 and max(q) > 1:
            continue
        p = pattern(q)
        best = None
        for v in range(1, bound + 1):
            for y in range(1, v + 1):
                for u in range(1, v + 1):
                    for x in range(1, v + 1):
                        if s * (x - u) != 3 * (v - y):
                            continue
                        lens = (x, y, u, v)
                        if best and sum(lens) >= sum(map(len, best)):
                            continue
                        w = counterexample(p, lens)
                        if w:
                            best = w
        results[q] = best
    return results


class Tests(unittest.TestCase):
    def test_against_literal_enumeration(self):
        for p in ("aabbaba", "abbba", "babbb", "bbb", "abbb", "babab"):
            for lens in product(range(4), repeat=4):
                x, y, u, v = lens
                if p.count("a") * (x - u) != p.count("b") * (v - y):
                    continue
                choices = [["".join(w) for w in product("01", repeat=n)] for n in lens]
                expected = any(
                    image(p, *r[:2]) == image(p, *r[2:])
                    and r[:2] != r[2:]
                    and any(a + b != b + a for a, b in combinations(r, 2))
                    for r in product(*choices)
                )
                self.assertEqual(
                    counterexample(p, lens) is not None, expected, (p, lens)
                )

    def test_cube_transfer(self):
        words = ["".join(w) for n in range(5) for w in product("01", repeat=n)]
        for p, z in product(words, repeat=2):
            for n in (1, 3, 5):
                value = p * n + z
                if value.startswith(z):
                    q = value[len(z) :]
                    k = q[: len(p)]
                    self.assertEqual(q, k * n)
                    self.assertEqual(p + z, z + k)

    def test_extension_and_boundaries(self):
        for t in range(1, 5):
            for bits in product("01", repeat=t):
                h = "".join(bits)
                for u, y in product(["", h, h * 2], repeat=2):
                    x, v = h * 3 + u, h * 4 + y
                    lhs = image("aabbaba", x, y)
                    rhs = image("aabbaba", u, v)
                    self.assertEqual(lhs, rhs)
                    left = right = 0
                    for e, delta in zip("aabbaba", [3, 6, 2, -2, 1, -3, 0]):
                        left += len(x if e == "a" else y)
                        right += len(u if e == "a" else v)
                        self.assertEqual(left - right, delta * t)
        for m in range(3, 20):
            p = "a" * m + "bbb"
            T = "0" * (3 * m)
            x, y, u, v = (T + "1") * 3, "0" * m, "000", ("1" + T) * m
            self.assertEqual(image(p, x, y), image(p, u, v))
            self.assertLessEqual(max(map(len, (x, y, u))), len(v))
            self.assertNotEqual(x + y, y + x)


if __name__ == "__main__":
    for q, w in witnesses().items():
        print("".join(map(str, q)), w)
    unittest.main()
