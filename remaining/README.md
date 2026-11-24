# The remaining family (i,0,k,l): status 24 Nov 2026

Everything else is settled by manuscript Sections 7-8. Left: X^i Y^2 X^k Y X^l = U^i V^2 U^k V U^l.

## Findings
- **Length condition not needed here.** `genfree.cpp` drops |V| >= |X|,|Y|,|U| (lengths up to 40 for exponents <= 4, `free4.txt`; up to 30 for exponents <= 6, `free6.txt`). The only nonforcing j=0 tuples are B, C (1011, 2022, ...), D (1020, 2040, ...), 0010, plus 0020 and 1001, which already have proofs using the length condition. So every open tuple appears to force periodicity unconditionally, and proofs may assume |X| > |U| by symmetry.
- **Reformulation.** By Lemma perred, g, h are nonperiodic. By Holub's two-generator theorem, if Eq(g,h) has two generators then w is in A, C or D. So an open tuple is nonforcing iff w = a^i b^2 a^k b a^l is the primitive single generator of Eq(g,h) for some nonperiodic g, h. This is the "three b's" analogue of Holub-Sykora 2018 (two b's).
- **Proof shape.** Let d = x-u > 0, D = v-y = (i+k+l)d/3. Prefix side: V starts i*d before Y1. Suffix side: V ends l*d after Y3. Reading V from each end gives two occurrences of Y inside V whose offsets differ by |k-2i-2l|*d/3. That difference is 0 exactly on family D's line k = 2(i+l). Off that line, Y gets a period, and Fine-Wilf arguments as in Section 8 should apply, but the case split (signs of 2l-k, k+l-2i, size of D vs y and vs kx) has not been carried out.

## Not done
No proof of any new infinite subfamily yet.
