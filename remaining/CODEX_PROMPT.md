# Task: prove the last open family of Holub's periodicity-forcing problem

Work in: "/Users/adityabalaji/Documents/Three Binary Words/2 - Holub Periodicity Forcing"
Read first: paper/manuscript.tex (Sections 2, 5, 7, 8), remaining/README.md, extension/classification.md.
Rules: do not delete or overwrite existing files; write new work in remaining/. Keep every process under ~1 GB RAM.

## Problem
For exponents (i,j,k,l), the equation X^i Y X^j Y X^k Y X^l = U^i V U^j V U^k V U^l "forces periodicity" if every solution has X=U and Y=V, or all four words are powers of one word. Everything is classified except the family j = 0:

    X^i Y Y X^k Y X^l = U^i V V U^k V U^l        (i,0,k,l)

Already settled inside this family:
- k = 0 or i = l = 0
- balanced cases: S = i+k+l = 3m with i = m or i <= 2m <= i+k
- (2,0,1,1)
- the exceptions, which are nonforcing:
  - B: (m,0,0,0), (0,0,0,m)
  - C: (n,0,n,n)
  - D: (n,0,2n,0)
  - 0010
- (0,0,2,0) and (1,0,0,1), which use the length condition

Goal: prove every other (i,0,k,l) forces periodicity.

## Known facts to use
- Search (remaining/genfree.cpp, free4.txt, free6.txt): for exponents <= 6, every open tuple forces periodicity even WITHOUT the length condition |V| >= |X|,|Y|,|U|. So assume x = |X| > |U| = u by symmetry and aim for unconditional proofs.
- Lengths: with d = x-u > 0, v - y = (i+k+l)d/3.
- Prefix side: V starts i*d before the first Y. Suffix side: V ends l*d after the third Y. Reading V from both ends gives two occurrences of Y inside V, with offsets differing by |k-2i-2l|*d/3. That is 0 exactly on family D's line k = 2(i+l). Off it, Y gets a period.
- Tools that already worked (Section 8 of the manuscript):
  - Fine-Wilf
  - primitive roots (if a factor of R^w of length >= |R|+c has period c, then |R| divides c)
  - overlapping squares (VV vs YY)
  - finishing step: from |W| = 3Q + m*u, get |R| | u
- Lemma perred: periodic morphisms are already excluded. By Holub's two-generator theorem, an open tuple is nonforcing iff a^i b^2 a^k b a^l is the single generator of Eq(g,h) for nonperiodic g,h (the three-b analogue of Holub-Sykora 2018, references/holub-sykora-2018.pdf).

## What to do
1. Split by the signs of k-2i-2l, 2l-k and k+l-2i, and by D=v-y compared with y and with k*x. Prove each region with written Fine-Wilf arguments in the style of Section 8. Start with the easiest infinite subfamilies (e.g. i = 0: Y Y X^k Y X^l; or l = 0) and grow from there.
2. After every claimed lemma, test it: write a brute-force check (union-find generic solution as in extension/gen.cpp) over all tuples with exponents <= 6 and lengths <= 30. Run it with and without the length condition. Any counterexample means the lemma is wrong.
3. Be skeptical. Never claim a case is proved unless every step is written and checked. Say clearly which regions are proved, which are open, and why.

## Output
- remaining/proof.tex: LaTeX section(s) ready to paste into the manuscript as Section 9, with full proofs
- remaining/checks/: scripts and logs
- remaining/STATUS.md: which tuples or regions are proved, which are open, and the exact gap if not finished
