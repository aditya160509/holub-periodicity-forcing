# Final pass on the Holub tail: certified Fine–Wilf covering (26 Nov 2026)

## Result
All 18 tuples left open at exponents ≤ 6 are proved. These include the four open at exponents ≤ 4: (0,1,3), (0,1,4), (1,1,3) and (1,1,4). The proof is computer-assisted, with a finite certificate and an independent checker.

- Exponents ≤ 4: **625/625 settled**, previously 621/625.
- Exponents ≤ 6: **0 open**, previously 18.

The LaTeX is in `proof.tex`: Lemma tail:rules, Lemma tail:dilation, Lemma tail:longY, Theorem tail:certified, a table, and a remark. It is also appended to `paper/sec13_tail.tex`.

## Idea
The FINAL_PROMPT suggested a cone prover. The earlier `cone2` attempt failed for three reasons: it fitted forms numerically, it used the crude overlap bound P+Q, and its pairwise search blew up. Here the approach is different.

1. **Tracing engine** (`checks/engine.py`):
   - It runs a Fine–Wilf window prover at one rational point (u/w, y/w).
   - Every length is carried as an exact integer linear form in (w,u,y), with d = κw (κ = 3 if 3∤S, else 1).
   - Every comparison the derivation relies on is recorded as a homogeneous linear inequality. Their conjunction is a polyhedral cone on which the same derivation is valid.
2. **Periods are lattices of forms**, not numbers. The period of a window is P_M = gcd of the values of a set M of forms. For two such periods, the Fine–Wilf threshold P1 + P2 − gcd is bounded above by τ(M1, M2):
   - **Nested lattices:** if one lattice contains the other, τ = β(larger period). The pack's notes call this the "exact P+Q−gcd" that cone2 lacked.
   - **Rank one:** if Λ(M1 ∪ M2) = Zf, the gcd is exactly |f|.
   - **Otherwise:** τ = β1 + β2, where β is any positive lattice element (a valid upper bound for the gcd).
3. **Closure:** Π has a period P_Γ with u ∈ Λ(Γ) (so XU = UX), or with p ∈ Λ(Γ) (contradiction by Lemma tail:rp).
4. **Lower-dimensional pieces:**
   - On a line, forms that vanish there are added to every lattice. This leaves every gcd of values unchanged.
   - This closed two lines: w = u + 2y for (0,1,3), which accumulates at u → 0, and y = w + 3u for (0,2,5). On these lines the full-dimensional lattices miss u only through the line relation.
5. **Exact covering** (`checks/cover.py`):
   - Certify a sample point, subtract its cone exactly (rational polygon arithmetic with open and closed edges), and recurse on the rest.
   - It terminates on all 18 tuples.
   - Single points left over are closed by exact union-find at the primitive integer vector on their ray, plus the **dilation lemma**: at tP0 the position graph is t interleaved copies of the graph at P0.
6. **Bounded region:** u/w < κ/c by the outer bound. For y/w ≥ Y*, Lemma tail:twoper(iii) closes, or Lemma tail:013 for (0,1,3); see Lemma tail:longY.

## Verification
- `checks/check_certs.py` is an independent checker. It does not import engine.py or cover.py. It has its own geometry, its own lattice code, and its own derivation of the relations from the four identities (via common refinement of breakpoints).
  - For each certificate it checks that every relation used is derived (or is a subrelation of one, or holds trivially by x-periodicity) under sign conditions implied on the cell.
  - It checks every (W1)/(W2)/(G)/(C) step. Stored bound forms β are verified to lie in the lattice and to be positive on the cell, with exact vertex and edge handling of strict inequalities.
  - It re-verifies the covering by its own recursive subdivision, and recomputes the exceptional points by BFS on the position graph.
- Soundness tests against exact union-find of the reduced system (`sound.py`, `sound_line.py`):
  - Every claimed period was checked at random integer points, and at other integer points of each certificate's cone.
  - This included weakened systems with one identity dropped, so that genuinely nonforcing points exist.
  - Result: 0 unsound claims.
- `membership.py`: 18,888 random and special rational points for (0,1,4), including the winprover's problem rays t·(9,4,6) and t·(9,4,7); all were inside certified cells.

## Counts (`checks/summary.txt`)
- 23,273 certificates in total, 25 of them on lines (vanishing forms).
- 1 exact ray point: (2,1,5) at (w,u,y) = (5,1,41), where the forced period is 1.
- All 18 coverings were re-verified by `check_certs.py`.
- Largest: (1,2,5), with 4,448 cones. Smallest: (2,2,6), with 165.
- Reproduce one tuple with `python3 cover.py i k l Ymax covikl.json; python3 points.py covikl.json; python3 check_certs.py covikl.json`. The Ymax values are in the table and in runall2.sh.

## Still open
- **Exponents ≤ 6:** nothing.
- **The family (i,0,k,ℓ) for arbitrary exponents** is still infinite. The residual region is k < ℓ, 2i ≤ k+ℓ, 2k−i−ℓ ≤ 2, i+ℓ ≠ 2k, outside the proved families. By a coarse count there are 66 residual tuples with exponent 7 or 8 (117 with exponents ≤ 8, versus 51 with exponents ≤ 6, before removing the tuples already closed by Theorem tail:general and the like).
  - The method applies verbatim to every residual tuple up to exponent 10. It needs |m| ≤ i+ℓ−2 and the long-Y lemma, which hold except for (0,1,3), (0,2,3), (0,3,4) and (1,1,2), all already proved.
  - So any finite range can be done by running `runall2.sh`-style batches, at about 1–3 minutes per tuple to generate and 1–5 minutes to check.
  - A uniform proof for all exponents needs a different idea: for example, a parametric version in which the exponents are also variables.
- **Padded descendants** (REMAINING-WORK step 2) and the **write-up consistency check against map4** (step 3) are unchanged.
