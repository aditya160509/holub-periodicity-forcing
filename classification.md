# Toward the full answer to Holub's periodicity-forcing problem

Holub (WORDS 2025) asks for all (i,j,k,l) such that X^i Y X^j Y X^k Y X^l = U^i V U^j V U^k V U^l with |X|,|Y|,|U| ≤ |V| forces X=U, Y=V or all four words commuting.

## Conjecture (complete classification)

The tuple is **not** periodicity forcing exactly when it belongs to one of:

| Family | Tuples | Counterexample (any n, m ≥ 1 unless stated) |
|---|---|---|
| A | (i, m, m, m−i), 0 ≤ i ≤ m, m ≥ 0 | X=a, Y=b, U=ε, V=a^i b a^(m−i) (image is V³) |
| B | (m,0,0,0), (0,0,0,m) | m ≥ 3: manuscript family (T=0^{3m}, X=(T1)³, Y=0^m, U=000, V=(1T)^m); m=1,2: explicit witnesses in `families.py`; reversal for (0,0,0,m) |
| C | (n,0,n,n), (n,n,0,n) | X=aⁿbaⁿ, Y=(ba^{2n})^{n−1}b, U=a, V=YaⁿY |
| D | (0,n,2n,0), (0,2n,n,0), (0,2n,0,n), (n,0,2n,0) | same words as C |
| Sporadic | 0010, 0100, 0110, 1111 | explicit witnesses in `families.py` |

Every other tuple forces periodicity.

## What is proved

- **All non-forcing families are proved for every n, m.** Families C and D: since Xⁿ = aⁿYaⁿ and V = YaⁿY, both sides expand to the same word, e.g. for (n,0,n,n) both equal aⁿYaⁿYYaⁿYaⁿYaⁿYaⁿ. All words used are palindromes, so the reversed tuples follow. Length condition: |V| = 2|Y|+n ≥ 2n+1 = |X|. X and U = a do not commute. `families.py` also checks every instance up to n, m = 40.
- **Forcing for (2,0,1,1)** (Holub's simplest unknown case): full proof plus Lean 4 (main manuscript).

## Evidence for the forcing side

- `gen.cpp` computes the most general solution at each fixed length (union-find on letter positions). Every solution is a letter-image of it, so a counterexample exists at those lengths iff the generic one is a counterexample. This is exact, not sampling.
- All 625 tuples with exponents ≤ 4, |V| ≤ 150: exactly the 43 tuples predicted by the conjecture are non-forcing, and no others. The largest witness needed was |V| = 60, far below the bound (`map4.txt`).
- Larger spot checks to |V| ≤ 250: 0360, 0603, 0630, 3060, 5055, 5505, 6066, 0555 non-forcing as predicted; 0220, 0330, 2222, 2333, 1331, 2112, 0550 forcing as predicted.

## Open

A proof that every tuple outside the families forces periodicity. Fixed-length searches cannot establish this; each forcing tuple needs an argument like the (2,0,1,1) proof, or a general reduction.
