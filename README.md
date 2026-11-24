# Holub’s periodicity-forcing problem

**Yes.** Every solution of `XXYYXYX = UUVVUVU` either has `X = U` and `Y = V`, or all four words commute pairwise. This holds for every alphabet, even with empty words and without the length inequalities. In the second case with unequal corresponding lengths, choosing one arbitrary block of length equal to the gcd of the four lengths describes all solutions.

Start with the [paper](manuscript.pdf). Section 2 contains the proof and alignment diagram. [Editable LaTeX](manuscript.tex) and [Lean proof](Holub.lean) are included. The result resolves the specific seven-letter equation. The general four-exponent classification remains incomplete.

## Reproduce the formal proof

Use Lean 4.33.0 and its standard library. No Mathlib dependency is required.

```sh
lean --version
lean -o Holub.olean Holub.lean
LEAN_PATH=. leanchecker -v Holub
```

[Checker output](lean-check.txt) records the axioms of both main declarations. The original equation, the unrestricted version and the supporting lemmas were kernel-checked. There are no placeholders or custom axioms. The gcd formula and the exponent-family extensions are proved in the manuscript.

## Reproduce the computational checks

```sh
c++ -O3 -std=c++17 search.cpp -o search
./search 320
python3 verify.py
```

[Search results](search-results.txt) give the exhaustive count for the main pattern through maximum image length 320. Each reported primitive tuple checks all letters simultaneously using a disjoint-set graph. [Tests](test-results.txt) compare the Python solver to literal enumeration on small lengths. [Small-pattern certificates](small-cases.txt) give actual binary witnesses in the order X, Y, U, V. A line reading “None” means that the search through maximum length 12 with all images nonempty found no witness. The manuscript states the separate mathematical evidence for each claimed positive result.

The literature assessment and AI contribution disclosure are in Section 5 of the paper. External expert review and bibliographic priority remain unverified.
