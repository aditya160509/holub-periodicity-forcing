# Status of the adjacent-b family

The classification remains open. In the supplied counting convention the corrected counts are **63** through exponent four and **210** through exponent six. Three unrestricted forcing rays account for the correction: (0,0,n,n), (n,0,n,0), and (2n,0,n,n), n positive. The third ray was already explicit in the manuscript. The first two follow by substitution into its length-five seeds. The audit log lists every tuple removed, including the seeds that were still in the original count.

## Descent and the remaining gap

The new shortening lemma removes the same length from corresponding images. The cuts agree in the common word, and the deleted material can be recovered from a retained repeat if the reduced solution is periodic. This gives a finite search at each prescribed positive difference d, both with and without Holub's length condition. For fixed exponents the bounds grow linearly in d. No argument here bounds d or reduces a minimal counterexample to a smaller d. In particular, enumerating d through any fixed limit is insufficient.

The exact residual tuple set in the supplied accounting is implemented by the original exclusions and three ray predicates in checks/audit.py. Minimum counterexamples additionally obey the length bounds in proof.tex and the existing Section 9 exclusions. No full coordinate slice i=0 or l=0 has been closed.

## Methods

* The Levi prefix split alone does not return the same pattern. The descent that does preserve the pattern cuts inside corresponding occurrences using their extreme start displacements.
* The equality-word route supplies two published forcing seeds. The 2018 classification concerns exactly two occurrences of one letter. The 2011 length bound assumes unique overflows and high multiplicity of both letters. A search of Holub's publication list and Hadravová's thesis record did not identify a classification covering the residual family. Sources: [Holub–Sýkora](https://cmuc.karlin.mff.cuni.cz/pdf/cmuc1802/holsyk.pdf), [2011 paper](https://dml.cz/manakin/handle/10338.dmlcz/141422), [thesis record](https://dspace.cuni.cz/handle/20.500.11956/8163), [publication list](https://www.karlin.mff.cuni.cz/~holub/publications.html).
* Across the suffix-prefix join of two copies of the equation, Fine–Wilf uses the sum of the outer exponents. A second Fine–Wilf test needs only part of the second V inside the initial X-run. Both are conditional.
* Padded B, C, D and 0010 seeds are covered by the manuscript reductions and the balanced-prefix argument recorded in proof.tex. Padding a forcing ray preserves forcing. None of these descendant checks removes an additional adjacent-b tuple.

## Checks

Run python3 checks/audit.py. Its union-find test imposes only the local overlap equalities, allowing genuinely nonconstant test words. The direct border test enumerates actual binary words. checks/free6-rerun.log is the output of the existing genfree.cpp at exponent six and image length thirty, over both length orientations, without the maximum-length restriction. An unrestricted absence also covers the restricted search. These checks do not certify unbounded lengths.
