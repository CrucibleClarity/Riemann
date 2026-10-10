# An Observation Plane for the Riemann Hypothesis: Judgement Completeness and the Open Reading Constraint

Anonymous version, prepared for double-blind review.

## Contents

- `paper/riemann_observation_EN.tex` — LaTeX source
- `paper/riemann_observation_EN.pdf` — compiled paper (11 pages)

## Abstract

The Riemann hypothesis asserts that all non-trivial zeros of the Riemann zeta
function $\zeta$ lie on the critical line $\Re s = 1/2$. This paper proves
nothing; it does two things: it restates this assertion on a newly constructed
observation plane, and it states, item by item, which parts of the restatement
are machine-verified and which remain open. The construction has two steps:
a base-point migration turning the critical line into a unit circle with an
exact mark, and a $45^\circ$ rotation producing fold coordinates. Three
coordinate properties of the projection $d=\sqrt2(\Re s-1/2)$, judgement
completeness of the zero-on-line decision, and the reading-form equivalence of
the Riemann hypothesis are machine-verified (Lean 4, mathlib; 0 error,
0 `sorry`); the universal reading constraint remains open. Section 9
(Verification record and reproduction) lists the files and declaration counts.

## Note

This is the anonymized version of the manuscript. Its references to a
published framework by the author are cited in the third person, as is
standard practice for double-blind review.
