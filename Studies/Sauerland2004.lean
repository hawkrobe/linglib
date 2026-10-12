module

public import Linglib.Pragmatics.NeoGricean.Basic
public import Mathlib.Tactic.DeriveFintype

/-!
# Sauerland (2004): Scalar Implicatures in Complex Sentences

This file formalizes the paper's derivation of the implicatures of disjunction. The paper
separates primary implicatures, that the speaker is not certain of a stronger alternative,
from secondary implicatures, that the speaker is certain the alternative is false, and admits
a secondary implicature only when it is consistent with the assertion and every primary
implicature; the two conditions are `IsSecondaryImplicature` of
`Pragmatics/NeoGricean/Basic`. Asserting *A or B* against the alternatives *A*, *B* and
*A and B* yields the primary implicatures that the speaker is not certain of either disjunct
or of the conjunction. The secondary implicature that the conjunction is false is consistent
with them and arises (`conj_secondary`), while the one that *A* is false is blocked: with the
assertion it would force certainty of *B*, against the primary implicature
(`disjunct_blocked`); the paper puts the block as a conflict with the possibility of *A*
that the assertion and the primary implicature about *B* entail. That "not both" arises but
"not A" does not is the paper's prediction for disjunction, which accounts negating every
stronger alternative cannot make.

## Implementation notes

The worlds are the four combinations of the disjuncts' truth values, so the assertion excludes
only the world in which neither holds.

## References

* [sauerland-2004]
-/

@[expose] public section

namespace Sauerland2004

open NeoGricean

/-- Worlds distinguished by which of the two disjuncts hold. -/
inductive DisjWorld where
  | neither
  | onlyA
  | onlyB
  | both
  deriving DecidableEq, Repr, Fintype

namespace DisjWorld

/-- The first disjunct A. -/
def propA : Set DisjWorld := {.onlyA, .both}

/-- The second disjunct B. -/
def propB : Set DisjWorld := {.onlyB, .both}

/-- The assertion *A or B*. -/
def disj : Set DisjWorld := {.onlyA, .onlyB, .both}

/-- The conjunctive alternative *A and B*. -/
def conj : Set DisjWorld := {.both}

end DisjWorld

open DisjWorld

/-- The scalar alternatives to *A or B*: each disjunct and the
conjunction. -/
def orAlts : Set (Set DisjWorld) := {propA, propB, conj}

/-- **The secondary implicature that arises**: K¬(A∧B) is consistent with
the assertion and all primary implicatures — witnessed by the
strengthened meaning `disj \ conj`, the state considering exactly
`onlyA` and `onlyB` possible. This is the "not both" inference of
*A or B*. -/
theorem conj_secondary : IsSecondaryImplicature disj orAlts conj := by
  rw [isSecondaryImplicature_iff]
  refine ⟨⟨.onlyA, by simp [disj, conj]⟩, ?_⟩
  simp only [orAlts, Set.forall_mem_insert, Set.mem_singleton_iff, forall_eq, Set.subset_def,
    Set.mem_sdiff, disj, conj, propA, propB]
  decide

/-- **The blocked secondary implicature**: K¬A is inconsistent with the
commitments. The strengthened meaning `disj \ propA` entails B, so K¬A
together with K(A∨B) forces KB — contradicting the primary implicature
¬KB (`isSecondaryImplicature_iff`: the single primary ¬KB blocks K¬A).
The disjuncts therefore yield only ignorance inferences, never "not A". -/
theorem disjunct_blocked : ¬ IsSecondaryImplicature disj orAlts propA := λ h =>
  (isSecondaryImplicature_iff.1 h).2 propB (by simp [orAlts])
    (by simp only [Set.subset_def, Set.mem_sdiff, disj, propA, propB]; decide)

/-- By the A↔B symmetry of the model, K¬B is blocked identically, by ¬KA. -/
theorem disjunct_blocked' : ¬ IsSecondaryImplicature disj orAlts propB := λ h =>
  (isSecondaryImplicature_iff.1 h).2 propA (by simp [orAlts])
    (by simp only [Set.subset_def, Set.mem_sdiff, disj, propA, propB]; decide)

/-- The strengthened reading of *A or B* the algorithm predicts:
assertion plus the licensed "not both", realizable at exactly the
one-disjunct worlds. -/
theorem strengthened_or_realizable : (disj \ conj).Nonempty :=
  ⟨.onlyA, by simp [disj, conj]⟩

end Sauerland2004
