import Linglib.Pragmatics.NeoGricean.Basic
import Mathlib.Tactic.DeriveFintype

/-!
# [sauerland-2004] — Scalar Implicatures in Complex Sentences
[sauerland-2004]

Sauerland, U. (2004). Scalar implicatures in complex sentences.
*Linguistics and Philosophy* 27(3): 367–391.

The paper's derivation for disjunction, run through the consistency-gated
algorithm in `Pragmatics/NeoGricean/Basic.lean` (`IsSecondaryImplicature`,
implementing the paper's (42)/(43), verified p. 383): asserting *A or B*
against the alternatives {A, B, A∧B} yields the primary implicatures
¬KA, ¬KB, ¬K(A∧B). Of the candidate secondary implicatures, K¬(A∧B)
is consistent with the commitments and arises (`conj_secondary`),
while K¬A is **blocked** (`disjunct_blocked`): K¬A together with
K(A∨B) forces KB, contradicting the primary ¬KB. (The paper frames the same block dually:
K¬A contradicts the possibility implicature PA entailed by the
assertion plus ¬KB.) This asymmetry — "not both" arises but
"not A" does not — is the paper's signature prediction for disjunction,
unavailable to accounts that negate all stronger alternatives
indiscriminately.

The four-world model `DisjWorld` distinguishes worlds by which
disjuncts hold; the assertion *A or B* excludes only `neither`.
-/

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
theorem disjunct_blocked : ¬ IsSecondaryImplicature disj orAlts propA := fun h =>
  (isSecondaryImplicature_iff.1 h).2 propB (by simp [orAlts])
    (by simp only [Set.subset_def, Set.mem_sdiff, disj, propA, propB]; decide)

/-- By the A↔B symmetry of the model, K¬B is blocked identically, by ¬KA. -/
theorem disjunct_blocked' : ¬ IsSecondaryImplicature disj orAlts propB := fun h =>
  (isSecondaryImplicature_iff.1 h).2 propA (by simp [orAlts])
    (by simp only [Set.subset_def, Set.mem_sdiff, disj, propA, propB]; decide)

/-- The strengthened reading of *A or B* the algorithm predicts:
assertion plus the licensed "not both", realizable at exactly the
one-disjunct worlds. -/
theorem strengthened_or_realizable : (disj \ conj).Nonempty :=
  ⟨.onlyA, by simp [disj, conj]⟩

end Sauerland2004
