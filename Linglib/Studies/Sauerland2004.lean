import Linglib.Pragmatics.NeoGricean.Basic
import Mathlib.Tactic.DeriveFintype

/-!
# [sauerland-2004] — Scalar Implicatures in Complex Sentences
[sauerland-2004]

Sauerland, U. (2004). Scalar implicatures in complex sentences.
*Linguistics and Philosophy* 27(3): 367–391.

The paper's derivation for disjunction, run through the consistency-gated
algorithm in `Pragmatics/NeoGricean/Basic.lean` (`SecondaryLicensed`,
implementing the paper's (42)/(43), verified p. 383): asserting *A or B*
against the alternatives {A, B, A∧B} yields the primary implicatures
¬KA, ¬KB, ¬K(A∧B). Of the candidate secondary implicatures, K¬(A∧B)
is consistent with the commitments and licensed
(`conj_secondary_licensed`), while K¬A is **blocked**
(`disjunct_secondary_blocked`): K¬A together with K(A∨B) forces KB,
contradicting the primary ¬KB. (The paper frames the same block dually:
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
def propA : DisjWorld → Prop
  | .onlyA => True
  | .both => True
  | _ => False

/-- The second disjunct B. -/
def propB : DisjWorld → Prop
  | .onlyB => True
  | .both => True
  | _ => False

/-- The assertion *A or B*. -/
def disj : DisjWorld → Prop
  | .neither => False
  | _ => True

/-- The conjunctive alternative *A and B*. -/
def conj : DisjWorld → Prop
  | .both => True
  | _ => False

instance : DecidablePred propA
  | .onlyA | .both => isTrue trivial
  | .neither | .onlyB => isFalse not_false

instance : DecidablePred propB
  | .onlyB | .both => isTrue trivial
  | .neither | .onlyA => isFalse not_false

instance : DecidablePred disj
  | .neither => isFalse not_false
  | .onlyA | .onlyB | .both => isTrue trivial

instance : DecidablePred conj
  | .both => isTrue trivial
  | .neither | .onlyA | .onlyB => isFalse not_false

end DisjWorld

open DisjWorld

/-- The scalar alternatives to *A or B*: each disjunct and the
conjunction. -/
def orAlts : List (DisjWorld → Prop) := [propA, propB, conj]

/-- **The licensed secondary implicature**: K¬(A∧B) is consistent with
the assertion and all primary implicatures — witnessed by the state
considering exactly `onlyA` and `onlyB` possible. This is the "not
both" inference of *A or B*. -/
theorem conj_secondary_licensed : SecondaryLicensed disj orAlts conj := by
  refine ⟨⟨{.onlyA, .onlyB}, ⟨.onlyA, by decide⟩⟩, ⟨by decide, ?_⟩, by decide⟩
  intro ψ hψ
  simp only [orAlts, List.mem_cons, List.not_mem_nil, or_false] at hψ
  rcases hψ with rfl | rfl | rfl <;> decide

/-- **The blocked secondary implicature**: K¬A is inconsistent with the
commitments. From K(A∨B) and K¬A every possible world satisfies B, so
KB holds — contradicting the primary implicature ¬KB. The disjuncts
therefore yield only ignorance inferences, never "not A". -/
theorem disjunct_secondary_blocked : ¬ SecondaryLicensed disj orAlts propA := by
  rintro ⟨e, ⟨hφ, hprim⟩, hsec⟩
  refine hprim propB (by simp [orAlts]) (fun w hw => ?_)
  have hd := hφ w hw
  have hna := hsec w hw
  cases w <;> simp_all [disj, propA, propB]

/-- By the A↔B symmetry of the model, K¬B is blocked identically. -/
theorem disjunct_secondary_blocked' : ¬ SecondaryLicensed disj orAlts propB := by
  rintro ⟨e, ⟨hφ, hprim⟩, hsec⟩
  refine hprim propA (by simp [orAlts]) (fun w hw => ?_)
  have hd := hφ w hw
  have hnb := hsec w hw
  cases w <;> simp_all [disj, propA, propB]

/-- The strengthened reading of *A or B* the algorithm predicts:
assertion plus the licensed "not both", realizable at exactly the
one-disjunct worlds. -/
theorem strengthened_or_realizable :
    ∃ w, disj w ∧ ¬ conj w := ⟨.onlyA, trivial, not_false⟩

end Sauerland2004
