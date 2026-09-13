/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.Set.Image
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.DeriveFintype

/-!
# Control Diagnostics and Profiles

The observable diagnostic battery of control — the antecedence and reading
tests every framework's account is answerable to. A profile is the set of an
analysis's licensing clauses that hold of a construction, over an arbitrary
clause index `ι`; an `Excludes ι` instance says which clause's failure admits
each diagnostic, and `admits` computes the admitted diagnostics as the
preimage of the failing clauses: `admits` is antitone, obligatory control (every
clause holds) is the empty fiber, non-obligatory control the full one, and the
battery encodes the profile faithfully (`admits_injective`). `ofAttested` goes
the other way, from the diagnostics a construction is observed to admit to the
clauses none of them refutes. Which configurations admit which diagnostics
varies by theory — [landau-2013] (75)–(79) derives the five from the two
clauses of its OC signature (`Studies/Landau2013.lean`).

## Main definitions

- `Control.Diagnostic`: the observable battery
- `Control.Excludes`: the clause each diagnostic is excluded by
- `Control.admits`, `Control.ofAttested`: from a profile to its admitted
  diagnostics and back from attested diagnostics to a profile
-/

namespace Control

/-- The observable control diagnostics: the antecedence and reading tests any
    account of a control construction is answerable to. -/
inductive Diagnostic where
  /-- Arbitrary control: a free reading of the controlled element -/
  | arbitraryControl
  /-- Long-distance control: a non-local antecedent -/
  | longDistanceControl
  /-- A non-c-commanding antecedent -/
  | nonCCommandingControl
  /-- A strict reading under VP-ellipsis -/
  | strictEllipsis
  /-- A strict (non-bound-variable) reading under *only* -/
  | strictUnderOnly
  deriving DecidableEq, Repr, Fintype

/-- An index of licensing clauses, together with the clause whose failure
    admits each diagnostic. Surjectivity says every clause is witnessed by
    some diagnostic — what makes the battery a faithful encoding of the
    profile. -/
class Excludes (ι : Type*) where
  /-- The clause whose failure admits each diagnostic. -/
  excludedBy : Diagnostic → ι
  /-- Every clause is witnessed by some diagnostic. -/
  surjective : Function.Surjective excludedBy

export Excludes (excludedBy)

variable {ι : Type*} [Excludes ι] {p q : Set ι} {A : Set Diagnostic}

/-- The diagnostics a profile — the set of clauses holding of a construction —
    admits: those whose excluding clause fails. -/
def admits (p : Set ι) : Set Diagnostic := excludedBy ⁻¹' pᶜ

instance [DecidablePred (· ∈ p)] : DecidablePred (· ∈ admits p) :=
  fun d => decidable_of_iff (excludedBy d ∉ p) Iff.rfl

/-- The more clauses hold, the fewer diagnostics are admitted. -/
@[gcongr] theorem admits_anti : Antitone (admits (ι := ι)) :=
  fun _ _ h => Set.preimage_mono (Set.compl_subset_compl.2 h)

/-- Obligatory control, every clause holding, admits no diagnostic. -/
theorem admits_eq_empty_iff : admits p = ∅ ↔ p = Set.univ := by
  simp [admits, Set.eq_empty_iff_forall_notMem, Set.eq_univ_iff_forall,
    (Excludes.surjective (ι := ι)).forall]

/-- Non-obligatory control, no clause holding, admits every diagnostic. -/
theorem admits_eq_univ_iff : admits p = Set.univ ↔ p = ∅ := by
  simp [admits, Set.eq_univ_iff_forall, Set.eq_empty_iff_forall_notMem,
    (Excludes.surjective (ι := ι)).forall]

/-- The battery encodes the profile faithfully: distinct profiles admit
    distinct diagnostic sets. -/
theorem admits_injective : Function.Injective (admits (ι := ι)) :=
  (Set.preimage_injective.2 Excludes.surjective).comp compl_injective

/-- The profile a set of attested diagnostics determines: the clauses none of
    them refutes. -/
def ofAttested (A : Set Diagnostic) : Set ι := (excludedBy '' A)ᶜ

instance [DecidableEq ι] [DecidablePred (· ∈ A)] :
    DecidablePred (· ∈ ofAttested (ι := ι) A) :=
  fun c => decidable_of_iff (∀ d ∈ A, excludedBy d ≠ c) (by simp [ofAttested])

/-- Attested diagnostics are admitted. -/
theorem subset_admits_ofAttested : A ⊆ admits (ofAttested (ι := ι) A) := by
  rw [admits, ofAttested, compl_compl]
  exact Set.subset_preimage_image _ _

/-- With nothing attested every clause holds. -/
@[simp] theorem ofAttested_eq_univ_iff : ofAttested (ι := ι) A = Set.univ ↔ A = ∅ := by
  rw [ofAttested, Set.compl_univ_iff, Set.image_eq_empty]

end Control
