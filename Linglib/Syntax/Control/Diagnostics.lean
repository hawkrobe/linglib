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
tests every framework's account is answerable to. A `Profile ι` records which
of an analysis's licensing clauses hold of a construction, over an arbitrary
clause index `ι`; an `Excludes ι` instance says which clause's failure admits
each diagnostic, and `Profile.admits` computes the admitted diagnostics as a
preimage: `admits` is antitone, obligatory control is the empty fiber,
non-obligatory control the full one, and the battery encodes the profile
faithfully (`Profile.admits_injective`). Which configurations admit which
diagnostics varies by theory — [landau-2013] (75)–(79) derives the five from
the two clauses of its OC signature (`Studies/Landau2013.lean`).

## Main definitions

- `Control.Diagnostic`: the observable battery
- `Control.Profile`: clause profiles over an index, with `Profile.admits`
- `Control.Excludes`: the clause each diagnostic is excluded by
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

/-- A profile over an index of licensing clauses: which clauses hold of a
    construction. -/
abbrev Profile (ι : Type*) : Type _ := ι → Bool

namespace Profile

variable {ι : Type*} [Excludes ι] {p q : Profile ι}

/-- Obligatory control: every licensing clause holds. -/
def IsObligatory (p : Profile ι) : Prop := ∀ c, p c

/-- Non-obligatory control: no licensing clause holds. -/
def IsNonObligatory (p : Profile ι) : Prop := ∀ c, ¬ p c

instance [Fintype ι] : DecidablePred (IsObligatory (ι := ι)) :=
  fun _ => inferInstanceAs (Decidable (∀ _, _))

instance [Fintype ι] : DecidablePred (IsNonObligatory (ι := ι)) :=
  fun _ => inferInstanceAs (Decidable (∀ _, _))

/-- The diagnostics a profile admits: those whose excluding clause fails. -/
def admits (p : Profile ι) : Set Diagnostic := excludedBy ⁻¹' {c | ¬ p c}

instance : DecidablePred (· ∈ p.admits) :=
  fun _ => inferInstanceAs (Decidable ¬(_ = true))

/-- The more clauses hold, the fewer diagnostics are admitted. -/
@[gcongr] theorem admits_anti : Antitone (admits (ι := ι)) :=
  fun _ _ h => Set.preimage_mono fun _ hc hc' => hc (h _ hc')

/-- A profile is obligatory control iff it admits nothing. -/
theorem isObligatory_iff_admits_eq_empty : p.IsObligatory ↔ p.admits = ∅ := by
  simp [admits, IsObligatory, Set.eq_empty_iff_forall_notMem,
    (Excludes.surjective (ι := ι)).forall]

/-- A profile is non-obligatory control iff it admits everything. -/
theorem isNonObligatory_iff_admits_eq_univ :
    p.IsNonObligatory ↔ p.admits = Set.univ := by
  simp [admits, IsNonObligatory, Set.eq_univ_iff_forall,
    (Excludes.surjective (ι := ι)).forall]

/-- The battery encodes the profile faithfully: distinct profiles admit
    distinct diagnostic sets. -/
theorem admits_injective : Function.Injective (admits (ι := ι)) := fun p q h => by
  have h' := Set.preimage_injective.2 (Excludes.surjective (ι := ι)) h
  exact funext fun c => by simpa using congrArg (c ∈ ·) h'

end Profile

end Control
