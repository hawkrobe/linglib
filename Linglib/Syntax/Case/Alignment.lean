/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Syntax.Case.Basic
public import Linglib.Syntax.Clause.ArgumentRole

/-!
# Alignment

A marking of the argument roles, by case, agreement or constituent order, is a function out of
`ArgumentRole`, and its alignment is which of the three core roles S, A and P it identifies,
the kernel of the marking on the core roles ([comrie-1978], [dixon-1994]). A three-element set
has five partitions, so a marking has one of five alignments: neutral, accusative, with S
marked like A, ergative, with S marked like P, horizontal, with A marked like P, and tripartite.
The case labels a marking uses are a further dimension: the Mayan non-perfective pattern with
Set A on every subject and the Kaqchikel progressive with Set A on the object are accusative
alignments in genitive rather than nominative clothing.

## Main declarations

* `Alignment.IsNeutral`, `Alignment.IsAccusative`, `Alignment.IsErgative`,
  `Alignment.IsHorizontal`, `Alignment.IsTripartite`: the five alignments of a marking, one of
  which every marking has (`Alignment.marking_cases`).
* `Alignment.accusative`, `Alignment.ergative`, `Alignment.tripartite`,
  `Alignment.extendedErgative`, `Alignment.invertedErgative`: the canonical case markings.
* `Alignment.AlignmentType`: the observational classification of WALS chapters 98 to 100
  ([comrie-2013]), with `AlignmentType.MarksAgent` and `AlignmentType.MarksPatient`; a split
  conditioned by tense, aspect or a nominal hierarchy is a function into it.

## Implementation notes

The alignment predicates read the three core roles only. The values a canonical marking gives
the ditransitive roles R and T, a dative recipient in the accusative marking and the theme with
the patient elsewhere, are placeholders with no audit trail, and no consumer reads them.
`AlignmentType.active`, the split-S systems, identifies no fixed pair of roles and so is not the
alignment of a single marking.

## References

* [comrie-1978]
* [comrie-2013]
* [coon-2013]
* [dixon-1994]
* [imanishi-2014]
* [imanishi-2020]
* [scott-2023]
-/

@[expose] public section

namespace Alignment

variable {κ : Type*} (m : ArgumentRole → κ)

/-- The marking treats S, A and P alike. -/
def IsNeutral : Prop := m .S = m .A ∧ m .S = m .P

/-- The marking treats S like A and unlike P. -/
def IsAccusative : Prop := m .S = m .A ∧ m .S ≠ m .P

/-- The marking treats S like P and unlike A. -/
def IsErgative : Prop := m .S = m .P ∧ m .S ≠ m .A

/-- The marking treats A like P and unlike S. -/
def IsHorizontal : Prop := m .A = m .P ∧ m .S ≠ m .A

/-- The marking treats S, A and P all differently. -/
def IsTripartite : Prop := m .S ≠ m .A ∧ m .S ≠ m .P ∧ m .A ≠ m .P

section
variable [DecidableEq κ]

instance : Decidable (IsNeutral m) := inferInstanceAs (Decidable (_ ∧ _))
instance : Decidable (IsAccusative m) := inferInstanceAs (Decidable (_ ∧ _))
instance : Decidable (IsErgative m) := inferInstanceAs (Decidable (_ ∧ _))
instance : Decidable (IsHorizontal m) := inferInstanceAs (Decidable (_ ∧ _))
instance : Decidable (IsTripartite m) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

end

/-- Every marking has one of the five alignments, the five partitions of a three-element
set. -/
theorem marking_cases :
    IsNeutral m ∨ IsAccusative m ∨ IsErgative m ∨ IsHorizontal m ∨ IsTripartite m := by
  unfold IsNeutral IsAccusative IsErgative IsHorizontal IsTripartite
  by_cases h₁ : m .S = m .A <;> by_cases h₂ : m .S = m .P <;> by_cases h₃ : m .A = m .P <;>
    simp_all

variable {m}

/-- No marking is accusative and ergative at once, since it identifies S with at most one of A
and P. -/
theorem IsAccusative.not_isErgative (h : IsAccusative m) : ¬ IsErgative m := fun h' ↦ h.2 h'.1

theorem IsErgative.not_isAccusative (h : IsErgative m) : ¬ IsAccusative m := fun h' ↦ h.2 h'.1

/-! ### Canonical case markings -/

/-- The accusative marking: S and A nominative, P accusative. -/
def accusative : ArgumentRole → Case
  | .S | .A => .nom
  | .P | .T => .acc
  | .R => .dat

/-- The ergative marking: A ergative, S and P absolutive. -/
def ergative : ArgumentRole → Case
  | .A => .erg
  | .S | .P | .R | .T => .abs

/-- The tripartite marking: A ergative, P accusative, S absolutive, as in San Juan Atitán Mam
([scott-2023]) and several Australian languages ([dixon-1994]). -/
def tripartite : ArgumentRole → Case
  | .A => .erg
  | .S => .abs
  | .P | .R | .T => .acc

/-- The extended-ergative marking of the Mayan non-perfective and aspectless clause: genitive
on S and A, from D under nominalization, absolutive on P ([coon-2013], [imanishi-2020]; the
label is [dixon-1994]'s). -/
def extendedErgative : ArgumentRole → Case
  | .S | .A => .gen
  | .P | .R | .T => .abs

/-- The inverted marking of the Kaqchikel progressive ([imanishi-2014]): absolutive on S and
A, genitive on P, the object being the only Case-less DP of a nominalized clause under the
unaccusative requirement. -/
def invertedErgative : ArgumentRole → Case
  | .S | .A | .R | .T => .abs
  | .P => .gen

theorem isAccusative_accusative : IsAccusative accusative := ⟨rfl, nofun⟩

theorem isErgative_ergative : IsErgative ergative := ⟨rfl, nofun⟩

theorem isTripartite_tripartite : IsTripartite tripartite := ⟨nofun, nofun, nofun⟩

/-- Extended ergativity is accusative alignment in genitive clothing. -/
theorem isAccusative_extendedErgative : IsAccusative extendedErgative := ⟨rfl, nofun⟩

/-- The inverted marking is likewise an accusative alignment. -/
theorem isAccusative_invertedErgative : IsAccusative invertedErgative := ⟨rfl, nofun⟩

/-! ### The observational classification -/

/-- Morphosyntactic alignment type, the classification of WALS chapters 98 to 100
([comrie-2013]): how a language groups S, A and P. -/
inductive AlignmentType where
  /-- S, A and P alike. -/
  | neutral
  /-- S with A, P apart. -/
  | accusative
  /-- S with P, A apart. -/
  | ergative
  /-- S, A and P all distinct. -/
  | tripartite
  /-- Split-S: S is marked like A for some predicates and like P for others. -/
  | active
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- The type marks A apart from S. -/
def AlignmentType.MarksAgent (a : AlignmentType) : Prop := a = .ergative ∨ a = .tripartite

instance (a : AlignmentType) : Decidable a.MarksAgent := inferInstanceAs (Decidable (_ ∨ _))

/-- The type marks P apart from S. -/
def AlignmentType.MarksPatient (a : AlignmentType) : Prop := a = .accusative ∨ a = .tripartite

instance (a : AlignmentType) : Decidable a.MarksPatient := inferInstanceAs (Decidable (_ ∨ _))

end Alignment
