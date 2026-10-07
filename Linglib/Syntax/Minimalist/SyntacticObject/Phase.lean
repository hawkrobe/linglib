/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.SyntacticObject.Selection
public import Linglib.Syntax.Minimalist.SyntacticObject.Term

/-!
# Phases

The phases of [marcolli-chomsky-berwick-2025] §1.14, after [chomsky-2000], with the selection head
`SyntacticObject.selHead` as head function. A lexical item heads a phase when it projects, and its
complement is the sister it projects over. The phase is what lies within the terms the head
heads; its interior is what lies within the complement, the domain the Phase Impenetrability
Condition freezes; and its edge is the rest of the phase, the head and what is merged above it.

## Main definitions

* `SyntacticObject.IsPhaseHead`, `SyntacticObject.IsComplementOf`: a lexical item projects, and
  the sister it projects over.
* `SyntacticObject.WithinProjection`, `SyntacticObject.WithinComplement`: a term lies within the
  projection or the complement of a head.
* `SyntacticObject.phase`, `SyntacticObject.phaseInterior`, `SyntacticObject.phaseEdge`: the
  phase of a head, its interior, and its edge.

## Main statements

* `SyntacticObject.isPhaseHead_iff_phaseInterior_ne_zero`: a head projects exactly when its phase
  has a nonempty interior.
* `SyntacticObject.phaseInterior_add_phaseEdge`: the interior and the edge partition the phase.
* `SyntacticObject.phaseInterior_eq_domainIn`: the interior of a head that projects wherever it
  occurs is its c-command domain.

## Implementation notes

* Terms are values, not occurrences, so all copies of a head share one phase; positions tell
  copies apart in `Linearization/Chain.lean`.
* Every head that projects heads a phase, as in the book; which heads a study treats as phase
  heads (C alone, or also v, D, or Voice) is its choice of head.
* A selection head projects only over a sister it selects, so the book's empty complement and
  modifiers of the head do not arise, and a specifier blocks projection above it.

## TODO

* The terms made inaccessible by the interiors of lower phases, and the stricter variant that
  also freezes their heads.

## References

* [marcolli-chomsky-berwick-2025]
* [chomsky-2000]
-/

@[expose] public section

namespace Minimalist.SyntacticObject

open Relation

variable (T : SyntacticObject) (ℓ : LIToken) (x z : SyntacticObject)

/-- `ℓ` heads a phase of `T` when it projects, heading a mother of its leaf. -/
def IsPhaseHead : Prop := ∃ m ∈ T.terms, m.selHead = some ℓ ∧ immediatelyContains m (leaf ℓ)

instance : Decidable (IsPhaseHead T ℓ) := Multiset.decidableExistsMultiset

/-- `z` is the complement of `ℓ` in `T` when `ℓ` projects over its sister `z`. -/
def IsComplementOf : Prop :=
  ∃ m ∈ T.terms, m.selHead = some ℓ ∧ immediatelyContains m (leaf ℓ) ∧
    immediatelyContains m z ∧ z ≠ leaf ℓ

instance : Decidable (IsComplementOf T ℓ z) := Multiset.decidableExistsMultiset

/-- `x` lies within the projection of `ℓ` in `T` when a term of `T` that `ℓ` heads contains it. -/
def WithinProjection : Prop := ∃ p ∈ T.terms, p.selHead = some ℓ ∧ containsOrEq p x

instance : Decidable (WithinProjection T ℓ x) := Multiset.decidableExistsMultiset

/-- `x` lies within the complement of `ℓ` in `T` when a complement of `ℓ` contains it. -/
def WithinComplement : Prop := ∃ z ∈ T.terms, IsComplementOf T ℓ z ∧ containsOrEq z x

instance : Decidable (WithinComplement T ℓ x) := Multiset.decidableExistsMultiset

/-- The phase of `ℓ` in `T` is the multiset of terms within its projection. -/
def phase : Multiset SyntacticObject := T.terms.filter (WithinProjection T ℓ)

/-- The interior of the phase of `ℓ` in `T` is the multiset of terms within its complement. -/
def phaseInterior : Multiset SyntacticObject := T.terms.filter (WithinComplement T ℓ)

/-- The edge of the phase of `ℓ` in `T` is the multiset of terms of the phase outside its
interior. -/
def phaseEdge : Multiset SyntacticObject := (T.phase ℓ).filter (· ∉ T.phaseInterior ℓ)

variable {T ℓ x z} {y : SyntacticObject}

theorem IsComplementOf.mem_terms (h : IsComplementOf T ℓ z) : z ∈ T.terms :=
  let ⟨_, hm, _, _, hz, _⟩ := h
  SyntacticObject.mem_terms.2 (.tail (SyntacticObject.mem_terms.1 hm) hz)

theorem WithinProjection.mem_terms (h : WithinProjection T ℓ x) : x ∈ T.terms :=
  let ⟨_, hp, _, hpx⟩ := h
  terms_subset_terms (SyntacticObject.mem_terms.1 hp) (SyntacticObject.mem_terms.2 hpx)

/-- What lies within the complement lies within the projection. -/
theorem WithinComplement.withinProjection (h : WithinComplement T ℓ x) : WithinProjection T ℓ x :=
  let ⟨_, _, ⟨m, hm, hℓ, _, hz, _⟩, hzx⟩ := h
  ⟨m, hm, hℓ, .head hz hzx⟩

theorem WithinComplement.mem_terms (h : WithinComplement T ℓ x) : x ∈ T.terms :=
  h.withinProjection.mem_terms

theorem WithinProjection.trans (hx : WithinProjection T ℓ x) (hxy : containsOrEq x y) :
    WithinProjection T ℓ y :=
  let ⟨p, hp, hℓ, hpx⟩ := hx
  ⟨p, hp, hℓ, hpx.trans hxy⟩

/-- Whatever a frozen term contains is frozen. -/
theorem WithinComplement.trans (hx : WithinComplement T ℓ x) (hxy : containsOrEq x y) :
    WithinComplement T ℓ y :=
  let ⟨z, hz, hc, hzx⟩ := hx
  ⟨z, hz, hc, hzx.trans hxy⟩

/-- The head c-commands what lies within its complement. -/
theorem WithinComplement.cCommandsIn (h : WithinComplement T ℓ x) : T.cCommandsIn (leaf ℓ) x :=
  let ⟨z, hz, ⟨m, hm, _, hmℓ, hmz, hne⟩, hzx⟩ := h
  ⟨z, hz, ⟨m, hm, hmℓ, hmz, hne.symm⟩, hzx⟩

@[simp] theorem mem_phase : x ∈ T.phase ℓ ↔ WithinProjection T ℓ x :=
  Multiset.mem_filter.trans (and_iff_right_of_imp WithinProjection.mem_terms)

@[simp] theorem mem_phaseInterior : x ∈ T.phaseInterior ℓ ↔ WithinComplement T ℓ x :=
  Multiset.mem_filter.trans (and_iff_right_of_imp WithinComplement.mem_terms)

@[simp] theorem mem_phaseEdge :
    x ∈ T.phaseEdge ℓ ↔ WithinProjection T ℓ x ∧ ¬ WithinComplement T ℓ x :=
  Multiset.mem_filter.trans (and_congr mem_phase (not_congr mem_phaseInterior))

/-- A head projects exactly when it has a complement, since a head never selects a copy of
itself. -/
theorem isPhaseHead_iff_exists_isComplementOf : IsPhaseHead T ℓ ↔ ∃ z, IsComplementOf T ℓ z := by
  refine ⟨fun ⟨m, hm, hℓ, hmℓ⟩ ↦ ?_, fun ⟨_, m, hm, hℓ, hmℓ, _⟩ ↦ ⟨m, hm, hℓ, hmℓ⟩⟩
  induction m using SyntacticObject.ind with
  | leaf => simp at hmℓ
  | trace => simp at hmℓ
  | traceOf => simp at hmℓ
  | merge l r _ _ =>
    rcases (immediatelyContains_merge _ _ _).1 hmℓ with rfl | rfl
    · exact ⟨r, _, hm, hℓ, by simp, by simp, by rintro rfl; simp at hℓ⟩
    · exact ⟨l, _, hm, hℓ, by simp, by simp, by rintro rfl; simp at hℓ⟩

/-- A head projects exactly when its phase has a nonempty interior. -/
theorem isPhaseHead_iff_phaseInterior_ne_zero : IsPhaseHead T ℓ ↔ T.phaseInterior ℓ ≠ 0 := by
  rw [isPhaseHead_iff_exists_isComplementOf]
  refine ⟨fun ⟨z, hz⟩ h0 ↦ Multiset.filter_eq_nil.1 h0 z hz.mem_terms ⟨z, hz.mem_terms, hz, .refl⟩,
    fun h ↦ ?_⟩
  obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero h
  obtain ⟨z, -, hz, -⟩ := mem_phaseInterior.1 hx
  exact ⟨z, hz⟩

theorem phaseInterior_le_phase : T.phaseInterior ℓ ≤ T.phase ℓ :=
  Multiset.monotone_filter_right _ fun _ h ↦ h.withinProjection

/-- The interior and the edge partition the phase. -/
theorem phaseInterior_add_phaseEdge : T.phaseInterior ℓ + T.phaseEdge ℓ = T.phase ℓ := by
  conv_rhs => rw [← Multiset.filter_add_not (· ∈ T.phaseInterior ℓ) (T.phase ℓ)]
  congr 1
  rw [phase, Multiset.filter_filter]
  exact Multiset.filter_congr fun _ _ ↦ by
    grind [mem_phaseInterior, WithinComplement.withinProjection]

theorem phaseInterior_le_domainIn : T.phaseInterior ℓ ≤ T.domainIn (leaf ℓ) :=
  Multiset.monotone_filter_right _ fun _ h ↦ h.cCommandsIn

/-- The interior of a head that projects wherever it occurs is its c-command domain. -/
theorem phaseInterior_eq_domainIn
    (h : ∀ m ∈ T.terms, immediatelyContains m (leaf ℓ) → m.selHead = some ℓ) :
    T.phaseInterior ℓ = T.domainIn (leaf ℓ) :=
  Multiset.filter_congr fun _ _ ↦ by
    grind [WithinComplement, IsComplementOf, cCommandsIn, areSistersIn]

end Minimalist.SyntacticObject
