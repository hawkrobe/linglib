/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Logic.Trivalent.Basic
public import Mathlib.Data.Set.Basic

/-!
# Trivalent propositions

A trivalent proposition is a plain function `W → Trivalent`: at each world it is true, false,
or undefined. Its worlds split into the positive extension, the negative extension, and the
extension gap, and the Beaver–Krahmer 𝒜 operator applied pointwise (`Trivalent.metaAssert ∘ p`)
collapses the gap into the negative extension. As a `Pi` type, `W → Trivalent` inherits its
lattice structure pointwise (`⊓`/`⊔` via `Pi.instLattice`), so Strong Kleene conjunction and
disjunction of propositions need no definitions of their own; this file adds what the `Pi`
instances do not provide — the extensions, bivalence, and Haug's trivalent quantifiers, which
project a quantified presupposition existentially.

## Main declarations

* `Trivalent.posExt`, `Trivalent.negExt`, `Trivalent.gapExt`: the three extensions.
* `Trivalent.IsBivalent`: the proposition takes no `.indet` value.
* `Trivalent.forallWeak`, `Trivalent.existsWeak`: the Weak Kleene quantifiers, undefined as
  soon as any instance is.
* `Trivalent.forallStrong`, `Trivalent.existsStrong`: the Strong Kleene quantifiers, the
  indexed `⊓` and `⊔`.
* `Trivalent.forallHaug`, `Trivalent.existsHaug`: Haug's quantifiers, undefined only when
  every instance is, with `existsHaug_meetWeak_presuppose` as Quantifier Projection.

Each family is the trivalent face of a presupposition-projection theory under
`PartialProp.eval` (`Presupposition.Quantified`).

## Implementation notes

The Strong Kleene quantifiers are explicit definitions rather than `⨅`/`⨆`: a
`CompleteLinearOrder` instance on `Trivalent` carries a second `LinearOrder` parent that
instance search prefers, making every later `⊓` noncomputable.

## References

* [beaver-krahmer-2001]
* [kriz-2016]
* [haug-2014]
* [coppock-beaver-2015]
-/

@[expose] public section


namespace Trivalent

variable {W : Type*}

/-! ### Extensions -/

/-- The positive extension collects the worlds where the proposition is true. -/
def posExt (p : W → Trivalent) : Set W := {w | p w = .true}

/-- The negative extension collects the worlds where the proposition is false. -/
def negExt (p : W → Trivalent) : Set W := {w | p w = .false}

/-- The extension gap collects the worlds where the proposition is neither true nor false. -/
def gapExt (p : W → Trivalent) : Set W := {w | p w = .indet}

@[simp] theorem mem_posExt {p : W → Trivalent} {w : W} :
    w ∈ posExt p ↔ p w = .true := Iff.rfl

@[simp] theorem mem_negExt {p : W → Trivalent} {w : W} :
    w ∈ negExt p ↔ p w = .false := Iff.rfl

@[simp] theorem mem_gapExt {p : W → Trivalent} {w : W} :
    w ∈ gapExt p ↔ p w = .indet := Iff.rfl

instance (p : W → Trivalent) : DecidablePred (· ∈ posExt p) :=
  fun w ↦ inferInstanceAs (Decidable (p w = .true))

instance (p : W → Trivalent) : DecidablePred (· ∈ negExt p) :=
  fun w ↦ inferInstanceAs (Decidable (p w = .false))

instance (p : W → Trivalent) : DecidablePred (· ∈ gapExt p) :=
  fun w ↦ inferInstanceAs (Decidable (p w = .indet))

/-- The three extensions cover the world space. -/
theorem posExt_union_negExt_union_gapExt (p : W → Trivalent) :
    posExt p ∪ negExt p ∪ gapExt p = Set.univ := by
  ext w
  simp only [Set.mem_union, mem_posExt, mem_negExt, mem_gapExt, Set.mem_univ,
    iff_true]
  cases p w <;> simp

/-- The positive and negative extensions are disjoint. -/
theorem disjoint_posExt_negExt (p : W → Trivalent) :
    Disjoint (posExt p) (negExt p) := by
  rw [Set.disjoint_left]
  intro w hw hw'
  rw [mem_posExt] at hw
  rw [mem_negExt, hw] at hw'
  cases hw'

/-- A proposition is bivalent if it takes no `.indet` value. -/
def IsBivalent (p : W → Trivalent) : Prop :=
  ∀ w, p w = .true ∨ p w = .false

theorem isBivalent_iff_gapExt_eq_empty (p : W → Trivalent) :
    IsBivalent p ↔ gapExt p = ∅ := by
  simp only [IsBivalent, Set.eq_empty_iff_forall_notMem, mem_gapExt]
  exact forall_congr' fun w => by cases p w <;> simp

theorem isBivalent_iff_forall_ne_indet (p : W → Trivalent) :
    IsBivalent p ↔ ∀ w, p w ≠ .indet :=
  forall_congr' fun w => by cases p w <;> simp

theorem IsBivalent.ne_indet {p : W → Trivalent} (h : IsBivalent p) (w : W) : p w ≠ .indet :=
  (isBivalent_iff_forall_ne_indet p).1 h w

/-! ### Extensions under meta-assertion

Meta-assertion of a proposition is the pointwise composite `metaAssert ∘ p`; no dedicated
pointwise operator is needed. -/

@[simp] theorem posExt_comp_metaAssert (p : W → Trivalent) :
    posExt (metaAssert ∘ p) = posExt p := by
  ext w; simp only [mem_posExt, Function.comp_apply]
  cases p w <;> simp

@[simp] theorem negExt_comp_metaAssert (p : W → Trivalent) :
    negExt (metaAssert ∘ p) = negExt p ∪ gapExt p := by
  ext w
  simp only [mem_negExt, Set.mem_union, mem_gapExt, Function.comp_apply]
  cases p w <;> simp

@[simp] theorem gapExt_comp_metaAssert (p : W → Trivalent) :
    gapExt (metaAssert ∘ p) = ∅ := by
  ext w
  simp only [mem_gapExt, Function.comp_apply, Set.mem_empty_iff_false, iff_false]
  cases p w <;> simp

/-- Meta-assertion produces a bivalent proposition. -/
theorem isBivalent_comp_metaAssert (p : W → Trivalent) : IsBivalent (metaAssert ∘ p) := by
  intro w; simp only [Function.comp_apply]; cases p w <;> simp

/-! ### Quantifiers

Like the binary connectives, the trivalent quantifiers come in rival families, by where
undefinedness projects. The Weak Kleene quantifiers are undefined as soon as any instance
is; the Strong Kleene quantifiers are `⨅` and `⨆` in the complete chain; and the
quantifiers of [haug-2014], adopted by [coppock-beaver-2015] and [cooper-2023], are
undefined only when every instance is, so that a quantified presupposition projects
existentially. -/

open Classical in
/-- The Weak Kleene universal quantifier is undefined when any instance is, and otherwise
classical. -/
noncomputable def forallWeak {ι : Sort*} (p : ι → Trivalent) : Trivalent :=
  if ∃ i, p i = .indet then .indet else if ∀ i, p i = .true then .true else .false

/-- The Weak Kleene existential quantifier is the dual of `forallWeak`. -/
noncomputable def existsWeak {ι : Sort*} (p : ι → Trivalent) : Trivalent :=
  neg (forallWeak fun i => neg (p i))

section WeakQuantifiers

variable {ι : Sort*} {p : ι → Trivalent}

@[simp] theorem forallWeak_eq_indet_iff : forallWeak p = .indet ↔ ∃ i, p i = .indet := by
  unfold forallWeak; split_ifs <;> simp_all

@[simp] theorem forallWeak_eq_true_iff : forallWeak p = .true ↔ ∀ i, p i = .true := by
  unfold forallWeak; split_ifs with h₁ h₂
  · exact iff_of_false (by decide) fun h => by obtain ⟨i, hi⟩ := h₁; rw [h i] at hi; cases hi
  · exact iff_of_true rfl h₂
  · exact iff_of_false (by decide) h₂

@[simp] theorem forallWeak_eq_false_iff :
    forallWeak p = .false ↔ (∀ i, p i ≠ .indet) ∧ ∃ i, p i = .false := by
  unfold forallWeak
  split_ifs with h₁ h₂
  · exact iff_of_false (by decide) fun h => h.1 h₁.choose h₁.choose_spec
  · refine iff_of_false (by decide) fun h => ?_
    obtain ⟨-, i, hi⟩ := h
    rw [h₂ i] at hi
    cases hi
  · push Not at h₁ h₂
    obtain ⟨i, hi⟩ := h₂
    exact iff_of_true rfl ⟨h₁, i, by cases h : p i <;> simp_all⟩

@[simp] theorem existsWeak_eq_indet_iff : existsWeak p = .indet ↔ ∃ i, p i = .indet := by
  simp [existsWeak]

@[simp] theorem existsWeak_eq_true_iff :
    existsWeak p = .true ↔ (∀ i, p i ≠ .indet) ∧ ∃ i, p i = .true := by
  simp [existsWeak]

@[simp] theorem existsWeak_eq_false_iff : existsWeak p = .false ↔ ∀ i, p i = .false := by
  simp [existsWeak]

end WeakQuantifiers

open Classical in
/-- The Strong Kleene universal quantifier is the indexed `⊓`: false when any instance is,
true when all are, and undefined otherwise. -/
noncomputable def forallStrong {ι : Sort*} (p : ι → Trivalent) : Trivalent :=
  if ∃ i, p i = .false then .false else if ∀ i, p i = .true then .true else .indet

/-- The Strong Kleene existential quantifier is the dual of `forallStrong`, the indexed `⊔`. -/
noncomputable def existsStrong {ι : Sort*} (p : ι → Trivalent) : Trivalent :=
  neg (forallStrong fun i => neg (p i))

section StrongQuantifiers

variable {ι : Sort*} {p : ι → Trivalent}

@[simp] theorem forallStrong_eq_false_iff : forallStrong p = .false ↔ ∃ i, p i = .false := by
  unfold forallStrong; split_ifs <;> simp_all

@[simp] theorem forallStrong_eq_true_iff : forallStrong p = .true ↔ ∀ i, p i = .true := by
  unfold forallStrong
  split_ifs with h₁ h₂
  · refine iff_of_false (by decide) fun h => ?_
    obtain ⟨i, hi⟩ := h₁
    rw [h i] at hi
    cases hi
  · exact iff_of_true rfl h₂
  · exact iff_of_false (by decide) h₂

@[simp] theorem forallStrong_eq_indet_iff :
    forallStrong p = .indet ↔ (∀ i, p i ≠ .false) ∧ ∃ i, p i = .indet := by
  unfold forallStrong
  split_ifs with h₁ h₂
  · exact iff_of_false (by decide) fun h => h.1 h₁.choose h₁.choose_spec
  · refine iff_of_false (by decide) fun h => ?_
    obtain ⟨-, i, hi⟩ := h
    rw [h₂ i] at hi
    cases hi
  · push Not at h₁ h₂
    obtain ⟨i, hi⟩ := h₂
    exact iff_of_true rfl ⟨h₁, i, by cases h : p i <;> simp_all⟩

@[simp] theorem existsStrong_eq_true_iff : existsStrong p = .true ↔ ∃ i, p i = .true := by
  simp [existsStrong]

@[simp] theorem existsStrong_eq_false_iff : existsStrong p = .false ↔ ∀ i, p i = .false := by
  simp [existsStrong]

@[simp] theorem existsStrong_eq_indet_iff :
    existsStrong p = .indet ↔ (∀ i, p i ≠ .true) ∧ ∃ i, p i = .indet := by
  simp [existsStrong]

end StrongQuantifiers

open Classical in
/-- Haug's universal quantifier evaluates a trivalent predicate: undefined only when every
instance is, false when some instance is, and true otherwise. -/
noncomputable def forallHaug (p : W → Trivalent) : Trivalent :=
  if ∀ w, p w = .indet then .indet else if ∃ w, p w = .false then .false else .true

/-- The existential quantifier is the dual of `forallHaug`. -/
noncomputable def existsHaug (p : W → Trivalent) : Trivalent :=
  neg (forallHaug fun w => neg (p w))

@[simp] theorem forallHaug_eq_indet_iff (p : W → Trivalent) :
    forallHaug p = .indet ↔ ∀ w, p w = .indet := by
  unfold forallHaug; split_ifs <;> simp_all

@[simp] theorem forallHaug_eq_false_iff (p : W → Trivalent) :
    forallHaug p = .false ↔ ∃ w, p w = .false := by
  unfold forallHaug; split_ifs <;> simp_all

@[simp] theorem forallHaug_eq_true_iff (p : W → Trivalent) :
    forallHaug p = .true ↔ (∃ w, p w ≠ .indet) ∧ ∀ w, p w ≠ .false := by
  unfold forallHaug; split_ifs <;> simp_all

@[simp] theorem existsHaug_eq_indet_iff (p : W → Trivalent) :
    existsHaug p = .indet ↔ ∀ w, p w = .indet := by
  simp only [existsHaug, neg_eq_indet_iff, forallHaug_eq_indet_iff]

@[simp] theorem existsHaug_eq_true_iff (p : W → Trivalent) :
    existsHaug p = .true ↔ ∃ w, p w = .true := by
  simp only [existsHaug, neg_eq_true_iff, forallHaug_eq_false_iff, neg_eq_false_iff]

@[simp] theorem existsHaug_eq_false_iff (p : W → Trivalent) :
    existsHaug p = .false ↔ (∃ w, p w ≠ .indet) ∧ ∀ w, p w ≠ .true := by
  simp only [existsHaug, neg_eq_false_iff, forallHaug_eq_true_iff, ne_eq, neg_eq_indet_iff]

/-- An existentially quantified presupposition is true or undefined, never false. -/
theorem existsHaug_presuppose_ne_false (p : W → Trivalent) :
    existsHaug (fun w => presuppose (p w)) ≠ .false := by
  simp

/-- Quantifier Projection ([coppock-beaver-2015]'s appendix) lets a presupposition under the
existential project as an existentially quantified presupposition, over bivalent `φ` and
`ψ`. -/
theorem existsHaug_meetWeak_presuppose {φ ψ : W → Trivalent} (hφ : IsBivalent φ)
    (hψ : IsBivalent ψ) :
    existsHaug (fun w => meetWeak (presuppose (φ w)) (ψ w)) =
      meetWeak (existsHaug fun w => presuppose (φ w))
        (existsHaug fun w => meetWeak (φ w) (ψ w)) := by
  refine eq_of_indet_iff_of_true_iff ?_ ?_
  · simp only [existsHaug_eq_indet_iff, meetWeak_eq_indet_iff, presuppose_eq_indet_iff, hφ.ne_indet,
      hψ.ne_indet, or_false]
    exact ⟨Or.inl, fun h => h.elim id fun h w => (h w).elim⟩
  · simp only [existsHaug_eq_true_iff, meetWeak_eq_true_iff, presuppose_eq_true_iff]
    exact ⟨fun ⟨w, h⟩ => ⟨⟨w, h.1⟩, w, h⟩, fun h => h.2⟩

end Trivalent
