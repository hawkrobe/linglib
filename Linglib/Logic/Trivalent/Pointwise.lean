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

Like the binary connectives, the trivalent quantifiers come in rival families that share one
truth rule and differ only in where undefinedness projects, which `forallWith` and
`existsWith` make definitional: a family is fixed by its definedness condition. The Weak
Kleene quantifiers are undefined as soon as any instance is; the Strong Kleene quantifiers
are defined whenever the instances settle the value, the indexed `⊓` and `⊔`; and the
quantifiers of [haug-2014], adopted by [coppock-beaver-2015] and [cooper-2023], are undefined
only when every instance is, so that a quantified presupposition projects existentially.
Restricted to a pair of instances the families are the binary connectives — Weak Kleene
`meetWeak`, Strong Kleene `⊓`, and, for Haug's quantifier, Belnap's skip-undefined
`meetBelnap` (`forallHaug_pair`). Middle Kleene reads its operands left to right, so it has
no order-free quantifier. -/

open Classical in
/-- `forallWith D p` is the universal quantifier of the family whose definedness condition
is `D`: undefined unless `D` holds, and otherwise false exactly when some instance is. All
the families share this truth rule (`forallWith_eq_forallWith_of_defined`). -/
noncomputable def forallWith {ι : Sort*} (D : Prop) (p : ι → Trivalent) : Trivalent :=
  if D then if ∃ i, p i = .false then .false else .true else .indet

/-- `existsWith D p` is the existential quantifier of the family whose definedness condition
is `D`, the dual of `forallWith`. -/
noncomputable def existsWith {ι : Sort*} (D : Prop) (p : ι → Trivalent) : Trivalent :=
  neg (forallWith D fun i => neg (p i))

section WithFamilies

variable {ι : Sort*} {D D' : Prop} {p : ι → Trivalent}

theorem forallWith_eq_indet_iff : forallWith D p = .indet ↔ ¬D := by
  unfold forallWith; split_ifs <;> simp_all

theorem forallWith_eq_false_iff : forallWith D p = .false ↔ D ∧ ∃ i, p i = .false := by
  unfold forallWith; split_ifs <;> simp_all

theorem forallWith_eq_true_iff : forallWith D p = .true ↔ D ∧ ∀ i, p i ≠ .false := by
  unfold forallWith; split_ifs <;> simp_all

theorem existsWith_eq_indet_iff : existsWith D p = .indet ↔ ¬D := by
  simp [existsWith, forallWith_eq_indet_iff]

theorem existsWith_eq_true_iff : existsWith D p = .true ↔ D ∧ ∃ i, p i = .true := by
  simp [existsWith, forallWith_eq_false_iff]

theorem existsWith_eq_false_iff : existsWith D p = .false ↔ D ∧ ∀ i, p i ≠ .true := by
  simp [existsWith, forallWith_eq_true_iff]

/-- The families share one truth rule: any two agree wherever both are defined. -/
theorem forallWith_eq_forallWith_of_defined (hD : D) (hD' : D') :
    forallWith D p = forallWith D' p := by
  unfold forallWith
  rw [ite_eq_left hD, ite_eq_left hD']

end WithFamilies

/-- The Weak Kleene universal quantifier is undefined when any instance is, and otherwise
classical. -/
noncomputable def forallWeak {ι : Sort*} (p : ι → Trivalent) : Trivalent :=
  forallWith (∀ i, p i ≠ .indet) p

/-- The Weak Kleene existential quantifier is the dual of `forallWeak`. -/
noncomputable def existsWeak {ι : Sort*} (p : ι → Trivalent) : Trivalent :=
  existsWith (∀ i, p i ≠ .indet) p

section WeakQuantifiers

variable {ι : Sort*} {p : ι → Trivalent}

@[simp] theorem forallWeak_eq_indet_iff : forallWeak p = .indet ↔ ∃ i, p i = .indet := by
  rw [forallWeak, forallWith_eq_indet_iff, not_forall]
  simp

@[simp] theorem forallWeak_eq_true_iff : forallWeak p = .true ↔ ∀ i, p i = .true := by
  rw [forallWeak, forallWith_eq_true_iff]
  constructor
  · rintro ⟨hd, hf⟩ i
    cases h : p i
    · rfl
    · exact absurd h (hf i)
    · exact absurd h (hd i)
  · exact fun h => ⟨fun i => h i ▸ by decide, fun i => h i ▸ by decide⟩

@[simp] theorem forallWeak_eq_false_iff :
    forallWeak p = .false ↔ (∀ i, p i ≠ .indet) ∧ ∃ i, p i = .false := by
  rw [forallWeak, forallWith_eq_false_iff]

@[simp] theorem existsWeak_eq_indet_iff : existsWeak p = .indet ↔ ∃ i, p i = .indet := by
  rw [existsWeak, existsWith_eq_indet_iff, not_forall]
  simp

@[simp] theorem existsWeak_eq_true_iff :
    existsWeak p = .true ↔ (∀ i, p i ≠ .indet) ∧ ∃ i, p i = .true := by
  rw [existsWeak, existsWith_eq_true_iff]

@[simp] theorem existsWeak_eq_false_iff : existsWeak p = .false ↔ ∀ i, p i = .false := by
  rw [existsWeak, existsWith_eq_false_iff]
  constructor
  · rintro ⟨hd, hf⟩ i
    cases h : p i
    · exact absurd h (hf i)
    · rfl
    · exact absurd h (hd i)
  · exact fun h => ⟨fun i => h i ▸ by decide, fun i => h i ▸ by decide⟩

end WeakQuantifiers

/-- The Strong Kleene universal quantifier is the indexed `⊓`: false when any instance is,
true when all are, and undefined otherwise. -/
noncomputable def forallStrong {ι : Sort*} (p : ι → Trivalent) : Trivalent :=
  forallWith ((∃ i, p i = .false) ∨ ∀ i, p i = .true) p

/-- The Strong Kleene existential quantifier is the dual of `forallStrong`, the indexed
`⊔`. -/
noncomputable def existsStrong {ι : Sort*} (p : ι → Trivalent) : Trivalent :=
  existsWith ((∃ i, p i = .true) ∨ ∀ i, p i = .false) p

section StrongQuantifiers

variable {ι : Sort*} {p : ι → Trivalent}

@[simp] theorem forallStrong_eq_false_iff : forallStrong p = .false ↔ ∃ i, p i = .false := by
  rw [forallStrong, forallWith_eq_false_iff, and_iff_right_iff_imp]
  exact fun h => .inl h

@[simp] theorem forallStrong_eq_true_iff : forallStrong p = .true ↔ ∀ i, p i = .true := by
  rw [forallStrong, forallWith_eq_true_iff]
  constructor
  · rintro ⟨⟨i, hi⟩ | h, hf⟩
    · exact absurd hi (hf i)
    · exact h
  · exact fun h => ⟨.inr h, fun i => h i ▸ by decide⟩

@[simp] theorem forallStrong_eq_indet_iff :
    forallStrong p = .indet ↔ (∀ i, p i ≠ .false) ∧ ∃ i, p i = .indet := by
  rw [forallStrong, forallWith_eq_indet_iff, not_or, not_exists, not_forall]
  refine and_congr_right fun hne => exists_congr fun i => ?_
  cases h : p i <;> simp_all

@[simp] theorem existsStrong_eq_true_iff : existsStrong p = .true ↔ ∃ i, p i = .true := by
  rw [existsStrong, existsWith_eq_true_iff, and_iff_right_iff_imp]
  exact fun h => .inl h

@[simp] theorem existsStrong_eq_false_iff : existsStrong p = .false ↔ ∀ i, p i = .false := by
  rw [existsStrong, existsWith_eq_false_iff]
  constructor
  · rintro ⟨⟨i, hi⟩ | h, hf⟩
    · exact absurd hi (hf i)
    · exact h
  · exact fun h => ⟨.inr h, fun i => h i ▸ by decide⟩

@[simp] theorem existsStrong_eq_indet_iff :
    existsStrong p = .indet ↔ (∀ i, p i ≠ .true) ∧ ∃ i, p i = .indet := by
  rw [existsStrong, existsWith_eq_indet_iff, not_or, not_exists, not_forall]
  refine and_congr_right fun hne => exists_congr fun i => ?_
  cases h : p i <;> simp_all

end StrongQuantifiers

/-- Haug's universal quantifier skips undefined instances: undefined only when every
instance is, false when some instance is, and true otherwise. -/
noncomputable def forallHaug (p : W → Trivalent) : Trivalent :=
  forallWith (∃ w, p w ≠ .indet) p

/-- The dual of `forallHaug`. -/
noncomputable def existsHaug (p : W → Trivalent) : Trivalent :=
  existsWith (∃ w, p w ≠ .indet) p

section HaugQuantifiers

variable {p : W → Trivalent}

@[simp] theorem forallHaug_eq_indet_iff : forallHaug p = .indet ↔ ∀ w, p w = .indet := by
  rw [forallHaug, forallWith_eq_indet_iff, not_exists]
  simp

@[simp] theorem forallHaug_eq_false_iff : forallHaug p = .false ↔ ∃ w, p w = .false := by
  rw [forallHaug, forallWith_eq_false_iff, and_iff_right_iff_imp]
  rintro ⟨w, hw⟩
  exact ⟨w, hw ▸ by decide⟩

@[simp] theorem forallHaug_eq_true_iff :
    forallHaug p = .true ↔ (∃ w, p w ≠ .indet) ∧ ∀ w, p w ≠ .false := by
  rw [forallHaug, forallWith_eq_true_iff]

@[simp] theorem existsHaug_eq_indet_iff : existsHaug p = .indet ↔ ∀ w, p w = .indet := by
  rw [existsHaug, existsWith_eq_indet_iff, not_exists]
  simp

@[simp] theorem existsHaug_eq_true_iff : existsHaug p = .true ↔ ∃ w, p w = .true := by
  rw [existsHaug, existsWith_eq_true_iff, and_iff_right_iff_imp]
  rintro ⟨w, hw⟩
  exact ⟨w, hw ▸ by decide⟩

@[simp] theorem existsHaug_eq_false_iff :
    existsHaug p = .false ↔ (∃ w, p w ≠ .indet) ∧ ∀ w, p w ≠ .true := by
  rw [existsHaug, existsWith_eq_false_iff]

end HaugQuantifiers

/-! ### Each family restricted to a pair is its binary connective -/

section Pairs

variable (a b : Trivalent)

theorem forallWeak_pair : forallWeak (fun i : Bool => bif i then a else b) = meetWeak a b := by
  cases a <;> cases b <;>
    refine eq_of_indet_iff_of_true_iff ?_ ?_ <;>
    simp [Bool.exists_bool, Bool.forall_bool]

theorem existsWeak_pair : existsWeak (fun i : Bool => bif i then a else b) = joinWeak a b := by
  cases a <;> cases b <;>
    refine eq_of_indet_iff_of_true_iff ?_ ?_ <;>
    simp [Bool.exists_bool, Bool.forall_bool, joinWeak]

theorem forallStrong_pair :
    forallStrong (fun i : Bool => bif i then a else b) = a ⊓ b := by
  cases a <;> cases b <;>
    refine eq_of_indet_iff_of_true_iff ?_ ?_ <;>
    simp [Bool.exists_bool, Bool.forall_bool] <;> decide

theorem existsStrong_pair :
    existsStrong (fun i : Bool => bif i then a else b) = a ⊔ b := by
  cases a <;> cases b <;>
    refine eq_of_indet_iff_of_true_iff ?_ ?_ <;>
    simp [Bool.exists_bool, Bool.forall_bool] <;> decide

/-- **Haug's quantifier is Belnap's conditional assertion, quantified**: restricted to a
pair of instances it is the skip-undefined conjunction of [belnap-1970]. -/
theorem forallHaug_pair :
    forallHaug (fun i : Bool => bif i then a else b) = meetBelnap a b := by
  cases a <;> cases b <;>
    refine eq_of_indet_iff_of_true_iff ?_ ?_ <;>
    simp [Bool.exists_bool, Bool.forall_bool, meetBelnap]

/-- The dual: Haug's existential restricted to a pair is Belnap disjunction. -/
theorem existsHaug_pair :
    existsHaug (fun i : Bool => bif i then a else b) = joinBelnap a b := by
  cases a <;> cases b <;>
    refine eq_of_indet_iff_of_true_iff ?_ ?_ <;>
    simp [Bool.exists_bool, Bool.forall_bool, joinBelnap]

end Pairs

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
