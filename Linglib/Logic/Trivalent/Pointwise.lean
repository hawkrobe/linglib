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

A trivalent proposition is a function `W → SignType`, true, false or undefined at each world.
Its worlds split into a positive extension, a negative extension and a gap, and Beaver and
Krahmer's assertion operator applied pointwise collapses the gap into the negative extension.
Strong Kleene conjunction and disjunction of propositions are the pointwise `⊓` and `⊔`. This file
adds the extensions, bivalence, and the three families of trivalent quantifiers.

## Main definitions

* `Trivalent.posExt`, `Trivalent.negExt`, `Trivalent.gapExt`: the three extensions.
* `Trivalent.IsBivalent`: the proposition is never `0`.
* `Trivalent.forallWeak`, `Trivalent.existsWeak`: the Weak Kleene quantifiers, undefined as
  soon as any instance is.
* `Trivalent.forallStrong`, `Trivalent.existsStrong`: the Strong Kleene quantifiers, the
  indexed `⊓` and `⊔`.
* `Trivalent.forallHaug`, `Trivalent.existsHaug`: Haug's quantifiers, undefined only when
  every instance is, with `existsHaug_meetWeak_presuppose` as Quantifier Projection.

Each family is the trivalent face of a presupposition-projection theory under
`PartialProp.eval` (`Presupposition.Quantified`).

## Implementation notes

The Strong Kleene quantifiers are explicit definitions rather than `⨅` and `⨆`, because a
`CompleteLinearOrder` instance on `SignType` would carry a second `LinearOrder` parent that
instance search prefers, making every later `⊓` noncomputable.

## References

* [beaver-krahmer-2001]
* [kriz-2016]
* [haug-2014]
* [coppock-beaver-2015]
-/

@[expose] public section


namespace Trivalent

open SignType

variable {W : Type*}

/-! ### Extensions -/

/-- The positive extension collects the worlds where the proposition is true. -/
def posExt (p : W → SignType) : Set W := {w | p w = 1}

/-- The negative extension collects the worlds where the proposition is false. -/
def negExt (p : W → SignType) : Set W := {w | p w = -1}

/-- The extension gap collects the worlds where the proposition is neither true nor false. -/
def gapExt (p : W → SignType) : Set W := {w | p w = 0}

@[simp] theorem mem_posExt {p : W → SignType} {w : W} :
    w ∈ posExt p ↔ p w = 1 := Iff.rfl

@[simp] theorem mem_negExt {p : W → SignType} {w : W} :
    w ∈ negExt p ↔ p w = -1 := Iff.rfl

@[simp] theorem mem_gapExt {p : W → SignType} {w : W} :
    w ∈ gapExt p ↔ p w = 0 := Iff.rfl

instance (p : W → SignType) : DecidablePred (· ∈ posExt p) :=
  fun w ↦ inferInstanceAs (Decidable (p w = 1))

instance (p : W → SignType) : DecidablePred (· ∈ negExt p) :=
  fun w ↦ inferInstanceAs (Decidable (p w = -1))

instance (p : W → SignType) : DecidablePred (· ∈ gapExt p) :=
  fun w ↦ inferInstanceAs (Decidable (p w = 0))

/-- The three extensions cover the world space. -/
theorem posExt_union_negExt_union_gapExt (p : W → SignType) :
    posExt p ∪ negExt p ∪ gapExt p = Set.univ := by
  ext w
  simp only [Set.mem_union, mem_posExt, mem_negExt, mem_gapExt, Set.mem_univ,
    iff_true]
  cases p w <;> simp

/-- The positive and negative extensions are disjoint. -/
theorem disjoint_posExt_negExt (p : W → SignType) :
    Disjoint (posExt p) (negExt p) := by
  rw [Set.disjoint_left]
  intro w hw hw'
  rw [mem_posExt] at hw
  rw [mem_negExt, hw] at hw'
  cases hw'

/-- A proposition is bivalent if it takes no `0` value. -/
def IsBivalent (p : W → SignType) : Prop :=
  ∀ w, p w = 1 ∨ p w = -1

theorem isBivalent_iff_gapExt_eq_empty (p : W → SignType) :
    IsBivalent p ↔ gapExt p = ∅ := by
  simp only [IsBivalent, Set.eq_empty_iff_forall_notMem, mem_gapExt]
  exact forall_congr' fun w => by cases p w <;> simp

theorem isBivalent_iff_forall_ne_zero (p : W → SignType) :
    IsBivalent p ↔ ∀ w, p w ≠ 0 :=
  forall_congr' fun w => by cases p w <;> simp

theorem IsBivalent.ne_zero {p : W → SignType} (h : IsBivalent p) (w : W) : p w ≠ 0 :=
  (isBivalent_iff_forall_ne_zero p).1 h w

/-! ### Extensions under meta-assertion

Meta-assertion of a proposition is the pointwise composite `metaAssert ∘ p`; no dedicated
pointwise operator is needed. -/

@[simp] theorem posExt_comp_metaAssert (p : W → SignType) :
    posExt (metaAssert ∘ p) = posExt p := by
  ext w; simp only [mem_posExt, Function.comp_apply]
  cases p w <;> simp

@[simp] theorem negExt_comp_metaAssert (p : W → SignType) :
    negExt (metaAssert ∘ p) = negExt p ∪ gapExt p := by
  ext w
  simp only [mem_negExt, Set.mem_union, mem_gapExt, Function.comp_apply]
  cases p w <;> simp

@[simp] theorem gapExt_comp_metaAssert (p : W → SignType) :
    gapExt (metaAssert ∘ p) = ∅ := by
  ext w
  simp only [mem_gapExt, Function.comp_apply, Set.mem_empty_iff_false, iff_false]
  cases p w <;> simp

/-- Meta-assertion produces a bivalent proposition. -/
theorem isBivalent_comp_metaAssert (p : W → SignType) : IsBivalent (metaAssert ∘ p) := by
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
/-- `forallWith D p` is the universal quantifier undefined unless `D` holds, and otherwise false
exactly when some instance is. All the families share this truth rule
(`forallWith_eq_forallWith_of_defined`). -/
noncomputable def forallWith {ι : Sort*} (D : Prop) (p : ι → SignType) : SignType :=
  if D then if ∃ i, p i = -1 then -1 else 1 else 0

/-- `existsWith D p` is the existential quantifier of the family whose definedness condition
is `D`, the dual of `forallWith`. -/
noncomputable def existsWith {ι : Sort*} (D : Prop) (p : ι → SignType) : SignType :=
  -forallWith D fun i ↦ -p i

section WithFamilies

variable {ι : Sort*} {D D' : Prop} {p : ι → SignType}

theorem forallWith_eq_zero_iff : forallWith D p = 0 ↔ ¬D := by
  unfold forallWith; split_ifs <;> simp_all

theorem forallWith_eq_neg_one_iff : forallWith D p = -1 ↔ D ∧ ∃ i, p i = -1 := by
  unfold forallWith; split_ifs <;> simp_all

theorem forallWith_eq_one_iff : forallWith D p = 1 ↔ D ∧ ∀ i, p i ≠ -1 := by
  unfold forallWith; split_ifs <;> simp_all

theorem existsWith_eq_zero_iff : existsWith D p = 0 ↔ ¬D := by
  simp [existsWith, SignType.neg_eq_zero_iff, forallWith_eq_zero_iff]

theorem existsWith_eq_one_iff : existsWith D p = 1 ↔ D ∧ ∃ i, p i = 1 := by
  simp [existsWith, neg_eq_iff_eq_neg, forallWith_eq_neg_one_iff]

theorem existsWith_eq_neg_one_iff : existsWith D p = -1 ↔ D ∧ ∀ i, p i ≠ 1 := by
  simp [existsWith, neg_eq_iff_eq_neg, forallWith_eq_one_iff]

/-- Any two families agree wherever both are defined, since they share one truth rule. -/
theorem forallWith_eq_forallWith_of_defined (hD : D) (hD' : D') :
    forallWith D p = forallWith D' p := by
  unfold forallWith
  rw [ite_eq_left hD, ite_eq_left hD']

theorem forallWith_congr (h : D ↔ D') : forallWith D p = forallWith D' p :=
  eq_of_eq_zero_iff_of_eq_one_iff
    (by rw [forallWith_eq_zero_iff, forallWith_eq_zero_iff, h])
    (by rw [forallWith_eq_one_iff, forallWith_eq_one_iff, h])

theorem existsWith_congr (h : D ↔ D') : existsWith D p = existsWith D' p :=
  congrArg Neg.neg (forallWith_congr h)

end WithFamilies

/-- The Weak Kleene universal quantifier is undefined when any instance is, and otherwise
classical. -/
noncomputable def forallWeak {ι : Sort*} (p : ι → SignType) : SignType :=
  forallWith (∀ i, p i ≠ 0) p

/-- The Weak Kleene existential quantifier is the dual of `forallWeak`. -/
noncomputable def existsWeak {ι : Sort*} (p : ι → SignType) : SignType :=
  existsWith (∀ i, p i ≠ 0) p

section WeakQuantifiers

variable {ι : Sort*} {p : ι → SignType}

@[simp] theorem forallWeak_eq_zero_iff : forallWeak p = 0 ↔ ∃ i, p i = 0 := by
  rw [forallWeak, forallWith_eq_zero_iff, not_forall]
  simp

@[simp] theorem forallWeak_eq_one_iff : forallWeak p = 1 ↔ ∀ i, p i = 1 := by
  rw [forallWeak, forallWith_eq_one_iff]
  constructor
  · rintro ⟨hd, hf⟩ i
    cases h : p i
    · exact absurd h (hd i)
    · exact absurd h (hf i)
    · rfl
  · exact fun h => ⟨fun i ↦ by rw [h i]; decide, fun i ↦ by rw [h i]; decide⟩

@[simp] theorem forallWeak_eq_neg_one_iff :
    forallWeak p = -1 ↔ (∀ i, p i ≠ 0) ∧ ∃ i, p i = -1 := by
  rw [forallWeak, forallWith_eq_neg_one_iff]

@[simp] theorem existsWeak_eq_zero_iff : existsWeak p = 0 ↔ ∃ i, p i = 0 := by
  rw [existsWeak, existsWith_eq_zero_iff, not_forall]
  simp

@[simp] theorem existsWeak_eq_one_iff :
    existsWeak p = 1 ↔ (∀ i, p i ≠ 0) ∧ ∃ i, p i = 1 := by
  rw [existsWeak, existsWith_eq_one_iff]

@[simp] theorem existsWeak_eq_neg_one_iff : existsWeak p = -1 ↔ ∀ i, p i = -1 := by
  rw [existsWeak, existsWith_eq_neg_one_iff]
  constructor
  · rintro ⟨hd, hf⟩ i
    cases h : p i
    · exact absurd h (hd i)
    · rfl
    · exact absurd h (hf i)
  · exact fun h => ⟨fun i ↦ by rw [h i]; decide, fun i ↦ by rw [h i]; decide⟩

end WeakQuantifiers

/-- The Strong Kleene universal quantifier is the indexed `⊓`, false when any instance is, true
when all are, and undefined otherwise. -/
noncomputable def forallStrong {ι : Sort*} (p : ι → SignType) : SignType :=
  forallWith ((∃ i, p i = -1) ∨ ∀ i, p i = 1) p

/-- The Strong Kleene existential quantifier is the dual of `forallStrong`, the indexed
`⊔`. -/
noncomputable def existsStrong {ι : Sort*} (p : ι → SignType) : SignType :=
  existsWith ((∃ i, p i = 1) ∨ ∀ i, p i = -1) p

section StrongQuantifiers

variable {ι : Sort*} {p : ι → SignType}

@[simp] theorem forallStrong_eq_neg_one_iff : forallStrong p = -1 ↔ ∃ i, p i = -1 := by
  rw [forallStrong, forallWith_eq_neg_one_iff, and_iff_right_iff_imp]
  exact fun h => .inl h

@[simp] theorem forallStrong_eq_one_iff : forallStrong p = 1 ↔ ∀ i, p i = 1 := by
  rw [forallStrong, forallWith_eq_one_iff]
  constructor
  · rintro ⟨⟨i, hi⟩ | h, hf⟩
    · exact absurd hi (hf i)
    · exact h
  · exact fun h => ⟨.inr h, fun i ↦ by rw [h i]; decide⟩

@[simp] theorem forallStrong_eq_zero_iff :
    forallStrong p = 0 ↔ (∀ i, p i ≠ -1) ∧ ∃ i, p i = 0 := by
  rw [forallStrong, forallWith_eq_zero_iff, not_or, not_exists, not_forall]
  refine and_congr_right fun hne => exists_congr fun i => ?_
  cases h : p i <;> simp_all

@[simp] theorem existsStrong_eq_one_iff : existsStrong p = 1 ↔ ∃ i, p i = 1 := by
  rw [existsStrong, existsWith_eq_one_iff, and_iff_right_iff_imp]
  exact fun h => .inl h

@[simp] theorem existsStrong_eq_neg_one_iff : existsStrong p = -1 ↔ ∀ i, p i = -1 := by
  rw [existsStrong, existsWith_eq_neg_one_iff]
  constructor
  · rintro ⟨⟨i, hi⟩ | h, hf⟩
    · exact absurd hi (hf i)
    · exact h
  · exact fun h => ⟨.inr h, fun i ↦ by rw [h i]; decide⟩

@[simp] theorem existsStrong_eq_zero_iff :
    existsStrong p = 0 ↔ (∀ i, p i ≠ 1) ∧ ∃ i, p i = 0 := by
  rw [existsStrong, existsWith_eq_zero_iff, not_or, not_exists, not_forall]
  refine and_congr_right fun hne => exists_congr fun i => ?_
  cases h : p i <;> simp_all

end StrongQuantifiers

/-- Haug's universal quantifier skips undefined instances — undefined only when every
instance is, false when some instance is, and true otherwise. -/
noncomputable def forallHaug (p : W → SignType) : SignType :=
  forallWith (∃ w, p w ≠ 0) p

/-- The dual of `forallHaug`. -/
noncomputable def existsHaug (p : W → SignType) : SignType :=
  existsWith (∃ w, p w ≠ 0) p

section HaugQuantifiers

variable {p : W → SignType}

@[simp] theorem forallHaug_eq_zero_iff : forallHaug p = 0 ↔ ∀ w, p w = 0 := by
  rw [forallHaug, forallWith_eq_zero_iff, not_exists]
  simp

@[simp] theorem forallHaug_eq_neg_one_iff : forallHaug p = -1 ↔ ∃ w, p w = -1 := by
  rw [forallHaug, forallWith_eq_neg_one_iff, and_iff_right_iff_imp]
  rintro ⟨w, hw⟩
  exact ⟨w, hw ▸ by decide⟩

@[simp] theorem forallHaug_eq_one_iff :
    forallHaug p = 1 ↔ (∃ w, p w ≠ 0) ∧ ∀ w, p w ≠ -1 := by
  rw [forallHaug, forallWith_eq_one_iff]

@[simp] theorem existsHaug_eq_zero_iff : existsHaug p = 0 ↔ ∀ w, p w = 0 := by
  rw [existsHaug, existsWith_eq_zero_iff, not_exists]
  simp

@[simp] theorem existsHaug_eq_one_iff : existsHaug p = 1 ↔ ∃ w, p w = 1 := by
  rw [existsHaug, existsWith_eq_one_iff, and_iff_right_iff_imp]
  rintro ⟨w, hw⟩
  exact ⟨w, hw ▸ by decide⟩

@[simp] theorem existsHaug_eq_neg_one_iff :
    existsHaug p = -1 ↔ (∃ w, p w ≠ 0) ∧ ∀ w, p w ≠ 1 := by
  rw [existsHaug, existsWith_eq_neg_one_iff]

end HaugQuantifiers

/-! ### Each family restricted to a pair is its binary connective

One lemma carries the correspondence: the gap-policy quantifier at a pair of instances is
the gap-policy connective at the matching policy (`forallWith_pair`), and each family's
pair lemma instantiates it. -/

section Pairs

variable (a b : SignType)

theorem forallWith_pair {D : Prop} [Decidable D] :
    forallWith D (fun i : Bool => bif i then a else b) = meetWith D a b := by
  refine eq_of_eq_zero_iff_of_eq_one_iff ?_ ?_
  · rw [forallWith_eq_zero_iff, meetWith_eq_zero_iff]
  · rw [forallWith_eq_one_iff, meetWith_eq_one_iff, Bool.forall_bool]
    exact and_congr_right fun _ => and_comm

theorem existsWith_pair {D : Prop} [Decidable D] :
    existsWith D (fun i : Bool => bif i then a else b) = joinWith D a b := by
  refine eq_of_eq_zero_iff_of_eq_one_iff ?_ ?_
  · rw [existsWith_eq_zero_iff, joinWith_eq_zero_iff]
  · rw [existsWith_eq_one_iff, joinWith_eq_one_iff, Bool.exists_bool]
    exact and_congr_right fun _ => or_comm

theorem forallWeak_pair : forallWeak (fun i : Bool => bif i then a else b) = meetWeak a b :=
  (forallWith_congr (Bool.forall_bool.trans and_comm)).trans
    ((forallWith_pair a b).trans (meetWeak_eq_meetWith a b).symm)

theorem existsWeak_pair : existsWeak (fun i : Bool => bif i then a else b) = joinWeak a b :=
  (existsWith_congr (Bool.forall_bool.trans and_comm)).trans
    ((existsWith_pair a b).trans (joinWeak_eq_joinWith a b).symm)

theorem forallStrong_pair :
    forallStrong (fun i : Bool => bif i then a else b) = a ⊓ b :=
  (forallWith_congr
      (or_congr (Bool.exists_bool.trans or_comm) (Bool.forall_bool.trans and_comm))).trans
    ((forallWith_pair a b).trans (inf_eq_meetWith a b).symm)

theorem existsStrong_pair :
    existsStrong (fun i : Bool => bif i then a else b) = a ⊔ b :=
  (existsWith_congr
      (or_congr (Bool.exists_bool.trans or_comm) (Bool.forall_bool.trans and_comm))).trans
    ((existsWith_pair a b).trans (sup_eq_joinWith a b).symm)

/-- Haug's universal quantifier restricted to a pair of instances is the conjunction of
[belnap-1970], which skips undefined operands. -/
theorem forallHaug_pair :
    forallHaug (fun i : Bool => bif i then a else b) = meetBelnap a b :=
  (forallWith_congr (Bool.exists_bool.trans or_comm)).trans
    ((forallWith_pair a b).trans (meetBelnap_eq_meetWith a b).symm)

/-- Dually, Haug's existential restricted to a pair is Belnap disjunction. -/
theorem existsHaug_pair :
    existsHaug (fun i : Bool => bif i then a else b) = joinBelnap a b :=
  (existsWith_congr (Bool.exists_bool.trans or_comm)).trans
    ((existsWith_pair a b).trans (joinBelnap_eq_joinWith a b).symm)

end Pairs

/-- An existentially quantified presupposition is true or undefined, never false. -/
theorem existsHaug_presuppose_ne_neg_one (p : W → SignType) :
    existsHaug (fun w => presuppose (p w)) ≠ -1 := by
  simp

/-- Quantifier Projection ([coppock-beaver-2015]'s appendix) lets a presupposition under the
existential project as an existentially quantified presupposition, over bivalent `φ` and
`ψ`. -/
theorem existsHaug_meetWeak_presuppose {φ ψ : W → SignType} (hφ : IsBivalent φ)
    (hψ : IsBivalent ψ) :
    existsHaug (fun w => meetWeak (presuppose (φ w)) (ψ w)) =
      meetWeak (existsHaug fun w => presuppose (φ w))
        (existsHaug fun w => meetWeak (φ w) (ψ w)) := by
  refine eq_of_eq_zero_iff_of_eq_one_iff ?_ ?_
  · simp only [existsHaug_eq_zero_iff, meetWeak_eq_zero_iff, presuppose_eq_zero_iff, hφ.ne_zero,
      hψ.ne_zero, or_false]
    exact ⟨Or.inl, fun h => h.elim id fun h w => (h w).elim⟩
  · simp only [existsHaug_eq_one_iff, meetWeak_eq_one_iff, presuppose_eq_one_iff]
    exact ⟨fun ⟨w, h⟩ => ⟨⟨w, h.1⟩, w, h⟩, fun h => h.2⟩

end Trivalent
