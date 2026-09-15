import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Basic
import Linglib.Semantics.Presupposition.Trivalent
import Linglib.Logic.Trivalent.Prop3
import Linglib.Semantics.Dynamic.UpdateSemantics.Basic
import Linglib.Data.Examples.Yagi2025

/-!
# Yagi (2025): Conflicting Presuppositions in Disjunction

This file formalizes [yagi-2025]'s survey of disjunctions whose disjuncts carry contradictory
presuppositions (`Conflict`), *Either the King of Buganda is opening parliament or the
President of Buganda is conducting the ceremony*. Such a disjunction presupposes the
disjunction of the two presuppositions and is false when that holds and both disjuncts are
false. Four theories fail the second observation. Under Strong Kleene disjunction the sentence
is true whenever defined, so it is never false and its negation never true
(`orStrong_ne_false`, `neg_orStrong_ne_true`); the symmetric two-dimensional definition of
[karttunen-peters-1979] has a presupposition that entails the assertion
(`orKPSymmetric_ne_false`), and replacing it by the disjunction of the presuppositions
(`orSeven`) fixes the case but predicts a tautologous presupposition for *either baldness is
not hereditary or all of Bill's children are bald* (`orSeven_presup_of_left`); the update
of [heim-1982] and [beaver-2001], with failure as a designated state, is defined only when the
first disjunct already holds throughout the input, so it is uninformative wherever defined
(`disjS_eq_some_iff`); and the local contexts of [schlenker-2009] admit only worlds where one
disjunct is defined and true (`local_contexts_force_truth`). Of the two reactions, the
meta-assertion operator of [beaver-krahmer-2001] makes the disjunction false, but also where
neither presupposition holds, and leaves it presuppositionless (`or_assertMeta_false_iff`,
`or_assertMeta_presup`); inserting it on one disjunct under Strong Kleene yields only a
conditional presupposition (`orStrong_assertMeta_presup_iff`). Flexible accommodation splits
the input by two accommodated propositions (`flexS`). With the default tautologies it is
never defined under conflict (`flexS_top_eq_none`) and violates genuineness when a
presupposition contradicts the other disjunct (`not_genuine_top`); accommodating each
disjunct's negated rival presupposition derives both observations (`flexS_split_eq_some_iff`,
`negOf_flexS_split`), at the cost of demanding accommodation where the standard update
filters the presupposition away (`exists_disjS_some_flexS_top_none`).

## Implementation notes

The designated undefined state of the update semantics is `none` on `Option (State W)`, with
union and subtraction absorbing it. The meta-assertion operator is stated on partial
propositions and agrees with the trivalent `Prop3.metaAssert` (`eval_assertMeta`). The
licensing constraint on the operator is not modelled.

## References

* [yagi-2025]
* [beaver-2001]
* [beaver-krahmer-2001]
* [geurts-2005]
* [heim-1982]
* [karttunen-peters-1979]
* [schlenker-2009]
* [zimmermann-2000]
-/

namespace Yagi2025

open Presupposition Trivalent UpdateSemantics Classical

variable {W : Type*}

/-- Two partial propositions have conflicting presuppositions. -/
def Conflict (φ ψ : PartialProp W) : Prop := ∀ w, ¬ (φ.presup w ∧ ψ.presup w)

/-- A partial proposition whose presupposition entails its assertion is never false. -/
theorem eval_ne_false_of_imp {d : PartialProp W} {w : W} (h : d.presup w → d.assertion w) :
    d.eval w ≠ .false := by
  by_cases hp : d.presup w
  · simp [PartialProp.eval, hp, h hp]
  · simp [PartialProp.eval, hp]

/-- Its negation is never true. -/
theorem eval_neg_ne_true_of_imp {d : PartialProp W} {w : W}
    (h : d.presup w → d.assertion w) : (PartialProp.neg d).eval w ≠ .true := by
  by_cases hp : d.presup w
  · simp [PartialProp.eval, PartialProp.neg, hp, h hp]
  · simp [PartialProp.eval, PartialProp.neg, hp]

/-! ### Strong Kleene and two-dimensional disjunction -/

variable {φ ψ : PartialProp W}

/-- Under conflict, the Strong Kleene presupposition entails the assertion. -/
theorem orStrong_presup_imp (h : Conflict φ ψ) (w : W) :
    (PartialProp.orStrong φ ψ).presup w → (PartialProp.orStrong φ ψ).assertion w := by
  rintro (hpq | hφ | hψ)
  · exact absurd hpq (h w)
  · exact Or.inl hφ
  · exact Or.inr hψ

/-- The Strong Kleene disjunction is never false. -/
theorem orStrong_ne_false (h : Conflict φ ψ) (w : W) :
    (PartialProp.orStrong φ ψ).eval w ≠ .false :=
  eval_ne_false_of_imp (orStrong_presup_imp h w)

/-- Its negation is never true. -/
theorem neg_orStrong_ne_true (h : Conflict φ ψ) (w : W) :
    (PartialProp.neg (PartialProp.orStrong φ ψ)).eval w ≠ .true :=
  eval_neg_ne_true_of_imp (orStrong_presup_imp h w)

/-- The symmetric two-dimensional disjunction is never false either. -/
theorem orKPSymmetric_ne_false (h : Conflict φ ψ) (w : W) :
    (PartialProp.orKPSymmetric φ ψ).eval w ≠ .false :=
  eval_ne_false_of_imp (PartialProp.orKPSymmetric_presup_entails_when_conflicting φ ψ w (h w))

/-- The modified two-dimensional disjunction whose presupposition is the disjunction of the
presuppositions. -/
def orSeven (φ ψ : PartialProp W) : PartialProp W where
  presup w := φ.presup w ∨ ψ.presup w
  assertion w := φ.assertion w ∨ ψ.assertion w

/-- The modification is false exactly where a presupposition holds and both assertions fail. -/
theorem orSeven_eval_false_iff (w : W) :
    (orSeven φ ψ).eval w = .false ↔
      (φ.presup w ∨ ψ.presup w) ∧ ¬ φ.assertion w ∧ ¬ ψ.assertion w := by
  by_cases hp : φ.presup w ∨ ψ.presup w <;> simp [PartialProp.eval, orSeven, hp]

/-- With a presuppositionless first disjunct the modification presupposes nothing. -/
theorem orSeven_presup_of_left (h : ∀ w, φ.presup w) (w : W) : (orSeven φ ψ).presup w :=
  Or.inl (h w)

/-! ### Update semantics with a designated undefined state -/

@[simp] theorem mem_prop {p : W → Prop} {s : State W} {w : W} :
    w ∈ Update.prop p s ↔ w ∈ s ∧ p w := Iff.rfl

/-- Union with the undefined state absorbing. -/
def unionU : Option (State W) → Option (State W) → Option (State W)
  | some a, some b => some (a ∪ b)
  | _, _ => none

@[simp] theorem unionU_some_some (a b : State W) : unionU (some a) (some b) = some (a ∪ b) :=
  rfl

@[simp] theorem unionU_none_left (b : Option (State W)) : unionU none b = none := by
  cases b <;> rfl

@[simp] theorem unionU_none_right (a : Option (State W)) : unionU a none = none := by
  cases a <;> rfl

/-- Update by a partial proposition: undefined unless the presupposition holds throughout. -/
noncomputable def updateS (φ : PartialProp W) (s : State W) : Option (State W) :=
  if ∀ w ∈ s, φ.presup w then some (Update.prop φ.assertion s) else none

/-- Negation of an update: the input minus the result. -/
def negOf (upd : State W → Option (State W)) (s : State W) : Option (State W) :=
  (upd s).map (s \ ·)

/-- Disjunction: the first update, joined with the second in the negation of the first. -/
noncomputable def disjS (φ ψ : PartialProp W) (s : State W) : Option (State W) :=
  unionU (updateS φ s) ((negOf (updateS φ) s).bind (updateS ψ))

theorem updateS_eq_some_iff {s t : State W} :
    updateS φ s = some t ↔ (∀ w ∈ s, φ.presup w) ∧ t = Update.prop φ.assertion s := by
  unfold updateS
  split_ifs with h
  · exact ⟨λ e => ⟨h, (Option.some_inj.mp e).symm⟩, λ e => by rw [e.2]⟩
  · exact iff_of_false (by simp) (λ e => h e.1)

theorem updateS_eq_none_iff {s : State W} :
    updateS φ s = none ↔ ¬ ∀ w ∈ s, φ.presup w := by
  unfold updateS
  split_ifs with h
  · exact iff_of_false (by simp) (not_not.2 h)
  · exact iff_of_true rfl h

/-- The disjunction is defined exactly when the first presupposition holds throughout the
input and the second holds wherever the first disjunct fails. -/
theorem disjS_isSome_iff (s : State W) :
    (disjS φ ψ s).isSome ↔
      (∀ w ∈ s, φ.presup w) ∧ ∀ w ∈ s, ¬ φ.assertion w → ψ.presup w := by
  unfold disjS negOf
  by_cases hp : ∀ w ∈ s, φ.presup w
  · rw [updateS_eq_some_iff.2 ⟨hp, rfl⟩, Option.map_some, Option.bind_some]
    have hiff : (∀ w ∈ s \ Update.prop φ.assertion s, ψ.presup w) ↔
        ∀ w ∈ s, ¬ φ.assertion w → ψ.presup w := by
      constructor
      · intro hq w hw hφ; exact hq w ⟨hw, λ h => hφ h.2⟩
      · intro hq w hw; exact hq w hw.1 (λ h => hw.2 ⟨hw.1, h⟩)
    by_cases hq : ∀ w ∈ s \ Update.prop φ.assertion s, ψ.presup w
    · rw [updateS_eq_some_iff.2 ⟨hq, rfl⟩, unionU_some_some]
      exact iff_of_true rfl ⟨hp, hiff.1 hq⟩
    · rw [updateS_eq_none_iff.2 hq, unionU_none_right]
      exact iff_of_false (by simp) (λ h => hq (hiff.2 h.2))
  · rw [updateS_eq_none_iff.2 hp, unionU_none_left]
    exact iff_of_false (by simp) (λ h => hp h.1)

/-- Under conflict the disjunction is defined only when the first disjunct already holds
throughout the input, and then it returns the input: defined only if uninformative. -/
theorem disjS_eq_some_iff (h : Conflict φ ψ) (s t : State W) :
    disjS φ ψ s = some t ↔
      (∀ w ∈ s, φ.presup w) ∧ (∀ w ∈ s, φ.assertion w) ∧ t = s := by
  have hempty : updateS ψ (s \ s) = some ∅ :=
    updateS_eq_some_iff.2 ⟨by simp, by ext w; simp⟩
  constructor
  · intro ht
    have hs := (disjS_isSome_iff s).1 (by rw [ht]; rfl)
    have hφ : ∀ w ∈ s, φ.assertion w := λ w hw =>
      by_contra λ hn => h w ⟨hs.1 w hw, hs.2 w hw hn⟩
    refine ⟨hs.1, hφ, ?_⟩
    have hprop : Update.prop φ.assertion s = s :=
      Set.ext λ w => ⟨λ h => h.1, λ hw => ⟨hw, hφ w hw⟩⟩
    rw [disjS, negOf, updateS_eq_some_iff.2 ⟨hs.1, rfl⟩, hprop, Option.map_some,
      Option.bind_some, hempty, unionU_some_some, Set.union_empty] at ht
    exact (Option.some_inj.mp ht).symm
  · rintro ⟨hp, hφ, ht⟩
    have hprop : Update.prop φ.assertion s = s :=
      Set.ext λ w => ⟨λ h => h.1, λ hw => ⟨hw, hφ w hw⟩⟩
    rw [disjS, negOf, updateS_eq_some_iff.2 ⟨hp, rfl⟩, hprop, Option.map_some, Option.bind_some,
      hempty, unionU_some_some, Set.union_empty, ht]

/-! ### Local contexts -/

/-- If each disjunct's presupposition is entailed by its local context, the negation of the
other disjunct within the global context, then under conflict every world of the global
context makes some disjunct defined and true. -/
theorem local_contexts_force_truth (h : Conflict φ ψ) (s : State W)
    (h₁ : ∀ w ∈ s, ¬ (φ.presup w ∧ φ.assertion w) → ψ.presup w)
    (h₂ : ∀ w ∈ s, ¬ (ψ.presup w ∧ ψ.assertion w) → φ.presup w) :
    ∀ w ∈ s, (φ.presup w ∧ φ.assertion w) ∨ (ψ.presup w ∧ ψ.assertion w) := by
  intro w hw
  by_cases hp : φ.presup w
  · exact Or.inl (by_contra λ hn => h w ⟨hp, h₁ w hw hn⟩)
  · exact Or.inr (by_contra λ hn => hp (h₂ w hw hn))

/-! ### The meta-assertion operator -/

/-- The meta-assertion operator: always defined, true where the proposition is defined and
true. -/
def assertMeta (φ : PartialProp W) : PartialProp W where
  presup _ := True
  assertion w := φ.presup w ∧ φ.assertion w

/-- It agrees with the trivalent operator. -/
theorem eval_assertMeta (w : W) : (assertMeta φ).eval w = Prop3.metaAssert φ.eval w := by
  by_cases hp : φ.presup w <;> by_cases ha : φ.assertion w <;>
    simp [PartialProp.eval, assertMeta, hp, ha, Trivalent.metaAssert]

/-- The disjunction of two meta-asserted disjuncts has no presupposition. -/
theorem or_assertMeta_presup (w : W) :
    (PartialProp.or (assertMeta φ) (assertMeta ψ)).presup w :=
  ⟨trivial, trivial⟩

/-- It is false whenever neither disjunct is defined and true, so also where neither
presupposition holds. -/
theorem or_assertMeta_false_iff (w : W) :
    (PartialProp.or (assertMeta φ) (assertMeta ψ)).eval w = .false ↔
      ¬ (φ.presup w ∧ φ.assertion w) ∧ ¬ (ψ.presup w ∧ ψ.assertion w) := by
  simp [PartialProp.eval, PartialProp.or, assertMeta, not_or]

/-- Meta-asserting one disjunct under Strong Kleene yields the conditional presupposition
that the first presupposition holds unless the second disjunct is defined and true. -/
theorem orStrong_assertMeta_presup_iff (w : W) :
    (PartialProp.orStrong φ (assertMeta ψ)).presup w ↔
      (¬ (ψ.presup w ∧ ψ.assertion w) → φ.presup w) := by
  simp only [PartialProp.orStrong, assertMeta, and_true, true_and]
  constructor
  · rintro (hp | ⟨hp, -⟩ | hψ) <;> intro hn
    · exact hp
    · exact hp
    · exact absurd hψ hn
  · intro hc
    by_cases hψ : ψ.presup w ∧ ψ.assertion w
    · exact Or.inr (Or.inr hψ)
    · exact Or.inl (hc hψ)

/-! ### Flexible accommodation -/

/-- The update by a disjunction whose disjuncts are evaluated in the input restricted by the
accommodated propositions `χ` and `ω`. -/
noncomputable def flexS (χ ω : W → Prop) (φ ψ : PartialProp W) (s : State W) :
    Option (State W) :=
  unionU (updateS φ (Update.prop χ s)) (updateS ψ (Update.prop ω s))

/-- The accommodated propositions split the input. -/
def Splits (χ ω : W → Prop) (s : State W) : Prop := Update.prop χ s ∪ Update.prop ω s = s

theorem splits_top (s : State W) : Splits (λ _ => True) (λ _ => True) s := by
  ext w; simp

/-- Each disjunct's negated rival presupposition splits any input under conflict. -/
theorem splits_of_conflict (h : Conflict φ ψ) (s : State W) :
    Splits (λ w => ¬ ψ.presup w) (λ w => ¬ φ.presup w) s := by
  ext w
  simp only [Set.mem_union, mem_prop]
  constructor
  · rintro (⟨hw, -⟩ | ⟨hw, -⟩) <;> exact hw
  · intro hw
    by_cases hp : φ.presup w
    · exact Or.inl ⟨hw, λ hq => h w ⟨hp, hq⟩⟩
    · exact Or.inr ⟨hw, hp⟩

theorem prop_top (s : State W) : Update.prop (λ _ : W => True) s = s := by ext w; simp

/-- With the default tautologies the update is defined exactly when both presuppositions
hold throughout, and then returns the worlds verifying either assertion. -/
theorem flexS_top_eq_some_iff (s t : State W) :
    flexS (λ _ => True) (λ _ => True) φ ψ s = some t ↔
      (∀ w ∈ s, φ.presup w) ∧ (∀ w ∈ s, ψ.presup w) ∧
        t = Update.prop φ.assertion s ∪ Update.prop ψ.assertion s := by
  simp only [flexS, prop_top]
  by_cases hp : ∀ w ∈ s, φ.presup w
  · by_cases hq : ∀ w ∈ s, ψ.presup w
    · rw [updateS_eq_some_iff.2 ⟨hp, rfl⟩, updateS_eq_some_iff.2 ⟨hq, rfl⟩, unionU_some_some]
      exact ⟨λ e => ⟨hp, hq, (Option.some_inj.mp e).symm⟩, λ e => by rw [e.2.2]⟩
    · rw [updateS_eq_none_iff.2 hq, unionU_none_right]
      exact iff_of_false (by simp) (λ e => hq e.2.1)
  · rw [updateS_eq_none_iff.2 hp, unionU_none_left]
    exact iff_of_false (by simp) (λ e => hp e.1)

/-- Under conflict the default is never defined on a nonempty input. -/
theorem flexS_top_eq_none (h : Conflict φ ψ) {s : State W} (hs : s.Nonempty) :
    flexS (λ _ => True) (λ _ => True) φ ψ s = none := by
  obtain ⟨w, hw⟩ := hs
  cases ht : flexS (λ _ => True) (λ _ => True) φ ψ s with
  | none => rfl
  | some t =>
    obtain ⟨hp, hq, -⟩ := (flexS_top_eq_some_iff s t).1 ht
    exact absurd ⟨hp w hw, hq w hw⟩ (h w)

/-- Accommodating each disjunct's negated rival presupposition, the update is defined exactly
when some presupposition holds at every world of the input, and returns the worlds where a
disjunct is defined and true. -/
theorem flexS_split_eq_some_iff (h : Conflict φ ψ) (s t : State W) :
    flexS (λ w => ¬ ψ.presup w) (λ w => ¬ φ.presup w) φ ψ s = some t ↔
      (∀ w ∈ s, φ.presup w ∨ ψ.presup w) ∧
        t = {w ∈ s | (φ.presup w ∧ φ.assertion w) ∨ (ψ.presup w ∧ ψ.assertion w)} := by
  have key : (∀ w ∈ Update.prop (λ w => ¬ ψ.presup w) s, φ.presup w) ∧
      (∀ w ∈ Update.prop (λ w => ¬ φ.presup w) s, ψ.presup w) ↔
        ∀ w ∈ s, φ.presup w ∨ ψ.presup w := by
    constructor
    · rintro ⟨h₁, h₂⟩ w hw
      by_cases hq : ψ.presup w
      · exact Or.inr hq
      · exact Or.inl (h₁ w ⟨hw, hq⟩)
    · intro hor
      exact ⟨λ w hw => (hor w hw.1).resolve_right hw.2,
        λ w hw => (hor w hw.1).resolve_left hw.2⟩
  have hset : ∀ (h₁ : ∀ w ∈ Update.prop (λ w => ¬ ψ.presup w) s, φ.presup w)
      (h₂ : ∀ w ∈ Update.prop (λ w => ¬ φ.presup w) s, ψ.presup w),
      Update.prop φ.assertion (Update.prop (λ w => ¬ ψ.presup w) s) ∪
        Update.prop ψ.assertion (Update.prop (λ w => ¬ φ.presup w) s) =
      {w ∈ s | (φ.presup w ∧ φ.assertion w) ∨ (ψ.presup w ∧ ψ.assertion w)} := by
    intro h₁ h₂
    ext w
    simp only [Set.mem_union, mem_prop, Set.mem_ofPred_eq]
    constructor
    · rintro (⟨⟨hw, hq⟩, hφ⟩ | ⟨⟨hw, hp⟩, hψ⟩)
      · exact ⟨hw, Or.inl ⟨h₁ w ⟨hw, hq⟩, hφ⟩⟩
      · exact ⟨hw, Or.inr ⟨h₂ w ⟨hw, hp⟩, hψ⟩⟩
    · rintro ⟨hw, ⟨hp, hφ⟩ | ⟨hq, hψ⟩⟩
      · exact Or.inl ⟨⟨hw, λ hq => h w ⟨hp, hq⟩⟩, hφ⟩
      · exact Or.inr ⟨⟨hw, λ hp => h w ⟨hp, hq⟩⟩, hψ⟩
  simp only [flexS]
  by_cases h₁ : ∀ w ∈ Update.prop (λ w => ¬ ψ.presup w) s, φ.presup w
  · by_cases h₂ : ∀ w ∈ Update.prop (λ w => ¬ φ.presup w) s, ψ.presup w
    · rw [updateS_eq_some_iff.2 ⟨h₁, rfl⟩, updateS_eq_some_iff.2 ⟨h₂, rfl⟩,
        unionU_some_some, hset h₁ h₂]
      exact ⟨λ e => ⟨key.1 ⟨h₁, h₂⟩, (Option.some_inj.mp e).symm⟩,
        λ e => by rw [e.2]⟩
    · rw [updateS_eq_none_iff.2 h₂, unionU_none_right]
      exact iff_of_false (by simp) (λ e => h₂ (key.2 e.1).2)
  · rw [updateS_eq_none_iff.2 h₁, unionU_none_left]
    exact iff_of_false (by simp) (λ e => h₁ (key.2 e.1).1)

/-- The negation of the split update removes exactly the worlds where both disjuncts are
false: the disjunction can be false. -/
theorem negOf_flexS_split (h : Conflict φ ψ) {s : State W}
    (hs : ∀ w ∈ s, φ.presup w ∨ ψ.presup w) :
    negOf (flexS (λ w => ¬ ψ.presup w) (λ w => ¬ φ.presup w) φ ψ) s =
      some {w ∈ s |
        ¬ (φ.presup w ∧ φ.assertion w) ∧ ¬ (ψ.presup w ∧ ψ.assertion w)} := by
  rw [negOf, (flexS_split_eq_some_iff h s _).2 ⟨hs, rfl⟩, Option.map_some]
  congr 1
  ext w
  simp only [Set.mem_sdiff, Set.mem_ofPred_eq, not_and, not_or]
  tauto

/-- Genuineness: each disjunct is defined and true at some world of the input that survives
the update. -/
def Genuine (upd : State W → Option (State W)) (φ ψ : PartialProp W) (s : State W) : Prop :=
  (∃ w ∈ s, φ.presup w ∧ φ.assertion w ∧ ∃ t, upd s = some t ∧ w ∈ t) ∧
    (∃ w ∈ s, ψ.presup w ∧ ψ.assertion w ∧ ∃ t, upd s = some t ∧ w ∈ t)

/-- When the first assertion contradicts the second presupposition, the default update, where
defined, violates genuineness: it presupposes the second presupposition throughout, which
empties the first disjunct. -/
theorem not_genuine_top (h : ∀ w, ¬ (φ.assertion w ∧ ψ.presup w)) {s t : State W}
    (ht : flexS (λ _ => True) (λ _ => True) φ ψ s = some t) :
    ¬ Genuine (flexS (λ _ => True) (λ _ => True) φ ψ) φ ψ s := by
  rintro ⟨⟨w, hw, -, hφ, -⟩, -⟩
  exact h w ⟨hφ, ((flexS_top_eq_some_iff s t).1 ht).2.1 w hw⟩

/-- The standard update filters a presupposition entailed by the negation of the first
disjunct, where the default accommodation still demands it: a singleton input where the
first disjunct holds and the second presupposition fails. -/
theorem exists_disjS_some_flexS_top_none (hφ : ∀ w, φ.presup w) {w : W}
    (hw : φ.assertion w) (hq : ¬ ψ.presup w) :
    (disjS φ ψ {w}).isSome ∧ flexS (λ _ => True) (λ _ => True) φ ψ {w} = none := by
  refine ⟨(disjS_isSome_iff _).2 ⟨λ _ _ => hφ _, ?_⟩, ?_⟩
  · rintro v rfl hv
    exact absurd hw hv
  · cases ht : flexS (λ _ => True) (λ _ => True) φ ψ {w} with
    | none => rfl
    | some t => exact absurd (((flexS_top_eq_some_iff _ t).1 ht).2.1 w rfl) hq

/-! ### The ideal input -/

/-- The four worlds of the ideal input: king opening, king not opening, president conducting,
president not conducting. -/
abbrev IW := Fin 4

/-- *The King of Buganda is opening parliament*. -/
def kingOpens : PartialProp IW where
  presup w := w < 2
  assertion w := w = 0

/-- *The President of Buganda is conducting the ceremony*. -/
def presidentConducts : PartialProp IW where
  presup w := 2 ≤ w
  assertion w := w = 2

theorem conflict_buganda : Conflict kingOpens presidentConducts := by
  unfold Conflict kingOpens presidentConducts; decide

/-- On the ideal input the split update keeps the worlds where the head of state performs
the duty, and its negation the others. -/
theorem buganda_split :
    flexS (λ w => ¬ presidentConducts.presup w) (λ w => ¬ kingOpens.presup w) kingOpens
      presidentConducts Set.univ = some {0, 2} ∧
    negOf (flexS (λ w => ¬ presidentConducts.presup w) (λ w => ¬ kingOpens.presup w)
      kingOpens presidentConducts) Set.univ = some {1, 3} := by
  have hs : ∀ w ∈ (Set.univ : Set IW), kingOpens.presup w ∨ presidentConducts.presup w := by
    unfold kingOpens presidentConducts
    intro w _; fin_cases w <;> decide
  constructor
  · rw [flexS_split_eq_some_iff conflict_buganda]
    refine ⟨hs, ?_⟩
    ext w
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq, Set.mem_univ,
      true_and, kingOpens, presidentConducts]
    fin_cases w <;> decide
  · rw [negOf_flexS_split conflict_buganda hs]
    congr 1
    ext w
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq, Set.mem_univ,
      true_and, kingOpens, presidentConducts]
    fin_cases w <;> decide

end Yagi2025
