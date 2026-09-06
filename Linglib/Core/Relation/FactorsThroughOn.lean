import Mathlib.Logic.Function.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Finite.Range
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Factor-through on a subset

This file defines the set-restricted variant of mathlib's
`Function.FactorsThrough`: `g` factors through `f` on a subset `s` of
the domain when, for `a b ∈ s`, equality of `f a` and `f b` forces
equality of `g a` and `g b`.

## Main definitions

* `Function.FactorsThroughOn g f s`: `g` factors through `f` on `s`.

## Main results

* `Function.factorsThroughOn_univ`: equivalent to `Function.FactorsThrough` on `Set.univ`.
* `Function.FactorsThrough.factorsThroughOn`: a global factor-through
  restricts to any subset.
* `Function.not_factorsThroughOn_iff_exists_witness`: refutation by a
  pair of in-set points agreeing on `f` and differing on `g`.
* `Function.FactorsThrough.card_range_le`: a function that factors through
  another takes no more values.
-/

namespace Function

variable {α : Type*} {β : Type*} {γ : Type*}

/-- `g` factors through `f` on `s`: for `a b ∈ s`, `f a = f b` implies
`g a = g b`. -/
def FactorsThroughOn (g : α → γ) (f : α → β) (s : Set α) : Prop :=
  ∀ ⦃a b⦄, a ∈ s → b ∈ s → f a = f b → g a = g b

theorem factorsThroughOn_univ (g : α → γ) (f : α → β) :
    FactorsThroughOn g f Set.univ ↔ FactorsThrough g f :=
  ⟨fun h _ _ hab => h (Set.mem_univ _) (Set.mem_univ _) hab,
   fun h _ _ _ _ hab => h hab⟩

theorem FactorsThrough.factorsThroughOn {g : α → γ} {f : α → β}
    (h : FactorsThrough g f) (s : Set α) : FactorsThroughOn g f s :=
  fun _ _ _ _ hab => h hab

theorem not_factorsThroughOn_iff_exists_witness {g : α → γ} {f : α → β} {s : Set α} :
    ¬ FactorsThroughOn g f s ↔
    ∃ a b, a ∈ s ∧ b ∈ s ∧ f a = f b ∧ g a ≠ g b := by
  simp only [FactorsThroughOn, not_forall, exists_prop]

/-- Factoring through on `s`, existentially: `g` agrees on `s` with some
function of `f`. The mirror of `Function.factorsThrough_iff` for the
set-restricted variant. -/
theorem factorsThroughOn_iff_exists_eqOn [Nonempty γ] {g : α → γ} {f : α → β}
    {s : Set α} :
    FactorsThroughOn g f s ↔ ∃ h : β → γ, Set.EqOn g (h ∘ f) s := by
  constructor
  · intro hf
    classical
    refine ⟨fun b => if hb : ∃ a ∈ s, f a = b then g hb.choose
      else Classical.arbitrary γ, fun a ha => ?_⟩
    have hb : ∃ a' ∈ s, f a' = f a := ⟨a, ha, rfl⟩
    simp only [Function.comp_apply, dif_pos hb]
    exact (hf hb.choose_spec.1 ha hb.choose_spec.2).symm
  · rintro ⟨h, hh⟩ a b ha hb hab
    rw [hh ha, hh hb, Function.comp_apply, Function.comp_apply, hab]

/-- For an **idempotent** `f`, `g` factors through `f` iff `g` is `f`-invariant
(pointwise `g = g ∘ f`). -/
theorem factorsThrough_iff_of_idempotent {g : α → γ} {f : α → α} (hf : ∀ a, f (f a) = f a) :
    FactorsThrough g f ↔ ∀ a, g a = g (f a) :=
  ⟨fun h a => h (hf a).symm,
   fun h a b hab => (h a).trans ((congrArg g hab).trans (h b).symm)⟩

instance {g : α → γ} {f : α → β} {s : Set α}
    [Fintype α] [DecidablePred (· ∈ s)] [DecidableEq β] [DecidableEq γ] :
    Decidable (FactorsThroughOn g f s) := by
  unfold FactorsThroughOn; infer_instance

/-- A function that factors through another takes no more values. -/
theorem FactorsThrough.card_range_le [Finite α] {g : α → γ} {f : α → β}
    (h : FactorsThrough g f) : Nat.card (Set.range g) ≤ Nat.card (Set.range f) := by
  refine Nat.card_le_card_of_surjective (λ b => ⟨g b.2.choose, b.2.choose, rfl⟩) ?_
  rintro ⟨_, a, rfl⟩
  exact ⟨⟨f a, a, rfl⟩, Subtype.ext (h (⟨a, rfl⟩ : ∃ a', f a' = f a).choose_spec)⟩

end Function
