import Mathlib.Data.Set.Basic
import Mathlib.Order.Defs.PartialOrder

/-!
# The criteria-derived preorder

`Preorder.ofCriteria sat criteria` orders a carrier by inclusion of
satisfied criteria: `a ≤ b` iff every criterion in `criteria` that `b`
satisfies, `a` satisfies too. This is [kratzer-1981]'s ordering-source
construction at full generality — the pullback of `⊇` along the
satisfied-set map (`ofCriteria_le_iff_subset`; `Core.Order.PullbackPreorder`
is the bundled, decidability-carrying form of the same pattern).

One construction, several instantiations across the library:

- `Semantics.Modality.Kratzer.kratzerPreorder` / `atLeastAsGoodAs` —
  worlds ordered by an ordering source.
- `Core.Order.NormalityOrder.fromProps` — the same order repackaged as a
  `NormalityOrder` for the default-reasoning infrastructure.
- `Semantics.Attitudes.Desire.worldAtLeastAsGood` — worlds ordered by
  desires (via `atLeastAsGoodAs`).
- `Core.Order.SatisfactionOrdering.ofCriteria` — the bundled
  `Bool`-valued/`List`-criteria specialization with decidable `≤`
  (`SatisfactionOrdering.le_iff_ofCriteria`).
-/

namespace Preorder

variable {α C : Type*}

/-- **The criteria-derived preorder**: `a ≤ b` iff every criterion in
    `criteria` that `b` satisfies, `a` satisfies too —
    [kratzer-1981]'s ordering-source construction
    `{c ∈ A : sat b c} ⊆ {c ∈ A : sat a c}` at full generality. -/
@[reducible] def ofCriteria (sat : α → C → Prop) (criteria : Set C) :
    Preorder α where
  le a b := ∀ c ∈ criteria, sat b c → sat a c
  le_refl _ _ _ h := h
  le_trans _ _ _ hab hbc c hc h := hab c hc (hbc c hc h)

/-- Unfolding lemma for the criteria-derived order. Not `@[simp]` —
    unfolding is opt-in. -/
theorem ofCriteria_le_iff (sat : α → C → Prop) (criteria : Set C) (a b : α) :
    (ofCriteria sat criteria).le a b ↔ ∀ c ∈ criteria, sat b c → sat a c :=
  Iff.rfl

/-- The criteria-derived order is the pullback of `⊇` along the
    satisfied-set map `a ↦ {c ∈ criteria | sat a c}` — the
    `Core.Order.PullbackPreorder` pattern with target `(Set C)ᵒᵈ`. -/
theorem ofCriteria_le_iff_subset (sat : α → C → Prop) (criteria : Set C)
    (a b : α) :
    (ofCriteria sat criteria).le a b ↔
      {c ∈ criteria | sat b c} ⊆ {c ∈ criteria | sat a c} := by
  constructor
  · intro h c hc
    obtain ⟨hcrit, hsat⟩ := Set.mem_sep_iff.mp hc
    exact Set.mem_sep_iff.mpr ⟨hcrit, h c hcrit hsat⟩
  · intro h c hc hsat
    exact (Set.mem_sep_iff.mp (h (Set.mem_sep_iff.mpr ⟨hc, hsat⟩))).2

/-- Fewer criteria, coarser order: dominance over a criteria set transfers
    to any subset. The general form of "adding a proposition to the
    ordering source refines it". -/
theorem ofCriteria_le_of_subset {sat : α → C → Prop}
    {criteria criteria' : Set C} (hsub : criteria ⊆ criteria') {a b : α}
    (h : (ofCriteria sat criteria').le a b) :
    (ofCriteria sat criteria).le a b :=
  fun c hc => h c (hsub hc)

end Preorder
