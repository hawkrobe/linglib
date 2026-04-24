import Mathlib.Data.Set.Basic
import Linglib.Theories.Semantics.Entailment.AntiAdditivity

/-!
# Intolerance — Horn 1989 / Gajewski 2011
@cite{horn-1989} @cite{gajewski-2011}

A generalized-quantifier-typed function `f : Set α → Prop` is
**Intolerant** iff it cannot map both a set `x` and its complement `xᶜ`
to truth — equivalently, it sits "above the midpoint" of its scale.

@cite{gajewski-2011} (eq. 80, p. 131) introduces this in the form
"f is Intolerant iff if f is not trivial, then for all x: ¬f x ∨ ¬f xᶜ"
to make Appendix 2's hierarchy `AA ⊆ DE + Intolerant ⊆ DE` work cleanly:
the trivial case is included by stipulation so that the AA inclusion is
not blocked by trivially-true functions.

## Examples

- `no` is Intolerant: `#Few of my friends are linguists and few of them
  aren't` (eq. 82a) — the conjunction is incoherent.
- `fewer than n` is *not* Intolerant when scale density permits:
  `Fewer than 4 of my friends are linguists and fewer than 4 aren't`
  (eq. 83) is consistent if I have ≤ 6 friends.

## Hierarchy

Appendix 2 (p. 143) proves `AA ⊆ DE + Intolerant`. The reverse inclusion
`DE + Intolerant ⊆ DE` is trivial. The strict inclusion (`AA ⊊ DE +
Intolerant`) is asserted but not proved by Gajewski; would need a witness
function that is DE + Intolerant but not AA.
-/

namespace Semantics.Entailment.Intolerance

/-- A GQ-typed function is **trivial** if it is constantly true or
    constantly false. -/
def IsTrivial {α : Type*} (f : Set α → Prop) : Prop :=
  (∀ x : Set α, f x) ∨ (∀ x : Set α, ¬ f x)

/-- @cite{gajewski-2011} eq. 80: a function `f : Set α → Prop` is
    **Intolerant** iff it is trivial, OR for every `x`, at most one of
    `f x` and `f xᶜ` holds.

    @cite{horn-1989}: Intolerant functions are "above the midpoint of
    their scale" — they cannot accept both a property and its
    complement. -/
def IsIntolerant {α : Type*} (f : Set α → Prop) : Prop :=
  IsTrivial f ∨ ∀ x : Set α, ¬ f x ∨ ¬ f xᶜ

/-- A GQ-typed AA function (`f : Set α → Prop` with `f (p ∪ q) ↔ f p ∧ f q`). -/
def IsAntiAdditiveGQ {α : Type*} (f : Set α → Prop) : Prop :=
  ∀ p q : Set α, f (p ∪ q) ↔ f p ∧ f q

/-- A GQ-typed DE function. -/
def IsDownwardEntailingGQ {α : Type*} (f : Set α → Prop) : Prop :=
  ∀ p q : Set α, p ⊆ q → f q → f p

/-- AA-GQ implies DE-GQ. Standard. -/
theorem isAntiAdditiveGQ_implies_isDEGQ {α : Type*} (f : Set α → Prop)
    (hAA : IsAntiAdditiveGQ f) : IsDownwardEntailingGQ f := by
  intro p q hpq hfq
  -- Show f p from f q via p ⊆ q ⇒ q = p ∪ q ⇒ f q ↔ f p ∧ f q ⇒ f p
  have hUnion : p ∪ q = q := by
    ext x; constructor
    · rintro (h | h)
      · exact hpq h
      · exact h
    · intro h; exact Or.inr h
  have : f (p ∪ q) := by rw [hUnion]; exact hfq
  exact ((hAA p q).mp this).1

/-- @cite{gajewski-2011} Appendix 2 (p. 143): AA implies Intolerant.

    Proof sketch (Gajewski's): suppose `f` is AA and not trivial. For
    arbitrary `a`, suppose `f a = True` and `f aᶜ = True`. Then
    `f (a ∪ aᶜ) ↔ f a ∧ f aᶜ` gives `f Set.univ = True`. Since AA
    implies DE, every `y ⊆ Set.univ` has `f y = True` — contradicting
    non-triviality. So either `¬f a` or `¬f aᶜ`. -/
theorem antiAdditiveGQ_implies_intolerant {α : Type*} (f : Set α → Prop)
    (hAA : IsAntiAdditiveGQ f) : IsIntolerant f := by
  -- Use classical reasoning on whether f is trivial
  by_cases hTriv : IsTrivial f
  · -- Trivial case: trivially Intolerant by Or.inl
    exact Or.inl hTriv
  · -- Non-trivial case: prove ∀ x, ¬f x ∨ ¬f xᶜ
    refine Or.inr ?_
    intro x
    by_contra hNeither
    push_neg at hNeither
    obtain ⟨hfx, hfxc⟩ := hNeither
    -- Now f x = True and f xᶜ = True. Show f Set.univ = True via AA.
    have hUnion : x ∪ xᶜ = Set.univ := by
      ext y
      simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_univ, iff_true]
      exact Classical.em (y ∈ x)
    have hfUniv : f Set.univ := by
      rw [← hUnion]
      exact (hAA x xᶜ).mpr ⟨hfx, hfxc⟩
    -- By DE (which AA implies), every y has f y
    have hDE := isAntiAdditiveGQ_implies_isDEGQ f hAA
    -- Contradicts non-triviality: ∃ y, ¬ f y (since f isn't constantly false:
    -- f Set.univ holds; and not constantly true since not trivial)
    apply hTriv
    left
    intro y
    exact hDE y Set.univ (fun _ _ => trivial) hfUniv

end Semantics.Entailment.Intolerance
