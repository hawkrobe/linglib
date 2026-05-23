import Mathlib.Logic.Basic
import Mathlib.Logic.ExistsUnique
import Mathlib.Logic.Nontrivial.Basic

/-!
# Exclusive satisfaction of a predicate

Pure-logic facts about *exclusive* satisfiers of a predicate `P : D → Prop`:
the property "`d` is the unique element where `P` holds." These show up
constantly in formalizations of free-choice / exhaustification (where each
"pre-exhaustified domain alternative" says "only this `d` satisfies the
prejacent") but the facts themselves are framework-agnostic.

## Main results

* `exclusive_pairwise_inconsistent` — two distinct elements cannot both be
  the exclusive satisfier.
* `neg_all_exclusive_alts` — if at least one element satisfies `P` and no
  element is the exclusive satisfier, then at least two distinct elements
  satisfy `P`.
* `exclusive_false_of_universal` — if every element satisfies `P` (and `D`
  has at least two elements), then no element is the exclusive satisfier.

Naming follows mathlib idiom: theorems describe what they prove rather
than the EFCI-literature label, so non-EFCI consumers can find them.
-/

namespace Core.Quantification

variable {D : Type*}

/-- **Pairwise inconsistency of exclusive alternatives**: two distinct
elements cannot simultaneously be the unique satisfier of `P`. This is
the structural fact behind Spector's closure-failure observation for
free-choice item alternative sets: the pre-exhaustified domain
alternatives (each saying "only this element satisfies the prejacent")
are pairwise incompatible. -/
theorem exclusive_pairwise_inconsistent (P : D → Prop) {d₁ d₂ : D}
    (hne : d₁ ≠ d₂) :
    ¬((P d₁ ∧ ∀ e, e ≠ d₁ → ¬P e) ∧ (P d₂ ∧ ∀ e, e ≠ d₂ → ¬P e)) := by
  rintro ⟨⟨_, hexcl₁⟩, hPd₂, _⟩
  exact hexcl₁ d₂ hne.symm hPd₂

/-- **Existence plus no-exclusive-satisfier forces plurality**: if `P`
holds somewhere and no element is the exclusive satisfier, then at least
two distinct elements satisfy `P`. -/
theorem neg_all_exclusive_alts (P : D → Prop)
    (hExist : ∃ d, P d)
    (hNegExcl : ∀ d, ¬(P d ∧ ∀ e, e ≠ d → ¬P e)) :
    ∃ d₁ d₂, d₁ ≠ d₂ ∧ P d₁ ∧ P d₂ := by
  obtain ⟨d, hd⟩ := hExist
  by_contra hNoTwo
  exact hNegExcl d ⟨hd, fun e hne hPe => hNoTwo ⟨e, d, hne, hPe, hd⟩⟩

/-- **Universality kills exclusive satisfiers**: if every element of a
non-trivial domain satisfies `P`, then no element is the exclusive
satisfier (there's always some other `e ≠ d` that also satisfies `P`). -/
theorem exclusive_false_of_universal {a b : D} (hab : a ≠ b) (P : D → Prop)
    (hAll : ∀ d, P d) :
    ∀ d, ¬(P d ∧ ∀ e, e ≠ d → ¬P e) := by
  intro d hand
  obtain ⟨_, hexcl⟩ := hand
  haveI : Nontrivial D := ⟨⟨a, b, hab⟩⟩
  obtain ⟨e, hne⟩ := exists_ne d
  exact hexcl e hne (hAll e)

/-- **Uniqueness precludes universality** (contrapositive of
`exclusive_false_of_universal`): in a non-trivial domain, if exactly one
element satisfies `P`, then not every element does. -/
theorem uniqueness_precludes_universality {a b : D} (hab : a ≠ b)
    (P : D → Prop) (hUniq : ∃ d, P d ∧ ∀ e, P e → e = d) :
    ¬∀ d, P d := by
  obtain ⟨d, _, huniq⟩ := hUniq
  intro hall
  exact hab ((huniq a (hall a)).trans (huniq b (hall b)).symm)

end Core.Quantification
