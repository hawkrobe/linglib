import Linglib.Semantics.Quantification.Quantifier

/-!
# Quantifier domain restriction

A quantifier's domain is restricted by a contextual predicate intersected with the
restrictor: `every_restricted C R S` is `every_sem` of `C ∩ R` and `S`, and likewise
`some_restricted` and `no_restricted` ([von-fintel-1994], [stanley-szab-2000]); *every* and
*no* are antitone in the restrictor and *some* monotone, `every_restricted_anti_mono`.
Restriction by intersection is well defined because natural-language determiners are
conservative ([barwise-cooper-1981]), `conservative_domain_restricted`.

## References

* [K. von Fintel, *Restrictions on quantifier domains* (1994)][von-fintel-1994]
* [J. Stanley, Z. Gendler Szabó, *On quantifier domain restriction*
  (2000)][stanley-szab-2000]
* [J. Barwise, R. Cooper, *Generalized quantifiers and natural language*
  (1981)][barwise-cooper-1981]
-/

namespace Quantification.DomainRestriction

/-! ### Domain-restricted quantifiers -/

/-- A domain restrictor is a predicate selecting contextually relevant entities. -/
abbrev DomainRestrictor (E : Type*) := Set E

/-- Domain-restricted ⟦every⟧: ∀x. C(x) ∧ R(x) → S(x).
    Restricts the quantifier domain to entities satisfying C. -/
def every_restricted {α : Type*}
    (C : DomainRestrictor α) (R S : α → Prop) : Prop :=
  every_sem (λ x => C x ∧ R x) S

/-- Domain-restricted ⟦some⟧: ∃x. C(x) ∧ R(x) ∧ S(x). -/
def some_restricted {α : Type*}
    (C : DomainRestrictor α) (R S : α → Prop) : Prop :=
  some_sem (λ x => C x ∧ R x) S

/-- Domain-restricted ⟦no⟧: ¬∃x. C(x) ∧ R(x) ∧ S(x). -/
def no_restricted {α : Type*}
    (C : DomainRestrictor α) (R S : α → Prop) : Prop :=
  no_sem (λ x => C x ∧ R x) S

/-! ### Unrestricted recovery -/

/-- Unrestricted domain recovers the standard quantifier:
    ⟦every⟧_{λ_.True}(R)(S) = ⟦every⟧(R)(S). -/
theorem every_unrestricted {α : Type*}
    (R S : α → Prop) :
    every_restricted (λ _ => True) R S = every_sem R S := by
  unfold every_restricted every_sem; simp

/-- ⟦some⟧_{λ_.True}(R)(S) = ⟦some⟧(R)(S). -/
theorem some_unrestricted {α : Type*}
    (R S : α → Prop) :
    some_restricted (λ _ => True) R S = some_sem R S := by
  unfold some_restricted some_sem; simp

/-- ⟦no⟧_{λ_.True}(R)(S) = ⟦no⟧(R)(S). -/
theorem no_unrestricted {α : Type*}
    (R S : α → Prop) :
    no_restricted (λ _ => True) R S = no_sem R S := by
  unfold no_restricted no_sem; simp

/-! ### Restrictor monotonicity -/

/-- Smaller domain makes ⟦every⟧ easier to satisfy (restrictor ↓MON).
    If C ⊆ C' and every_C'(R)(S), then every_C(R)(S): fewer entities
    to check means the universal is weaker. -/
theorem every_restricted_anti_mono {α : Type*} [Fintype α] [DecidableEq α]
    {C C' : DomainRestrictor α} {R S : α → Prop}
    (hCC' : ∀ x, C x → C' x)
    (h : every_restricted C' R S) :
    every_restricted C R S :=
  every_restrictor_down _ _ S
    (λ x hx => ⟨hCC' x hx.1, hx.2⟩)
    h

/-- Larger domain makes ⟦some⟧ easier to satisfy (restrictor ↑MON).
    Dual of `every_restricted_anti_mono`: more entities to check means
    more chances to find a witness. -/
theorem some_restricted_mono {α : Type*} [Fintype α] [DecidableEq α]
    {C C' : DomainRestrictor α} {R S : α → Prop}
    (hCC' : ∀ x, C x → C' x)
    (h : some_restricted C R S) :
    some_restricted C' R S :=
  some_restrictor_up _ _ S
    (λ x hx => ⟨hCC' x hx.1, hx.2⟩)
    h

/-- Smaller domain makes ⟦no⟧ easier to satisfy (restrictor ↓MON).
    Like ⟦every⟧, ⟦no⟧ is anti-monotone in the restrictor: fewer entities
    to check means fewer chances for a counterexample. -/
theorem no_restricted_anti_mono {α : Type*} [Fintype α] [DecidableEq α]
    {C C' : DomainRestrictor α} {R S : α → Prop}
    (hCC' : ∀ x, C x → C' x)
    (h : no_restricted C' R S) :
    no_restricted C R S :=
  no_restrictor_down _ _ S
    (λ x hx => ⟨hCC' x hx.1, hx.2⟩)
    h

/-! ### Conservativity connection -/

/-- Domain-restricted *every* is conservative: restricting the restrictor to `C ∩ R`
preserves the quantifier's meaning. -/
theorem every_restricted_conservative {α : Type*}
    (C : DomainRestrictor α) (R S : α → Prop) :
    every_restricted C R S ↔ every_restricted C R (λ x => R x ∧ S x) := by
  unfold every_restricted every_sem
  constructor
  · intro h x ⟨hC, hR⟩; exact ⟨hR, h x ⟨hC, hR⟩⟩
  · intro h x ⟨hC, hR⟩; exact (h x ⟨hC, hR⟩).2

/-- Spectator irrelevance for domain restriction: entities outside C ∩ R don't
    affect ⟦every⟧_C(R, S). If S and S' agree on all entities satisfying both
    C and R, the restricted quantifier gives the same result.
    This formalizes the intuition that domain restriction makes irrelevant
    entities invisible to the quantifier. -/
theorem every_restricted_spectator {α : Type*}
    {C : DomainRestrictor α} {R S S' : α → Prop}
    (h : ∀ x, C x → R x → (S x ↔ S' x)) :
    every_restricted C R S ↔ every_restricted C R S' := by
  unfold every_restricted every_sem
  constructor
  · intro h1 x ⟨hC, hR⟩; exact (h x hC hR).mp (h1 x ⟨hC, hR⟩)
  · intro h1 x ⟨hC, hR⟩; exact (h x hC hR).mpr (h1 x ⟨hC, hR⟩)

open Quantification (Conservative GQ) in
/-- Conservativity is preserved under domain restriction: if Q is conservative,
    then Q restricted by any domain predicate C is also conservative.
    Generalizes `every_restricted_conservative` from `every_sem` to any
    conservative GQ: [barwise-cooper-1981]'s conservativity universal guarantees that
    intersecting the restrictor with a contextual predicate preserves it. -/
theorem conservative_domain_restricted {E : Type*}
    {Q : GQ E} {C : DomainRestrictor E}
    (hQ : Conservative Q) :
    Conservative (λ R S => Q (λ x => C x ∧ R x) S) := by
  intro R S
  show Q (λ x => C x ∧ R x) S ↔ Q (λ x => C x ∧ R x) (λ x => R x ∧ S x)
  have h1 := hQ (λ x => C x ∧ R x) S
  have h2 := hQ (λ x => C x ∧ R x) (λ x => R x ∧ S x)
  have heq : (λ x => (C x ∧ R x) ∧ R x ∧ S x) = (λ x => (C x ∧ R x) ∧ S x) := by
    funext x; exact propext ⟨fun ⟨⟨hc, hr⟩, _, hs⟩ => ⟨⟨hc, hr⟩, hs⟩,
                             fun ⟨⟨hc, hr⟩, hs⟩ => ⟨⟨hc, hr⟩, hr, hs⟩⟩
  rw [h1, h2, heq]

end Quantification.DomainRestriction
