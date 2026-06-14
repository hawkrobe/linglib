import Linglib.Semantics.Quantification.Quantifier
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.Fin.Basic

/-!
# Quantifier Domain Restriction

[ritchie-schiller-2024] [cutting-vishton-1995] [previc-1998] [stanley-szab-2000] [von-fintel-1994] [barwise-cooper-1981]

[ritchie-schiller-2024]: Default Domain Restriction Possibilities.
*Semantics & Pragmatics* 17, Article 13: 1–49.

## Core Idea

Quantifier domains are restricted by a contextual predicate C that intersects
the restrictor: ⟦every⟧_C(R)(S) = ∀x. C(x) ∧ R(x) → S(x). Ritchie & Schiller
argue that existing accounts of domain restriction — rational pragmatic (§2.1),
discourse-structural (§2.2), and intentionalist (§2.3) — fail to explain *why*
certain restrictions are defaults. Their proposal (§3): cognitive heuristics
(perceptual availability, salience, manipulability) generate a structured set
of **default domain restriction possibilities** (DDRPs) that pragmatic reasoning
then selects among.

## Nested Spatial Regions

The cognitive heuristic account is grounded in ecological psychology's parsing
of space into nested regions. [cutting-vishton-1995] distinguish three zones
(personal, action, vista); [previc-1998] proposes four (peripersonal, focal
extrapersonal, action extrapersonal, ambient extrapersonal). We adopt a hybrid
terminology with four levels:

    peripersonal ⊆ action ⊆ vista ⊆ unrestricted

Each region induces a predicate on entities, yielding a partially ordered set
of candidate domain restrictions. Pragmatic reasoning selects among them.

## Connection to Conservativity

Domain restriction via C-intersection is well-defined because all natural language
determiners are conservative: Q(R, S) = Q(R, R ∩ S).
Combined with Extension (spectator irrelevance), restricting the domain to entities
satisfying C is equivalent to restricting the restrictor to C ∩ R.

-/

set_option autoImplicit false

namespace Quantification.DomainRestriction

open Quantification.Quantifier

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

/-- Domain-restricted ⟦every⟧ is conservative:
    ⟦every⟧_C(R, S) ↔ ⟦every⟧_C(R, R ∧ S).
    Domain restriction preserves the fundamental GQ property. This is the formal justification for the `every_restricted` definition:
    conservativity guarantees that restricting the restrictor to C ∩ R preserves
    the quantifier's meaning. -/
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
    conservative GQ. This is the formal justification for the DDRP
    infrastructure: [barwise-cooper-1981]'s conservativity universal
    guarantees that C-intersection preserves the fundamental GQ property. -/
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

/-! ### Spatial scale and DDRP -/

/-- Spatial scales from ecological psychology.

    [cutting-vishton-1995] distinguish three zones (personal, action, vista).
    [previc-1998] proposes four (peripersonal, focal extrapersonal, action
    extrapersonal, ambient extrapersonal). We adopt a hybrid:
    - **Peripersonal**: Within arm's reach (~2m). Direct manipulation.
    - **Action**: Accessible by locomotion (~30m).
    - **Vista**: Visible panorama. Perception without action affordances.
    - **Unrestricted**: The entire universe (degenerate case, no spatial constraint). -/
inductive SpatialScale where
  | peripersonal
  | action
  | vista
  | unrestricted
  deriving DecidableEq, Repr, Inhabited

instance : Fintype SpatialScale where
  elems := {.peripersonal, .action, .vista, .unrestricted}
  complete := λ x => by cases x <;> simp

/-- Rank embedding for the linear order on SpatialScale. -/
def SpatialScale.toFin : SpatialScale → Fin 4
  | .peripersonal => 0
  | .action => 1
  | .vista => 2
  | .unrestricted => 3

private theorem SpatialScale.toFin_injective : Function.Injective SpatialScale.toFin := by
  intro a b h; cases a <;> cases b <;> simp_all [toFin]

/-- peripersonal < action < vista < unrestricted. -/
instance : LinearOrder SpatialScale :=
  LinearOrder.lift' SpatialScale.toFin SpatialScale.toFin_injective

instance : OrderTop SpatialScale where
  top := .unrestricted
  le_top a := by cases a <;> decide

instance : OrderBot SpatialScale where
  bot := .peripersonal
  bot_le a := by cases a <;> decide

/-- Default Domain Restriction Possibilities (DDRPs) — a monotone family of
    candidate domain restrictors indexed by an ordered scale, with the top of
    the scale unrestricted.

    Given a perceptual scene, cognitive heuristics generate nested spatial
    regions that induce candidate domain restrictors. The nesting reflects
    physical containment: what is within reach is also within walking
    distance, which is also within view.

    Parameterized by a scale type `S` with a preorder and top element,
    enabling reuse for non-spatial heuristics. `SpatialScale` is the
    canonical instantiation; the same nesting structure is instantiated by
    ASL signing height (`HeightDDRP`, [davidson-gagne-2022]) and comparison
    class inference ([tessler-goodman-2022]). -/
structure DDRP (S E : Type*) [Preorder S] [OrderTop S] where
  /-- Each scale level induces a candidate restrictor on the domain. -/
  region : S → Set E
  /-- Nesting: smaller scale ⊆ larger scale. -/
  monotone : Monotone region
  /-- The top scale is unrestricted. -/
  top_total : region ⊤ = Set.univ

/-- The candidate domain restrictors: one per scale level.
    DDRPs constrain the candidate set to a small, structured menu —
    not the set of all possible predicates (contra pure pragmatic approaches). -/
noncomputable def DDRP.candidates {S E : Type*} [Preorder S] [OrderTop S] [Fintype S]
    (d : DDRP S E) : List (S × DomainRestrictor E) :=
  (Fintype.elems (α := S)).val.toList.map (λ s => (s, d.region s))

/-! ### DDRP nesting theorems -/

/-- General ⟦every⟧ nesting: truth under a larger scale entails truth under
    any smaller scale. Subsumes all specific nesting theorems for ⟦every⟧.
    Follows from restrictor ↓MON of ⟦every⟧ + DDRP monotonicity. -/
theorem DDRP.every_nesting {S : Type*} [Preorder S] [OrderTop S]
    {α : Type*} [Fintype α] [DecidableEq α]
    (d : DDRP S α) (R Sc : α → Prop)
    {s₁ s₂ : S} (h : s₁ ≤ s₂) :
    every_restricted (d.region s₂) R Sc →
    every_restricted (d.region s₁) R Sc :=
  λ hev => every_restricted_anti_mono (λ _ hx => d.monotone h hx) hev

/-- General ⟦some⟧ nesting (reversed direction): truth under a smaller scale
    entails truth under any larger scale. Dual of `every_nesting`.
    Follows from restrictor ↑MON of ⟦some⟧ + DDRP monotonicity. -/
theorem DDRP.some_nesting {S : Type*} [Preorder S] [OrderTop S]
    {α : Type*} [Fintype α] [DecidableEq α]
    (d : DDRP S α) (R Sc : α → Prop)
    {s₁ s₂ : S} (h : s₁ ≤ s₂) :
    some_restricted (d.region s₁) R Sc →
    some_restricted (d.region s₂) R Sc :=
  λ hso => some_restricted_mono (λ _ hx => d.monotone h hx) hso

/-- General ⟦no⟧ nesting: truth under a larger scale entails truth under
    any smaller scale. Same direction as ⟦every⟧ (both are restrictor ↓MON).
    Follows from restrictor ↓MON of ⟦no⟧ + DDRP monotonicity. -/
theorem DDRP.no_nesting {S : Type*} [Preorder S] [OrderTop S]
    {α : Type*} [Fintype α] [DecidableEq α]
    (d : DDRP S α) (R Sc : α → Prop)
    {s₁ s₂ : S} (h : s₁ ≤ s₂) :
    no_restricted (d.region s₂) R Sc →
    no_restricted (d.region s₁) R Sc :=
  λ hno => no_restricted_anti_mono (λ _ hx => d.monotone h hx) hno

end Quantification.DomainRestriction
