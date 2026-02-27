import Linglib.Theories.Semantics.Lexical.Determiner.Quantifier

/-!
# Quantifier Domain Restriction

@cite{ritchie-schiller-2024}

Ritchie, H. & Schiller, K. (2024). Default Domain Restriction Possibilities.
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

## Spatial Affordance Hierarchy

The cognitive heuristic account is grounded in ecological psychology's parsing
of space into nested regions. Cutting & Vishton (1995) distinguish three zones
(personal, action, vista); Previc (1998) proposes four (peripersonal, focal
extrapersonal, action extrapersonal, ambient extrapersonal). We adopt a hybrid
terminology with four levels:

    peripersonal ⊆ action ⊆ vista ⊆ unrestricted

Each region induces a predicate on entities, yielding a partially ordered set
of candidate domain restrictions. Pragmatic reasoning selects among them.

## Connection to Conservativity

Domain restriction via C-intersection is well-defined because all natural language
determiners are conservative (Barwise & Cooper 1981): Q(R, S) = Q(R, R ∩ S).
Combined with Extension (spectator irrelevance), restricting the domain to entities
satisfying C is equivalent to restricting the restrictor to C ∩ R.

## References

- von Fintel, K. (1994). Restrictions on Quantifier Domains. UMass dissertation.
- Stanley, J. & Szabó, Z.G. (2000). On quantifier domain restriction. M&L 15(3).
- Bach, K. (1994). Conversational impliciture. M&L 9(2).
- Previc, F.H. (1998). The neuropsychology of 3-D space. Psychological Bulletin 124(2).
- Cutting, J.E. & Vishton, P.M. (1995). Perceiving layout and knowing distances.
-/

set_option autoImplicit false

namespace Semantics.Lexical.Determiner.DomainRestriction

open Semantics.Montague (Model)
open Semantics.Lexical.Determiner.Quantifier

-- ============================================================================
-- §1. Domain-Restricted Quantifiers
-- ============================================================================

/-- A domain restrictor is a predicate selecting contextually relevant entities. -/
abbrev DomainRestrictor (E : Type*) := E → Bool

/-- Domain-restricted ⟦every⟧: ∀x. C(x) ∧ R(x) → S(x).
    Restricts the quantifier domain to entities satisfying C. -/
def every_restricted (m : Model) [FiniteModel m]
    (C : DomainRestrictor m.Entity) (R S : m.Entity → Bool) : Bool :=
  every_sem m (λ x => C x && R x) S

/-- Domain-restricted ⟦some⟧: ∃x. C(x) ∧ R(x) ∧ S(x). -/
def some_restricted (m : Model) [FiniteModel m]
    (C : DomainRestrictor m.Entity) (R S : m.Entity → Bool) : Bool :=
  some_sem m (λ x => C x && R x) S

/-- Domain-restricted ⟦no⟧: ¬∃x. C(x) ∧ R(x) ∧ S(x). -/
def no_restricted (m : Model) [FiniteModel m]
    (C : DomainRestrictor m.Entity) (R S : m.Entity → Bool) : Bool :=
  no_sem m (λ x => C x && R x) S

-- ============================================================================
-- §2. Key Properties
-- ============================================================================

/-- Unrestricted domain recovers the standard quantifier:
    ⟦every⟧_{λ_.true}(R)(S) = ⟦every⟧(R)(S). -/
theorem every_unrestricted {m : Model} [FiniteModel m]
    (R S : m.Entity → Bool) :
    every_restricted m (λ _ => true) R S = every_sem m R S := by
  unfold every_restricted every_sem
  simp [Bool.true_and]

/-- Smaller domain makes ⟦every⟧ easier to satisfy (restrictor ↓MON).
    If C ⊆ C' and every_C'(R)(S), then every_C(R)(S): fewer entities
    to check means the universal is weaker. -/
theorem every_restricted_anti_mono {m : Model} [FiniteModel m]
    {C C' : DomainRestrictor m.Entity} {R S : m.Entity → Bool}
    (hCC' : ∀ x, C x = true → C' x = true)
    (h : every_restricted m C' R S = true) :
    every_restricted m C R S = true :=
  every_restrictor_down _ _ S
    (λ x hx => by simp only [Bool.and_eq_true] at hx ⊢; exact ⟨hCC' x hx.1, hx.2⟩)
    h

/-- Larger domain makes ⟦some⟧ easier to satisfy (restrictor ↑MON).
    Dual of `every_restricted_anti_mono`: more entities to check means
    more chances to find a witness. -/
theorem some_restricted_mono {m : Model} [FiniteModel m]
    {C C' : DomainRestrictor m.Entity} {R S : m.Entity → Bool}
    (hCC' : ∀ x, C x = true → C' x = true)
    (h : some_restricted m C R S = true) :
    some_restricted m C' R S = true :=
  some_restrictor_up _ _ S
    (λ x hx => by simp only [Bool.and_eq_true] at hx ⊢; exact ⟨hCC' x hx.1, hx.2⟩)
    h

-- ============================================================================
-- §3. Default Domain Restriction Possibilities (DDRPs)
-- ============================================================================

/-- Spatial scales from ecological psychology (Cutting & Vishton 1995; Previc 1998).

    Cutting & Vishton (1995) distinguish three zones (personal, action, vista).
    Previc (1998) proposes four (peripersonal, focal extrapersonal, action
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
  deriving DecidableEq, BEq, Repr, Inhabited

instance : Fintype SpatialScale where
  elems := {.peripersonal, .action, .vista, .unrestricted}
  complete := λ x => by cases x <;> simp

/-- Default Domain Restriction Possibilities (DDRPs).

    Given a perceptual scene, affordance-based spatial cognition generates
    nested spatial regions that induce candidate domain restrictors.
    The nesting reflects physical containment: what is within reach is also
    within walking distance, which is also within view. -/
structure DDRP (E : Type*) where
  /-- Each spatial scale induces a predicate on entities. -/
  region : SpatialScale → DomainRestrictor E
  /-- Nesting: peripersonal ⊆ action. -/
  peri_sub_action : ∀ e, region .peripersonal e = true → region .action e = true
  /-- Nesting: action ⊆ vista. -/
  action_sub_vista : ∀ e, region .action e = true → region .vista e = true
  /-- Nesting: vista ⊆ unrestricted. -/
  vista_sub_unr : ∀ e, region .vista e = true → region .unrestricted e = true
  /-- Unrestricted contains everything. -/
  unr_total : ∀ e, region .unrestricted e = true

/-- The candidate domain restrictors: one per spatial scale.
    DDRPs constrain the candidate set to a small, structured menu —
    not the set of all possible predicates (contra pure pragmatic approaches). -/
def DDRP.candidates {E : Type*} (d : DDRP E) : List (DomainRestrictor E) :=
  [d.region .peripersonal, d.region .action, d.region .vista, d.region .unrestricted]

-- ============================================================================
-- §4. DDRP Nesting for Domain-Restricted ⟦every⟧
-- ============================================================================

/-- If ⟦every⟧ is true under action restriction, it's true under peripersonal.
    A universal over a superset entails the same universal over any subset. -/
theorem DDRP.action_implies_peri {m : Model} [FiniteModel m]
    (d : DDRP m.Entity) (R S : m.Entity → Bool) :
    every_restricted m (d.region .action) R S = true →
    every_restricted m (d.region .peripersonal) R S = true :=
  λ h => every_restricted_anti_mono d.peri_sub_action h

/-- If ⟦every⟧ is true under vista restriction, it's true under action. -/
theorem DDRP.vista_implies_action {m : Model} [FiniteModel m]
    (d : DDRP m.Entity) (R S : m.Entity → Bool) :
    every_restricted m (d.region .vista) R S = true →
    every_restricted m (d.region .action) R S = true :=
  λ h => every_restricted_anti_mono d.action_sub_vista h

/-- If ⟦every⟧ is true unrestricted, it's true under vista. -/
theorem DDRP.unr_implies_vista {m : Model} [FiniteModel m]
    (d : DDRP m.Entity) (R S : m.Entity → Bool) :
    every_restricted m (d.region .unrestricted) R S = true →
    every_restricted m (d.region .vista) R S = true :=
  λ h => every_restricted_anti_mono d.vista_sub_unr h

end Semantics.Lexical.Determiner.DomainRestriction
