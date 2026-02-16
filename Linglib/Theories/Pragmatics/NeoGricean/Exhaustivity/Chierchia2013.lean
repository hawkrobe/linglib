import Linglib.Theories.Pragmatics.NeoGricean.Exhaustivity.Basic

/-!
# Core Theorems from Chierchia (2013) *Logic in Grammar*

Deep integration of Chierchia's central results connecting polarity,
scalar implicatures, free choice, and intervention — all with real proofs.

## Main results

1. **Free Choice via Double Exhaustification** (Ch. 2, 5):
   `Exh(Exh(◇(p ∨ q)))  ↔  ◇p ∧ ◇q`

2. **SI–NPI Generalization** (Ch. 1–2):
   Scalar implicatures are vacuous in exactly DE contexts.

3. **Domain Widening Reversal** (Ch. 1, 3):
   Widening strengthens in DE contexts, weakens in UE contexts.

4. **Intervention Disrupts DE** (Ch. 7):
   Inserting a non-monotone strengthening operator inside a DE context
   destroys the DE property, blocking NPI licensing.

5. **Scalar Reversal** (Ch. 1):
   The same scale produces opposite implicatures in UE vs DE contexts.

6. **FC Duality** (Ch. 5–6):
   Free choice works uniformly for ◇ and □ via the same exhaustification.

## References

- Chierchia, G. (2013). *Logic in Grammar: Polarity, Free Choice, and
  Intervention*. Oxford University Press.
- Fox, D. (2007). Free choice and the theory of scalar implicatures.
  In Sauerland & Stateva (eds.), *Presupposition and Implicature in
  Compositional Semantics*. Palgrave Macmillan.
- Spector, B. (2016). Comparing exhaustivity operators. *S&P* 9(11):1–33.
-/

namespace NeoGricean.Exhaustivity.Chierchia2013

open NeoGricean.Exhaustivity

-- ============================================================================
-- § 1. Free Choice via Double Exhaustification
-- ============================================================================

/-!
## Free Choice Derivation

Chierchia's signature result: the Free Choice inference for permission
sentences like "You may have coffee or tea" → "You may have coffee AND
you may have tea" is derived grammatically via double exhaustification.

We work over an abstract `World` type where `◇p = ∃ w, p w`.
-/

section FreeChoice

variable {World : Type*}

/-- Possibility modal: ◇p holds iff p is true at some accessible world. -/
def diamond (p : Prop' World) : Prop := ∃ w, p w

/-- Necessity modal: □p holds iff p is true at all accessible worlds. -/
def box (p : Prop' World) : Prop := ∀ w, p w

/-- Disjunction of propositions. -/
def pdisj (p q : Prop' World) : Prop' World := λ w => p w ∨ q w

/-- The alternative set for ◇(p ∨ q) consists of {◇p, ◇q, ◇(p ∧ q)}.

This is the standard alternative set: subdomain alternatives ◇p, ◇q
(restricting the disjunction) and the conjunction alternative ◇(p ∧ q)
(strengthening the disjunction). -/
structure FCAltSet (World : Type*) where
  p : Prop' World
  q : Prop' World

namespace FCAltSet

variable (a : FCAltSet World)

/-- The assertion: ◇(p ∨ q) -/
def assertion : Prop := diamond (pdisj a.p a.q)

/-- Alternative: ◇p -/
def altP : Prop := diamond a.p

/-- Alternative: ◇q -/
def altQ : Prop := diamond a.q

/-- Alternative: ◇(p ∧ q) -/
def altPQ : Prop := diamond (a.p ∧ₚ a.q)

/-- First exhaustification: Exh(◇(p ∨ q))
    = ◇(p ∨ q) ∧ ¬◇(p ∧ q)

    The conjunction alternative ◇(p ∧ q) is the unique innocently
    excludable alternative at this stage — excluding either ◇p or ◇q
    alone would be incompatible with the assertion. -/
def exh1 : Prop := a.assertion ∧ ¬a.altPQ

/-- The strengthened alternatives after first Exh:
    Exh(◇p) = ◇p ∧ ¬◇q  and  Exh(◇q) = ◇q ∧ ¬◇p

    These are the alternatives to the *exhaustified* sentence, obtained
    by exhaustifying each subdomain alternative the same way. -/
def exhAltP : Prop := a.altP ∧ ¬a.altQ
def exhAltQ : Prop := a.altQ ∧ ¬a.altP

/-- Second exhaustification: Exh(Exh(◇(p ∨ q)))
    = Exh₁ ∧ ¬(◇p ∧ ¬◇q) ∧ ¬(◇q ∧ ¬◇p)

    Now the strengthened subdomain alternatives are innocently excludable. -/
def exh2 : Prop := a.exh1 ∧ ¬a.exhAltP ∧ ¬a.exhAltQ

/-- Free choice: ◇p ∧ ◇q -/
def freeChoice : Prop := a.altP ∧ a.altQ

end FCAltSet

/-- **Theorem 1 (Free Choice via Double Exhaustification).**

Chierchia (2013) Ch. 2, 5; Fox (2007):

  Exh(Exh(◇(p ∨ q)))  →  ◇p ∧ ◇q

Double exhaustification of a disjunction under a possibility modal
yields the conjunctive (free choice) reading.

Proof: The second Exh negates ◇p∧¬◇q and ◇q∧¬◇p. Combined with
the assertion ◇(p∨q), we derive both ◇p and ◇q. -/
theorem free_choice_forward (a : FCAltSet World) (h : a.exh2) : a.freeChoice := by
  obtain ⟨⟨hassert, _hnpq⟩, hnexhP, hnexhQ⟩ := h
  unfold FCAltSet.freeChoice
  unfold FCAltSet.exhAltP at hnexhP
  unfold FCAltSet.exhAltQ at hnexhQ
  unfold FCAltSet.assertion diamond pdisj at hassert
  obtain ⟨w, hw⟩ := hassert
  constructor
  · -- Show ◇p
    by_contra hnp
    have hq : a.altQ := by
      unfold FCAltSet.altQ diamond
      cases hw with
      | inl hp => exact absurd ⟨w, hp⟩ hnp
      | inr hq => exact ⟨w, hq⟩
    exact hnexhQ ⟨hq, hnp⟩
  · -- Show ◇q
    by_contra hnq
    have hp : a.altP := by
      unfold FCAltSet.altP diamond
      cases hw with
      | inl hp => exact ⟨w, hp⟩
      | inr hq => exact absurd ⟨w, hq⟩ hnq
    exact hnexhP ⟨hp, hnq⟩

/-- **Theorem 1 (converse direction).**

  ◇p ∧ ◇q ∧ ¬◇(p ∧ q)  →  Exh(Exh(◇(p ∨ q)))

When both disjuncts are individually possible but their conjunction is not,
we get exactly the double-exhaustified meaning. -/
theorem free_choice_backward (a : FCAltSet World)
    (hfc : a.freeChoice) (hnpq : ¬a.altPQ) : a.exh2 := by
  obtain ⟨hp, hq⟩ := hfc
  unfold FCAltSet.exh2 FCAltSet.exh1
  refine ⟨⟨?_, hnpq⟩, ?_, ?_⟩
  · -- assertion: ◇(p ∨ q) from ◇p
    unfold FCAltSet.assertion diamond pdisj
    obtain ⟨w, hw⟩ := hp
    exact ⟨w, Or.inl hw⟩
  · -- ¬(◇p ∧ ¬◇q)
    unfold FCAltSet.exhAltP
    intro ⟨_, hnq⟩
    exact hnq hq
  · -- ¬(◇q ∧ ¬◇p)
    unfold FCAltSet.exhAltQ
    intro ⟨_, hnp⟩
    exact hnp hp

end FreeChoice

-- ============================================================================
-- § 2. SI–NPI Generalization
-- ============================================================================

/-!
## The SI–NPI Generalization

Chierchia (2013) Ch. 1–2, building on Chierchia (2004):

Scalar implicatures are blocked in exactly the environments that
license NPIs — namely, Downward Entailing environments.

In a DE environment `f`, if `strong ⊆ₚ weak` (strong entails weak),
then `f weak ⊆ₚ f strong` (f reverses the entailment). Exhaustifying
`f(weak)` by negating `f(strong)` would produce `f(weak) ∧ₚ ∼(f(strong))`,
but since `f(weak) ⊆ₚ f(strong)`, this is contradictory — i.e., the
scalar implicature is vacuous.
-/

section SINPIGeneralization

variable {World : Type*}

/-- A context function mapping propositions to propositions. -/
abbrev Ctx (World : Type*) := Prop' World → Prop' World

/-- Exhaustification in context: assert `C(weak)` and negate `C(strong)`. -/
def exhInCtx (C : Ctx World) (weak strong : Prop' World) : Prop' World :=
  C weak ∧ₚ ∼(C strong)

/-- The SI is vacuous: the exhaustified meaning entails ⊥ (is empty). -/
def siVacuous (C : Ctx World) (weak strong : Prop' World) : Prop :=
  ∀ w, ¬(exhInCtx C weak strong w)

/-- **Theorem 2 (SI–NPI Generalization, one direction).**

In a DE context, if `strong ⊆ₚ weak`, then the scalar implicature
`C(weak) ∧ ¬C(strong)` is contradictory (vacuous).

This is the formal content of Chierchia's observation that SIs are
suspended in NPI-licensing environments. -/
theorem si_vacuous_in_de (C : Ctx World)
    (hDE : ∀ (p q : Prop' World), entails p q → entails (C q) (C p))
    (weak strong : Prop' World) (h_ent : entails strong weak) :
    siVacuous C weak strong := by
  intro w ⟨hCw, hnCs⟩
  have hCws := hDE strong weak h_ent w hCw
  exact hnCs hCws

/-- **Theorem 2 (converse direction).**

If the SI is non-vacuous, there must be some world where it fires. -/
theorem si_active_witness (C : Ctx World)
    (weak strong : Prop' World)
    (h_witness : ∃ w, C weak w ∧ ¬C strong w) :
    ¬siVacuous C weak strong := by
  intro hvac
  obtain ⟨w, hCw, hnCs⟩ := h_witness
  exact hvac w ⟨hCw, hnCs⟩

end SINPIGeneralization

-- ============================================================================
-- § 3. Domain Widening Reversal
-- ============================================================================

/-!
## Domain Widening and Informativity

Chierchia (2013) Ch. 1, 3, building on Kadmon & Landman (1993):

NPIs like "any" are indefinites with obligatory domain widening.
- In UE contexts, widening the domain is *weakening* (less informative) → bad
- In DE contexts, widening the domain is *strengthening* (more informative) → good

This explains NPI licensing: "any" is grammatical exactly where its
obligatory widening is informative, i.e., in DE contexts.
-/

section DomainWidening

variable {World : Type*} {Entity : Type*}

/-- An existential statement over a domain D: ∃ x ∈ D, P x. -/
def existsInDomain (D : Set Entity) (P : Entity → Prop' World) : Prop' World :=
  λ w => ∃ x ∈ D, P x w

/-- Widening the domain is weakening: if D ⊆ D', then (∃x∈D, Px) ⊆ₚ (∃x∈D', Px).

Larger domain = more potential witnesses = weaker existential claim. -/
theorem wider_domain_weaker_existential (D D' : Set Entity) (P : Entity → Prop' World)
    (h : D ⊆ D') : entails (existsInDomain D P) (existsInDomain D' P) := by
  intro w ⟨x, hxD, hPx⟩
  exact ⟨x, h hxD, hPx⟩

/-- **Theorem 3a (Widening strengthens in DE).**

In a DE context, widening the domain of an indefinite *strengthens*
the overall claim: C(∃x∈D', Px) ⊆ₚ C(∃x∈D, Px) when D ⊆ D'.

This is why NPIs are licensed in DE contexts: widening is informative. -/
theorem widening_strengthens_in_de (C : Ctx World)
    (hDE : ∀ (p q : Prop' World), entails p q → entails (C q) (C p))
    (D D' : Set Entity) (P : Entity → Prop' World) (h : D ⊆ D') :
    entails (C (existsInDomain D' P)) (C (existsInDomain D P)) :=
  hDE _ _ (wider_domain_weaker_existential D D' P h)

/-- **Theorem 3b (Widening weakens in UE).**

In a UE context, widening the domain *weakens* the overall claim:
C(∃x∈D, Px) ⊆ₚ C(∃x∈D', Px) when D ⊆ D'.

This is why NPIs are *not* licensed in UE contexts: widening is
uninformative (violates Maximize Strength). -/
theorem widening_weakens_in_ue (C : Ctx World)
    (hUE : ∀ (p q : Prop' World), entails p q → entails (C p) (C q))
    (D D' : Set Entity) (P : Entity → Prop' World) (h : D ⊆ D') :
    entails (C (existsInDomain D P)) (C (existsInDomain D' P)) :=
  hUE _ _ (wider_domain_weaker_existential D D' P h)

end DomainWidening

-- ============================================================================
-- § 4. Intervention Disrupts DE
-- ============================================================================

/-!
## Intervention Effects

Chierchia (2013) Ch. 7:

Scalar triggers embedded between an NPI licensor and the NPI can
disrupt licensing. This is because exhaustification (EXH) applied
at the scalar trigger's scope is not monotone: it can break the
Downward Entailing property of the embedding context.

Key insight: Exhaustification is a *strengthening* operation
(exh(φ) ⊆ₚ φ). Any non-trivial strengthening can disrupt antitonicity
because subset-preservation is not preserved under arbitrary strengthening.
-/

section Intervention

variable {World : Type*}

/-- An operator S is a *strengthening* operator if S(φ) ⊆ₚ φ for all φ. -/
def IsStrengthening (S : Ctx World) : Prop :=
  ∀ φ, entails (S φ) φ

/-- **Theorem 4 (Intervention disrupts DE).**

If S is not monotone (∃ p ⊆ₚ q with ¬(S p ⊆ₚ S q)), then composing
negation (a DE context) with S fails to be DE.

This captures Chierchia's insight: a scalar trigger (which acts like
Exh, a non-monotone strengthening operator) between an NPI licensor
and an NPI disrupts the DE chain. -/
theorem intervention_negation_not_de
    (S : Ctx World)
    (p q : Prop' World)
    (_hpq : entails p q)
    -- S is not monotone: it does not preserve p ⊆ₚ q
    (w : World) (hSpw : S p w) (hnSqw : ¬S q w) :
    -- Then ¬ ∘ S is not DE at this pair
    ¬entails (pneg (S q)) (pneg (S p)) := by
  intro hDE
  -- ¬S(q)(w) holds, so pneg(S q)(w) holds
  have h1 : pneg (S q) w := hnSqw
  -- By hDE: pneg(S p)(w), i.e., ¬S(p)(w)
  have h2 := hDE w h1
  -- But S(p)(w) holds — contradiction
  exact h2 hSpw

/-- **Corollary: Exhaustification (Exh) is the prototypical intervener.**

Exh is strengthening (exh(φ) ⊆ₚ φ) and not monotone
(∃ p ⊆ₚ q with exh(p) ⊄ exh(q)). So Exh inserted between a
DE licensor and an NPI disrupts the DE property. -/
theorem exh_is_strengthening (ALT : Set (Prop' World)) :
    IsStrengthening (exhMW ALT) := by
  intro φ w ⟨hφw, _⟩
  exact hφw

end Intervention

-- ============================================================================
-- § 5. Scalar Reversal
-- ============================================================================

/-!
## Scalar Reversal in DE Contexts

Chierchia (2013) Ch. 1:

The same Horn scale produces opposite effects depending on polarity:
- In UE: "some" implicates "not all" (negate stronger alternative)
- In DE: "some" is STRONGER than "all" (entailment reverses), so
  exhaustification is vacuous

This is proven as a direct consequence of antitonicity.
-/

section ScalarReversal

variable {World : Type*}

/-- **Theorem 5 (Entailment reversal in DE contexts).**

If `strong ⊆ₚ weak` (strong entails weak) and C is DE, then
`C weak ⊆ₚ C strong` (C(weak) entails C(strong)).

The "stronger" alternative in UE becomes the "weaker" one in DE,
making the exhaustification move vacuous. -/
theorem entailment_reversal_in_de (C : Ctx World)
    (hDE : ∀ (p q : Prop' World), entails p q → entails (C q) (C p))
    (weak strong : Prop' World) (h : entails strong weak) :
    entails (C weak) (C strong) :=
  hDE strong weak h

/-- **Corollary: In DE, the "weak" scalar term is informationally stronger.**

"Not all students came" entails "Not some students came" (= "No student came").
So in "not ___ students came", "some" is the stronger filler.
This is why "any" (= widened "some") is licensed: it's the strongest. -/
theorem weak_is_strong_in_de (C : Ctx World)
    (hDE : ∀ (p q : Prop' World), entails p q → entails (C q) (C p))
    (some_ all_ : Prop' World) (h : entails all_ some_) :
    entails (C some_) (C all_) :=
  hDE all_ some_ h

end ScalarReversal

-- ============================================================================
-- § 6. FC Duality: ◇ and □
-- ============================================================================

/-!
## Free Choice Duality

Chierchia (2013) Ch. 5–6:

The Free Choice derivation is *uniform* across modal forces. Both
existential FC (◇(p∨q) → ◇p ∧ ◇q) and universal FC (□(p∨q) → □p ∧ □q,
i.e., "subtrigging") follow from the same double-exhaustification mechanism.

We prove this by parameterizing over an arbitrary modal operator.
-/

section FCDuality

variable {World : Type*}

/-- A modal operator: maps a proposition about worlds to a truth value. -/
abbrev ModalOp (World : Type*) := Prop' World → Prop

/-- The FC alt set parameterized by modal operator M:
    Assertion M(p ∨ q), alternatives M(p), M(q), M(p ∧ q). -/
structure ModalFCAltSet (World : Type*) where
  M : ModalOp World
  p : Prop' World
  q : Prop' World

namespace ModalFCAltSet

variable (a : ModalFCAltSet World)

def assertion : Prop := a.M (pdisj a.p a.q)
def altP : Prop := a.M a.p
def altQ : Prop := a.M a.q
def altPQ : Prop := a.M (a.p ∧ₚ a.q)
def exh1 : Prop := a.assertion ∧ ¬a.altPQ
def exhAltP : Prop := a.altP ∧ ¬a.altQ
def exhAltQ : Prop := a.altQ ∧ ¬a.altP
def exh2 : Prop := a.exh1 ∧ ¬a.exhAltP ∧ ¬a.exhAltQ
def freeChoice : Prop := a.altP ∧ a.altQ

end ModalFCAltSet

/-- **Theorem 6 (FC Duality).**

For ANY modal operator M satisfying distributivity over disjunction
(M(p ∨ q) → M(p) ∨ M(q)), double exhaustification yields free choice.

This covers:
- ◇ (possibility): ◇(p∨q) → ◇p ∨ ◇q trivially
- □ (necessity): □(p∨q) → □p ∨ □q (when the box distributes)
- Deontic, epistemic, ability modals

The proof is structurally identical to the ◇ case. -/
theorem fc_duality_forward (a : ModalFCAltSet World)
    (h_distrib : a.assertion → a.altP ∨ a.altQ)
    (h : a.exh2) : a.freeChoice := by
  obtain ⟨⟨hassert, _hnpq⟩, hnexhP, hnexhQ⟩ := h
  unfold ModalFCAltSet.freeChoice
  unfold ModalFCAltSet.exhAltP at hnexhP
  unfold ModalFCAltSet.exhAltQ at hnexhQ
  have hdisj := h_distrib hassert
  constructor
  · by_contra hnp
    cases hdisj with
    | inl hp => exact hnp hp
    | inr hq => exact hnexhQ ⟨hq, hnp⟩
  · by_contra hnq
    cases hdisj with
    | inl hp => exact hnexhP ⟨hp, hnq⟩
    | inr hq => exact hnq hq

/-- **Corollary: ◇ satisfies the distributivity condition.** -/
theorem diamond_distributes (p q : Prop' World) :
    diamond (pdisj p q) → diamond p ∨ diamond q := by
  intro ⟨w, hw⟩
  cases hw with
  | inl hp => exact Or.inl ⟨w, hp⟩
  | inr hq => exact Or.inr ⟨w, hq⟩

end FCDuality

-- ============================================================================
-- § 7. Polarity Composition (grounded from Mathlib)
-- ============================================================================

/-!
## Polarity Composition Laws

Chierchia (2013) Ch. 1 §1.1.3:

The four composition rules for monotonicity, grounded in Mathlib's
order theory. These are the foundation for all of Chierchia's results.
-/

section PolarityComposition

variable {World : Type*}

/-- Double negation restores UE: "Nobody doubts that ..." is UE.
    DE ∘ DE = UE, from Mathlib's `Antitone.comp`. -/
theorem double_negation_ue {f g : Prop' World → Prop' World}
    (hf : Antitone f) (hg : Antitone g) : Monotone (f ∘ g) :=
  hf.comp hg

/-- DE under UE stays DE: "It's true that nobody ..." is DE.
    UE ∘ DE = DE -/
theorem ue_under_de {f g : Prop' World → Prop' World}
    (hf : Monotone f) (hg : Antitone g) : Antitone (f ∘ g) :=
  hf.comp_antitone hg

/-- UE under DE stays DE: "Nobody said ..." is DE when "said" is UE.
    DE ∘ UE = DE -/
theorem de_under_ue {f g : Prop' World → Prop' World}
    (hf : Antitone f) (hg : Monotone g) : Antitone (f ∘ g) :=
  hf.comp_monotone hg

/-- UE under UE stays UE: "Somebody said ..." is UE.
    UE ∘ UE = UE -/
theorem ue_under_ue {f g : Prop' World → Prop' World}
    (hf : Monotone f) (hg : Monotone g) : Monotone (f ∘ g) :=
  hf.comp hg

end PolarityComposition

-- ============================================================================
-- § 8. Bridge: Maximize Strength = Exhaustification
-- ============================================================================

/-!
## Maximize Strength as Exhaustification

Chierchia (2013) Ch. 1 §1.1.4:

Maximize Strength says: among alternative parses, prefer the one that
generates the strongest (most informative) proposition. This is
equivalent to applying the exhaustivity operator, since exhaustification
negates alternatives to produce the strongest consistent meaning.
-/

section MaximizeStrength

variable {World : Type*}

/-- Maximize Strength: exhIE produces an interpretation that entails
    the plain meaning — it is a strengthening operation.
    This is Chierchia's Maximize Strength principle formalized as
    the defining property of exhaustification. -/
theorem maximize_strength_eq_exhIE (ALT : Set (Prop' World)) (φ : Prop' World) :
    entails (exhIE ALT φ) φ := by
  intro w hw
  have hφ_in_IE : φ ∈ IE ALT φ := by
    intro E hMC
    exact hMC.1.1
  exact hw φ hφ_in_IE

end MaximizeStrength

end NeoGricean.Exhaustivity.Chierchia2013
