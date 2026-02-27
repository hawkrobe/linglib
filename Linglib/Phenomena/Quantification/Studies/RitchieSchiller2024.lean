import Linglib.Theories.Semantics.Lexical.Determiner.DomainRestriction
import Linglib.Theories.Pragmatics.RSA.Core.Config

/-!
# Ritchie & Schiller (2024) — Default Domain Restriction Possibilities

@cite{ritchie-schiller-2024}

Ritchie, H. & Schiller, K. (2024). Default Domain Restriction Possibilities.
*Semantics & Pragmatics* 17, Article 13: 1–49.

## The Argument

When a speaker says "Every bottle is empty" at a dinner party, the hearer
restricts the quantifier domain to contextually relevant bottles — not all bottles
in the universe (R&S §1, ex. 3). Ritchie & Schiller argue that existing accounts
fail to explain *why* certain restrictions are defaults:
- **Rational pragmatic** (§2.1): RSA/Gricean reasoning doesn't explain default status
- **Discourse-structural** (§2.2): QUD-based accounts are too demanding
- **Intentionalist** (§2.3): speaker-intention accounts are too unconstrained

Their positive proposal (§3): cognitive heuristics — perceptual availability,
salience, and manipulability — generate a structured set of default domain
restriction possibilities (DDRPs). These are grounded in spatial cognition
(Cutting & Vishton 1995; Previc 1998), where nested spatial regions provide
a natural ordering on candidate restrictions.

## Scenario

We construct an illustrative scenario (not from the paper) with 4 entities at
increasing spatial distances and 3 world states, then verify key formal
consequences of the DDRP framework for both ⟦every⟧ (↓MON) and ⟦some⟧ (↑MON).

## Compositional Grounding

Truth conditions derive from `every_restricted` / `some_restricted`
(DomainRestriction.lean), which wrap `every_sem` / `some_sem` (Quantifier.lean)
with a domain restrictor predicate. Nesting theorems derive from
`DDRP.every_nesting` / `DDRP.some_nesting`, connecting the nested spatial
regions to restrictor monotonicity.

## RSA Connection

While R&S argue *against* RSA as explaining default status (§2.1), DDRPs are
compatible with RSA as the *selection mechanism*: the listener reasons over
candidate DDRPs (= `Latent` in RSAConfig) to infer which domain restriction
the speaker intended. We demonstrate this connection in §7.
-/

set_option autoImplicit false

namespace Phenomena.Quantification.Studies.RitchieSchiller2024

open Semantics.Montague (Model)
open Semantics.Lexical.Determiner.Quantifier (every_sem some_sem FiniteModel)
open Semantics.Lexical.Determiner.DomainRestriction

-- ============================================================================
-- §1. Domain Types
-- ============================================================================

/-- Entities in the constructed scene: 4 bottles at increasing spatial distances. -/
inductive Entity where
  | b1  -- bottle on table (peripersonal)
  | b2  -- bottle on table (peripersonal)
  | b3  -- bottle across room (action space)
  | b4  -- bottle outside window (vista)
  deriving DecidableEq, BEq, Repr, Inhabited

def bottleModel : Model := { Entity := Entity, decEq := inferInstance }

instance : FiniteModel bottleModel where
  elements := [.b1, .b2, .b3, .b4]
  complete := λ x => by cases x <;> simp
  nodup := by simp [List.nodup_cons, List.mem_cons]

-- ============================================================================
-- §2. Spatial Scene & DDRPs
-- ============================================================================

/-- Peripersonal space: entities within arm's reach (b1, b2 on the table). -/
def near : Entity → Bool
  | .b1 | .b2 => true
  | _ => false

/-- Action space: entities accessible by locomotion (b1, b2, b3). -/
def mid : Entity → Bool
  | .b4 => false
  | _ => true

/-- DDRP for the bottle scenario.
    Near ⊆ mid ⊆ vista (= unrestricted in this indoor scene). -/
def sceneDDRP : DDRP SpatialScale Entity where
  region
    | .peripersonal => near
    | .action => mid
    | .vista => λ _ => true
    | .unrestricted => λ _ => true
  monotone {s₁ s₂} h e hr := by
    cases s₁ <;> cases s₂ <;> (first | exact hr | trivial | (cases e <;> simp_all [near, mid]))
  top_total _ := rfl

-- ============================================================================
-- §3. World States
-- ============================================================================

/-- World states: which bottles are empty.
    - `nearEmpty`: only proximal bottles (b1, b2) are empty
    - `midEmpty`: proximal + action-space bottles (b1, b2, b3) are empty
    - `allEmpty`: all bottles are empty -/
inductive World where
  | nearEmpty
  | midEmpty
  | allEmpty
  deriving DecidableEq, BEq, Repr, Inhabited

instance : Fintype World where
  elems := {.nearEmpty, .midEmpty, .allEmpty}
  complete := λ x => by cases x <;> simp

def emptyIn : World → Entity → Bool
  | .allEmpty, _ => true
  | .midEmpty, .b4 => false
  | .midEmpty, _ => true
  | .nearEmpty, .b1 | .nearEmpty, .b2 => true
  | .nearEmpty, _ => false

/-- All entities are bottles in this scenario (trivial restrictor). -/
def isBottle : bottleModel.Entity → Bool := λ _ => true

-- ============================================================================
-- §4. Truth Table: "Every bottle is empty" under each DDRP
-- ============================================================================

/-- Truth of "every bottle is empty" under a given spatial domain restriction. -/
def everyBottleEmpty (scale : SpatialScale) (w : World) : Bool :=
  every_restricted bottleModel (sceneDDRP.region scale) isBottle (emptyIn w)

-- w_near: only proximal bottles empty
-- Only peripersonal restriction licenses the utterance.
theorem w_near_peri : everyBottleEmpty .peripersonal .nearEmpty = true := by native_decide
theorem w_near_action : everyBottleEmpty .action .nearEmpty = false := by native_decide
theorem w_near_vista : everyBottleEmpty .vista .nearEmpty = false := by native_decide

-- w_mid: proximal + action-space bottles empty
-- Both peripersonal and action restrictions license the utterance.
theorem w_mid_peri : everyBottleEmpty .peripersonal .midEmpty = true := by native_decide
theorem w_mid_action : everyBottleEmpty .action .midEmpty = true := by native_decide
theorem w_mid_vista : everyBottleEmpty .vista .midEmpty = false := by native_decide

-- w_all: all bottles empty
-- All restrictions license the utterance.
theorem w_all_peri : everyBottleEmpty .peripersonal .allEmpty = true := by native_decide
theorem w_all_action : everyBottleEmpty .action .allEmpty = true := by native_decide
theorem w_all_vista : everyBottleEmpty .vista .allEmpty = true := by native_decide

-- ============================================================================
-- §5. Truth Table: "Some bottle is empty" under each DDRP
-- ============================================================================

/-- Truth of "some bottle is empty" under a given spatial domain restriction. -/
def someBottleEmpty (scale : SpatialScale) (w : World) : Bool :=
  some_restricted bottleModel (sceneDDRP.region scale) isBottle (emptyIn w)

-- w_near: only proximal bottles empty
-- All restrictions license "some bottle is empty" (there's always a witness).
theorem some_near_peri : someBottleEmpty .peripersonal .nearEmpty = true := by native_decide
theorem some_near_action : someBottleEmpty .action .nearEmpty = true := by native_decide
theorem some_near_vista : someBottleEmpty .vista .nearEmpty = true := by native_decide

-- w_mid: proximal + action-space bottles empty
theorem some_mid_peri : someBottleEmpty .peripersonal .midEmpty = true := by native_decide
theorem some_mid_action : someBottleEmpty .action .midEmpty = true := by native_decide
theorem some_mid_vista : someBottleEmpty .vista .midEmpty = true := by native_decide

-- w_all: all bottles empty
theorem some_all_peri : someBottleEmpty .peripersonal .allEmpty = true := by native_decide
theorem some_all_action : someBottleEmpty .action .allEmpty = true := by native_decide
theorem some_all_vista : someBottleEmpty .vista .allEmpty = true := by native_decide

-- ============================================================================
-- §6. Key Predictions
-- ============================================================================

/-- **Proximal default**: In the proximal world, only peripersonal restriction
    makes "every bottle is empty" true. The listener *must* infer the speaker
    intended the proximal domain — no other DDRP candidate works.
    This illustrates R&S's claim (§3.1) that perceptual availability biases
    hearers toward proximal domains: when only one candidate restriction works,
    pragmatic selection is forced. -/
theorem proximal_default :
    everyBottleEmpty .peripersonal .nearEmpty = true ∧
    everyBottleEmpty .action .nearEmpty = false ∧
    everyBottleEmpty .vista .nearEmpty = false :=
  ⟨by native_decide, by native_decide, by native_decide⟩

/-- **↓MON/↑MON contrast**: ⟦every⟧ and ⟦some⟧ react oppositely to domain
    restriction. In the proximal world, ⟦every⟧ is true only under peripersonal
    restriction (↓MON: smaller domain helps), while ⟦some⟧ is true under all
    restrictions (↑MON: larger domain never hurts). -/
theorem monotonicity_contrast :
    -- every: only peripersonal works
    everyBottleEmpty .peripersonal .nearEmpty = true ∧
    everyBottleEmpty .action .nearEmpty = false ∧
    -- some: all scales work (↑MON preserves truth upward)
    someBottleEmpty .peripersonal .nearEmpty = true ∧
    someBottleEmpty .action .nearEmpty = true ∧
    someBottleEmpty .vista .nearEmpty = true :=
  ⟨by native_decide, by native_decide, by native_decide,
   by native_decide, by native_decide⟩

-- ============================================================================
-- §7. Bridge to Theory: Nesting from DDRP Structure
-- ============================================================================

/-- ⟦every⟧ nesting: truth under any scale entails truth under any smaller scale.
    Uses the general `DDRP.every_nesting` theorem parameterized by the ordering. -/
theorem nesting_action_to_peri (w : World) :
    everyBottleEmpty .action w = true →
    everyBottleEmpty .peripersonal w = true := by
  exact DDRP.every_nesting sceneDDRP isBottle (emptyIn w) (show SpatialScale.peripersonal ≤ .action by decide)

theorem nesting_vista_to_action (w : World) :
    everyBottleEmpty .vista w = true →
    everyBottleEmpty .action w = true := by
  exact DDRP.every_nesting sceneDDRP isBottle (emptyIn w) (show SpatialScale.action ≤ .vista by decide)

/-- Transitive nesting: vista → peripersonal (2-step composition). -/
theorem nesting_vista_to_peri (w : World) :
    everyBottleEmpty .vista w = true →
    everyBottleEmpty .peripersonal w = true := by
  exact DDRP.every_nesting sceneDDRP isBottle (emptyIn w) (show SpatialScale.peripersonal ≤ .vista by decide)

/-- ⟦some⟧ nesting (reversed): truth under any scale entails truth under any
    larger scale. The ↑MON dual of ⟦every⟧ nesting. -/
theorem some_nesting_peri_to_action (w : World) :
    someBottleEmpty .peripersonal w = true →
    someBottleEmpty .action w = true := by
  exact DDRP.some_nesting sceneDDRP isBottle (emptyIn w) (show SpatialScale.peripersonal ≤ .action by decide)

theorem some_nesting_action_to_vista (w : World) :
    someBottleEmpty .action w = true →
    someBottleEmpty .vista w = true := by
  exact DDRP.some_nesting sceneDDRP isBottle (emptyIn w) (show SpatialScale.action ≤ .vista by decide)

/-- Transitive ⟦some⟧ nesting: peripersonal → vista (2-step composition). -/
theorem some_nesting_peri_to_vista (w : World) :
    someBottleEmpty .peripersonal w = true →
    someBottleEmpty .vista w = true := by
  exact DDRP.some_nesting sceneDDRP isBottle (emptyIn w) (show SpatialScale.peripersonal ≤ .vista by decide)

-- ============================================================================
-- §8. RSA Connection: DDRPs as Latent Interpretation Variables
-- ============================================================================

/-- Utterance type for the RSA model. -/
inductive Utterance where
  | everyEmpty  -- "every bottle is empty"
  | someEmpty   -- "some bottle is empty"
  deriving DecidableEq, BEq, Repr, Inhabited

instance : Fintype Utterance where
  elems := {.everyEmpty, .someEmpty}
  complete := λ x => by cases x <;> simp

/-- Literal meaning under a given DDRP scale. -/
def utteranceMeaning (scale : SpatialScale) : Utterance → World → Bool
  | .everyEmpty, w => everyBottleEmpty scale w
  | .someEmpty, w => someBottleEmpty scale w

/-- RSAConfig instantiation with DDRPs as the latent variable.

    The listener reasons over which spatial scale the speaker intended when
    uttering a quantified sentence. `Latent = SpatialScale`: L1 marginalizes
    over candidate domain restrictions to infer the speaker's intended domain.

    While R&S argue against RSA as explaining *default status* (§2.1), their
    DDRPs are fully compatible with RSA as the *selection mechanism* once the
    candidate set is fixed by cognitive heuristics. This models the pragmatic
    step: given the DDRP candidates, which one did the speaker intend? -/
noncomputable def domainRestrictionRSA : RSA.RSAConfig Utterance World where
  Latent := SpatialScale
  meaning scale u w := if utteranceMeaning scale u w then 1 else 0
  meaning_nonneg _ _ _ := by split <;> norm_num
  s1Score := λ l0 α _ w u => (l0 u w) ^ α
  s1Score_nonneg _ _ _ _ _ h_nn h_pos := by
    exact Real.rpow_nonneg (h_nn _ _) _
  α := 1
  α_pos := by norm_num
  latentPrior_nonneg := λ _ _ => by norm_num
  worldPrior_nonneg := λ _ => by norm_num

/-- L0 correctly reflects literal semantics: when ⟦every⟧ is true under
    a given scale, L0's score is positive. -/
theorem l0_reflects_every (s : SpatialScale) (w : World)
    (h : everyBottleEmpty s w = true) :
    domainRestrictionRSA.meaning s .everyEmpty w = 1 := by
  simp [domainRestrictionRSA, utteranceMeaning, h]

/-- L0 correctly reflects literal semantics: when ⟦every⟧ is false under
    a given scale, L0's score is zero. -/
theorem l0_reflects_every_false (s : SpatialScale) (w : World)
    (h : everyBottleEmpty s w = false) :
    domainRestrictionRSA.meaning s .everyEmpty w = 0 := by
  simp [domainRestrictionRSA, utteranceMeaning, h]

end Phenomena.Quantification.Studies.RitchieSchiller2024
