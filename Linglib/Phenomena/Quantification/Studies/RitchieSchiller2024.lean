import Linglib.Theories.Semantics.Lexical.Determiner.DomainRestriction

/-!
# Ritchie & Schiller (2024) — Default Domain Restriction Possibilities

@cite{ritchie-schiller-2024}

Ritchie, H. & Schiller, K. (2024). Default Domain Restriction Possibilities.
*Semantics & Pragmatics* 17, Article 13: 1–49.

## The Argument

When a speaker says "Every book is on the table" at a dinner party, the hearer
restricts the quantifier domain to contextually relevant books — not all books
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
increasing spatial distances and 3 world states, then verify a key formal
consequence of the DDRP framework: in a world where only nearby entities
satisfy the predicate, only peripersonal restriction licenses the universal.

## Compositional Grounding

Truth conditions derive from `every_restricted` (DomainRestriction.lean),
which wraps `every_sem` (Quantifier.lean) with a domain restrictor predicate.
Nesting theorems derive from `DDRP.action_implies_peri` etc., connecting
the spatial affordance hierarchy to restrictor downward monotonicity.
-/

set_option autoImplicit false

namespace Phenomena.Quantification.Studies.RitchieSchiller2024

open Semantics.Montague (Model)
open Semantics.Lexical.Determiner.Quantifier (every_sem FiniteModel)
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
def sceneDDRP : DDRP Entity where
  region
    | .peripersonal => near
    | .action => mid
    | .vista => λ _ => true
    | .unrestricted => λ _ => true
  peri_sub_action e _ := by cases e <;> simp_all [near, mid]
  action_sub_vista _ _ := rfl
  vista_sub_unr _ _ := rfl
  unr_total _ := rfl

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
-- §5. Key Predictions
-- ============================================================================

/-- **Proximal default**: In the proximal world, only peripersonal restriction
    makes "every bottle is empty" true. The listener *must* infer the speaker
    intended the proximal domain — no other DDRP candidate works.
    This illustrates R&S's claim (§3.2) that cognitive heuristics bias hearers
    toward proximal domains: when only one candidate restriction works,
    pragmatic selection is forced. -/
theorem proximal_default :
    everyBottleEmpty .peripersonal .nearEmpty = true ∧
    everyBottleEmpty .action .nearEmpty = false ∧
    everyBottleEmpty .vista .nearEmpty = false :=
  ⟨by native_decide, by native_decide, by native_decide⟩

/-- **Finite candidate set**: The DDRP framework constrains the candidate set
    to one restrictor per spatial scale (§1.1, §3). This is a structural
    property of the `DDRP` type, not a derived result — but it makes explicit
    that DDRP candidates are a small structured menu, not the space of all
    possible predicates over entities (contra pure pragmatic approaches). -/
theorem finite_candidates : sceneDDRP.candidates.length = 4 := rfl

-- ============================================================================
-- §6. Bridge to Theory: Nesting from DDRP Structure
-- ============================================================================

/-- Nesting: truth under action restriction entails truth under peripersonal.
    Derived from `DDRP.action_implies_peri` (DomainRestriction.lean), which
    follows from restrictor ↓MON of ⟦every⟧ + DDRP spatial nesting. -/
theorem nesting_action_to_peri (w : World) :
    everyBottleEmpty .action w = true →
    everyBottleEmpty .peripersonal w = true :=
  DDRP.action_implies_peri (m := bottleModel) sceneDDRP isBottle (emptyIn w)

/-- Nesting: truth under vista restriction entails truth under action. -/
theorem nesting_vista_to_action (w : World) :
    everyBottleEmpty .vista w = true →
    everyBottleEmpty .action w = true :=
  DDRP.vista_implies_action (m := bottleModel) sceneDDRP isBottle (emptyIn w)

end Phenomena.Quantification.Studies.RitchieSchiller2024
