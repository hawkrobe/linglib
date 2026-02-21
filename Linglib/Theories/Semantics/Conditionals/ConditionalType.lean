/-
# Conditional Type: Hypothetical vs Premise Conditionals

Formalizes the distinction between Hypothetical Conditionals (HCs) and
Premise Conditionals (PCs) as described in the linguistics literature.

## Insight

HCs and PCs have the SAME truth conditions but DIFFERENT felicity conditions:
- **HC**: Antecedent is supposed/hypothesized; speaker uncertain
- **PC**: Antecedent echoes prior discourse; speaker treats as established

The distinction is DISCOURSE-LEVEL, not semantic. This parallels the
separation of truth from assertability in `Assertability.lean`.

## Polarity Licensing

A key diagnostic: HCs license NPIs, PCs license PPIs in the antecedent.

This requires separating TWO factors:
1. **Monotonicity** (semantic): Conditional antecedents are always DE
2. **Epistemic status** (discourse): HC = uncertain, PC = established

NPI licensing requires BOTH DE + uncertain (HC).
PPI licensing requires established status (PC).
This explains why PCs block NPIs despite being semantically DE!

## References

- Lassiter (2025). Sorting out left-nested conditionals.
- Iatridou (1991). Topics in Conditionals.
- Haegeman (2003). Conditional clauses: External and internal syntax.
- Bhatt & Pancheva (2006). Conditionals.
-/

import Linglib.Theories.Semantics.Dynamic.State
import Linglib.Core.Proposition
import Linglib.Theories.Semantics.Entailment.Polarity
import Linglib.Theories.Semantics.Conditionals.Basic

namespace Semantics.Conditionals

open Core.Proposition
open Semantics.Entailment.Polarity
open Semantics.Dynamic.State

-- Conditional Type: HC vs PC

/--
The two fundamental conditional interpretation types.

Following Lassiter (2025) and building on Iatridou (1991), Haegeman (2003):
- **Hypothetical (HC)**: Antecedent is supposed; speaker uncertain about its truth
- **Premise (PC)**: Antecedent echoes prior discourse; no uncertainty implication

Key diagnostics:
- HC can't be paraphrased with "given that/since"
- PC can be paraphrased with "given that/since"
- HC licenses NPIs in antecedent
- PC licenses PPIs in antecedent
-/
inductive ConditionalType where
  | hypothetical  -- Antecedent supposed, speaker uncertain
  | premise       -- Antecedent echoes discourse, no uncertainty
  deriving DecidableEq, Repr, BEq, Inhabited

namespace ConditionalType

/-- Whether a conditional type implies speaker uncertainty about the antecedent -/
def impliesUncertainty : ConditionalType → Bool
  | .hypothetical => true
  | .premise => false

/-- Whether a conditional type requires discourse anchoring -/
def requiresDiscourseAnchor : ConditionalType → Bool
  | .hypothetical => false
  | .premise => true

/-- Can this conditional type be paraphrased with "given that" or "since"?

    Definitionally equal to `requiresDiscourseAnchor`: a conditional
    admits "given that" paraphrase iff its antecedent is discourse-anchored. -/
abbrev canUseGivenThat (ct : ConditionalType) : Bool := ct.requiresDiscourseAnchor

end ConditionalType

-- Discourse Echo Condition

/--
Check whether a proposition "echoes" the current discourse state.

A proposition p echoes the discourse if:
1. It is entailed by some speaker commitment (dcS), OR
2. It is entailed by some common ground proposition (cg)

This captures the requirement that premise conditionals must have their
antecedent grounded in prior discourse.
-/
def echoesDiscourse {W : Type*} (ds : DiscourseState W) (p : BProp W)
    (worlds : List W) : Bool :=
  ds.dcS.any (λ q => Decidable.entails W worlds q p) ||
  ds.cg.any (λ q => Decidable.entails W worlds q p)

/--
Weaker echo check: proposition is merely consistent with discourse.

This is a looser condition - the antecedent is at least compatible with
what's been established, even if not explicitly entailed.
-/
def consistentWithDiscourse {W : Type*} (ds : DiscourseState W) (p : BProp W)
    (worlds : List W) : Bool :=
  worlds.any λ w => ds.compatible w && p w

-- Felicity Conditions

/--
Felicity condition for premise conditionals.

A PC "if p, then q" is felicitous in discourse state ds iff:
- The antecedent p echoes prior discourse (dcS or cg)

This is the key felicity requirement that distinguishes PC from HC.
-/
def pcFelicitous {W : Type*} (ds : DiscourseState W) (antecedent : BProp W)
    (worlds : List W) : Bool :=
  echoesDiscourse ds antecedent worlds

/--
Felicity condition for hypothetical conditionals.

An HC "if p, then q" is felicitous in discourse state ds iff:
- The antecedent p is consistent with cg (not contradicted)
- The antecedent p is not already established (some uncertainty)

Note: The second condition is captured implicitly - if p were established,
a PC reading would be preferred.
-/
def hcFelicitous {W : Type*} (ds : DiscourseState W) (antecedent : BProp W)
    (worlds : List W) : Bool :=
  consistentWithDiscourse ds antecedent worlds

-- Polarity Context for Conditionals

/--
Epistemic status of an antecedent for polarity licensing purposes.

This is the key insight: polarity licensing in conditional antecedents
depends on BOTH monotonicity (semantic) AND epistemic status (discourse).

- **hypothetical**: Speaker treats antecedent as uncertain → licenses NPIs
- **established**: Speaker treats antecedent as given → licenses PPIs
-/
inductive AntecedentStatus where
  | hypothetical   -- Speaker uncertain → licenses NPIs
  | established    -- Speaker treats as given → licenses PPIs
  deriving DecidableEq, Repr, BEq, Inhabited

/--
Get the antecedent status from a conditional type.
-/
def ConditionalType.toAntecedentStatus : ConditionalType → AntecedentStatus
  | .hypothetical => .hypothetical
  | .premise => .established

/--
Full polarity context for conditional antecedents.

Separates the two factors that determine polarity licensing:
1. **monotonicity**: Semantic DE/UE property (conditional antecedents are DE)
2. **epistemicStatus**: Discourse-level status (uncertain vs established)

NPI licensing requires: DE monotonicity + hypothetical status
PPI licensing requires: established status (monotonicity irrelevant)
-/
structure ConditionalPolarityContext where
  /-- Semantic monotonicity (conditional antecedents are always DE) -/
  monotonicity : ContextPolarity := .downward
  /-- Discourse-level epistemic status -/
  epistemicStatus : AntecedentStatus
  deriving DecidableEq, Repr

namespace ConditionalPolarityContext

/--
Create polarity context from conditional type.

All conditional antecedents are semantically DE; the epistemic status
varies based on whether it's an HC or PC.
-/
def fromConditionalType (ct : ConditionalType) : ConditionalPolarityContext :=
  { monotonicity := .downward
    epistemicStatus := ct.toAntecedentStatus }

/--
Does this context license NPIs?

NPIs require BOTH:
1. Downward-entailing monotonicity (semantic)
2. Hypothetical epistemic status (discourse)

This explains why PCs block NPIs despite being DE!
-/
def licensesNPI (ctx : ConditionalPolarityContext) : Bool :=
  ctx.monotonicity == .downward && ctx.epistemicStatus == .hypothetical

/--
Does this context license PPIs?

PPIs are licensed when the antecedent has established status.
(Monotonicity is irrelevant for PPI licensing.)
-/
def licensesPPI (ctx : ConditionalPolarityContext) : Bool :=
  ctx.epistemicStatus == .established

end ConditionalPolarityContext

-- Theorems: Polarity Licensing

/--
**PCs are felicitous iff antecedent echoes prior discourse.**

This is the defining felicity condition for premise conditionals.
-/
theorem pc_felicity {W : Type*} (ds : DiscourseState W) (p : BProp W)
    (worlds : List W) :
    pcFelicitous ds p worlds = echoesDiscourse ds p worlds := rfl

/--
**HCs license NPIs in the antecedent.**

Because HCs have both:
- DE monotonicity (semantic property of conditional antecedents)
- Hypothetical epistemic status (speaker uncertainty)
-/
theorem hc_licenses_npi :
    (ConditionalPolarityContext.fromConditionalType .hypothetical).licensesNPI = true := by
  native_decide

/--
**PCs license PPIs in the antecedent.**

Because PCs have established epistemic status.
-/
theorem pc_licenses_ppi :
    (ConditionalPolarityContext.fromConditionalType .premise).licensesPPI = true := by
  native_decide

/--
**PCs do NOT license NPIs in the antecedent.**

Despite being semantically DE, PCs lack the hypothetical epistemic status
required for NPI licensing. This is the key insight from Lassiter (2025).
-/
theorem pc_blocks_npi :
    (ConditionalPolarityContext.fromConditionalType .premise).licensesNPI = false := by
  native_decide

/--
**HCs do NOT license PPIs in the antecedent.**

Because HCs have hypothetical (not established) epistemic status.
-/
theorem hc_blocks_ppi :
    (ConditionalPolarityContext.fromConditionalType .hypothetical).licensesPPI = false := by
  native_decide

-- Conditional with Explicit Type

/--
A conditional with its interpretation type made explicit.

This bundles the antecedent, consequent, and interpretation type together.
Useful for analyzing how different readings affect discourse update.
-/
structure TypedConditional (W : Type*) where
  /-- The antecedent proposition -/
  antecedent : BProp W
  /-- The consequent proposition -/
  consequent : BProp W
  /-- The interpretation type (HC or PC) -/
  condType : ConditionalType

namespace TypedConditional

variable {W : Type*}

/-- Get the semantic content (same for both HC and PC) -/
def semantics (tc : TypedConditional W) : BProp W :=
  materialImpB tc.antecedent tc.consequent

/-- Check felicity in a given discourse state -/
def isFelicitous (tc : TypedConditional W) (ds : DiscourseState W)
    (worlds : List W) : Bool :=
  match tc.condType with
  | .hypothetical => hcFelicitous ds tc.antecedent worlds
  | .premise => pcFelicitous ds tc.antecedent worlds

/-- Get the polarity context for the antecedent -/
def antecedentPolarityContext (tc : TypedConditional W) : ConditionalPolarityContext :=
  ConditionalPolarityContext.fromConditionalType tc.condType

end TypedConditional

/--
**HCs and PCs have identical truth conditions.**

The distinction is entirely in felicity/discourse conditions, not semantics.
Both are interpreted via the same conditional semantics (material, strict,
Kratzer, etc.).
-/
theorem hc_pc_same_semantics {W : Type*} (p q : BProp W) :
    (TypedConditional.mk p q .hypothetical).semantics =
    (TypedConditional.mk p q .premise).semantics := rfl

-- Cross-Linguistic Markers

/--
Cross-linguistic conditional markers and their type restrictions.

Some languages have distinct lexical items for HC vs PC conditionals.
This captures the typological pattern.

Note: `pcOnly` is currently uninstantiated across known languages;
included for typological completeness.
-/
inductive ConditionalMarkerType where
  | hcOnly     -- Only marks HCs (e.g., Japanese -ra, German falls)
  | pcOnly     -- Only marks PCs (currently uninstantiated)
  | both       -- Can mark either (e.g., English "if", German wenn)
  deriving DecidableEq, Repr, BEq

/-- Cross-linguistic conditional marker datum.

    Per-language marker entries live in `Fragments/{Language}/Conditionals.lean`. -/
structure ConditionalMarker where
  language : String
  marker : String
  gloss : String
  markerType : ConditionalMarkerType
  notes : String
  deriving Repr

-- Summary

/-!
## Summary

This module provides:

### Types
- `ConditionalType`: HC vs PC distinction
- `AntecedentStatus`: Epistemic status for polarity
- `ConditionalPolarityContext`: Full polarity context (monotonicity + epistemic)
- `TypedConditional`: Conditional with explicit interpretation type
- `ConditionalMarkerType` / `ConditionalMarker`: Marker type vocabulary
  (per-language data in `Fragments/{Language}/Conditionals.lean`)

### Key Operations
- `echoesDiscourse`: Check if proposition echoes prior discourse
- `pcFelicitous`: Felicity condition for premise conditionals
- `hcFelicitous`: Felicity condition for hypothetical conditionals
- `licensesNPI`: Check if context licenses NPIs
- `licensesPPI`: Check if context licenses PPIs

### Theorems
- `hc_pc_same_semantics`: HCs and PCs have identical truth conditions
- `hc_licenses_npi`: HCs license NPIs in antecedent
- `pc_licenses_ppi`: PCs license PPIs in antecedent
- `pc_blocks_npi`: PCs do NOT license NPIs (key insight!)
- `hc_blocks_ppi`: HCs do NOT license PPIs

### Insight

The HC/PC distinction is DISCOURSE-LEVEL, not semantic. The polarity
licensing pattern requires separating:
1. Monotonicity (semantic) - always DE in conditional antecedents
2. Epistemic status (discourse) - uncertain (HC) vs established (PC)

This explains the apparent paradox that PCs block NPIs despite being
semantically DE: NPI licensing requires BOTH DE + uncertain status.
-/

end Semantics.Conditionals
