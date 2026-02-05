/-
# Left-Nested Conditionals (LNCs)

Formalizes the analysis of left-nested conditionals following Lassiter (2025)
"Sorting out left-nested conditionals."

## Overview

A left-nested conditional (LNC) has another conditional in the antecedent:
  "If (B if A), then C"  =  "If A → B, then C"

Example (Gibbard 1981):
  "If Kripke was there if Strawson was, then Anscomb was there"

## Key Claim

Lassiter (2025) argues that bare LNCs are preferentially interpreted as
**premise conditionals** (PCs), not hypothetical conditionals (HCs).

### Why?

The inner conditional "B if A" refers to a **conditional proposition** -
something that must be grounded in prior discourse to be suppposed. This
automatically satisfies the discourse-anchoring requirement of PCs.

### Exception

LNCs with modals, quantificational adverbs, or generic/habitual readings
CAN be interpreted as HCs, because these provide "object-level" content
that can be genuinely supposed without prior discourse.

## References

- Lassiter (2025). Sorting out left-nested conditionals.
- Gibbard (1981). Two recent theories of conditionals.
- McGee (1985). A counterexample to modus ponens.
-/

import Linglib.Theories.Montague.Sentence.Conditional.ConditionalType
import Linglib.Theories.Montague.Sentence.Conditional.Basic

namespace Montague.Sentence.Conditional

open Core.Proposition
open Theories.DynamicSemantics.State

-- Left-Nested Conditional Structure

/--
Left-nested conditional structure: "If (B if A), C"

The structure of an LNC where the outer antecedent is itself a conditional.

Example: "If Kripke was there if Strawson was, Anscomb was there"
- innerAntecedent = "Strawson was there"
- innerConsequent = "Kripke was there"
- outerConsequent = "Anscomb was there"
-/
structure LNC (W : Type*) where
  /-- A: The inner antecedent -/
  innerAntecedent : BProp W
  /-- B: The inner consequent -/
  innerConsequent : BProp W
  /-- C: The outer consequent -/
  outerConsequent : BProp W

namespace LNC

variable {W : Type*}

/--
Get the inner conditional "B if A" as a proposition.

This is the outer antecedent of the full LNC.
-/
def innerConditional (lnc : LNC W) : BProp W :=
  materialImpB lnc.innerAntecedent lnc.innerConsequent

/--
Full LNC semantics using material implication.

"If (B if A), C" = (A → B) → C
-/
def semantics (lnc : LNC W) : BProp W :=
  materialImpB (lnc.innerConditional) lnc.outerConsequent

/--
Full LNC semantics using Kratzer-style conditionals.

The outer conditional uses the Kratzer semantics with modal base and
ordering source, while the inner conditional is the restrictor.
-/
def kratzerSemantics (ctx : KratzerContext W) (lnc : LNC W) : Prop' W :=
  kratzerConditional ctx lnc.innerConditional lnc.outerConsequent

end LNC

-- Inner Conditional Content Type

/--
Classification of the inner conditional's content.

The content type determines whether the LNC can be interpreted as an HC.
Bare conditionals force PC reading; modals/generics allow HC reading.
-/
inductive InnerConditionalContent where
  /-- No modal/generic content → forces PC reading -/
  | bare
  /-- Has modal verb/operator → allows HC reading -/
  | modal
  /-- Generic/habitual → allows HC reading -/
  | generic
  /-- Quantificational adverb (always, usually, etc.) → allows HC reading -/
  | quantAdv
  deriving DecidableEq, Repr, BEq, Inhabited

namespace InnerConditionalContent

/-- Does this content type require discourse anchoring for the inner conditional? -/
def requiresDiscourseAnchor : InnerConditionalContent → Bool
  | .bare => true
  | .modal => false
  | .generic => false
  | .quantAdv => false

/-- Can this content type be interpreted as an HC? -/
def allowsHCReading : InnerConditionalContent → Bool
  | .bare => false
  | .modal => true
  | .generic => true
  | .quantAdv => true

end InnerConditionalContent

-- LNC Interpretation

/--
Interpret an LNC given discourse context and content type.

The main result of Lassiter (2025): bare LNCs default to PC interpretation.
-/
def interpretLNC {W : Type*} (ds : DiscourseState W) (lnc : LNC W)
    (content : InnerConditionalContent) (worlds : List W) : ConditionalType :=
  if content.allowsHCReading then
    -- Modal/generic/quantAdv: can be either HC or PC
    -- Default to PC if inner conditional echoes discourse
    if echoesDiscourse ds lnc.innerConditional worlds then
      .premise
    else
      .hypothetical
  else
    -- Bare: must be PC (inner conditional requires discourse anchor)
    .premise

/--
Check if an LNC is felicitous in a given discourse state.
-/
def lncFelicitous {W : Type*} (ds : DiscourseState W) (lnc : LNC W)
    (content : InnerConditionalContent) (worlds : List W) : Bool :=
  match interpretLNC ds lnc content worlds with
  | .hypothetical => hcFelicitous ds lnc.innerConditional worlds
  | .premise => pcFelicitous ds lnc.innerConditional worlds

-- Theorems

/--
**Main result: Bare LNCs default to PC interpretation.**

When the inner conditional has bare content (no modal/generic/quantAdv),
the LNC is interpreted as a premise conditional, regardless of discourse.
-/
theorem bare_lnc_as_pc {W : Type*} (ds : DiscourseState W) (lnc : LNC W)
    (worlds : List W) :
    interpretLNC ds lnc .bare worlds = .premise := by
  unfold interpretLNC InnerConditionalContent.allowsHCReading
  simp

/--
**Exception: Modal LNCs can be HCs.**

When the inner conditional has modal content, the LNC can be interpreted
as either HC or PC, depending on discourse context.
-/
theorem modal_lnc_allows_hc {W : Type*} (ds : DiscourseState W) (lnc : LNC W)
    (worlds : List W)
    (h_no_echo : echoesDiscourse ds lnc.innerConditional worlds = false) :
    interpretLNC ds lnc .modal worlds = .hypothetical := by
  unfold interpretLNC InnerConditionalContent.allowsHCReading
  simp [h_no_echo]

/--
**Modal LNCs prefer PC when discourse anchor exists.**
-/
theorem modal_lnc_prefers_pc {W : Type*} (ds : DiscourseState W) (lnc : LNC W)
    (worlds : List W)
    (h_echo : echoesDiscourse ds lnc.innerConditional worlds = true) :
    interpretLNC ds lnc .modal worlds = .premise := by
  unfold interpretLNC InnerConditionalContent.allowsHCReading
  simp [h_echo]

/--
**LNC semantics grounded in Kratzer.**

The LNC semantics is compositionally derived from Kratzer's conditional
semantics - it's not stipulated specially for LNCs.
-/
theorem lnc_grounded {W : Type*} (ctx : KratzerContext W) (lnc : LNC W) :
    lnc.kratzerSemantics ctx =
    kratzerConditional ctx lnc.innerConditional lnc.outerConsequent := rfl

-- Extended LNC with Metadata

/--
Left-nested conditional with metadata for analysis.
-/
structure AnnotatedLNC (W : Type*) where
  /-- The LNC structure -/
  lnc : LNC W
  /-- Content type of inner conditional -/
  content : InnerConditionalContent
  /-- String representation for display -/
  sentence : String := ""
  /-- Notes on interpretation -/
  notes : String := ""

namespace AnnotatedLNC

variable {W : Type*}

/-- Get interpretation in discourse context -/
def interpret (alnc : AnnotatedLNC W) (ds : DiscourseState W)
    (worlds : List W) : ConditionalType :=
  interpretLNC ds alnc.lnc alnc.content worlds

/-- Check felicity -/
def isFelicitous (alnc : AnnotatedLNC W) (ds : DiscourseState W)
    (worlds : List W) : Bool :=
  lncFelicitous ds alnc.lnc alnc.content worlds

/-- Get polarity context for inner conditional antecedent -/
def innerAntecedentPolarity (alnc : AnnotatedLNC W) (ds : DiscourseState W)
    (worlds : List W) : ConditionalPolarityContext :=
  ConditionalPolarityContext.fromConditionalType (alnc.interpret ds worlds)

end AnnotatedLNC

-- Polarity Patterns in LNCs

/-!
## Polarity Patterns (Lassiter 2025, Section 4)

The PC analysis of LNCs predicts specific polarity patterns:

### In the embedded consequent (B in "if (B if A), C")
- PPIs licensed: "If John helped someone if asked, we're in good shape"
- NPIs blocked: "*If John helped anyone if asked, we're in good shape"

### In the inner antecedent (A)
- This position is DE regardless of HC/PC reading
- But polarity licensing also depends on epistemic status

The embedded consequent patterns are diagnostic because:
- In HCs: the embedded consequent is in an epistemic uncertainty context
- In PCs: the embedded consequent is treated as established
-/

/--
Polarity licensing in the embedded consequent position.

Following Lassiter (2025): the embedded consequent of an LNC (the B position
in "if (B if A), C") shows polarity patterns consistent with PC reading.
-/
structure EmbeddedConsequentPolarity where
  /-- Whether the LNC licenses PPIs in B position -/
  licensesPPI : Bool
  /-- Whether the LNC licenses NPIs in B position -/
  licensesNPI : Bool

/--
Get polarity licensing for embedded consequent based on LNC interpretation.
-/
def embeddedConsequentPolarity (ct : ConditionalType) : EmbeddedConsequentPolarity :=
  match ct with
  | .hypothetical => { licensesPPI := false, licensesNPI := true }
  | .premise => { licensesPPI := true, licensesNPI := false }

/--
**Bare LNCs license PPIs in embedded consequent.**
-/
theorem bare_lnc_licenses_ppi_in_B :
    (embeddedConsequentPolarity .premise).licensesPPI = true := rfl

/--
**Bare LNCs block NPIs in embedded consequent.**
-/
theorem bare_lnc_blocks_npi_in_B :
    (embeddedConsequentPolarity .premise).licensesNPI = false := rfl

-- Example Worlds for Testing

/--
Simple world type for LNC examples.

Based on the Gibbard scenario: Strawson, Kripke, and Anscomb may or may not
have attended a party.
-/
inductive PartyWorld where
  | sOnly      -- Only Strawson attended
  | kOnly      -- Only Kripke attended
  | aOnly      -- Only Anscomb attended
  | sk         -- Strawson and Kripke
  | sa         -- Strawson and Anscomb
  | ka         -- Kripke and Anscomb
  | ska        -- All three attended
  | none_      -- No one attended
  deriving DecidableEq, Repr, BEq, Inhabited

instance : Core.Proposition.FiniteWorlds PartyWorld where
  worlds := [.sOnly, .kOnly, .aOnly, .sk, .sa, .ka, .ska, .none_]
  complete := λ w => by cases w <;> simp

namespace PartyWorld

def strawsonAttended : BProp PartyWorld
  | .sOnly | .sk | .sa | .ska => true
  | _ => false

def kripkeAttended : BProp PartyWorld
  | .kOnly | .sk | .ka | .ska => true
  | _ => false

def anscombAttended : BProp PartyWorld
  | .aOnly | .sa | .ka | .ska => true
  | _ => false

/--
Gibbard's example LNC:
"If Kripke was there if Strawson was, Anscomb was there"
-/
def gibbardLNC : LNC PartyWorld :=
  { innerAntecedent := strawsonAttended
    innerConsequent := kripkeAttended
    outerConsequent := anscombAttended }

end PartyWorld

-- Summary

/-!
## Summary

This module provides:

### Types
- `LNC`: Left-nested conditional structure
- `InnerConditionalContent`: Content type classification (bare/modal/generic/quantAdv)
- `AnnotatedLNC`: LNC with metadata for analysis
- `EmbeddedConsequentPolarity`: Polarity licensing in embedded consequent

### Key Operations
- `LNC.innerConditional`: Extract the inner conditional proposition
- `LNC.semantics`: Material implication semantics
- `LNC.kratzerSemantics`: Kratzer-style semantics
- `interpretLNC`: Determine HC/PC interpretation based on content and discourse
- `lncFelicitous`: Check felicity in discourse context
- `embeddedConsequentPolarity`: Get polarity licensing for embedded position

### Theorems
- `bare_lnc_as_pc`: Bare LNCs default to PC interpretation
- `modal_lnc_allows_hc`: Modal LNCs can be HCs (when no discourse anchor)
- `modal_lnc_prefers_pc`: Modal LNCs prefer PC when discourse anchor exists
- `lnc_grounded`: LNC semantics from Kratzer conditionals
- `bare_lnc_licenses_ppi_in_B`: Bare LNCs license PPIs in embedded consequent
- `bare_lnc_blocks_npi_in_B`: Bare LNCs block NPIs in embedded consequent

### Insight

Bare LNCs force PC interpretation because the inner conditional (a propositional
object) inherently requires discourse anchoring to be supposed. This explains:
1. Why bare LNCs sound odd out of the blue
2. Why they improve with discourse context
3. Why they pattern with PCs for polarity licensing
4. Why modal/generic LNCs allow HC readings
-/

end Montague.Sentence.Conditional
