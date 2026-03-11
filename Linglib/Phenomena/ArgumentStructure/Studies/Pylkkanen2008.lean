import Linglib.Theories.Syntax.Minimalism.Core.Basic
import Linglib.Theories.Syntax.Minimalism.Core.Applicative
import Linglib.Phenomena.ArgumentStructure.Studies.Larson1988

/-!
# @cite{pylkknen-2008} — Introducing Arguments
@cite{pylkknen-2008} @cite{cuervo-2003} @cite{barss-lasnik-1986}

*Linguistic Inquiry Monographs* 49. MIT Press.

## Core Claims

1. **High vs Low Applicatives**: Applicative heads come in two types.
   Low Appl merges below VP, relating the applied argument to the theme
   (transfer-of-possession). High Appl merges above vP, relating the
   applied argument to the event (benefactive).

2. **C-command asymmetries**: In both configurations, the applied argument
   asymmetrically c-commands the theme. This derives the
   @cite{barss-lasnik-1986} binding asymmetries structurally.

3. **Cross-linguistic variation**: Languages vary in which Appl types
   they allow. English has both; Bantu languages have high Appl only.

## Cross-references

- `Studies/Larson1988.lean`: VP shell predecessor — same c-command
  hierarchy (IO > DO) derived differently. Bridge theorem below proves
  convergence.
- `Studies/Kratzer1996.lean` Part III: Voice-based tree derivations
  (transitive, anticausative) using the same infrastructure.
-/

namespace Phenomena.ArgumentStructure.Studies.Pylkkanen2008

open Minimalism

-- ============================================================================
-- § 1: Lexical Items
-- ============================================================================

def voice_ag_t  := mkLeafPhon .Voice [.v]  "Voice[AG]"  400
def v_head_t    := mkLeafPhon .v     [.V]  "v"          401
def appl_low_t  := mkLeafPhon .Appl  [.V]  "Appl[LOW]"  402
def appl_high_t := mkLeafPhon .Appl  [.v]  "Appl[HI]"   403
def V_sent_t    := mkLeafPhon .V     [.D]  "sent"       404
def V_baked_t   := mkLeafPhon .V     [.D]  "baked"      405
def DP_john_t   := mkLeafPhon .D     []    "John"       406
def DP_mary_t   := mkLeafPhon .D     []    "Mary"       407
def DP_letter_t := mkLeafPhon .D     []    "a letter"   408
def DP_cake_t   := mkLeafPhon .D     []    "a cake"     409

-- ============================================================================
-- § 2: Tree Derivations
-- ============================================================================

/-- Ditransitive with low applicative: "John sent Mary a letter"

    `[VoiceP John [Voice' Voice_AG [vP v [ApplP Mary [Appl' Appl_LOW [VP sent [DP a letter]]]]]]]`

    Low Appl introduces the goal *below* VP: the goal c-commands the theme
    but not vice versa. -/
def ditransitiveTree : SyntacticObject :=
  merge DP_john_t
    (merge voice_ag_t
      (merge v_head_t
        (merge DP_mary_t
          (merge appl_low_t
            (merge V_sent_t DP_letter_t)))))

/-- High applicative benefactive: "John baked Mary a cake"

    `[VoiceP John [Voice' Voice_AG [ApplP Mary [Appl' Appl_HIGH [vP v [VP baked [DP a cake]]]]]]]`

    High Appl introduces the benefactive *above* vP: the benefactive
    c-commands the theme. -/
def benefactiveTree : SyntacticObject :=
  merge DP_john_t
    (merge voice_ag_t
      (merge DP_mary_t
        (merge appl_high_t
          (merge v_head_t
            (merge V_baked_t DP_cake_t)))))

-- ============================================================================
-- § 3: C-command Predictions
-- ============================================================================

-- Ditransitive (low Appl): agent > goal > theme

/-- Agent c-commands goal. -/
theorem ditransitive_agent_ccommands_goal :
    cCommandsInB ditransitiveTree DP_john_t DP_mary_t = true := by native_decide

/-- Agent c-commands theme. -/
theorem ditransitive_agent_ccommands_theme :
    cCommandsInB ditransitiveTree DP_john_t DP_letter_t = true := by native_decide

/-- Goal c-commands theme — the @cite{barss-lasnik-1986} asymmetry
    derived structurally from the low-Appl position. -/
theorem ditransitive_goal_ccommands_theme :
    cCommandsInB ditransitiveTree DP_mary_t DP_letter_t = true := by native_decide

/-- Theme does NOT c-command goal: the asymmetry is structural. -/
theorem ditransitive_theme_not_ccommands_goal :
    cCommandsInB ditransitiveTree DP_letter_t DP_mary_t = false := by native_decide

-- Benefactive (high Appl): benefactive > theme

/-- Benefactive c-commands theme. -/
theorem benefactive_benef_ccommands_theme :
    cCommandsInB benefactiveTree DP_mary_t DP_cake_t = true := by native_decide

/-- Theme does NOT c-command benefactive. -/
theorem benefactive_theme_not_ccommands_benef :
    cCommandsInB benefactiveTree DP_cake_t DP_mary_t = false := by native_decide

-- Appl head containment

/-- Low applicative marks the ditransitive. -/
theorem send_is_low_appl :
    containsB ditransitiveTree appl_low_t = true := by native_decide

/-- High applicative marks the benefactive. -/
theorem bake_is_high_appl :
    containsB benefactiveTree appl_high_t = true := by native_decide

-- ============================================================================
-- § 4: Bridge — Larson VP Shell ↔ Modern Voice/Appl
-- ============================================================================

/-! @cite{larson-1988}'s VP shell is the precursor of the modern Voice/v* +
Applicative decomposition. While the tree shapes differ (Larson uses
one VP-shell layer; modern theory uses Voice, v, Appl heads), the
c-command hierarchy among DP arguments is identical: agent > goal/IO > theme/DO. -/

open Phenomena.ArgumentStructure.Studies.Larson1988 in

/-- @cite{larson-1988}'s DOC and the modern Voice + low-Appl derivation
    produce the same c-command hierarchy: IO asymmetrically c-commands DO.

    This proves that @cite{larson-1988} and @cite{pylkknen-2008},
    despite different decompositions, converge on the same structural
    prediction for @cite{barss-lasnik-1986} asymmetries. -/
theorem larson_modern_same_hierarchy :
    -- Larson's DOC: IO > DO
    cCommandsInB docDativeShift.final DP_mary DP_letter = true ∧
    cCommandsInB docDativeShift.final DP_letter DP_mary = false ∧
    -- Modern Voice/Appl: goal > theme (same asymmetry)
    cCommandsInB ditransitiveTree DP_mary_t DP_letter_t = true ∧
    cCommandsInB ditransitiveTree DP_letter_t DP_mary_t = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

end Phenomena.ArgumentStructure.Studies.Pylkkanen2008
