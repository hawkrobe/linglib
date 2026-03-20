import Linglib.Theories.Pragmatics.Dialogue.KOS.Rules
import Linglib.Theories.Syntax.HPSG.Core.HeadFiller

/-!
# KOS–Grammar Integration
@cite{ginzburg-2012} Ch. 5, @cite{ginzburg-sag-2000}

@cite{ginzburg-2012}'s central thesis: interaction is built into grammar.
The Sign type has `dgb-params` and `q-params` — dialogue features living
inside syntactic representations (Ch. 5, §5.2).

This module provides the integration point between HPSG signs and KOS
dialogue gameboards. Neither `HPSG/Core/Basic.lean` nor `KOS/Basic.lean`
knows about the other; this module imports both and defines:

1. **DialogueSign** — an HPSG sign extended with DGB-params and Q-params
2. **Conversions** to both `HPSG.Synsem` and `KOS.LocProp`
3. **Example entries** for wh-words and proper names

## Design

This is opt-in integration: theories that don't need dialogue features
continue to use plain HPSG signs. Theories that need the Ginzburg 2012
architecture import this module.
-/

namespace Theories.Pragmatics.Dialogue.KOS.Grammar

open Theories.Pragmatics.Dialogue.KOS
open HPSG

-- ════════════════════════════════════════════════════
-- § 1. DialogueSign
-- ════════════════════════════════════════════════════

/-- An HPSG sign extended with dialogue features.

@cite{ginzburg-2012} Ch. 5, §5.2: the sign type has three dialogue-relevant
features:
- `dgbParams`: contextual parameters that must be resolved for grounding
- `qParams`: parameters contributed by interrogative elements (wh-words)
- `questDom`: the question domain — what question the sign introduces

These correspond to DGB-PARAMS, Q-PARAMS, and QUEST-DOM in the book. -/
structure DialogueSign where
  /-- Phonological form -/
  phon : String
  /-- Part of speech (UD-based, matching HPSG.Synsem.cat) -/
  pos : UD.UPOS
  /-- Head features from HPSG -/
  head : HeadFeatures := {}
  /-- Semantic content -/
  cont : String
  /-- DGB-PARAMS: contextual parameters requiring grounding.
      Non-empty for referential NPs ("Bo"), demonstratives, etc. -/
  dgbParams : CParamSet := []
  /-- Q-PARAMS: parameters contributed by interrogative elements.
      Non-empty for wh-words ("who", "what"). -/
  qParams : CParamSet := []
  /-- QUEST-DOM: the question this sign introduces (if interrogative). -/
  questDom : Option String := none
  deriving Repr

-- ════════════════════════════════════════════════════
-- § 2. Conversions
-- ════════════════════════════════════════════════════

/-- Project a DialogueSign to its HPSG Synsem (dropping dialogue features). -/
def DialogueSign.toSynsem (ds : DialogueSign) : Synsem where
  cat := ds.pos
  head := ds.head

/-- Convert a DialogueSign to a LocProp for the KOS DGB.
DGB-PARAMS become cparams; Q-PARAMS are not cparams (they are
contributed, not requiring resolution). -/
def DialogueSign.toLocProp (ds : DialogueSign) : LocProp String where
  phon := ds.phon
  cat := toString ds.pos
  cont := ds.cont
  cparams := ds.dgbParams

/-- Conversion preserves phonological form. -/
theorem toLocProp_preserves_phon (ds : DialogueSign) :
    ds.toLocProp.phon = ds.phon := rfl

/-- Conversion preserves content. -/
theorem toLocProp_preserves_cont (ds : DialogueSign) :
    ds.toLocProp.cont = ds.cont := rfl

-- ════════════════════════════════════════════════════
-- § 3. Example Entries
-- ════════════════════════════════════════════════════

/-- "who" — a wh-word with Q-PARAMS.
@cite{ginzburg-2012} Ch. 5: wh-words contribute Q-PARAMS that
project to the QUEST-DOM of the clause. -/
def who : DialogueSign where
  phon := "who"
  pos := .PRON
  cont := "who(x)"
  qParams := [{ index := "x", restriction := "individual" }]
  questDom := some "?x.P(x)"

/-- "Jo" — a proper name with DGB-PARAMS.
@cite{ginzburg-2012} Ch. 6: referential NPs introduce DGB-PARAMS
that must be resolved (grounded) for the utterance to be integrated. -/
def jo : DialogueSign where
  phon := "Jo"
  pos := .PROPN
  cont := "jo"
  dgbParams := [{ index := "jo_ref", restriction := "individual" }]

/-- "left" — an intransitive verb (no dialogue params). -/
def left : DialogueSign where
  phon := "left"
  pos := .VERB
  head := { vform := .finite }
  cont := "leave(x)"

-- ════════════════════════════════════════════════════
-- § 4. Verification
-- ════════════════════════════════════════════════════

/-- "Jo" needs grounding: it has non-empty DGB-PARAMS. -/
theorem jo_needs_grounding : jo.toLocProp.isFullyResolved = false := rfl

/-- "who" has Q-PARAMS (it's interrogative). -/
theorem who_has_qparams : who.qParams ≠ [] := by
  simp [who]

/-- "who" doesn't need grounding (Q-PARAMS ≠ DGB-PARAMS). -/
theorem who_no_grounding_needed : who.toLocProp.isFullyResolved = true := rfl

/-- "left" has no dialogue features. -/
theorem left_plain : left.dgbParams = [] ∧ left.qParams = [] := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 5. SLASH–CPARAMS Structural Analogy
-- ════════════════════════════════════════════════════

/-- Structural analogy: discharging a SLASH gap and resolving a C-PARAM
    both reduce the count of outstanding dependencies.

    Both SLASH (filler-gap) and C-PARAMS (grounding) are sets of outstanding
    dependencies discharged by similar mechanisms. This theorem makes the
    isomorphism explicit. -/
theorem slash_cparams_both_decrease
    (sv : HPSG.SlashValue) (cat : UD.UPOS)
    (ps : CParamSet) (idx : String) :
    (sv.discharge cat).gaps.length ≤ sv.gaps.length ∧
    (ps.filter (·.index != idx)).length ≤ ps.length := by
  constructor
  · simp only [HPSG.SlashValue.discharge]; exact List.length_erase_le
  · exact List.length_filter_le _ _

end Theories.Pragmatics.Dialogue.KOS.Grammar
