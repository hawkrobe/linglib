import Linglib.Discourse.Gameboard.Defs
import Linglib.Studies.Ginzburg2012.Grounding
import Linglib.Syntax.HPSG.Basic

/-!
# KOS–Grammar Integration
[ginzburg-2012] Ch. 5, [ginzburg-sag-2000]

[ginzburg-2012]'s central thesis: interaction is built into grammar.
The Sign type has `dgb-params` and `q-params` — dialogue features living
inside syntactic representations (Ch. 5, §5.2).

This module provides the integration point between HPSG signs and KOS
dialogue gameboards. Neither `HPSG/Basic.lean` nor `Gameboard/Basic.lean`
knows about the other; this module imports both and defines:

1. **DialogueSign** — an HPSG sign extended with DGB-params and Q-params
2. **Conversions** to both `HPSG.Synsem` and `KOS.LocProp`
3. **Example entries** for wh-words and proper names

## Design

This is opt-in integration: theories that don't need dialogue features
continue to use plain HPSG signs. Theories that need the Ginzburg 2012
architecture import this module.
-/

namespace Discourse.Gameboard.Grammar

open Discourse.Gameboard
open HPSG

-- ════════════════════════════════════════════════════
-- § 1. DialogueSign
-- ════════════════════════════════════════════════════

/-- An HPSG sign extended with dialogue features.

[ginzburg-2012] Ch. 5 §5.2 (Sign schema, p. 122 ex. 12) introduces
**dgb-params** and **quest-dom** as dialogue-relevant features on Sign:
- `dgbParams`: contextual parameters that must be resolved for grounding
- `questDom`: the question domain — what question the sign introduces

The third field, **q-params** (parameters contributed by interrogative
elements like wh-words), is added in Ch. 8 §8.5.1 (ex. 101 p. 325, ex.
103 p. 326, ex. 104 p. 326) — Ginzburg's footnote on p. 122 explicitly
notes "the field q-params introduced in section 8.5 of Chapter 8". We
include it here in the canonical form for substrate convenience.

These correspond to DGB-PARAMS, Q-PARAMS, and QUEST-DOM in the book.

The `Cont` parameter is the content type — `String` for surface form,
or richer typed values (`BCheckableAustinian S`, etc.) for TTR-typed
grammars. -/
structure DialogueSign (Cont : Type) where
  /-- Phonological form -/
  phon : String
  /-- Part of speech (UD-based, matching HPSG.Synsem.cat) -/
  pos : UD.UPOS
  /-- Head features from HPSG -/
  head : HeadFeatures := {}
  /-- Semantic content -/
  cont : Cont
  /-- DGB-PARAMS: contextual parameters requiring grounding.
      Non-empty for referential NPs ("Bo"), demonstratives, etc. -/
  dgbParams : CParamSet := []
  /-- Q-PARAMS: parameters contributed by interrogative elements.
      Non-empty for wh-words ("who", "what"). -/
  qParams : CParamSet := []
  /-- QUEST-DOM: the question this sign introduces (if interrogative). -/
  questDom : Option String := none

-- ════════════════════════════════════════════════════
-- § 2. Conversions
-- ════════════════════════════════════════════════════

/-- Project a DialogueSign to its HPSG Synsem (dropping dialogue features). -/
def DialogueSign.toSynsem {Cont : Type} (ds : DialogueSign Cont) : Synsem where
  cat := ds.pos
  head := ds.head

/-- Convert a DialogueSign to a LocProp for the KOS DGB.
DGB-PARAMS become `cparams` (block grounding until resolved);
Q-PARAMS become `qcparams` (travel with the sign, do not block grounding,
but remain available for fragment-reprise queries per
[ginzburg-2012] §8.5.1, [purver-ginzburg-2004]). -/
def DialogueSign.toLocProp {Cont : Type} (ds : DialogueSign Cont) :
    LocProp Cont where
  phon := ds.phon
  cat := toString ds.pos
  cont := ds.cont
  cparams := ds.dgbParams
  qcparams := ds.qParams

/-- Conversion preserves phonological form. -/
theorem toLocProp_preserves_phon {Cont : Type} (ds : DialogueSign Cont) :
    ds.toLocProp.phon = ds.phon := rfl

/-- Conversion preserves content. -/
theorem toLocProp_preserves_cont {Cont : Type} (ds : DialogueSign Cont) :
    ds.toLocProp.cont = ds.cont := rfl

/-- Conversion routes DGB-PARAMS to `cparams` (the resolution channel). -/
theorem toLocProp_dgb_to_cparams {Cont : Type} (ds : DialogueSign Cont) :
    ds.toLocProp.cparams = ds.dgbParams := rfl

/-- Conversion routes Q-PARAMS to `qcparams` (the existential-witness
channel) — the structural prerequisite for the Reprise Content Hypothesis. -/
theorem toLocProp_q_to_qcparams {Cont : Type} (ds : DialogueSign Cont) :
    ds.toLocProp.qcparams = ds.qParams := rfl

-- ════════════════════════════════════════════════════
-- § 3. Example Entries (String-typed lexicon)
-- ════════════════════════════════════════════════════

/-- "who" — a wh-word with Q-PARAMS.
[ginzburg-2012] Ch. 5: wh-words contribute Q-PARAMS that
project to the QUEST-DOM of the clause. -/
def who : DialogueSign String where
  phon := "who"
  pos := .PRON
  cont := "who(x)"
  qParams := [{ index := "x", restriction := "individual" }]
  questDom := some "?x.P(x)"

/-- "Jo" — a proper name with DGB-PARAMS.
[ginzburg-2012] Ch. 6: referential NPs introduce DGB-PARAMS
that must be resolved (grounded) for the utterance to be integrated. -/
def jo : DialogueSign String where
  phon := "Jo"
  pos := .PROPN
  cont := "jo"
  dgbParams := [{ index := "jo_ref", restriction := "individual" }]

/-- "left" — an intransitive verb (no dialogue params). -/
def left : DialogueSign String where
  phon := "left"
  pos := .VERB
  head := { vform := .finite }
  cont := "leave(x)"

-- ════════════════════════════════════════════════════
-- § 4. Verification
-- ════════════════════════════════════════════════════

/-- "Jo" needs grounding: it has non-empty DGB-PARAMS. -/
theorem jo_needs_grounding : ¬ jo.toLocProp.isFullyResolved := by decide

/-- "who" has Q-PARAMS (it's interrogative). -/
theorem who_has_qparams : who.qParams ≠ [] := by
  simp [who]

/-- "who" doesn't need grounding (Q-PARAMS ≠ DGB-PARAMS). -/
theorem who_no_grounding_needed : who.toLocProp.isFullyResolved := by decide

/-- "left" has no dialogue features. -/
theorem left_plain : left.dgbParams = [] ∧ left.qParams = [] := ⟨rfl, rfl⟩

end Discourse.Gameboard.Grammar
