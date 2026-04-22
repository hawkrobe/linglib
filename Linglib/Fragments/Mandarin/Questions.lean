import Linglib.Phenomena.Questions.Typology
import Linglib.Core.Lexical.ExpressiveModifier

/-!
# Mandarin Wh-Question Formation
@cite{chou-2012} @cite{huang-1982a} @cite{chan-shen-2026}

Mandarin is a wh-in-situ language (WALS 93A: `notInitialInterrogativePhrase`).
Content questions are formed with the wh-phrase remaining in its base-generated
position, interpreted via unselective binding by a Q operator in C
(@cite{huang-1982a}).

## ANDL modifier: *到底 daodi*

Mandarin *daodi* ('on earth') is the functional equivalent of English
*the-hell* — both are aggressively non-D-linked (ANDL) modifiers
(@cite{chou-2012}).

The cross-linguistic difference (@cite{chan-shen-2026}, isolated as the
single typological parameter):

- *The-hell* (English/Singlish) is **parasitic**: must adjoin to the
  wh-phrase and rides along with wh-movement. In a wh-in-situ language
  (or strategy), the wh-phrase doesn't move, so *the-hell* is stranded.
- *Daodi* (Mandarin) is **independent**: can undergo covert movement to
  Spec-CP on its own, so it is licensed even when the wh-phrase stays
  in situ.

This file is theory-neutral: the Minimalist POV-feature analysis lives
in `Theories/Syntax/Minimalism/ANDL.lean`; this file only carries
the lexical entries with their typological parameters.
-/

namespace Fragments.Mandarin.Questions

open Phenomena.Questions.Typology (WhInterpMechanism WhMovementStrategy)
open Core.Lexical.ExpressiveModifier
  (ExpressiveWhModifier ANDLMovementType ANDLHostPosition)

-- ============================================================================
-- Mandarin wh-interpretation mechanism
-- ============================================================================

/-- Mandarin uses unselective binding for wh-interpretation.
    The Q operator in C binds the wh-variable in situ — no overt or
    covert wh-movement of the wh-phrase itself occurs. -/
def whMechanism : WhInterpMechanism := .unselectiveBinding

-- ============================================================================
-- ANDL modifier: 到底 daodi
-- ============================================================================

/-- 到底 *daodi* ('on earth') — Mandarin ANDL modifier.

    Theory-neutral lexical entry: phonological form, gloss, and
    typological parameters only. The POV-feature analysis (shared with
    *the-hell*) lives in `Theories/Syntax/Minimalism/ANDL.lean`;
    no Minimalist commitments are baked in here. -/
def daodi : ExpressiveWhModifier :=
  { form := "到底"
  , gloss := "dàodǐ 'on earth' (ANDL intensifier)"
  , movementType := .independent
  , hostPosition := .matrixScope }

-- ============================================================================
-- Verification theorems (theory-neutral)
-- ============================================================================

/-- *Daodi* uses independent movement (not parasitic). -/
theorem daodi_is_independent :
    daodi.movementType = .independent := rfl

/-- Mandarin wh-in-situ does not involve movement to Spec-CP. -/
theorem mandarin_wh_no_specCP :
    ¬ whMechanism.ReachesSpecCP := id

/-- Mandarin wh-in-situ is island-insensitive (binding, not movement). -/
theorem mandarin_wh_island_free :
    ¬ whMechanism.IslandSensitive := id

end Fragments.Mandarin.Questions
