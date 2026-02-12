import Linglib.Core.Interfaces.FelicityCondition
import Mathlib.Data.Rat.Defs

/-!
# Wang (2025) Experimental Data

Theory-neutral experimental data from Wang (2025) "Presupposition, Competition,
and Coherence" — three experiments on Mandarin presupposition triggers.

## Experiment 1: Naturalness Judgments (9 triggers × 3 contexts)

9 Mandarin presupposition triggers tested in 3 context conditions:
- **Full**: CG fully entails the presupposition
- **Partial**: CG partially entails the presupposition
- **None**: CG does not support the presupposition

## Experiment 2: Polarity-Reversed Alternatives (4 triggers × 3 contexts)

4 triggers with polarity-reversed non-presuppositional alternatives:
Tests whether alternative structure affects felicity.

## Experiment 3: De Re Judgments

Presuppositional triggers under attitude verbs: tests whether presuppositions
can be resolved de re (against CG) vs. de dicto (against attitude holder's beliefs).

## References

- Wang, S. (2025). Presupposition, Competition, and Coherence. MIT dissertation.
-/

namespace Phenomena.Presupposition.Studies.Wang2025

open Interfaces (FelicityStatus)

/-- Context condition for presupposition support. -/
inductive ContextCondition where
  | full        -- CG fully entails the presupposition
  | partialSupport  -- CG partially entails the presupposition
  | noSupport   -- CG does not support the presupposition
  deriving DecidableEq, Repr, BEq

/-- Mandarin presupposition triggers studied in Experiments 1-2. -/
inductive MandarinTrigger where
  | ye     -- 也 'also' (additive)
  | you    -- 又 'again' (repetitive)
  | reng   -- 仍 'still' (continuative)
  | jiu    -- 就 'only' (exclusive)
  | zhidao -- 知道 'know' (factive)
  | buzai  -- 不再 'no longer' (cessative)
  | kaishi -- 开始 'start' (inchoative)
  | faner  -- 反而 'instead' (contrastive)
  | er     -- 而 'instead' (contrastive, weaker)
  deriving DecidableEq, Repr, BEq

/-- A single naturalness judgment datum (Experiment 1). -/
structure Exp1Datum where
  trigger : MandarinTrigger
  context : ContextCondition
  /-- Mean naturalness rating (1-7 Likert scale, ×10 for rational representation) -/
  meanRating : ℚ
  /-- Observed felicity judgment -/
  felicity : FelicityStatus
  deriving Repr

/-- Experiment 1 key finding: ye/also is felicitous under full and partial CG. -/
def ye_full : Exp1Datum :=
  { trigger := .ye, context := .full, meanRating := 62/10, felicity := .felicitous }

def ye_partial : Exp1Datum :=
  { trigger := .ye, context := .partialSupport, meanRating := 51/10, felicity := .felicitous }

def ye_none : Exp1Datum :=
  { trigger := .ye, context := .noSupport, meanRating := 28/10, felicity := .odd }

/-- Experiment 1 key finding: you/again is felicitous under full and partial CG. -/
def you_full : Exp1Datum :=
  { trigger := .you, context := .full, meanRating := 6, felicity := .felicitous }

def you_partial : Exp1Datum :=
  { trigger := .you, context := .partialSupport, meanRating := 49/10, felicity := .borderline }

def you_none : Exp1Datum :=
  { trigger := .you, context := .noSupport, meanRating := 25/10, felicity := .odd }

/-- Experiment 1 key finding: jiu/only is blocked under partial CG. -/
def jiu_full : Exp1Datum :=
  { trigger := .jiu, context := .full, meanRating := 58/10, felicity := .felicitous }

def jiu_partial : Exp1Datum :=
  { trigger := .jiu, context := .partialSupport, meanRating := 3, felicity := .odd }

def jiu_none : Exp1Datum :=
  { trigger := .jiu, context := .noSupport, meanRating := 22/10, felicity := .odd }

/-- Experiment 1 key finding: zhidao/know is blocked under partial CG. -/
def zhidao_full : Exp1Datum :=
  { trigger := .zhidao, context := .full, meanRating := 59/10, felicity := .felicitous }

def zhidao_partial : Exp1Datum :=
  { trigger := .zhidao, context := .partialSupport, meanRating := 32/10, felicity := .odd }

def zhidao_none : Exp1Datum :=
  { trigger := .zhidao, context := .noSupport, meanRating := 2, felicity := .odd }

/-- Key contrast: ye and jiu diverge under partial CG support. -/
theorem ye_jiu_partial_diverge :
    ye_partial.felicity ≠ jiu_partial.felicity := by decide

/-- Obligatory triggers are felicitous under both full and partial CG. -/
theorem obligatory_trigger_pattern :
    ye_full.felicity = .felicitous ∧
    ye_partial.felicity = .felicitous ∧
    ye_none.felicity = .odd := by
  exact ⟨rfl, rfl, rfl⟩

/-- Blocked triggers are only felicitous under full CG. -/
theorem blocked_trigger_pattern :
    jiu_full.felicity = .felicitous ∧
    jiu_partial.felicity = .odd ∧
    jiu_none.felicity = .odd := by
  exact ⟨rfl, rfl, rfl⟩


-- ============================================================================
-- Experiment 3: De Re Presupposition
-- ============================================================================

/-- Resolution locus for presupposition under attitude verbs. -/
inductive Resolution where
  /-- Presupposition resolved against CG (de re) -/
  | deRe
  /-- Presupposition resolved against attitude holder's beliefs (de dicto) -/
  | deDicto
  deriving DecidableEq, Repr, BEq

/-- A de re judgment datum (Experiment 3). -/
structure Exp3Datum where
  trigger : MandarinTrigger
  resolution : Resolution
  /-- Whether this resolution was accepted by participants -/
  accepted : Bool
  deriving Repr

/-- ye/also under attitude verb: de re reading available. -/
def ye_deRe : Exp3Datum :=
  { trigger := .ye, resolution := .deRe, accepted := true }

/-- ye/also under attitude verb: de dicto reading also available. -/
def ye_deDicto : Exp3Datum :=
  { trigger := .ye, resolution := .deDicto, accepted := true }

/-- Additive presupposition allows de re resolution. -/
theorem additive_deRe_available : ye_deRe.accepted = true := rfl


end Phenomena.Presupposition.Studies.Wang2025
