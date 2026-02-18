import Linglib.Core.Empirical

/-!
# Bale et al. (2025) — Competence by Default @cite{bale-etal-2025}

Bale, A. C., Noguchi, H., Rolland, M. & Barner, D. (2025). Competence by
default: Do listeners assume that speakers are knowledgeable when computing
conversational inferences? *Journal of Semantics* 42(1–2): 39–55.

## Core Contribution

Tests whether the competence assumption in scalar implicature derivation
(step 5 of Soames 1982 / Horn 1989 / Sauerland 2004) is a cognitive default
or must be contextually licensed. The 5-step derivation:

1. Speaker said φ (e.g., "some of the marbles are red")
2. There exists a stronger alternative ψ (e.g., "all of the marbles are red")
3. Speaker didn't say ψ (Quantity)
4. Therefore ¬Bel_S(ψ) — weak implicature
5. With competence (Bel_S(ψ) ∨ Bel_S(¬ψ)), derive Bel_S(¬ψ) — strong SI

Step 5 depends on the **competence assumption**: the listener assumes the
speaker knows whether ψ. Three hypotheses about when this is applied:

- **Competence-by-default** (Geurts 2010): competence is assumed by default;
  cancellation requires effortful integration of contextual evidence
- **SSI-by-default** (Levinson 2000): the entire SSI is a default; load
  disrupts SI computation itself
- **Contextual licensing** (Soames 1982, Horn 1989, Zimmermann 2000):
  competence must be contextually justified; it is not a default

## Experimental Design

Dual-task paradigm with 2 × 2 design:
- **Between-subjects**: cognitive load (load vs. no load), n = 30 per group
- **Within-subjects**: speaker knowledge (full knowledge = FK vs. partial
  knowledge = PK)
- **Trials**: FK+All (control), FK+Some, PK+Some
- **Response**: 3-way forced choice ("Yes" / "No" / "I don't know")
- **Key DV**: proportion of "No" responses on *some* trials (= SSI computed)

## Key Finding

GLMM reveals a significant **Knowledge × Load interaction** (β = 2.62,
SE = 0.86, χ²(1) = 11.3, P < .001): load increases SSI rate in the PK
(ignorant) condition (10% → 23.3%) while non-significantly decreasing it
in the FK (competent) condition (65.6% → 56.7%). This crossover supports
competence-by-default: load impairs effortful cancellation of the default
competence assumption.
-/

namespace Phenomena.ScalarImplicatures.Studies.BaleEtAl2025

open Phenomena


/-! ## Measure Specification -/

/-- Three-way forced choice: "Yes" (literal, no SI), "No" (SSI computed,
    speaker meant "some but not all"), "I don't know" (uncertain).
    Key DV is proportion of "No" responses. -/
def measure : MeasureSpec :=
  { scale := .proportion
  , task := .forcedChoice
  , unit := "proportion 'No' responses (SSI computed)" }

/-- Total participants. -/
def nTotal : Nat := 60


/-! ## Experimental Conditions -/

/-- Speaker's epistemic state regarding the stronger alternative ψ.

    Manipulated via cover story: speaker either looked in all sections of
    a box (full knowledge) or only some sections (partial knowledge). -/
inductive SpeakerKnowledge where
  /-- Full Knowledge: speaker inspected all sections, knows whether ψ -/
  | fullKnowledge
  /-- Partial Knowledge: speaker inspected only some sections, ignorant of ψ -/
  | partialKnowledge
  deriving DecidableEq, BEq, Repr

/-- Cognitive load manipulation (between-subjects). -/
inductive LoadCondition where
  /-- No concurrent task -/
  | noLoad
  /-- Dual-task: memorize a dot pattern while processing utterance -/
  | load
  deriving DecidableEq, BEq, Repr

/-- A full experimental condition: speaker knowledge × cognitive load. -/
structure ExperimentalCondition where
  knowledge : SpeakerKnowledge
  load : LoadCondition
  deriving DecidableEq, BEq, Repr


/-! ## Observed SSI Rates

    Rates are stored in tenths of a percent to preserve the one-decimal-place
    precision reported in the paper (e.g., 233 = 23.3%). -/

/-- Observed strong scalar implicature rate for one condition. -/
structure SSIRate where
  /-- The experimental condition -/
  condition : ExperimentalCondition
  /-- SSI rate in tenths of a percent (e.g., 233 = 23.3%) -/
  rateTenths : Nat
  /-- Number of participants in this load group -/
  n : Nat
  deriving Repr

/-- FK + No Load: 65.6% SSI rate (baseline for competent speaker). -/
def fk_noLoad : SSIRate :=
  { condition := ⟨.fullKnowledge, .noLoad⟩
  , rateTenths := 656
  , n := 30 }

/-- FK + Load: 56.7% SSI rate (non-significant decrease, P = .22). -/
def fk_load : SSIRate :=
  { condition := ⟨.fullKnowledge, .load⟩
  , rateTenths := 567
  , n := 30 }

/-- PK + No Load: 10.0% SSI rate (competence properly canceled). -/
def pk_noLoad : SSIRate :=
  { condition := ⟨.partialKnowledge, .noLoad⟩
  , rateTenths := 100
  , n := 30 }

/-- PK + Load: 23.3% SSI rate — the key finding.
    Load impairs cancellation of the default competence assumption,
    yielding more SSIs despite speaker ignorance. -/
def pk_load : SSIRate :=
  { condition := ⟨.partialKnowledge, .load⟩
  , rateTenths := 233
  , n := 30 }

/-- All four conditions. -/
def allConditions : List SSIRate :=
  [fk_noLoad, fk_load, pk_noLoad, pk_load]


/-! ## Interaction Test

    The key statistical test: Knowledge × Load interaction in a GLMM. -/

/-- Result of the Knowledge × Load interaction test (GLMM, logistic). -/
structure InteractionTest where
  /-- Interaction coefficient -/
  beta : Float
  /-- Standard error -/
  se : Float
  /-- Chi-squared statistic (likelihood ratio, 1 df) -/
  chiSq : Float
  /-- p-value -/
  p : Float
  deriving Repr

/-- The observed interaction: β = 2.62, χ²(1) = 11.3, P < .001. -/
def knowledgeLoadInteraction : InteractionTest :=
  { beta := 2.62
  , se := 0.86
  , chiSq := 11.3
  , p := 0.001 }

/-- The interaction is significant (P < .05). -/
theorem interaction_significant :
    knowledgeLoadInteraction.p < 0.05 := by native_decide


/-! ## Load Effects by Condition -/

/-- Signed load effect in tenths of a percent.
    Positive = load increases SSI rate; negative = load decreases. -/
def loadEffect (k : SpeakerKnowledge) : Int :=
  match k with
  | .fullKnowledge    => (fk_load.rateTenths : Int) - fk_noLoad.rateTenths
  | .partialKnowledge => (pk_load.rateTenths : Int) - pk_noLoad.rateTenths

/-- The crossover interaction: load increases SSIs for PK speakers
    but decreases SSIs for FK speakers. -/
theorem crossover_interaction :
    loadEffect .partialKnowledge > 0 ∧ loadEffect .fullKnowledge < 0 := by
  simp only [loadEffect, fk_load, fk_noLoad, pk_load, pk_noLoad]
  omega

/-- Load increases SSI rate in PK condition by 13.3 percentage points. -/
theorem pk_load_increase :
    pk_load.rateTenths > pk_noLoad.rateTenths := by
  simp only [pk_load, pk_noLoad]
  omega

/-- The interaction magnitude: the difference in load effects across
    knowledge conditions is positive (PK effect > FK effect). -/
theorem interaction_magnitude :
    loadEffect .partialKnowledge - loadEffect .fullKnowledge > 0 := by
  simp only [loadEffect, fk_load, fk_noLoad, pk_load, pk_noLoad]
  omega


/-! ## Competing Hypotheses -/

/-- Three hypotheses about the status of the competence assumption. -/
inductive CompetenceHypothesis where
  /-- Competence is assumed by default; cancellation requires effortful
      processing. Load impairs cancellation → more SSIs when speaker is
      actually ignorant (Geurts 2010). -/
  | competenceByDefault
  /-- The entire SI derivation is a default; load disrupts SI computation
      itself. Predicts load decreases SSI rates (Levinson 2000). -/
  | ssiByDefault
  /-- Competence must be contextually licensed; it is not a default.
      Load should not increase SSI rates for ignorant speakers — competence
      was never assumed, so there is nothing to fail to cancel
      (Soames 1982, Horn 1989, Zimmermann 2000). -/
  | contextualLicensing
  deriving DecidableEq, BEq, Repr

/-- Whether a hypothesis predicts a positive Knowledge × Load interaction
    (i.e., load increases SSI more — or decreases it less — in PK than FK).

    This is the key discriminating prediction: only competence-by-default
    predicts a positive interaction. -/
def predictsPositiveInteraction : CompetenceHypothesis → Bool
  | .competenceByDefault  => true   -- load prevents canceling default competence
  | .ssiByDefault         => false  -- load disrupts SI uniformly
  | .contextualLicensing  => false  -- no default to fail to cancel

/-- Competence-by-default is the only hypothesis predicting a positive
    interaction, matching the observed data. -/
theorem only_competenceByDefault_predicts_interaction :
    [CompetenceHypothesis.competenceByDefault, .ssiByDefault, .contextualLicensing].filter
      predictsPositiveInteraction
    = [.competenceByDefault] := by native_decide


end Phenomena.ScalarImplicatures.Studies.BaleEtAl2025
