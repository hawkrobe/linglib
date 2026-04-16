import Linglib.Fragments.Singlish.Questions
import Linglib.Theories.Syntax.Minimalism.Core.Features

/-!
# Chan & Shen (2026): Conditions on *wh-the-hell* licensing
@cite{chan-shen-2026}

*Linguistic Inquiry*. Advance publication.
https://doi.org/10.1162/LING.a.562

## Empirical Contribution

Acceptability judgment experiment (N=32 Singlish speakers, 2×2 factorial)
establishing that in Singlish single wh-questions:

- In-situ *wh-the-hell* is **unacceptable** (superadditive interaction,
  WhType × Strategy p < 0.001; DD = 1.15)
- Partial-movement *wh-the-hell* is **acceptable** (additive costs only,
  no interaction p = 0.882; DD = -0.02)

## Theoretical Contribution

Two-component analysis combining:

1. **POV licensing** (@cite{chou-2012}): *the-hell* bears an unvalued
   point-of-view feature [*ud*] that must be checked in a Spec-head
   relation with a POV operator in matrix CP. This ascribes the negative
   attitude of *the-hell* to the speaker of the utterance.

2. **Parasitic movement** (@cite{merchant-2002}): *the-hell* is a modifier
   adjoined to the wh-head. It cannot move independently — its movement
   to Spec-CP is parasitic on the wh-phrase's movement.

The combination predicts: *the-hell* is licensed iff the wh-phrase
reaches matrix Spec-CP (overtly or covertly). Full and partial movement
satisfy this; unselective binding (in-situ) does not.

## Comparison with Alternative Accounts

- **@cite{den-dikken-giannakidou-2002}** (intervention): correctly predicts
  full/partial OK, but wrongly predicts in-situ OK in single wh-questions
  (no intervener between Q and *the-hell*).
- **@cite{vu-lohiniva-2020}** (AttP): correctly predicts full OK and
  in-situ bad, but wrongly predicts partial *bad* (cannot generate the
  correct word order for partially moved *wh-the-hell*).
-/

namespace ChanShen2026

open Fragments.Singlish.Questions (WhStrategy fullMovement partialMovement whInSitu)
open Phenomena.Questions.Typology (WhInterpMechanism)
open ShenHuang2026 (WhDependencyType constraintsForDependencyType)
open Minimalism (FeatureVal GramFeature)

-- ============================================================================
-- § 1: The-hell licensing — derived from mechanism + POV feature
-- ============================================================================

/-- *The-hell* bears an unvalued POV feature [*ud*] that must be checked
    in matrix Spec-CP. The feature is valued [+d] by a POV operator
    merged in the matrix C domain. @cite{chou-2012} -/
def theHellFeature : GramFeature := .unvalued (.pov true)

/-- *The-hell* is licensed iff its adjunction host (the wh-phrase) reaches
    matrix Spec-CP. This is **derived** from the wh-phrase's interpretation
    mechanism, not stipulated as a stored property:

    - Movement-based mechanisms (overt or covert) bring the wh-phrase to
      Spec-CP, carrying the adjoined *the-hell* along.
    - Unselective binding leaves the wh-phrase in situ — no movement
      occurs, so *the-hell* cannot reach Spec-CP to check [*ud*].

    This function is `WhInterpMechanism.reachesSpecCP` by another name:
    the licensing condition IS the reachability condition. -/
def theHellLicensed (s : WhStrategy) : Bool :=
  s.mechanism.reachesSpecCP

-- ============================================================================
-- § 2: Empirical data — 2×2 factorial experiments
-- ============================================================================

/-- Experimental condition in a 2×2 factorial design. -/
structure Condition where
  label : String
  /-- Wh-type factor: bare wh or wh-the-hell. -/
  hasTheHell : Bool
  /-- Strategy factor: full movement (Long) vs test strategy. -/
  strategy : WhStrategy
  /-- Example sentence (Singlish). -/
  sentence : String
  deriving Repr

/-- In-situ comparison conditions (Table 1–2): -/
def whLong : Condition :=
  { label := "Wh-Long", hasTheHell := false, strategy := fullMovement
  , sentence := "What you think Natalie is baking at 3am ah?" }

def whHellLong : Condition :=
  { label := "WhHell-Long", hasTheHell := true, strategy := fullMovement
  , sentence := "What the hell you think Natalie is baking at 3am ah?" }

def whSitu : Condition :=
  { label := "Wh-Situ", hasTheHell := false, strategy := whInSitu
  , sentence := "You think Natalie is baking what at 3am ah?" }

def whHellSitu : Condition :=
  { label := "WhHell-Situ", hasTheHell := true, strategy := whInSitu
  , sentence := "You think Natalie is baking what the hell at 3am ah?" }

/-- Partial movement comparison conditions (Table 3–4): -/
def whPartial : Condition :=
  { label := "Wh-Partial", hasTheHell := false, strategy := partialMovement
  , sentence := "You think what Natalie is baking at 3am ah?" }

def whHellPartial : Condition :=
  { label := "WhHell-Partial", hasTheHell := true, strategy := partialMovement
  , sentence := "You think what the hell Natalie is baking at 3am ah?" }

/-- Differences-in-differences (DD) scores from the experiment.
    DD > 0 ↔ superadditive interaction ↔ extra penalty for *the-hell*. -/
structure DDResult where
  comparison : String
  dd : Float
  interactionSignificant : Bool
  deriving Repr

def insituDD : DDResult :=
  { comparison := "in-situ vs full movement"
  , dd := 1.15, interactionSignificant := true }

def partialDD : DDResult :=
  { comparison := "partial vs full movement"
  , dd := -0.02, interactionSignificant := false }

-- ============================================================================
-- § 3: Predictions — derived from mechanism
-- ============================================================================

/-- Full wh-movement licenses *the-hell*: overtMovement.reachesSpecCP = true. -/
theorem fullMovement_licenses_theHell :
    theHellLicensed fullMovement = true := rfl

/-- Partial wh-movement licenses *the-hell*: covertMovement.reachesSpecCP = true. -/
theorem partialMovement_licenses_theHell :
    theHellLicensed partialMovement = true := rfl

/-- Wh-in-situ blocks *the-hell*: unselectiveBinding.reachesSpecCP = false. -/
theorem inSitu_blocks_theHell :
    theHellLicensed whInSitu = false := rfl

/-- Predictions match the experiment. -/
theorem predictions_match_experiment :
    theHellLicensed fullMovement = true ∧
    theHellLicensed partialMovement = true ∧
    theHellLicensed whInSitu = false ∧
    insituDD.interactionSignificant = true ∧
    partialDD.interactionSignificant = false := ⟨rfl, rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- § 4: Alternative accounts — predictions DERIVED from structural properties
-- ============================================================================

/-! ### Intervention account (@cite{den-dikken-giannakidou-2002})

The intervention account treats *the-hell* as a polarity item (PI) licensed
by Q. Licensing fails when a higher wh-phrase intervenes between Q and
*the-hell*. The key structural property: is there an intervener?

In single wh-questions (Singlish in-situ), there is NO intervening
wh-phrase. So the intervention account predicts licensing — contradicting
the experimental finding. -/

/-- Is there a wh-phrase intervening between Q (in C) and *the-hell*?
    In single wh-questions: only one wh-phrase, so no intervener. -/
def hasIntervener (numWhPhrases : Nat) : Bool := numWhPhrases > 1

/-- Intervention account prediction: licensed iff no intervener. -/
def interventionPredicts (numWhPhrases : Nat) : Bool :=
  !hasIntervener numWhPhrases

/-- In single wh-questions, the intervention account wrongly predicts OK. -/
theorem intervention_wrong_for_single_insitu :
    interventionPredicts 1 = true ∧ theHellLicensed whInSitu = false :=
  ⟨rfl, rfl⟩

/-- The intervention account correctly handles multiple wh-questions:
    "* Who loves what the hell?" has an intervener (*who*). -/
theorem intervention_correct_for_multiple :
    interventionPredicts 2 = false := rfl

/-! ### AttP account (@cite{vu-lohiniva-2020})

*The-hell* is base-generated in Spec-AttP (Attitude Phrase) in the matrix
IP domain. The nearest wh-phrase must move to Spec-AttP to check [+wh].
This requires the wh-phrase and *the-hell* to be in the SAME clause's
IP domain. -/

/-- Are *the-hell* (in matrix Spec-AttP) and the wh-phrase in the same
    clause's IP domain? For partial movement, the wh-phrase is in the
    embedded clause — not the same domain as matrix AttP. -/
def attPSameDomain (whInMatrixDomain : Bool) : Bool := whInMatrixDomain

/-- AttP account prediction: licensed iff in same domain. -/
def attPPredicts (whInMatrixDomain : Bool) : Bool :=
  attPSameDomain whInMatrixDomain

/-- Full movement: wh-phrase ends up in matrix domain. -/
theorem attp_correct_full : attPPredicts true = true := rfl

/-- Partial movement: wh-phrase is in embedded Spec-CP, NOT matrix domain.
    AttP account wrongly predicts unacceptable. -/
theorem attp_wrong_partial :
    attPPredicts false = false ∧ theHellLicensed partialMovement = true :=
  ⟨rfl, rfl⟩

-- ============================================================================
-- § 5: Summary — Table 5 comparison (derived from account functions)
-- ============================================================================

/-- Predictions of three accounts across all strategies (Table 5).
    The paper tests both object and subject in-situ (§3.3, exx. 3c, 22b);
    all accounts make identical predictions for both, so a single `insituOk`
    suffices. -/
structure AccountPredictions where
  name : String
  fullOk : Bool
  partialOk : Bool
  insituOk : Bool
  deriving Repr, DecidableEq

def empiricalPattern : AccountPredictions :=
  { name := "Empirical", fullOk := true, partialOk := true
  , insituOk := false }

/-- @cite{den-dikken-giannakidou-2002}: predictions derived from
    `interventionPredicts`. Single wh = 1, so all non-multiple cases OK. -/
def denDikkenGiannakidou : AccountPredictions :=
  { name := "Den Dikken & Giannakidou 2002"
  , fullOk := interventionPredicts 1    -- true (no intervener)
  , partialOk := interventionPredicts 1 -- true (no intervener)
  , insituOk := interventionPredicts 1 } -- true: WRONG

/-- @cite{vu-lohiniva-2020}: predictions derived from `attPPredicts`.
    Full: wh in matrix (true). Partial: wh in embedded (false).
    In-situ: wh in embedded, no movement (false). -/
def vuLohiniva : AccountPredictions :=
  { name := "Vu & Lohiniva 2020"
  , fullOk := attPPredicts true         -- true
  , partialOk := attPPredicts false     -- false: WRONG
  , insituOk := attPPredicts false }    -- false

/-- @cite{chan-shen-2026}: predictions derived from `theHellLicensed`,
    which is itself derived from `WhInterpMechanism.reachesSpecCP`. -/
def negativeAttitudeAscription : AccountPredictions :=
  { name := "Chan & Shen 2026"
  , fullOk := theHellLicensed fullMovement
  , partialOk := theHellLicensed partialMovement
  , insituOk := theHellLicensed whInSitu }

/-- Whether an account's predictions match the empirical pattern. -/
def AccountPredictions.matchesPattern (a b : AccountPredictions) : Bool :=
  a.fullOk == b.fullOk && a.partialOk == b.partialOk &&
  a.insituOk == b.insituOk

/-- Only the negative attitude ascription account matches (Table 5). -/
theorem only_pov_account_matches :
    negativeAttitudeAscription.matchesPattern empiricalPattern = true ∧
    denDikkenGiannakidou.matchesPattern empiricalPattern = false ∧
    vuLohiniva.matchesPattern empiricalPattern = false := ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- § 5b: Per-condition predictions — data ↔ theory
-- ============================================================================

/-- Each *the-hell* condition's acceptability is predicted by its strategy's
    mechanism. These theorems break if a condition's strategy changes or
    if `reachesSpecCP` is redefined — they tie experimental data to theory. -/
theorem whHellLong_predicted_ok :
    whHellLong.hasTheHell = true ∧ theHellLicensed whHellLong.strategy = true :=
  ⟨rfl, rfl⟩

theorem whHellSitu_predicted_bad :
    whHellSitu.hasTheHell = true ∧ theHellLicensed whHellSitu.strategy = false :=
  ⟨rfl, rfl⟩

theorem whHellPartial_predicted_ok :
    whHellPartial.hasTheHell = true ∧ theHellLicensed whHellPartial.strategy = true :=
  ⟨rfl, rfl⟩

-- ============================================================================
-- § 6: Cross-study bridge — island sensitivity
-- ============================================================================

/-- Singlish wh-in-situ uses binding (not movement), just like Mandarin
    wh-in-situ in @cite{shen-huang-2026}. Therefore only the Specificity
    Condition applies — the PIC is inapplicable. This is why Singlish
    wh-in-situ is island-insensitive (@cite{sato-ngui-2017}: 11b).

    The connection: `constraintsForDependencyType .binding = [.semantic]`
    (no syntactic/PIC constraint). -/
theorem insitu_binding_no_pic :
    constraintsForDependencyType
      (WhInterpMechanism.unselectiveBinding.toDependencyType) =
    [IslandSource.semantic] := rfl

-- ============================================================================
-- § 7: Bridge — POV ↔ PerspectiveP
-- ============================================================================

/-- The POV operator in matrix C carries a valued [+d] feature. Agree
    matches it with *the-hell*'s unvalued [*ud*] via `featuresMatch`. -/
def povOperatorFeature : GramFeature := .valued (.pov true)

/-- *The-hell*'s unvalued POV feature matches the POV operator's valued
    feature — the Agree prerequisite for feature checking. -/
theorem pov_features_match :
    Minimalism.featuresMatch theHellFeature povOperatorFeature = true := rfl

/-- *The-hell*'s POV feature is unvalued (a probe, not a goal). -/
theorem theHell_pov_is_unvalued :
    theHellFeature.isUnvalued = true := rfl

/-! The syntactic POV feature on *the-hell* is the feature-checking reflex
    of the semantic PerspectiveP layer (@cite{dayal-2025}). Both encode
    the requirement that a perspectival center (the speaker, in direct
    questions) must be identified.

    - **Syntactic**: [*ud*] on *the-hell* checked by POV-op in matrix C
    - **Semantic**: PerspP introduces PRO with ◇¬know(speaker, Ans(Q))

    *The-hell*'s negative attitude (speaker finds every possible answer
    improbable, @cite{rawlins-2008}) strengthens PerspP's possible-ignorance
    presupposition. Checking [*ud*] in Spec-CP corresponds to entering
    PerspP's scope. -/

-- ============================================================================
-- § 8: Cross-linguistic — Mandarin *daodi*
-- ============================================================================

/-- Whether an ANDL modifier can undergo independent covert movement
    (not parasitic on wh-phrase movement). This is the single parameter
    distinguishing English/Singlish *the-hell* from Mandarin *daodi*
    (@cite{chou-2012}). -/
inductive ANDLMovementType where
  | parasitic    -- must adjoin to wh-phrase; cannot move independently
  | independent  -- can undergo independent covert movement to Spec-CP
  deriving DecidableEq, Repr

/-- English/Singlish *the-hell*: parasitic movement (must adjoin to wh). -/
def theHellMovement : ANDLMovementType := .parasitic

/-- Mandarin *daodi*: independent covert movement to Spec-CP. -/
def daodiMovement : ANDLMovementType := .independent

/-- *Daodi* can be licensed with wh-in-situ because it moves independently.
    *The-hell* cannot. Both share the same POV feature [*ud*]. -/
def andlLicensedInSitu (mvt : ANDLMovementType) : Bool :=
  match mvt with
  | .independent => true   -- *daodi* moves to Spec-CP on its own
  | .parasitic   => false  -- *the-hell* stranded in situ

theorem daodi_ok_insitu : andlLicensedInSitu daodiMovement = true := rfl
theorem theHell_bad_insitu : andlLicensedInSitu theHellMovement = false := rfl

end ChanShen2026
