import Linglib.Fragments.Singlish.Questions
import Linglib.Fragments.Mandarin.Questions
import Linglib.Theories.Syntax.Minimalism.Core.ANDL
import Linglib.Theories.Interfaces.SyntaxSemantics.LeftPeriphery
import Linglib.Paradigms.AcceptabilityJudgment
import Linglib.Phenomena.Islands.Studies.Ross1967

/-!
# Chan & Shen (2026): Conditions on *wh-the-hell* licensing
@cite{chan-shen-2026} @cite{pesetsky-1987} @cite{chou-2012}
@cite{merchant-2002} @cite{sato-ngui-2017} @cite{rawlins-2008}
@cite{martin-2020} @cite{ippolito-2024} @cite{huang-ochi-2004}
@cite{linebarger-1987} @cite{hoeksema-napoli-2008}

*Linguistic Inquiry*. Advance publication.
https://doi.org/10.1162/LING.a.562

## Empirical Contribution

Acceptability judgment experiment (N=32 Singlish speakers, two crossed
2×2 factorial designs sharing the Long baseline). Establishes that in
Singlish single wh-questions:

- **In-situ** *wh-the-hell* is unacceptable: superadditive interaction
  (WhType × Strategy p < 0.001; DD = 1.15)
- **Partial-movement** *wh-the-hell* is acceptable: additive costs only
  (no interaction p = 0.882; DD = -0.02)
- The same in-situ ban holds for **subject** wh-in-situ (paper §3.3
  ex 22b) — a separate prediction failure for the intervention account
  (paper §3.4.1, p. 23–24): no higher wh, no intervener, but still bad.

The original observation that in-situ *wh-the-hell* is bad goes back
to @cite{pesetsky-1987} (introducing "aggressively non-D-linked").

## Theoretical Contribution

Two-component analysis:

1. **POV licensing** (@cite{chou-2012}, building on @cite{huang-ochi-2004}):
   *the-hell* bears an unvalued POV feature [*ud*] that must be checked
   in a Spec-head relation with a POV operator in matrix CP, ascribing
   the negative attitude of *the-hell* to the speaker of the utterance.

2. **Parasitic movement** (@cite{merchant-2002}): *the-hell* is a
   modifier adjoined to the wh-head. It cannot move independently — its
   movement to Spec-CP is parasitic on the wh-phrase's movement.

Predicts: *the-hell* is licensed iff the wh-phrase reaches matrix
Spec-CP. Full and partial movement satisfy this; unselective binding
(in-situ) does not.

## Comparison with Alternative Accounts

- **@cite{den-dikken-giannakidou-2002}** (intervention/PI): correctly
  predicts in-situ bad in *multiple* wh-questions (intervener present)
  but wrongly predicts in-situ OK in *single* wh-questions (no intervener,
  per @cite{linebarger-1987}'s immediate-scope condition); doubly wrong
  for subject in-situ where Q is in immediate scope.
- **@cite{vu-lohiniva-2020}** (AttP, building on @cite{huang-ochi-2004}):
  correctly predicts full OK and in-situ bad, but wrongly predicts
  partial *bad* (paper §3.4.2 ex 32: cannot generate the correct word
  order with *the-hell* in matrix Spec-AttP and wh-phrase in embedded
  Spec-CP).

## Cross-linguistic generalization

The single typological parameter @cite{chan-shen-2026} isolate is the
modifier's movement profile (`ANDLMovementType.parasitic` for
English/Singlish *the-hell* vs `.independent` for Mandarin *daodi*,
@cite{chou-2012}). Other ANDL items — *the heck*, *the fuck*,
*the dickens*, *in the world*, *in God's name* (@cite{hoeksema-napoli-2008},
@cite{jackendoff-audring-2020}; paper footnote 6) — are predicted to
behave like *the-hell*.

## Architecture

Theory-neutral lexical entries (`theHell`, `daodi`) live in the
respective Fragment files. The Minimalist analysis (POV features,
Agree, the licensing predicate) lives in `Theories/Syntax/Minimalism/
Core/ANDL.lean`. The empirical 2×2 design uses
`Paradigms/AcceptabilityJudgment.lean`. This study file only carries
the paper's specific data (six conditions, two DD scores) and the
bridge theorems connecting theory to data.
-/

namespace ChanShen2026

open Fragments.Singlish.Questions (WhStrategy fullMovement partialMovement
  whInSitu theHell)
open Fragments.Mandarin.Questions (daodi)
open Phenomena.Questions.Typology (WhInterpMechanism)
open Phenomena.Islands (IslandSource)
open Core.Lexical.ExpressiveModifier
  (ExpressiveWhModifier ANDLMovementType Licensed)
open Minimalism.ANDL
  (povUnvaluedFeature povOperatorFeature LicensedMinimalist)
open Paradigms.AcceptabilityJudgment
  (FactorialCondition DDResult AccountPredictions)
open Interfaces.SyntaxSemantics.LeftPeriphery (SelectionClass)

-- ============================================================================
-- §1. The licensing predicate — derived from mechanism
-- ============================================================================

/-- *The-hell* is licensed under strategy `s` iff the Minimalist
    `LicensedMinimalist` predicate holds with the wh-host's matrix
    Spec-CP reachability as the input. For parasitic *the-hell*, this
    reduces to "wh-host reaches matrix Spec-CP" — the licensing
    condition IS the reachability condition. -/
def TheHellLicensed (s : WhStrategy) : Prop :=
  LicensedMinimalist theHell s.ReachesMatrixSpecCP

instance (s : WhStrategy) : Decidable (TheHellLicensed s) := by
  unfold TheHellLicensed; infer_instance

/-- For parasitic *the-hell*, licensing reduces to host reachability. -/
theorem theHellLicensed_iff_reachesSpecCP (s : WhStrategy) :
    TheHellLicensed s ↔ s.ReachesMatrixSpecCP := by
  unfold TheHellLicensed LicensedMinimalist
  exact Core.Lexical.ExpressiveModifier.parasitic_licensed_iff_host_reaches
    (m := theHell) rfl _

-- ============================================================================
-- §2. Per-strategy predictions (paper §3.3)
-- ============================================================================

/-- Full wh-movement licenses *the-hell*. -/
theorem fullMovement_licenses_theHell : TheHellLicensed fullMovement :=
  (theHellLicensed_iff_reachesSpecCP _).mpr True.intro

/-- Partial wh-movement licenses *the-hell*. -/
theorem partialMovement_licenses_theHell : TheHellLicensed partialMovement :=
  (theHellLicensed_iff_reachesSpecCP _).mpr True.intro

/-- Wh-in-situ blocks *the-hell*. -/
theorem inSitu_blocks_theHell : ¬ TheHellLicensed whInSitu := by
  rw [theHellLicensed_iff_reachesSpecCP]
  exact id

-- ============================================================================
-- §3. Empirical data — six conditions across two 2×2 factorials
-- ============================================================================

/-- A *wh-the-hell* condition is a `FactorialCondition` with two factors:
    WhType (does the sentence contain *the hell*?) and the wh-strategy. -/
abbrev Condition := FactorialCondition Bool WhStrategy

/-- In-situ comparison conditions (paper §2.1, ex 4): -/
def whLong : Condition :=
  { label := "Wh-Long", level1 := false, level2 := fullMovement
  , sentence := "What you think Natalie is baking at 3am ah?" }

def whHellLong : Condition :=
  { label := "WhHell-Long", level1 := true, level2 := fullMovement
  , sentence := "What the hell you think Natalie is baking at 3am ah?" }

def whSitu : Condition :=
  { label := "Wh-Situ", level1 := false, level2 := whInSitu
  , sentence := "You think Natalie is baking what at 3am ah?" }

def whHellSitu : Condition :=
  { label := "WhHell-Situ", level1 := true, level2 := whInSitu
  , sentence := "You think Natalie is baking what the hell at 3am ah?" }

/-- Partial movement comparison conditions (paper §2.1, ex 6): -/
def whPartial : Condition :=
  { label := "Wh-Partial", level1 := false, level2 := partialMovement
  , sentence := "You think what Natalie is baking at 3am ah?" }

def whHellPartial : Condition :=
  { label := "WhHell-Partial", level1 := true, level2 := partialMovement
  , sentence := "You think what the hell Natalie is baking at 3am ah?" }

/-- Subject wh-in-situ comparison (paper §3.3, ex 22). Subject in-situ
    *wh-the-hell* is also unacceptable, despite no intervener (single
    wh-question, Q in immediate scope) — a separate prediction failure
    for the intervention account. -/
def whHellSituSubject : Condition :=
  { label := "WhHell-Situ-Subject", level1 := true, level2 := whInSitu
  , sentence := "You that time heard that who the hell went hospital for surgery ah?" }

-- ============================================================================
-- §4. DD scores (paper §2.2)
-- ============================================================================

/-- In-situ comparison DD score: large positive (1.15), significant
    interaction → superadditive penalty for *the-hell* in-situ. -/
def insituDD : DDResult :=
  { comparison := "in-situ vs full movement"
  , dd := 23 / 20  -- 1.15 exact
  , interactionSignificant := true }

/-- Partial-movement comparison DD score: ≈ 0 (-0.02), no significant
    interaction → costs are linearly additive. -/
def partialDD : DDResult :=
  { comparison := "partial vs full movement"
  , dd := -1 / 50  -- -0.02 exact
  , interactionSignificant := false }

/-- The in-situ DD is genuinely positive (superadditive). -/
theorem insituDD_superadditive : insituDD.Superadditive := by
  unfold DDResult.Superadditive insituDD
  norm_num

/-- The partial-movement DD is non-positive (additive or below). -/
theorem partialDD_not_superadditive : ¬ partialDD.Superadditive := by
  unfold DDResult.Superadditive partialDD
  norm_num

-- ============================================================================
-- §5. Theory ↔ data bridge — the licensed conditions are exactly the
-- ones the experiment found acceptable
-- ============================================================================

/-- For each *wh-the-hell* condition, the strategy's licensing prediction
    matches the experimental outcome. These theorems break if a
    condition's strategy changes or if the licensing predicate is
    redefined — they tie experimental data to theory. -/
theorem whHellLong_licensed : TheHellLicensed whHellLong.level2 :=
  fullMovement_licenses_theHell

theorem whHellPartial_licensed : TheHellLicensed whHellPartial.level2 :=
  partialMovement_licenses_theHell

theorem whHellSitu_unlicensed : ¬ TheHellLicensed whHellSitu.level2 :=
  inSitu_blocks_theHell

theorem whHellSituSubject_unlicensed : ¬ TheHellLicensed whHellSituSubject.level2 :=
  inSitu_blocks_theHell

-- ============================================================================
-- §6. Account comparison (paper Table 5)
-- ============================================================================

/-- The empirical pattern: full ✓, partial ✓, in-situ ✗, subject in-situ ✗. -/
def empiricalPattern : AccountPredictions 4 :=
  AccountPredictions.of2x2 True True False False

/-- Chan & Shen 2026 (negative attitude ascription via POV). The
    predictions are derived from `TheHellLicensed`, which derives from
    `WhStrategy.ReachesMatrixSpecCP`, which derives from the strategy's
    `WhInterpMechanism`. -/
def negativeAttitudeAscription : AccountPredictions 4 :=
  AccountPredictions.of2x2
    (TheHellLicensed fullMovement)
    (TheHellLicensed partialMovement)
    (TheHellLicensed whInSitu)
    (TheHellLicensed whInSitu)  -- subject in-situ predicted alike

/-- Den Dikken & Giannakidou (2002) intervention account predictions.
    Their empirical claim is that *wh-the-hell* is licensed iff Q is in
    the modifier's *immediate scope* (@cite{linebarger-1987}). In single
    wh-questions there is no other wh-phrase to intervene; their account
    therefore predicts all four single-wh cells acceptable — including
    object in-situ and subject in-situ, both wrongly. (Paper §3.4.1.) -/
def denDikkenGiannakidou : AccountPredictions 4 :=
  AccountPredictions.of2x2 True True True True

/-- Vu & Lohiniva (2020) AttP account predictions. *The-hell* is
    base-generated in matrix Spec-AttP; the nearest wh-phrase moves to
    Spec-AttP to check [+wh] before *wh-the-hell* moves to Spec-CP.

    - Full movement: wh-phrase moves all the way; ✓.
    - Partial movement: wh-phrase stops in *embedded* Spec-CP; *the hell*
      is in *matrix* Spec-AttP. There is no derivation that places them
      in a single constituent at Spell-Out (paper §3.4.2 ex 32: "no way
      to generate the correct word order"). Predicts ✗ — wrongly.
    - In-situ: wh-phrase doesn't reach Spec-AttP. ✗.
    - Subject in-situ: same. ✗.
    Three out of four right; partial-movement cell is the failure. -/
def vuLohiniva : AccountPredictions 4 :=
  AccountPredictions.of2x2 True False False False

/-- Only the Chan & Shen (2026) account matches the empirical pattern. -/
theorem only_pov_account_matches :
    AccountPredictions.Matches negativeAttitudeAscription empiricalPattern ∧
    ¬ AccountPredictions.Matches denDikkenGiannakidou empiricalPattern ∧
    ¬ AccountPredictions.Matches vuLohiniva empiricalPattern := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

-- ============================================================================
-- §7. Cross-study bridge — island sensitivity (Shen & Huang 2026)
-- ============================================================================

/-- Singlish wh-in-situ uses binding (not movement), just like Mandarin
    wh-in-situ in @cite{shen-huang-2026}. Therefore only the Specificity
    Condition applies — the PIC is inapplicable. This is why Singlish
    wh-in-situ is island-insensitive (@cite{sato-ngui-2017}: 11b).

    Connection: `constraintsForDependencyType .binding = [.semantic]`
    (no syntactic / PIC constraint). -/
theorem insitu_binding_no_pic :
    ShenHuang2026.constraintsForDependencyType
      WhInterpMechanism.unselectiveBinding.toDependencyType =
    [IslandSource.semantic] := rfl

/-- Conversely, partial movement (the second covert step) IS island-
    sensitive — paper §3.1 ex 15 shows partial movement out of a
    complex NP is unacceptable. Bridges to Shen & Huang's classification
    via `partialMovement → .movement → [.syntactic, .semantic]`. -/
theorem partial_movement_pic_applies :
    ShenHuang2026.constraintsForDependencyType
      WhInterpMechanism.partialMovement.toDependencyType =
    ShenHuang2026.constraintsForDependencyType
      WhInterpMechanism.overtMovement.toDependencyType := rfl

-- ============================================================================
-- §8. Bridge to PerspP / Dayal 2025 (`LeftPeriphery.lean`)
-- ============================================================================

/-! The syntactic POV feature on *the-hell* is the feature-checking reflex
    of the semantic PerspectiveP layer (@cite{dayal-2025}). Both encode
    the requirement that a perspectival center (the speaker, in direct
    questions) must be identified.

    - **Syntactic** (this file): [*ud*] on *the-hell* checked by POV-op
      in matrix C; reaches Spec-CP iff host reaches Spec-CP.
    - **Semantic** (`LeftPeriphery.lean`): PerspP introduces PRO with
      `◇¬know(speaker, Ans(Q))` — the possible-ignorance presupposition.

    *The-hell*'s negative attitude (speaker finds every possible answer
    improbable, @cite{rawlins-2008}; ignorance reading,
    @cite{martin-2020}; conventional implicature, @cite{ippolito-2024})
    strengthens PerspP's possible-ignorance presupposition. -/

/-- Direct *wh-the-hell* questions select PerspP — they require the
    speaker as perspectival center (the negative attitude bearer in
    @cite{chou-2012}'s analysis). Bridges Chan & Shen's syntactic POV
    apparatus to Dayal's semantic PerspP layer. -/
def theHellSelectionClass : SelectionClass := .rogativePerspP

/-- The PerspP-selecting class is precisely the one that does *not*
    entail knowledge of the answer — matching *the-hell*'s ignorance
    component (@cite{martin-2020}). Bridge from `LeftPeriphery`. -/
theorem theHell_no_knowledge :
    Interfaces.SyntaxSemantics.LeftPeriphery.entailsKnowledge
      theHellSelectionClass = false := rfl

/-- The PerspP-selecting class is consistent with the possible-ignorance
    presupposition (`◇¬know(speaker, Ans(Q))`) — the semantic side of
    *the-hell*'s negative attitude (@cite{rawlins-2008},
    @cite{ippolito-2024}). -/
theorem theHell_persp_consistent :
    Interfaces.SyntaxSemantics.LeftPeriphery.perspPConsistent
      theHellSelectionClass false false = true := rfl

-- ============================================================================
-- §9. Cross-linguistic — Mandarin *daodi* and the typological parameter
-- ============================================================================

/-- The *the-hell* / *daodi* minimal pair: same POV feature analysis
    (`povUnvaluedFeature` in both); single parametric difference is
    `ANDLMovementType.parasitic` vs `.independent`. -/
theorem theHell_daodi_movement_contrast :
    theHell.movementType = .parasitic ∧
    daodi.movementType = .independent := ⟨rfl, rfl⟩

/-- *Daodi* is licensed even with wh-in-situ — it moves independently
    to matrix Spec-CP. Theory-neutral consequence of the typological
    parameter, derived via `independent_matrix_always_licensed`. -/
theorem daodi_licensed_insitu (P : Prop) :
    Licensed daodi P :=
  Core.Lexical.ExpressiveModifier.independent_matrix_always_licensed
    rfl rfl P

end ChanShen2026
