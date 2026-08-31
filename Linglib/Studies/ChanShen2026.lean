import Linglib.Fragments.Singlish.Questions
import Linglib.Fragments.Mandarin.Questions
import Linglib.Syntax.Minimalist.Features
import Linglib.Syntax.Category.ExpressiveModifier
import Linglib.Syntax.Minimalist.LeftPeriphery
import Linglib.Studies.SprouseEtAl2012
import Linglib.Studies.Ross1967

/-!
# Chan and Shen 2026: conditions on *wh-the-hell* licensing

This file formalizes the account of *wh-the-hell* licensing in [chan-shen-2026]. Colloquial
Singapore English forms single wh-questions three ways — full movement, partial movement, and
in-situ — and an acceptability experiment with 32 speakers finds that *the-hell* survives the
first two but not the third: the in-situ comparison shows a superadditive interaction (DD = 1.15)
while the partial-movement one shows only additive costs (DD = −0.02, no interaction, p = 0.882).
The ban extends to subject wh-in-situ, where no higher wh-phrase could intervene.

The account has two parts. *The-hell* bears an unvalued point-of-view feature that must be checked
against a valued operator in matrix C ([chou-2012], after [huang-ochi-2004]), which is what
ascribes its negative attitude to the speaker; and it is a modifier adjoined to the wh-head, so it
cannot move on its own and rides to Spec-CP on the wh-phrase ([merchant-2002]). Licensing is then
reachability of matrix Spec-CP, which full and partial movement give and unselective binding does
not. The typological parameter is the modifier's movement profile: Mandarin *daodi* is
independent, so it is licensed even where its host stays in situ.

The paper's Table 5 compares this account with the intervention account of
[den-dikken-giannakidou-2002], which predicts in-situ acceptable in a single wh-question where no
intervener stands in the modifier's immediate scope ([linebarger-1987]), and with the AttP account
of [vu-lohiniva-2020], which cannot generate the partial-movement word order. Neither rival is
formalized here.

## Main definitions

* `Minimalist.ANDL.povUnvaluedFeature`, `povOperatorFeature`, `LicensedMinimalist` — the
  point-of-view probe and goal, and Minimalist licensing
* `TheHellLicensed` — licensing of parasitic *the-hell* under a wh-strategy
* `whLong`, `whHellSitu`, … — the experiment's six conditions plus the subject-in-situ one

## Main results

* `theHellLicensed_iff_reachesSpecCP` — for a parasitic modifier, licensing is host reachability
* `fullMovement_licenses_theHell`, `partialMovement_licenses_theHell`, `inSitu_blocks_theHell` —
  the three verdicts
* `whHellSitu_unlicensed`, `whHellSituSubject_unlicensed`, `whHellPartial_licensed` — the same
  verdicts at the experiment's conditions
* `insitu_binding_no_pic`, `partial_movement_pic_applies` — why in-situ is island-insensitive and
  partial movement is not
* `daodi_licensed_insitu`, `theHell_daodi_movement_contrast` — the typological parameter

## References

* [chan-shen-2026]
* [pesetsky-1987]
* [chou-2012]
* [huang-ochi-2004]
* [merchant-2002]
* [den-dikken-giannakidou-2002]
* [vu-lohiniva-2020]
* [linebarger-1987]
* [sato-ngui-2017]
* [rawlins-2008]
* [martin-2020]
* [ippolito-2024]
* [dayal-2025]
* [hoeksema-napoli-2008]
* [jackendoff-audring-2020]
* [shen-huang-2026]
-/

namespace Minimalist.ANDL

/-! ## Minimalist POV-feature analysis

The Minimalist (POV-feature) analysis of aggressively non-D-linked
(ANDL) wh-modifiers, due to [chou-2012] (building on
[huang-ochi-2004], [merchant-2002]). The theory-neutral
lexical entry lives in `Core/Lexical/ExpressiveModifier.lean`; this
section adds the framework-specific syntactic apparatus: an unvalued
POV feature [*ud*] on the modifier, a valued [+d] POV operator
merged in matrix C, and Spec-head Agree as the licensing relation.

1. ANDL modifier (e.g., *the-hell*) carries an **unvalued** POV feature
   [*ud*]: a probe needing valuation.
2. Matrix C carries a **valued** POV operator [+d]: a goal.
3. Feature checking happens in Spec-head configuration in matrix CP.
4. Therefore the modifier must reach matrix Spec-CP. For parasitic
   modifiers (English/Singlish *the-hell*), this requires the wh-host
   to reach matrix Spec-CP. For independent modifiers (Mandarin *daodi*),
   the modifier moves on its own. -/

open ExpressiveModifier (ExpressiveWhModifier Licensed)

/-- The unvalued POV feature [*ud*] borne by ANDL modifiers
    ([chou-2012]). A probe seeking a [+d] goal in a Spec-head
    relation. -/
def povUnvaluedFeature : GramFeature := .unvalued (.pov true)

/-- The valued POV feature [+d] on the matrix-C POV operator. The goal
    that values [*ud*]. -/
def povOperatorFeature : GramFeature := .valued (.pov true)

/-- The probe-goal pair matches under `featuresMatch`: same feature
    type, opposite valuation status — the prerequisite for Agree. -/
theorem pov_probe_goal_match :
    featuresMatch povUnvaluedFeature povOperatorFeature = true := rfl

/-- Minimalist licensing: an ANDL modifier is licensed iff a configuration
    obtains in which `povUnvaluedFeature` checks against `povOperatorFeature`
    in matrix Spec-CP. Operationally:

    - For a **parasitic** modifier, the wh-host must reach matrix Spec-CP
      (so that the adjoined modifier reaches Spec-CP with it).
    - For an **independent** modifier, the modifier moves to matrix Spec-CP
      on its own — host reachability is irrelevant.

    This is the Minimalist instantiation of the theory-neutral
    `ExpressiveModifier.Licensed`. The Minimalist version
    doesn't add a separate condition — it identifies "modifier reaches
    Spec-CP" as the structural realization of "scope position reached". -/
abbrev LicensedMinimalist (m : ExpressiveWhModifier)
    (whHostReachesMatrixSpecCP : Prop) : Prop :=
  Licensed m whHostReachesMatrixSpecCP

end Minimalist.ANDL

namespace ChanShen2026

open Singlish.Questions (WhStrategy fullMovement partialMovement
  whInSitu theHell)
open Mandarin.Questions (daodi)
open Syntax.Question (WhInterpMechanism)
open ExpressiveModifier
  (ExpressiveWhModifier ANDLMovementType Licensed)
open Minimalist.ANDL
  (povUnvaluedFeature povOperatorFeature LicensedMinimalist)
open SprouseEtAl2012 (FactorialCondition)
open Minimalist.LeftPeriphery (SelectionClass)

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
  exact ExpressiveModifier.parasitic_licensed_iff_host_reaches
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
-- §7. Cross-study bridge — island sensitivity (Shen & Huang 2026)
-- ============================================================================

/-- Singlish wh-in-situ uses binding (not movement), just like Mandarin
    wh-in-situ in [shen-huang-2026]. Therefore only the Specificity
    Condition applies — the PIC is inapplicable. This is why Singlish
    wh-in-situ is island-insensitive ([sato-ngui-2017]: 11b).

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
    of the semantic PerspectiveP layer ([dayal-2025]). Both encode
    the requirement that a perspectival center (the speaker, in direct
    questions) must be identified.

    - **Syntactic** (this file): [*ud*] on *the-hell* checked by POV-op
      in matrix C; reaches Spec-CP iff host reaches Spec-CP.
    - **Semantic** (`LeftPeriphery.lean`): PerspP introduces PRO with
      `◇¬know(speaker, Ans(Q))` — the possible-ignorance presupposition.

    *The-hell*'s negative attitude (speaker finds every possible answer
    improbable, [rawlins-2008]; ignorance reading,
    [martin-2020]; conventional implicature, [ippolito-2024])
    strengthens PerspP's possible-ignorance presupposition. -/

/-- Direct *wh-the-hell* questions select PerspP — they require the
    speaker as perspectival center (the negative attitude bearer in
    [chou-2012]'s analysis). Bridges Chan & Shen's syntactic POV
    apparatus to Dayal's semantic PerspP layer. -/
def theHellSelectionClass : SelectionClass := .rogativePerspP

/-- The PerspP-selecting class is precisely the one that does *not*
    entail knowledge of the answer — matching *the-hell*'s ignorance
    component ([martin-2020]). Bridge from `LeftPeriphery`. -/
theorem theHell_no_knowledge :
    Minimalist.LeftPeriphery.entailsKnowledge
      theHellSelectionClass = false := rfl

/-- The PerspP-selecting class is consistent with the possible-ignorance
    presupposition (`◇¬know(speaker, Ans(Q))`) — the semantic side of
    *the-hell*'s negative attitude ([rawlins-2008],
    [ippolito-2024]). -/
theorem theHell_persp_consistent :
    Minimalist.LeftPeriphery.perspPConsistent
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
  ExpressiveModifier.independent_matrix_always_licensed
    rfl rfl P

end ChanShen2026
