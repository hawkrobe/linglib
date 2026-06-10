import Linglib.Semantics.Modality.Kratzer.Operators
import Linglib.Data.Examples.Schema

/-!
# [vonfintel-iatridou-2005] — Anankastic conditionals and related matters

The "Harlem Sentence" — *If you want to go to Harlem, you have to take
the A train* — and the puzzle: no straightforward Kratzerian analysis
delivers its truth conditions. vF&I rule out three candidate analyses
(if-clause restricts the modal base, modifies the ordering source à la
[saebo-2001], or is restricted by a covert higher modal), then
propose a **Designated Goals** account paired with
[sloman-1970]'s have-to-vs-ought-to distinction.

This file contains:

* `obviousAnalysis` (if-clause adds to modal base) refuted on the
  Hoboken Problem (vF&I (11));
* `saeboAnalysis` (if-clause adds to ordering source) refuted on the
  Conflicting Goals scenario (vF&I (13));
* the **Designated Goals** structure with `oughtTo`/`haveTo` operators
  and the Sloman entailment `haveTo_implies_oughtTo_of_best_subset_accessible`;
* cross-reference (in the closing docstring) to
  [chung-mascarenhas-2024]: the C&M exhaustification clause is the
  formal expected-value realisation of Sloman's "only candidate".
  C&M handles the Harlem base case, Burdick's contextual designation,
  and Breathe-style trivialities (via §5 plausibility). Open: Nissenbaum
  Pedro Martinez (no causal-essentialness filter); Huitink van
  Nistelrooy (correlated-irrelevant).

Example data lives in `Linglib/Data/Examples/vonFintelIatridou2005.json`
and is generated into the `Examples` section below by
`scripts/gen_examples.py vonFintelIatridou2005`.
-/

namespace VonFintelIatridou2005

open Data.Examples (LinguisticExample SourceRef)
open Features (Judgment)

/-! ### Analytical predicates

Each candidate analysis is a predicate parameterized by the relevant
propositions on a world type. Concrete vF&I scenarios (Hoboken,
Conflicting Goals) instantiate these arguments with their own predicates
and `decide` discharges the refutation. Bundling the propositions into
a `Scenario` structure would hide the per-predicate decidability the
refutations need behind a field projection; the explicit-argument form
keeps each refutation mechanically verifiable. The circumstantial
modal base is taken as universal (the worked vF&I scenarios do not
exploit modal-base restriction). -/

/-! ### Obvious analysis and the Hoboken Problem

vF&I eq. (9): `[have to](w)(f)(g)(q) = 1 iff ∀w' ∈ max_{g(w)}(∩f(w)) : q(w') = 1`.
vF&I eq. (10): `[if φ](f) = λw. f(w) ∪ {⟦φ⟧}`.

Combined, the "obvious analysis" of the Harlem Sentence asserts: in the
best (per actual goals) worlds where you want to go to Harlem, you take
the A train. In the Hoboken scenario the actual ordering source ranks
worlds by satisfaction of *want-Hoboken*. Best *want-Harlem* worlds are
then those that simultaneously achieve Hoboken — i.e., take the PATH
train — so the obvious analysis predicts the sentence false (vF&I p. 5
intuition: true). -/

/-- The obvious analysis: the candidate is true at every want-Harlem
world that maximizes actual-goal-achievement. -/
def obviousAnalysis {W : Type*}
    (wantHyp achieveAct candidate : W → Prop) : Prop :=
  ∀ w : W, wantHyp w →
    (∀ w' : W, wantHyp w' → achieveAct w' → achieveAct w) →
    candidate w

/-! The Hoboken scenario. Four worlds:
`w0`: A train, achieves Harlem; `w1`: PATH, achieves Hoboken;
`w2`: PATH, achieves both Hoboken AND want-Harlem holds — the
counterexample world; `w3`: A train, achieves Harlem. -/

namespace HobokenScenario

abbrev World := Fin 4

def wantHypothetical : World → Prop := λ w => w.val = 0 ∨ w.val = 2 ∨ w.val = 3
instance : DecidablePred wantHypothetical := λ w => by unfold wantHypothetical; infer_instance

def achieveActual : World → Prop := λ w => w.val = 1 ∨ w.val = 2
instance : DecidablePred achieveActual := λ w => by unfold achieveActual; infer_instance

def takeCandidate : World → Prop := λ w => w.val = 0 ∨ w.val = 3
instance : DecidablePred takeCandidate := λ w => by unfold takeCandidate; infer_instance

end HobokenScenario

/-- The Hoboken scenario falsifies the obvious analysis: at `w2` the
candidate (A train) is false. -/
theorem hoboken_refutes_obvious :
    ¬ obviousAnalysis
        HobokenScenario.wantHypothetical
        HobokenScenario.achieveActual
        HobokenScenario.takeCandidate := by
  intro h
  have hCand : HobokenScenario.takeCandidate (⟨2, by decide⟩ : Fin 4) := by
    apply h ⟨2, by decide⟩
    · decide -- wantHypothetical w₂
    · intro w' _ _; decide -- w₂ maximizes achieveActual among want-Harlem worlds
  exact absurd hCand (by decide)

/-! ### Sæbø 2001's analysis and the Conflicting Goals refutation

[saebo-2001] adds the *if*-clause's proposition to the **ordering
source** rather than the modal base: `g⁺(w) := g(w) ∪ {⟦want-Harlem⟧}`.
The modal quantifies over best worlds in the modal base under `g⁺`.
This survives the basic Hoboken setup but is non-compositional
(*want* has to be zapped) and fails on Conflicting Goals scenarios
(vF&I (13), (22)) where actual and hypothetical goals are jointly
satisfiable yet conflicting in the concrete instance. -/

/-- Sæbø's analysis: quantifies over worlds maximizing actual goal
∧ hypothetical goal jointly. -/
def saeboAnalysis {W : Type*}
    (achieveAct achieveHyp candidate : W → Prop) : Prop :=
  ∀ w : W,
    (∀ w' : W, (achieveAct w' ∧ achieveHyp w') →
       (achieveAct w ∧ achieveHyp w)) →
    candidate w

/-! The Conflicting Goals scenario (vF&I (13)/(22)). Five worlds:
`w0`: A, Harlem-only; `w1`: PATH, Hoboken-only;
`w2`: A, both; `w3`: PATH, both — the counterexample world;
`w4`: neither, neither. -/

namespace ConflictingGoalsScenario

abbrev World := Fin 5

def achieveHypothetical : World → Prop := λ w => w.val = 0 ∨ w.val = 2 ∨ w.val = 3
instance : DecidablePred achieveHypothetical := λ w => by unfold achieveHypothetical; infer_instance

def achieveActual : World → Prop := λ w => w.val = 1 ∨ w.val = 2 ∨ w.val = 3
instance : DecidablePred achieveActual := λ w => by unfold achieveActual; infer_instance

def takeCandidate : World → Prop := λ w => w.val = 0 ∨ w.val = 2
instance : DecidablePred takeCandidate := λ w => by unfold takeCandidate; infer_instance

end ConflictingGoalsScenario

/-- The Conflicting Goals scenario falsifies Sæbø's analysis: at `w3`
both goals are jointly achieved but the candidate (A train) is false. -/
theorem conflictingGoals_refutes_saebo :
    ¬ saeboAnalysis
        ConflictingGoalsScenario.achieveActual
        ConflictingGoalsScenario.achieveHypothetical
        ConflictingGoalsScenario.takeCandidate := by
  intro h
  have hCand : ConflictingGoalsScenario.takeCandidate (⟨3, by decide⟩ : Fin 5) := by
    apply h ⟨3, by decide⟩
    intro w' _; decide
  exact absurd hCand (by decide)

/-! ### Nested Modality

vF&I §5 propose that the *if*-clause restricts an additional covert
necessity modal scoping over the teleological modal:
`[ NEC if you want to go to Harlem ] [ have-to (you take the A train) ]`.
This survives the Hoboken Problem but fails on the Conflicting Goals
scenario and on Huitink's van Nistelrooy (correlated-irrelevant). The
shared failure motivates the Designated Goals move below. Not
formalised here. -/

/-! ### The Designated Goals proposal -/

section DesignatedGoals
open Semantics.Modality.Kratzer

/-- [vonfintel-iatridou-2005] §6 parameter for a teleological
modal: a *designated goal* supplied by the to/if-clause, *ancillary
considerations* ranking goal-achieving worlds, and a circumstantial
modal base. -/
structure DesignatedGoal (W : Type*) where
  /-- The designated goal: a proposition the addressee is taken to pursue. -/
  goal : W → Prop
  /-- Ancillary considerations: a Kratzer ordering source over worlds. -/
  ancillary : OrderingSource W
  /-- Circumstantial modal base. -/
  modalBase : ModalBase W

/-- vF&I (24a): *to p, ought-to q* — q at every ancillary-best
goal-achieving world. -/
def oughtTo {W : Type*} (dg : DesignatedGoal W) (q : W → Prop) (w : W) : Prop :=
  ∀ w' : W, w' ∈ bestWorlds dg.modalBase
                  (λ v => dg.ancillary v ++ [dg.goal]) w →
    q w'

/-- vF&I (24b): *to p, have-to q* — q at every goal-achieving world
in the modal base. The exhaustification (no ranking) is the formal
counterpart of [sloman-1970]'s "only candidate". -/
def haveTo {W : Type*} (dg : DesignatedGoal W) (q : W → Prop) (w : W) : Prop :=
  ∀ w' : W, w' ∈ accessibleWorlds dg.modalBase w → dg.goal w' → q w'

/-- [sloman-1970] / vF&I §6: have-to entails ought-to, under the
structural assumption that every ancillary-best world is accessible
and goal-achieving. -/
theorem haveTo_implies_oughtTo_of_best_subset_accessible {W : Type*}
    (dg : DesignatedGoal W) (q : W → Prop) (w : W)
    (hHave : haveTo dg q w)
    (hBestSubset : ∀ w',
      w' ∈ bestWorlds dg.modalBase
              (λ v => dg.ancillary v ++ [dg.goal]) w →
      w' ∈ accessibleWorlds dg.modalBase w ∧ dg.goal w') :
    oughtTo dg q w := by
  intro w' hBest
  obtain ⟨hAcc, hGoal⟩ := hBestSubset w' hBest
  exact hHave w' hAcc hGoal

end DesignatedGoals

/-! ### Cross-reference to [chung-mascarenhas-2024]

C&M's `mustCM` operator
(`Studies/ChungMascarenhas2024.lean`) realises
[sloman-1970]'s "only candidate" condition as an
**exhaustification clause** on expected values:
`mustCM φ` iff `E[μ_R ∣ φ] > θ ∧ ∀ψ ∈ Alt(φ). E[μ_R ∣ ψ] ≤ θ`.
The first conjunct is strong permissibility (φ achieves the goal
well enough); the second is the only-candidate condition. Under
deontic/teleological `R = R_D`, this directly maps to vF&I's
*have-to*: φ has to be the unique good-enough way of achieving the
designated goal.

**Handled cleanly by C&M:**
* Harlem base case (`vFI2005_1_harlem`, `vFI2005_4_harlemPurpose`).
* Burdick's hot chocolate (`vFI2005_28_burdicks`) via contextually
  supplied `R`.
* Trivially-true Breathe (`vFI2005_34c_harlemBreathe`) via §5
  plausibility requirement on `R`.
* Sloman's have-to-vs-ought-to (`vFI2005_23_slomanOughtNot`,
  `vFI2005_p13_londonByNoon`) by dropping the exhaustification clause
  for ought-to.

**Not dissolved by C&M:**
* Pedro Martinez (`vFI2005_36_pedroMartinez`): C&M's `R` is a flat set
  of propositions, no causal-essentialness filter. Nissenbaum's
  insight (the to-clause requires the consequent to be an *essential
  part of a way of achieving* the goal) is not in C&M.
* Van Nistelrooy (`vFI2005_p12_vanNistelrooy`): correlated-irrelevant
  preferences enter `R` and skew the expected value.
-/

-- BEGIN GENERATED EXAMPLES
-- (Generated from Linglib/Data/Examples/vonFintelIatridou2005.json by scripts/gen_examples.py.
-- Do not edit between markers; re-run the generator after editing the JSON.)

namespace Examples
open Data.Examples

def vFI2005_1_harlem : LinguisticExample :=
  { id := "vFI2005_1_harlem"
    source := ⟨"vonfintel-iatridou-2005", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If you want to go to Harlem, you have to take the A train."
    discourseSegments := []
    glossedTokens := []
    translation := "If you want to go to Harlem, you have to take the A train."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("puzzle", "harlemBase")]
    comment := "The canonical Harlem Sentence; the paper's central example."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def vFI2005_2_sugarWaiter : LinguisticExample :=
  { id := "vFI2005_2_sugarWaiter"
    source := ⟨"hare-1971", "p. 45"⟩
    reportedIn := some ⟨"vonfintel-iatridou-2005", "(2)"⟩
    language := "stan1293"
    primaryText := "If you want sugar in your soup, you should ask the waiter."
    discourseSegments := []
    glossedTokens := []
    translation := "If you want sugar in your soup, you should ask the waiter."
    context := "Waiter has the only access to sugar."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("puzzle", "hareMinimalPair"), ("reading", "anankastic")]
    comment := "Anankastic reading: asking the waiter is a means to having sugar. Same surface form as (3) but different reading — surface form does not determine anankasticity."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def vFI2005_3_sugarDiabetes : LinguisticExample :=
  { id := "vFI2005_3_sugarDiabetes"
    source := ⟨"hare-1971", "p. 45"⟩
    reportedIn := some ⟨"vonfintel-iatridou-2005", "(3)"⟩
    language := "stan1293"
    primaryText := "If you want sugar in your soup, you should get tested for diabetes."
    discourseSegments := []
    glossedTokens := []
    translation := "If you want sugar in your soup, you should get tested for diabetes."
    context := "Excessive desire for sugar may indicate diabetes."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("puzzle", "hareMinimalPair"), ("reading", "non-anankastic")]
    comment := "NON-anankastic reading: getting tested is not a means to having sugar. Pair with (2) to show that surface form does not determine anankasticity."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def vFI2005_4_harlemPurpose : LinguisticExample :=
  { id := "vFI2005_4_harlemPurpose"
    source := ⟨"vonfintel-iatridou-2005", "(4)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "To go to Harlem, you have to take the A train."
    discourseSegments := []
    glossedTokens := []
    translation := "To go to Harlem, you have to take the A train."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("puzzle", "harlemBase"), ("clauseType", "purpose")]
    comment := "Purpose-clause near-equivalent of (1); vF&I treat the purpose variant as the primary form for their designated-goal analysis."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def vFI2005_11_hoboken : LinguisticExample :=
  { id := "vFI2005_11_hoboken"
    source := ⟨"vonfintel-iatridou-2005", "(11) / p. 5"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If you want to go to Harlem, you have to take the A train."
    discourseSegments := []
    glossedTokens := []
    translation := "If you want to go to Harlem, you have to take the A train."
    context := "You actually want to go to Hoboken; I do not know that. Best way to Hoboken is the PATH train; best way to Harlem is the A train."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("puzzle", "hoboken")]
    comment := "The Hoboken Problem. Defeats the obvious analysis: if the if-clause merely added 'you want Harlem' to the modal base, the best goal-achievement at the actual world would be PATH (since the actual goal is Hoboken)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def vFI2005_13_hobokenSaebo : LinguisticExample :=
  { id := "vFI2005_13_hobokenSaebo"
    source := ⟨"vonfintel-iatridou-2005", "(13)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If you want to go to Harlem, you should take the A train."
    discourseSegments := []
    glossedTokens := []
    translation := "If you want to go to Harlem, you should take the A train."
    context := "You want Hoboken (PATH); I am uncertain whether you want Hoboken or Harlem. Sæbø's analysis adds 'go to Harlem' to your existing goals, making the new best worlds include both Hoboken and Harlem destinations."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("puzzle", "conflictingGoals")]
    comment := "Sæbø 2001's analysis predicts this false (best worlds equally split between PATH and A train); intuition says true. Defeats the if-clause-modifies-ordering-source analysis."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def vFI2005_22_mayorPub : LinguisticExample :=
  { id := "vFI2005_22_mayorPub"
    source := ⟨"kratzer-1991", "mayor scenario"⟩
    reportedIn := some ⟨"vonfintel-iatridou-2005", "(21)/(22)"⟩
    language := "stan1293"
    primaryText := "If you want to become mayor, you have to go to the pub regularly."
    discourseSegments := []
    glossedTokens := []
    translation := "If you want to become mayor, you have to go to the pub regularly."
    context := "You want to become mayor. You also want to not go to the pub regularly. You will become mayor only if you go to the pub regularly."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("puzzle", "conflictingGoals")]
    comment := "Conflicting jointly-satisfiable goals. The if-clause's goal must override the actual conflicting goal, not merely augment the ordering source."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def vFI2005_p12_vanNistelrooy : LinguisticExample :=
  { id := "vFI2005_p12_vanNistelrooy"
    source := ⟨"huitink-2008", "van Nistelrooy scenario"⟩
    reportedIn := some ⟨"vonfintel-iatridou-2005", "p. 12"⟩
    language := "stan1293"
    primaryText := "If you want to go to Harlem, you have to take the A train."
    discourseSegments := []
    glossedTokens := []
    translation := "If you want to go to Harlem, you have to take the A train."
    context := "Either A train or C train goes to Harlem. You are an incorrigible fan of Ruud van Nistelrooy and most want to meet him. Van Nistelrooy regularly rides the A train."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("puzzle", "correlatedIrrelevant")]
    comment := "Both routes achieve Harlem; van Nistelrooy preference makes A optimal under naive lifting, but speakers report reluctance to judge the have-to sentence true on this scenario."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def vFI2005_36_pedroMartinez : LinguisticExample :=
  { id := "vFI2005_36_pedroMartinez"
    source := ⟨"nissenbaum-2005", "Pedro Martinez"⟩
    reportedIn := some ⟨"vonfintel-iatridou-2005", "(36)"⟩
    language := "stan1293"
    primaryText := "To go to Harlem, you ought to kiss Pedro Martinez."
    discourseSegments := []
    glossedTokens := []
    translation := "To go to Harlem, you ought to kiss Pedro Martinez."
    context := "Both A train and C train go to Harlem. Pedro Martinez is on both. You want to kiss Pedro Martinez."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("puzzle", "nonCausalCoincidence")]
    comment := "Kissing Pedro is not an essential part of any way of achieving Harlem; sentence is absurd despite the correlation. Motivates vF&I's 'essential part of a way of achieving' refinement (their (42))."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def vFI2005_34c_harlemBreathe : LinguisticExample :=
  { id := "vFI2005_34c_harlemBreathe"
    source := ⟨"vonstechow-krasikova-penka-2005", "breathe example"⟩
    reportedIn := some ⟨"vonfintel-iatridou-2005", "(34c)"⟩
    language := "stan1293"
    primaryText := "In order to go to Harlem, you have to breathe."
    discourseSegments := []
    glossedTokens := []
    translation := "In order to go to Harlem, you have to breathe."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("puzzle", "triviallyTrue"), ("modal", "have-to")]
    comment := "vF&I accept as true though unhelpful. Chung & Mascarenhas 2024 §5 needs a plausibility-requirement patch to rule out analogous epistemic cases (#He must be dead)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def vFI2005_35_harlemBreatheOught : LinguisticExample :=
  { id := "vFI2005_35_harlemBreatheOught"
    source := ⟨"vonfintel-iatridou-2005", "(35)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "To go to Harlem, you ought to breathe."
    discourseSegments := []
    glossedTokens := []
    translation := "To go to Harlem, you ought to breathe."
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("puzzle", "triviallyTrue"), ("modal", "ought-to")]
    comment := "Less acceptable than the have-to variant. vF&I derive this from have-to entailing ought-to, so ought-to signals there are alternatives — false for breathing."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def vFI2005_23_slomanOughtNot : LinguisticExample :=
  { id := "vFI2005_23_slomanOughtNot"
    source := ⟨"sloman-1970", "ought vs better"⟩
    reportedIn := some ⟨"vonfintel-iatridou-2005", "(23)"⟩
    language := "stan1293"
    primaryText := "You ought to take the train, but you don't have to."
    discourseSegments := []
    glossedTokens := []
    translation := "You ought to take the train, but you don't have to."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("puzzle", "oughtVsHaveTo")]
    comment := "Felicitous because ought says what is best while have-to picks out the only candidate."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def vFI2005_p13_londonByNoon : LinguisticExample :=
  { id := "vFI2005_p13_londonByNoon"
    source := ⟨"sloman-1970", "p. 391"⟩
    reportedIn := some ⟨"vonfintel-iatridou-2005", "p. 13"⟩
    language := "stan1293"
    primaryText := "If you want to get to London by noon, then you ought to go by train."
    discourseSegments := []
    glossedTokens := []
    translation := "If you want to get to London by noon, then you ought to go by train."
    context := "Train is the best option but not the only one."
    judgment := .acceptable
    alternatives := [("If you want to get to London by noon, then you have to go by train.", .unacceptable)]
    readings := []
    paperFeatures := [("puzzle", "oughtVsHaveTo")]
    comment := "Sloman: 'picks out the best means without excluding the possibility of others.' Contrast with the have-to variant implying no other means exists."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def vFI2005_29_vladivostokHave : LinguisticExample :=
  { id := "vFI2005_29_vladivostokHave"
    source := ⟨"vonstechow-krasikova-penka-2005", "Vladivostok"⟩
    reportedIn := some ⟨"vonfintel-iatridou-2005", "(29)"⟩
    language := "stan1293"
    primaryText := "To go to Vladivostok, you have to take the Chinese train."
    discourseSegments := []
    glossedTokens := []
    translation := "To go to Vladivostok, you have to take the Chinese train."
    context := "Two trains cross Siberia to Vladivostok: Russian and Chinese. The Chinese train is significantly more comfortable."
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("puzzle", "vladivostokOughtHave"), ("modal", "have-to"), ("speakerVariation", "Klein-vs-Percus")]
    comment := "Klein-type speakers accept (comfort is implicitly part of the designated goal); Percus-type speakers reject. Documents real speaker variation."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def vFI2005_30_vladivostokOught : LinguisticExample :=
  { id := "vFI2005_30_vladivostokOught"
    source := ⟨"vonfintel-iatridou-2005", "(30)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "To go to Vladivostok, you ought to take the Chinese train."
    discourseSegments := []
    glossedTokens := []
    translation := "To go to Vladivostok, you ought to take the Chinese train."
    context := "Same Vladivostok scenario."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("puzzle", "vladivostokOughtHave"), ("modal", "ought-to")]
    comment := "Ought-to accepts without controversy because comfort considerations rank the Chinese train above the Russian."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def vFI2005_28_burdicks : LinguisticExample :=
  { id := "vFI2005_28_burdicks"
    source := ⟨"vonfintel-iatridou-2005", "(28)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: I'm going to Harvard Square tomorrow. B: You have to have some hot chocolate at Burdick's."
    discourseSegments := ["I'm going to Harvard Square tomorrow.", "You have to have some hot chocolate at Burdick's."]
    glossedTokens := []
    translation := "Same."
    context := "A announces an itinerary; no to-clause or if-clause overtly supplies a goal."
    judgment := .acceptable
    alternatives := [("You ought to have some hot chocolate at Burdick's.", .acceptable)]
    readings := []
    paperFeatures := [("puzzle", "contextualDesignation")]
    comment := "Designated goal supplied by context (something like 'have a good Harvard Square experience'), not by overt syntax. Motivates vF&I §6.4."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def vFI2005_20_weinerJoe : LinguisticExample :=
  { id := "vFI2005_20_weinerJoe"
    source := ⟨"vonfintel-iatridou-2005", "(20) (scenario by Weiner)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Joe wants to go to Harlem, he must take the A train."
    discourseSegments := []
    glossedTokens := []
    translation := "If Joe wants to go to Harlem, he must take the A train."
    context := "Joe has been considering buying a used car in Harlem. If he hasn't bought it yet, the A train is his only way to Harlem; if he has bought it, he can drive or take the A train. The only reason Joe would want Harlem is to buy the car (so if he wants Harlem, he hasn't bought it)."
    judgment := .acceptable
    alternatives := []
    readings := [("epistemic", .marginal), ("anankastic", .acceptable)]
    paperFeatures := [("puzzle", "weinerJoe")]
    comment := "On the anankastic reading: true in all cases. On Weiner's intended epistemic reading: true only if Joe hasn't bought the car. vF&I admit the epistemic reading is sometimes available; tests the must-can-be-epistemic-in-anankastic-shell hypothesis."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [vFI2005_1_harlem, vFI2005_2_sugarWaiter, vFI2005_3_sugarDiabetes, vFI2005_4_harlemPurpose, vFI2005_11_hoboken, vFI2005_13_hobokenSaebo, vFI2005_22_mayorPub, vFI2005_p12_vanNistelrooy, vFI2005_36_pedroMartinez, vFI2005_34c_harlemBreathe, vFI2005_35_harlemBreatheOught, vFI2005_23_slomanOughtNot, vFI2005_p13_londonByNoon, vFI2005_29_vladivostokHave, vFI2005_30_vladivostokOught, vFI2005_28_burdicks, vFI2005_20_weinerJoe]

end Examples
-- END GENERATED EXAMPLES

end VonFintelIatridou2005
