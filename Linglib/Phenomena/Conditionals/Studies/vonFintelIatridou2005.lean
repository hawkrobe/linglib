import Linglib.Theories.Semantics.Modality.Kratzer.Operators
import Linglib.Data.Examples.Schema

/-!
# @cite{vonfintel-iatridou-2005} — Anankastic conditionals and related matters

The "Harlem Sentence":

> If you want to go to Harlem, you have to take the A train.

vF&I argue that **no straightforward Kratzerian analysis** delivers the
right truth conditions for this sentence, then propose a "designated
goal" analysis paired with @cite{sloman-1970}'s have-to-vs-ought-to
distinction. This file formalizes:

* §1 the **scenario substrate** common to vF&I's worked examples
  (worlds + want-clause proposition + goal-achievement proposition +
  action propositions),
* §2 the **obvious analysis** (if-clause restricts the modal base) and
  its refutation by the Hoboken Problem (vF&I (11)),
* §3 @cite{saebo-2001}'s analysis (if-clause modifies the ordering
  source) and its refutation by the Conflicting Goals scenario (vF&I
  (13)),
* §4 the **nested modality analysis** (covert higher modal) and its
  shared failure on conflicting-goal scenarios,
* §5 the **Designated Goals proposal** (vF&I §6): the to-clause supplies
  a designated goal that overrides ancillary considerations, with
  @cite{sloman-1970}'s have-to-vs-ought-to as exhaustification asymmetry,
* §6 cross-reference to @cite{chung-mascarenhas-2024}: their
  exhaustification clause realises Sloman's "only candidate" as a
  formal expected-value condition. C&M's compositional account cleanly
  handles the Harlem base case, the contextual-designation Burdick's
  case, and the trivially-true Breathe! case (via §5's plausibility
  requirement). It stumbles on Nissenbaum's Pedro Martinez (no causal
  filter) and Huitink's van Nistelrooy (correlated-irrelevant) absent
  further refinement.

## Scope

This file does **not** rebuild vF&I's full designated-goal semantics in
machine-checked form. The two refutation theorems (obvious analysis,
Sæbø's analysis) are stated and proved on minimal `decide`-checkable
scenarios; the positive proposal is given as a structure
(`DesignatedGoal`) with its truth conditions defined, but exhaustive
predictions are left as informal commentary in docstrings. The point
is to make vF&I's empirical landscape grep-able and to fix the
cross-paper bridge to C&M, not to settle the anankastic-conditional
literature.

The example data lives in `Linglib/Data/Examples/vonFintelIatridou2005.json`
and is generated into the `Examples` section below by
`scripts/gen_examples.py vonFintelIatridou2005`. See
`Linglib/Data/Examples/README.md` for the schema and regeneration
convention.
-/

namespace Phenomena.Conditionals.Studies.VonFintelIatridou2005

open Semantics.Modality.Kratzer
open Data.Examples (LinguisticExample SourceRef Judgment)

/-! ## §1. Analytical predicates

The four analytical proposals (obvious, Sæbø, nested, designated-goal)
are predicates on a world type with explicit decidable-predicate
arguments for the relevant propositions. Each concrete vF&I scenario
(Hoboken, Conflicting Goals, ...) instantiates these arguments with
its own predicates. Bundling them into a structure would have hidden
the decidability needed for `decide`-based refutations behind a field
projection; the explicit-argument form keeps each refutation
mechanically verifiable. -/

/-! ## §2. The "Obvious Analysis" and the Hoboken Problem

vF&I eq. (9): `[have to](w)(f)(g)(q) = 1 iff ∀w' ∈ max_{g(w)}(∩f(w)) : q(w') = 1`.
vF&I eq. (10): `[if φ](f) = λw. f(w) ∪ {⟦φ⟧}`.

Combined, the "obvious analysis" of *If you want to go to Harlem, you
have to take the A train* asserts: in the best (per actual goals)
worlds where you want to go to Harlem, you take the A train.

In the Hoboken scenario the actual ordering source ranks worlds by
satisfaction of want(Hoboken). Best want(Harlem)-worlds are then those
that simultaneously achieve Hoboken — i.e., take the PATH train — so
the sentence is predicted false. Empirically the sentence is true
(intuition of vF&I, paper p. 5). -/

/-- Truth conditions for the obvious analysis: the candidate is true
at every accessible-and-want-Harlem world that maximizes
actual-goal-achievement. -/
def obviousAnalysis {W : Type*}
    (accessible wantHyp achieveAct candidate : W → Prop) : Prop :=
  ∀ w : W, accessible w → wantHyp w →
    (∀ w' : W, accessible w' → wantHyp w' → achieveAct w' → achieveAct w) →
    candidate w

/-! ### The Hoboken scenario

Four worlds:
* `w0`: takes A train, achieves Harlem (want-Hoboken false, want-Harlem true)
* `w1`: takes PATH, achieves Hoboken (want-Hoboken true, want-Harlem false)
* `w2`: takes PATH, achieves Hoboken (want-Hoboken true, want-Harlem true)
  — accessible & want-Harlem & best-on-actual-goals
* `w3`: takes A train, achieves Harlem (want-Hoboken false, want-Harlem true)

At evaluation world (where actual goal = Hoboken), the obvious analysis
restricts to want-Harlem worlds {w0, w2, w3}; best by actual-goal is
{w2} (achieves Hoboken). At w2 the candidate (A train) is FALSE.
Therefore the obvious analysis predicts the Harlem Sentence false in
the Hoboken context. -/

namespace HobokenScenario

abbrev W := Fin 4

instance : DecidableEq W := inferInstance

def accessible : W → Prop := fun _ => True
instance : DecidablePred accessible := fun _ => isTrue trivial

def wantHypothetical : W → Prop := fun w => w.val = 0 ∨ w.val = 2 ∨ w.val = 3
instance : DecidablePred wantHypothetical := fun w => by unfold wantHypothetical; infer_instance

def wantActual : W → Prop := fun w => w.val = 1 ∨ w.val = 2
instance : DecidablePred wantActual := fun w => by unfold wantActual; infer_instance

def achieveHypothetical : W → Prop := fun w => w.val = 0 ∨ w.val = 3
instance : DecidablePred achieveHypothetical := fun w => by unfold achieveHypothetical; infer_instance

def achieveActual : W → Prop := fun w => w.val = 1 ∨ w.val = 2
instance : DecidablePred achieveActual := fun w => by unfold achieveActual; infer_instance

def takeCandidate : W → Prop := fun w => w.val = 0 ∨ w.val = 3
instance : DecidablePred takeCandidate := fun w => by unfold takeCandidate; infer_instance

def takeAlternative : W → Prop := fun w => w.val = 1 ∨ w.val = 2
instance : DecidablePred takeAlternative := fun w => by unfold takeAlternative; infer_instance

end HobokenScenario

/-- **Refutation theorem**: the Hoboken scenario falsifies the
obvious analysis. At w2 (want-Harlem and best-on-actual-goals) the
candidate (A train) is false. -/
theorem hoboken_refutes_obvious :
    ¬ obviousAnalysis
        HobokenScenario.accessible
        HobokenScenario.wantHypothetical
        HobokenScenario.achieveActual
        HobokenScenario.takeCandidate := by
  intro h
  have h2 := h ⟨2, by decide⟩ (by decide) (by decide)
    (by intro w' _ _ _; decide)
  exact absurd h2 (by decide)

/-! ## §3. Sæbø 2001's Analysis and the Conflicting Goals refutation

@cite{saebo-2001} modifies the ordering source: instead of adding the
*if*-clause proposition to the modal base, add it to the ordering source.
vF&I formalize this as `g⁺(w) := g(w) ∪ {⟦want-Harlem⟧}`. The modal
quantifies over best worlds in the modal base under g⁺.

This avoids the basic Hoboken Problem when the actual ordering source
contains *want-Hoboken*: the new ordering source augments preferences
with want-Harlem, so best worlds satisfy both goals — typically the A
train (Harlem direction). But:

* it is **non-compositional** (vF&I §4.2): want has to be "zapped" so
  the proposition added to g is `go-to-Harlem`, not `want-go-to-Harlem`;
* and it fails when actual and hypothetical goals are **jointly
  satisfiable but conflicting** in the *concrete* scenario, as in
  vF&I (13) (Hoboken-for-Sæbø) and vF&I (22) (mayor/pub). -/

/-- Truth conditions for Sæbø's analysis. Quantifies over best worlds
where both the actual goal and the hypothetical goal-achievement are
ranked together. -/
def saeboAnalysis {W : Type*}
    (accessible achieveAct achieveHyp candidate : W → Prop) : Prop :=
  ∀ w : W, accessible w →
    (∀ w' : W, accessible w' →
       ((achieveAct w' ∧ achieveHyp w') →
        (achieveAct w ∧ achieveHyp w))) →
    candidate w

/-! ### The Conflicting Goals scenario

Adapted from vF&I (13)/(22). Five worlds:
* `w0`: takes A, achieves Harlem only (no Hoboken, no mayor-goal)
* `w1`: takes PATH, achieves Hoboken only
* `w2`: takes A, achieves both Harlem and Hoboken — best under Sæbø
* `w3`: takes PATH, achieves both Harlem and Hoboken — best under Sæbø
* `w4`: takes neither, achieves neither

Under Sæbø, the best-under-`g⁺` set is `{w2, w3}` (both maximize
joint goal-achievement). At w3 you take PATH, not A. Sæbø therefore
predicts the Harlem sentence false; vF&I report it as true. -/

namespace ConflictingGoalsScenario

abbrev W := Fin 5

instance : DecidableEq W := inferInstance

def accessible : W → Prop := fun _ => True
instance : DecidablePred accessible := fun _ => isTrue trivial

def achieveHypothetical : W → Prop := fun w => w.val = 0 ∨ w.val = 2 ∨ w.val = 3
instance : DecidablePred achieveHypothetical := fun w => by unfold achieveHypothetical; infer_instance

def achieveActual : W → Prop := fun w => w.val = 1 ∨ w.val = 2 ∨ w.val = 3
instance : DecidablePred achieveActual := fun w => by unfold achieveActual; infer_instance

def takeCandidate : W → Prop := fun w => w.val = 0 ∨ w.val = 2
instance : DecidablePred takeCandidate := fun w => by unfold takeCandidate; infer_instance

def takeAlternative : W → Prop := fun w => w.val = 1 ∨ w.val = 3
instance : DecidablePred takeAlternative := fun w => by unfold takeAlternative; infer_instance

def wantHypothetical : W → Prop := fun _ => True
instance : DecidablePred wantHypothetical := fun _ => isTrue trivial

def wantActual : W → Prop := fun _ => True
instance : DecidablePred wantActual := fun _ => isTrue trivial

end ConflictingGoalsScenario

/-- **Refutation theorem**: the Conflicting Goals scenario falsifies
Sæbø's analysis. World `w3` achieves both goals but takes the
alternative (PATH), so it is a best-world counterexample to the
candidate-uniform prediction. -/
theorem conflictingGoals_refutes_saebo :
    ¬ saeboAnalysis
        ConflictingGoalsScenario.accessible
        ConflictingGoalsScenario.achieveActual
        ConflictingGoalsScenario.achieveHypothetical
        ConflictingGoalsScenario.takeCandidate := by
  intro h
  have h3 := h ⟨3, by decide⟩ (by decide)
    (by intro w' _ _; decide)
  exact absurd h3 (by decide)

/-! ## §4. Nested Modality

vF&I §5 propose that the *if*-clause does not modify the lower
teleological modal at all — instead, the *if*-clause restricts an
**additional covert necessity modal** scoping over the teleological
modal:

`[ NEC if you want to go to Harlem ] [ have-to (you take the A train) ]`

This survives the Hoboken Problem (the covert outer modal takes us to
worlds where you want Harlem; the inner have-to then operates on the
*actual* goals at those worlds, which include want-Harlem). It fails
on the Conflicting Goals scenario for analogous reasons, and on
Huitink's van Nistelrooy (correlated-irrelevant) scenario.

We do not give a full formalization here; the key point is that the
shared failure on conflicting-goal scenarios already motivates the
Designated Goals move (§5). -/

/-! ## §5. The Designated Goals proposal

vF&I §6 propose distinguishing a **designated goal** from ancillary
considerations. The to-clause / if-clause supplies the designated goal;
*have-to* and *ought-to* differ in exhaustification:

* `to p, have-to q`: q at every world (in the modal base) where p is
  achieved.
* `to p, ought-to q`: q at every world that maximizes the ancillary
  ordering source restricted to worlds where p is achieved.

These differ exactly in @cite{sloman-1970}'s sense: *have-to* "picks
out the only candidate"; *ought-to* "says what is best". The
have-to entails ought-to, and ought-to signals there are alternatives. -/

/-- @cite{vonfintel-iatridou-2005} §6 designated-goal parameter for a
teleological modal. The `goal` is the to-clause / if-clause–supplied
proposition; `ancillary` is the ordering source for ranking goal-achieving
worlds. -/
structure DesignatedGoal (W : Type*) where
  /-- The designated goal: a proposition the addressee is taken to pursue. -/
  goal : W → Prop
  /-- Ancillary considerations: a Kratzer ordering source over worlds. -/
  ancillary : OrderingSource W
  /-- The (circumstantial) modal base. -/
  modalBase : ModalBase W

/-- vF&I (24a): *to p, ought-to q* — q at every ancillary-best
goal-achieving world. -/
def oughtTo {W : Type*} (dg : DesignatedGoal W) (q : W → Prop) (w : W) : Prop :=
  ∀ w' : W, w' ∈ bestWorlds dg.modalBase
                  (fun v => dg.ancillary v ++ [dg.goal]) w →
    q w'

/-- vF&I (24b): *to p, have-to q* — q at every goal-achieving world
in the modal base. The exhaustification (no ranking over the goal
slice) is the formal counterpart of Sloman's "only candidate". -/
def haveTo {W : Type*} (dg : DesignatedGoal W) (q : W → Prop) (w : W) : Prop :=
  ∀ w' : W, w' ∈ accessibleWorlds dg.modalBase w → dg.goal w' → q w'

/-- @cite{sloman-1970} / @cite{vonfintel-iatridou-2005} §6: have-to is
strictly stronger than ought-to. Stated as a structural inequality:
have-to-q quantifies over a (typically larger) set than ought-to-q does. -/
theorem haveTo_implies_oughtTo_structurally {W : Type*}
    (dg : DesignatedGoal W) (q : W → Prop) (w : W)
    (hHave : haveTo dg q w)
    (hBestSubset : ∀ w',
      w' ∈ bestWorlds dg.modalBase
              (fun v => dg.ancillary v ++ [dg.goal]) w →
      w' ∈ accessibleWorlds dg.modalBase w ∧ dg.goal w') :
    oughtTo dg q w := by
  intro w' hBest
  obtain ⟨hAcc, hGoal⟩ := hBestSubset w' hBest
  exact hHave w' hAcc hGoal

/-! ## §6. Cross-reference to @cite{chung-mascarenhas-2024}

C&M's `mustCM` operator (`Phenomena/Modality/Studies/ChungMascarenhas2024.lean`)
realises @cite{sloman-1970}'s "only candidate" condition as an
**exhaustification clause** on expected values:

> `mustCM φ` iff `E[μ_R ∣ φ] > θ ∧ ∀ψ ∈ Alt(φ). E[μ_R ∣ ψ] ≤ θ`.

The first conjunct is the strong-permissibility condition (φ
achieves the goal well enough); the second is the only-candidate
condition (no alternative does). Under the deontic / teleological
flavor `R = R_D = {goal-achievement-propositions}`, this directly
maps onto vF&I's *have-to* truth conditions: φ has to be the unique
good-enough way of achieving the designated goal.

**What C&M handles cleanly:**
* Harlem base case (`vFI2005_1_harlem`, `vFI2005_4_harlemPurpose`).
* Burdick's hot chocolate (`vFI2005_28_burdicks`) via contextually
  supplied `R`.
* Trivially-true Breathe (`vFI2005_34c_harlemBreathe`) via §5
  plausibility requirement on `R`.
* Sloman's have-to-vs-ought-to (`vFI2005_23_slomanOughtNot`,
  `vFI2005_p13_londonByNoon`) by dropping the exhaustification clause
  for ought-to.

**What C&M doesn't dissolve:**
* Pedro Martinez (`vFI2005_36_pedroMartinez`): C&M's `R` is a flat set
  of propositions, no causal-essentialness filter. Nissenbaum's
  insight (that the to-clause requires the consequent to be an
  *essential part of a way of achieving* the goal) is not in C&M.
* Van Nistelrooy (`vFI2005_p12_vanNistelrooy`): correlated-irrelevant
  preferences enter `R` and skew the expected value.

These remain open puzzles for the expected-value approach. -/

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

end Phenomena.Conditionals.Studies.VonFintelIatridou2005
