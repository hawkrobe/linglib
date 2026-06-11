import Linglib.Semantics.Modality.Kratzer.Operators
import Linglib.Data.Examples.Schema
import Linglib.Data.Examples.VonFintelIatridou2005

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

end VonFintelIatridou2005
