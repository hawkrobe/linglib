import Linglib.Theories.Semantics.Attitudes.Representationality
import Linglib.Theories.Semantics.Attitudes.Preferential
import Linglib.Theories.Semantics.Attitudes.Doxastic
import Linglib.Core.Agent.Emotion

/-!
# Anand & Hacquard (2013): Epistemics and Attitudes
@cite{anand-hacquard-2013}

*Semantics & Pragmatics* 6, Article 8: 1–59.

## Summary

This paper investigates the distribution of epistemic modals (might, must)
in the complements of attitude verbs across French, Italian, and Spanish.
The central finding:

1. Epistemics are fully acceptable under **attitudes of acceptance**
   (doxastics, argumentatives, semifactives) but degraded under
   **desideratives** and **directives**.

2. **Emotive doxastics** (hope, fear) and **dubitatives** (doubt) show a
   mixed pattern: they license epistemic *possibility* (might) but not
   epistemic *necessity* (must).

## Proposal

Two proposals are combined:

**About epistemics** (@cite{yalcin-2007}, @cite{hacquard-2006}): Epistemics
quantify over an information state parameter S, obtained by anaphora
to the embedding attitude.

**About attitudes** (@cite{bolinger-1968}, @cite{villalta-2008}):
- Representational attitudes (believe, say, know) provide an information
  state S = DOX(x,w) — epistemics are licensed.
- Non-representational attitudes (want, demand) use comparative
  semantics with S = ∅ — epistemics are trivial/contradictory.
- Hybrid attitudes (hope, fear, doubt) have both components: the
  representational component licenses possibility epistemics, but the
  uncertainty condition blocks necessity epistemics.

## Connection to BToM

The hybrid structure of emotive doxastics maps directly onto BToM
inference (@cite{baker-jara-ettinger-saxe-tenenbaum-2017}):
- Doxastic component = belief marginal P(b | a)
- Preference component = desire marginal P(d | a)
- Uncertainty condition = non-extreme credence

This bridges @cite{anand-hacquard-2013}'s attitude semantics with
@cite{houlihan-kleiman-weiner-hewitt-tenenbaum-saxe-2023}'s emotion
appraisal architecture: emotive doxastics ARE prospective emotions
computed from BToM marginals.
-/

namespace AnandHacquard2013

open Semantics.Attitudes.Representationality
open Semantics.Attitudes.Preferential
open Semantics.Attitudes.Doxastic

-- ════════════════════════════════════════════════════════════════
-- § 1. Empirical Data: Acceptability Ratings (Table 4)
-- ════════════════════════════════════════════════════════════════

/-!
## Cross-Romance Survey Data

Seven-point acceptability ratings (1 = unacceptable, 7 = completely
acceptable) for epistemic modals under attitude verbs, pooled across
French (n=31), Italian (n=11), and Spanish (n=21).

### Table 4: Pooled Descriptive Statistics (mean (sd) / median)

|             | des/direct | emo dox | dubitative | semifactive | accept | Mean       |
|-------------|-----------|---------|------------|-------------|--------|------------|
| **might**   | 3.5/3     | 5.1/6  | 6.1/7      | 6.1/7       | 6.4/7  | 5.4 (1.8)/6|
| **must**    | 1.9/1     | 2.7/2  | 3.1/2      | 5.6/6       | 6.0/7  | 3.9 (1.7)/4|
| **probable**| 2.4/3     | 4.2/5  | 4.8/6      | 5.6/7       | 6.2/7  | 5.0 (1.9)/5|

The critical contrasts:
- Acceptance/semifactive: might ≈ must (both high)
- Des/directive: might ≈ must (both low)
- Emotive doxastic/dubitative: might >> must

We use `AttitudeClass` from Representationality.lean directly (7 classes)
rather than defining a study-local enum. The survey collapses some
classes (doxastics ≈ argumentatives, desideratives ≈ directives), but the
theory predicts the same licensing for collapsed classes — which we verify.
-/

/-- Acceptability judgment: acceptable (median ≥ 5) or degraded. -/
inductive Acceptability where
  | acceptable  -- median ≥ 5
  | degraded    -- median ≤ 3
  deriving DecidableEq, Repr

/-- Observed acceptability from the survey data, indexed by the full
`AttitudeClass` from Representationality.lean. Argumentatives pattern
with doxastics; directives pattern with desideratives. -/
def observedAcceptability : AttitudeClass → EpistemicForce → Acceptability
  | .doxastic,        .possibility  => .acceptable
  | .doxastic,        .necessity    => .acceptable
  | .argumentative,   .possibility  => .acceptable
  | .argumentative,   .necessity    => .acceptable
  | .semifactive,     .possibility  => .acceptable
  | .semifactive,     .necessity    => .acceptable
  | .desiderative,    .possibility  => .degraded
  | .desiderative,    .necessity    => .degraded
  | .directive,       .possibility  => .degraded
  | .directive,       .necessity    => .degraded
  | .emotiveDoxastic, .possibility  => .acceptable
  | .emotiveDoxastic, .necessity    => .degraded
  | .dubitative,      .possibility  => .acceptable
  | .dubitative,      .necessity    => .degraded

/-- Predicted licensing derived from `AttitudeClass.licensesEpistemic`
(Representationality.lean). No stipulation — the prediction follows
from the representationality classification. -/
def predictedAcceptability (att : AttitudeClass) (force : EpistemicForce) :
    Acceptability :=
  if att.LicensesEpistemic force then .acceptable else .degraded

-- ════════════════════════════════════════════════════════════════
-- § 2. Theory Matches Data
-- ════════════════════════════════════════════════════════════════

/-- The representationality theory correctly predicts all 14 cells
(7 attitude classes × 2 epistemic forces). -/
theorem theory_matches_data :
    ∀ att : AttitudeClass, ∀ force : EpistemicForce,
    predictedAcceptability att force = observedAcceptability att force := by
  intro att force
  cases att <;> cases force <;> rfl

-- ════════════════════════════════════════════════════════════════
-- § 3. Information State Semantics (Yalcin's S parameter)
-- ════════════════════════════════════════════════════════════════

/-!
## Epistemic Modals as Information-State Quantifiers

Following @cite{yalcin-2007} and @cite{veltman-1996}, epistemic modals
quantify over an information state parameter S:

    ⟦might φ⟧^{c,w,S,g} = 1 iff ∃w' ∈ S: ⟦φ⟧^{c,w',S,g} = 1
    ⟦must φ⟧^{c,w,S,g} = 1 iff ∀w' ∈ S: ⟦φ⟧^{c,w',S,g} = 1

Attitude verbs update S with their quantificational domain:

    ⟦att φ⟧^{c,w,S,g} = λx. ∀w' ∈ S': ⟦φ⟧^{c,w',S',g} = 1
    where S' = quantificational domain provided by att

For representational attitudes: S' = DOX(x,w) (non-trivial)
For non-representational attitudes: S' = ∅ (trivial → tautology/contradiction)
-/

variable {W : Type*} [DecidableEq W]

/-- Information state: a set of worlds (represented as a list). -/
abbrev InfoState (W : Type*) := List W

/-- Epistemic possibility over information state S:
    ⟦might φ⟧_S = ∃w' ∈ S: φ(w') -/
def mightS (S : InfoState W) (φ : W → Prop) : Prop :=
  ∃ w ∈ S, φ w

instance {S : InfoState W} {φ : W → Prop} [DecidablePred φ] :
    Decidable (mightS S φ) := by
  unfold mightS; infer_instance

/-- Epistemic necessity over information state S:
    ⟦must φ⟧_S = ∀w' ∈ S: φ(w') -/
def mustS (S : InfoState W) (φ : W → Prop) : Prop :=
  ∀ w ∈ S, φ w

instance {S : InfoState W} {φ : W → Prop} [DecidablePred φ] :
    Decidable (mustS S φ) := by
  unfold mustS; infer_instance

/-- Non-triviality presupposition (@cite{geurts-2005}):
    epistemics presuppose their modal base is non-trivial. -/
def nonTrivial (S : InfoState W) : Prop := S ≠ []

instance {S : InfoState W} : Decidable (nonTrivial S) := by
  unfold nonTrivial; infer_instance

/-- Epistemic possibility is defined (non-trivial) whenever S ≠ ∅. -/
theorem might_defined_iff_nontrivial (S : InfoState W) (φ : W → Prop) [DecidablePred φ]
    (_h : nonTrivial S) :
    mightS S φ ∨ ¬ mightS S φ := by
  exact Decidable.em _

/-- With empty S, might is trivially false — yielding infelicity. -/
theorem might_empty (φ : W → Prop) : ¬ mightS ([] : InfoState W) φ := by
  simp [mightS]

/-- With empty S, must is trivially true — yielding infelicity. -/
theorem must_empty (φ : W → Prop) : mustS ([] : InfoState W) φ := by
  simp [mustS]

-- ════════════════════════════════════════════════════════════════
-- § 4. Attitude Embedding: S-Update
-- ════════════════════════════════════════════════════════════════

/-- Representational attitude embedding: S' = DOX(x,w).
    The doxastic alternatives form the information state that
    embedded epistemics quantify over. -/
def representationalS {E : Type*} (R : AccessRel W E) [∀ a w w', Decidable (R a w w')]
    (agent : E) (w : W) (worlds : List W) : InfoState W :=
  worlds.filter (fun w' => decide (R agent w w'))

/-- Non-representational attitude embedding: S' = ∅.
    Comparative semantics provides no information state. -/
def nonRepresentationalS : InfoState W := []

/-- Representational attitudes yield non-trivial information states
    (when there is at least one accessible world). -/
theorem representational_nontrivial {E : Type*} (R : AccessRel W E)
    [∀ a w w', Decidable (R a w w')]
    (agent : E) (w : W) (worlds : List W)
    (h : ∃ w' ∈ worlds, R agent w w') :
    nonTrivial (representationalS R agent w worlds) := by
  obtain ⟨w', hw'_in, hw'_acc⟩ := h
  unfold nonTrivial representationalS
  intro hempty
  have hmem : w' ∈ worlds.filter (fun w' => decide (R agent w w')) :=
    List.mem_filter.mpr ⟨hw'_in, by simp [hw'_acc]⟩
  rw [hempty] at hmem
  cases hmem

/-- Non-representational attitudes yield trivial information states. -/
theorem nonRepresentational_trivial :
    ¬ nonTrivial (nonRepresentationalS : InfoState W) := by
  simp [nonTrivial, nonRepresentationalS]

-- ════════════════════════════════════════════════════════════════
-- § 5. Deriving the Distribution
-- ════════════════════════════════════════════════════════════════

/-- Under a representational attitude, embedded `must p` holds iff
    all doxastic alternatives satisfy p — a non-trivial claim. -/
theorem believe_must {E : Type*} (R : AccessRel W E)
    [∀ a w w', Decidable (R a w w')]
    (agent : E) (w : W) (worlds : List W) (p : W → Prop) [DecidablePred p] :
    mustS (representationalS R agent w worlds) p ↔
    boxAt R agent w worlds p := by
  simp only [mustS, representationalS, boxAt,
    List.mem_filter, decide_eq_true_eq]
  constructor
  · intro h w' hw' hR
    exact h w' ⟨hw', hR⟩
  · intro h w' ⟨hw', hR⟩
    exact h w' hw' hR

/-- Under a non-representational attitude, `must p` is trivially true. -/
theorem want_must_trivial (p : W → Prop) :
    mustS (nonRepresentationalS : InfoState W) p := by
  simp [mustS, nonRepresentationalS]

/-- Under a non-representational attitude, `might p` is trivially false. -/
theorem want_might_trivial (p : W → Prop) :
    ¬ mightS (nonRepresentationalS : InfoState W) p := by
  simp [mightS, nonRepresentationalS]

-- ════════════════════════════════════════════════════════════════
-- § 6. Emotive Doxastic Finite Model
-- ════════════════════════════════════════════════════════════════

/-!
## Concrete Demonstration

We instantiate the abstract theory with a finite model demonstrating
the must/might asymmetry under emotive doxastics.

World model: 3 worlds {w₁, w₂, w₃}
- w₁: it is raining
- w₂: it is not raining
- w₃: it is raining (backup)

John's beliefs (DOX): {w₁, w₂} — uncertain whether it's raining.
John's preference: raining worlds preferred to non-raining.

Predictions:
- "John hopes it is raining": ✓ (uncertainty + doxastic + preference)
- "John hopes it might be raining": ✓ (same doxastic assertion)
- "John hopes it must be raining": ✗ (contradicts uncertainty)
-/

inductive RainWorld where
  | raining₁ | notRaining | raining₂
  deriving DecidableEq, Repr

def isRaining : RainWorld → Prop
  | .raining₁ => True
  | .notRaining => False
  | .raining₂ => True

instance : DecidablePred isRaining := fun w => by
  cases w <;> unfold isRaining <;> infer_instance

/-- John's doxastic accessibility: worlds w₁ and w₂ are doxastically
accessible (he's uncertain), w₃ is not. -/
def johnDox : RainWorld → Bool
  | .raining₁ => true
  | .notRaining => true
  | .raining₂ => false

def allRainWorlds : List RainWorld := [.raining₁, .notRaining, .raining₂]

/-- John's doxastic information state -/
def johnS : InfoState RainWorld :=
  allRainWorlds.filter johnDox

theorem johnS_eq : johnS = [.raining₁, .notRaining] := by decide

/-- John's DOX is non-trivial (he has beliefs). -/
theorem john_nontrivial : nonTrivial johnS := by decide

/-- "might be raining" is true in John's DOX — there's a raining world. -/
theorem john_might_rain : mightS johnS isRaining := by decide

/-- "must be raining" is false in John's DOX — there's a non-raining world. -/
theorem john_must_rain : ¬ mustS johnS isRaining := by decide

/-- Uncertainty: both raining and non-raining worlds in DOX. -/
theorem john_uncertain :
    mightS johnS isRaining ∧
    mightS johnS (fun w => ¬ isRaining w) := by
  exact ⟨by decide, by decide⟩

-- ════════════════════════════════════════════════════════════════
-- § 7. BToM Connection: Prospective Emotions = Emotive Doxastics
-- ════════════════════════════════════════════════════════════════

/-!
## The BToM–Emotive Doxastic Bridge

@cite{houlihan-kleiman-weiner-hewitt-tenenbaum-saxe-2023}'s emotion model
computes retrospective appraisals from BToM marginals. We show that
@cite{anand-hacquard-2013}'s emotive doxastic semantics gives the
formal content of *prospective* emotions computed from the same marginals.

The mapping:

| A&H component        | BToM computation                        |
|-----------------------|-----------------------------------------|
| Doxastic assertion    | beliefMarginal: Pr(b \| a) > 0 for b ⊨ φ |
| Uncertainty condition | 0 < Σ_b Pr(b\|a)·⟦φ⟧_b < 1              |
| Preference assertion  | desireMarginal: Σ_d Pr(d\|a)·U(φ,d) > Σ_d Pr(d\|a)·U(¬φ,d) |

This unification means:
- **hope** is a prospective emotion with positive AU (prefers φ-resolution)
- **fear** is a prospective emotion with negative AU (prefers ¬φ-resolution)
- Both require the *same* BToM inference (belief + desire marginals)
- The emotive doxastic lexical semantics IS the readout function for
  prospective emotions, just as the 8-dimensional β vector is the readout
  for retrospective emotions
-/

open Core

/-- Hope holds from uncertainty + positive preference over resolutions. -/
theorem hope_from_uncertainty_and_preference
    (cred : ℚ) (u_true u_false : ℚ)
    (h_pos : 0 < cred) (h_lt_one : cred < 1) (h_pref : u_false < u_true) :
    (ProspectiveAppraisal.mk cred u_true u_false).isHope = true := by
  simp only [ProspectiveAppraisal.isHope, ProspectiveAppraisal.isUncertain,
    decide_eq_true_eq, Bool.and_eq_true]
  exact ⟨⟨h_pos, h_lt_one⟩, h_pref⟩

/-- Fear holds from uncertainty + negative preference over resolutions. -/
theorem fear_from_uncertainty_and_dispreference
    (cred : ℚ) (u_true u_false : ℚ)
    (h_pos : 0 < cred) (h_lt_one : cred < 1) (h_pref : u_true < u_false) :
    (ProspectiveAppraisal.mk cred u_true u_false).isFear = true := by
  simp only [ProspectiveAppraisal.isFear, ProspectiveAppraisal.isUncertain,
    decide_eq_true_eq, Bool.and_eq_true]
  exact ⟨⟨h_pos, h_lt_one⟩, h_pref⟩

/-- The uncertainty condition in the emotive doxastic semantics is the
same as requiring non-extreme credence in the BToM framework:
Pr(φ) > 0 ∧ Pr(φ) < 1 ↔ ∃w' ∈ DOX: φ(w') ∧ ∃w' ∈ DOX: ¬φ(w').

This is the formal content of why necessity epistemics are blocked:
Pr(φ) ≥ θ_must (≈ 1) contradicts Pr(φ) < 1. -/
theorem necessity_contradicts_uncertainty
    (cred : ℚ) (h_high : cred ≥ 1) (h_lt : cred < 1) : False :=
  not_lt.mpr h_high h_lt

end AnandHacquard2013
