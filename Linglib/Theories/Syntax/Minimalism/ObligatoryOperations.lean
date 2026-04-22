import Linglib.Theories.Syntax.Minimalism.Agree

/-!
# Obligatory Operations @cite{preminger-2014}
@cite{chomsky-2001}

@cite{preminger-2014} argues that φ-agreement is an **obligatory
operation** that can **fail without crashing** the derivation. This
contrasts with the standard Minimalist view where
unvalued features at the interfaces cause the derivation to crash.

## The Standard Model

Probes carry uninterpretable/unvalued features ([uφ]). If [uφ] reaches
the interfaces (PF/LF) without being valued by Agree, the derivation
crashes. This makes agreement effectively obligatory AND success-
mandatory: any probe must find a matching goal, or the structure is
ungrammatical.

## Preminger's Alternative

Agreement is obligatory — the grammar MUST attempt it — but failure
does NOT crash the derivation:

- At PF: unvalued features receive the Elsewhere exponent (3SG ∅)
- At LF: unvalued features make no semantic contribution (vacuous)
- The derivation converges either way

The key distinction: **obligatoriness** (the probe must search) vs.
**crash-on-failure** (failure to find a goal is fatal). Standard
Minimalism conflates these; Preminger separates them.

## The Derivational Time-Bomb Argument (Ch. 5)

Derivational time-bombs (uninterpretable features that cause crash at
the interface) cannot model obligatory-but-failable agreement because:

1. A time-bomb ([uF]) detonates at the interface if unvalued
2. The system cannot distinguish "probe attempted and failed" from
   "probe was never present"
3. But obligatoriness requires this distinction: a probe that tried
   and failed should produce default morphology, while a probe that
   was never there should produce *no* morphology

## Empirical Evidence

- **Kichean AF**: omnivorous agreement targets whichever argument
  bears the sought feature. If neither does, the default (3SG ∅)
  surfaces — the probe failed without crashing.
- **Dative intervention**: a dative DP blocks the probe but cannot
  be a valid goal (wrong case). The probe fails → default agreement.
- **Icelandic quirky subjects**: dative subject intervenes between T
  and the nominative object → T's probe fails → default 3SG.

All three are instances of the same mechanism: obligatory probing +
failure without crash → default morphology.

-/

namespace Minimalism

-- ============================================================================
-- § 1: Agreement Models
-- ============================================================================

/-- Two models of what happens when a probe fails to find a matching
    goal.

    - **crashOnFailure**: the standard Minimalist model. Unvalued
      features at the interfaces cause the derivation to crash.
      Agreement is both obligatory and success-mandatory.
    - **obligatoryNocrash**: Preminger's model. Agreement is obligatory
      (the probe must attempt to Agree), but failure to find a goal
      does NOT crash — default morphology surfaces instead. -/
inductive AgreementModel where
  /-- Standard: unvalued features at interface → crash. -/
  | crashOnFailure
  /-- Preminger: obligatory but failure → default, no crash. -/
  | obligatoryNocrash
  deriving DecidableEq, Repr

-- ============================================================================
-- § 2: Probe Outcomes
-- ============================================================================

/-- The outcome of an obligatory probing operation.

    - **valued**: the probe found a goal and was valued by its φ-features.
    - **unvalued**: the probe attempted but found no suitable goal.
      In the crash model, this crashes. In the obligatory-no-crash
      model, the derivation continues with default morphology. -/
inductive ProbeOutcome where
  /-- Probe successfully agreed with a goal. -/
  | valued
  /-- Probe attempted but found no suitable goal. -/
  | unvalued
  deriving DecidableEq, Repr

-- ============================================================================
-- § 3: Convergence
-- ============================================================================

/-- Does the derivation converge given a probe outcome?
    In the crash model: only if the probe was valued.
    In the obligatory-no-crash model: always. -/
def derivationConverges (model : AgreementModel) (outcome : ProbeOutcome) : Bool :=
  match model, outcome with
  | .crashOnFailure, .unvalued => false
  | _, _ => true

/-- Does this outcome yield default morphology?
    Only unvalued probes produce the default (Elsewhere entry). -/
def ProbeOutcome.yieldsDefault : ProbeOutcome → Bool
  | .valued => false
  | .unvalued => true

-- ============================================================================
-- § 4: Morphological Realization
-- ============================================================================

/-- What surfaces at PF for a given probe outcome.
    - Valued probe: agreement morphology reflecting the goal's features.
    - Unvalued probe: the Elsewhere entry (3SG ∅ in Kaqchikel).

    In the crash model, the unvalued case never reaches PF (the
    derivation crashes first). In Preminger's model, it does, and
    the Elsewhere entry surfaces. -/
inductive PFRealization where
  /-- Agreement morphology reflecting the valued features. -/
  | agreement
  /-- Default/Elsewhere morphology (3SG ∅ in Kichean). -/
  | elsewhere
  deriving DecidableEq, Repr

/-- Map a probe outcome to its PF realization. -/
def ProbeOutcome.pfRealization : ProbeOutcome → PFRealization
  | .valued => .agreement
  | .unvalued => .elsewhere

-- ============================================================================
-- § 5: Verification
-- ============================================================================

/-- The two models agree when the probe succeeds: both converge. -/
theorem models_agree_on_success :
    derivationConverges .crashOnFailure .valued = true ∧
    derivationConverges .obligatoryNocrash .valued = true := ⟨rfl, rfl⟩

/-- The two models diverge when the probe fails: the crash model
    does not converge, but the obligatory-no-crash model does. -/
theorem models_diverge_on_failure :
    derivationConverges .crashOnFailure .unvalued = false ∧
    derivationConverges .obligatoryNocrash .unvalued = true := ⟨rfl, rfl⟩

/-- The crash model requires success for convergence. -/
theorem crash_requires_success (outcome : ProbeOutcome) :
    derivationConverges .crashOnFailure outcome = true ↔
    outcome = .valued := by
  cases outcome <;> simp [derivationConverges]

/-- The obligatory-no-crash model always converges. -/
theorem obligatory_always_converges (outcome : ProbeOutcome) :
    derivationConverges .obligatoryNocrash outcome = true := by
  cases outcome <;> rfl

/-- Failed probes yield default morphology (the Elsewhere entry). -/
theorem failed_yields_default :
    ProbeOutcome.unvalued.yieldsDefault = true := rfl

/-- Successful probes do NOT yield default morphology. -/
theorem success_no_default :
    ProbeOutcome.valued.yieldsDefault = false := rfl

/-- In the obligatory-no-crash model, failed agreement produces the
    Elsewhere PF realization — not a crash. This is Preminger's
    central empirical prediction (Ch. 5). -/
theorem failure_produces_elsewhere :
    derivationConverges .obligatoryNocrash .unvalued = true ∧
    ProbeOutcome.unvalued.pfRealization = .elsewhere := ⟨rfl, rfl⟩

-- ============================================================================
-- § 6: Obligatoriness vs. Optionality
-- ============================================================================

/-- Whether a probe was present in the derivation.
    Obligatoriness means: if the functional head is projected, its
    probe MUST be present. The question is what happens when the
    probe fails — not whether it can be absent. -/
inductive ProbePresence where
  /-- Probe is present (functional head projected). -/
  | present : ProbeOutcome → ProbePresence
  /-- No probe (functional head not projected). -/
  | absent
  deriving DecidableEq, Repr

/-- The three-way distinction that Preminger argues for:
    1. Probe present + valued → agreement morphology
    2. Probe present + unvalued → default morphology (NOT crash)
    3. Probe absent → no agreement morphology at all

    The crash model collapses (2) into ungrammaticality, losing the
    distinction between (2) and (3). -/
def ProbePresence.realization : ProbePresence → Option PFRealization
  | .present outcome => some outcome.pfRealization
  | .absent => none

/-- Present+unvalued and absent are observationally distinct:
    the former produces default morphology, the latter produces
    no morphology. The crash model cannot capture this. -/
theorem present_unvalued_vs_absent :
    ProbePresence.realization (.present .unvalued) ≠
    ProbePresence.realization .absent := by decide

-- ============================================================================
-- § 7: Connecting Agree to Probe Outcomes
-- ============================================================================

/-- Run an Agree attempt and return the outcome.

    This bridges the Agree mechanism (`applyAgree`) with the failure model
    (`ProbeOutcome`): if valuation succeeds, the probe was valued; otherwise
    it attempted but failed. This is the missing link between the Agree
    operation (which returns `Option FeatureBundle`) and Preminger's
    obligatory-but-failable model (which distinguishes valued from unvalued).

    The key insight: the Agree mechanism itself
    doesn't decide what happens on failure — that's the job of the
    `AgreementModel`. This function extracts the binary outcome so the
    model can decide convergence. -/
def attemptAgree (probeFeats goalFeats : FeatureBundle) (ftype : FeatureVal) : ProbeOutcome :=
  match applyAgree probeFeats goalFeats ftype with
  | some _ => .valued
  | none => .unvalued

/-- Run Agree under a given model and return convergence + PF realization. -/
def agreeWithModel (model : AgreementModel) (probeFeats goalFeats : FeatureBundle)
    (ftype : FeatureVal) : Bool × PFRealization :=
  let outcome := attemptAgree probeFeats goalFeats ftype
  (derivationConverges model outcome, outcome.pfRealization)

/-- Successful Agree yields a valued probe outcome. -/
theorem attemptAgree_valued {pf gf : FeatureBundle} {ft : FeatureVal} {result : FeatureBundle}
    (h : applyAgree pf gf ft = some result) :
    attemptAgree pf gf ft = .valued := by
  simp only [attemptAgree, h]

/-- Failed Agree yields an unvalued probe outcome. -/
theorem attemptAgree_unvalued {pf gf : FeatureBundle} {ft : FeatureVal}
    (h : applyAgree pf gf ft = none) :
    attemptAgree pf gf ft = .unvalued := by
  simp only [attemptAgree, h]

/-- Under the obligatory-no-crash model, Agree always converges
    regardless of whether the probe found a goal. -/
theorem agreeWithModel_obligatory_converges (pf gf : FeatureBundle) (ft : FeatureVal) :
    (agreeWithModel .obligatoryNocrash pf gf ft).1 = true := by
  simp only [agreeWithModel]
  exact obligatory_always_converges _

end Minimalism
