import Linglib.Theories.TruthConditional.Sentence.Tense.Evidential
import Linglib.Theories.IntensionalSemantics.Modal.Kernel

/-!
# Tense–Modal Evidentiality Bridge

Connects Cumming's (2026) tense evidential constraint to von Fintel & Gillies's
(2010) kernel semantics for epistemic `must`. Both phenomena reflect the same
underlying requirement: the speaker's evidence is *indirect* — causally downstream
of the target event but not directly settling it.

## The Parallel

| Cumming (tense)                    | VF&G (modals)                         |
|------------------------------------|---------------------------------------|
| T ≤ A (downstream evidence)        | K doesn't settle φ                    |
| Nonfuture → downstream required    | must → indirectness presupposition     |
| Future → no constraint             | Bare assertion → no presupposition     |
| Direct observation → bare past ok  | Direct evidence → must infelicitous    |

`EvidentialPerspective` (the three temporal orientations) lives in `Core.Evidence`;
`EPCondition`/`UPCondition` (the five attested constraint shapes) live in
`Theories/TruthConditional/Sentence/Tense/Evidential.lean`.

## Concrete Scenario: Dripping Raincoat

The dripping-raincoat scenario (Zheng 2026, used in Kernel.lean) provides a
concrete bridge: the raincoat evidence is causally downstream of rain (T ≤ A),
and the kernel {wearingRaincoat} doesn't settle isRaining.

## References

- Cumming, S. (2026). Tense and evidence. *L&P* 49:153–175.
- von Fintel, K. & Gillies, A. (2010). Must...stay...strong! *NLS* 18:351–383.
- Zheng, L. (2026). The semantics of Mandarin polar *nandao*-questions. *NLS*.
-/

namespace Comparisons.TenseModalEvidentiality

open TruthConditional.Sentence.Tense.Evidential
open IntensionalSemantics.Modal
open IntensionalSemantics.Attitude.Intensional (World allWorlds)
open Core.Proposition (World4 BProp)

-- ════════════════════════════════════════════════════
-- § 1. Raincoat Scenario (parallel to Kernel.lean)
-- ════════════════════════════════════════════════════

/-! The kernel defs in Kernel.lean are private. We redefine equivalent
    propositions over `World4` for the bridge. The world interpretation:
    w0 = raining, w1 = sprinkler (wet but not rain), w2 = dry, w3 = unknown. -/

/-- Wearing a raincoat: true in w0 (rain) and w1 (sprinkler). -/
def wearingRaincoat : BProp World := λ w =>
  match w with | .w0 => true | .w1 => true | _ => false

/-- It is raining: true only in w0. -/
def isRaining : BProp World := λ w =>
  match w with | .w0 => true | _ => false

/-- The raincoat kernel: K = {wearingRaincoat}. -/
def raincoatK : Kernel := ⟨[wearingRaincoat]⟩

-- ════════════════════════════════════════════════════
-- § 2. Downstream Evidence in the Raincoat Scenario
-- ════════════════════════════════════════════════════

/-- A concrete evidential frame for the raincoat scenario:
    S = 0 (speech time now), T = -2 (rain event in the past),
    R = 0, A = -1 (evidence acquired between event and speech). -/
def raincoatFrame : EvidentialFrame ℤ where
  speechTime := 0
  perspectiveTime := 0
  referenceTime := 0
  eventTime := -2
  acquisitionTime := -1

/-- The raincoat evidence is downstream: T ≤ A (-2 ≤ -1). -/
theorem raincoat_downstream : downstreamEvidence raincoatFrame := by
  show (-2 : ℤ) ≤ -1; omega

-- ════════════════════════════════════════════════════
-- § 3. Bridge Theorems
-- ════════════════════════════════════════════════════

/-- The raincoat kernel doesn't settle isRaining: K = {wearingRaincoat},
    and wearingRaincoat neither entails nor excludes isRaining. -/
theorem raincoat_not_settled :
    directlySettlesExplicit raincoatK isRaining = false := by native_decide

/-- **Downstream implies must-defined**: in the raincoat scenario, downstream
    evidence (T ≤ A) co-occurs with the kernel not settling the prejacent.
    This is a concrete theorem over World4 — the general claim (that evidence
    derived from downstream causal effects doesn't individually entail the
    target event) would require formalizing causation. -/
theorem downstream_implies_must_defined :
    downstreamEvidence raincoatFrame ∧
    (kernelMust raincoatK isRaining).presup .w0 = true := by
  exact ⟨raincoat_downstream, by native_decide⟩

/-- **Tense–modal evidential parallel**: both Cumming's nonfuture constraint
    and VF&G's `kernelMust` presupposition hold simultaneously for the same
    scenario. The raincoat evidence is downstream (T ≤ A) AND the kernel
    doesn't settle isRaining — so both nonfuture tense ("It rained") and
    `must` ("It must be raining") are felicitous. -/
theorem tense_modal_evidential_parallel :
    -- Cumming: nonfuture tense is felicitous (downstream evidence)
    downstreamEvidence raincoatFrame ∧
    -- VF&G: must is defined (kernel doesn't settle)
    (kernelMust raincoatK isRaining).presup .w0 = true ∧
    -- VF&G: must is true (B_K entails isRaining? No — B_K = {w0, w1})
    -- Actually B_K does NOT entail isRaining (w1 ∈ B_K but ¬isRaining(w1))
    -- So must is defined but FALSE — the speaker doesn't have enough evidence
    -- for "must". This is correct: the raincoat alone doesn't prove rain.
    (kernelMust raincoatK isRaining).assertion .w0 = false := by
  exact ⟨raincoat_downstream, by native_decide, by native_decide⟩

/-- **Direct evidence blocks both**: when evidence is direct (the speaker
    saw the rain), the kernel settles the prejacent. Then:
    - `kernelMust` is *undefined* (presupposition failure)
    - The tense evidential constraint is vacuously satisfied (T ≤ A holds
      trivially when A = T for direct observation)
    - The speaker uses a bare assertion ("It's raining"), not "must"

    Witness: K = {isRaining} directly settles isRaining. -/
theorem direct_evidence_blocks_both :
    let directK : Kernel := ⟨[isRaining]⟩
    -- Direct evidence settles the prejacent
    directlySettlesExplicit directK isRaining = true ∧
    -- Therefore must is undefined (presupposition failure)
    (kernelMust directK isRaining).presup .w0 = false ∧
    -- A direct-observation frame: T = A (saw the rain as it happened)
    let directFrame : EvidentialFrame ℤ :=
      { speechTime := 0, perspectiveTime := 0, referenceTime := 0, eventTime := -1, acquisitionTime := -1 }
    -- Downstream constraint trivially satisfied (T = A → T ≤ A)
    downstreamEvidence directFrame := by
  refine ⟨by native_decide, by native_decide, ?_⟩
  show (-1 : ℤ) ≤ -1; omega

end Comparisons.TenseModalEvidentiality
