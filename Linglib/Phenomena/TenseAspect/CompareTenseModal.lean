import Linglib.Theories.Semantics.Tense.Evidential
import Linglib.Theories.Semantics.Modality.Kernel
import Linglib.Core.Epistemicity
import Mathlib.Data.Fin.Basic

/-!
# Tense–Modal Evidentiality Bridge
@cite{cumming-2026} @cite{von-fintel-gillies-2010} @cite{zheng-2025}

Connects @cite{cumming-2026}'s tense evidential constraint to @cite{von-fintel-gillies-2010} kernel semantics for epistemic `must`. Both phenomena reflect the same
underlying requirement: the speaker's evidence is *indirect* — causally downstream
of the target event but not directly settling it.

## The Parallel

| Cumming (tense)                    | VF&G (modals)                         |
|------------------------------------|---------------------------------------|
| T ≤ A (downstream evidence)        | K doesn't settle φ                    |
| Nonfuture → downstream required    | must → indirectness presupposition     |
| Future → no constraint             | Bare assertion → no presupposition     |
| Direct observation → bare past ok  | Direct evidence → must infelicitous    |

`EvidentialPerspective` (the three temporal orientations) lives in `Features.Evidentiality`;
`EPCondition`/`UPCondition` (the five attested constraint shapes) live in
`Theories/Semantics.Montague/Sentence/Tense/Evidential.lean`.

## Concrete Scenario: Dripping Raincoat

The dripping-raincoat scenario (@cite{zheng-2025}, used in Kernel.lean) provides a
concrete bridge: the raincoat evidence is causally downstream of rain (T ≤ A),
and the kernel {wearingRaincoat} doesn't settle isRaining.

-/

namespace Phenomena.TenseAspect.CompareTenseModal

abbrev World := Fin 4

def allWorlds : List World := [0, 1, 2, 3]

open Semantics.Tense.Evidential
open Semantics.Modality
open Core.Presupposition (PrProp)

-- ════════════════════════════════════════════════════
-- § 1. Raincoat Scenario (parallel to Kernel.lean)
-- ════════════════════════════════════════════════════

/-! The kernel defs in Kernel.lean are private. We redefine equivalent
    propositions over `World4` for the bridge. The world interpretation:
    w0 = raining, w1 = sprinkler (wet but not rain), w2 = dry, w3 = unknown. -/

/-- Wearing a raincoat: true in w0 (rain) and w1 (sprinkler). -/
def wearingRaincoat : World → Prop
  | 0 => True
  | 1 => True
  | _ => False

instance : DecidablePred wearingRaincoat := fun w =>
  match w with
  | 0 => inferInstanceAs (Decidable True)
  | 1 => inferInstanceAs (Decidable True)
  | 2 => inferInstanceAs (Decidable False)
  | 3 => inferInstanceAs (Decidable False)

/-- It is raining: true only in w0. -/
def isRaining : World → Prop
  | 0 => True
  | _ => False

instance : DecidablePred isRaining := fun w =>
  match w with
  | 0 => inferInstanceAs (Decidable True)
  | 1 => inferInstanceAs (Decidable False)
  | 2 => inferInstanceAs (Decidable False)
  | 3 => inferInstanceAs (Decidable False)

/-- The raincoat kernel: K = {wearingRaincoat}. -/
def raincoatK : Kernel World := ⟨[wearingRaincoat]⟩

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

open Core.IntensionalLogic.Premise (propExtension propIntersection)

/-- The raincoat kernel doesn't settle isRaining: K = {wearingRaincoat},
    and wearingRaincoat neither entails nor excludes isRaining. -/
theorem raincoat_not_settled :
    ¬ directlySettlesExplicit raincoatK isRaining := by
  rintro ⟨x, hx, hcase⟩
  rcases List.mem_singleton.mp hx with rfl
  cases hcase with
  | inl h_ent =>
    -- w1 ∈ propExtension wearingRaincoat but ¬ isRaining (1 : World)
    have hw1 : ((1 : World) : World) ∈ propExtension wearingRaincoat :=
      show wearingRaincoat (1 : World) from trivial
    have : isRaining (1 : World) := h_ent (1 : World) hw1
    exact this
  | inr h_exc =>
    -- w0 ∈ propExtension wearingRaincoat AND isRaining (0 : World)
    exact h_exc ⟨(0 : World), show wearingRaincoat (0 : World) from trivial,
                       show isRaining (0 : World) from trivial⟩

/-- **Downstream implies must-defined**: in the raincoat scenario, downstream
    evidence (T ≤ A) co-occurs with the kernel not settling the prejacent.
    This is a concrete theorem over World4 — the general claim (that evidence
    derived from downstream causal effects doesn't individually entail the
    target event) would require formalizing causation. -/
theorem downstream_implies_must_defined :
    downstreamEvidence raincoatFrame ∧
    (kernelMust raincoatK isRaining).presup (0 : World) :=
  ⟨raincoat_downstream, raincoat_not_settled⟩

/-- **Tense–modal evidential parallel**: both Cumming's nonfuture constraint
    and VF&G's `kernelMust` presupposition hold simultaneously for the same
    scenario. The raincoat evidence is downstream (T ≤ A) AND the kernel
    doesn't settle isRaining — so both nonfuture tense ("It rained") and
    `must` ("It must be raining") are felicitous. -/
theorem tense_modal_evidential_parallel :
    -- Cumming: nonfuture tense is felicitous (downstream evidence)
    downstreamEvidence raincoatFrame ∧
    -- VF&G: must is defined (kernel doesn't settle)
    (kernelMust raincoatK isRaining).presup (0 : World) ∧
    -- VF&G: must is true (B_K entails isRaining? No — B_K = {w0, w1})
    -- Actually B_K does NOT entail isRaining (w1 ∈ B_K but ¬isRaining(w1))
    -- So must is defined but FALSE — the speaker doesn't have enough evidence
    -- for "must". This is correct: the raincoat alone doesn't prove rain.
    ¬(kernelMust raincoatK isRaining).assertion (0 : World) := by
  refine ⟨raincoat_downstream, raincoat_not_settled, ?_⟩
  -- ¬ raincoatK.followsFrom isRaining: w1 ∈ B_K (satisfies wearingRaincoat)
  -- but ¬ isRaining (1 : World), so B_K ⊄ ⟦isRaining⟧.
  intro hAll
  have hw1 : ((1 : World) : World) ∈ propIntersection raincoatK.props := by
    intro p hp
    rcases List.mem_singleton.mp hp with rfl
    exact (show wearingRaincoat (1 : World) from trivial)
  exact (hAll hw1 : isRaining (1 : World))

/-- **Direct evidence blocks both**: when evidence is direct (the speaker
    saw the rain), the kernel settles the prejacent. Then:
    - `kernelMust` is *undefined* (presupposition failure)
    - The tense evidential constraint is vacuously satisfied (T ≤ A holds
      trivially when A = T for direct observation)
    - The speaker uses a bare assertion ("It's raining"), not "must"

    Witness: K = {isRaining} directly settles isRaining. -/
private theorem isRaining_settles_isRaining :
    directlySettlesExplicit (⟨[isRaining]⟩ : Kernel World) isRaining := by
  refine ⟨isRaining, by simp, Or.inl ?_⟩
  intro w hw; exact hw

theorem direct_evidence_blocks_both :
    let directK : Kernel World := ⟨[isRaining]⟩
    -- Direct evidence settles the prejacent
    directlySettlesExplicit directK isRaining ∧
    -- Therefore must is undefined (presupposition failure)
    ¬(kernelMust directK isRaining).presup (0 : World) ∧
    -- A direct-observation frame: T = A (saw the rain as it happened)
    let directFrame : EvidentialFrame ℤ :=
      { speechTime := 0, perspectiveTime := 0, referenceTime := 0, eventTime := -1, acquisitionTime := -1 }
    -- Downstream constraint trivially satisfied (T = A → T ≤ A)
    downstreamEvidence directFrame := by
  refine ⟨isRaining_settles_isRaining, ?_, ?_⟩
  · -- ¬ ¬ directlySettlesExplicit ...
    intro h
    exact h isRaining_settles_isRaining
  · show (-1 : ℤ) ≤ -1; omega

-- ════════════════════════════════════════════════════
-- § 4. Epistemic Authority Bridge
-- ════════════════════════════════════════════════════

open Core.Epistemicity
open Features.Evidentiality

/-- Strong assertions (ego + direct) correspond to settling kernels.
    When the speaker has privileged access AND direct evidence, the kernel
    settles the prejacent — 'must' is infelicitous, bare assertion is used. -/
theorem strong_assertion_settles :
    strongAssertion.source = .direct ∧
    strongAssertion.authority = .ego ∧
    -- Concrete witness: direct kernel settles isRaining
    let directK : Kernel World := ⟨[isRaining]⟩
    directlySettlesExplicit directK isRaining :=
  ⟨rfl, rfl, isRaining_settles_isRaining⟩

/-- Inferential claims (nonparticipant + inference) correspond to non-settling
    kernels with must-defined presuppositions — the canonical 'must' profile. -/
theorem inferential_claim_must_profile :
    inferentialClaim.source = .inference ∧
    inferentialClaim.authority = .nonparticipant ∧
    -- Concrete witness: raincoat kernel doesn't settle but must is defined
    ¬ directlySettlesExplicit raincoatK isRaining ∧
    (kernelMust raincoatK isRaining).presup (0 : World) :=
  ⟨rfl, rfl, raincoat_not_settled, raincoat_not_settled⟩

/-- Ego↔direct and nonparticipant↔indirect form natural pairs.
    This is the core glossary insight: epistemic authority and evidential
    source are orthogonal dimensions that CORRELATE but don't reduce. -/
theorem authority_source_correlation :
    strongAssertion.authority = .ego ∧ strongAssertion.source = .direct ∧
    inferentialClaim.authority = .nonparticipant ∧ inferentialClaim.source = .inference := by
  exact ⟨rfl, rfl, rfl, rfl⟩

end Phenomena.TenseAspect.CompareTenseModal
