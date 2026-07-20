import Linglib.Fragments.English.Tense
import Linglib.Fragments.Korean.Evidentials
import Linglib.Fragments.Slavic.Bulgarian.Evidentials
import Linglib.Semantics.Modality.Kernel
import Linglib.Semantics.Evidential.Epistemicity

/-!
# Cumming (2026): Tense and evidence — verification theorems
[cumming-2026]

Verification theorems for the cross-linguistic nonfuture-downstream
generalization of [cumming-2026]. Paradigm data (the paper's tables
(17)–(20) and (22)) lives in the Fragment files; this file imports them and
proves the empirical predictions.

## Main results

* `nonfuture_downstream`: any paradigm entry whose EP constraint is
  nonfuture entails T ≤ A (downstream evidence), with per-entry
  verification anchors and corollaries
* `future_no_downstream`: future entries impose no downstream requirement
* `korean_te_ney_up_diverge`: -te and -ney present share one EP constraint
  but differ in UP — EP and UP factorize independently in the morphology
* `tense_modal_evidential_parallel`: the tense constraint and
  [von-fintel-gillies-2010]'s `kernelMust` presupposition hold jointly in
  the [zheng-2025] raincoat scenario
-/

namespace Cumming2026

open Tense.Evidential
open English.Tense
open Korean.Evidentials
open Bulgarian.Evidentials

/-! ### Cross-linguistic collection -/

/-- All paradigm entries across the three languages. -/
def allParadigms : List TAMEEntry :=
  English.Tense.allEntries ++
  Korean.Evidentials.allEntries ++
  Bulgarian.Evidentials.allEntries

/-- Nonfuture paradigm entries (across all languages). -/
def nonfutureParadigms : List TAMEEntry :=
  allParadigms.filter (decide ·.IsNonfuture)

/-- Future paradigm entries (across all languages). -/
def futureParadigms : List TAMEEntry :=
  allParadigms.filter (decide ¬ ·.IsNonfuture)

/-! ### Per-entry nonfuture verification -/

/-- English simple past is nonfuture (EP = downstream). -/
theorem simplePast_nonfuture : simplePast.IsNonfuture := by decide

/-- English present progressive is nonfuture (EP = downstream). -/
theorem presentProg_nonfuture : presentProg.IsNonfuture := by decide

/-- Korean -te PAST is nonfuture (EP = strictDownstream). -/
theorem tePast_nonfuture : tePast.IsNonfuture := by decide

/-- Korean -te PRESENT is nonfuture (EP = contemporaneous). -/
theorem tePresent_nonfuture : tePresent.IsNonfuture := by decide

/-- Korean -ney PAST is nonfuture (EP = strictDownstream). -/
theorem neyPast_nonfuture : neyPast.IsNonfuture := by decide

/-- Korean -ney PRESENT is nonfuture (EP = contemporaneous). -/
theorem neyPresent_nonfuture : neyPresent.IsNonfuture := by decide

/-- Bulgarian NFUT + -l is nonfuture (EP = downstream). -/
theorem nfutL_nonfuture : nfutL.IsNonfuture := by decide

/-! ### Master downstream theorem -/

/-- **Generic nonfuture downstream**: any paradigm entry
    whose EP constraint is nonfuture entails T ≤ A (downstream evidence).
    Delegates to `EPCondition.nonfuture_implies_downstream`. -/
theorem nonfuture_downstream (p : TAMEEntry) (f : EvidentialFrame ℤ)
    (h_nf : p.IsNonfuture) (h_ep : p.epConstraint f) :
    downstreamEvidence f :=
  EPCondition.nonfuture_implies_downstream p.ep f h_nf h_ep

/-! ### Per-entry downstream corollaries -/

/-- English simple past EP entails downstream evidence. -/
theorem simplePast_downstream (f : EvidentialFrame ℤ) :
    simplePast.epConstraint f → downstreamEvidence f :=
  nonfuture_downstream simplePast f simplePast_nonfuture

/-- English present progressive EP entails downstream evidence. -/
theorem presentProg_downstream (f : EvidentialFrame ℤ) :
    presentProg.epConstraint f → downstreamEvidence f :=
  nonfuture_downstream presentProg f presentProg_nonfuture

/-- Korean -te PAST EP entails downstream evidence. -/
theorem tePast_downstream (f : EvidentialFrame ℤ) :
    tePast.epConstraint f → downstreamEvidence f :=
  nonfuture_downstream tePast f tePast_nonfuture

/-- Korean -te PRESENT EP entails downstream evidence. -/
theorem tePresent_downstream (f : EvidentialFrame ℤ) :
    tePresent.epConstraint f → downstreamEvidence f :=
  nonfuture_downstream tePresent f tePresent_nonfuture

/-- Korean -ney PAST EP entails downstream evidence. -/
theorem neyPast_downstream (f : EvidentialFrame ℤ) :
    neyPast.epConstraint f → downstreamEvidence f :=
  nonfuture_downstream neyPast f neyPast_nonfuture

/-- Korean -ney PRESENT EP entails downstream evidence. -/
theorem neyPresent_downstream (f : EvidentialFrame ℤ) :
    neyPresent.epConstraint f → downstreamEvidence f :=
  nonfuture_downstream neyPresent f neyPresent_nonfuture

/-- Bulgarian NFUT + -l EP entails downstream evidence. -/
theorem nfutL_downstream (f : EvidentialFrame ℤ) :
    nfutL.epConstraint f → downstreamEvidence f :=
  nonfuture_downstream nfutL f nfutL_nonfuture

/-! ### Future counterexample -/

/-- Future entries do not require downstream evidence: the EP constraint
    is either trivially true (English bare future) or imposes A < T
    (prospective), which is the opposite of T ≤ A. -/
theorem future_no_downstream :
    English.Tense.future.epConstraint ⟨⟨10, 10, 0, 5⟩, 0⟩ ∧
    ¬ downstreamEvidence ⟨⟨10, 10, 0, 5⟩, 0⟩ := by
  refine ⟨(Core.Order.holds_unrestricted _ _).mpr trivial, ?_⟩
  simp [downstreamEvidence]

/-! ### Korean EP/UP factorization -/

/-- **-te and -ney factorize EP from UP** ([cumming-2026], tables (18)–(19)):
    the two present-tense evidentials impose the same EP constraint (T = A)
    but different UP constraints (-te: T < S; -ney: T = S), witnessed in
    both directions. EP and UP vary independently in the morphology. -/
theorem korean_te_ney_up_diverge :
    tePresent.ep = neyPresent.ep ∧
    (∃ f : EvidentialFrame ℤ,
      tePresent.upConstraint f ∧ ¬ neyPresent.upConstraint f) ∧
    (∃ f : EvidentialFrame ℤ,
      neyPresent.upConstraint f ∧ ¬ tePresent.upConstraint f) := by
  refine ⟨rfl, ⟨⟨⟨0, 0, 0, -1⟩, -1⟩, ?_, ?_⟩, ⟨⟨⟨0, 0, 0, 0⟩, 0⟩, ?_, ?_⟩⟩
  · show (-1 : ℤ) < 0; omega
  · show ¬ ((-1 : ℤ) = 0); omega
  · show (0 : ℤ) = 0; rfl
  · show ¬ ((0 : ℤ) < 0); omega

/-! ### Tense-modal evidentiality bridge

[cumming-2026] observes that the "fake future" *will*-forms closely
resemble epistemic *must*: both require the prejacent to follow from the
evidence rather than being directly observed. The
[von-fintel-gillies-2010] kernel semantics states the modal side as a
presupposition that the kernel does not directly settle the prejacent; the
tense side is the nonfuture downstream constraint (T ≤ A). The
[zheng-2025] dripping-raincoat scenario (public in
`Semantics/Modality/Kernel.lean`) witnesses both at once: the raincoat
evidence is causally downstream of the rain, and the kernel
`{wearingRaincoat}` does not settle `isRaining`. -/

open Semantics.Modality
open Intensional.Premise (propIntersection)

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

/-- The raincoat kernel doesn't settle isRaining — the third conjunct of
    [zheng-2025]'s nandao-felicity theorem. -/
theorem raincoat_not_settled :
    ¬ directlySettlesExplicit raincoatK isRaining :=
  raincoat_nandao_felicitous.2.2

/-- **Downstream implies must-defined**: in the raincoat scenario, downstream
    evidence (T ≤ A) co-occurs with the kernel not settling the prejacent. -/
theorem downstream_implies_must_defined :
    downstreamEvidence raincoatFrame ∧
    (kernelMust raincoatK isRaining).presup World.w0 :=
  ⟨raincoat_downstream, raincoat_not_settled⟩

/-- **Tense-modal evidential parallel**: both Cumming's nonfuture constraint
    and VF&G's `kernelMust` presupposition hold simultaneously for the same
    scenario. The raincoat evidence is downstream (T ≤ A) AND the kernel
    doesn't settle isRaining. -/
theorem tense_modal_evidential_parallel :
    downstreamEvidence raincoatFrame ∧
    (kernelMust raincoatK isRaining).presup World.w0 ∧
    ¬(kernelMust raincoatK isRaining).assertion World.w0 := by
  refine ⟨raincoat_downstream, raincoat_not_settled, ?_⟩
  intro hAll
  have hw1 : World.w1 ∈ propIntersection raincoatK.props := by
    intro p hp
    rcases List.mem_singleton.mp hp with rfl
    exact show wearingRaincoat .w1 by decide
  exact (hAll hw1 : isRaining .w1)

private theorem isRaining_settles_isRaining :
    directlySettlesExplicit (⟨[isRaining]⟩ : Kernel World) isRaining := by
  refine ⟨isRaining, by simp, Or.inl ?_⟩
  intro w hw; exact hw

/-- **Direct evidence blocks both**: when evidence is direct, the kernel
    settles the prejacent → `kernelMust` is undefined and downstream is
    trivially satisfied (T = A). Speaker uses bare assertion, not `must`. -/
theorem direct_evidence_blocks_both :
    let directK : Kernel World := ⟨[isRaining]⟩
    directlySettlesExplicit directK isRaining ∧
    ¬(kernelMust directK isRaining).presup World.w0 ∧
    let directFrame : EvidentialFrame ℤ :=
      { speechTime := 0, perspectiveTime := 0, referenceTime := 0,
        eventTime := -1, acquisitionTime := -1 }
    downstreamEvidence directFrame := by
  refine ⟨isRaining_settles_isRaining, ?_, ?_⟩
  · intro h
    exact h isRaining_settles_isRaining
  · show (-1 : ℤ) ≤ -1; omega

/-! ### Epistemic authority bridge -/

open Semantics.Epistemicity

/-- Strong assertions (ego + direct) correspond to settling kernels.
    When the speaker has privileged access AND direct evidence, the
    kernel settles the prejacent — 'must' is infelicitous, bare
    assertion is used. -/
theorem strong_assertion_settles :
    strongAssertion.source = .direct ∧
    strongAssertion.authority = .ego ∧
    let directK : Kernel World := ⟨[isRaining]⟩
    directlySettlesExplicit directK isRaining :=
  ⟨rfl, rfl, isRaining_settles_isRaining⟩

/-- Inferential claims (nonparticipant + inference) correspond to
    non-settling kernels with must-defined presuppositions — the
    canonical 'must' profile. -/
theorem inferential_claim_must_profile :
    inferentialClaim.source = .inference ∧
    inferentialClaim.authority = .nonparticipant ∧
    ¬ directlySettlesExplicit raincoatK isRaining ∧
    (kernelMust raincoatK isRaining).presup World.w0 :=
  ⟨rfl, rfl, raincoat_not_settled, raincoat_not_settled⟩

/-- Ego pairs with direct evidence and nonparticipant with inference in
    the Epistemicity profiles. -/
theorem authority_source_correlation :
    strongAssertion.authority = .ego ∧ strongAssertion.source = .direct ∧
    inferentialClaim.authority = .nonparticipant ∧
    inferentialClaim.source = .inference :=
  ⟨rfl, rfl, rfl, rfl⟩

end Cumming2026
