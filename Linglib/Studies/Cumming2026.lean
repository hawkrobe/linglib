import Linglib.Fragments.English.Tense
import Linglib.Fragments.Korean.Evidentials
import Linglib.Fragments.Slavic.Bulgarian.Evidentials
import Linglib.Semantics.Modality.Kernel
import Linglib.Semantics.Evidential.Epistemicity
import Mathlib.Data.Fin.Basic

/-!
# [cumming-2026] Verification Theorems
[cumming-2026]

Verification theorems for the cross-linguistic nonfuture downstream
generalization from [cumming-2026]. Paradigm data
lives in Fragment files; this file imports them and proves the empirical
predictions.

## Key Results

1. `nonfuture_downstream`: generic master theorem — any paradigm entry whose
   EP constraint is nonfuture entails T ≤ A (downstream evidence)
2. Per-entry corollaries: one-liner applications of the generic lemma
3. Per-entry `isNonfuture` verification: breaks if EP changed
4. `future_no_downstream`: future entries do not require downstream evidence
5. `korean_te_ney_ep_diverge`: EP and UP factorize independently in Korean

-/

namespace Cumming2026

open Tense.Evidential
open English.Tense
open Korean.Evidentials
open Bulgarian.Evidentials

-- ════════════════════════════════════════════════════
-- § 1. Cross-Linguistic Collection
-- ════════════════════════════════════════════════════

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

-- ════════════════════════════════════════════════════
-- § 2. Per-Entry IsNonfuture Verification
-- ════════════════════════════════════════════════════

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

-- ════════════════════════════════════════════════════
-- § 3. Master Downstream Theorem
-- ════════════════════════════════════════════════════

/-- **Generic nonfuture downstream**: any paradigm entry
    whose EP constraint is nonfuture entails T ≤ A (downstream evidence).
    Delegates to `EPCondition.nonfuture_implies_downstream`. -/
theorem nonfuture_downstream (p : TAMEEntry) (f : EvidentialFrame ℤ)
    (h_nf : p.IsNonfuture) (h_ep : p.epConstraint f) :
    downstreamEvidence f :=
  EPCondition.nonfuture_implies_downstream p.ep f h_nf h_ep

-- ════════════════════════════════════════════════════
-- § 4. Per-Entry Downstream Corollaries
-- ════════════════════════════════════════════════════

/-- English simple past EP entails downstream evidence. -/
theorem simplePast_downstream (f : EvidentialFrame ℤ) :
    simplePast.epConstraint f → downstreamEvidence f :=
  EPCondition.nonfuture_implies_downstream .downstream f (by decide)

/-- English present progressive EP entails downstream evidence. -/
theorem presentProg_downstream (f : EvidentialFrame ℤ) :
    presentProg.epConstraint f → downstreamEvidence f :=
  EPCondition.nonfuture_implies_downstream .downstream f (by decide)

/-- Korean -te PAST EP entails downstream evidence. -/
theorem tePast_downstream (f : EvidentialFrame ℤ) :
    tePast.epConstraint f → downstreamEvidence f :=
  EPCondition.nonfuture_implies_downstream .strictDownstream f (by decide)

/-- Korean -te PRESENT EP entails downstream evidence. -/
theorem tePresent_downstream (f : EvidentialFrame ℤ) :
    tePresent.epConstraint f → downstreamEvidence f :=
  EPCondition.nonfuture_implies_downstream .contemporaneous f (by decide)

/-- Korean -ney PAST EP entails downstream evidence. -/
theorem neyPast_downstream (f : EvidentialFrame ℤ) :
    neyPast.epConstraint f → downstreamEvidence f :=
  EPCondition.nonfuture_implies_downstream .strictDownstream f (by decide)

/-- Korean -ney PRESENT EP entails downstream evidence. -/
theorem neyPresent_downstream (f : EvidentialFrame ℤ) :
    neyPresent.epConstraint f → downstreamEvidence f :=
  EPCondition.nonfuture_implies_downstream .contemporaneous f (by decide)

/-- Bulgarian NFUT + -l EP entails downstream evidence. -/
theorem nfutL_downstream (f : EvidentialFrame ℤ) :
    nfutL.epConstraint f → downstreamEvidence f :=
  EPCondition.nonfuture_implies_downstream .downstream f (by decide)

-- ════════════════════════════════════════════════════
-- § 5. Future Counterexample
-- ════════════════════════════════════════════════════

/-- Future entries do not require downstream evidence: the EP constraint
    is either trivially true (English bare future) or imposes A < T
    (prospective), which is the opposite of T ≤ A. -/
theorem future_no_downstream :
    English.Tense.future.epConstraint ⟨⟨10, 10, 0, 5⟩, 0⟩ ∧
    ¬ downstreamEvidence ⟨⟨10, 10, 0, 5⟩, 0⟩ := by
  refine ⟨(Core.Order.holds_unrestricted _ _).mpr trivial, ?_⟩
  simp [downstreamEvidence]

-- ════════════════════════════════════════════════════
-- § 6. Korean EP/UP Factorization
-- ════════════════════════════════════════════════════

/-- **Korean -te and -ney EP diverge on the same tense**:
    for present tense, -te requires T = A (contemporaneous evidence) while
    -ney requires T = A ∧ T = S (contemporaneous + speech-time present).
    The UP constraints differ: -te has T < S, -ney has T = S. This shows
    EP and UP factorize independently in the morphology. -/
theorem korean_te_ney_ep_diverge :
    -- -te PRES: UP requires T < S (past-shifted evidential perspective)
    (∃ f : EvidentialFrame ℤ,
      tePresent.upConstraint f ∧ ¬ neyPresent.upConstraint f) ∧
    -- -ney PRES: UP requires T = S (speech-time present)
    (∃ f : EvidentialFrame ℤ,
      neyPresent.upConstraint f ∧ ¬ tePresent.upConstraint f) := by
  constructor
  · -- -te PRES with T < S (e.g., T = -1, S = 0, A = -1)
    refine ⟨⟨⟨0, 0, 0, -1⟩, -1⟩, ?_, ?_⟩
    · show (-1 : ℤ) < 0; omega
    · show ¬ ((-1 : ℤ) = 0); omega
  · -- -ney PRES with T = S (e.g., T = 0, S = 0, A = 0)
    refine ⟨⟨⟨0, 0, 0, 0⟩, 0⟩, ?_, ?_⟩
    · show (0 : ℤ) = 0; rfl
    · show ¬ ((0 : ℤ) < 0); omega


-- ════════════════════════════════════════════════════════════════
-- § Tense-Modal Evidentiality Bridge (Cumming ↔ VF&G 2010 ↔ Zheng 2025)
-- ════════════════════════════════════════════════════════════════

/-! [cumming-2026]'s tense evidential constraint and
    [von-fintel-gillies-2010]'s kernel semantics for epistemic
    `must` reflect the same underlying requirement: the speaker's
    evidence is *indirect* — causally downstream of the target event
    but not directly settling it.

    | Cumming (tense)                   | VF&G (modals)                       |
    |-----------------------------------|-------------------------------------|
    | T ≤ A (downstream evidence)       | K doesn't settle φ                  |
    | Nonfuture → downstream required   | must → indirectness presupposition  |
    | Future → no constraint            | Bare assertion → no presupposition  |
    | Direct observation → bare past ok | Direct evidence → must infelicitous |

    The dripping-raincoat scenario ([zheng-2025], used in
    `Modality/Kernel.lean`) provides a concrete bridge: the raincoat
    evidence is causally downstream of rain (T ≤ A), and the kernel
    {wearingRaincoat} doesn't settle isRaining. -/

abbrev World := Fin 4

def allWorlds : List World := [0, 1, 2, 3]

open Semantics.Modality
open Semantics.Presupposition (PartialProp)

-- ── § Raincoat scenario (parallel to Kernel.lean) ──

/-! The kernel defs in `Modality/Kernel.lean` are private. We redefine
    equivalent propositions over `World4` for the bridge. World
    interpretation: w0 = raining, w1 = sprinkler (wet but not rain),
    w2 = dry, w3 = unknown. -/

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

-- ── § Downstream evidence in the raincoat scenario ──

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

-- ── § Bridge theorems ──

open Intensional.Premise (propExtension propIntersection)

/-- The raincoat kernel doesn't settle isRaining: K = {wearingRaincoat},
    and wearingRaincoat neither entails nor excludes isRaining. -/
theorem raincoat_not_settled :
    ¬ directlySettlesExplicit raincoatK isRaining := by
  rintro ⟨x, hx, hcase⟩
  rcases List.mem_singleton.mp hx with rfl
  cases hcase with
  | inl h_ent =>
    have hw1 : ((1 : World) : World) ∈ propExtension wearingRaincoat :=
      show wearingRaincoat (1 : World) from trivial
    have : isRaining (1 : World) := h_ent (1 : World) hw1
    exact this
  | inr h_exc =>
    exact h_exc ⟨(0 : World), show wearingRaincoat (0 : World) from trivial,
                       show isRaining (0 : World) from trivial⟩

/-- **Downstream implies must-defined**: in the raincoat scenario, downstream
    evidence (T ≤ A) co-occurs with the kernel not settling the prejacent. -/
theorem downstream_implies_must_defined :
    downstreamEvidence raincoatFrame ∧
    (kernelMust raincoatK isRaining).presup (0 : World) :=
  ⟨raincoat_downstream, raincoat_not_settled⟩

/-- **Tense-modal evidential parallel**: both Cumming's nonfuture constraint
    and VF&G's `kernelMust` presupposition hold simultaneously for the same
    scenario. The raincoat evidence is downstream (T ≤ A) AND the kernel
    doesn't settle isRaining. -/
theorem tense_modal_evidential_parallel :
    downstreamEvidence raincoatFrame ∧
    (kernelMust raincoatK isRaining).presup (0 : World) ∧
    ¬(kernelMust raincoatK isRaining).assertion (0 : World) := by
  refine ⟨raincoat_downstream, raincoat_not_settled, ?_⟩
  intro hAll
  have hw1 : ((1 : World) : World) ∈ propIntersection raincoatK.props := by
    intro p hp
    rcases List.mem_singleton.mp hp with rfl
    exact (show wearingRaincoat (1 : World) from trivial)
  exact (hAll hw1 : isRaining (1 : World))

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
    ¬(kernelMust directK isRaining).presup (0 : World) ∧
    let directFrame : EvidentialFrame ℤ :=
      { speechTime := 0, perspectiveTime := 0, referenceTime := 0, eventTime := -1, acquisitionTime := -1 }
    downstreamEvidence directFrame := by
  refine ⟨isRaining_settles_isRaining, ?_, ?_⟩
  · intro h
    exact h isRaining_settles_isRaining
  · show (-1 : ℤ) ≤ -1; omega

-- ── § Epistemic authority bridge ──

open Semantics.Epistemicity
open Semantics.Evidential

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
    (kernelMust raincoatK isRaining).presup (0 : World) :=
  ⟨rfl, rfl, raincoat_not_settled, raincoat_not_settled⟩

/-- Ego↔direct and nonparticipant↔indirect form natural pairs.
    Epistemic authority and evidential source are orthogonal
    dimensions that correlate but don't reduce. -/
theorem authority_source_correlation :
    strongAssertion.authority = .ego ∧ strongAssertion.source = .direct ∧
    inferentialClaim.authority = .nonparticipant ∧ inferentialClaim.source = .inference := by
  exact ⟨rfl, rfl, rfl, rfl⟩

end Cumming2026
