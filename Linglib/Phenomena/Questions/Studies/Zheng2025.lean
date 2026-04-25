import Linglib.Core.Lexical.Word
import Linglib.Fragments.Mandarin.QuestionParticles
import Linglib.Theories.Semantics.Modality.Kernel
import Linglib.Theories.Semantics.Questions.QParticleLayer
import Linglib.Core.Question.Singleton
import Linglib.Phenomena.Questions.Studies.BhattDayal2020

/-!
# Zheng (2025): Nandao-Q Felicity @cite{zheng-2025}

Mandarin *nandao*-question felicity. Self-contained study file:
empirical data, the Mandarin Fragment entry, and bridges to the
Kernel-theoretic felicity predicate `nandaoFelicitous`.

The core finding is that positive evidential bias is **necessary** for
nandao-Q felicity, while negative epistemic bias is **neither necessary
nor sufficient**.

## Key Generalizations

1. Positive evidential bias (contextual evidence for p) → nandao felicitous
2. Epistemic bias alone (prior belief against p, no evidence) → nandao infelicitous
3. Evidence must be **unexpected** relative to prior information state
4. Nandao-Qs can function as pure inquiry (no prior belief required)

## Predictions verified

- `fragment_data_evidential`: Fragment entry's evidential bias requirement
  matches the empirical generalization
- `fragment_data_epistemic`: Fragment entry correctly does not require
  epistemic bias
- `kernel_requires_evidence`: Kernel `nandaoFelicitous` entails
  `evidenceSupports`
- `nandaoFullFelicity`: integrated two-layer felicity (singleton sister
  presupposition ∧ Kernel-bias check) — §5
- `biasedUse_integrated_felicity`: dripping-raincoat scenario satisfies
  integrated felicity at the §5 level — §6
- `biasedUse_witnesses_integrated_felicity`: §1 datum (ex. 2) ↔ §6
  theoretical prediction

## Known gaps

- No formalization of the unexpectedness requirement in the Kernel theory
-/

namespace Phenomena.Questions.Studies.Zheng2025

-- ════════════════════════════════════════════════════════════════════════════
-- §1 — Empirical Data
-- ════════════════════════════════════════════════════════════════════════════

/-- A nandao-Q felicity datum. -/
structure NandaoDatum where
  /-- Example number from @cite{zheng-2025} -/
  exampleNum : String
  /-- Context description -/
  context : String
  /-- The nandao-Q sentence (pinyin) -/
  sentence : String
  /-- Is there positive evidential bias (contextual evidence for p)? -/
  evidentialBias : Bool
  /-- Is there negative epistemic bias (prior belief against p)? -/
  epistemicBias : Bool
  /-- Is the evidence unexpected? -/
  unexpectedEvidence : Bool
  /-- Is the nandao-Q felicitous? -/
  felicitous : Bool
  deriving Repr, DecidableEq

-- ════════════════════════════════════════════════════════════════════════════
-- §1.1 — Rhetorical, Biased, and Pure Inquiry Uses
-- ════════════════════════════════════════════════════════════════════════════

/-- Ex. 1: Rhetorical use. Lee working on Sunday (evidence) contradicts B's
norm that people don't work Sundays (epistemic/deontic bias). -/
def rhetoricalUse : NandaoDatum where
  exampleNum := "1"
  context := "Lee plans to work on Sunday; B thinks people don't work Sundays"
  sentence := "Nandao ta fafeng-le ma? (Is he crazy?)"
  evidentialBias := true
  epistemicBias := true
  unexpectedEvidence := true
  felicitous := true

/-- Ex. 2: Biased question. A believes not-raining; B enters with dripping
raincoat (evidence contradicting belief). -/
def biasedUse : NandaoDatum where
  exampleNum := "2"
  context := "A believes not-raining; B enters with dripping raincoat"
  sentence := "Nandao waimian xiayu-le ma? (Is it raining outside?)"
  evidentialBias := true
  epistemicBias := true
  unexpectedEvidence := true
  felicitous := true

/-- Ex. 3: Pure inquiry (NOVEL). Same evidence as ex. 2 but A has NO prior
belief about the weather. Nandao is still felicitous. -/
def pureInquiry : NandaoDatum where
  exampleNum := "3"
  context := "A has no weather expectation; B enters with dripping raincoat"
  sentence := "Nandao waimian xiayu-le ma? (Is it raining outside?)"
  evidentialBias := true
  epistemicBias := false
  unexpectedEvidence := true
  felicitous := true

-- ════════════════════════════════════════════════════════════════════════════
-- §1.2 — Epistemic Bias Not Sufficient
-- ════════════════════════════════════════════════════════════════════════════

/-- Ex. 4a: Epistemic bias without evidence. Speaker believes room is empty
but has no contextual evidence either way. -/
def epistemicOnly : NandaoDatum where
  exampleNum := "4a"
  context := "Speaker believes room is empty; no contextual evidence"
  sentence := "Nandao wuli you ren? (Are there people in the room?)"
  evidentialBias := false
  epistemicBias := true
  unexpectedEvidence := false
  felicitous := false

-- ════════════════════════════════════════════════════════════════════════════
-- §1.3 — Evidence Without Epistemic Bias
-- ════════════════════════════════════════════════════════════════════════════

/-- Ex. 5 ctx 1: Evidence + no belief → felicitous. -/
def evidenceNoBelief : NandaoDatum where
  exampleNum := "5.1"
  context := "No prior beliefs; B enters with dripping raincoat"
  sentence := "Nandao waimian xiayu-le ma? (Is it raining outside?)"
  evidentialBias := true
  epistemicBias := false
  unexpectedEvidence := true
  felicitous := true

/-- Ex. 5 ctx 2: No evidence + no belief → infelicitous. -/
def noEvidenceNoBelief : NandaoDatum where
  exampleNum := "5.2"
  context := "No prior beliefs; B enters normally (no raincoat)"
  sentence := "Nandao waimian xiayu-le ma? (Is it raining outside?)"
  evidentialBias := false
  epistemicBias := false
  unexpectedEvidence := false
  felicitous := false

/-- Ex. 5 ctx 3: No evidence + epistemic bias → infelicitous. -/
def beliefNoEvidence : NandaoDatum where
  exampleNum := "5.3"
  context := "A thinks it won't rain; B enters normally (no raincoat)"
  sentence := "Nandao waimian xiayu-le ma? (Is it raining outside?)"
  evidentialBias := false
  epistemicBias := true
  unexpectedEvidence := false
  felicitous := false

-- ════════════════════════════════════════════════════════════════════════════
-- §1.4 — Unexpectedness Required
-- ════════════════════════════════════════════════════════════════════════════

/-- Ex. 6 ctx 1: Unexpected evidence → felicitous. -/
def unexpectedEvidence_ : NandaoDatum where
  exampleNum := "6.1"
  context := "B doesn't think people work Sundays; A says Lee is working Sunday"
  sentence := "Nandao ta hen.mang ma? (Is he busy?)"
  evidentialBias := true
  epistemicBias := true
  unexpectedEvidence := true
  felicitous := true

/-- Ex. 6 ctx 2: Expected evidence → infelicitous. -/
def expectedEvidence : NandaoDatum where
  exampleNum := "6.2"
  context := "B knows Lee usually works Sundays; A says Lee is working Sunday"
  sentence := "Nandao ta hen.mang ma? (Is he busy?)"
  evidentialBias := true
  epistemicBias := false
  unexpectedEvidence := false
  felicitous := false

-- ════════════════════════════════════════════════════════════════════════════
-- §1.5 — Dataset and Generalization Theorems
-- ════════════════════════════════════════════════════════════════════════════

def allData : List NandaoDatum :=
  [ rhetoricalUse, biasedUse, pureInquiry,
    epistemicOnly,
    evidenceNoBelief, noEvidenceNoBelief, beliefNoEvidence,
    unexpectedEvidence_, expectedEvidence ]

/-- **Generalization 1**: All felicitous nandao-Qs have evidential bias. -/
theorem evidential_bias_necessary :
    (allData.filter (·.felicitous)).all (·.evidentialBias) = true := by native_decide

/-- **Generalization 2**: Some felicitous nandao-Qs lack epistemic bias
(the pure inquiry use). -/
theorem epistemic_bias_not_necessary :
    (allData.filter (λ d => d.felicitous && !d.epistemicBias)).length > 0 := by native_decide

/-- **Generalization 3**: Some infelicitous nandao-Qs have epistemic bias
(epistemic bias is not sufficient). -/
theorem epistemic_bias_not_sufficient :
    (allData.filter (λ d => d.epistemicBias && !d.felicitous)).length > 0 := by native_decide

/-- **Generalization 4**: All felicitous nandao-Qs have unexpected evidence. -/
theorem unexpectedness_necessary :
    (allData.filter (·.felicitous)).all (·.unexpectedEvidence) = true := by native_decide

/-- 9 data points from 6 examples covering 4 conditions. -/
theorem dataset_size : allData.length = 9 := by native_decide

-- ════════════════════════════════════════════════════════════════════════════
-- §2 — Bridges: Fragment ↔ Data, Theory ↔ Data
-- ════════════════════════════════════════════════════════════════════════════

open Fragments.Mandarin.QuestionParticles (nandao)
open Semantics.Modality (Kernel Background nandaoFelicitous World)

/-- The nandao Fragment entry's evidential bias requirement matches the
empirical generalization: all felicitous nandao-Qs have evidential bias. -/
theorem fragment_data_evidential :
    nandao.requiresEvidentialBias = true ∧
    (allData.filter (·.felicitous)).all (·.evidentialBias) = true :=
  ⟨rfl, by native_decide⟩

/-- The nandao Fragment entry correctly does NOT require epistemic bias,
matching the empirical finding that some felicitous nandao-Qs lack it. -/
theorem fragment_data_epistemic :
    nandao.requiresEpistemicBias = false ∧
    (allData.filter (λ d => d.felicitous && !d.epistemicBias)).length > 0 :=
  ⟨rfl, by native_decide⟩

/-- Kernel `nandaoFelicitous` entails `evidenceSupports`, connecting the
Theory predicate to the Fragment's `requiresEvidentialBias = true` and
the empirical generalization `evidential_bias_necessary`. -/
theorem kernel_requires_evidence (k : Kernel World) (u : Background World) (φ : (World → Prop))
    [DecidablePred φ] (h : nandaoFelicitous k u φ) :
    k.evidenceSupports φ :=
  h.1

-- ════════════════════════════════════════════════════════════════════════════
-- §3 — Left-Peripheral Layer Assignments (@cite{dayal-2025} cartography)
-- ════════════════════════════════════════════════════════════════════════════

open Semantics.Questions (QParticleLayer)
open Fragments.Mandarin.QuestionParticles (QuestionParticleEntry ma ba)

/-- Zheng's layer assignments for the three Mandarin Q-particles in the
    @cite{dayal-2025} cartography `[SAP [PerspP [CP ...]]]`. The `_`
    argument is unused: the layer is a theoretical overlay on the
    fragment particle, not a computed property of its lexical fields. -/
def ma_layer     (_ : QuestionParticleEntry) : QParticleLayer := .cp
def ba_layer     (_ : QuestionParticleEntry) : QParticleLayer := .perspP
def nandao_layer (_ : QuestionParticleEntry) : QParticleLayer := .perspP

/-- *ma* is the unmarked CP-layer particle: widest distribution
    (matrix, subordinated, quasi-subordinated). -/
theorem ma_is_CP : ma_layer ma = .cp := rfl

/-- *ba* and *nandao* are PerspP-layer biased particles: matrix +
    quasi-subordinated only. -/
theorem ba_nandao_PerspP :
    ba_layer ba = .perspP ∧ nandao_layer nandao = .perspP := ⟨rfl, rfl⟩

/-- The layer split mirrors the bias-profile split: the unbiased
    particle is CP, the biased ones are PerspP. -/
theorem layer_correlates_with_bias :
    ma_layer ma = .cp ∧
    ma.requiresEvidentialBias = false ∧ ma.requiresEpistemicBias = false ∧
    ba_layer ba = .perspP ∧ ba.requiresEpistemicBias = true ∧
    nandao_layer nandao = .perspP ∧ nandao.requiresEvidentialBias = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════════════════════════════
-- §4 — Singleton-Alternative Presupposition (parallel to kya:)
-- ════════════════════════════════════════════════════════════════════════════

/-! @cite{bhatt-dayal-2020} fn. 11 explicitly cites the parallel
Mandarin *nandao* analysis as the model for their kya: proposal.
At the algebraic level, both particles share the same singleton
presupposition: their sister question must denote a singleton-cell
issue (@cite{bhatt-dayal-2020} eq. 23). The cross-particle
generalization is captured by inheriting the same
`Core.Question.IsSingleton` predicate — both kya: and nandao take a
`SingletonQuestion W` as well-typed sister content. -/

open Core.Question (IsSingleton SingletonQuestion declarative
  isSingleton_declarative)

universe u
variable {W : Type u}

/-- nandao is felicitous on a one-cell ("highlighted") polar — same
    canonical good-input case as kya:. The proof reduces to
    `isSingleton_declarative`, identical to the kya: side. -/
theorem nandao_felicitous_declarative (p : Set W) :
    IsSingleton (declarative (W := W) p) :=
  isSingleton_declarative p

/-- **Cross-particle agreement**: the felicity conditions for kya: and
    nandao on a one-cell polar are *the same theorem* — both reduce to
    `isSingleton_declarative`. The convergence noted in
    @cite{bhatt-dayal-2020} fn. 11 holds by construction. -/
theorem nandao_kya_share_felicity (p : Set W) :
    nandao_felicitous_declarative (W := W) p =
      Phenomena.Questions.TypologyBridge.kya_felicitous_declarative
        (W := W) p := rfl

-- ════════════════════════════════════════════════════════════════════════════
-- §5 — Integrated Felicity: §2 (Kernel-bias) ∧ §4 (Question-singleton)
-- ════════════════════════════════════════════════════════════════════════════

/-! Bridge §2 and §4. Nandao's full felicity has two independent layers:

  - **Layer 1** (Question-level, §4): the sister content `Q : Core.Question World`
    is *singleton* — `alt Q = {p}` for some unique witness `p`. This is the
    @cite{bhatt-dayal-2020} eq. 23 presupposition: nandao requires a
    one-cell sister, not a two-cell Hamblin polar.
  - **Layer 2** (Kernel-level, §2): the Kernel-bias check
    `nandaoFelicitous k u p` holds for the witness — the evidence in `K`
    raises `P(p)`, `K` is incompatible with the prior `U`, and `p` is
    not directly settled.

These layers are independent concerns: Layer 1 is about semantic
well-formedness of the sister content, Layer 2 is about discourse
felicity in context. The integrated predicate composes them into a
single statement, and the bridges below show that Layer 1 failure
(e.g. a non-trivial two-cell polar) blocks felicity at the integrated
level regardless of `(k, u)`. -/

open Core.Question (alt polar
  not_isSingleton_polar_of_nontrivial alt_polar_of_nontrivial
  alt_declarative)

/-- **Integrated nandao felicity**: the conjunction of Layer 1
    (singleton presupposition: `alt Q = {p}`) and Layer 2 (Kernel-bias
    check on the witness). The witness `p` is supplied externally so
    decidability is concrete; for the noncomputable choice from a
    `SingletonQuestion` use `SingletonQuestion.witness`. -/
def nandaoFullFelicity (Q : Core.Question World) (k : Kernel World) (u : Background World)
    (p : Set World) [DecidablePred p] : Prop :=
  alt Q = {p} ∧ nandaoFelicitous k u p

/-- **Layer-1 projection**: integrated felicity entails the §4
    singleton presupposition. -/
theorem nandaoFullFelicity_isSingleton {Q : Core.Question World} {k : Kernel World}
    {u : Background World} {p : Set World} [DecidablePred p]
    (h : nandaoFullFelicity Q k u p) :
    Core.Question.IsSingleton Q :=
  ⟨p, h.1⟩

/-- **Layer-2 projection**: integrated felicity entails the §2
    Kernel-bias check on the witness. -/
theorem nandaoFullFelicity_kernel {Q : Core.Question World} {k : Kernel World}
    {u : Background World} {p : Set World} [DecidablePred p]
    (h : nandaoFullFelicity Q k u p) :
    nandaoFelicitous k u p :=
  h.2

/-- **Layer-1 obstruction**: a two-cell Hamblin polar `polar p₀` (with
    non-trivial `p₀`) admits no integrated-felicity witness. No
    Kernel + Background can rescue it: the §4 type-level barrier
    propagates upward through the `alt Q = {p}` requirement. The
    structural reason `polar` two-cell questions are universally
    blocked from nandao licensing. -/
theorem nandao_polar_no_witness {p₀ : Set World}
    (hne : p₀ ≠ ∅) (hnu : p₀ ≠ Set.univ)
    (k : Kernel World) (u : Background World) :
    ¬ ∃ (p : Set World) (_ : DecidablePred p),
        nandaoFullFelicity (polar p₀) k u p := by
  rintro ⟨p, _, hfull, _⟩
  exact not_isSingleton_polar_of_nontrivial hne hnu ⟨p, hfull⟩

/-- **Declarative reduction**: on a one-cell sister `declarative p`,
    integrated felicity is exactly the §2 Kernel-bias check on `p`.
    The Layer-1 component holds trivially because `alt (declarative p)
    = {p}` (`alt_declarative`). This makes the §2 ↔ §5 connection
    explicit on the canonical felicitous case. -/
theorem nandaoFullFelicity_declarative_iff {p : Set World} [DecidablePred p]
    (k : Kernel World) (u : Background World) :
    nandaoFullFelicity (Core.Question.declarative p) k u p ↔
      nandaoFelicitous k u p := by
  unfold nandaoFullFelicity
  rw [alt_declarative]
  exact ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩

-- ════════════════════════════════════════════════════════════════════════════
-- §6 — Empirical Closure: §1 datum (biasedUse) ↔ §5 integrated felicity
-- ════════════════════════════════════════════════════════════════════════════

/-! Apply §5 to the canonical biased-use scenario from @cite{zheng-2025} ex. 2:

  - K = `[wearingRaincoat]` — direct evidence (B enters with dripping coat)
  - U = `[expectDry]` — A's prior expectation it is not raining
  - p = `isRaining` — the question content

The Kernel-side bias check is `raincoat_nandao_felicitous` (proven in
`Theories/Semantics/Modality/Kernel.lean` from explicit cardinality
counts on `World4`). Pairing it with the singleton presupposition
yields integrated felicity at the §5 level. The §1 datum `biasedUse`
records the same scenario as empirical data (`evidentialBias = true`,
`epistemicBias = true`, `felicitous = true`); the bridge below makes
the data ↔ theory correspondence explicit. -/

open Semantics.Modality (raincoatK dryU isRaining raincoat_nandao_felicitous)

/-- **§1 ex. 2 ↔ §5 integrated felicity**: in the dripping-raincoat
    scenario with sister `declarative isRaining`, both layers of nandao
    felicity hold simultaneously. Reduces to `raincoat_nandao_felicitous`
    via `nandaoFullFelicity_declarative_iff`. -/
theorem biasedUse_integrated_felicity :
    nandaoFullFelicity (Core.Question.declarative isRaining) raincoatK dryU
      isRaining := by
  rw [nandaoFullFelicity_declarative_iff]
  exact raincoat_nandao_felicitous

/-- **Data ↔ theory bridge**: the §1 datum `biasedUse` is felicitous and
    has both bias profiles set; the §5 integrated felicity holds for the
    matching Kernel scenario. The shared scaffold is the dripping-raincoat
    setup of @cite{zheng-2025} ex. 2 — empirical observation on the data
    side, derived prediction on the theory side. -/
theorem biasedUse_witnesses_integrated_felicity :
    biasedUse.felicitous = true ∧
    biasedUse.evidentialBias = true ∧
    biasedUse.epistemicBias = true ∧
    nandaoFullFelicity (Core.Question.declarative isRaining) raincoatK dryU
      isRaining :=
  ⟨rfl, rfl, rfl, biasedUse_integrated_felicity⟩

end Phenomena.Questions.Studies.Zheng2025
