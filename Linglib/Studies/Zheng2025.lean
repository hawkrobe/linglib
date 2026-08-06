import Linglib.Data.UD.Basic
import Linglib.Fragments.Mandarin.QuestionParticles
import Linglib.Semantics.Modality.Kernel
import Linglib.Features.QParticleLayer
import Linglib.Semantics.Questions.Bias
import Linglib.Semantics.Questions.Singleton
import Mathlib.Data.Set.Card
import Mathlib.Tactic.DeriveFintype

/-!
# Zheng (2025): Nandao-Q Felicity
[zheng-2025]

Mandarin *nandao*-question felicity: positive evidential bias is necessary,
while negative epistemic bias is neither necessary nor sufficient. The
felicity conditions (Zheng's condition (11)) are built on
[von-fintel-gillies-2010]'s kernel: some evidence in the kernel K raises the
probability of the prejacent, K conflicts with the prior information state U,
and the prejacent is not directly settled in K.

## Main declarations

- `NandaoDatum`, `allData`: the felicity data of exx. 1–6, with the
  generalizations `evidential_bias_necessary`, `epistemic_bias_not_necessary`,
  `epistemic_bias_not_sufficient`, `unexpectedness_necessary`
- `nandaoFelicitous`: condition (11) — evidence raises P(φ), the kernel is
  unexpected given the prior state, φ unsettled
- `raincoat_nandao_felicitous`: the dripping-raincoat scenario (exx. 2–3)
  satisfies all three conditions; `no_evidence_nandao_infelicitous` and
  `expected_evidence_infelicitous` are the matching negative checks
- `nandaoContextualEvidence` / `nandaoOriginalBias`: Zheng's bias
  classification of *nandao*
- `nandaoFullFelicity`: integrated two-layer felicity — singleton sister
  presupposition (shared with [bhatt-dayal-2020]'s kya:) ∧ kernel-bias check
- `biasedUse_integrated_felicity`: the raincoat scenario satisfies the
  integrated predicate
-/

namespace Zheng2025

open Semantics.Modality (Kernel directlySettlesExplicit)
open Intensional.Premise

/-! ### Empirical data -/

/-- A nandao-Q felicity datum. -/
structure NandaoDatum where
  /-- Example number from [zheng-2025] -/
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

/-- Ex. 1, rhetorical use: Lee working on Sunday (evidence) contradicts B's
norm that people don't work Sundays. -/
def rhetoricalUse : NandaoDatum where
  exampleNum := "1"
  context := "Lee plans to work on Sunday; B thinks people don't work Sundays"
  sentence := "Nandao ta fafeng-le ma? (Is he crazy?)"
  evidentialBias := true
  epistemicBias := true
  unexpectedEvidence := true
  felicitous := true

/-- Ex. 2, biased question: A believes not-raining; B enters with a dripping
raincoat. -/
def biasedUse : NandaoDatum where
  exampleNum := "2"
  context := "A believes not-raining; B enters with dripping raincoat"
  sentence := "Nandao waimian xiayu-le ma? (Is it raining outside?)"
  evidentialBias := true
  epistemicBias := true
  unexpectedEvidence := true
  felicitous := true

/-- Ex. 3, pure inquiry (novel): same evidence as ex. 2 but A has no prior
belief about the weather. Nandao is still felicitous. -/
def pureInquiry : NandaoDatum where
  exampleNum := "3"
  context := "A has no weather expectation; B enters with dripping raincoat"
  sentence := "Nandao waimian xiayu-le ma? (Is it raining outside?)"
  evidentialBias := true
  epistemicBias := false
  unexpectedEvidence := true
  felicitous := true

/-- Ex. 4a: epistemic bias without evidence — infelicitous. -/
def epistemicOnly : NandaoDatum where
  exampleNum := "4a"
  context := "Speaker believes room is empty; no contextual evidence"
  sentence := "Nandao wuli you ren? (Are there people in the room?)"
  evidentialBias := false
  epistemicBias := true
  unexpectedEvidence := false
  felicitous := false

/-- Ex. 5 ctx 1: evidence, no belief — felicitous. -/
def evidenceNoBelief : NandaoDatum where
  exampleNum := "5.1"
  context := "No prior beliefs; B enters with dripping raincoat"
  sentence := "Nandao waimian xiayu-le ma? (Is it raining outside?)"
  evidentialBias := true
  epistemicBias := false
  unexpectedEvidence := true
  felicitous := true

/-- Ex. 5 ctx 2: no evidence, no belief — infelicitous. -/
def noEvidenceNoBelief : NandaoDatum where
  exampleNum := "5.2"
  context := "No prior beliefs; B enters normally (no raincoat)"
  sentence := "Nandao waimian xiayu-le ma? (Is it raining outside?)"
  evidentialBias := false
  epistemicBias := false
  unexpectedEvidence := false
  felicitous := false

/-- Ex. 5 ctx 3: epistemic bias, no evidence — infelicitous. -/
def beliefNoEvidence : NandaoDatum where
  exampleNum := "5.3"
  context := "A thinks it won't rain; B enters normally (no raincoat)"
  sentence := "Nandao waimian xiayu-le ma? (Is it raining outside?)"
  evidentialBias := false
  epistemicBias := true
  unexpectedEvidence := false
  felicitous := false

/-- Ex. 6 ctx 1: unexpected evidence — felicitous. -/
def workSundayUnexpected : NandaoDatum where
  exampleNum := "6.1"
  context := "B doesn't think people work Sundays; A says Lee is working Sunday"
  sentence := "Nandao ta hen.mang ma? (Is he busy?)"
  evidentialBias := true
  epistemicBias := true
  unexpectedEvidence := true
  felicitous := true

/-- Ex. 6 ctx 2: expected evidence — infelicitous. -/
def workSundayExpected : NandaoDatum where
  exampleNum := "6.2"
  context := "B knows Lee usually works Sundays; A says Lee is working Sunday"
  sentence := "Nandao ta hen.mang ma? (Is he busy?)"
  evidentialBias := true
  epistemicBias := false
  unexpectedEvidence := false
  felicitous := false

/-- The pooled felicity data of exx. 1–6. -/
def allData : List NandaoDatum :=
  [ rhetoricalUse, biasedUse, pureInquiry,
    epistemicOnly,
    evidenceNoBelief, noEvidenceNoBelief, beliefNoEvidence,
    workSundayUnexpected, workSundayExpected ]

/-- **Generalization 1**: all felicitous nandao-Qs have evidential bias. -/
theorem evidential_bias_necessary :
    (allData.filter (·.felicitous)).all (·.evidentialBias) = true := by decide

/-- **Generalization 2**: some felicitous nandao-Qs lack epistemic bias
(the pure inquiry use). -/
theorem epistemic_bias_not_necessary :
    (allData.filter (λ d => d.felicitous && !d.epistemicBias)).length > 0 := by decide

/-- **Generalization 3**: some infelicitous nandao-Qs have epistemic bias
(epistemic bias is not sufficient). -/
theorem epistemic_bias_not_sufficient :
    (allData.filter (λ d => d.epistemicBias && !d.felicitous)).length > 0 := by decide

/-- **Generalization 4**: all felicitous nandao-Qs have unexpected evidence. -/
theorem unexpectedness_necessary :
    (allData.filter (·.felicitous)).all (·.unexpectedEvidence) = true := by decide

/-! ### Kernel-theoretic felicity conditions

Zheng's condition (11), the final felicity condition for nandao on polar
questions, built on [von-fintel-gillies-2010]'s kernel: (i) some evidence
`p ∈ K` raises the probability of the prejacent φ; (ii) the kernel conflicts
with the prior information state U — the evidence is unexpected; (iii) φ is
not directly settled in K. Condition (iii) is the presupposition of
[von-fintel-gillies-2010]'s `kernelMust`. -/

variable {W : Type*}

/-- Evidence `p` raises the probability of `φ` under the uniform (counting)
measure: P(φ|p) > P(φ), stated by cross-multiplication over cardinalities to
avoid rationals. [zheng-2025]'s condition (11i) writes P(φ|p) ≫ P(φ); we
sharpen "significantly raises" to strict raising and fix the uniform measure
on `W`. Meaningful for finite `W` (`Set.ncard` and `Nat.card` are junk
otherwise). -/
def evidenceRaises (p φ : W → Prop) : Prop :=
  {w | p w ∧ φ w}.ncard * Nat.card W > {w | φ w}.ncard * {w | p w}.ncard

/-- Some proposition in K raises the probability of φ
([zheng-2025] condition (11i)). -/
def evidenceSupports (k : Kernel W) (φ : W → Prop) : Prop :=
  ∃ p ∈ k.props, evidenceRaises p φ

/-- The evidence in K is unexpected given the prior information state U
([zheng-2025] condition (11ii)): B_K ∩ ⋂U = ∅. U collects what leads to the
information state prior to encountering the evidence — beliefs, norms,
desires — distinct from the kernel's direct evidence. -/
def unexpected (k : Kernel W) (u : List ((W → Prop))) : Prop :=
  k.base ∩ propIntersection u = ∅

/-- **Nandao-Q felicity** ([zheng-2025] condition (11), final version for
polar questions): (i) some evidence in K raises P(φ), (ii) the evidence is
unexpected given the prior state U, (iii) φ is not directly settled in K. -/
def nandaoFelicitous (k : Kernel W) (u : List ((W → Prop))) (φ : W → Prop) : Prop :=
  evidenceSupports k φ ∧ unexpected k u ∧ ¬ directlySettlesExplicit k φ

/-! ### The dripping-raincoat scenario ([zheng-2025] exx. 2–3, 5)

K = {wearingRaincoat}: direct evidence that someone entered with a wet coat.
U = {expectDry}: prior expectation of no rain (doxastic or normative). -/

/-- Four worlds for the raincoat scenario: it rains, the sprinkler ran
    (wet coat without rain), it is dry, or nothing is known. -/
inductive World where
  | rain | sprinkler | dry | unknown
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- B enters wearing a dripping raincoat: true where the coat is wet. -/
abbrev wearingRaincoat : World → Prop := λ w => w = .rain ∨ w = .sprinkler

/-- A's prior expectation: no rain. -/
abbrev expectDry : World → Prop := λ w => w = .dry ∨ w = .unknown

/-- It is raining outside. -/
abbrev isRaining : World → Prop := (· = .rain)

/-- The raincoat kernel: direct evidence of the wet coat. -/
def raincoatK : Kernel World := ⟨[wearingRaincoat]⟩

/-- The prior information state: A expects dry weather. -/
def dryU : List ((World → Prop)) := [expectDry]

/-- "Nandao waimian xiayu-le ma?" is felicitous with a dripping raincoat:
P(rain|coat) = 1/2 > P(rain) = 1/4; B_K ∩ ⋂U = ∅; rain unsettled by K. -/
theorem raincoat_nandao_felicitous :
    nandaoFelicitous raincoatK dryU isRaining := by
  refine ⟨⟨wearingRaincoat, by simp [raincoatK], ?_⟩, ?_, ?_⟩
  · -- |coat ∧ rain| ⬝ |W| > |rain| ⬝ |coat|: 1 ⬝ 4 > 1 ⬝ 2.
    have hpφ : {w | wearingRaincoat w ∧ isRaining w} = {World.rain} := by
      ext w; cases w <;> simp [wearingRaincoat, isRaining]
    have hφ : {w | isRaining w} = {World.rain} := by
      ext w; cases w <;> simp [isRaining]
    have hp : {w | wearingRaincoat w} = {World.rain, World.sprinkler} := by
      ext w; cases w <;> simp [wearingRaincoat]
    unfold evidenceRaises
    rw [hpφ, hφ, hp, Set.ncard_singleton, Set.ncard_pair (by decide),
      Nat.card_eq_fintype_card]
    decide
  · refine Set.eq_empty_iff_forall_notMem.mpr λ w ⟨hK, hU⟩ => ?_
    have h1 : wearingRaincoat w := mem_propIntersection.mp hK _ (by simp [raincoatK])
    have h2 : expectDry w := mem_propIntersection.mp hU _ (by simp [dryU])
    revert h1 h2
    cases w <;> decide
  · rintro ⟨x, hx, hxor⟩
    rcases List.mem_singleton.mp (by simpa [raincoatK] using hx) with rfl
    rcases hxor with h_ent | h_exc
    · exact absurd (h_ent .sprinkler (show wearingRaincoat .sprinkler from by decide))
        (by decide)
    · exact h_exc ⟨.rain, show wearingRaincoat .rain from by decide, by decide⟩

/-- Without evidence, nandao is infelicitous ([zheng-2025] ex. 5 ctx 2). -/
theorem no_evidence_nandao_infelicitous :
    ¬ nandaoFelicitous ⟨[]⟩ dryU isRaining := by
  rintro ⟨⟨x, hx, _⟩, _, _⟩
  exact List.not_mem_nil hx

/-- When evidence is expected (K compatible with U), nandao is infelicitous
([zheng-2025] ex. 6 ctx 2, transposed to the raincoat scenario: a prior
expectation of wet coats makes the evidence unremarkable). -/
theorem expected_evidence_infelicitous :
    ¬ nandaoFelicitous raincoatK [wearingRaincoat] isRaining := by
  rintro ⟨_, hInc, _⟩
  have hmem : World.rain ∈ raincoatK.base ∩ propIntersection [wearingRaincoat] :=
    ⟨mem_propIntersection.mpr (by simp [raincoatK, wearingRaincoat]),
     mem_propIntersection.mpr (by simp [wearingRaincoat])⟩
  rw [unexpected] at hInc
  exact absurd (hInc ▸ hmem) (Set.notMem_empty _)

/-! ### Bias classification -/

open Mandarin.QuestionParticles (nandao ma ba)

/-- Zheng's evidential classification of *nandao*: requires contextual
evidence for p — the lexical face of `evidential_bias_necessary`. -/
def nandaoContextualEvidence : Option Semantics.Questions.Bias.ContextualEvidence :=
  some .forP

/-- Zheng's classification: *nandao* does NOT require epistemic bias —
compatible with a neutral epistemic state (pure inquiry use, ex. 3);
the lexical face of `epistemic_bias_not_necessary`. -/
def nandaoOriginalBias : Option Semantics.Questions.Bias.OriginalBias := none

/-- `nandaoFelicitous` entails `evidenceSupports`, connecting the felicity
predicate to `nandaoContextualEvidence` and the empirical generalization
`evidential_bias_necessary`. -/
theorem kernel_requires_evidence (k : Kernel World) (u : List ((World → Prop)))
    (φ : (World → Prop)) (h : nandaoFelicitous k u φ) :
    evidenceSupports k φ :=
  h.1

/-! ### Left-peripheral layer assignments ([dayal-2025] cartography)

Zheng's layer assignments for the three Mandarin Q-particles in the
[dayal-2025] cartography `[SAP [PerspP [CP ...]]]`. The layer split mirrors
the bias split: the unbiased particle *ma* is CP (widest distribution:
matrix, subordinated, quasi-subordinated); the biased *ba* and *nandao* are
PerspP (matrix + quasi-subordinated only). The `_` argument is unused: the
layer is a theoretical overlay on the fragment particle, not a computed
property of its lexical fields. -/

open Features (QParticleLayer)

/-- *ma*: the unmarked CP-layer particle. -/
def ma_layer (_ : Particle) : QParticleLayer := .cp

/-- *ba*: PerspP-layer biased particle. -/
def ba_layer (_ : Particle) : QParticleLayer := .perspP

/-- *nandao*: PerspP-layer biased particle. -/
def nandao_layer (_ : Particle) : QParticleLayer := .perspP

/-- Zheng's classification of *ba*: speaker-bias (expects a positive answer,
seeks confirmation), no evidential requirement; the unbiased *ma* imposes
neither. -/
def baOriginalBias : Option Semantics.Questions.Bias.OriginalBias := some .forP

/-! ### Singleton-alternative presupposition (parallel to kya:)

[bhatt-dayal-2020] fn. 11 explicitly cites the parallel Mandarin *nandao*
analysis as the model for their kya: proposal. At the algebraic level, both
particles share the same singleton presupposition: their sister question must
denote a singleton-cell issue ([bhatt-dayal-2020] eq. 23), captured by the
shared `Question.IsSingleton` predicate. -/

open Question (IsSingleton SingletonQuestion ofSet isSingleton_ofSet alt polar
  not_isSingleton_polar_of_nontrivial alt_ofSet)

/-- nandao is felicitous on a one-cell ("highlighted") polar — the same
canonical good-input case as kya:. Both this and
`BhattDayal2020.kya_felicitous_singleton_polar` are `isSingleton_ofSet`,
capturing the kya:–nandao convergence [bhatt-dayal-2020] draw from
[xu-2012]. -/
theorem nandao_felicitous_ofSet (p : Set W) :
    IsSingleton (ofSet (W := W) p) :=
  isSingleton_ofSet p

/-! ### Integrated felicity

Nandao's full felicity has two independent layers: the sister content is
*singleton* — `alt Q = {p}` for a unique witness `p` (semantic
well-formedness, the [bhatt-dayal-2020] eq. 23 presupposition) — and the
kernel-bias check `nandaoFelicitous k u p` holds for the witness (discourse
felicity in context). The integrated predicate composes them; a Layer-1
failure (a non-trivial two-cell polar) blocks felicity regardless of
`(k, u)`. -/

/-- **Integrated nandao felicity**: the singleton presupposition
(`alt Q = {p}`) together with the kernel-bias check on the witness. The
witness `p` is supplied externally; for the noncomputable choice from a
`SingletonQuestion` use `SingletonQuestion.witness`. -/
def nandaoFullFelicity (Q : Question World) (k : Kernel World)
    (u : List ((World → Prop))) (p : Set World) : Prop :=
  alt Q = {p} ∧ nandaoFelicitous k u p

/-- Integrated felicity entails the singleton presupposition. -/
theorem nandaoFullFelicity_isSingleton {Q : Question World} {k : Kernel World}
    {u : List ((World → Prop))} {p : Set World}
    (h : nandaoFullFelicity Q k u p) :
    Question.IsSingleton Q :=
  ⟨p, h.1⟩

/-- Integrated felicity entails the kernel-bias check on the witness. -/
theorem nandaoFullFelicity_kernel {Q : Question World} {k : Kernel World}
    {u : List ((World → Prop))} {p : Set World}
    (h : nandaoFullFelicity Q k u p) :
    nandaoFelicitous k u p :=
  h.2

/-- A two-cell Hamblin polar `polar p₀` (with non-trivial `p₀`) admits no
integrated-felicity witness: no kernel and prior state can rescue it, because
the singleton requirement `alt Q = {p}` already fails. -/
theorem nandao_polar_no_witness {p₀ : Set World}
    (hne : p₀ ≠ ∅) (hnu : p₀ ≠ Set.univ)
    (k : Kernel World) (u : List ((World → Prop))) :
    ¬ ∃ p : Set World, nandaoFullFelicity (polar p₀) k u p := by
  rintro ⟨p, hfull, _⟩
  exact not_isSingleton_polar_of_nontrivial hne hnu ⟨p, hfull⟩

/-- On a one-cell sister `ofSet p`, integrated felicity is exactly the
kernel-bias check on `p`: the singleton component holds by `alt_ofSet`. -/
theorem nandaoFullFelicity_declarative_iff {p : Set World}
    (k : Kernel World) (u : List ((World → Prop))) :
    nandaoFullFelicity (Question.ofSet p) k u p ↔
      nandaoFelicitous k u p := by
  unfold nandaoFullFelicity
  rw [alt_ofSet]
  exact ⟨λ h => h.2, λ h => ⟨rfl, h⟩⟩

/-- In the dripping-raincoat scenario with sister `declarative isRaining`,
both layers of nandao felicity hold simultaneously; reduces to
`raincoat_nandao_felicitous` via `nandaoFullFelicity_declarative_iff`. The
datum `biasedUse` records the same scenario ([zheng-2025] ex. 2) as
empirical data. -/
theorem biasedUse_integrated_felicity :
    nandaoFullFelicity (Question.ofSet isRaining) raincoatK dryU
      isRaining := by
  rw [nandaoFullFelicity_declarative_iff]
  exact raincoat_nandao_felicitous

end Zheng2025
