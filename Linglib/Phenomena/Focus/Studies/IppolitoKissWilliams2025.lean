import Linglib.Theories.Semantics.Questions.Probabilistic
import Linglib.Core.Question.Relevance
import Linglib.Theories.Pragmatics.DecisionTheoretic.But
import Linglib.Theories.Pragmatics.DecisionTheoretic.Core
import Linglib.Phenomena.Focus.DiscourseOnly
import Linglib.Core.Probability.PMFFin
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Basic

/-!
# @cite{ippolito-kiss-williams-2025}: Discourse *only*
@cite{potts-2005} @cite{roberts-2012} @cite{thomas-2026} @cite{merin-1999}

Single-paper formalisation of @cite{ippolito-kiss-williams-2025}
"Discourse only" (WCCFL 41 proceedings). Discourse *only* is a
clausal connective taking two clausal arguments `S` and `S'` and
contributing a conventional implicature (CI) that `S'` fails to
support the evidential direction established by prior partial answers
to the QUD. Substrate primitives (`Supports`, `Agree`, `Disagree`,
`IsPositiveEvidence`) live in
`Theories/Semantics/Questions/Probabilistic.lean`; this file owns the
paper-specific bundling — `Sentence`, `Context`, the felicity
conditions of Def. 16, the architectural derivations of §5.2, the
worked house-buying example of §7, and the DTS bridge of §6.

## The puzzle

Cross-linguistically, some languages have a discourse particle glossed
as "only" that conjoins two clauses while signalling that the second
undermines the evidential trajectory of the first:

- Italian   *solo che*  ("La casa è bella, solo che è costosissima")
- Russian   *tol'ko*    ("Квартира большая, только кухня маленькая")
- Hungarian *csak*      ("A ház szép, csak drága")
- Mandarin  *zhǐshì*    ("房子很好, 只是太贵了")

## Definition 16

`⟦S [only S']⟧^c` is defined only if `S` and `S'` are relevant to the
QUD in `c` and `∃ α ∈ QUD, S` supports `α`. If defined:

* **At-issue**: highlighted content of `S` intersected with that of `S'`
  — every world where both are informatively true.
* **CI**: `∃ α ∈ QUD` such that
  (i)  every true partial answer `p ∉ QUD` is positive evidence for `α`;
  (ii) `S'` does not support `α`.

## Architectural derivations

* **Interrogative left-arg restriction** (§5.2). Canonical info-seeking
  questions cannot be the left argument because the speaker doesn't
  believe any answer, so `dox ⊆ q` fails for all `q ∈ alt S`, so
  `Supports` fails. This falls out from `Supports.of_no_belief_fails`
  in `Probabilistic.lean` — no clause-type filter required.
* **Biased / rhetorical questions can be left-args** (§5.2 exx 20–21).
  These have a believed answer (`dox ⊆ q` for some `q`), so the doxastic
  condition is satisfied.
* **Comparison with *but*** (§6). Both express contrast, but *only*'s
  right argument only needs to fail to support (`¬Supports`), not
  actively counter-support (negative relevance). This makes *only*
  strictly weaker than *but*; see Part II below.

## Layout

* **Substrate** (`Sentence`, `Context`, `isDefined`, `ciContent`,
  `agree`, `disagree`) and architectural theorems
  (`interrogative_blocks_support`, `weak_non_agreement`,
  `disagree_imp_ciContent_of_empty_partials`).
* **Part I**: end-to-end derivation chains for the house-buying
  scenario (§7), instantiating the substrate on a concrete 8-world
  model and connecting the predictions to `Phenomena/Focus/DiscourseOnly`.
* **Part II**: bridge to @cite{merin-1999}'s DTS — establishing that
  every *but* context can license discourse *only* but not vice versa
  (the §6 asymmetry).
-/

namespace Phenomena.Focus.Studies.IppolitoKissWilliams2025

open Core Core.Question Semantics.Questions.Probabilistic

/-! ### Discourse context -/

/-- Discourse context for evaluating discourse *only*.

The doxastic state is what makes the interrogative restriction fall
out naturally: canonical info-seeking questions fail the doxastic
condition of `Supports` (the speaker doesn't believe any answer). -/
structure Context (W : Type*) where
  /-- The QUD as an inquisitive issue. -/
  qud : Question W
  /-- Prior probability distribution. -/
  prior : PMF W
  /-- Speaker's doxastic state `dox_sp`. -/
  dox : Set W
  /-- True partial answers to the QUD established in prior discourse.
      @cite{ippolito-kiss-williams-2025} Def. 16 CI condition (i)
      quantifies universally over all true partial answers `p ∉ QUD`. -/
  partialAnswers : List (Set W)
  /-- Subquestions of the QUD established by the discourse context.
      @cite{roberts-2012} Def. 8–9; @cite{ippolito-kiss-williams-2025}
      §5.1: provided by the context, not computed. -/
  subquestions : List (Question W)

/-! ### Sentence -/

/-- A discourse *only* sentence with two clausal arguments.

`sDen` is the inquisitive denotation of the left argument `S`,
`s'Den` is the inquisitive denotation of the right argument `S'`. The
denotation type is uniform — what varies between declarative and
interrogative arguments is whether `Supports` can be satisfied. -/
structure Sentence (W : Type*) where
  /-- Inquisitive denotation of the left argument `S`. -/
  sDen : Question W
  /-- Inquisitive denotation of the right argument `S'`. -/
  s'Den : Question W

namespace Sentence

variable {W : Type*}

/-- At-issue content of `S only S'`: every world where both
    `S` and `S'` are informatively true.
    @cite{ippolito-kiss-williams-2025} Def. 16. -/
def atIssueContent (d : Sentence W) : Set W :=
  d.sDen.info ∩ d.s'Den.info

/-- Presupposition / definedness condition for discourse *only*.
    @cite{ippolito-kiss-williams-2025} Def. 16:

    1. `S` is structurally relevant to the QUD;
    2. `S'` is structurally relevant to the QUD;
    3. `S` supports some answer α ∈ QUD via `Supports`. -/
def isDefined (d : Sentence W) (ctx : Context W) : Prop :=
  moveRelevant d.sDen ctx.qud ctx.subquestions ∧
  moveRelevant d.s'Den ctx.qud ctx.subquestions ∧
  ∃ α ∈ alt ctx.qud, Supports ctx.dox d.sDen α ctx.prior

/-- CI content of discourse *only*. @cite{ippolito-kiss-williams-2025}
    Def. 16: `∃ α ∈ QUD` such that
    (i)  every true partial answer `p` is positive evidence for `α`;
    (ii) `S` itself supports `α`;
    (iii) `S'` does **not** support `α`.

    When `partialAnswers` is empty, condition (i) is vacuously true:
    no prior evidence contradicts the direction. -/
def ciContent (d : Sentence W) (ctx : Context W) : Prop :=
  ∃ α ∈ alt ctx.qud,
    (∀ p ∈ ctx.partialAnswers, IsPositiveEvidence p α ctx.prior) ∧
    Supports ctx.dox d.sDen α ctx.prior ∧
    ¬ Supports ctx.dox d.s'Den α ctx.prior

/-- `S` and `S'` **agree** on the QUD: there is some `α ∈ QUD`
    that both `Supports`. Lifted from `Probabilistic.Agree`.
    @cite{ippolito-kiss-williams-2025} Def. 14a. -/
def agree (d : Sentence W) (ctx : Context W) : Prop :=
  Agree ctx.dox d.sDen d.s'Den ctx.qud ctx.prior

/-- `S` and `S'` **disagree** on the QUD. Lifted from
    `Probabilistic.Disagree`.
    @cite{ippolito-kiss-williams-2025} Def. 14b. -/
def disagree (d : Sentence W) (ctx : Context W) : Prop :=
  Disagree ctx.dox d.sDen d.s'Den ctx.qud ctx.prior

end Sentence

/-! ### Architectural derivations -/

/-- At-issue content unfolds as the intersection of informational
    content. -/
@[simp] theorem atIssue_eq_inter {W : Type*} (d : Sentence W) :
    d.atIssueContent = d.sDen.info ∩ d.s'Den.info := rfl

/-- @cite{ippolito-kiss-williams-2025} §5.2: an info-seeking
    interrogative cannot be the left argument because the speaker
    doesn't believe any of its alternatives, so `Supports` fails for
    every answer. Direct re-export of `Supports.of_no_belief_fails`. -/
theorem interrogative_blocks_support {W : Type*} {dox : Set W}
    {S : Question W} {μ : PMF W} {α : Set W}
    (h : ∀ q ∈ alt S, ¬ (dox ⊆ q)) :
    ¬ Supports dox S α μ :=
  Supports.of_no_belief_fails h

/-- @cite{ippolito-kiss-williams-2025} §5.2: an info-seeking
    interrogative `S'` trivially satisfies the CI's condition (ii) —
    `Supports` fails for every `α`, so `¬ Supports …` holds. -/
theorem interrogative_satisfies_ci_clause {W : Type*} {dox : Set W}
    {S' : Question W} {μ : PMF W} {α : Set W}
    (h : ∀ q ∈ alt S', ¬ (dox ⊆ q)) :
    ¬ Supports dox S' α μ :=
  Supports.of_no_belief_fails h

/-- Weak non-agreement (@cite{ippolito-kiss-williams-2025} p. 227): when
    `S'` cannot support any QUD answer, `S` and `S'` neither agree nor
    disagree. Both relations require `S'` to support *something*.

    Example (IKW ex. 18): "The house is beautiful, only can we afford
    it?" — `S` supports "buy the house", `S'` supports nothing. Not
    agreement, not disagreement: weak non-agreement. -/
theorem weak_non_agreement {W : Type*} (d : Sentence W) (ctx : Context W)
    (hS' : ∀ α ∈ alt ctx.qud, ¬ Supports ctx.dox d.s'Den α ctx.prior) :
    ¬ d.agree ctx ∧ ¬ d.disagree ctx := by
  refine ⟨?_, ?_⟩
  · rintro ⟨α, hMem, _, hS'α⟩
    exact hS' α hMem hS'α
  · rintro ⟨_, ⟨α, hMem, hS'α⟩, _⟩
    exact hS' α hMem hS'α

/-- @cite{ippolito-kiss-williams-2025} core insight: when `S` and `S'`
    evidentially clash (`disagree`) and there are no prior partial
    answers, the CI is automatically satisfied.

    Proof: pick the witness `α` from `S`'s support side; by ¬agree,
    `S'` cannot support that same `α`; the empty-partial-answers
    hypothesis discharges (i) vacuously. -/
theorem disagree_imp_ciContent_of_empty_partials {W : Type*}
    (d : Sentence W) (ctx : Context W)
    (hDisagree : d.disagree ctx) (hPartial : ctx.partialAnswers = []) :
    d.ciContent ctx := by
  obtain ⟨⟨α, hMem, hS⟩, _, hNotAgree⟩ := hDisagree
  refine ⟨α, hMem, ?_, hS, ?_⟩
  · intro p hp
    rw [hPartial] at hp
    simp at hp
  · intro hS'
    exact hNotAgree ⟨α, hMem, hS, hS'⟩

/-! ## Part I: End-to-End Derivation Chains

Concrete instantiations on a 8-world model of the house-buying
scenario (@cite{ippolito-kiss-williams-2025} §7). Connects the
substrate predictions to the empirical data in
`Phenomena/Focus/DiscourseOnly`. -/

open Phenomena.Focus.DiscourseOnly

/-! ### § 1: World Type and Propositions

8-world model. Encoding `w = 4b + 2e + r` where:

| World | Beautiful | Expensive | Renovated | Buy? |
|-------|-----------|-----------|-----------|------|
| w₀    | ✓         |           | ✓         | ✓    |
| w₁    | ✓         |           |           |      |
| w₂    | ✓         | ✓         | ✓         |      |
| w₃    | ✓         | ✓         |           |      |
| w₄    |           |           | ✓         |      |
| w₅    |           |           |           |      |
| w₆    |           | ✓         | ✓         |      |
| w₇    |           | ✓         |           |      |
-/
abbrev World := Fin 8

/-- The house is beautiful (w₀–w₃). -/
def beautiful : Set World := {w | w.val < 4}

instance : DecidablePred (· ∈ beautiful) := fun w => Nat.decLt w.val 4

/-- The house is expensive (w₂, w₃, w₆, w₇). -/
def expensive : Set World := {w | (w.val / 2) % 2 = 1}

instance : DecidablePred (· ∈ expensive) := fun w => Nat.decEq _ _

/-- The house has been renovated (w₀, w₂, w₄, w₆). -/
def renovated : Set World := {w | w.val % 2 = 0}

instance : DecidablePred (· ∈ renovated) := fun w => Nat.decEq _ _

/-- Should we buy the house? Only if beautiful, affordable, and
    renovated (w₀). -/
def buy : Set World := {w | w.val = 0}

instance : DecidablePred (· ∈ buy) := fun w => Nat.decEq _ _

/-- Uniform prior: P(w) = 1/8 for each world. -/
noncomputable def prior : PMF World :=
  PMF.ofFintype (fun _ => 1 / 8)
    (by rw [Fin.sum_univ_eight]; ennreal_arith)

/-! ### § 2: QUD and Denotations -/

/-- QUD: "Should we buy the house?" — binary issue. -/
def qud : Question World := Question.polar buy

/-- Declarative S: "The house is beautiful" — one alternative. -/
def sBeautiful : Question World := Question.polar beautiful

/-- Declarative S': "It's (very) expensive" — one alternative. -/
def s'Expensive : Question World := Question.polar expensive

/-- Polar Q S': "Has it been renovated?" — two alternatives. -/
def s'RenovatedQ : Question World := Question.polar renovated

/-! ### § 3: Doxastic States -/

/-- Speaker who asserts "beautiful" and "expensive": believes both.
    `dox = {w₂, w₃}` (beautiful ∧ expensive). -/
def doxBE : Set World := beautiful ∩ expensive

/-- Speaker who asserts "beautiful" but asks about renovation: believes
    beautiful, uncertain about expense and renovation.
    `dox = {w₀, w₁, w₂, w₃}` (beautiful). -/
def doxB : Set World := beautiful

/-! ### § 4: Contexts -/

/-- Context for core examples: S = "beautiful", S' = "expensive".
    No prior partial answers — fresh discourse.

    Subquestions per IKW §5.1 ("Answering this question requires
    answering its plausible subquestions, such as *Is the house
    beautiful? Is the house expensive?*"). We also include renovation
    since it appears in the polar Q examples. -/
noncomputable def coreCtx : Context World where
  qud := qud
  prior := prior
  dox := doxBE
  partialAnswers := []
  subquestions := [Question.polar beautiful, Question.polar expensive,
                   Question.polar renovated]

/-- Context for clause-type examples: S = "beautiful", S' =
    interrogative. Speaker believes S but doesn't know the answer to
    S'. Same subquestions as core context — the QUD structure doesn't
    change with clause type. -/
noncomputable def clauseTypeCtx : Context World where
  qud := qud
  prior := prior
  dox := doxB
  partialAnswers := []
  subquestions := [Question.polar beautiful, Question.polar expensive,
                   Question.polar renovated]

/-! ### § 5: Sentences -/

/-- "The house is beautiful, only it's expensive" (core
    declarative-declarative). -/
def declSentence : Sentence World where
  sDen := sBeautiful
  s'Den := s'Expensive

/-- "The house is beautiful, only has it been renovated?" (polar Q
    as S'). -/
def polarQSentence : Sentence World where
  sDen := sBeautiful
  s'Den := s'RenovatedQ

/-! ### § 6: Core Derivation: Declarative S + Declarative S' -/

section CoreDerivation

/-- The presupposition is satisfied: S' is relevant and S supports an
    answer.

    TODO: structured proof constructing witnesses for each conjunct.
    The Set/Prop API replaces the legacy `native_decide` over `Bool
    isDefined`. -/
theorem core_isDefined : declSentence.isDefined coreCtx := by sorry

/-- The CI holds: ∃α (= buy) s.t. all partial answers are positive
    evidence for α (vacuous), S supports α, and S' does not. -/
theorem core_ciContent : declSentence.ciContent coreCtx := by sorry

/-- The at-issue content is non-trivial: there exist worlds where both
    S and S' hold (e.g., w₂: beautiful ∧ expensive). -/
theorem core_atIssue_nonempty :
    (2 : World) ∈ declSentence.atIssueContent := by
  unfold Sentence.atIssueContent declSentence sBeautiful s'Expensive
  simp [Question.info_polar]

/-- S and S' disagree w.r.t. the QUD: S supports "buy" but S' supports
    "don't buy", and they don't agree on any single answer. -/
theorem core_disagree : declSentence.disagree coreCtx := by sorry

/-- Per-datum: predicts felicitous for the core declarative-declarative
    examples (Italian 29a, Russian 29b, Hungarian 29c, Mandarin 29d,
    English 2). -/
theorem core_predicted :
    declSentence.isDefined coreCtx ∧
    declSentence.ciContent coreCtx ∧
    italian_house.felicitous = true := ⟨core_isDefined, core_ciContent, rfl⟩

theorem russian_house_predicted :
    declSentence.isDefined coreCtx ∧
    declSentence.ciContent coreCtx ∧
    russian_house.felicitous = true := ⟨core_isDefined, core_ciContent, rfl⟩

theorem hungarian_house_predicted :
    declSentence.isDefined coreCtx ∧
    declSentence.ciContent coreCtx ∧
    hungarian_house.felicitous = true := ⟨core_isDefined, core_ciContent, rfl⟩

theorem mandarin_house_predicted :
    declSentence.isDefined coreCtx ∧
    declSentence.ciContent coreCtx ∧
    mandarin_house.felicitous = true := ⟨core_isDefined, core_ciContent, rfl⟩

theorem english_house_predicted :
    declSentence.isDefined coreCtx ∧
    declSentence.ciContent coreCtx ∧
    english_house.felicitous = true := ⟨core_isDefined, core_ciContent, rfl⟩

end CoreDerivation

/-! ### § 7: Clause-Type Derivation: Declarative S + Polar Q S' -/

section PolarQDerivation

/-- The presupposition is satisfied even with interrogative S': the
    polar Q "has it been renovated?" has alternatives [renovated,
    ¬renovated], and knowing whether the house is renovated is
    relevant to buying. -/
theorem polarQ_isDefined : polarQSentence.isDefined clauseTypeCtx := by sorry

/-- The CI holds: the speaker believes the house is beautiful, so S
    supports "buy". But the speaker doesn't know the answer to "has
    it been renovated?", so the doxastic condition of `Supports`
    fails for S' on every QUD answer. S' trivially fails to support
    the buying direction. -/
theorem polarQ_ciContent : polarQSentence.ciContent clauseTypeCtx := by sorry

/-- Per-datum: predicts felicitous for the polar-Q-as-S' examples
    (Russian 30a, Hungarian 31a, Mandarin 32a). -/
theorem russian_polarQ_predicted :
    polarQSentence.isDefined clauseTypeCtx ∧
    polarQSentence.ciContent clauseTypeCtx ∧
    russian_s'_polarQ.felicitous = true := ⟨polarQ_isDefined, polarQ_ciContent, rfl⟩

theorem hungarian_polarQ_predicted :
    polarQSentence.isDefined clauseTypeCtx ∧
    polarQSentence.ciContent clauseTypeCtx ∧
    hungarian_s'_polarQ.felicitous = true := ⟨polarQ_isDefined, polarQ_ciContent, rfl⟩

theorem mandarin_polarQ_predicted :
    polarQSentence.isDefined clauseTypeCtx ∧
    polarQSentence.ciContent clauseTypeCtx ∧
    mandarin_s'_polarQ.felicitous = true := ⟨polarQ_isDefined, polarQ_ciContent, rfl⟩

end PolarQDerivation

/-! ### § 8: Abstract theorem — interrogative S' trivially satisfies CI

For any context where S supports some QUD answer and S' is an
interrogative whose answer the speaker doesn't know, the CI's
condition (ii) is satisfied: S' trivially fails to support any answer
because `Supports` requires the doxastic condition (`dox ⊆ q`),
which fails when the speaker doesn't believe any alternative of S'.

This generalises the polar-Q derivation to all interrogative S'
examples (30a-d, 31a-d, 32a-d): the specific question content
doesn't matter for the CI — only that the speaker doesn't know the
answer. -/
theorem interrogative_s'_ci_satisfied {W' : Type*}
    (sent : Sentence W') (ctx : Context W')
    (hSsupports : ∃ α ∈ alt ctx.qud,
      Supports ctx.dox sent.sDen α ctx.prior)
    (hNoBelief : ∀ q ∈ alt sent.s'Den, ¬ (ctx.dox ⊆ q))
    (hPartial : ctx.partialAnswers = []) :
    sent.ciContent ctx := by
  obtain ⟨α, hMem, hSupp⟩ := hSsupports
  refine ⟨α, hMem, ?_, hSupp, ?_⟩
  · intro p hp
    rw [hPartial] at hp
    simp at hp
  · exact Supports.of_no_belief_fails hNoBelief

/-! ## Part II: DTS connection (@cite{merin-1999})

Connects discourse *only*'s CI to @cite{merin-1999}'s
Decision-Theoretic Semantics, specifically the notion of
unexpectedness from the analysis of *but*.

### Key Connection

Both *but* and discourse *only* express a form of evidential contrast:

* *but*: A is positively relevant and B is negatively relevant to H
  → B is unexpected given A (Theorem 8).
* discourse *only*: S supports α but S' does not support α
  → S' undermines the evidential direction.

### The *but*/*only* asymmetry (@cite{ippolito-kiss-williams-2025} §6)

*but* requires `negRelevant` (BF < 1): the second clause must actively
provide counter-evidence. Discourse *only* only requires
`¬probSupports`: the second clause merely fails to support the
direction. Since `negRelevant → ¬probSupports`, *but*'s condition is
strictly stronger: every *but* context could license discourse
*only*, but not vice versa. -/

open DTS DTS.But

/-! ### § 9: Witness structure -/

/-- A witness for the discourse *only* → DTS unexpectedness connection.

Bundles a DTS context together with two clausal arguments `s` and
`s'` (as `Set W`) and the evidence that `s` is positively relevant to
the topic H. Unlike the *but* witness, this does NOT require `s'` to
be negatively relevant — discourse *only* only requires `s'` to fail
to support, which is strictly weaker than negative relevance. -/
structure DTSDiscourseOnlyWitness (W : Type*) [Fintype W] where
  /-- The DTS context (dichotomic issue H + prior). -/
  dtsCtx : DTSContext W
  /-- Left clausal argument S. -/
  s : Set W
  /-- Decidability of `s` (lifted to a typeclass instance below). -/
  sDec : DecidablePred (· ∈ s)
  /-- Right clausal argument S'. -/
  s' : Set W
  /-- Decidability of `s'` (lifted to a typeclass instance below). -/
  s'Dec : DecidablePred (· ∈ s')
  /-- S is positively relevant to H. -/
  sPosRelevant : posRelevant dtsCtx s

attribute [instance] DTSDiscourseOnlyWitness.sDec DTSDiscourseOnlyWitness.s'Dec

/-! ### § 10: Bridge theorems -/

/-- Probabilistic support implies DTS positive relevance for binary
    issues.

    If `P(H|S) > P(H)` then `BF_H(S) > 1`. Both formalize the
    intuition that S provides evidence for H; this theorem
    establishes the direction needed for IKW's analysis.

    The bridge is Bayes' theorem: `P(H|S) > P(H) ↔ … ↔ BF > 1`. The
    full proof requires partition / total-mass lemmas for `probSum`
    over `Set.inter` / `Set.compl`. The legacy Bool-version proof used
    the parallel `probOfProp` API; on the Prop side those bridge
    lemmas need to be re-proved against `DTS.probSum`. Deferred. -/
theorem probSupports_implies_posRelevant_binary {W : Type*} [Fintype W]
    (prior : W → ℚ) (topic : Set W) [DecidablePred (· ∈ topic)]
    (evidence : Set W) [DecidablePred (· ∈ evidence)]
    (_hH_pos : probSum prior topic > 0)
    (_hNH_pos : probSum prior (topicᶜ) > 0)
    (_hS_pos : probSum prior evidence > 0)
    (_hNonneg : ∀ w, prior w ≥ 0)
    (_hNorm : probSum prior (Set.univ : Set W) = 1)
    (_hSupp : condProb prior evidence topic > margProb prior evidence) :
    posRelevant ⟨topic, inferInstance, prior⟩ evidence := by
  sorry

/-- Negative relevance (DTS) implies non-support (probabilistic).

    If `S'` is negatively relevant to H (BF < 1, i.e., `P(S'|H) <
    P(S'|¬H)`), then `S'` does not probabilistically support H — i.e.,
    `P(H|S') ≤ P(H)`. This is the formal content of IKW's observation
    that *but*'s condition on the second clause is strictly stronger
    than discourse *only*'s.

    By contrapositive: if `S'` did probabilistically support H, the
    previous theorem would give `posRelevant` (BF > 1), contradicting
    `negRelevant` (BF < 1). -/
theorem negRelevant_implies_not_probSupports {W : Type*} [Fintype W]
    (prior : W → ℚ) (topic : Set W) [DecidablePred (· ∈ topic)]
    (evidence : Set W) [DecidablePred (· ∈ evidence)]
    (hH_pos : probSum prior topic > 0)
    (hNH_pos : probSum prior (topicᶜ) > 0)
    (hS_pos : probSum prior evidence > 0)
    (hNonneg : ∀ w, prior w ≥ 0)
    (hNorm : probSum prior (Set.univ : Set W) = 1)
    (hNeg : negRelevant ⟨topic, inferInstance, prior⟩ evidence) :
    ¬ (condProb prior evidence topic > margProb prior evidence) := by
  intro hSupp
  have hPos := probSupports_implies_posRelevant_binary prior topic evidence
    hH_pos hNH_pos hS_pos hNonneg hNorm hSupp
  simp only [posRelevant, negRelevant] at hPos hNeg
  linarith

/-- Every *but* context can license discourse *only*.

    When `s` is `posRelevant` and `s'` is `negRelevant` (the *but*
    condition), `s'` also fails to probabilistically support H (the
    *only* condition). This formalizes
    @cite{ippolito-kiss-williams-2025} §6's claim that discourse
    *only* is strictly weaker than *but*. -/
theorem but_sufficient_for_only {W : Type*} [Fintype W]
    (prior : W → ℚ) (topic : Set W) [DecidablePred (· ∈ topic)]
    (s s' : Set W) [DecidablePred (· ∈ s)] [DecidablePred (· ∈ s')]
    (hH_pos : probSum prior topic > 0)
    (hNH_pos : probSum prior (topicᶜ) > 0)
    (_hS_pos : probSum prior s > 0)
    (hS'_pos : probSum prior s' > 0)
    (_hSpos : posRelevant ⟨topic, inferInstance, prior⟩ s)
    (hS'neg : negRelevant ⟨topic, inferInstance, prior⟩ s')
    (hNonneg : ∀ w, prior w ≥ 0)
    (hNorm : probSum prior (Set.univ : Set W) = 1) :
    ¬ (condProb prior s' topic > margProb prior s') :=
  negRelevant_implies_not_probSupports prior topic s' hH_pos hNH_pos hS'_pos
    hNonneg hNorm hS'neg

/-- Discourse *only*'s CI implies unexpectedness when the QUD is
    binary, S' is negatively relevant, and CIP holds.

    When S is `posRelevant` and S' is `negRelevant` (the stronger *but*
    condition), Merin's Theorem 8 gives `P(S'|S) < P(S')`: S' is
    unexpected given S.

    Note: this theorem uses the stronger *but* condition
    (`negRelevant`) rather than the weaker discourse *only* condition
    (`¬probSupports`). Unexpectedness in Merin's sense requires active
    counter-relevance, not just failure to support. So unexpectedness
    is a consequence when discourse *only* sentences happen to meet
    the stronger *but* threshold. -/
theorem discOnly_implies_unexpectedness_under_but {W : Type*} [Fintype W]
    (w : DTSDiscourseOnlyWitness W)
    (hS'neg : negRelevant w.dtsCtx w.s')
    (hPrior : ∀ x, w.dtsCtx.prior x ≥ 0)
    (hNorm : probSum w.dtsCtx.prior (Set.univ : Set W) = 1)
    (hS_pos : 0 < probSum w.dtsCtx.prior w.s)
    (hH_pos : 0 < probSum w.dtsCtx.prior w.dtsCtx.topic)
    (hNH_pos : 0 < probSum w.dtsCtx.prior (w.dtsCtx.topicᶜ))
    (hCIP : CIP w.dtsCtx w.s w.s') :
    condProb w.dtsCtx.prior w.s' w.s <
    margProb w.dtsCtx.prior w.s' :=
  cip_contrariness_implies_unexpectedness w.dtsCtx w.s w.s'
    hPrior hNorm hCIP (.inl ⟨w.sPosRelevant, hS'neg⟩) hS_pos hH_pos hNH_pos

end Phenomena.Focus.Studies.IppolitoKissWilliams2025
