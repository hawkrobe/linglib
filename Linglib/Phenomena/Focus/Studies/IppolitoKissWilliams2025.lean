import Linglib.Theories.Semantics.Questions.Probabilistic
import Linglib.Core.Question.Relevance
import Linglib.Phenomena.Focus.Studies.IppolitoKissWilliams2022
import Linglib.Phenomena.Focus.Studies.IppolitoKissWilliams2025.Data
import Linglib.Core.Probability.PMFFin
import Mathlib.Algebra.BigOperators.Fin

/-!
# @cite{ippolito-kiss-williams-2025}: Discourse *only*
@cite{ippolito-kiss-williams-2022} @cite{potts-2005} @cite{roberts-2012} @cite{thomas-2026}

Formalisation of @cite{ippolito-kiss-williams-2025} "Discourse only"
(WCCFL 41 proceedings, pp. 222–231). Discourse *only* is a clausal
connective taking two clausal arguments `S` and `S'` and contributing
a conventional implicature (CI) of *lack of agreement* between `S` and
`S'` w.r.t. a QUD.

The doxastic-evidential apparatus (`Supports`, `Agree`, `Disagree`)
that the paper's §4 statement uses is attributed by the paper itself
to the predecessor @cite{ippolito-kiss-williams-2022} ("Following
Ippolito et al. (2022) we define…"); it lives in
`Phenomena/Focus/Studies/IppolitoKissWilliams2022.lean` and is imported
here. This file owns the paper-specific bundling — `Sentence`,
`Context`, the felicity conditions of ex. (16), the architectural
derivations of §5.2, and the worked house-buying example of §7.

A previous "Part II: Bayesian-to-DTS bridge" was removed in 0.230.502:
@cite{merin-1999} is not cited in the paper's reference list, and
the §6 *only*-vs-*but* discussion grounds itself in
@cite{anscombre-ducrot-1977} and IKW 2022's notion of semantic equality
of *but*'s arguments — not in decision-theoretic semantics. The bridge
was the formaliser's editorial overlay; the substrate-internal Bayesian
theorems it contained (`probSupports_implies_posRelevant_binary`,
`negRelevant_implies_not_probSupports`) moved to
`Theories/Pragmatics/DecisionTheoretic/Core.lean` where they belong.

## The puzzle

Cross-linguistically, some languages have a discourse particle glossed
as "only" that conjoins two clauses while signalling that the second
undermines the evidential trajectory of the first. Paper (29a-d) all
use a single house-buying frame:

- Italian   *solo che*  ("La casa è bella, solo che è costosissima")
- Russian   *tol'ko*    ("Dom krasivyj, tol'ko ochen' dorogoj")
- Hungarian *csak*      ("Szép a ház, csak nagyon drága")
- Mandarin  *zhǐshì*    ("Zhège fángzi hěn piàoliang, zhǐshì yǒudiǎr guì")

## Paper ex. (16) — the proposal

`⟦S [only S']⟧^c` is defined only if `S` and `S'` are relevant to the
QUD in `c` and `∃ α ∈ QUD, S` supports `α`. If defined:

* **At-issue**: highlighted content of `S` intersected with that of `S'`
  — every world where both are informatively true.
* **CI**: `∃ α ∈ QUD` such that
  (i)  every true partial answer `p ∉ QUD` is positive evidence for `α`;
  (ii) `S'` does not support `α`.

The Lean `ciContent` (i) restricts to partial answers `p ∉ alt qud`
to match the paper's `p ∉ QUD` exclusion; the "p supports α" gloss is
implemented as `IsPositiveEvidence p α` rather than fully-doxastic
`Supports`, since established partial answers are presumed already
common-ground. A doxastic-gated variant is straightforward but
deferred.

## Architectural derivations

* **Interrogative left-arg restriction** (§5.2). Canonical info-seeking
  questions cannot be the left argument because the speaker doesn't
  believe any answer, so `dox ⊆ q` fails for all `q ∈ alt S`, so
  `Supports` fails. This falls out from `Supports.of_no_belief_fails`
  in `IppolitoKissWilliams2022.lean` — no clause-type filter required.
* **Biased / rhetorical questions can be left-args** (§5.2 ex. (20)–(21)).
  These have a believed answer (`dox ⊆ q` for some `q`), so the doxastic
  condition is satisfied.

## Layout

* **Substrate** (`Sentence`, `Context`, `isDefined`, `ciContent`,
  `agree`, `disagree`) and architectural theorems
  (`interrogative_blocks_support`, `weak_non_agreement`,
  `disagree_imp_ciContent_of_empty_partials`).
* **Part I**: end-to-end derivation chains for the house-buying
  scenario (§7), instantiating the substrate on a concrete 8-world
  model and connecting the predictions to the cross-linguistic data
  in the sibling `Data.lean`.
-/

namespace Phenomena.Focus.Studies.IppolitoKissWilliams2025

open Core Core.Question Semantics.Questions.Probabilistic
open Phenomena.Focus.Studies.IppolitoKissWilliams2022

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
      @cite{ippolito-kiss-williams-2025} ex. (16) CI clause (i)
      quantifies universally over all true partial answers `p ∉ QUD`. -/
  partialAnswers : List (Set W)
  /-- Subquestions of the QUD established by the discourse context.
      @cite{roberts-2012} (subquestion strategy); IKW §5.1: provided
      by the context, not computed. -/
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
    @cite{ippolito-kiss-williams-2025} ex. (16). -/
def atIssueContent (d : Sentence W) : Set W :=
  d.sDen.info ∩ d.s'Den.info

/-- Presupposition / definedness condition for discourse *only*.
    @cite{ippolito-kiss-williams-2025} ex. (16):

    1. `S` is structurally relevant to the QUD;
    2. `S'` is structurally relevant to the QUD;
    3. `S` supports some answer α ∈ QUD via `Supports`. -/
def isDefined (d : Sentence W) (ctx : Context W) : Prop :=
  moveRelevant d.sDen ctx.qud ctx.subquestions ∧
  moveRelevant d.s'Den ctx.qud ctx.subquestions ∧
  ∃ α ∈ alt ctx.qud, Supports ctx.dox d.sDen α ctx.prior

/-- CI content of discourse *only*. @cite{ippolito-kiss-williams-2025}
    ex. (16): `∃ α ∈ QUD` such that
    (i)  every true partial answer `p` **with `p ∉ QUD`** is positive
         evidence for `α`;
    (ii) `S` itself supports `α`;
    (iii) `S'` does **not** support `α`.

    The `p ∉ alt ctx.qud` exclusion in (i) matches the paper's
    `p ∉ QUD` restriction. The "p supports α" gloss is read here as
    raw `IsPositiveEvidence` (presuming established partial answers are
    common-ground); a doxastic-gated variant using the IKW 2022
    `Supports` predicate is straightforward but not currently used.

    When `partialAnswers` is empty, condition (i) is vacuously true:
    no prior evidence contradicts the direction. -/
def ciContent (d : Sentence W) (ctx : Context W) : Prop :=
  ∃ α ∈ alt ctx.qud,
    (∀ p ∈ ctx.partialAnswers, p ∉ alt ctx.qud →
      IsPositiveEvidence p α ctx.prior) ∧
    Supports ctx.dox d.sDen α ctx.prior ∧
    ¬ Supports ctx.dox d.s'Den α ctx.prior

/-- `S` and `S'` **agree** on the QUD: there is some `α ∈ QUD`
    that both `Supports`. Lifted from `IKW2022.Agree`.
    @cite{ippolito-kiss-williams-2025} ex. (14a). -/
def agree (d : Sentence W) (ctx : Context W) : Prop :=
  Agree ctx.dox d.sDen d.s'Den ctx.qud ctx.prior

/-- `S` and `S'` **disagree** on the QUD. Lifted from
    `IKW2022.Disagree`.
    @cite{ippolito-kiss-williams-2025} ex. (14b). -/
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

/-- Weak non-agreement (@cite{ippolito-kiss-williams-2025} §5.2 prose
    around ex. (18)): when `S'` cannot support any QUD answer, `S` and
    `S'` neither agree nor disagree. Both relations require `S'` to
    support *something*.

    Example IKW ex. (18): "The house is beautiful, only can we afford
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
substrate predictions to the empirical data in the sibling `Data.lean`
under this study's subdirectory. -/

open Phenomena.Focus.Studies.IppolitoKissWilliams2025.Data

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

instance : DecidablePred (· ∈ beautiful) := λ w => Nat.decLt w.val 4

/-- The house is expensive (w₂, w₃, w₆, w₇). -/
def expensive : Set World := {w | (w.val / 2) % 2 = 1}

instance : DecidablePred (· ∈ expensive) := λ _ => Nat.decEq _ _

/-- The house has been renovated (w₀, w₂, w₄, w₆). -/
def renovated : Set World := {w | w.val % 2 = 0}

instance : DecidablePred (· ∈ renovated) := λ _ => Nat.decEq _ _

/-- Should we buy the house? Only if beautiful, affordable, and
    renovated (w₀). -/
def buy : Set World := {w | w.val = 0}

instance : DecidablePred (· ∈ buy) := λ _ => Nat.decEq _ _

/-- Uniform prior: P(w) = 1/8 for each world. -/
noncomputable def prior : PMF World :=
  PMF.ofFintype (λ _ => 1 / 8)
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

/-! ### § 6: Core Derivation: Declarative S + Declarative S'

The five sorries discharged in §6 and §7 establish the §7 cross-linguistic
predictions on a concrete 8-world model with uniform prior. The PMF
arithmetic reduces to four base probabilities (`beautiful`, `expensive`,
their intersections with `buy`/`buyᶜ`) computed via
`PMF.probOfSet_apply` + `Fin.sum_univ_eight`. The doxastic `⊆` checks
and the `moveRelevant` reductions (via `moveRelevant_polar_iff`) are
pure Set arithmetic discharged by `decide`.
-/

section CoreDerivation

open scoped ENNReal

/-- Each world has prior mass `1/8` under the uniform 8-world prior. -/
private lemma prior_apply (a : World) : prior a = (1 : ℝ≥0∞) / 8 := rfl

/-- Reduces `prior.probOfSet S` on a decidable subset to an explicit
    8-fold conditional sum. The lifting through `PMF.probOfSet_apply` +
    `Fin.sum_univ_eight` happens once; specialised lemmas then unfold
    the set predicate and apply `ennreal_arith` on the residual. -/
private lemma prior_probOfSet_expand (S : Set World) [DecidablePred (· ∈ S)] :
    prior.probOfSet S =
      (if (⟨0, by decide⟩ : Fin 8) ∈ S then (1 : ℝ≥0∞)/8 else 0) +
      (if (⟨1, by decide⟩ : Fin 8) ∈ S then (1 : ℝ≥0∞)/8 else 0) +
      (if (⟨2, by decide⟩ : Fin 8) ∈ S then (1 : ℝ≥0∞)/8 else 0) +
      (if (⟨3, by decide⟩ : Fin 8) ∈ S then (1 : ℝ≥0∞)/8 else 0) +
      (if (⟨4, by decide⟩ : Fin 8) ∈ S then (1 : ℝ≥0∞)/8 else 0) +
      (if (⟨5, by decide⟩ : Fin 8) ∈ S then (1 : ℝ≥0∞)/8 else 0) +
      (if (⟨6, by decide⟩ : Fin 8) ∈ S then (1 : ℝ≥0∞)/8 else 0) +
      (if (⟨7, by decide⟩ : Fin 8) ∈ S then (1 : ℝ≥0∞)/8 else 0) := by
  rw [PMF.probOfSet_apply, Fin.sum_univ_eight]; rfl

/-- The 8 base probabilities the §6/§7 derivations need. Each follows the
    same pattern: expand via `prior_probOfSet_expand`, unfold the set
    predicate, reduce each `(⟨i, _⟩ : Fin 8).val` to a numeric literal,
    then discharge the residual ENNReal arithmetic with `ennreal_arith`. -/
private lemma prior_beautiful : prior.probOfSet beautiful = (1 : ℝ≥0∞) / 2 := by
  rw [prior_probOfSet_expand]
  simp only [beautiful, Set.mem_setOf_eq,
             show ((⟨0, by decide⟩ : Fin 8).val < 4) by decide,
             show ((⟨1, by decide⟩ : Fin 8).val < 4) by decide,
             show ((⟨2, by decide⟩ : Fin 8).val < 4) by decide,
             show ((⟨3, by decide⟩ : Fin 8).val < 4) by decide,
             show ¬ ((⟨4, by decide⟩ : Fin 8).val < 4) by decide,
             show ¬ ((⟨5, by decide⟩ : Fin 8).val < 4) by decide,
             show ¬ ((⟨6, by decide⟩ : Fin 8).val < 4) by decide,
             show ¬ ((⟨7, by decide⟩ : Fin 8).val < 4) by decide,
             if_true, if_false]
  ennreal_arith

private lemma prior_expensive : prior.probOfSet expensive = (1 : ℝ≥0∞) / 2 := by
  rw [prior_probOfSet_expand]
  simp only [expensive, Set.mem_setOf_eq,
             show ¬ (((⟨0, by decide⟩ : Fin 8).val / 2) % 2 = 1) by decide,
             show ¬ (((⟨1, by decide⟩ : Fin 8).val / 2) % 2 = 1) by decide,
             show (((⟨2, by decide⟩ : Fin 8).val / 2) % 2 = 1) by decide,
             show (((⟨3, by decide⟩ : Fin 8).val / 2) % 2 = 1) by decide,
             show ¬ (((⟨4, by decide⟩ : Fin 8).val / 2) % 2 = 1) by decide,
             show ¬ (((⟨5, by decide⟩ : Fin 8).val / 2) % 2 = 1) by decide,
             show (((⟨6, by decide⟩ : Fin 8).val / 2) % 2 = 1) by decide,
             show (((⟨7, by decide⟩ : Fin 8).val / 2) % 2 = 1) by decide,
             if_true, if_false]
  ennreal_arith

private lemma prior_buy : prior.probOfSet buy = (1 : ℝ≥0∞) / 8 := by
  rw [prior_probOfSet_expand]
  simp only [buy, Set.mem_setOf_eq,
             show ((⟨0, by decide⟩ : Fin 8).val = 0) by decide,
             show ¬ ((⟨1, by decide⟩ : Fin 8).val = 0) by decide,
             show ¬ ((⟨2, by decide⟩ : Fin 8).val = 0) by decide,
             show ¬ ((⟨3, by decide⟩ : Fin 8).val = 0) by decide,
             show ¬ ((⟨4, by decide⟩ : Fin 8).val = 0) by decide,
             show ¬ ((⟨5, by decide⟩ : Fin 8).val = 0) by decide,
             show ¬ ((⟨6, by decide⟩ : Fin 8).val = 0) by decide,
             show ¬ ((⟨7, by decide⟩ : Fin 8).val = 0) by decide,
             if_true, if_false]
  ennreal_arith

private lemma prior_buy_compl : prior.probOfSet (buyᶜ) = (7 : ℝ≥0∞) / 8 := by
  rw [prior_probOfSet_expand]
  simp only [buy, Set.mem_compl_iff, Set.mem_setOf_eq,
             show ((⟨0, by decide⟩ : Fin 8).val = 0) by decide,
             show ¬ ((⟨1, by decide⟩ : Fin 8).val = 0) by decide,
             show ¬ ((⟨2, by decide⟩ : Fin 8).val = 0) by decide,
             show ¬ ((⟨3, by decide⟩ : Fin 8).val = 0) by decide,
             show ¬ ((⟨4, by decide⟩ : Fin 8).val = 0) by decide,
             show ¬ ((⟨5, by decide⟩ : Fin 8).val = 0) by decide,
             show ¬ ((⟨6, by decide⟩ : Fin 8).val = 0) by decide,
             show ¬ ((⟨7, by decide⟩ : Fin 8).val = 0) by decide,
             not_true, not_false_eq_true, if_true, if_false]
  ennreal_arith

private lemma prior_beautiful_inter_buy :
    prior.probOfSet (beautiful ∩ buy) = (1 : ℝ≥0∞) / 8 := by
  rw [prior_probOfSet_expand]
  simp only [beautiful, buy, Set.mem_inter_iff, Set.mem_setOf_eq,
             show ((⟨0, by decide⟩ : Fin 8).val < 4 ∧
                   (⟨0, by decide⟩ : Fin 8).val = 0) by decide,
             show ¬ ((⟨1, by decide⟩ : Fin 8).val < 4 ∧
                     (⟨1, by decide⟩ : Fin 8).val = 0) by decide,
             show ¬ ((⟨2, by decide⟩ : Fin 8).val < 4 ∧
                     (⟨2, by decide⟩ : Fin 8).val = 0) by decide,
             show ¬ ((⟨3, by decide⟩ : Fin 8).val < 4 ∧
                     (⟨3, by decide⟩ : Fin 8).val = 0) by decide,
             show ¬ ((⟨4, by decide⟩ : Fin 8).val < 4 ∧
                     (⟨4, by decide⟩ : Fin 8).val = 0) by decide,
             show ¬ ((⟨5, by decide⟩ : Fin 8).val < 4 ∧
                     (⟨5, by decide⟩ : Fin 8).val = 0) by decide,
             show ¬ ((⟨6, by decide⟩ : Fin 8).val < 4 ∧
                     (⟨6, by decide⟩ : Fin 8).val = 0) by decide,
             show ¬ ((⟨7, by decide⟩ : Fin 8).val < 4 ∧
                     (⟨7, by decide⟩ : Fin 8).val = 0) by decide,
             if_true, if_false]
  ennreal_arith

private lemma prior_beautiful_inter_buy_compl :
    prior.probOfSet (beautiful ∩ buyᶜ) = (3 : ℝ≥0∞) / 8 := by
  rw [prior_probOfSet_expand]
  simp only [beautiful, buy, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_setOf_eq,
             show ¬ ((⟨0, by decide⟩ : Fin 8).val < 4 ∧
                     ¬ (⟨0, by decide⟩ : Fin 8).val = 0) by decide,
             show ((⟨1, by decide⟩ : Fin 8).val < 4 ∧
                   ¬ (⟨1, by decide⟩ : Fin 8).val = 0) by decide,
             show ((⟨2, by decide⟩ : Fin 8).val < 4 ∧
                   ¬ (⟨2, by decide⟩ : Fin 8).val = 0) by decide,
             show ((⟨3, by decide⟩ : Fin 8).val < 4 ∧
                   ¬ (⟨3, by decide⟩ : Fin 8).val = 0) by decide,
             show ¬ ((⟨4, by decide⟩ : Fin 8).val < 4 ∧
                     ¬ (⟨4, by decide⟩ : Fin 8).val = 0) by decide,
             show ¬ ((⟨5, by decide⟩ : Fin 8).val < 4 ∧
                     ¬ (⟨5, by decide⟩ : Fin 8).val = 0) by decide,
             show ¬ ((⟨6, by decide⟩ : Fin 8).val < 4 ∧
                     ¬ (⟨6, by decide⟩ : Fin 8).val = 0) by decide,
             show ¬ ((⟨7, by decide⟩ : Fin 8).val < 4 ∧
                     ¬ (⟨7, by decide⟩ : Fin 8).val = 0) by decide,
             if_true, if_false]
  ennreal_arith

private lemma prior_expensive_inter_buy :
    prior.probOfSet (expensive ∩ buy) = 0 := by
  rw [prior_probOfSet_expand]
  simp only [expensive, buy, Set.mem_inter_iff, Set.mem_setOf_eq,
             show ¬ (((⟨0, by decide⟩ : Fin 8).val / 2) % 2 = 1 ∧
                     (⟨0, by decide⟩ : Fin 8).val = 0) by decide,
             show ¬ (((⟨1, by decide⟩ : Fin 8).val / 2) % 2 = 1 ∧
                     (⟨1, by decide⟩ : Fin 8).val = 0) by decide,
             show ¬ (((⟨2, by decide⟩ : Fin 8).val / 2) % 2 = 1 ∧
                     (⟨2, by decide⟩ : Fin 8).val = 0) by decide,
             show ¬ (((⟨3, by decide⟩ : Fin 8).val / 2) % 2 = 1 ∧
                     (⟨3, by decide⟩ : Fin 8).val = 0) by decide,
             show ¬ (((⟨4, by decide⟩ : Fin 8).val / 2) % 2 = 1 ∧
                     (⟨4, by decide⟩ : Fin 8).val = 0) by decide,
             show ¬ (((⟨5, by decide⟩ : Fin 8).val / 2) % 2 = 1 ∧
                     (⟨5, by decide⟩ : Fin 8).val = 0) by decide,
             show ¬ (((⟨6, by decide⟩ : Fin 8).val / 2) % 2 = 1 ∧
                     (⟨6, by decide⟩ : Fin 8).val = 0) by decide,
             show ¬ (((⟨7, by decide⟩ : Fin 8).val / 2) % 2 = 1 ∧
                     (⟨7, by decide⟩ : Fin 8).val = 0) by decide,
             if_false]
  ennreal_arith

private lemma prior_expensive_inter_buy_compl :
    prior.probOfSet (expensive ∩ buyᶜ) = (1 : ℝ≥0∞) / 2 := by
  rw [prior_probOfSet_expand]
  simp only [expensive, buy, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_setOf_eq,
             show ¬ (((⟨0, by decide⟩ : Fin 8).val / 2) % 2 = 1 ∧
                     ¬ (⟨0, by decide⟩ : Fin 8).val = 0) by decide,
             show ¬ (((⟨1, by decide⟩ : Fin 8).val / 2) % 2 = 1 ∧
                     ¬ (⟨1, by decide⟩ : Fin 8).val = 0) by decide,
             show (((⟨2, by decide⟩ : Fin 8).val / 2) % 2 = 1 ∧
                   ¬ (⟨2, by decide⟩ : Fin 8).val = 0) by decide,
             show (((⟨3, by decide⟩ : Fin 8).val / 2) % 2 = 1 ∧
                   ¬ (⟨3, by decide⟩ : Fin 8).val = 0) by decide,
             show ¬ (((⟨4, by decide⟩ : Fin 8).val / 2) % 2 = 1 ∧
                     ¬ (⟨4, by decide⟩ : Fin 8).val = 0) by decide,
             show ¬ (((⟨5, by decide⟩ : Fin 8).val / 2) % 2 = 1 ∧
                     ¬ (⟨5, by decide⟩ : Fin 8).val = 0) by decide,
             show (((⟨6, by decide⟩ : Fin 8).val / 2) % 2 = 1 ∧
                   ¬ (⟨6, by decide⟩ : Fin 8).val = 0) by decide,
             show (((⟨7, by decide⟩ : Fin 8).val / 2) % 2 = 1 ∧
                   ¬ (⟨7, by decide⟩ : Fin 8).val = 0) by decide,
             if_true, if_false]
  ennreal_arith

/-! #### Bayesian-evidence facts and `Supports` witnesses -/

/-- `beautiful` is positive evidence for `buy`: P(buy | beautiful) = 1/4 > 1/8 = P(buy). -/
private lemma beautiful_pos_evidence_buy :
    IsPositiveEvidence beautiful buy prior := by
  show prior.condProbSet beautiful buy > prior.probOfSet buy
  rw [PMF.condProbSet_eq_div, prior_beautiful_inter_buy, prior_beautiful, prior_buy]
  ennreal_arith

/-- `expensive` is positive evidence for `buyᶜ`: P(¬buy | expensive) = 1 > 7/8. -/
private lemma expensive_pos_evidence_buy_compl :
    IsPositiveEvidence expensive buyᶜ prior := by
  show prior.condProbSet expensive buyᶜ > prior.probOfSet buyᶜ
  rw [PMF.condProbSet_eq_div, prior_expensive_inter_buy_compl, prior_expensive, prior_buy_compl]
  ennreal_arith

/-- `expensive` is NOT positive evidence for `buy`: P(buy | expensive) = 0, fails to
    exceed 1/8 = P(buy). -/
private lemma expensive_not_pos_evidence_buy :
    ¬ IsPositiveEvidence expensive buy prior := by
  show ¬ prior.condProbSet expensive buy > prior.probOfSet buy
  rw [PMF.condProbSet_eq_div, prior_expensive_inter_buy, prior_expensive, prior_buy]
  ennreal_arith

/-- `beautiful` is NOT positive evidence for `buyᶜ`: P(¬buy | beautiful) = 3/4 = 6/8,
    fails to exceed 7/8 = P(¬buy). -/
private lemma beautiful_not_pos_evidence_buy_compl :
    ¬ IsPositiveEvidence beautiful buyᶜ prior := by
  show ¬ prior.condProbSet beautiful buyᶜ > prior.probOfSet buyᶜ
  rw [PMF.condProbSet_eq_div, prior_beautiful_inter_buy_compl, prior_beautiful, prior_buy_compl]
  ennreal_arith

/-- `buy` and `buyᶜ` are nontrivial in this 8-world model. -/
private lemma buy_ne_empty : (buy : Set World) ≠ ∅ := by
  intro h; have : (⟨0, by decide⟩ : World) ∈ (∅ : Set World) := h ▸ rfl; exact this

private lemma buy_ne_univ : (buy : Set World) ≠ Set.univ := by
  intro h; have : (⟨1, by decide⟩ : World) ∈ buy := h ▸ Set.mem_univ _
  exact absurd this (by show ¬ ((⟨1, by decide⟩ : Fin 8).val = 0); decide)

private lemma beautiful_ne_empty : (beautiful : Set World) ≠ ∅ := by
  intro h; have : (⟨0, by decide⟩ : World) ∈ (∅ : Set World) := h ▸ (by decide); exact this

private lemma beautiful_ne_univ : (beautiful : Set World) ≠ Set.univ := by
  intro h; have : (⟨7, by decide⟩ : World) ∈ beautiful := h ▸ Set.mem_univ _
  exact absurd this (by show ¬ ((⟨7, by decide⟩ : Fin 8).val < 4); decide)

private lemma expensive_ne_empty : (expensive : Set World) ≠ ∅ := by
  intro h; have : (⟨2, by decide⟩ : World) ∈ (∅ : Set World) := h ▸ (by decide); exact this

private lemma expensive_ne_univ : (expensive : Set World) ≠ Set.univ := by
  intro h; have : (⟨0, by decide⟩ : World) ∈ expensive := h ▸ Set.mem_univ _
  exact absurd this (by show ¬ (((⟨0, by decide⟩ : Fin 8).val / 2) % 2 = 1); decide)

private lemma renovated_ne_empty : (renovated : Set World) ≠ ∅ := by
  intro h; have : (⟨0, by decide⟩ : World) ∈ (∅ : Set World) := h ▸ (by decide); exact this

private lemma renovated_ne_univ : (renovated : Set World) ≠ Set.univ := by
  intro h; have : (⟨1, by decide⟩ : World) ∈ renovated := h ▸ Set.mem_univ _
  exact absurd this (by show ¬ ((⟨1, by decide⟩ : Fin 8).val % 2 = 0); decide)

/-- `doxBE = beautiful ∩ expensive` is a subset of `beautiful`. -/
private lemma doxBE_subset_beautiful : doxBE ⊆ beautiful :=
  Set.inter_subset_left

/-- `doxBE = beautiful ∩ expensive` is a subset of `expensive`. -/
private lemma doxBE_subset_expensive : doxBE ⊆ expensive :=
  Set.inter_subset_right

/-- `doxBE` is NOT a subset of `expensiveᶜ`: world `2 ∈ doxBE ∩ expensive`. -/
private lemma doxBE_not_subset_expensive_compl : ¬ doxBE ⊆ expensiveᶜ := by
  intro h
  have h2 : (⟨2, by decide⟩ : World) ∈ doxBE := by
    show _ ∈ beautiful ∩ expensive
    refine ⟨?_, ?_⟩ <;> (show _ ; decide)
  have h2c : (⟨2, by decide⟩ : World) ∈ expensiveᶜ := h h2
  exact absurd h2c (by show ¬ ¬ _; rw [not_not]; show _ ; decide)

/-- `doxBE` is NOT a subset of `beautifulᶜ`: world `2 ∈ doxBE ∩ beautiful`. -/
private lemma doxBE_not_subset_beautiful_compl : ¬ doxBE ⊆ beautifulᶜ := by
  intro h
  have h2 : (⟨2, by decide⟩ : World) ∈ doxBE := by
    show _ ∈ beautiful ∩ expensive
    refine ⟨?_, ?_⟩ <;> (show _ ; decide)
  have h2c : (⟨2, by decide⟩ : World) ∈ beautifulᶜ := h h2
  exact absurd h2c (by show ¬ ¬ _; rw [not_not]; show _ ; decide)

/-- `S = sBeautiful` supports `buy` under `doxBE`: witness `q = beautiful`. -/
private lemma sBeautiful_supports_buy_doxBE :
    Supports doxBE sBeautiful buy prior := by
  refine ⟨beautiful, ?_, doxBE_subset_beautiful, beautiful_pos_evidence_buy⟩
  rw [show sBeautiful = Question.polar beautiful from rfl,
      alt_polar_of_nontrivial beautiful_ne_empty beautiful_ne_univ]
  exact Set.mem_insert _ _

/-- `S' = s'Expensive` supports `buyᶜ` under `doxBE`: witness `q = expensive`. -/
private lemma sExpensive_supports_buy_compl_doxBE :
    Supports doxBE s'Expensive buyᶜ prior := by
  refine ⟨expensive, ?_, doxBE_subset_expensive, expensive_pos_evidence_buy_compl⟩
  rw [show s'Expensive = Question.polar expensive from rfl,
      alt_polar_of_nontrivial expensive_ne_empty expensive_ne_univ]
  exact Set.mem_insert _ _

/-- `S' = s'Expensive` does NOT support `buy` under `doxBE`. Both alternatives
    of `s'Expensive` fail: `expensive` provides zero evidence for `buy`,
    `expensiveᶜ` fails the doxastic condition. -/
private lemma sExpensive_not_supports_buy_doxBE :
    ¬ Supports doxBE s'Expensive buy prior := by
  rintro ⟨q, hq, hdox, hpos⟩
  rw [show s'Expensive = Question.polar expensive from rfl,
      alt_polar_of_nontrivial expensive_ne_empty expensive_ne_univ] at hq
  rcases hq with hq | hq
  · subst hq; exact expensive_not_pos_evidence_buy hpos
  · rw [Set.mem_singleton_iff] at hq; subst hq
    exact doxBE_not_subset_expensive_compl hdox

/-- `S = sBeautiful` does NOT support `buyᶜ` under `doxBE`. `beautiful` fails
    the positive-evidence test for `buyᶜ`; `beautifulᶜ` fails the doxastic check. -/
private lemma sBeautiful_not_supports_buy_compl_doxBE :
    ¬ Supports doxBE sBeautiful buyᶜ prior := by
  rintro ⟨q, hq, hdox, hpos⟩
  rw [show sBeautiful = Question.polar beautiful from rfl,
      alt_polar_of_nontrivial beautiful_ne_empty beautiful_ne_univ] at hq
  rcases hq with hq | hq
  · subst hq; exact beautiful_not_pos_evidence_buy_compl hpos
  · rw [Set.mem_singleton_iff] at hq; subst hq
    exact doxBE_not_subset_beautiful_compl hdox

/-! #### Discharged theorems -/

/-- The presupposition is satisfied: both arguments are relevant via the
    explicit subquestion list, and `S` supports `buy` from `doxBE`. -/
theorem core_isDefined : declSentence.isDefined coreCtx := by
  refine ⟨?_, ?_, ?_⟩
  · -- moveRelevant sBeautiful coreCtx.qud coreCtx.subquestions
    -- via the `polar beautiful` subquestion in coreCtx.subquestions
    rw [show declSentence.sDen = Question.polar beautiful from rfl,
        moveRelevant_polar_iff beautiful_ne_empty beautiful_ne_univ]
    refine Or.inl (Or.inr ?_)
    refine ⟨Question.polar beautiful, ?_, ?_⟩
    · show Question.polar beautiful ∈ coreCtx.subquestions
      simp [coreCtx]
    · rw [partiallyAnswers_polar_iff beautiful_ne_empty beautiful_ne_univ]
      exact Or.inl Set.Subset.rfl
  · -- moveRelevant s'Expensive coreCtx.qud coreCtx.subquestions
    rw [show declSentence.s'Den = Question.polar expensive from rfl,
        moveRelevant_polar_iff expensive_ne_empty expensive_ne_univ]
    refine Or.inl (Or.inr ?_)
    refine ⟨Question.polar expensive, ?_, ?_⟩
    · show Question.polar expensive ∈ coreCtx.subquestions
      simp [coreCtx]
    · rw [partiallyAnswers_polar_iff expensive_ne_empty expensive_ne_univ]
      exact Or.inl Set.Subset.rfl
  · -- ∃ α ∈ alt qud, Supports doxBE sBeautiful α prior
    refine ⟨buy, ?_, sBeautiful_supports_buy_doxBE⟩
    show buy ∈ alt (Question.polar buy)
    rw [alt_polar_of_nontrivial buy_ne_empty buy_ne_univ]
    exact Set.mem_insert _ _

/-- The CI holds: ∃α (= buy) s.t. all partial answers are positive
    evidence for α (vacuous, since `coreCtx.partialAnswers = []`),
    S supports α, and S' does not. -/
theorem core_ciContent : declSentence.ciContent coreCtx := by
  refine ⟨buy, ?_, ?_, sBeautiful_supports_buy_doxBE, sExpensive_not_supports_buy_doxBE⟩
  · show buy ∈ alt (Question.polar buy)
    rw [alt_polar_of_nontrivial buy_ne_empty buy_ne_univ]
    exact Set.mem_insert _ _
  · -- ∀ p ∈ partialAnswers (= []), ...
    intro p hp _
    exact absurd hp (by simp [coreCtx])

/-- The at-issue content is non-trivial: there exist worlds where both
    S and S' hold (e.g., w₂: beautiful ∧ expensive). -/
theorem core_atIssue_nonempty :
    (2 : World) ∈ declSentence.atIssueContent := by
  unfold Sentence.atIssueContent declSentence sBeautiful s'Expensive
  simp [Question.info_polar]

/-- S and S' disagree w.r.t. the QUD: S supports "buy", S' supports
    "don't buy", no shared answer is supported by both. -/
theorem core_disagree : declSentence.disagree coreCtx := by
  refine ⟨?_, ?_, ?_⟩
  · -- S supports something
    refine ⟨buy, ?_, sBeautiful_supports_buy_doxBE⟩
    show buy ∈ alt (Question.polar buy)
    rw [alt_polar_of_nontrivial buy_ne_empty buy_ne_univ]
    exact Set.mem_insert _ _
  · -- S' supports something
    refine ⟨buyᶜ, ?_, sExpensive_supports_buy_compl_doxBE⟩
    show buyᶜ ∈ alt (Question.polar buy)
    rw [alt_polar_of_nontrivial buy_ne_empty buy_ne_univ]
    exact Set.mem_insert_of_mem _ rfl
  · -- ¬ Agree: refute shared support
    rintro ⟨α, hα, hSα, hS'α⟩
    rw [show declSentence.s'Den = Question.polar expensive from rfl] at hS'α
    rw [show declSentence.sDen = Question.polar beautiful from rfl] at hSα
    rw [show coreCtx.qud = Question.polar buy from rfl,
        alt_polar_of_nontrivial buy_ne_empty buy_ne_univ] at hα
    rcases hα with hα | hα
    · subst hα
      exact sExpensive_not_supports_buy_doxBE hS'α
    · rw [Set.mem_singleton_iff] at hα; subst hα
      exact sBeautiful_not_supports_buy_compl_doxBE hSα

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

/-! #### `doxB`-specific helpers (for the polar-Q derivation) -/

/-- Under `doxB = beautiful`, `S = sBeautiful` supports `buy`. -/
private lemma sBeautiful_supports_buy_doxB :
    Supports doxB sBeautiful buy prior := by
  refine ⟨beautiful, ?_, ?_, beautiful_pos_evidence_buy⟩
  · rw [show sBeautiful = Question.polar beautiful from rfl,
        alt_polar_of_nontrivial beautiful_ne_empty beautiful_ne_univ]
    exact Set.mem_insert _ _
  · -- doxB = beautiful ⊆ beautiful
    show beautiful ⊆ beautiful
    exact Set.Subset.rfl

/-- `doxB = beautiful` is NOT a subset of `renovated`: world `1 ∈ doxB`
    but `1 ∉ renovated` (1 is odd, so `1 % 2 = 1 ≠ 0`). -/
private lemma doxB_not_subset_renovated : ¬ doxB ⊆ renovated := by
  intro h
  have h1 : (⟨1, by decide⟩ : World) ∈ doxB := by
    show (⟨1, by decide⟩ : Fin 8).val < 4; decide
  exact absurd (h h1) (by show ¬ ((⟨1, by decide⟩ : Fin 8).val % 2 = 0); decide)

/-- `doxB = beautiful` is NOT a subset of `renovatedᶜ`: world `0 ∈ doxB`
    but `0 ∈ renovated`, so `0 ∉ renovatedᶜ`. -/
private lemma doxB_not_subset_renovated_compl : ¬ doxB ⊆ renovatedᶜ := by
  intro h
  have h0 : (⟨0, by decide⟩ : World) ∈ doxB := by
    show (⟨0, by decide⟩ : Fin 8).val < 4; decide
  have h0c : (⟨0, by decide⟩ : World) ∈ renovatedᶜ := h h0
  exact absurd h0c (by
    show ¬ ¬ _; rw [not_not]; show (⟨0, by decide⟩ : Fin 8).val % 2 = 0; decide)

/-- The presupposition is satisfied even with interrogative S'. The
    `polar renovated` subquestion in `clauseTypeCtx.subquestions` discharges
    the relevance of `s'RenovatedQ`. -/
theorem polarQ_isDefined : polarQSentence.isDefined clauseTypeCtx := by
  refine ⟨?_, ?_, ?_⟩
  · -- moveRelevant sBeautiful via polar beautiful subquestion
    rw [show polarQSentence.sDen = Question.polar beautiful from rfl,
        moveRelevant_polar_iff beautiful_ne_empty beautiful_ne_univ]
    refine Or.inl (Or.inr ?_)
    refine ⟨Question.polar beautiful, ?_, ?_⟩
    · show Question.polar beautiful ∈ clauseTypeCtx.subquestions
      simp [clauseTypeCtx]
    · rw [partiallyAnswers_polar_iff beautiful_ne_empty beautiful_ne_univ]
      exact Or.inl Set.Subset.rfl
  · -- moveRelevant s'RenovatedQ via polar renovated subquestion
    rw [show polarQSentence.s'Den = Question.polar renovated from rfl,
        moveRelevant_polar_iff renovated_ne_empty renovated_ne_univ]
    refine Or.inl (Or.inr ?_)
    refine ⟨Question.polar renovated, ?_, ?_⟩
    · show Question.polar renovated ∈ clauseTypeCtx.subquestions
      simp [clauseTypeCtx]
    · rw [partiallyAnswers_polar_iff renovated_ne_empty renovated_ne_univ]
      exact Or.inl Set.Subset.rfl
  · refine ⟨buy, ?_, sBeautiful_supports_buy_doxB⟩
    show buy ∈ alt (Question.polar buy)
    rw [alt_polar_of_nontrivial buy_ne_empty buy_ne_univ]
    exact Set.mem_insert _ _

/-- The CI holds: clause (ii) by `sBeautiful_supports_buy_doxB`; clause
    (iii) reduces to `Supports.of_no_belief_fails` since the speaker
    (who knows the house is beautiful but not whether renovated) doesn't
    believe any answer to "has it been renovated?". -/
theorem polarQ_ciContent : polarQSentence.ciContent clauseTypeCtx := by
  refine ⟨buy, ?_, ?_, sBeautiful_supports_buy_doxB, ?_⟩
  · show buy ∈ alt (Question.polar buy)
    rw [alt_polar_of_nontrivial buy_ne_empty buy_ne_univ]
    exact Set.mem_insert _ _
  · intro p hp _
    exact absurd hp (by simp [clauseTypeCtx])
  · -- ¬ Supports doxB s'RenovatedQ buy prior — speaker doesn't believe any answer
    apply Supports.of_no_belief_fails
    intro q hq
    rw [show polarQSentence.s'Den = Question.polar renovated from rfl,
        alt_polar_of_nontrivial renovated_ne_empty renovated_ne_univ] at hq
    rcases hq with hq | hq
    · subst hq; exact doxB_not_subset_renovated
    · rw [Set.mem_singleton_iff] at hq; subst hq
      exact doxB_not_subset_renovated_compl

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

end Phenomena.Focus.Studies.IppolitoKissWilliams2025
