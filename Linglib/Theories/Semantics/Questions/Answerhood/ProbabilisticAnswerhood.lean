import Linglib.Core.FinitePMF
import Linglib.Core.Discourse.QUD
import Mathlib.Algebra.Order.Field.Basic

/-!
# Probabilistic Answerhood @cite{thomas-2026}
@cite{groenendijk-stokhof-1984}

Answerhood in terms of probability changes, following @cite{thomas-2026}
"A probabilistic, question-based approach to additivity".

## Core Definitions

**Definition 61 - Relevance**: A proposition P is relevant to question Q iff
P changes the probability of some alternative:
```
Relevant(P, Q) ≡ ∃A ∈ Q: P(A|P) ≠ P(A)
```

**Definition 62 - Probabilistic Answerhood**: P probabilistically answers Q iff
P raises the probability of some alternative:
```
ProbAnswers(P, Q) ≡ ∃A ∈ Q: P(A|P) > P(A)
```

**Definition 63 - Evidences More Strongly**: R evidences A more strongly than R':
```
EvidencesMoreStrongly(R, R', A) ≡ P(A|info(R)) > P(A|info(R'))
```

These probabilistic notions of answerhood are central to Thomas's analysis
of additive particles like "too", "also", "either".

## Connection to Mention-Some

Probabilistic answerhood generalizes the mention-some/mention-all distinction:
- Under uniform priors, probabilistic answerhood reduces to standard partial answerhood
- Non-uniform priors allow context-sensitive answerhood

-/

namespace Semantics.Questions.ProbabilisticAnswerhood

open Semantics.Questions
open Discourse

-- Conditional Probability Infrastructure

/-- A prior distribution as a normalized mass function over worlds.

Bundled with non-negativity and normalization (∑ w, mass w = 1) proofs
via `Core.FinitePMF`. Use `prior w` to access the mass at world `w`
(via `CoeFun`). -/
abbrev Prior (W : Type*) [Fintype W] := Core.FinitePMF W

/-- Compute P(φ) - probability that φ is true.

Delegates to `Core.FinitePMF.probOf`. -/
def probOfProp {W : Type*} [Fintype W]
    (prior : Prior W) (φ : W → Bool) : ℚ :=
  prior.probOf φ

/-- Compute P(A | C) - conditional probability of A given C.

Delegates to `Core.FinitePMF.condProb`. -/
def conditionalProb {W : Type*} [Fintype W]
    (prior : Prior W) (condition : W → Bool) (target : W → Bool) : ℚ :=
  prior.condProb condition target

/-- Probability of an info state being actual.

P(σ) = probability that the actual world is in σ.

This is identical to `probOfProp` — a convenience alias using info state
vocabulary rather than proposition vocabulary. -/
abbrev probOfState {W : Type*} [Fintype W]
    (prior : Prior W) (σ : InfoState W) : ℚ :=
  probOfProp prior σ

-- Definition 61: Relevance

/-- Relevance: P changes the probability of some alternative in Q.

Simplified from @cite{thomas-2026} Definition 61 for the case where R is a
declarative (single alternative P). Thomas's full definition quantifies
over alternatives of both R and S: ∃A ∈ alt(R), A' ∈ alt(S) s.t.
P_L(A'|A) ≠ P_L(A'). For declarative R with a single alternative P,
this reduces to: ∃A' ∈ alt(Q): P(A'|P) ≠ P(A'). -/
def relevant {W : Type*} [Fintype W]
    (p : W → Bool) (q : Issue W) (prior : Prior W) : Bool :=
  q.alternatives.any λ alt =>
    let condProb := conditionalProb prior p alt
    let priorProb := probOfState prior alt
    condProb != priorProb

-- Definition 62: Probabilistic Answerhood

/-- Probabilistic answerhood (simplified): P raises the probability of some alternative.

Simplified from @cite{thomas-2026} Definition 62, which additionally requires
that the witnessed resolution is raised MORE than any other (in ratio terms):
(b) for all A' ⊂ alt(Q), if ∩A' ⊉ ∩A, then P(∩A|info(R))/P(∩A) > P(∩A'|info(R))/P(∩A').

This implementation captures only condition (a): ∃A ∈ Q: P(A|P) > P(A).
The full definition is stronger — it requires the supported answer to be
*maximally* supported. For the cases we use (binary QUDs, single-alternative
declaratives), the simplified version suffices. -/
def probAnswers {W : Type*} [Fintype W]
    (p : W → Bool) (q : Issue W) (prior : Prior W) : Bool :=
  q.alternatives.any λ alt =>
    let condProb := conditionalProb prior p alt
    let priorProb := probOfState prior alt
    condProb > priorProb

/-- Intersection of a list of propositions.

Empty intersection is trivialState (all worlds), per the convention
that the empty conjunction is ⊤. -/
private def intersectAlts {W : Type*} (alts : List (W → Bool)) : W → Bool :=
  alts.foldl (fun acc alt w => acc w && alt w) trivialState

/-- Full probabilistic answerhood per @cite{thomas-2026} Definition 62.

R ANSWERS Q iff ∃ nonempty A ⊆ alt(Q) s.t.
(a) P(∩A | info(R)) > P(∩A)
(b) ∀A' ⊆ alt(Q), ∩A' ⊄ ∩A → P(∩A|info(R))/P(∩A) > P(∩A'|info(R))/P(∩A')

Condition (b) ensures that A is the *maximally* supported resolution: no
other resolution whose intersection isn't already contained in ∩A has a
higher Bayes factor. This prevents a proposition from "answering" a question
by accidentally raising two unrelated alternatives equally.

For binary QUDs (|alt(Q)| = 2), conditions (a) and (b) coincide with
`probAnswers`: raising P(H) necessarily lowers P(¬H), so the Bayes factor
condition is automatic. See `probAnswersFull_eq_simple_binary`. -/
def probAnswersFull {W : Type*} [Fintype W]
    (p : W → Bool) (q : Issue W) (prior : Prior W) : Bool :=
  let nonemptySubsets := q.alternatives.sublists.filter fun l => !l.isEmpty
  nonemptySubsets.any fun a =>
    let interA := intersectAlts a
    let pA := probOfProp prior interA
    let condA := conditionalProb prior p interA
    -- (a) P(∩A | p) > P(∩A)
    condA > pA &&
    -- (b) A's Bayes factor dominates all non-contained subsets
    pA > 0 &&
    nonemptySubsets.all fun a' =>
      let interA' := intersectAlts a'
      let pA' := probOfProp prior interA'
      -- ∩A' ⊆ ∩A → condition vacuously satisfied
      let contained := decide (∀ w : W, interA' w = true → interA w = true)
      if contained then true
      else if pA' > 0 then
        condA / pA > conditionalProb prior p interA' / pA'
      else true  -- P(∩A') = 0 → ratio undefined, vacuous

-- ============================================================================
-- Helpers for probAnswersFull_eq_simple_binary
-- ============================================================================

private lemma probOfProp_complement_add' {W : Type*} [Fintype W]
    (prior : Prior W) (f : W → Bool) :
    probOfProp prior f + probOfProp prior (fun w => !f w) = 1 :=
  prior.probOf_complement_add f

private lemma probOfProp_nonneg' {W : Type*} [Fintype W]
    (prior : Prior W) (f : W → Bool) : 0 ≤ probOfProp prior f :=
  prior.probOf_nonneg f

private lemma probOfProp_and_le' {W : Type*} [Fintype W]
    (prior : Prior W) (f g : W → Bool) :
    probOfProp prior (fun w => g w && f w) ≤ probOfProp prior f :=
  prior.probOf_and_le g f

private lemma pp_pos_of_cond_gt' {W : Type*} [Fintype W]
    (prior : Prior W) (f g : W → Bool)
    (hGt : conditionalProb prior g f > probOfProp prior f) :
    probOfProp prior g > 0 :=
  prior.probOf_pos_of_condProb_gt g f hGt

private lemma pf_pos_of_cond_gt' {W : Type*} [Fintype W]
    (prior : Prior W) (f g : W → Bool)
    (hGt : conditionalProb prior g f > probOfProp prior f) :
    probOfProp prior f > 0 :=
  prior.probOf_target_pos_of_condProb_gt g f hGt

private lemma probOfProp_and_complement_split' {W : Type*} [Fintype W]
    (prior : Prior W) (g f : W → Bool) :
    probOfProp prior (fun w => g w && f w) +
    probOfProp prior (fun w => g w && !f w) = probOfProp prior g :=
  (prior.probOf_partition g f).symm

private lemma condProb_complement_sum' {W : Type*} [Fintype W]
    (prior : Prior W) (g f : W → Bool)
    (hPg : probOfProp prior g > 0) :
    conditionalProb prior g f + conditionalProb prior g (fun w => !f w) = 1 :=
  prior.condProb_complement_sum g f hPg

private lemma cond_complement_lt' {W : Type*} [Fintype W]
    (prior : Prior W) (p f : W → Bool)
    (hGt : conditionalProb prior p f > probOfProp prior f) :
    conditionalProb prior p (fun w => !f w) < probOfProp prior (fun w => !f w) := by
  have hPp := pp_pos_of_cond_gt' prior f p hGt
  linarith [condProb_complement_sum' prior p f hPp,
            probOfProp_complement_add' prior f]

private lemma bayes_factor_dominates' {W : Type*} [Fintype W]
    (prior : Prior W) (p f : W → Bool)
    (hGt : conditionalProb prior p f > probOfProp prior f)
    (hNfPos : probOfProp prior (fun w => !f w) > 0) :
    conditionalProb prior p f / probOfProp prior f >
    conditionalProb prior p (fun w => !f w) / probOfProp prior (fun w => !f w) := by
  have hfPos := pf_pos_of_cond_gt' prior f p hGt
  have hCondLt := cond_complement_lt' prior p f hGt
  linarith [(one_lt_div hfPos).mpr hGt, (div_lt_one hNfPos).mpr hCondLt]

private lemma and_and_iff_or {a b x c d y : Bool}
    (hab : a = true → b = true) (hax : a = true → x = true)
    (hcd : c = true → d = true) (hcy : c = true → y = true) :
    ((a && b) && x || (c && d) && y) = (a || c) := by
  cases a <;> cases c <;> simp_all

/-- The simplified `probAnswers` (condition (a) only) is equivalent to the
full Thomas (62) `probAnswersFull` for binary QUDs, **under a normalized
probability distribution**.

For binary {H, ¬H}, raising P(H) necessarily lowers P(¬H) (since
P(H|p) + P(¬H|p) = 1 = P(H) + P(¬H)), so the Bayes factor for H
automatically exceeds the Bayes factor for ¬H. The only nonempty subsets
with non-trivial intersections are {H} and {¬H} (since
∩{H,¬H} = H ∩ ¬H = ∅ has P(∅) = 0).

Without normalization, the theorem is false: if ∑ prior < 1, both
alternatives can have their probability raised simultaneously with equal
Bayes factors, making `probAnswersFull` false while `probAnswers` is true. -/
theorem probAnswersFull_eq_simple_binary {W : Type*} [Fintype W]
    (p : W → Bool) (h : W → Bool) (prior : Prior W) :
    probAnswersFull p (Issue.polar h) prior =
    probAnswers p (Issue.polar h) prior := by
  -- Both are Bool; prove they agree by showing true ↔ true
  -- Step 1: Establish what probAnswers checks
  -- probAnswers checks: ∃ alt ∈ [h, ¬h], P(alt|p) > P(alt)
  -- Step 2: Establish what probAnswersFull checks
  -- sublists [h, ¬h] = [[], [h], [¬h], [h, ¬h]]
  -- nonempty subsets = [[h], [¬h], [h, ¬h]]
  -- For each A: intersectAlts A, then check (a)(b)(c)
  -- [h,¬h] always fails (P(⊥) = 0)
  -- So: probAnswersFull = check([h]) || check([¬h])
  -- Under normalization, check([h]) ↔ P(h|p) > P(h)
  -- Step 3: show equivalence

  -- Convert to ↔ at the Prop level
  -- Establish the concrete sublists for polar {h, ¬h}
  -- sublists [h, ¬h] filtered nonempty = [[h], [¬h], [h, ¬h]]
  have h_subs : ([h, fun w => !h w] : List (W → Bool)).sublists.filter
      (fun l => !l.isEmpty) = [[h], [fun w => !h w], [h, fun w => !h w]] := rfl
  unfold probAnswersFull probAnswers
  dsimp only [Issue.polar]
  simp only [h_subs, List.any_cons, List.any_nil, Bool.or_false, probOfState]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  simp only [intersectAlts, List.foldl, trivialState, Bool.true_and]
  -- Key facts about ⊥ = h ∧ ¬h
  have h_bot : ∀ w : W, (h w && !h w) = false := fun w => by cases h w <;> rfl
  have pP_bot : probOfProp prior (fun w => h w && !h w) = 0 := by
    unfold probOfProp; apply Finset.sum_eq_zero; intro w _
    simp [h_bot]
  -- Simplify decidable containment checks (self-implications and vacuous implications)
  have dec_hh : decide (∀ w : W, h w = true → h w = true) = true :=
    decide_eq_true_eq.mpr fun _ a => a
  have dec_nhnh : decide (∀ w : W, (!h w) = true → (!h w) = true) = true :=
    decide_eq_true_eq.mpr fun _ a => a
  have dec_both : decide (∀ w : W, (h w && !h w) = true → (h w && !h w) = true) = true :=
    decide_eq_true_eq.mpr fun _ a => a
  have dec_bot_h : decide (∀ w : W, (h w && !h w) = true → h w = true) = true :=
    decide_eq_true_eq.mpr fun w hw => absurd (by rw [h_bot] at hw; exact hw) Bool.false_ne_true
  have dec_bot_nh : decide (∀ w : W, (h w && !h w) = true → (!h w) = true) = true :=
    decide_eq_true_eq.mpr fun w hw => absurd (by rw [h_bot] at hw; exact hw) Bool.false_ne_true
  simp only [dec_hh, dec_nhnh, dec_both, dec_bot_h, dec_bot_nh,
             pP_bot, gt_iff_lt, lt_irrefl, decide_false,
             Bool.true_and, Bool.and_true, Bool.false_and, Bool.and_false,
             Bool.or_false, ite_true]
  -- Eta-normalize: fun w => h w → h (definitionally equal)
  conv_lhs => simp only [show (fun w : W => h w) = h from rfl]
  -- Goal: ((dH && dB) && bayesH || (dNH && dD) && bayesNH) = (dH || dNH)
  -- Apply Bool helper: suffices to show dH → dB ∧ bayesH and dNH → dD ∧ bayesNH
  apply and_and_iff_or
  · -- dH = true → dB (prior positivity) = true
    intro hA; rw [decide_eq_true_eq] at hA ⊢
    exact pf_pos_of_cond_gt' prior h p hA
  · -- dH = true → bayesCheck_h = true
    intro hA; rw [decide_eq_true_eq] at hA
    split
    · rfl  -- containment check ¬h ⊆ h passed (vacuous)
    · split
      · -- P(¬h) > 0: Bayes factor dominates under normalization
        rename_i _ hNhPos; rw [decide_eq_true_eq]
        exact bayes_factor_dominates' prior p h hA hNhPos
      · rfl  -- P(¬h) = 0: vacuous
  · -- dNH = true → dD (prior positivity) = true
    intro hC; rw [decide_eq_true_eq] at hC ⊢
    exact pf_pos_of_cond_gt' prior (fun w => !h w) p hC
  · -- dNH = true → bayesCheck_nh = true
    intro hC; rw [decide_eq_true_eq] at hC
    split
    · rfl  -- containment check h ⊆ ¬h passed (vacuous)
    · split
      · -- P(h) > 0: Bayes factor via complement argument
        rename_i _ hHPos; rw [decide_eq_true_eq]
        have hPp := pp_pos_of_cond_gt' prior (fun w => !h w) p hC
        have hComp := condProb_complement_sum' prior p h hPp
        have hAdd := probOfProp_complement_add' prior h
        have pos_nh := pf_pos_of_cond_gt' prior (fun w => !h w) p hC
        have cp_h_lt : conditionalProb prior p h < probOfProp prior h := by
          linarith [hComp, hAdd]
        linarith [(div_lt_one hHPos).mpr cp_h_lt, (one_lt_div pos_nh).mpr hC]
      · rfl  -- P(h) = 0: vacuous

/-- Which alternative(s) are supported by P.

Returns the alternatives whose probability is raised by learning P. -/
def supportedAlternatives {W : Type*} [Fintype W]
    (p : W → Bool) (q : Issue W) (prior : Prior W) : List (InfoState W) :=
  q.alternatives.filter λ alt =>
    let condProb := conditionalProb prior p alt
    let priorProb := probOfState prior alt
    condProb > priorProb

-- Definition 63: Evidences More Strongly

/-- Informational content of a resolving state.

For a single info state σ (representing a potential resolution),
info(σ) is just σ itself - the proposition that the actual world is in σ.

For multiple resolving states, info({σ₁,..., σₙ}) is their union. -/
def infoContent {W : Type*} (states : List (InfoState W)) : W → Bool :=
  λ w => states.any λ σ => σ w

/-- Evidences more strongly: R evidences A more strongly than R' does.

Definition 63 from @cite{thomas-2026}:
```
EvidencesMoreStrongly(R, R', A) ≡ P(A|info(R)) > P(A|info(R'))
```

Used in the felicity conditions for additive particles: the prejacent
combined with the antecedent must evidence some resolution more strongly
than the antecedent alone. -/
def evidencesMoreStrongly {W : Type*} [Fintype W]
    (r r' : List (InfoState W)) (a : InfoState W)
    (prior : Prior W) : Bool :=
  let infoR := infoContent r
  let infoR' := infoContent r'
  let probGivenR := conditionalProb prior infoR a
  let probGivenR' := conditionalProb prior infoR' a
  probGivenR > probGivenR'

/-- Simpler version: single propositions instead of state lists.

Compares conditional probabilities P(A|R) > P(A|R'). This is equivalent
to comparing Bayes factors P(A|R)/P(A) > P(A|R')/P(A), since the
denominator P(A) is the same on both sides and cancels. -/
def evidencesMoreStronglyProp {W : Type*} [Fintype W]
    (evidence evidence' : W → Bool) (conclusion : W → Bool)
    (prior : Prior W) : Bool :=
  let probGivenEvidence := conditionalProb prior evidence conclusion
  let probGivenEvidence' := conditionalProb prior evidence' conclusion
  probGivenEvidence > probGivenEvidence'

-- Strength of Evidence

/-- Compute how much evidence raises the probability of a conclusion.

This is P(A|E) - P(A), measuring the "boost" from learning E. -/
def evidentialBoost {W : Type*} [Fintype W]
    (evidence : W → Bool) (conclusion : W → Bool)
    (prior : Prior W) : ℚ :=
  let condProb := conditionalProb prior evidence conclusion
  let priorProb := probOfProp prior conclusion
  condProb - priorProb

/-- Evidence is positive if it raises the probability of the conclusion. -/
def isPositiveEvidence {W : Type*} [Fintype W]
    (evidence : W → Bool) (conclusion : W → Bool)
    (prior : Prior W) : Bool :=
  evidentialBoost evidence conclusion prior > 0

/-- Evidence is negative if it lowers the probability of the conclusion. -/
def isNegativeEvidence {W : Type*} [Fintype W]
    (evidence : W → Bool) (conclusion : W → Bool)
    (prior : Prior W) : Bool :=
  evidentialBoost evidence conclusion prior < 0

-- Connection to Standard Answerhood

/-- Entailing an alternative guarantees probabilistic answerhood.

If P entails some alternative A (every P-world is an A-world) and A is not
already certain, then learning P raises A's probability to 1, which exceeds
the prior P(A) < 1. This gives probAnswers (not just relevance).

Note: the weaker condition of mere consistency (P ∩ A ≠ ∅) does NOT suffice —
a proposition balanced across alternatives (e.g., W={0,1,2,3}, Q={{0,1},{2,3}},
P={0,2}) can be consistent with every alternative without changing any
conditional probability. -/
theorem probAnswers_when_entailing {W : Type*} [Fintype W] [DecidableEq W]
    (p : W → Bool) (q : Issue W) (prior : Prior W)
    (alt : W → Bool)
    (hAltMem : alt ∈ q.alternatives)
    (hEntails : ∀ w, p w = true → alt w = true)
    (hPosP : probOfProp prior p > 0)
    (hNotCertain : probOfState prior alt < 1) :
    probAnswers p q prior = true := by
  simp only [probAnswers, List.any_eq_true, decide_eq_true_eq]
  refine ⟨alt, hAltMem, ?_⟩
  -- Show conditionalProb prior p alt = 1
  have hConj : probOfProp prior (λ w => p w && alt w) = probOfProp prior p := by
    unfold probOfProp
    congr 1; funext w
    cases hp : p w with
    | false => simp
    | true => simp [hEntails w hp]
  have hCond : conditionalProb prior p alt = 1 := by
    rw [show conditionalProb prior p alt =
          probOfProp prior (fun w => p w && alt w) / probOfProp prior p from
      Core.FinitePMF.condProb_of_pos prior p alt hPosP, hConj]
    exact div_self (ne_of_gt hPosP)
  -- conditionalProb = 1 > probOfState prior alt
  rw [hCond]
  exact hNotCertain

-- Combined Evidence (for Additive Particles)

/-- Check if conjunction of two propositions provides stronger evidence
than the first proposition alone.

This is the core of Thomas's analysis of additive particles:
TOO(π) requires that ANT ∧ π evidences some resolution more strongly
than ANT alone. -/
def conjunctionStrengthens {W : Type*} [Fintype W]
    (p1 p2 : W → Bool) (conclusion : W → Bool)
    (prior : Prior W) : Bool :=
  evidencesMoreStronglyProp (λ w => p1 w && p2 w) p1 conclusion prior

/-- Find resolutions that the conjunction evidences more strongly. -/
def strengthenedResolutions {W : Type*} [Fintype W]
    (p1 p2 : W → Bool) (q : Issue W)
    (prior : Prior W) : List (InfoState W) :=
  q.alternatives.filter λ alt =>
    conjunctionStrengthens p1 p2 alt prior

/-- Check if there exists some resolution that is strengthened. -/
def someResolutionStrengthened {W : Type*} [Fintype W]
    (p1 p2 : W → Bool) (q : Issue W)
    (prior : Prior W) : Bool :=
  (strengthenedResolutions p1 p2 q prior).length > 0

-- Theorems

/-- Probabilistic answerhood implies relevance.

If P raises the probability of some alternative, then P changes
the probability of that alternative. -/
theorem probAnswers_implies_relevant {W : Type*} [Fintype W]
    (p : W → Bool) (q : Issue W) (prior : Prior W) :
    probAnswers p q prior = true → relevant p q prior = true := by
  intro h
  simp only [probAnswers, relevant] at *
  simp only [List.any_eq_true, decide_eq_true_eq] at *
  obtain ⟨alt, hmem, hgt⟩ := h
  refine ⟨alt, hmem, ?_⟩
  simp only [bne_iff_ne, ne_eq]
  exact ne_of_gt hgt

/-- Stronger evidence is positive evidence.

If R evidences A more strongly than R', then R is positive evidence for A
relative to R'. -/
theorem strongerEvidence_is_positive {W : Type*} [Fintype W]
    (r r' : List (InfoState W)) (a : InfoState W)
    (prior : Prior W) :
    evidencesMoreStrongly r r' a prior = true →
    conditionalProb prior (infoContent r) a >
    conditionalProb prior (infoContent r') a := by
  intro h
  simp only [evidencesMoreStrongly, decide_eq_true_eq] at h
  exact h

-- Resolution Evidenced by R (Q|_R)

/-- The resolution of Q evidenced by R — Q|_R from @cite{thomas-2026} Def. 62.

Returns the alternative A ∈ alt(Q) that maximizes the Bayes factor
P(A|info(R)) / P(A). This is the ∩A from Definition 62 such that
A's Bayes factor strictly dominates all non-contained alternatives.

For single-alternative resolutions (the common case), this reduces
to the alternative with the highest conditional probability increase. -/
def evidencedResolution {W : Type*} [Fintype W]
    (p : W → Bool) (q : Issue W) (prior : Prior W) : Option (InfoState W) :=
  let candidates := q.alternatives.filterMap fun alt =>
    let pAlt := probOfProp prior alt
    if pAlt > 0 then
      let bayesFactor := conditionalProb prior p alt / pAlt
      if bayesFactor > 1 then some (alt, bayesFactor) else none
    else none
  match candidates with
  | [] => none
  | (best, _) :: _ =>
    -- Find the candidate with the highest Bayes factor
    let winner := candidates.foldl (fun (acc : InfoState W × ℚ) (cur : InfoState W × ℚ) =>
      if cur.2 > acc.2 then cur else acc) (best, 0)
    some winner.1

/-!
## ℚ↔ℝ Probability Bridge

ProbabilisticAnswerhood uses `Prior W := W → ℚ` (exact rational arithmetic),
while EntropyNPIs uses `W → ℝ` (for Mathlib's `negMulLog`/`Real.log`). To
connect the two, cast via `fun w => (prior w : ℝ)`. The identity
`probOfProp prior φ` cast to `ℝ` equals `∑ w, if φ w then (prior w : ℝ) else 0`
follows from `Rat.cast_sum`.

A formal bridge theorem (`probOfProp_cast_eq_cellProb`) is deferred until
both modules share an import of `Mathlib.Data.Real.Basic`.
-/

end Semantics.Questions.ProbabilisticAnswerhood
