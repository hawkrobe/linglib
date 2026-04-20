import Linglib.Core.Constraint.MaxEnt
import Linglib.Core.Constraint.Variation
import Linglib.Core.InformationStructure
import Linglib.Theories.Syntax.DependencyGrammar.Formal.DependencyLength

/-!
# Heaviness vs. Newness in Constituent Ordering @cite{arnold-wasow-losongco-ginstrom-2000}

@cite{arnold-wasow-losongco-ginstrom-2000} use a corpus analysis (the
Aligned-Hansard corpus, with verbs *give*, *bring...to*, *take...into
account*) and an elicitation experiment (with *give*) to disentangle
two confounded predictors of English postverbal constituent ordering:

1. **Heaviness** — relative word count: heavier constituents come later
   (Behaghel's *Gesetz der wachsenden Glieder* @cite{behaghel-1909};
   "end-weight" in @cite{quirk-greenbaum-leech-svartvik-1972}).
2. **Newness** — discourse status: given material precedes new
   information. The principle predates @cite{prince-1981}'s
   given/inferable/new taxonomy that the paper *codes* with;
   @cite{gundel-hedberg-zacharski-1993} place it in the broader
   accessibility-hierarchy literature.

The paper's central empirical claim is that **both** factors
independently predict ordering in dative alternation and heavy NP shift;
neither reduces to the other (§2-3). The deeper theoretical point of
§5 is that the two factors *interact*: heaviness exerts more influence
when newness is non-discriminating, and vice versa, consistent with a
constraint-based architecture in which "the strength of a constraint is
greater when competing constraints are weak".

## Formalization strategy

Following @cite{coetzee-pater-2011}, we model the system as a MaxEnt
grammar (@cite{goldwater-johnson-2003}) over the binary ordering
candidates `{themeLast, goalLast}` with two markedness constraints:

- `*HEAVY-FIRST` — penalize the order whose first constituent is
                   strictly heavier than the second
- `*NEW-FIRST`   — penalize the order whose first constituent is
                   discourse-new while the second is discourse-given

The harmony-score difference between the two orderings decomposes
additively (`score_diff_eq_components`) into a heaviness term
`wH * heavyDiff p` and a newness term `wN * newDiff p`, where
`heavyDiff p, newDiff p ∈ {-1, 0, +1}` record the per-constraint signed
preference for `themeLast` over `goalLast`. Every prediction theorem
below is a one-line consequence of this decomposition.

The §5 interaction story falls out as
`heaviness_dominates_when_newness_neutral`: when the newness constraint
is silent on a pair, the harmony difference is *exactly* `wH * heavyDiff`
— so any change in heaviness is undiluted by competing pressure. The
sigmoid shape of MaxEnt softmax then turns this into the empirical
"newness has more effect when heaviness is balanced" pattern.

## Non-reducibility of the two factors

`heaviness_and_newness_genuinely_independent` exhibits two pairs that
witness the §2-3 claim that neither factor reduces to the other:
- `heavyGoalContrast` has `newDiff = 0` but `heavyDiff ≠ 0` — only
  heaviness fires
- `newThemeContrast` has `heavyDiff = 0` but `newDiff ≠ 0` — only
  newness fires

A theory operationalizing only one of the two factors must give the
same prediction at one of these contrasts as at the trivial baseline,
contradicting the paper's findings.

## Bridges

- `Core.Constraint.MaxEntGrammar` — the grammar packages as a generic
  MaxEnt grammar (`maxEntGrammar`), making the softmax probability
  machinery available without redefinition.
- `Core.InformationStructure.DiscourseStatus` — discourse-status
  partition. The paper collapses @cite{prince-1981}'s three-way
  given/inferable/new into two categories (inferable → given);
  `DiscourseStatus.focused` is irrelevant for this construction (it
  satisfies neither side of `newFirst`'s pattern, evaluating to 0).
- `Theories.Syntax.DependencyGrammar.Formal.DependencyLength` —
  Dependency Locality (@cite{futrell-gibson-2020}) provides the
  *positive* derivation of the heaviness signal: §9 below shows
  `heavyDiff` is exactly the sign of the DLM cost difference between
  the two orderings, so `*HEAVY-FIRST` is not a stipulation but a
  theorem about which order minimizes total dependency length on a
  binary postverbal pair. The same module's word-invariance
  (`dlm_word_invariant`) shows DLM cannot, on its own, also derive
  the newness effect — motivating §10's UID derivation.
- `Theories.Processing.MemorySurprisal` — under @cite{futrell-2019}'s
  information-locality framework, DLM and UID are reductions of a
  single mutual-information-weighted cost (§11), so the two
  independent constraints `*HEAVY-FIRST` and `*NEW-FIRST` reflect
  variation along orthogonal axes of one underlying processing theory.
- `Theories.Processing.Memory` — `MemorySurprisal`'s information
  locality is itself the *behavioural profile* of a finite-capacity
  `MemoryProcess` (@cite{futrell-gibson-levy-2020}'s lossy-context
  surprisal). §11 below traces the full grounding chain
  `MemoryProcess → MemorySurprisal → {DLM, UID} → {*HEAVY-FIRST, *NEW-FIRST}`,
  so Arnold's two constraints are not just co-justified at the
  cost-function level but anchored in a single architectural
  primitive: a predictor reading from a lossily-encoded memory.
-/

namespace ArnoldEtAl2000

open Core.Constraint.OT Core.Constraint Core.InformationStructure
open DepGrammar DepGrammar.DependencyLength

-- ============================================================================
-- § 1: Phrases, Orderings, and Candidates
-- ============================================================================

/-- A constituent characterized by the two dimensions
    @cite{arnold-wasow-losongco-ginstrom-2000} measure: word count
    (heaviness) and discourse status (newness). Concrete syntactic
    structure is abstracted away — these two scalars exhaust what the
    paper's regressions condition on. -/
structure Phrase where
  wordCount : Nat
  discourse : DiscourseStatus
  deriving DecidableEq, Repr

/-- The two constituents of a binary postverbal alternation. For the
    dative alternation, `(theme, goal)`; for heavy NP shift, `(direct
    object, prepositional phrase)`. The constraints below are
    construction-neutral. -/
abbrev Pair := Phrase × Phrase

/-- Which of the two constituents occupies the second (sentence-final)
    slot. `themeLast` is the prepositional dative for DA and the
    *shifted* `V PP DO` for HNPS; `goalLast` is the double object for
    DA and the canonical `V DO PP` for HNPS. -/
inductive Order where
  | themeLast
  | goalLast
  deriving DecidableEq, Repr

instance : Fintype Order :=
  ⟨{.themeLast, .goalLast}, fun o => by cases o <;> decide⟩

abbrev Candidate := Pair × Order

-- ============================================================================
-- § 2: The Two Constraints
-- ============================================================================

/-- `*HEAVY-FIRST`: violated when the first (verb-adjacent) constituent
    is strictly heavier than the second. The OT-style markedness
    encoding of @cite{behaghel-1909}'s law of growing constituents:
    avoid placing the longer constituent first. -/
def heavyFirst : NamedConstraint Candidate where
  name := "*HEAVY-FIRST"
  family := .markedness
  eval := fun ((th, gl), o) =>
    match o with
    | .themeLast => if gl.wordCount > th.wordCount then 1 else 0
    | .goalLast  => if th.wordCount > gl.wordCount then 1 else 0

/-- `*NEW-FIRST`: violated when the first constituent is discourse-new
    while the second is discourse-given. A markedness encoding of the
    given-before-new principle the paper draws from
    @cite{prince-1981}/@cite{gundel-hedberg-zacharski-1993}.
    `DiscourseStatus.focused` doesn't satisfy either side of the
    pattern, so focused constituents contribute zero violations. -/
def newFirst : NamedConstraint Candidate where
  name := "*NEW-FIRST"
  family := .markedness
  eval := fun ((th, gl), o) =>
    match o with
    | .themeLast =>
      if gl.discourse = .new ∧ th.discourse = .given then 1 else 0
    | .goalLast  =>
      if th.discourse = .new ∧ gl.discourse = .given then 1 else 0

/-- The two-constraint MaxEnt grammar parameterized by weights.
    `wH` weights `*HEAVY-FIRST`; `wN` weights `*NEW-FIRST`. -/
def grammar (wH wN : ℚ) : List (WeightedConstraint Candidate) :=
  [ { toNamedConstraint := heavyFirst, weight := wH }
  , { toNamedConstraint := newFirst,   weight := wN } ]

-- ============================================================================
-- § 3: Per-Constraint Signed Preferences
-- ============================================================================

/-- The heaviness constraint's signed preference for `themeLast` over
    `goalLast` on a pair: `+1` when the theme (`p.1`) is heavier (so
    placing it last avoids violation), `-1` when the goal (`p.2`) is
    heavier, `0` when they are equal. -/
def heavyDiff (p : Pair) : ℚ :=
  (if p.1.wordCount > p.2.wordCount then (1:ℚ) else 0) -
  (if p.2.wordCount > p.1.wordCount then (1:ℚ) else 0)

/-- The newness constraint's signed preference for `themeLast` over
    `goalLast` on a pair: `+1` when the theme is new and the goal given
    (so placing the theme last respects given-before-new), `-1` when
    the goal is new and the theme given, `0` otherwise. -/
def newDiff (p : Pair) : ℚ :=
  (if p.1.discourse = .new ∧ p.2.discourse = .given then (1:ℚ) else 0) -
  (if p.2.discourse = .new ∧ p.1.discourse = .given then (1:ℚ) else 0)

/-- The harmony-score difference decomposes additively into per-constraint
    signed preferences scaled by their weights. This is the foundational
    identity of the formalization — every prediction theorem below is a
    one-step consequence. -/
lemma score_diff_eq_components (wH wN : ℚ) (p : Pair) :
    harmonyScore (grammar wH wN) (p, .themeLast) -
    harmonyScore (grammar wH wN) (p, .goalLast) =
      wH * heavyDiff p + wN * newDiff p := by
  obtain ⟨th, gl⟩ := p
  simp only [grammar, harmonyScore, List.foldl, heavyFirst, newFirst,
    heavyDiff, newDiff]
  push_cast
  ring

/-- `heavyDiff` is positive iff the theme (`p.1`) is strictly heavier
    than the goal — i.e., `*HEAVY-FIRST` prefers `themeLast`. -/
lemma heavyDiff_pos_iff {p : Pair} :
    0 < heavyDiff p ↔ p.1.wordCount > p.2.wordCount := by
  unfold heavyDiff
  by_cases h12 : p.1.wordCount > p.2.wordCount
  · have h21 : ¬ p.2.wordCount > p.1.wordCount := Nat.not_lt.mpr h12.le
    simp [h12, h21]
  · by_cases h21 : p.2.wordCount > p.1.wordCount <;> simp [h12, h21]

/-- `newDiff` is positive iff the theme is new while the goal is
    given — i.e., `*NEW-FIRST` prefers `themeLast`. -/
lemma newDiff_pos_iff {p : Pair} :
    0 < newDiff p ↔ p.1.discourse = .new ∧ p.2.discourse = .given := by
  unfold newDiff
  constructor
  · intro h
    by_contra hcon
    simp [hcon] at h
    split_ifs at h <;> linarith
  · intro ⟨h1, h2⟩
    have hn : ¬ (p.2.discourse = .new ∧ p.1.discourse = .given) := by
      rintro ⟨_, hr⟩
      rw [h1] at hr
      exact DiscourseStatus.noConfusion hr
    simp [h1, h2]

-- ============================================================================
-- § 4: Independence Theorems — the Central Paper Claim, Derived
-- ============================================================================

/-- **Heaviness independently predicts ordering.** With the newness
    weight zeroed out, a positive heaviness weight is enough to make
    the order placing the heavier constituent last strictly more
    probable. Symmetric in the heavier-side direction: when `heavyDiff p`
    is non-zero, its sign determines which order wins. -/
theorem heaviness_independently_predicts {p : Pair} {wH : ℚ}
    (hH : 0 < wH) (h : 0 < heavyDiff p) :
    moreProbable (grammar wH 0) (p, .themeLast) (p, .goalLast) := by
  have hdiff := score_diff_eq_components wH 0 p
  show harmonyScore _ _ > harmonyScore _ _
  have : 0 < wH * heavyDiff p := mul_pos hH h
  linarith

/-- **Newness independently predicts ordering.** With the heaviness
    weight zeroed out, a positive newness weight is enough to make
    the order placing the new constituent last strictly more probable. -/
theorem newness_independently_predicts {p : Pair} {wN : ℚ}
    (hN : 0 < wN) (h : 0 < newDiff p) :
    moreProbable (grammar 0 wN) (p, .themeLast) (p, .goalLast) := by
  have hdiff := score_diff_eq_components 0 wN p
  show harmonyScore _ _ > harmonyScore _ _
  have : 0 < wN * newDiff p := mul_pos hN h
  linarith

/-- **Both factors compose additively.** When neither factor opposes
    `themeLast` (both per-constraint contributions are non-negative)
    and at least one strictly favors it, `themeLast` wins — without
    requiring the caller to compute the combined sum. No separate
    interaction term is needed to reproduce the experiment's significant
    `heaviness × newness` term in logistic regression: it falls out of
    additive harmony plus the sigmoid shape of MaxEnt probability. -/
theorem both_factors_compose {p : Pair} {wH wN : ℚ}
    (hH : 0 ≤ wH) (hN : 0 ≤ wN)
    (hHeavy : 0 ≤ heavyDiff p) (hNew : 0 ≤ newDiff p)
    (hStrict : 0 < wH * heavyDiff p ∨ 0 < wN * newDiff p) :
    moreProbable (grammar wH wN) (p, .themeLast) (p, .goalLast) := by
  have hdiff := score_diff_eq_components wH wN p
  show harmonyScore _ _ > harmonyScore _ _
  have h1 : 0 ≤ wH * heavyDiff p := mul_nonneg hH hHeavy
  have h2 : 0 ≤ wN * newDiff p := mul_nonneg hN hNew
  rcases hStrict with hs | hs <;> linarith

/-- **Tradeoff theorem.** When heaviness and newness conflict — one
    favors `themeLast`, the other `goalLast` — the prediction depends
    on which side has the larger weighted contribution. This is the
    constraint-based architecture @cite{arnold-wasow-losongco-ginstrom-2000}
    argue for in §5. -/
theorem tradeoff_resolved_by_weights {p : Pair} {wH wN : ℚ}
    (h : 0 < wH * heavyDiff p + wN * newDiff p) :
    moreProbable (grammar wH wN) (p, .themeLast) (p, .goalLast) := by
  have hdiff := score_diff_eq_components wH wN p
  show harmonyScore _ _ > harmonyScore _ _
  linarith

-- ============================================================================
-- § 5: Constraint-Strength Interaction (the Paper's §5 Theoretical Claim)
-- ============================================================================

/-! @cite{arnold-wasow-losongco-ginstrom-2000} §5 observe that "heaviness
had the largest effect on utterances where both constituents were given"
— and in general, "the strength of a constraint is greater when competing
constraints are weak". The next two theorems derive this directly from
MaxEnt's additive harmony: when one constraint contributes 0 to the
harmony difference (its `eval` is identical on both candidates), the
*entire* difference is borne by the other constraint, undiluted. The
sigmoid then translates a larger harmony differential into a larger
probability shift. -/

/-- **Constraint-interaction theorem (heaviness side).** When the
    newness constraint is neutral on a pair (`newDiff p = 0`, i.e., the
    two constituents share the same discourse status, or one is
    `.focused`), the harmony difference between orderings is determined
    entirely by the weighted heaviness term. -/
theorem heaviness_dominates_when_newness_neutral
    (wH wN : ℚ) {p : Pair} (hN : newDiff p = 0) :
    harmonyScore (grammar wH wN) (p, .themeLast) -
    harmonyScore (grammar wH wN) (p, .goalLast) = wH * heavyDiff p := by
  rw [score_diff_eq_components, hN, mul_zero, add_zero]

/-- **Constraint-interaction theorem (newness side).** When the
    heaviness constraint is neutral on a pair (`heavyDiff p = 0`, i.e.,
    the two constituents are equally long), the harmony difference is
    determined entirely by the weighted newness term. The paper's
    elicitation experiment (where `give` stimuli held NP length roughly
    constant) is exactly this regime — and unsurprisingly newness
    showed a larger effect there than in the corpus study. -/
theorem newness_dominates_when_heaviness_neutral
    (wH wN : ℚ) {p : Pair} (hH : heavyDiff p = 0) :
    harmonyScore (grammar wH wN) (p, .themeLast) -
    harmonyScore (grammar wH wN) (p, .goalLast) = wN * newDiff p := by
  rw [score_diff_eq_components, hH, mul_zero, zero_add]

-- ============================================================================
-- § 6: Stimulus Contrasts and Non-Reducibility Witness
-- ============================================================================

/-- *Give the carrot to the white rabbit who lived in the briar patch.*
    Heavy goal (8 words), light theme (1 word), both new — the
    heaviness contrast (newness is silent here). -/
def heavyGoalContrast : Pair :=
  ({ wordCount := 1, discourse := .new },
   { wordCount := 8, discourse := .new })

/-- *Give Alice the carrot.* (Theme new, goal given.) Equal length,
    pure newness contrast (heaviness is silent here). -/
def newThemeContrast : Pair :=
  ({ wordCount := 1, discourse := .new  },
   { wordCount := 1, discourse := .given })

@[simp] lemma heavyDiff_heavyGoalContrast : heavyDiff heavyGoalContrast = -1 := by
  show (if (1:Nat) > 8 then (1:ℚ) else 0) -
       (if (8:Nat) > 1 then (1:ℚ) else 0) = -1
  rw [if_neg (by decide), if_pos (by decide)]; norm_num

@[simp] lemma newDiff_heavyGoalContrast : newDiff heavyGoalContrast = 0 := by
  show (if (DiscourseStatus.new = .new ∧ DiscourseStatus.new = .given)
          then (1:ℚ) else 0) -
       (if (DiscourseStatus.new = .new ∧ DiscourseStatus.new = .given)
          then (1:ℚ) else 0) = 0
  simp

@[simp] lemma heavyDiff_newThemeContrast : heavyDiff newThemeContrast = 0 := by
  show (if (1:Nat) > 1 then (1:ℚ) else 0) -
       (if (1:Nat) > 1 then (1:ℚ) else 0) = 0
  simp

@[simp] lemma newDiff_newThemeContrast : newDiff newThemeContrast = 1 := by
  show (if (DiscourseStatus.new = .new ∧ DiscourseStatus.given = .given)
          then (1:ℚ) else 0) -
       (if (DiscourseStatus.given = .new ∧ DiscourseStatus.new = .given)
          then (1:ℚ) else 0) = 1
  rw [if_pos ⟨rfl, rfl⟩, if_neg (by rintro ⟨h, _⟩; cases h)]; norm_num

/-- **Non-reducibility witness.** The two contrast pairs jointly
    establish the paper's central claim that neither factor reduces to
    the other: `heavyGoalContrast` activates *only* heaviness (newness
    differential is zero), `newThemeContrast` activates *only* newness
    (heaviness differential is zero). Any theory that operationalizes
    only one of the two dimensions must collapse the prediction at one
    contrast to the trivial baseline, contradicting
    @cite{arnold-wasow-losongco-ginstrom-2000}. -/
theorem heaviness_and_newness_genuinely_independent :
    newDiff heavyGoalContrast = 0 ∧ heavyDiff heavyGoalContrast ≠ 0 ∧
    heavyDiff newThemeContrast = 0 ∧ newDiff newThemeContrast ≠ 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp

/-- Pure-heaviness MaxEnt grammar predicts goal-last (heavier-last) when
    the goal is heavier than the theme. Direct application of the
    `heavyDiff`-symmetric independence theorem on the swapped pair. -/
theorem heavy_goal_predicts_goalLast :
    moreProbable (grammar 1 0)
      (heavyGoalContrast, .goalLast) (heavyGoalContrast, .themeLast) := by
  have hdiff := score_diff_eq_components 1 0 heavyGoalContrast
  show harmonyScore _ _ > harmonyScore _ _
  rw [heavyDiff_heavyGoalContrast] at hdiff
  linarith

/-- Pure-newness MaxEnt grammar predicts theme-last (given-first) when
    the theme is new and the goal is given. -/
theorem new_theme_predicts_themeLast :
    moreProbable (grammar 0 1)
      (newThemeContrast, .themeLast) (newThemeContrast, .goalLast) :=
  newness_independently_predicts (by norm_num) (by rw [newDiff_newThemeContrast]; norm_num)

-- ============================================================================
-- § 7: Bridge to the Generic MaxEntGrammar Machinery
-- ============================================================================

/-- The two-constraint grammar packaged as a generic `MaxEntGrammar`
    over pairs (input) and orderings (output). This makes the library's
    softmax probability infrastructure (`MaxEntGrammar.prob`, the
    `ConstraintSystem` bridge, `softmax_argmax_limit` for the OT limit,
    etc.) available without redefinition. -/
def maxEntGrammar (wH wN : ℚ) (inputs : List Pair) :
    MaxEntGrammar Pair Order where
  inputs := inputs
  gen := fun _ => [.themeLast, .goalLast]
  constraints := grammar wH wN

-- ============================================================================
-- § 8: Dependency Locality Bridge — Why DLM Alone Is Insufficient
-- ============================================================================

/-! `totalDepLength` (from `DependencyLength.lean`) is a candidate
formalization of @cite{behaghel-1909}'s end-weight effect — and
@cite{arnold-wasow-losongco-ginstrom-2000} discuss
@cite{hawkins-1990}'s parsing-theoretic version (Early Immediate
Constituents) as an instance. The next three lemmas show that any such
purely structural account cannot, on its own, reproduce the newness
effect: dependency length is a function of the dependency structure
alone — it never reads the words. So no DLM-derived predictor
distinguishes a sentence with discourse-given NPs from a sentence with
discourse-new NPs sharing the same dependency tree.

Combined with `newness_independently_predicts`, this implies any
adequate theory of postverbal ordering must combine a weight constraint
with at least one further dimension — here, discourse status. -/

/-- `totalDepLength` ignores word identity: it depends only on the
    dependency structure (head index × dep index × relation). -/
theorem dlm_word_invariant
    (deps : List Dependency) (rootIdx : Nat) (words₁ words₂ : List Word) :
    totalDepLength { words := words₁, deps := deps, rootIdx := rootIdx } =
    totalDepLength { words := words₂, deps := deps, rootIdx := rootIdx } := rfl

/-- Even at the single-dependency level, `depLength` is `|head − dep|`
    — the grammatical relation is irrelevant. -/
theorem depLength_ignores_relation (h d : Nat) (r₁ r₂ : UD.DepRel) :
    depLength ⟨h, d, r₁⟩ = depLength ⟨h, d, r₂⟩ := rfl

/-- Corollary of `dlm_word_invariant`: trees that differ only in whether
    their NPs are discourse-given or discourse-new receive identical
    DLM cost. So Dependency Locality, as a pure tree-structural cost,
    cannot reproduce the newness effect that
    @cite{arnold-wasow-losongco-ginstrom-2000} demonstrate. -/
theorem dlm_discourse_blind
    (deps : List Dependency) (rootIdx : Nat) (givenWords newWords : List Word) :
    totalDepLength { words := givenWords, deps := deps, rootIdx := rootIdx } =
    totalDepLength { words := newWords, deps := deps, rootIdx := rootIdx } :=
  dlm_word_invariant deps rootIdx givenWords newWords

-- ============================================================================
-- § 9: DLM Derivation of `heavyDiff` — Heaviness Is Not a Stipulation
-- ============================================================================

/-! @cite{futrell-gibson-2020} establish dependency length minimization (DLM) as
the explanatory principle behind a wide range of word-order universals,
including @cite{behaghel-1909}'s law of growing constituents (their §2.3).
The argument: in a head-initial language, when a head V has multiple
right-dependents, total dependency length from V is minimized by ordering
them shortest-first, because the head→dep distance to the second
constituent equals the length of the first plus one.

Specialized to Arnold's binary postverbal alternation:

- Order V Y X (head-initial): V→head(Y) = 1, V→head(X) = |Y|+1.
  V-side DLM cost = |Y| + 2.

So `goalLast` (V theme goal) costs `|theme|+2` and `themeLast` (V goal
theme) costs `|goal|+2`. DLM picks the order whose first constituent is
shorter — and *that* is what the `*HEAVY-FIRST` constraint operationalizes.
The `heavyDiff` sign is therefore not a free parameter of the
formalization but a theorem about DLM. -/

/-- DLM cost contribution from the verb to its two postverbal complement
    heads, under a head-initial binary structure. The verb sits at
    position 0; the first constituent occupies positions 1…|first|, so
    its head (also at position 1, head-initial) is distance 1 from V,
    and the second constituent's head is at position |first|+1. -/
def postverbalDLMCost (p : Pair) : Order → Nat
  | .goalLast  => p.1.wordCount + 2   -- V theme goal: cost = |theme| + 2
  | .themeLast => p.2.wordCount + 2   -- V goal theme: cost = |goal|  + 2

/-- **Heaviness is DLM, not a stipulation.** The MaxEnt grammar's
    `*HEAVY-FIRST` constraint signal `heavyDiff` is exactly the sign of
    the DLM cost difference between the two orderings. With this
    bridge, `heavyDiff` is no longer a primitive of the formalization —
    it is a theorem about which ordering @cite{futrell-gibson-2020}'s
    dependency-length cost minimizes on a binary postverbal pair. -/
theorem heavyDiff_eq_dlm_signal (p : Pair) :
    0 < heavyDiff p ↔
    postverbalDLMCost p .themeLast < postverbalDLMCost p .goalLast := by
  rw [heavyDiff_pos_iff]
  show p.2.wordCount < p.1.wordCount ↔ p.2.wordCount + 2 < p.1.wordCount + 2
  omega

/-- The DLM cost difference matches `heavyDiff` numerically up to scale:
    `cost(goalLast) - cost(themeLast) = p.1.wordCount - p.2.wordCount`,
    which has the same sign as `heavyDiff`. This is the "exact"
    arithmetic version of `heavyDiff_eq_dlm_signal` and makes the
    DLM-cost gap directly computable from word counts. -/
theorem dlm_diff_eq_wordCount_diff (p : Pair) :
    (postverbalDLMCost p .goalLast : Int) - postverbalDLMCost p .themeLast =
    (p.1.wordCount : Int) - p.2.wordCount := by
  show ((p.1.wordCount + 2 : Nat) : Int) - ((p.2.wordCount + 2 : Nat) : Int) =
       (p.1.wordCount : Int) - p.2.wordCount
  omega

-- ============================================================================
-- § 10: UID Derivation of `newDiff` — Newness as Information-Density Pressure
-- ============================================================================

/-! Genzel & Charniak's uniform information density (UID), elaborated in
@cite{levy-2008}'s expectation-based parsing, predicts that high-surprisal
material should be placed *late* in an utterance: by then more context has
been processed, so high-information words can be integrated with greater
predictability and lower per-step processing load.

For Arnold's binary postverbal pair, this maps cleanly: discourse-new
material is high-surprisal (the listener must construct a fresh referent),
discourse-given material is low-surprisal (the referent is already
active). UID therefore prefers placing the new constituent last — exactly
the direction `*NEW-FIRST` operationalizes.

Unlike the DLM/heaviness bridge, this is an *implication* rather than a
biconditional: UID over a richer surprisal scale ({.new, .given,
.focused}) makes finer-grained predictions than the binary
new-vs-given distinction `*NEW-FIRST` operationalizes. Whenever
`newDiff p > 0`, however, UID strictly prefers the same ordering. -/

/-- A coarse two-level surprisal proxy keyed on discourse status:
    `.new` is high-information (1), `.given` is low (0). `.focused`
    contributes 0 here — focused material has been activated by an
    explicit cue and is not surprising in the UID sense. This matches
    the asymmetric pattern of Arnold's `*NEW-FIRST` constraint, which
    fires only when one side is `.new` and the other is `.given`. -/
def discourseSurprisal : DiscourseStatus → ℚ
  | .new => 1
  | .given => 0
  | .focused => 0

/-- UID cost for the binary postverbal pair: the surprisal of whichever
    constituent occupies the verb-adjacent (first) position. UID prefers
    delaying high-surprisal material, so this should be minimized. -/
def uidCost (p : Pair) : Order → ℚ
  | .goalLast  => discourseSurprisal p.1.discourse  -- theme is first
  | .themeLast => discourseSurprisal p.2.discourse  -- goal is first

/-- **Newness is UID, in the direction `*NEW-FIRST` cares about.**
    Whenever the MaxEnt grammar's `newDiff` signal favors `themeLast`
    (theme new + goal given), UID strictly prefers the same order. The
    converse fails because UID makes finer distinctions than `newDiff`
    (e.g., UID still prefers `themeLast` when theme is new and goal is
    focused, but `newDiff = 0` there). -/
theorem newDiff_pos_implies_uid_prefers_themeLast {p : Pair}
    (h : 0 < newDiff p) :
    uidCost p .themeLast < uidCost p .goalLast := by
  obtain ⟨h1, h2⟩ := newDiff_pos_iff.mp h
  simp [uidCost, discourseSurprisal, h1, h2]

-- ============================================================================
-- § 11: Subsumption Under Information Locality
-- ============================================================================

/-! With §9 and §10 in place, Arnold's two MaxEnt constraints are no
longer free stipulations — each is the boundary signal of an
independently-motivated processing cost already formalized in linglib:

| Constraint | Bridge | Cost lives in |
|---|---|---|
| `*HEAVY-FIRST` | `heavyDiff_eq_dlm_signal` | `Theories.Syntax.DependencyGrammar.Formal.DependencyLength` |
| `*NEW-FIRST`   | `newDiff_pos_implies_uid_prefers_themeLast` | `Theories.Processing.MemorySurprisal` (information locality) |

The two costs unify under @cite{futrell-2019}'s **information locality**
framework (see `Theories.Processing.MemorySurprisal.Basic`,
`MutualInfoProfile.weightedSum`): both DLM and UID are special cases of
minimizing Σ (memory cost × mutual information) across the utterance.

- DLM is the limit where mutual information is uniform across positions
  (only structural distance matters).
- UID is the limit where structural distance is held constant and only
  per-word surprisal varies.

The fact that `*HEAVY-FIRST` and `*NEW-FIRST` are *both* needed in the
MaxEnt grammar — and neither reduces to the other empirically
(@cite{arnold-wasow-losongco-ginstrom-2000} §2-3,
`heaviness_and_newness_genuinely_independent`) — reflects that real
utterances vary along *both* the structural-distance and surprisal
axes. The MaxEnt weights `wH` / `wN` are then empirical estimates of
how much each pressure dominates in a given construction, with the
underlying processing theory supplying the constraint definitions
themselves rather than leaving them as stipulated penalties.

### Architectural anchor: the lossy-memory predictor

`MutualInfoProfile.weightedSum` is itself a *behavioural profile* of a
deeper substrate: a `MemoryProcess` (@cite{futrell-gibson-levy-2020},
formalized in `Theories.Processing.Memory.Basic`) — a predictor that
reads from a lossily-encoded summary of the past rather than from the
raw history. Classical surprisal arises as the lossless special case
(`MemoryProcess.expectedSurprisal_eq_surprisal_of_lossless` in
`Memory.LossyContext`); finite-capacity memory shifts it upward by an
amount controlled by which information the encoder retains.

Both Arnold constraints are diagnostic of this finite memory:
- `*HEAVY-FIRST` (DLM) penalises orderings that stress retention —
  long first constituents force the encoder to carry more history
  before integration, increasing per-bit memory cost.
- `*NEW-FIRST` (UID) penalises orderings that stress prediction —
  high-surprisal items at sentence-initial position face a memory
  state with no informative context yet to condition on.

The 4-level grounding chain is therefore explicit:

```
MemoryProcess (lossy substrate; Theories.Processing.Memory)
   ↓  (behavioural profile across distances)
MemorySurprisal.MutualInfoProfile (information locality)
   ↓  (specialise to one axis)
DLM (uniform info, distance varies) │ UID (uniform distance, info varies)
   ↓  (sign-of-cost-difference signal on a binary postverbal pair)
*HEAVY-FIRST                        │ *NEW-FIRST
```

What the new substrate buys here is not new theorems about Arnold's
data — `heavyDiff_eq_dlm_signal` and `newDiff_pos_implies_uid_prefers_themeLast`
already do that work — but a *common architectural source* for both
constraints. Where information locality says "DLM and UID are limits
of the same cost function", `MemoryProcess` says "and that cost
function is the expected surprisal of a memory-bottlenecked
predictor". The two-constraint MaxEnt grammar is then a quantitative
read-out of how that bottleneck shows up in postverbal ordering. -/

end ArnoldEtAl2000
