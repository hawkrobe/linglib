import Linglib.Semantics.Questions.Basic
import Linglib.Core.Probability.Decision.Basic
import Linglib.Semantics.Questions.Entailment

/-!
# [van-rooy-2003]: Questioning to Resolve Decision Problems
[groenendijk-stokhof-1984] [karttunen-1977] [ginzburg-1995] [merin-1999-relevance]
[blackwell-1953]

Single-paper formalisation of [van-rooy-2003], "Questioning to
Resolve Decision Problems", *Linguistics and Philosophy* 26.6:
727–763. The paper grounds question semantics in Bayesian decision
theory: questions are evaluated by how their answers affect the
optimal action in the questioner's decision problem.

## Substrate identification

The decision-theoretic machinery — `EU`, `UV`, `VSI`, `DecisionProblem`
— is already in `Core/Probability/Decision/Basic.lean`. Van Rooy's
notation maps to the substrate as:

| [van-rooy-2003]                             | substrate                                  |
|--------------------------------------------------|--------------------------------------------|
| `EU(a) = ∑_w P(w) · U(a, w)` (p. 733)            | `Core.DecisionTheory.DecisionProblem.expectedUtility`      |
| `UV(Choose now) = max_a EU(a)` (p. 734)          | `Core.DecisionTheory.DecisionProblem.value`              |
| `EU(a, C) = ∑_w P_C(w) · U(a, w)` (p. 735)       | `Core.DecisionTheory.DecisionProblem.condExpectedUtility`        |
| `UV(Learn C, choose later) = max_a EU(a, C)`     | `Core.DecisionTheory.DecisionProblem.condValue`   |
| `UV(C) = UV(L C, c later) − UV(C now)` (p. 735)  | `Core.DecisionTheory.DecisionProblem.utilityValue`         |
| `UV*(C) = VSI(C)` ≥ 0 (p. 735)                   | `Core.DecisionTheory.DecisionProblem.valueSampleInfo`      |
| `EUV(Q) = ∑_q P(q) · UV(q)` (p. 742)             | `Core.DecisionTheory.DecisionProblem.questionUtility`      |
| `Q ⊑ Q'`  (every Q-alt ⊆ some Q'-alt) (p. 741)   | `Question.Entails`                 |
| `C resolves DP` (p. 736)                         | `Core.DecisionTheory.DecisionProblem.IsResolved`           |

## What this file proves

* **§3.1 Action-induced partition `A*`** (p. 736-737):
  `optimalityCell dp acts a` and `actionPartition`.
* **§3.1 *C* resolves DP** (p. 736): the substrate's
  `Core.DecisionTheory.DecisionProblem.IsResolved dp acts C` — some action weakly
  dominates every other on every world in C.
* **§3.1/§4.1 decision-relevance** (`IsDecisionRelevant`): the
  qualitative, prior-free core of van Rooy's relevance — a question is
  *completely irrelevant* exactly when `EUV(Q) = EVSI(Q) = 0`, i.e. no
  answer changes the optimal action (p. 742). `alts_resolve_distinct`
  recasts a witness in the substrate's `IsResolved` vocabulary.
* **§4.1 Blackwell Fact** (p. 741, 743): "Q is more informative than Q'" is van
  Rooy's `Q ⊑ Q'`. Van Rooy's §4.1 theorem (p. 743, "a special case of
  [blackwell-1953]") is the quantitative *iff* `Q ⊑ Q' ↔ ∀ DP, EUV(Q) ≥ EUV(Q')`,
  stated over partition cells as `blackwell_euv_fact`. Its `⟹` ("only if")
  direction — a finer partition weakly dominates a coarser one for every decision
  problem — is the data-processing inequality `blackwell_euv_fact_forward`
  (deriving the substrate refinement map from `⊑` and applying
  `Core.DecisionTheory.DecisionProblem.questionUtility_mono_of_refines`). The `⟸`
  direction is proved by an elementary two-world / two-action witness (both
  `[Nontrivial A]` and `hcoarse_cover` rule out the vacuous-dominance corner cases
  documented at the theorem).
  `decisionRelevance_preserved_under_cover` is a separate, qualitative
  one-directional transfer (see its docstring).

## What this file does NOT replicate

* The *identification-question* discussion (§2 (1)–(8)) requires
  named-individual / referential machinery beyond plain `Set W`;
  deferred.
* The *underspecified meaning* proposal (§5) requires a typed
  ambiguity-resolution layer beyond `Question W`; deferred.
* The Italian-newspaper mention-some example (§3.2 (12)) is the
  natural target for the next refinement; it is
  `gs1984_mentionsome_italian_newspaper` in
  `Data.Examples.GroenendijkStokhof1984`.

## Provenance

The `IsDecisionRelevant` family and the decision-relevance
preservation theorem were consolidated here from the former
`Semantics/Questions/DecisionTheoretic.lean` (a single-paper
formalisation that did not meet the theory-layer ≥2-Studies admission
bar). The reusable substrate it relied on stays one layer down:
`Question.Entails` in `Entailment.lean` (`CoversAltsOf` is local below), the
`Core.DecisionTheory` value vocabulary in `DecisionTheory.lean`.
-/

namespace VanRooy2003

open Core Core.DecisionTheory Core.DecisionTheory.DecisionProblem Question

variable {W A : Type*}

/-! ### §3.1 Action-induced partition `A*` (p. 736-737)

[van-rooy-2003] p. 736: "Notice that not only a question, but
also the set of alternative actions, A, gives rise to a set of
propositions. We can relate each action a ∈ A to the set of worlds
in which there is no other action b in A that is strictly better.
We will denote the proposition corresponding with a by a*". -/

/-- The **optimality cell** of action `a`: the worlds where `a`
    *strictly* dominates every other action in `acts`.

    [van-rooy-2003]'s `a*` (p. 736-737) is the weaker "no other action
    is strictly better" region; this strict version is van Rooy's
    *partition condition* (p. 737: "exactly one action a ∈ A such that
    ∀b ∈ A−{a}: U(a,w) > U(b,w)"), which is what makes `actionPartition`
    genuinely disjoint (`optimalityCell_pairwise_disjoint`). -/
def optimalityCell (dp : DecisionProblem ℚ W A) (acts : Set A) (a : A) : Set W :=
  {w | ∀ b ∈ acts, b ≠ a → dp.utility w a > dp.utility w b}

/-- The **action-induced partition** `A*`: the set of optimality
    cells. [van-rooy-2003] p. 736-737. -/
def actionPartition (dp : DecisionProblem ℚ W A) (acts : Set A) : Set (Set W) :=
  optimalityCell dp acts '' acts

/-- The optimality cells are pairwise disjoint: each world lies in at
    most one cell. (Page 737: "the set of propositions A* does in
    general not partition the state space, but it does when for each
    world `w` there is always exactly one action a ∈ A such that
    ∀b ∈ A−{a} : U(a,w) > U(b,w)".) -/
theorem optimalityCell_pairwise_disjoint
    (dp : DecisionProblem ℚ W A) (acts : Set A)
    {a a' : A} (haa' : a ≠ a')
    (w : W) (hwa : w ∈ optimalityCell dp acts a) (hwa' : w ∈ optimalityCell dp acts a')
    (ha_acts : a ∈ acts) (ha'_acts : a' ∈ acts) :
    False := by
  have h1 : dp.utility w a > dp.utility w a' := hwa a' ha'_acts (Ne.symm haa')
  have h2 : dp.utility w a' > dp.utility w a := hwa' a ha_acts haa'
  exact absurd h1 (not_lt_of_gt h2)

/-! ### §3.1 *C* resolves DP (p. 736)

> "We should say that information `C` resolves a decision problem if
> after learning `C`, one of the actions in `A` dominates all other
> actions, i.e., if in each resulting world no action has a higher
> utility than this one."

This is exactly `Core.DecisionTheory.DecisionProblem.IsResolved dp acts C`. We do not
introduce a paper-vocabulary alias — consumers should use the
substrate predicate directly. -/

/-! ### §3.1/§4.1 Decision-relevance

A question is *completely irrelevant* exactly when `EUV(Q) = EVSI(Q) = 0`
— when no answer would change the agent's decision (p. 742). The
qualitative core below exhibits a witness pair of answers that *do*
change it. -/

/-- `Q` is **decision-relevant** to `dp` (relative to action set `acts`):
    there exist two **nonempty** alternatives `p, p' ∈ alt Q` and two
    actions `a, a'` such that `a` strictly dominates `a'` on every world
    of `p` while `a'` strictly dominates `a` on every world of `p'`.
    Learning *which* alternative obtains then shifts the optimal action.

    This is the qualitative, prior-independent core of [van-rooy-2003]'s
    relevance: a question is *completely irrelevant* exactly when
    `EUV(Q) = EVSI(Q) = 0`, i.e. no answer changes the agent's decision
    (p. 742); `IsDecisionRelevant` exhibits a witness pair of answers
    that *do* change it. It is therefore a **sufficient condition** for
    `EUV(Q) > 0` that holds for *any* prior assigning positive mass to
    both cells, and is strictly stronger than van Rooy's prior-weighted
    `EUV(Q) > 0` / `UV(C) > 0` relevance (pp. 735-736, 742).

    The nonemptiness clauses rule out the degenerate `Q = ⊥` case where
    the dominance conditions hold vacuously over empty witnesses. -/
def IsDecisionRelevant
    (Q : Question W) (dp : DecisionProblem ℚ W A) (acts : Set A) : Prop :=
  ∃ p ∈ alt Q, p.Nonempty ∧ ∃ p' ∈ alt Q, p'.Nonempty ∧
    ∃ a ∈ acts, ∃ a' ∈ acts,
      (∀ w ∈ p,  dp.utility w a  > dp.utility w a') ∧
      (∀ w ∈ p', dp.utility w a' > dp.utility w a)

/-- A `IsDecisionRelevant` witness exhibits two `Q`-alts whose two-action
    restriction `{a, a'}` is `IsResolved` (p. 736) to *distinct* actions:
    on `p`, action `a` resolves `(dp, {a, a'})`; on `p'`, `a'` does. So
    decision-relevance is precisely "two `Q`-alts resolve to distinct
    actions" in the substrate's `IsResolved` vocabulary. -/
theorem IsDecisionRelevant.alts_resolve_distinct
    {Q : Question W} {dp : DecisionProblem ℚ W A} {acts : Set A}
    (h : IsDecisionRelevant Q dp acts) :
    ∃ p ∈ alt Q, p.Nonempty ∧ ∃ p' ∈ alt Q, p'.Nonempty ∧
      ∃ a ∈ acts, ∃ a' ∈ acts, a ≠ a' ∧
        IsResolved dp {a, a'} p ∧ IsResolved dp {a, a'} p' := by
  obtain ⟨p, hp, hpne, p', hp', hp'ne, a, ha, a', ha', hpa, hpa'⟩ := h
  refine ⟨p, hp, hpne, p', hp', hp'ne, a, ha, a', ha', ?_, ?_, ?_⟩
  · -- a ≠ a': follows from strict-domination on a nonempty p.
    intro heq
    obtain ⟨w, hw⟩ := hpne
    have h1 : dp.utility w a > dp.utility w a' := hpa w hw
    rw [heq] at h1
    exact absurd h1 (lt_irrefl _)
  · -- IsResolved dp {a, a'} p: action a weakly dominates a' on p
    refine ⟨a, by simp, ?_⟩
    intro b hb w hw
    rcases hb with rfl | hb'
    · exact le_refl _
    · rw [Set.mem_singleton_iff] at hb'
      subst hb'
      exact le_of_lt (hpa w hw)
  · -- IsResolved dp {a, a'} p': action a' weakly dominates a on p'
    refine ⟨a', by simp, ?_⟩
    intro b hb w hw
    rcases hb with rfl | hb'
    · exact le_of_lt (hpa' w hw)
    · rw [Set.mem_singleton_iff] at hb'
      subst hb'
      exact le_refl _

/-- A question with at most one alternative is not decision-relevant:
    a single answer carries no decision value (`EVSI = 0`, p. 742). -/
theorem not_isDecisionRelevant_of_subsingleton_alt
    {Q : Question W} {dp : DecisionProblem ℚ W A} {acts : Set A}
    (hSingle : ∀ p p', p ∈ alt Q → p' ∈ alt Q → p = p') :
    ¬ IsDecisionRelevant Q dp acts := by
  rintro ⟨p, hp, hpne, p', hp', _, a, _, a', _, hpa, hpa'⟩
  rcases hSingle p p' hp hp' with rfl
  obtain ⟨w, hw⟩ := hpne
  exact absurd (hpa w hw) (not_lt_of_gt (hpa' w hw))

/-! ### §4.1 Question ordering (p. 741)

[van-rooy-2003] p. 741: "Q is a *better* question than Q' [...]
In terms of [groenendijk-stokhof-1984] partition semantics this comes
down to the natural requirement that for every element of Q there must
be an element of Q' such that the former entails the latter, i.e.,
`Q ⊑ Q'`:

    Q ⊑ Q' iff ∀q ∈ Q : ∃q' ∈ Q' : q ⊆ q'."

This is exactly `Question.Q.Entails Q'`. We do not introduce a
paper-vocabulary alias — consumers should write `Q.Entails Q'`
(or use `≤` on `Question W`'s lattice instance) directly. The relation
is reflexive (`Entails.refl`) and transitive
(`Entails.trans`). -/

/-! ### §4.1 Decision-relevance preservation -/

/-- Every nonempty alternative of `Q'` contains a nonempty alternative
    of `Q`: the dual of `Question.Entails`, in the form the preservation
    theorem below requires. The nonemptiness bars `⊥`-style vacuous
    covering, matching `IsDecisionRelevant`'s substantive witnesses. -/
def CoversAltsOf (Q Q' : Question W) : Prop :=
  ∀ q ∈ alt Q', q.Nonempty → ∃ p ∈ alt Q, p.Nonempty ∧ p ⊆ q

/-- **Qualitative monotonicity of decision-relevance** (substrate
    corollary in the spirit of [van-rooy-2003]'s §4.1 relevance
    ordering): when `Q` covers `Q'`'s alternatives (`CoversAltsOf`), a
    decision-relevance witness for `Q'` lifts to one for `Q`.

    This is **not** van Rooy's §4.1 Blackwell theorem itself. That
    theorem (p. 743, "a special case of [blackwell-1953]") is the
    quantitative *iff* `Q.Entails Q' ↔ ∀ dp, EUV(Q) ≥ EUV(Q')`
    over the expected utility value `EUV` (= substrate `questionUtility`,
    with `EUV = EVSI` available as `questionUtility_eq_expectedValueSampleInfo`). The result here is a
    one-directional, prior-free Prop transfer over the *dual* condition
    `CoversAltsOf`: on a general inquisitive (non-partition) `Question W`,
    `Entails` (P-alts ⊆ Q-alts) does not transfer the qualitative
    witness, but its dual does. On partition questions the two coincide,
    recovering [van-rooy-2003]'s partition-based argument.

    For the *quantitative* §4.1 Fact (p. 743), the EUV-monotonicity ("only if")
    direction is now `Core.DecisionTheory.DecisionProblem.questionUtility_split_ge` (a finer
    partition has `EUV ≥` the coarser one, for every decision problem). The
    remaining gap to the full `Entails`-level *iff* is (i) a
    `Question W → Finset (Finset W)` finite-alternatives partition-cell adapter, and
    (ii) the [blackwell-1953] converse
    `ProbabilityTheory.isGarblingOf_of_blackwellDominates`. -/
theorem decisionRelevance_preserved_under_cover
    {Q Q' : Question W} (hCover : CoversAltsOf Q Q')
    {dp : DecisionProblem ℚ W A} {acts : Set A}
    (hQ' : IsDecisionRelevant Q' dp acts) :
    IsDecisionRelevant Q dp acts := by
  obtain ⟨p, hp, hpne, p', hp', hp'ne, a, ha, a', ha', hpa, hpa'⟩ := hQ'
  obtain ⟨pP, hpP, hpP_ne, hpP_sub⟩ := hCover p hp hpne
  obtain ⟨p'P, hp'P, hp'P_ne, hp'P_sub⟩ := hCover p' hp' hp'ne
  exact ⟨pP, hpP, hpP_ne, p'P, hp'P, hp'P_ne, a, ha, a', ha',
         fun w hw => hpa w (hpP_sub hw),
         fun w hw => hpa' w (hp'P_sub hw)⟩

/-! ### §4.1 The Blackwell Fact (p. 743): partition-cell form

[van-rooy-2003] p. 743 states that `Q ⊑ Q' ↔ ∀ DP, EUV(Q) ≥ EUV(Q')` is "a special case
of [blackwell-1953]". We state it over [groenendijk-stokhof-1984] partition cells — the
`Finset (Finset W)` that `Core.DecisionTheory.DecisionProblem.questionUtility` consumes. There, van Rooy's
`Q ⊑ Q'` (p. 741: "∀ q ∈ Q : ∃ q' ∈ Q' : q ⊆ q'") is the cell-level refinement
`∀ f ∈ fine, ∃ c ∈ coarse, f ⊆ c`, and the value side ranges over every decision problem
with a proper prior.

(The lift to the type-level `Question.Entails`/`Question W` is the remaining
mechanical step: an `alt Q → Finset (Finset W)` adapter via `Set.Finite.toFinset`,
discharging `Entails` against this cell refinement.) -/

/-- **[van-rooy-2003] §4.1 Fact, the `⟹` ("only if") direction** (p. 743): a finer question
is weakly better than a coarser one for *every* decision problem (the data-processing
inequality). Van Rooy's refinement `fine ⊑ coarse` (each fine cell `⊆` some coarse cell,
p. 741) plus the partition structure furnish the substrate refinement map — each fine cell's
containing coarse cell — and `Core.DecisionTheory.DecisionProblem.questionUtility_mono_of_refines` concludes.

`hfine_cover` and the disjointness hypotheses encode that `fine`, `coarse` are genuine
[groenendijk-stokhof-1984] partitions of the world set. -/
theorem blackwell_euv_fact_forward [Fintype W] [DecidableEq W] [DecidableEq A]
    {fine coarse : Finset (Finset W)}
    (hcoarse_disj : ∀ c₁ ∈ coarse, ∀ c₂ ∈ coarse, c₁ ≠ c₂ → Disjoint c₁ c₂)
    (hfine_disj : ∀ f₁ ∈ fine, ∀ f₂ ∈ fine, f₁ ≠ f₂ → Disjoint f₁ f₂)
    (hfine_cover : ∀ w : W, ∃ f ∈ fine, w ∈ f)
    (href : ∀ f ∈ fine, ∃ c ∈ coarse, f ⊆ c)
    (dp : DecisionProblem ℚ W A) (acts : Finset A) (hprior : ∀ w, 0 ≤ dp.prior w) :
    questionUtility dp acts coarse ≤ questionUtility dp acts fine := by
  classical
  set g : Finset W → Finset W :=
    fun f => if h : ∃ c ∈ coarse, f ⊆ c then h.choose else ∅ with hg_def
  have hgspec : ∀ f ∈ fine, g f ∈ coarse ∧ f ⊆ g f := by
    intro f hf
    have h : ∃ c ∈ coarse, f ⊆ c := href f hf
    have hgf : g f = h.choose := by rw [hg_def]; exact dif_pos h
    rw [hgf]; exact h.choose_spec
  refine questionUtility_mono_of_refines dp acts g
    (fun f hf => (hgspec f hf).1) ?_ hfine_disj hprior
  -- hcover: every coarse cell is the union of the fine cells mapping to it
  intro c hc
  refine le_antisymm ?_ ?_
  · -- c ⊆ ⨆ fiber
    intro w hw
    obtain ⟨f, hf, hwf⟩ := hfine_cover w
    have hwgf : w ∈ g f := (hgspec f hf).2 hwf
    have hgfc : g f = c := by
      by_contra hne
      exact absurd hw (Finset.disjoint_left.mp
        (hcoarse_disj (g f) (hgspec f hf).1 c hc hne) hwgf)
    rw [Finset.mem_sup]
    exact ⟨f, Finset.mem_filter.mpr ⟨hf, hgfc⟩, hwf⟩
  · -- ⨆ fiber ⊆ c
    refine Finset.sup_le (fun f hf => ?_)
    rw [Finset.mem_filter] at hf
    exact hf.2 ▸ (hgspec f hf.1).2

/-- **[van-rooy-2003] §4.1 Fact** (p. 743), partition-cell form. For two
[groenendijk-stokhof-1984] partitions `fine`, `coarse` of the worlds, van Rooy's refinement
order `fine ⊑ coarse` (every fine cell is contained in some coarse cell, p. 741) is
equivalent to: the finer question has expected utility value `≥` the coarser one for
*every* decision problem (with a proper, nonnegative prior). Van Rooy calls this "a special
case of [blackwell-1953]".

The `⟹` direction is `blackwell_euv_fact_forward` (the data-processing inequality); the
`⟸` direction (EUV-dominance across all decision problems forces refinement) is proved
here by the elementary two-world / two-action witness: if some fine cell holds worlds
`w`, `v` in distinct coarse cells, the identification DP (nonneg prior 1 on `w` and `v`,
utility 1 for naming each world's coarse cell) values `coarse` strictly above `fine`.

### Hypothesis corrections

Two hypotheses beyond the forward direction's are required, each grounded in a concrete
counterexample to the plain statement:

* `[Nontrivial A]` (else `acts` is forced to `∅`, both `questionUtility` sides collapse to
  `0`, and dominance holds vacuously — while refinement can fail).
* `[Nonempty W]` and `hcoarse_cover` (a mirror of `hfine_cover`) — without either, taking
  e.g. `W = {w}`, `fine = {{w}}`, `coarse = ∅` makes both `questionUtility` sides `0`
  (empty coarse sum on one side, `utilityValue = condValue − value = 0` on the other)
  while refinement `∃ c ∈ ∅, {w} ⊆ c` fails. Together they force `coarse` to be a full
  partition of `W`, ruling out both the empty-`W` and the uncovering-`coarse` pathologies. -/
theorem blackwell_euv_fact [Fintype W] [DecidableEq W] [DecidableEq A]
    [Nontrivial A] [Nonempty W]
    {fine coarse : Finset (Finset W)}
    (hfine_disj : ∀ f₁ ∈ fine, ∀ f₂ ∈ fine, f₁ ≠ f₂ → Disjoint f₁ f₂)
    (hcoarse_disj : ∀ c₁ ∈ coarse, ∀ c₂ ∈ coarse, c₁ ≠ c₂ → Disjoint c₁ c₂)
    (hfine_cover : ∀ w : W, ∃ f ∈ fine, w ∈ f)
    (hcoarse_cover : ∀ w : W, ∃ c ∈ coarse, w ∈ c) :
    (∀ f ∈ fine, ∃ c ∈ coarse, f ⊆ c) ↔
      (∀ (dp : DecisionProblem ℚ W A) (acts : Finset A), (∀ w, 0 ≤ dp.prior w) →
        questionUtility dp acts coarse ≤ questionUtility dp acts fine) := by
  refine ⟨fun href dp acts hprior =>
    blackwell_euv_fact_forward hcoarse_disj hfine_disj hfine_cover href dp acts hprior, ?_⟩
  -- Contrapose and extract an offending fine cell.
  intro hdom
  by_contra hnref
  push Not at hnref
  obtain ⟨f₀, hf₀_fine, hf₀_uncov⟩ := hnref
  -- With [Nonempty W] + hcoarse_cover, coarse is nonempty (some c₀ contains
  -- an arbitrary world), and hf₀_uncov applied to c₀ finds v ∈ f₀ \ c₀.
  obtain ⟨w_wit⟩ := ‹Nonempty W›
  obtain ⟨c₀, hc₀, _⟩ := hcoarse_cover w_wit
  have h_ns_c₀ : ¬ f₀ ⊆ c₀ := hf₀_uncov c₀ hc₀
  rw [Finset.not_subset] at h_ns_c₀
  obtain ⟨v, hv_f₀, hv_nc₀⟩ := h_ns_c₀
  obtain ⟨c_v, hc_v, hv_c_v⟩ := hcoarse_cover v
  have hc_v_ne_c₀ : c_v ≠ c₀ := fun heq => hv_nc₀ (heq ▸ hv_c_v)
  -- Now apply hf₀_uncov to c_v: get w ∈ f₀ \ c_v.
  have h_ns_c_v : ¬ f₀ ⊆ c_v := hf₀_uncov c_v hc_v
  rw [Finset.not_subset] at h_ns_c_v
  obtain ⟨w, hw_f₀, hw_nc_v⟩ := h_ns_c_v
  obtain ⟨c_w, hc_w, hw_c_w⟩ := hcoarse_cover w
  have hc_w_ne_c_v : c_w ≠ c_v := fun heq => hw_nc_v (heq ▸ hw_c_w)
  have hwv_ne : w ≠ v := fun heq => by
    exact absurd (heq ▸ hv_c_v)
      (Finset.disjoint_left.mp (hcoarse_disj c_w hc_w c_v hc_v hc_w_ne_c_v) hw_c_w)
  -- Two distinct actions from `[Nontrivial A]`.
  obtain ⟨a₁, a₂, ha_ne⟩ := exists_pair_ne A
  -- The identification decision problem: prior mass `1` on `w` and `v`; utility
  -- `1` iff the action names the world's coarse cell (`a₁ ↦ c_w`, `a₂ ↦ c_v`).
  let dp : DecisionProblem ℚ W A :=
    { prior := fun w' => if w' = w then 1 else if w' = v then 1 else 0
      utility := fun w' a =>
        if w' = w ∧ a = a₁ then 1
        else if w' = v ∧ a = a₂ then 1
        else 0 }
  have hprior_nn : ∀ w' : W, 0 ≤ dp.prior w' := fun w' => by
    show 0 ≤ if w' = w then (1 : ℚ) else if w' = v then 1 else 0
    split_ifs <;> norm_num
  have hyp := hdom dp {a₁, a₂} hprior_nn
  -- Per-cell characterization: `∑_{w'∈S} prior · util aᵢ` is the indicator that
  -- the corresponding world lies in `S`.
  have hsum_a₁ : ∀ S : Finset W,
      ∑ w' ∈ S, dp.prior w' * dp.utility w' a₁ = if w ∈ S then (1 : ℚ) else 0 := by
    intro S
    have hpt : ∀ w' : W, dp.prior w' * dp.utility w' a₁ = if w' = w then (1 : ℚ) else 0 := by
      intro w'
      show (if w' = w then (1 : ℚ) else if w' = v then 1 else 0) *
             (if w' = w ∧ a₁ = a₁ then 1 else if w' = v ∧ a₁ = a₂ then 1 else 0)
           = if w' = w then 1 else 0
      by_cases hw : w' = w
      · subst hw; simp
      · by_cases hv : w' = v
        · subst hv; simp [hw, ha_ne]
        · simp [hw, hv]
    calc ∑ w' ∈ S, dp.prior w' * dp.utility w' a₁
        = ∑ w' ∈ S, if w' = w then (1 : ℚ) else 0 := Finset.sum_congr rfl (fun w' _ => hpt w')
      _ = if w ∈ S then 1 else 0 := Finset.sum_ite_eq' S w (fun _ => (1 : ℚ))
  have hsum_a₂ : ∀ S : Finset W,
      ∑ w' ∈ S, dp.prior w' * dp.utility w' a₂ = if v ∈ S then (1 : ℚ) else 0 := by
    intro S
    have hpt : ∀ w' : W, dp.prior w' * dp.utility w' a₂ = if w' = v then (1 : ℚ) else 0 := by
      intro w'
      show (if w' = w then (1 : ℚ) else if w' = v then 1 else 0) *
             (if w' = w ∧ a₂ = a₁ then 1 else if w' = v ∧ a₂ = a₂ then 1 else 0)
           = if w' = v then 1 else 0
      by_cases hw : w' = w
      · subst hw; simp [hwv_ne, ha_ne.symm]
      · by_cases hv : w' = v
        · subst hv; simp [hwv_ne.symm]
        · simp [hw, hv]
    calc ∑ w' ∈ S, dp.prior w' * dp.utility w' a₂
        = ∑ w' ∈ S, if w' = v then (1 : ℚ) else 0 := Finset.sum_congr rfl (fun w' _ => hpt w')
      _ = if v ∈ S then 1 else 0 := Finset.sum_ite_eq' S v (fun _ => (1 : ℚ))
  -- Local specialization of `cellProbability_mul_condValue_eq_uValue` (private
  -- in `Core.Probability.Decision.Basic`, replicated here at `K := ℚ`).
  have hcpcv : ∀ (S : Finset W) (acts : Finset A) (hne : acts.Nonempty),
      dp.cellProbability S * dp.condValue acts S =
        acts.sup' hne (fun a => ∑ w' ∈ S, dp.prior w' * dp.utility w' a) := by
    intro S acts hne
    rw [condValue_of_nonempty hne]
    have hpsum_nn : 0 ≤ dp.cellProbability S :=
      Finset.sum_nonneg (fun w' _ => hprior_nn w')
    by_cases hcp : dp.cellProbability S = 0
    · rw [hcp, zero_mul]
      have hprior_zero : ∀ w' ∈ S, dp.prior w' = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun w' _ => hprior_nn w')).mp hcp
      exact (Finset.sup'_eq_of_forall (s := acts) (H := hne) (a := (0 : ℚ))
        (f := fun a => ∑ w' ∈ S, dp.prior w' * dp.utility w' a)
        (fun a _ => Finset.sum_eq_zero
          fun w' hw' => by rw [hprior_zero w' hw', zero_mul])).symm
    · have hS : S.sum dp.prior ≠ 0 := hcp
      rw [Finset.mul₀_sup' hpsum_nn _ acts hne]
      refine Finset.sup'_congr hne rfl (fun a _ => ?_)
      show S.sum dp.prior * dp.condExpectedUtility S a = ∑ w' ∈ S, dp.prior w' * dp.utility w' a
      rw [condExpectedUtility_of_ne_zero hS, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun w' _ => ?_)
      rw [div_mul_eq_mul_div, ← mul_div_assoc, mul_div_cancel_left₀ _ hS]
  -- For our action pair `{a₁, a₂}`, the `sup'` collapses to a `max` of indicators.
  have hcpcv_max : ∀ S : Finset W,
      dp.cellProbability S * dp.condValue {a₁, a₂} S =
        max (if w ∈ S then (1 : ℚ) else 0) (if v ∈ S then 1 else 0) := by
    intro S
    rw [hcpcv S {a₁, a₂} (Finset.insert_nonempty _ _)]
    refine le_antisymm ?_ ?_
    · refine Finset.sup'_le _ _ fun a ha => ?_
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      · rw [hsum_a₁]; exact le_max_left _ _
      · rw [hsum_a₂]; exact le_max_right _ _
    · refine max_le ?_ ?_
      · rw [← hsum_a₁ S]
        exact Finset.le_sup' (s := ({a₁, a₂} : Finset A))
          (f := fun a => ∑ w' ∈ S, dp.prior w' * dp.utility w' a) (by simp)
      · rw [← hsum_a₂ S]
        exact Finset.le_sup' (s := ({a₁, a₂} : Finset A))
          (f := fun a => ∑ w' ∈ S, dp.prior w' * dp.utility w' a) (by simp)
  -- Filter equality: cells intersecting `{w, v}` are exactly the identified
  -- pair on each side.
  have hcoarse_filter : coarse.filter (fun c => w ∈ c ∨ v ∈ c) = {c_w, c_v} := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    refine ⟨fun ⟨hc, hor⟩ => ?_, ?_⟩
    · rcases hor with hw | hv
      · left
        by_contra hne
        exact absurd hw_c_w
          (Finset.disjoint_left.mp (hcoarse_disj c hc c_w hc_w hne) hw)
      · right
        by_contra hne
        exact absurd hv_c_v
          (Finset.disjoint_left.mp (hcoarse_disj c hc c_v hc_v hne) hv)
    · rintro (rfl | rfl)
      · exact ⟨hc_w, Or.inl hw_c_w⟩
      · exact ⟨hc_v, Or.inr hv_c_v⟩
  have hfine_filter : fine.filter (fun f => w ∈ f ∨ v ∈ f) = {f₀} := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_singleton]
    refine ⟨fun ⟨hf, hor⟩ => ?_, ?_⟩
    · rcases hor with hw | hv
      · by_contra hne
        exact absurd hw_f₀
          (Finset.disjoint_left.mp (hfine_disj f hf f₀ hf₀_fine hne) hw)
      · by_contra hne
        exact absurd hv_f₀
          (Finset.disjoint_left.mp (hfine_disj f hf f₀ hf₀_fine hne) hv)
    · rintro rfl; exact ⟨hf₀_fine, Or.inl hw_f₀⟩
  -- Similar filter equalities for the individual indicators (needed for the
  -- `∑ cellProb` computations that appear via `hqu_eq` below).
  have hcoarse_w_filter : coarse.filter (fun c => w ∈ c) = {c_w} := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_singleton]
    refine ⟨fun ⟨hc, hw⟩ => ?_, fun heq => heq ▸ ⟨hc_w, hw_c_w⟩⟩
    by_contra hne
    exact absurd hw_c_w
      (Finset.disjoint_left.mp (hcoarse_disj c hc c_w hc_w hne) hw)
  have hcoarse_v_filter : coarse.filter (fun c => v ∈ c) = {c_v} := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_singleton]
    refine ⟨fun ⟨hc, hv⟩ => ?_, fun heq => heq ▸ ⟨hc_v, hv_c_v⟩⟩
    by_contra hne
    exact absurd hv_c_v
      (Finset.disjoint_left.mp (hcoarse_disj c hc c_v hc_v hne) hv)
  have hfine_w_filter : fine.filter (fun f => w ∈ f) = {f₀} := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_singleton]
    refine ⟨fun ⟨hf, hw⟩ => ?_, fun heq => heq ▸ ⟨hf₀_fine, hw_f₀⟩⟩
    by_contra hne
    exact absurd hw_f₀
      (Finset.disjoint_left.mp (hfine_disj f hf f₀ hf₀_fine hne) hw)
  have hfine_v_filter : fine.filter (fun f => v ∈ f) = {f₀} := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_singleton]
    refine ⟨fun ⟨hf, hv⟩ => ?_, fun heq => heq ▸ ⟨hf₀_fine, hv_f₀⟩⟩
    by_contra hne
    exact absurd hv_f₀
      (Finset.disjoint_left.mp (hfine_disj f hf f₀ hf₀_fine hne) hv)
  -- Cell probabilities on `{w, v}`-supported prior: each partition's cellProbs
  -- sum to the total prior mass (2).
  have hcp_eq : ∀ (S : Finset W),
      dp.cellProbability S
        = (if w ∈ S then (1 : ℚ) else 0) + (if v ∈ S then 1 else 0) := by
    intro S
    show ∑ w' ∈ S, (if w' = w then (1 : ℚ) else if w' = v then 1 else 0)
        = (if w ∈ S then 1 else 0) + (if v ∈ S then 1 else 0)
    have hpt : ∀ w' : W,
        (if w' = w then (1 : ℚ) else if w' = v then 1 else 0)
          = (if w' = w then 1 else 0) + (if w' = v then 1 else 0) := by
      intro w'
      by_cases hw : w' = w
      · subst hw; simp [hwv_ne]
      · by_cases hv : w' = v
        · subst hv; simp [hwv_ne.symm]
        · simp [hw, hv]
    rw [Finset.sum_congr rfl (fun w' _ => hpt w'), Finset.sum_add_distrib,
      Finset.sum_ite_eq' S w (fun _ => (1 : ℚ)),
      Finset.sum_ite_eq' S v (fun _ => (1 : ℚ))]
  -- Sum over coarse of the indicator `if w ∈ c then 1 else 0` = 1 (only c_w).
  have hi_w_coarse : (∑ c ∈ coarse, if w ∈ c then (1 : ℚ) else 0) = 1 := by
    rw [← Finset.sum_filter, hcoarse_w_filter, Finset.sum_singleton]
  have hi_v_coarse : (∑ c ∈ coarse, if v ∈ c then (1 : ℚ) else 0) = 1 := by
    rw [← Finset.sum_filter, hcoarse_v_filter, Finset.sum_singleton]
  have hi_w_fine : (∑ f ∈ fine, if w ∈ f then (1 : ℚ) else 0) = 1 := by
    rw [← Finset.sum_filter, hfine_w_filter, Finset.sum_singleton]
  have hi_v_fine : (∑ f ∈ fine, if v ∈ f then (1 : ℚ) else 0) = 1 := by
    rw [← Finset.sum_filter, hfine_v_filter, Finset.sum_singleton]
  -- Sum of max over coarse = 2 (via c_w and c_v being distinct nonzero contributors).
  have hmax_coarse :
      (∑ c ∈ coarse, max (if w ∈ c then (1 : ℚ) else 0) (if v ∈ c then 1 else 0)) = 2 := by
    have hswap : ∀ c : Finset W,
        max ((if w ∈ c then (1 : ℚ) else 0)) (if v ∈ c then 1 else 0)
          = if w ∈ c ∨ v ∈ c then (1 : ℚ) else 0 := by
      intro c
      by_cases hw : w ∈ c <;> by_cases hv : v ∈ c <;> simp [hw, hv]
    rw [Finset.sum_congr rfl (fun c _ => hswap c), ← Finset.sum_filter,
      hcoarse_filter, Finset.sum_insert (by simp [hc_w_ne_c_v]),
      Finset.sum_singleton]
    norm_num
  -- Sum of max over fine = 1 (only f₀ contributes).
  have hmax_fine :
      (∑ f ∈ fine, max (if w ∈ f then (1 : ℚ) else 0) (if v ∈ f then 1 else 0)) = 1 := by
    have hswap : ∀ f : Finset W,
        max ((if w ∈ f then (1 : ℚ) else 0)) (if v ∈ f then 1 else 0)
          = if w ∈ f ∨ v ∈ f then (1 : ℚ) else 0 := by
      intro f
      by_cases hw : w ∈ f <;> by_cases hv : v ∈ f <;> simp [hw, hv]
    rw [Finset.sum_congr rfl (fun f _ => hswap f), ← Finset.sum_filter,
      hfine_filter, Finset.sum_singleton]
  -- Cellprob sums (2 on each side) via the same indicator trick.
  have hcpP_coarse : ∑ c ∈ coarse, dp.cellProbability c = 2 := by
    simp_rw [hcp_eq]
    rw [Finset.sum_add_distrib, hi_w_coarse, hi_v_coarse]
    norm_num
  have hcpP_fine : ∑ f ∈ fine, dp.cellProbability f = 2 := by
    simp_rw [hcp_eq]
    rw [Finset.sum_add_distrib, hi_w_fine, hi_v_fine]
    norm_num
  -- Unfolded `questionUtility`: `∑ cellProb · condValue − value · ∑ cellProb`.
  have hqu_eq : ∀ (cells : Finset (Finset W)),
      questionUtility dp {a₁, a₂} cells
        = (∑ c ∈ cells, dp.cellProbability c * dp.condValue {a₁, a₂} c)
          - dp.value {a₁, a₂} * (∑ c ∈ cells, dp.cellProbability c) := by
    intro cells
    unfold DecisionProblem.questionUtility DecisionProblem.utilityValue
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    congr 1
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun c _ => mul_comm _ _)
  -- ∑ cellProb · condValue on each side = ∑ max = 2 (coarse) / 1 (fine).
  have hX_coarse : ∑ c ∈ coarse, dp.cellProbability c * dp.condValue {a₁, a₂} c = 2 := by
    simp_rw [hcpcv_max]; exact hmax_coarse
  have hX_fine : ∑ f ∈ fine, dp.cellProbability f * dp.condValue {a₁, a₂} f = 1 := by
    simp_rw [hcpcv_max]; exact hmax_fine
  -- Assemble: `qU coarse − qU fine = 1 > 0`, contradicting `hyp : qU coarse ≤ qU fine`.
  rw [hqu_eq coarse, hqu_eq fine, hX_coarse, hX_fine, hcpP_coarse, hcpP_fine] at hyp
  linarith

end VanRooy2003
