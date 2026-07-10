import Linglib.Semantics.Questions.Basic
import Linglib.Semantics.Questions.DecisionTheory
import Linglib.Semantics.Questions.Entailment

/-!
# [van-rooy-2003]: Questioning to Resolve Decision Problems
[groenendijk-stokhof-1984] [karttunen-1977] [ginzburg-1995] [merin-1999]
[blackwell-1953]

Single-paper formalisation of [van-rooy-2003], "Questioning to
Resolve Decision Problems", *Linguistics and Philosophy* 26.6:
727–763. The paper grounds question semantics in Bayesian decision
theory: questions are evaluated by how their answers affect the
optimal action in the questioner's decision problem.

## Substrate identification

The decision-theoretic machinery — `EU`, `UV`, `VSI`, `DecisionProblem`
— is already in `Semantics/Questions/DecisionTheory.lean`. Van Rooy's
notation maps to the substrate as:

| [van-rooy-2003]                             | substrate                                  |
|--------------------------------------------------|--------------------------------------------|
| `EU(a) = ∑_w P(w) · U(a, w)` (p. 733)            | `Core.DecisionTheory.expectedUtility`      |
| `UV(Choose now) = max_a EU(a)` (p. 734)          | `Core.DecisionTheory.dpValue`              |
| `EU(a, C) = ∑_w P_C(w) · U(a, w)` (p. 735)       | `Core.DecisionTheory.conditionalEU`        |
| `UV(Learn C, choose later) = max_a EU(a, C)`     | `Core.DecisionTheory.valueAfterLearning`   |
| `UV(C) = UV(L C, c later) − UV(C now)` (p. 735)  | `Core.DecisionTheory.utilityValue`         |
| `UV*(C) = VSI(C)` ≥ 0 (p. 735)                   | `Core.DecisionTheory.valueSampleInfo`      |
| `EUV(Q) = ∑_q P(q) · UV(q)` (p. 742)             | `Core.DecisionTheory.questionUtility`      |
| `Q ⊑ Q'`  (every Q-alt ⊆ some Q'-alt) (p. 741)   | `Question.Entails`                 |
| `C resolves DP` (p. 736)                         | `Core.DecisionTheory.IsResolved`           |

## What this file proves

* **§3.1 Action-induced partition `A*`** (p. 736-737):
  `optimalityCell dp acts a` and `actionPartition`.
* **§3.1 *C* resolves DP** (p. 736): the substrate's
  `Core.DecisionTheory.IsResolved dp acts C` — some action weakly
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
  `Core.DecisionTheory.questionUtility_mono_of_refines`). The `⟸` direction is the
  [blackwell-1953] *converse*, `ProbabilityTheory.isGarblingOf_of_blackwellDominates`
  (finite, kernel-level — now proved; the partition-cell bridge to `questionUtility`
  is the remaining Layer-2 work, so this direction is still `sorry`).
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

open Core Core.DecisionTheory Question

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
def optimalityCell (dp : DecisionProblem W A) (acts : Set A) (a : A) : Set W :=
  {w | ∀ b ∈ acts, b ≠ a → dp.utility w a > dp.utility w b}

/-- The **action-induced partition** `A*`: the set of optimality
    cells. [van-rooy-2003] p. 736-737. -/
def actionPartition (dp : DecisionProblem W A) (acts : Set A) : Set (Set W) :=
  optimalityCell dp acts '' acts

/-- The optimality cells are pairwise disjoint: each world lies in at
    most one cell. (Page 737: "the set of propositions A* does in
    general not partition the state space, but it does when for each
    world `w` there is always exactly one action a ∈ A such that
    ∀b ∈ A−{a} : U(a,w) > U(b,w)".) -/
theorem optimalityCell_pairwise_disjoint
    (dp : DecisionProblem W A) (acts : Set A)
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

This is exactly `Core.DecisionTheory.IsResolved dp acts C`. We do not
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
    (Q : Question W) (dp : DecisionProblem W A) (acts : Set A) : Prop :=
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
    {Q : Question W} {dp : DecisionProblem W A} {acts : Set A}
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
    {Q : Question W} {dp : DecisionProblem W A} {acts : Set A}
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
    with `EUV = EVSI` available as `euv_eq_evsi`). The result here is a
    one-directional, prior-free Prop transfer over the *dual* condition
    `CoversAltsOf`: on a general inquisitive (non-partition) `Question W`,
    `Entails` (P-alts ⊆ Q-alts) does not transfer the qualitative
    witness, but its dual does. On partition questions the two coincide,
    recovering [van-rooy-2003]'s partition-based argument.

    For the *quantitative* §4.1 Fact (p. 743), the EUV-monotonicity ("only if")
    direction is now `Core.DecisionTheory.questionUtility_split_ge` (a finer
    partition has `EUV ≥` the coarser one, for every decision problem). The
    remaining gap to the full `Entails`-level *iff* is (i) a
    `Question W → Finset (Finset W)` finite-alternatives partition-cell adapter, and
    (ii) the [blackwell-1953] converse
    `ProbabilityTheory.isGarblingOf_of_blackwellDominates`. -/
theorem decisionRelevance_preserved_under_cover
    {Q Q' : Question W} (hCover : CoversAltsOf Q Q')
    {dp : DecisionProblem W A} {acts : Set A}
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
`Finset (Finset W)` that `Core.DecisionTheory.questionUtility` consumes. There, van Rooy's
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
containing coarse cell — and `Core.DecisionTheory.questionUtility_mono_of_refines` concludes.

`hfine_cover` and the disjointness hypotheses encode that `fine`, `coarse` are genuine
[groenendijk-stokhof-1984] partitions of the world set. -/
theorem blackwell_euv_fact_forward [Fintype W] [DecidableEq W] [DecidableEq A]
    {fine coarse : Finset (Finset W)}
    (hcoarse_disj : ∀ c₁ ∈ coarse, ∀ c₂ ∈ coarse, c₁ ≠ c₂ → Disjoint c₁ c₂)
    (hfine_disj : ∀ f₁ ∈ fine, ∀ f₂ ∈ fine, f₁ ≠ f₂ → Disjoint f₁ f₂)
    (hfine_cover : ∀ w : W, ∃ f ∈ fine, w ∈ f)
    (href : ∀ f ∈ fine, ∃ c ∈ coarse, f ⊆ c)
    (dp : DecisionProblem W A) (acts : Finset A) (hprior : ∀ w, 0 ≤ dp.prior w) :
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

The `⟹` direction is `blackwell_euv_fact_forward` (the data-processing inequality). The
`⟸` direction (EUV-dominance across all decision problems forces refinement) follows from
the now-proved [blackwell-1953] *converse*,
`ProbabilityTheory.isGarblingOf_of_blackwellDominates`, once the partition-cell bridge is in
place: the deterministic experiments of `fine`/`coarse` as Markov kernels, deterministic
garbling ↔ refinement, and `questionUtility ↔ bayesRisk`. That bridge (Layer 2) is the
remaining work; this direction stays `sorry` until it lands. -/
theorem blackwell_euv_fact [Fintype W] [DecidableEq W] [DecidableEq A]
    {fine coarse : Finset (Finset W)}
    (hfine_disj : ∀ f₁ ∈ fine, ∀ f₂ ∈ fine, f₁ ≠ f₂ → Disjoint f₁ f₂)
    (hcoarse_disj : ∀ c₁ ∈ coarse, ∀ c₂ ∈ coarse, c₁ ≠ c₂ → Disjoint c₁ c₂)
    (hfine_cover : ∀ w : W, ∃ f ∈ fine, w ∈ f) :
    (∀ f ∈ fine, ∃ c ∈ coarse, f ⊆ c) ↔
      (∀ (dp : DecisionProblem W A) (acts : Finset A), (∀ w, 0 ≤ dp.prior w) →
        questionUtility dp acts coarse ≤ questionUtility dp acts fine) := by
  refine ⟨fun href dp acts hprior =>
    blackwell_euv_fact_forward hcoarse_disj hfine_disj hfine_cover href dp acts hprior, ?_⟩
  -- ⟸ : EUV-dominance across all decision problems forces refinement.
  -- The finite [blackwell-1953] converse at the partition-cell level
  -- (`ProbabilityTheory.isGarblingOf_of_blackwellDominates`), the deep direction.
  -- TODO: instantiate the Blackwell converse with the deterministic (partition-cell)
  -- experiments of `fine`/`coarse`; when refinement fails, the separating decision problem
  -- reverses the EUV ordering.
  sorry

end VanRooy2003
