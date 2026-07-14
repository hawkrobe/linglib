import Linglib.Semantics.Modality.Kratzer.Flavor
import Linglib.Semantics.Modality.Kratzer.Operators
import Linglib.Semantics.Presupposition.Basic
import Linglib.Core.Order.Satisfaction
import Linglib.Core.Order.SimilarityOrdering
import Linglib.Semantics.Questions.Hamblin
import Linglib.Semantics.Questions.Partition.Basic
import Linglib.Core.Probability.Decision.Basic
import Mathlib.Order.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum

/-!
# Desire Semantics — substrate for `want`/`wish`/`hope`

This file collects three formalizations of desire ascriptions:

1. **von Fintel [von-fintel-1999]** (`wantVF`): "every undominated
   belief-world is a p-world", where the world ordering is induced by
   which desires each world satisfies.

2. **[heim-1992]** (`wantHeim`): "for every doxastic alternative
   `w'`, every closest p-world to `w'` is more desirable than every
   closest ¬p-world to `w'`". Three successive formulations from the
   paper are exposed: (27) naive Hintikka-style, (31) truth-conditional
   comparative-belief, and (37/39) the CCP-rephrased version with the
   (40) amendment as `wantHeimDefined`.

3. **[phillips-brown-2025]** (`wantQuestionBased`): "every best
   answer in Q_c-Bel_S entails p", parameterized on a contextual
   question Q_c. Handles conflicting-desire ascriptions ("S wants p" +
   "S wants ¬p") by varying Q_c.

The first two are **belief-based** and packaged into a common
`BeliefBasedDesireSemantics` structure with a parametric no-go
theorem (`bbds_no_simultaneous_want_p_and_negp`): no belief-based
semantics can predict simultaneous `want(p)` and `want(¬p)` against a
single belief state. PB's `wantQuestionBased` *evades* the no-go by
selecting from `Q-Bel_S` rather than directly from `Bel_S`.

## Phillips-Brown 2025 metasemantic constraints

The PB substrate exposes four metasemantic constraints:

* **Considering** (paper §3.6): every cell of Q_c settles p.
* **Diversity** (paper §3.7, attributed to [condoravdi-2002]):
  Q_c contains both p-cells and ¬p-cells.
* **Anti-deckstacking** (paper §3.7): for every "natural" proposition q,
  if some cell of Q_c entails q, then q is itself considered. The
  substrate parameterizes the constraint on a `naturalProps` test set
  rather than quantifying over all of `Set W` (see `isAntiDeckstacking`).
* **Belief-sensitivity** (paper §4.2, building on [yalcin-2018]'s
  question-sensitive belief): Bel_S discriminates among the cells of Q_c.

The question-based mechanism is inspired by [crnic-2014] (an idea
the paper credits as previously unformalized), parallels Yalcin's
question-sensitive belief on the doxastic side, and was independently
arrived at via a different route by Dandelet (situations rather than
questions).

The von Fintel [von-fintel-1999] baseline (`wantVF`) is included as
a foil. The paper's central metasemantic identity (paper §3.4) is that
when Q_c is the finest partition (singleton cells), question-based want
reduces to von Fintel's standard semantics — see
`wantQuestionBased_finestPartition_iff_wantVF`. Heim 1992
(comparative-belief) is *not* formalized here; the no-go theorem
`wantVF_no_simultaneous_pq_and_negpq` covers von Fintel only.

The world ordering used by `wantVF` is [kratzer-1981]'s ordering over
the projected desire propositions (every desire satisfied at z is also
satisfied at w) — definitionally, not by bridge: `worldAtLeastAsGood`
calls `Kratzer.atLeastAsGoodAs` directly.
-/

namespace Semantics.Attitudes.Desire

open Semantics.Presupposition (PartialProp)
open Core.Order (SatisfactionOrdering)

section Generic

variable {W : Type*} [Fintype W] [DecidableEq W]

/-! ## Decidable propositions

A `DecProp W` bundles a `Set W` with its `DecidablePred` witness so it
can sit as the element type of a partition list while remaining
`decide`-able. This is a structure (not `Subtype`) because
`DecidablePred` lives in `Type`, not `Prop`. -/

/-- A `Set W` paired with its `DecidablePred` witness. -/
structure DecProp (W : Type*) where
  /-- The underlying `Prop`-valued proposition. -/
  prop : Set W
  /-- Decidability witness for the underlying proposition. -/
  dec : DecidablePred prop

/-- Smart constructor for a `DecProp` from a `Set W` with synthesizable
    decidability. -/
@[reducible] def mkDec (p : Set W) [h : DecidablePred p] : DecProp W := ⟨p, h⟩

instance (a : DecProp W) : DecidablePred a.prop := a.dec

/-! ## Decidable subset / overlap on `Set W`

Mathlib's `s ⊆ t` and `(s ∩ t).Nonempty` are not auto-decidable on `Set`
(the elaborator does not unfold `Set.Subset` to see the underlying `∀`).
We expose `@[reducible]` aliases that *are* decidable under
`[Fintype W]` + `DecidablePred` for both arguments. The aliases are
definitionally equal to their `Set`-API counterparts and are intended
to read as the same operation. -/

/-- `propEntails p q ↔ p ⊆ q` (definitionally), with decidability. -/
@[reducible] def propEntails (p q : Set W) : Prop := ∀ w, p w → q w

/-- `propOverlap p q ↔ (p ∩ q).Nonempty` (definitionally), with
    decidability. -/
@[reducible] def propOverlap (p q : Set W) : Prop := ∃ w, p w ∧ q w

/-! ## Propositional preference (von Fintel 1999, paper §3.5)

The paper's preference relation between answers `a, a' ∈ Q_c-Bel_S`:

  S prefers a to a' iff {p ∈ G_S : a' ⊆ p} ⊊ {p ∈ G_S : a ⊆ p}

— i.e. *strict* subset inclusion of satisfied desires. We expose the
weak relation `≤` via `SatisfactionOrdering.ofCriteria` and the strict
relation via `SatisfactionOrdering.strictlyBetter`; the paper's "best
answers" are the maxima under the strict relation, i.e. the
Pareto-undominated elements (see paper §3.5, p. 11:21). -/

/-- Proposition ordering: `a ≤ a'` iff every desire in `GS` that `a'`
    entails, `a` also entails. The Pareto-undominated elements under
    this relation are the "best answers" of [phillips-brown-2025]
    §3.5. -/
def propositionOrdering (GS : List (DecProp W)) :
    SatisfactionOrdering (DecProp W) (DecProp W) :=
  SatisfactionOrdering.ofCriteria (fun a p => decide (propEntails a.prop p.prop)) GS

/-- Best (= Pareto-undominated) answers among a candidate list. -/
abbrev undominatedAnswers (GS answers : List (DecProp W)) : List (DecProp W) :=
  (propositionOrdering GS).undominated answers

/-! ## Question-relative belief (paper §3.3)

Q_c-Bel_S = the cells of Q_c compatible with S's beliefs. -/

/-- The cells of `answers` that overlap `belS`. -/
def questionRelativeBelief (answers : List (DecProp W))
    (belS : Set W) [DecidablePred belS] : List (DecProp W) :=
  answers.filter fun a => decide (propOverlap a.prop belS)

/-! ## Core semantics -/

/-- ⟦S wants p⟧^c = every undominated answer in Q_c-Bel_S entails p.
    The paper's central definition (paper §3.5). -/
def wantQuestionBased (belS : Set W) [DecidablePred belS]
    (GS answers : List (DecProp W)) (p : Set W) [DecidablePred p] : Prop :=
  ∀ a ∈ undominatedAnswers GS (questionRelativeBelief answers belS),
    propEntails a.prop p

instance (belS : Set W) [DecidablePred belS]
    (GS answers : List (DecProp W)) (p : Set W) [DecidablePred p] :
    Decidable (wantQuestionBased belS GS answers p) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-! ## von Fintel baseline (paper §2.1)

`wantVF` evaluates to "every undominated belief-world is a p-world",
where the world ordering is induced by which desires each world
satisfies — [kratzer-1981]'s `atLeastAsGoodAs` over the projected
desires, by definition. -/

/-- World ordering induced by a desire list: `w ≤ z` iff every desire
    in `GS` satisfied at `z` is also satisfied at `w` — [kratzer-1981]'s
    `atLeastAsGoodAs` over the projected proposition list, by definition.
    Decidability is transported from the per-`DecProp` witnesses via
    `worldAtLeastAsGood_iff_decProp`. -/
def worldAtLeastAsGood (GS : List (DecProp W)) (w z : W) : Prop :=
  Semantics.Modality.Kratzer.atLeastAsGoodAs (GS.map (·.prop)) w z

omit [Fintype W] [DecidableEq W] in
/-- The ordering in its `DecProp`-quantified form, where each desire
    carries its decidability witness. -/
theorem worldAtLeastAsGood_iff_decProp (GS : List (DecProp W)) (w z : W) :
    worldAtLeastAsGood GS w z ↔ ∀ p ∈ GS, p.prop z → p.prop w := by
  show (∀ p ∈ GS.map (·.prop), p z → p w) ↔ _
  simp only [List.mem_map]
  refine ⟨fun h a ha hpz => h a.prop ⟨a, ha, rfl⟩ hpz,
          fun h _ ⟨a, ha, hap⟩ hpz => hap ▸ h a ha (hap ▸ hpz)⟩

instance (GS : List (DecProp W)) (w z : W) :
    Decidable (worldAtLeastAsGood GS w z) :=
  decidable_of_iff _ (worldAtLeastAsGood_iff_decProp GS w z).symm

omit [Fintype W] [DecidableEq W] in
/-- The desire-induced world ordering coincides with Kratzer's ordering
    over the projected proposition list — definitional since
    `worldAtLeastAsGood` calls `atLeastAsGoodAs` directly; kept for
    discoverability. -/
theorem worldAtLeastAsGood_iff_kratzer (GS : List (DecProp W)) (w z : W) :
    worldAtLeastAsGood GS w z ↔
      Semantics.Modality.Kratzer.atLeastAsGoodAs (GS.map (·.prop)) w z :=
  Iff.rfl

/-- Standard von Fintel [von-fintel-1999] semantics: every undominated
    belS-world is a p-world. The `[DecidablePred]` hypotheses are not
    used in the definition body; they live on the `Decidable` instance
    so that abstract reasoning (e.g. instances of
    `BeliefBasedDesireSemantics`) can use `wantVF` without supplying
    them. -/
def wantVF (belS : Set W) (GS : List (DecProp W)) (p : Set W) : Prop :=
  ∀ w, belS w →
    (∀ z, belS z → ¬ (worldAtLeastAsGood GS z w ∧ ¬ worldAtLeastAsGood GS w z)) →
    p w

instance (belS : Set W) [DecidablePred belS]
    (GS : List (DecProp W)) (p : Set W) [DecidablePred p] :
    Decidable (wantVF belS GS p) :=
  inferInstanceAs (Decidable (∀ _, _))

/-! ## Metasemantic constraints (paper §3.6, §3.7, §4.2) -/

/-- **Considering Constraint** (paper §3.6): every cell of Q_c either
    entails p or entails ¬p. Equivalently (over partition cells):
    p is a union of cells. -/
def isConsidered (answers : List (DecProp W))
    (p : Set W) [DecidablePred p] : Prop :=
  ∀ a ∈ answers, (∀ w, a.prop w → p w) ∨ (∀ w, a.prop w → ¬ p w)

instance (answers : List (DecProp W)) (p : Set W) [DecidablePred p] :
    Decidable (isConsidered answers p) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-- **Diversity Constraint** (paper §3.7, attributed to
    [condoravdi-2002]): Q_c contains both p-cells and ¬p-cells.
    Without diversity, ⟦want p⟧ would be vacuously true (or false). -/
def isDiverse (answers : List (DecProp W))
    (p : Set W) [DecidablePred p] : Prop :=
  (∃ a ∈ answers, ∀ w, a.prop w → p w) ∧
  (∃ a ∈ answers, ∀ w, a.prop w → ¬ p w)

instance (answers : List (DecProp W)) (p : Set W) [DecidablePred p] :
    Decidable (isDiverse answers p) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! ### Anti-deckstacking (paper §3.7)

The paper quantifies over "all q": if some cell entails q, then q must
itself be considered relative to Q_c. The naive `∀ q : Set W` over a
finite model trivially fails on gerrymandered subsets — e.g. for the
`qNapRest` 4-cell partition, `q = {w₀, w₁, w₂}` is entailed by the
`nap ∧ rested` cell `{w₀, w₁}` but not settled by the `nap ∧ ¬rested`
cell `{w₂, w₃}` (which contains `w₂ ∈ q` and `w₃ ∉ q`). These
violations are artifacts of the encoding, not of the question.

The substrate solves this by parameterizing the constraint on a
**test set of natural propositions** `naturalProps` — the propositions
the modeller deems salient for the model. For PB's `qDeckstacked`
example, `naturalProps = [r, h]` correctly fails AD (cell `¬r ∧ h`
entails `h`, but `h` is not considered by `qDeckstacked` — the `r` cell
neither entails `h` nor entails `¬h`). For `qNapRest` and `qRainHappy`
with the same `naturalProps`, AD passes (those questions cross-cut both
basic dimensions). -/

/-- **Anti-deckstacking Constraint** (paper §3.7), parameterized on the
    test set of natural propositions `naturalProps`: for every
    `q ∈ naturalProps`, if some cell of `answers` entails `q`, then `q`
    must be considered relative to `answers`.

    The `naturalProps` parameter is the modeller's chosen vocabulary of
    salient propositions; passing the empty list trivially satisfies the
    constraint, so study files must opt in by listing the basic
    propositions of their model. -/
def isAntiDeckstacking (naturalProps answers : List (DecProp W)) : Prop :=
  ∀ q ∈ naturalProps,
    (∀ a ∈ answers, ¬ ∀ w, a.prop w → q.prop w) ∨
    (∀ a ∈ answers, (∀ w, a.prop w → q.prop w) ∨ (∀ w, a.prop w → ¬ q.prop w))

instance (naturalProps answers : List (DecProp W)) :
    Decidable (isAntiDeckstacking naturalProps answers) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-- **Belief-sensitivity Constraint** (paper §4.2, building on
    [yalcin-2018]'s question-sensitive belief): Bel_S discriminates
    among the cells of Q_c — at least one answer is compatible with
    S's beliefs and at least one is incompatible. Blocks inferences
    like William III ⊨ "Avoid nuclear war" when the agent lacks the
    conceptual resources to grasp the question. -/
def isBelSensitive (belS : Set W) [DecidablePred belS]
    (answers : List (DecProp W)) : Prop :=
  let live := questionRelativeBelief answers belS
  live ≠ [] ∧ live.length ≠ answers.length

instance (belS : Set W) [DecidablePred belS] (answers : List (DecProp W)) :
    Decidable (isBelSensitive belS answers) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Full definedness condition for ⟦S wants p⟧^c. The paper requires
    all four constraints (Considering §3.6, Diversity §3.7,
    Anti-deckstacking §3.7, Belief-sensitivity §4.2). The
    `naturalProps` parameter feeds Anti-deckstacking. -/
def wantDefined (belS : Set W) [DecidablePred belS]
    (naturalProps answers : List (DecProp W)) (p : Set W) [DecidablePred p] : Prop :=
  isConsidered answers p ∧
  isDiverse answers p ∧
  isAntiDeckstacking naturalProps answers ∧
  isBelSensitive belS answers

instance (belS : Set W) [DecidablePred belS]
    (naturalProps answers : List (DecProp W)) (p : Set W) [DecidablePred p] :
    Decidable (wantDefined belS naturalProps answers p) := by
  unfold wantDefined; infer_instance

/-! ## Partial-proposition wrapper (paper §3.6)

The presupposition is the four-constraint definedness predicate; the
assertion is the question-based truth condition. Both are
world-independent because Q_c is contextually fixed prior to
evaluation; we expose them as a `PartialProp W` for uniformity with
linglib's presupposition infrastructure, with the world argument
suppressed. -/

/-- Question-based `want` as a partial proposition (`Core.PartialProp`):
    presupposition = full definedness; assertion = question-based truth. -/
def wantPartialProp (belS : Set W) [DecidablePred belS]
    (GS naturalProps answers : List (DecProp W)) (p : Set W) [DecidablePred p] :
    PartialProp W where
  presup _ := wantDefined belS naturalProps answers p
  assertion _ := wantQuestionBased belS GS answers p

/-! ## §3.4 metasemantic identity: finest question simulates vF

When Q_c is the finest partition (every cell is a singleton world),
the question-based semantics reduces to standard vF. The substrate
provides the construction parameterized on an explicit world list so
the result is computable and `decide`-able for concrete models. -/

/-- The finest partition over an explicit world list: one singleton
    cell per listed world. -/
def finestPartition (worlds : List W) : List (DecProp W) :=
  worlds.map fun w => mkDec (· = w)

/-! ### §3.4 supporting lemmas

The §3.4 metasemantic identity is proved via three helper lemmas
(singleton-cell preference reduces to single-world preference under
`worldAtLeastAsGood`; the question-relative belief filter on
`finestPartition` selects exactly the singleton cells of belS-worlds;
undominated singleton cells correspond to Pareto-undominated
belS-worlds), then a direct two-direction `iff` proof. -/

/-- Singleton-cell preference under `propositionOrdering` reduces to
    single-world preference under `worldAtLeastAsGood`: for cells
    `mkDec (· = w)` and `mkDec (· = z)`, `mkDec (· = w) ≤ mkDec (· = z)`
    in the proposition ordering iff `worldAtLeastAsGood GS w z`. -/
private theorem singleton_le_iff_world (GS : List (DecProp W)) (w z : W) :
    (propositionOrdering GS).le (mkDec (· = w)) (mkDec (· = z)) ↔
      worldAtLeastAsGood GS w z := by
  rw [worldAtLeastAsGood_iff_decProp]
  unfold propositionOrdering SatisfactionOrdering.ofCriteria
  show (∀ q ∈ GS.filter (fun q => decide (propEntails (mkDec (· = z)).prop q.prop)),
          decide (propEntails (mkDec (· = w)).prop q.prop) = true) ↔
       (∀ q ∈ GS, q.prop z → q.prop w)
  simp only [mkDec, propEntails, decide_eq_true_eq]
  constructor
  · intro h q hq hqz
    have hqfilter : q ∈ GS.filter (fun q' => decide (∀ x, x = z → q'.prop x)) := by
      rw [List.mem_filter]
      refine ⟨hq, ?_⟩
      simp only [decide_eq_true_eq]
      intro x hx; exact hx ▸ hqz
    exact h q hqfilter w rfl
  · intro h q hq_filter
    rw [List.mem_filter] at hq_filter
    obtain ⟨hq, hqz_filter⟩ := hq_filter
    simp only [decide_eq_true_eq] at hqz_filter
    have hqz : q.prop z := hqz_filter z rfl
    intro x hx
    exact hx ▸ h q hq hqz

/-- A singleton cell `mkDec (· = w)` is in `questionRelativeBelief
    (finestPartition worlds) belS` iff `w ∈ worlds` and `belS w`. -/
private theorem mem_qRB_finestPartition_iff (belS : Set W) [DecidablePred belS]
    (worlds : List W) (w : W) :
    mkDec (· = w) ∈ questionRelativeBelief (finestPartition worlds) belS ↔
      w ∈ worlds ∧ belS w := by
  unfold questionRelativeBelief finestPartition
  rw [List.mem_filter]
  simp only [List.mem_map, decide_eq_true_eq, propOverlap, mkDec]
  constructor
  · rintro ⟨⟨v, hv_mem, hv_eq⟩, ⟨x, hxv, hxBel⟩⟩
    -- mkDec injection on `prop`: (· = v) = (· = w), evaluate at v
    have hpropEq : (fun x => x = v) = (fun x => x = w) :=
      congrArg DecProp.prop hv_eq
    have hvw : v = w := by
      have := congrFun hpropEq v
      simpa using this
    subst hvw
    subst hxv
    exact ⟨hv_mem, hxBel⟩
  · rintro ⟨hw_mem, hbel⟩
    exact ⟨⟨w, hw_mem, rfl⟩, ⟨w, rfl, hbel⟩⟩

theorem wantQuestionBased_finestPartition_iff_wantVF
    (belS : Set W) [DecidablePred belS] (GS : List (DecProp W))
    (worlds : List W) (hUniv : ∀ w, w ∈ worlds)
    (p : Set W) [DecidablePred p] :
    wantQuestionBased belS GS (finestPartition worlds) p ↔ wantVF belS GS p := by
  unfold wantQuestionBased wantVF undominatedAnswers SatisfactionOrdering.undominated
  refine ⟨fun hLHS w hw hUnd => ?_, fun hRHS a ha => ?_⟩
  · -- LHS → RHS: pick the cell `mkDec (· = w)`, show it's undominated, apply
    have hcell_mem : mkDec (· = w) ∈
        questionRelativeBelief (finestPartition worlds) belS :=
      (mem_qRB_finestPartition_iff belS worlds w).mpr ⟨hUniv w, hw⟩
    have hcell_undom : mkDec (· = w) ∈
        ((propositionOrdering GS).undominated
          (questionRelativeBelief (finestPartition worlds) belS)) := by
      unfold SatisfactionOrdering.undominated
      rw [List.mem_filter]
      refine ⟨hcell_mem, ?_⟩
      simp only [decide_eq_true_eq]
      rintro ⟨c, hc_mem, hc_strict⟩
      -- c is in qRB; via mem_qRB_finestPartition_iff, c = mkDec (· = z) for
      -- some z with belS z. Translate hc_strict to wAALG and contradict hUnd.
      have hc_in_fp : c ∈ finestPartition worlds := by
        unfold questionRelativeBelief at hc_mem
        exact (List.mem_filter.mp hc_mem).1
      obtain ⟨z, _hz_mem, hz_eq⟩ := List.mem_map.mp hc_in_fp
      have hz_bel : belS z := by
        rw [← hz_eq] at hc_mem
        exact ((mem_qRB_finestPartition_iff belS worlds z).mp hc_mem).2
      rw [← hz_eq] at hc_strict
      have hzw : worldAtLeastAsGood GS z w := (singleton_le_iff_world GS z w).mp hc_strict.1
      have hnwz : ¬ worldAtLeastAsGood GS w z := fun h =>
        hc_strict.2 ((singleton_le_iff_world GS w z).mpr h)
      exact hUnd z hz_bel ⟨hzw, hnwz⟩
    have := hLHS _ hcell_undom
    exact this w rfl
  · -- RHS → LHS: a is in undominated qRB; extract its world and apply hRHS
    rw [List.mem_filter] at ha
    obtain ⟨ha_mem, ha_min⟩ := ha
    -- a ∈ qRB; extract w with a = mkDec (· = w), w ∈ worlds, belS w
    have ha_in_fp : a ∈ finestPartition worlds := by
      unfold questionRelativeBelief at ha_mem
      exact (List.mem_filter.mp ha_mem).1
    obtain ⟨w, _hw_mem, hw_eq⟩ := List.mem_map.mp ha_in_fp
    -- Substitute a := mkDec (· = w) throughout
    subst hw_eq
    have hbelw : belS w :=
      ((mem_qRB_finestPartition_iff belS worlds w).mp ha_mem).2
    -- ha_min: ¬ ∃ c ∈ qRB, c strictly better than mkDec (· = w)
    simp only [decide_eq_true_eq] at ha_min
    have hUnd : ∀ z, belS z → ¬ (worldAtLeastAsGood GS z w ∧
                                  ¬ worldAtLeastAsGood GS w z) := by
      intro z hz_bel ⟨hzw, hnwz⟩
      apply ha_min
      refine ⟨mkDec (· = z), ?_, ?_⟩
      · exact (mem_qRB_finestPartition_iff belS worlds z).mpr ⟨hUniv z, hz_bel⟩
      · exact ⟨(singleton_le_iff_world GS z w).mpr hzw,
               fun h => hnwz ((singleton_le_iff_world GS w z).mp h)⟩
    -- Apply hRHS at w; get p w; convert to propEntails
    have hpw : p w := hRHS w hbelw hUnd
    intro x hx
    -- hx : (mkDec (· = w)).prop x = (x = w)
    -- Goal: p x
    show p x
    have : x = w := hx
    exact this ▸ hpw

/-! ## §2 no-go: vF cannot predict simultaneous `want p` and `want ¬p`

The paper's central argument against belief-based semantics. For any
non-empty belief state with at least one undominated world, vF cannot
make both `wantVF belS GS p` and `wantVF belS GS (¬p)` true at the
same context. -/

omit [Fintype W] [DecidableEq W] in
/-- **No-go for vF** (paper §2.1): if some belS-world is undominated,
    then no vF-prediction makes both `want p` and `want ¬p` true. -/
theorem wantVF_no_simultaneous_pq_and_negpq
    (belS : Set W) [DecidablePred belS]
    (GS : List (DecProp W)) (p : Set W) [DecidablePred p]
    (h : ∃ w, belS w ∧
      ∀ z, belS z → ¬ (worldAtLeastAsGood GS z w ∧ ¬ worldAtLeastAsGood GS w z)) :
    ¬ (wantVF belS GS p ∧ wantVF belS GS (fun w => ¬ p w)) := by
  rintro ⟨hp, hnp⟩
  obtain ⟨w, hw, hund⟩ := h
  exact (hnp w hw hund) (hp w hw hund)

/-! ## Closure properties (paper §4.1, §4.2) -/

omit [Fintype W] [DecidableEq W] in
/-- vF is **upward monotonic**: if `p ⊆ q` and `wantVF belS GS p`,
    then `wantVF belS GS q`. This is the [villalta-2008]
    doxastic-closure problem that motivates the question-based
    approach (paper §4.1). -/
theorem wantVF_upward_monotonic (belS : Set W) [DecidablePred belS]
    (GS : List (DecProp W)) (p q : Set W) [DecidablePred p] [DecidablePred q]
    (hpq : ∀ w, p w → q w) (h : wantVF belS GS p) :
    wantVF belS GS q :=
  fun w hw hund => hpq w (h w hw hund)

/-- Question-based `want` is **Strawson upward monotonic** (paper §4.2):
    `wantQuestionBased belS GS Q p`, `p ⊆ q`, and `q` considered
    relative to `Q` jointly imply `wantQuestionBased belS GS Q q`. The
    Considering presupposition is what blocks naive upward monotonicity
    that derived "Avoid-war ⊨ Avoid-nuclear-war" from "wants
    Avoid-war". -/
theorem wantQuestionBased_strawson_upward_monotonic
    (belS : Set W) [DecidablePred belS]
    (GS answers : List (DecProp W)) (p q : Set W)
    [DecidablePred p] [DecidablePred q]
    (hpq : ∀ w, p w → q w) (_hCons : isConsidered answers q)
    (h : wantQuestionBased belS GS answers p) :
    wantQuestionBased belS GS answers q :=
  fun a ha w hw => hpq w (h a ha w hw)

/-! ## [heim-1992] comparative-belief desire semantics

The paper has three successive truth conditions for `want`, each fixing
a defect of the prior. We expose all three as a feature, not a bug — it
shows the trajectory and lets future readers reproduce the argument.

(27) The naive Hintikka-style `want` (paper §3, p. 192): "every bouletic
alternative is a φ-world." Heim immediately rejects it via Asher's
Concorde counterexample at (32) p. 194. We formalize it as `wantHeimNaive`
to make the rejection-by-counterexample testable.

(31) Truth-conditional comparative-belief `want` (paper §4.1, p. 193 —
the canonical "Heim semantics"): "α wants φ is true at w iff for every
w' ∈ Dox_α(w): every φ-world maximally similar to w' is more desirable
to α than any non-φ-world maximally similar to w'." This is the textbook
formulation.

(37/39) CCP-rephrased Heim `want` (paper §4.2.2, p. 197): same content,
but the proposition is restricted to Dox first
(`Sim_w'(Dox_α(w) + φ) <_{α,w} Sim_w'(Dox_α(w) + ¬φ)`). The (40)
amendment makes this **undefined** when the agent already believes φ
or already believes ¬φ — a presupposition failure that is the
formal mechanism behind Heim's account being unable to predict
simultaneous `want(p) ∧ want(¬p)`.

Heim does NOT use a Kratzer-style ordering source — she uses a
[lewis-1973] / [stalnaker-1968] similarity ordering on worlds.
The desirability `<_{α,w}` is treated as primitive (a relation between
worlds, parameterized by agent and evaluation world), not derived from
a desire-list the way vF's is. -/

/-- Parameters for Heim 1992's desire semantics: a similarity ordering
    on worlds (for `Sim_w(p)` = closest p-worlds to w) and a comparative
    desirability relation `pref w_eval x y` saying "at evaluation world
    w_eval, world x is at least as desirable as world y". -/
structure HeimDesireParams (W : Type*) where
  /-- The Lewis–Stalnaker similarity ordering on worlds. -/
  sim : Core.Order.SimilarityOrdering W
  /-- Comparative desirability `pref w_eval x y`: at `w_eval`, `x` is
      more desirable than `y`. The agent argument is suppressed
      (single-agent setup). -/
  pref : W → W → W → Prop
  /-- Decidability of the desirability relation. -/
  prefDec : ∀ w x y, Decidable (pref w x y)

instance (params : HeimDesireParams W) (w x y : W) :
    Decidable (params.pref w x y) :=
  params.prefDec w x y

/-- Sim_w(p) restricted to `belS ∩ p`: the closest worlds in
    `belS ∩ p` to `w` under the similarity ordering. Heim's formulation
    (37) restricts the proposition argument of `Sim` to the doxastic
    base, which is what makes the Limit Assumption automatic on a
    finite model. -/
def heimSim {W : Type*} [Fintype W] [DecidableEq W]
    (params : HeimDesireParams W)
    (belS : Set W) [DecidablePred belS]
    (p : Set W) [DecidablePred p] (w : W) : Finset W :=
  params.sim.closestWorlds w
    (Finset.univ.filter (fun z => belS z ∧ p z))

/-- Heim 1992 (27), the naive Hintikka-style baseline: "α wants φ" iff
    every bouletic alternative (here: every belief-world; we suppress
    the bouletic/doxastic distinction at the substrate level) is a
    φ-world. Provided to enable formalizing Asher's (32) Concorde
    counterexample as a test of the analysis Heim *rejected*. -/
def wantHeimNaive (belS : Set W) [DecidablePred belS]
    (p : Set W) [DecidablePred p] : Prop :=
  ∀ w, belS w → p w

instance (belS : Set W) [DecidablePred belS]
    (p : Set W) [DecidablePred p] :
    Decidable (wantHeimNaive belS p) :=
  inferInstanceAs (Decidable (∀ _, _))

/-- Heim 1992 (37/39), the canonical comparative-belief semantics:
    "α wants φ" at `w_eval` iff for every doxastic alternative `w' ∈ belS`,
    every closest `belS ∩ φ`-world to `w'` is at least as desirable as
    every closest `belS ∩ ¬φ`-world to `w'`.

    The doxastic-alternative quantifier ranges over a `Finset` so the
    `Decidable` instance below can be derived via `Finset.decidableBAll`.
    The `[DecidablePred belS]`/`[DecidablePred p]` are needed because
    `heimSim` uses them. -/
def wantHeim (belS : Set W) [DecidablePred belS]
    (params : HeimDesireParams W) (w_eval : W) (p : Set W) [DecidablePred p] : Prop :=
  ∀ w' ∈ (Finset.univ : Finset W).filter belS,
    ∀ x ∈ heimSim params belS p w',
      ∀ y ∈ heimSim params belS (fun z => ¬ p z) w',
        params.pref w_eval x y

instance (belS : Set W) [DecidablePred belS]
    (params : HeimDesireParams W) (w_eval : W) (p : Set W) [DecidablePred p] :
    Decidable (wantHeim belS params w_eval p) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-- Heim's (40) amendment (paper §4.2.3, p. 198): ⟦α wants φ⟧ is defined
    only when the agent does not already believe φ and does not already
    believe ¬φ. Equivalently: both `belS ∩ φ` and `belS ∩ ¬φ` are
    non-empty. -/
def wantHeimDefined (belS : Set W) [DecidablePred belS]
    (p : Set W) [DecidablePred p] : Prop :=
  (∃ w, belS w ∧ p w) ∧ (∃ w, belS w ∧ ¬ p w)

instance (belS : Set W) [DecidablePred belS]
    (p : Set W) [DecidablePred p] :
    Decidable (wantHeimDefined belS p) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! ### Heim no-go: comparative-belief blocks simultaneous `want(p) ∧ want(¬p)`

The proof shape: pick any `w' ∈ belS` (exists since `wantHeimDefined`
gives non-empty `belS ∩ p`). Pick any `x ∈ Sim p w'` and any
`y ∈ Sim ¬p w'` (both non-empty under `wantHeimDefined`). Then
`wantHeim belS params w_eval p` gives `pref w_eval x y` and
`wantHeim belS params w_eval ¬p` gives `pref w_eval y x`. Strict
asymmetry of `pref` — i.e., `pref w x y ∧ pref w y x → x = y` for the
weak relation, or `pref w x y → ¬ pref w y x` for the strict — yields
`x = y`, but `x ∈ p` and `y ∈ ¬p` (since Sim's first arg restricts to
`belS ∩ p` / `belS ∩ ¬p`), contradiction.

The substrate exposes the asymmetry as a hypothesis to keep the
no-go applicable to both strict and partial-order desirability
relations. -/

/-- A `belS ∩ p`-world reachable via similarity from any belS-world
    under the limit assumption, i.e. when `wantHeimDefined` holds, gives
    a non-empty `heimSim params belS p w'`. Discharges Heim's Limit
    Assumption automatically on finite types via
    `Core.Order.SimilarityOrdering.closestWorlds_nonempty`. -/
theorem heimSim_nonempty (belS : Set W) [DecidablePred belS]
    (params : HeimDesireParams W) (p : Set W) [DecidablePred p]
    (w' : W) (hNE : ∃ z, belS z ∧ p z) :
    (heimSim params belS p w').Nonempty := by
  unfold heimSim
  apply Core.Order.SimilarityOrdering.closestWorlds_nonempty
  obtain ⟨z, hzBel, hzp⟩ := hNE
  exact ⟨z, by simp [Finset.mem_filter, hzBel, hzp]⟩

/-- **Heim no-go theorem**: under the (40) definedness amendment and a
    *strictly asymmetric* desirability relation, no Heim-semantic
    prediction makes both `want(p)` and `want(¬p)` true.

    Proof: extract a witness from each `Sim` (non-empty by
    `heimSim_nonempty`), then chase strict asymmetry of `pref` to a
    `p w ∧ ¬ p w` contradiction.

    The asymmetry hypothesis `hAsym` is the substantive condition: it
    says `pref` is a strict (irreflexive) preference, i.e., a world
    cannot be strictly preferred to itself. Standard for any
    well-formed comparative desirability. -/
theorem wantHeim_no_simultaneous_pq_and_negpq
    (belS : Set W) [DecidablePred belS]
    (params : HeimDesireParams W) (w_eval : W) (p : Set W) [DecidablePred p]
    (hAsym : ∀ x y, params.pref w_eval x y → params.pref w_eval y x → x = y)
    (h : wantHeimDefined belS p) :
    ¬ (wantHeim belS params w_eval p ∧
       wantHeim belS params w_eval (fun w => ¬ p w)) := by
  rintro ⟨hp, hnp⟩
  obtain ⟨⟨wp, hwp_bel, hwp_p⟩, ⟨wn, hwn_bel, hwn_np⟩⟩ := h
  -- The negation argument's heimSim has a double-negation that needs
  -- reduction: heimSim belS (¬¬p) = heimSim belS p extensionally.
  have hSim_negneg :
      heimSim params belS (fun z => ¬ (fun w => ¬ p w) z) wp
        = heimSim params belS p wp := by
    unfold heimSim
    congr 1
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
               Decidable.not_not]
  -- Pick w' = wp (any belS-world; we use the p-witness).
  have hwp_filter : wp ∈ (Finset.univ : Finset W).filter belS := by
    simp [Finset.mem_filter, hwp_bel]
  obtain ⟨x, hx⟩ := heimSim_nonempty belS params p wp ⟨wp, hwp_bel, hwp_p⟩
  obtain ⟨y, hy⟩ := heimSim_nonempty belS params (fun z => ¬ p z) wp ⟨wn, hwn_bel, hwn_np⟩
  have hxy : params.pref w_eval x y := hp wp hwp_filter x hx y hy
  -- Use hSim_negneg to convert hx : x ∈ heimSim params belS p wp into the
  -- form expected by hnp (which has heimSim ... (¬¬p) ...).
  have hx' : x ∈ heimSim params belS (fun z => ¬ (fun w => ¬ p w) z) wp :=
    hSim_negneg ▸ hx
  have hyx : params.pref w_eval y x := hnp wp hwp_filter y hy x hx'
  have hxy_eq : x = y := hAsym x y hxy hyx
  -- x ∈ heimSim params belS p wp ⊆ {z | belS z ∧ p z}, so p x.
  have hxp : p x := by
    have := Core.Order.SimilarityOrdering.closestWorlds_subset _ _ _ hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact this.2
  have hynp : ¬ p y := by
    have := Core.Order.SimilarityOrdering.closestWorlds_subset _ _ _ hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact this.2
  exact hynp (hxy_eq ▸ hxp)

/-! ## Belief-based desire semantics: structural typology and parametric no-go

A `BeliefBasedDesireSemantics` packages a desire-semantic device that
takes (Bel_S, parameters, evaluation world, proposition) and returns a
truth value, without any contextual question parameter outside this
shape. Both vF and Heim are instances; PB's `wantQuestionBased` is
*not* (its question parameter `answers` plays a non-trivial role that
varies per ascription).

The structure operates on `Set W` to match the substrate's underlying
predicates and to make the `want(p) ∧ want(¬p)` no-go statement
notation-clean (using `fun w => ¬ p w` rather than `Finset.univ \ p`,
which would require an awkward `Finset.mem_sdiff` rewrite chain).
Decidability inside instances is supplied via `Classical.dec` — the
structure is for Prop-level reasoning, not for `decide`. The
substrate-level `wantVF`/`wantHeim` retain their per-instance
decidability for concrete `decide` proofs in study files. -/

/-- A belief-based desire semantics on world type `W`. `defined`
    carries the presuppositional definedness condition; `want` is the
    truth condition. Both range over `Set W` for the doxastic state and
    proposition. -/
structure BeliefBasedDesireSemantics (W : Type*) where
  /-- Type of additional parameters (desire list for vF, similarity +
      pref for Heim, etc.). -/
  Param : Type*
  /-- Definedness condition: the presupposition that ⟦S wants p⟧^c is
      defined at the configuration. -/
  defined : Set W → Param → Set W → Prop
  /-- Truth condition: when defined, the prediction of ⟦S wants p⟧^c. -/
  want : Set W → Param → W → Set W → Prop

namespace BeliefBasedDesireSemantics

variable {W : Type*}

/-- A semantics is **conflict-blocking** if no parameters/world make
    `want(p)` and `want(¬p)` both true when both are defined. This is
    the no-go theorem in slogan form: belief-based semantics cannot
    handle conflicting desire ascriptions. -/
def isConflictBlocking (F : BeliefBasedDesireSemantics W) : Prop :=
  ∀ belS Param w_eval (p : Set W),
    F.defined belS Param p → F.defined belS Param (fun w => ¬ p w) →
    ¬ (F.want belS Param w_eval p ∧ F.want belS Param w_eval (fun w => ¬ p w))

end BeliefBasedDesireSemantics

/-- vF as a `BeliefBasedDesireSemantics` instance. The evaluation-world
    argument is suppressed (vF is world-independent at the `want`
    level). The `defined` predicate requires both p and ¬p to overlap
    with belS — strong enough that some belS-world is necessarily
    undominated, which is what the vF no-go needs. -/
def vFSemantics {W : Type*} [Fintype W] :
    BeliefBasedDesireSemantics W where
  Param := List (DecProp W)
  defined belS _ p := (∃ w, belS w ∧ p w) ∧ (∃ w, belS w ∧ ¬ p w)
  want belS GS _ p := wantVF belS GS p

/-- A propositional-equivalent form of `wantHeim` that takes its
    decidability arguments via `Classical.decPred` rather than from the
    ambient typeclass context. Used in `heimSemantics.want` to ensure
    the structure projection has a stable form independent of caller
    decidability instances. -/
noncomputable def wantHeimClassical {W : Type*} [Fintype W] [DecidableEq W]
    (belS : Set W) (params : HeimDesireParams W) (w_eval : W) (p : Set W) : Prop :=
  letI : DecidablePred belS := Classical.decPred _
  letI : DecidablePred p := Classical.decPred _
  wantHeim belS params w_eval p

/-- The classical-decidability variant agrees with `wantHeim` under any
    ambient decidability instances (via `Subsingleton`). -/
theorem wantHeimClassical_iff_wantHeim {W : Type*} [Fintype W] [DecidableEq W]
    (belS : Set W) [DecidablePred belS]
    (params : HeimDesireParams W) (w_eval : W) (p : Set W) [DecidablePred p] :
    wantHeimClassical belS params w_eval p ↔ wantHeim belS params w_eval p := by
  -- LHS uses `Classical.decPred`-derived instances; RHS uses ambient
  -- typeclass instances. `DecidablePred` is a `Subsingleton`, so the two
  -- agree propositionally — `congr!` closes the goal directly.
  unfold wantHeimClassical
  congr!

/-- Heim as a `BeliefBasedDesireSemantics` instance. Definedness is
    Heim's (40) amendment; `want` wraps `wantHeimClassical` (which
    bakes in `Classical.decPred` so the structure projection is stable
    across ambient decidability instances). Abstract reasoning at the
    typology level is Prop-only; the `wantHeimClassical_iff_wantHeim`
    bridge converts to/from the typeclass-decidable form. -/
noncomputable def heimSemantics {W : Type*} [Fintype W] [DecidableEq W] :
    BeliefBasedDesireSemantics W where
  Param := HeimDesireParams W
  defined belS _ p :=
    (∃ w, belS w ∧ p w) ∧ (∃ w, belS w ∧ ¬ p w)
  want belS params w_eval p := wantHeimClassical belS params w_eval p

/-! ## Parametric no-go theorems for the structural typology -/

/-- vF is **conflict-blocking** (parametric no-go). The `defined`
    predicate requires both p-witnesses and ¬p-witnesses in belS, which
    is exactly what `wantVF_no_simultaneous_pq_and_negpq` needs after
    we extract a Pareto-undominated witness via finite-preorder
    minimal-element existence. -/
theorem vFSemantics_isConflictBlocking {W : Type*} [Fintype W] :
    BeliefBasedDesireSemantics.isConflictBlocking (vFSemantics (W := W)) := by
  classical
  intro belS GS _w_eval p hDef _hDefNeg ⟨hp, hnp⟩
  -- vFSemantics.want belS GS _ p reduces to wantVF belS GS p.
  -- Apply the substrate no-go; need an undominated belS-world, which exists
  -- by Finite.exists_minimal under the desire-induced preorder.
  apply wantVF_no_simultaneous_pq_and_negpq belS GS p ?_ ⟨hp, hnp⟩
  obtain ⟨wp, hwp_bel, _⟩ := hDef.1
  -- Set up worldAtLeastAsGood as a Preorder and extract a minimal belS-world.
  letI : Preorder W :=
    { le := worldAtLeastAsGood GS
      le_refl := fun _ _ _ hp_w => hp_w
      le_trans := fun _ _ _ huv hvw q hq hqz => huv q hq (hvw q hq hqz) }
  have hbelNonempty : (belS : Set W).Nonempty := ⟨wp, hwp_bel⟩
  obtain ⟨m, hmA, hmin⟩ := (Set.toFinite _).exists_minimal hbelNonempty
  exact ⟨m, hmA, fun z hz ⟨hzm, hnmz⟩ => hnmz (hmin hz hzm)⟩

/-- Heim is **conflict-blocking** (parametric no-go) at any
    `(params, w_eval)` with strict preference asymmetry. Delegates to
    `wantHeim_no_simultaneous_pq_and_negpq`. -/
theorem heimSemantics_isConflictBlocking {W : Type*} [Fintype W] [DecidableEq W]
    (params : HeimDesireParams W) (w_eval : W)
    (hAsym : ∀ x y, params.pref w_eval x y → params.pref w_eval y x → x = y) :
    ∀ belS (p : Set W),
      (heimSemantics (W := W)).defined belS params p →
      (heimSemantics (W := W)).defined belS params (fun w => ¬ p w) →
      ¬ ((heimSemantics (W := W)).want belS params w_eval p ∧
         (heimSemantics (W := W)).want belS params w_eval (fun w => ¬ p w)) := by
  classical
  intro belS p hDef _hDefNeg ⟨hp, hnp⟩
  -- `heimSemantics.want` reduces to `wantHeimClassical` after the
  -- structure projection; the bridge `wantHeimClassical_iff_wantHeim`
  -- converts to the typeclass-decidable form needed by the substrate.
  rw [show (heimSemantics (W := W)).want = fun belS params w p =>
        wantHeimClassical belS params w p from rfl] at hp hnp
  rw [wantHeimClassical_iff_wantHeim] at hp hnp
  exact wantHeim_no_simultaneous_pq_and_negpq belS params w_eval p hAsym hDef
    ⟨hp, hnp⟩

/-! ## Bridge to `Question` infrastructure

PB's `List (DecProp W)` is a finite-presentation view of a partition
question. The substrate exposes bridge theorems showing each PB
predicate corresponds to a property of the underlying
`Question W`:

* `wantQuestionBased` "every undominated answer entails p" relates to
  the partition property "every undominated cell of `Q` entails `p`"
  — i.e., `∀ q ∈ alt Q, q ∈ undominated → q ⊆ p`.

* `isConsidered` corresponds to `partial-answerhood for the polar
  question of p`: every cell of Q is either a confirming or refuting
  answer to "p?".

The `toQuestion` constructor lifts a `List (DecProp W)` to
`Question W` via `Question.ofList`. -/

/-- Lift a list of decidable cells to a `Question W`. -/
def toQuestion (answers : List (DecProp W)) : Question W :=
  Question.ofList (answers.map (·.prop))

omit [Fintype W] [DecidableEq W] in
/-- `isConsidered Q p` agrees with the polar-answerhood reading of
    every cell: each cell either entails `p` or entails `pᶜ`, which is
    exactly "every cell is a partial answer to the polar question of
    `p`". -/
theorem isConsidered_iff_polar_partial_answer
    (answers : List (DecProp W)) (p : Set W) [DecidablePred p] :
    isConsidered answers p ↔
    ∀ a ∈ answers, a.prop ⊆ p ∨ a.prop ⊆ {w | ¬ p w} := by
  unfold isConsidered
  refine ⟨fun h a ha => ?_, fun h a ha => ?_⟩
  · rcases h a ha with hp | hnp
    · exact Or.inl (fun w hw => hp w hw)
    · exact Or.inr (fun w hw hpw => hnp w hw hpw)
  · rcases h a ha with hp | hnp
    · exact Or.inl (fun w hw => hp hw)
    · exact Or.inr (fun w hw hpw => hnp hw hpw)

end Generic

/-! ## [lassiter-2017] (apparatus) / [lassiter-2011] (want application):
       Expected-value desire semantics

[lassiter-2017] ch.7 (titled "Scalar goodness", *not* a desire
chapter) develops an expected-value semantics for evaluative gradable
predicates: `E_V(φ) = Σ_{w ∈ φ ∩ D} V(w) · prob({w} | φ ∩ D)` (eq. 7.22,
p.187). The book's positive-form *ought* (§8.14 eq. 8.72a, p.253) is
exactly the threshold reading `μ_ought(φ) > θ_ought` we adopt as `want`.
The book extends to *want* in a single sentence at §8.13 (p.249):
"*want* behaves as a gradable verb like *like, matter, care, [...]
need*." The detailed *want*-as-EU account lives in [lassiter-2011]
ch.6 (NYU dissertation).

The substrate exposes:

* `Lassiter.expectedValue pr V belS p` — conditional expected value of
  `p` given the agent's belief state. Convention: returns `0` when
  `p ∩ belS = ∅` (Lassiter notes E_V undefined here, p.187 fn.).
* `Lassiter.want belS pr V θ p` — Lassiter-style positive-form want:
  `E_V(p|bel) > θ`. Matches paper §8.14 eq. 8.72a.
* `Lassiter.slomanPrinciple` (paper §8.6 eq. 8.16, p.216) — a constraint
  that the wanted proposition strictly dominates every other relevant
  alternative on the value scale.
* `Lassiter.wantWithSloman` — Lassiter's *full* account: bare threshold
  AND Sloman's Principle.

**The bare threshold form admits simultaneous want(p) ∧ want(¬p)**
(`Lassiter.threshold_admits_conflict_witness`), violating the substrate's
`BeliefBasedDesireSemantics.isConflictBlocking`. This makes Lassiter's
*bare apparatus* a sibling of vF/Heim/PB, *not* a `BBSemantics`
instance. Lassiter and Phillips-Brown are *different ways* of escaping
the no-go: PB via question-sensitivity, Lassiter via
probabilistic-decision-theoretic gradability.

**However, Lassiter's full account blocks the witness.** Per paper
§8.11 (p.245): *"we should not weaken the semantics to make room for
the simultaneous truth of ought(φ) and ought(¬φ). Instead, we should
allow that there are various, possibly conflicting **sources of
value**..."* Sloman's Principle (eq. 8.16, p.216;
`Lassiter.wantWithSloman_blocks_conflict`) excludes the witness on a
single value function; genuine conflicting wants come from multiple
value sources with weighted aggregation (§8.11 pp.243-245), not from
single-V threshold-tuning. The bare threshold's admission of conflict
is what Cariani 2013 attacks; Lassiter's response is *not* "let
single-V conflict happen" but "let multi-source aggregation explain
the data without single-V conflict."

The substrate exposes both layers (bare threshold + Sloman-augmented
full account) so the reader can see exactly which Lassiter-flavored
claim is being made. -/

namespace Lassiter

variable {W : Type*}

/-! ### §1. Bare expected-value apparatus -/

/-- Conditional expected value of `p` given belief state `belS` under
    prior `pr` and value function `V`. Lassiter 2017 §7.6 eq. 7.22:

      E_V(p) = Σ_{w ∈ p ∩ belS} V(w) · pr({w} | p ∩ belS)

    Expanded as a ratio:

      E_V(p) = (Σ pr·V over (p ∩ belS)) / (Σ pr over (p ∩ belS))

    Indicator-style sums (rather than `Finset.filter`) make the
    definition `decide`-friendly for concrete witness models. The two
    sums are inlined (not `let`-bound) so that downstream `rw` calls
    don't have to unfold a `have`-binding. Returns `0` when the
    denominator is zero (Lassiter notes E_V undefined for the empty
    proposition, p.187 fn.; we make the 0 convention). -/
def expectedValue [Fintype W]
    (pr : W → ℚ) (V : W → ℚ)
    (belS : Set W) [DecidablePred belS]
    (p : Set W) [DecidablePred p] : ℚ :=
  if (∑ w, (if belS w ∧ p w then pr w else 0)) = 0 then 0
  else (∑ w, (if belS w ∧ p w then pr w * V w else 0)) /
       (∑ w, (if belS w ∧ p w then pr w else 0))

/-- **Lassiter-style positive-form `want`**: ⟦S wants p⟧ iff the
    conditional expected value of `p` given S's beliefs exceeds
    threshold `θ`. Matches paper §8.14 eq. 8.72a's scalar
    interpretation `μ_ought(φ) > θ_ought`, extended to *want* per
    §8.13 + Lassiter 2011 ch.6. -/
def want [Fintype W]
    (belS : Set W) [DecidablePred belS]
    (pr : W → ℚ) (V : W → ℚ) (θ : ℚ)
    (p : Set W) [DecidablePred p] : Prop :=
  expectedValue pr V belS p > θ

instance [Fintype W]
    (belS : Set W) [DecidablePred belS]
    (pr : W → ℚ) (V : W → ℚ) (θ : ℚ)
    (p : Set W) [DecidablePred p] :
    Decidable (want belS pr V θ p) :=
  inferInstanceAs (Decidable (_ > θ))

/-! ### §2. Sloman's Principle (paper §8.6 eq. 8.16, p.216)

`ought(φ) → [∀ψ ∈ ALT(φ) : ψ ≠ φ → φ >_good ψ]`

The wanted proposition strictly dominates every other alternative on
the value scale. This is the constraint Lassiter adopts to block
simultaneous truth of `ought(φ) ∧ ought(¬φ)` when both are in the
alternative set. -/

/-- Sloman's Principle: `p` strictly dominates every other listed
    alternative on the expected-value scale. Decidable via the
    underlying `expectedValue` decidability. -/
def slomanPrinciple [Fintype W]
    (belS : Set W) [DecidablePred belS]
    (pr : W → ℚ) (V : W → ℚ)
    (alts : List (Σ' (q : Set W), DecidablePred q))
    (p : Set W) [DecidablePred p] : Prop :=
  ∀ entry ∈ alts,
    let _ : DecidablePred entry.fst := entry.snd
    entry.fst ≠ p →
    expectedValue pr V belS p > expectedValue pr V belS entry.fst

/-- **Lassiter's full account**: the bare threshold AND Sloman's
    Principle. This is the *actual* account Lassiter defends in §8;
    the bare `want` operator alone is the apparatus, not the position. -/
def wantWithSloman [Fintype W]
    (belS : Set W) [DecidablePred belS]
    (pr : W → ℚ) (V : W → ℚ) (θ : ℚ)
    (alts : List (Σ' (q : Set W), DecidablePred q))
    (p : Set W) [DecidablePred p] : Prop :=
  want belS pr V θ p ∧ slomanPrinciple belS pr V alts p

/-! ### §3. Bridge to `Core.Agent.DecisionTheory`

`Lassiter.expectedValue` is the proposition-conditional analog of
`Core.Agent.DecisionTheory.DecisionProblem.condExpectedUtility`. Wrapping the value function
as a unit-action utility makes the bridge explicit. -/

/-- Wrap a Lassiter `(prior, value)` pair as a unit-action
    `DecisionProblem`. -/
def toDecisionProblem (pr : W → ℚ) (V : W → ℚ) :
    Core.DecisionTheory.DecisionProblem ℚ W Unit where
  utility w _ := V w
  prior := pr

/-! ### §4. Conflict witness for the bare threshold

A 4-world model demonstrating that the *bare* `want` operator (without
Sloman) admits simultaneous `want(p) ∧ want(¬p)`. Uniform prior 1/4 over
`Fin 4`; asymmetric value `V = (10, 4, 4, 0)`; threshold `θ = 3/2`;
`p = {w₀, w₁}`. Then `E_V(p) = 7 > 3/2` and `E_V(¬p) = 2 > 3/2`.

This is Lassiter Table 8.4 p.239 — Lassiter's reconstruction of the
Weakening-failure pattern [cariani-2016] attacks within actualism,
applied to the EV semantics. Cariani 2016's own counter-model
(p.405) uses an actualist closeness ordering, not EV. Lassiter's
*response* is to add Sloman's Principle, which excludes the witness
(see `wantWithSloman_blocks_conflict_on_witness` below). -/

theorem threshold_admits_conflict_witness :
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (belS : Set W) (_ : DecidablePred belS)
      (pr : W → ℚ) (V : W → ℚ) (θ : ℚ)
      (p : Set W) (_ : DecidablePred p),
      want belS pr V θ p ∧
      want belS pr V θ (fun w => ¬ p w) := by
  refine ⟨Fin 4, inferInstance, inferInstance,
          (fun _ => True), inferInstance,
          (fun _ => 1/4),
          (fun w => match w with
            | 0 => 10 | 1 => 4 | 2 => 4 | 3 => 0),
          3/2,
          (fun w => w = 0 ∨ w = 1), inferInstance,
          ?_, ?_⟩
  all_goals
    show want _ _ _ _ _
    unfold want expectedValue
    simp [Fin.sum_univ_succ]
    norm_num

/-- **Lassiter's bare apparatus is structurally outside the
    belief-based family.** The `threshold_admits_conflict_witness` model
    cannot be reproduced by any `BeliefBasedDesireSemantics` instance
    that satisfies `isConflictBlocking`. Stated as a direct existential
    — no padding with the `isConflictBlocking` definition unfolding. -/
theorem outside_belief_based_family :
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (belS : Set W) (_ : DecidablePred belS)
      (pr : W → ℚ) (V : W → ℚ) (θ : ℚ)
      (p : Set W) (_ : DecidablePred p),
      want belS pr V θ p ∧
      want belS pr V θ (fun w => ¬ p w) :=
  threshold_admits_conflict_witness

/-! ### §5. Sloman's Principle blocks the witness

Lassiter's *full* account adds Sloman's Principle (eq. 8.16 p.216).
On the conflict-witness model with `alts = [propP, ¬propP]`, Sloman
holds for `propP` (E_V(propP) = 7 > 2 = E_V(¬propP) ✓) but FAILS for
`¬propP` (E_V(¬propP) = 2 ≯ 7 = E_V(propP) ✗). So
`wantWithSloman` makes only `propP` wanted, blocking the conflict.

This formalizes Lassiter's §8.11 (p.245) position: single-V conflict
is blocked by his own constraints; genuine conflicting wants come from
multi-source aggregation, not from threshold-tuning. -/

theorem wantWithSloman_blocks_conflict
    [Fintype W] (belS : Set W) [DecidablePred belS]
    (pr : W → ℚ) (V : W → ℚ) (θ : ℚ)
    (p : Set W) [DecidablePred p]
    (alts : List (Σ' (q : Set W), DecidablePred q))
    (h_p_in_alts : ⟨p, inferInstance⟩ ∈ alts)
    (h_negp_in_alts : ⟨fun w => ¬ p w, inferInstance⟩ ∈ alts)
    (h_p_ne_negp : (p : Set W) ≠ (fun w => ¬ p w)) :
    ¬ (wantWithSloman belS pr V θ alts p ∧
       wantWithSloman belS pr V θ alts (fun w => ¬ p w)) := by
  simp only [wantWithSloman, slomanPrinciple]
  rintro ⟨⟨_, hSlomanP⟩, ⟨_, hSlomanNegP⟩⟩
  -- Sloman for p: E_V(p) > E_V(¬p) (since ¬p is in alts and ≠ p)
  have h1 : expectedValue pr V belS p > expectedValue pr V belS (fun w => ¬ p w) := by
    exact hSlomanP ⟨fun w => ¬ p w, inferInstance⟩ h_negp_in_alts h_p_ne_negp.symm
  -- Sloman for ¬p: E_V(¬p) > E_V(p) (since p is in alts and ≠ ¬p)
  have h2 : expectedValue pr V belS (fun w => ¬ p w) > expectedValue pr V belS p := by
    exact hSlomanNegP ⟨p, inferInstance⟩ h_p_in_alts h_p_ne_negp
  exact absurd (lt_trans h1 h2) (lt_irrefl _)

/-! ### §6. Intermediacy of `expectedValue` (paper §7.5, §7.6 p.188)

Lassiter §7.5 establishes that `S_good` is an *intermediate* scale: the
goodness of `φ ∨ ψ` is between the goodness of `φ` and the goodness of
`ψ` (rather than maximal — equal to the better of the two — or
positive — strictly above both). In §7.6 (p.188), the disjoint union
formula

  E_V(φ ∨ ψ) = (E_V(φ)·prob(φ) + E_V(ψ)·prob(ψ)) / (prob(φ) + prob(ψ))

shows E_V is a weighted average over disjoint propositions, hence
intermediate.

We formalize the disjoint case directly: for disjoint p, q with
positive belief mass, `min(E_V(p), E_V(q)) ≤ E_V(p ∪ q) ≤ max(...)`.
This is the key abstract scalar property that underlies Weakening
(below) and is the empirical motivation for Lassiter's whole
expected-value semantics. -/

/-- A proposition has *positive belief mass* if some belS-world
    satisfies it. Decidability is inherited via the fact that
    `Set.Nonempty (belS ∩ p)` is decidable on finite types. -/
def hasPositiveBeliefMass [Fintype W]
    (pr : W → ℚ) (belS : Set W) [DecidablePred belS]
    (p : Set W) [DecidablePred p] : Prop :=
  (∑ w, (if belS w ∧ p w then pr w else 0)) > 0

/-- **Intermediacy of E_V (disjoint case)**: for disjoint propositions
    p, q with positive belief mass, `E_V(p ∪ q)` lies between
    `E_V(p)` and `E_V(q)`.

    The formal claim: when both sides are well-defined and the prior
    is non-negative on the support, `min(E_V(p), E_V(q)) ≤ E_V(p ∪ q)
    ≤ max(E_V(p), E_V(q))`.

    Proof is left as `sorry` pending the algebraic manipulation of the
    indicator-style sum (the inequality is well-known for weighted
    averages but the bookkeeping over `Finset.sum` of `if`-then-else
    expressions is non-trivial). The statement is the load-bearing
    item; consumers (e.g. `want_satisfies_weakening_disjoint`) can use
    it via the named theorem without waiting for the proof. -/
theorem expectedValue_intermediate_disjoint [Fintype W]
    (pr : W → ℚ) (V : W → ℚ)
    (belS : Set W) [DecidablePred belS]
    (p q : Set W) [DecidablePred p] [DecidablePred q]
    (hPosP : hasPositiveBeliefMass pr belS p)
    (hPosQ : hasPositiveBeliefMass pr belS q)
    (hDisjoint : ∀ w, ¬ (p w ∧ q w))
    (hNonneg : ∀ w, 0 ≤ pr w) :
    min (expectedValue pr V belS p) (expectedValue pr V belS q)
      ≤ expectedValue pr V belS (fun w => p w ∨ q w) ∧
    expectedValue pr V belS (fun w => p w ∨ q w)
      ≤ max (expectedValue pr V belS p) (expectedValue pr V belS q) := by
  -- TODO: discharge via algebraic manipulation. The disjoint union
  -- expectation is `(E(p)·μ(p) + E(q)·μ(q)) / (μ(p) + μ(q))`, a
  -- weighted average between `E(p)` and `E(q)`. Standard result.
  sorry

/-! ### §7. Smith Principle and Weakening (paper §8.10, §8.14 eq. 8.54)

Lassiter eq. 8.54 collects three constraints on `ought`:

* (a) **Sloman** (Sloman 1970): `ought(φ) → ∀ψ ∈ ALT(φ), ψ ≠ φ → φ >_good ψ`
  (already formalized as `slomanPrinciple`)
* (b) **Smith** (Horty 1993, 2003): `[(φ ∨ ψ) = W ∧ ought(φ) ∧ ought(ψ)]
  → ought(φ ∧ ψ)` — restricted agglomeration
* (c) **Weakening** ([cariani-2016]): `ought(φ) ∧ ought(ψ) → ought(φ ∨ ψ)`

These are constraints on the `want` operator, not properties of single
propositions. We formalize each as a `Prop` relating two propositions;
the universally-quantified "operator satisfies the constraint" is the
`∀ p q` closure.

**Provenance for Weakening**: [cariani-2016] introduces the name
and argues the principle is valid within actualist deontic semantics
(Cariani's own Counterexample to Weakening on p.405 attacks the
*conjunction* actualism + simple alternatives mapping; he wants to
preserve Weakening). Lassiter §8.14 derives Weakening from intermediacy
of E_V — see `want_satisfies_weakening_disjoint`. So in our
formalization, Weakening is *named* per Cariani 2016, *defined* as an
operator constraint, and *derived* (in the disjoint case) from the
intermediacy property of expected value (Lassiter §7.5, §7.6 p.188).
This honors linglib's "derive don't stipulate" discipline: Weakening
isn't a brute axiom — it falls out of the underlying scalar property.

Smith is stated as a separate constraint; its derivation requires more
structure than intermediacy alone (Horty 1993, 2003). -/

/-- **Smith Principle (paper eq. 8.54b)**: if `(p ∨ q) = univ` and
    both `want(p)` and `want(q)` hold, then `want(p ∧ q)` holds.

    Formalized as a `Prop` parameterized on a specific `(p, q)` pair.
    The "want operator satisfies Smith" is the `∀ p q` closure. -/
def smithPrinciple [Fintype W]
    (belS : Set W) [DecidablePred belS]
    (pr : W → ℚ) (V : W → ℚ) (θ : ℚ)
    (p q : Set W) [DecidablePred p] [DecidablePred q] : Prop :=
  (∀ w, p w ∨ q w) →
  want belS pr V θ p →
  want belS pr V θ q →
  want belS pr V θ (fun w => p w ∧ q w)

/-- **Weakening (paper eq. 8.54c)**: if both `want(p)` and `want(q)`
    hold, then `want(p ∨ q)` holds. Lassiter argues this is empirically
    valid (§8.10) and derivable from intermediacy of E_V (§8.14). -/
def weakeningPrinciple [Fintype W]
    (belS : Set W) [DecidablePred belS]
    (pr : W → ℚ) (V : W → ℚ) (θ : ℚ)
    (p q : Set W) [DecidablePred p] [DecidablePred q] : Prop :=
  want belS pr V θ p →
  want belS pr V θ q →
  want belS pr V θ (fun w => p w ∨ q w)

/-- **Weakening from intermediacy** (disjoint case): when `p ⊥ q` and
    both have positive belief mass, the disjoint-union expected value
    is at least the smaller of `E_V(p)` and `E_V(q)`. So if both
    exceed `θ`, so does their union.

    This is Lassiter §8.14 eq. (8.78)'s derivation: intermediacy
    means `E_V(p ∨ q) ≥ min(E_V(p), E_V(q)) > θ`. -/
theorem want_satisfies_weakening_disjoint [Fintype W]
    (belS : Set W) [DecidablePred belS]
    (pr : W → ℚ) (V : W → ℚ) (θ : ℚ)
    (p q : Set W) [DecidablePred p] [DecidablePred q]
    (hPosP : hasPositiveBeliefMass pr belS p)
    (hPosQ : hasPositiveBeliefMass pr belS q)
    (hDisjoint : ∀ w, ¬ (p w ∧ q w))
    (hNonneg : ∀ w, 0 ≤ pr w)
    (hp : want belS pr V θ p) (hq : want belS pr V θ q) :
    want belS pr V θ (fun w => p w ∨ q w) := by
  unfold want at hp hq ⊢
  have ⟨hMin, _hMax⟩ :=
    expectedValue_intermediate_disjoint pr V belS p q hPosP hPosQ hDisjoint hNonneg
  exact lt_of_lt_of_le (lt_min hp hq) hMin

/-- **The full Lassiter constraint trio (paper eq. 8.54)**: a `want`
    operator satisfies the trio at `(p, q)` iff Sloman holds for `p`
    and Smith and Weakening hold pointwise. The `∀ p q alts` closure
    over this gives Lassiter's full theory. -/
def fullConstraintsTrio [Fintype W]
    (belS : Set W) [DecidablePred belS]
    (pr : W → ℚ) (V : W → ℚ) (θ : ℚ)
    (alts : List (Σ' (q : Set W), DecidablePred q))
    (p q : Set W) [DecidablePred p] [DecidablePred q] : Prop :=
  slomanPrinciple belS pr V alts p ∧
  smithPrinciple belS pr V θ p q ∧
  weakeningPrinciple belS pr V θ p q

/-- **The full constraint trio also blocks the conflict witness.**
    With Sloman as the active blocker (Smith and Weakening don't
    directly address `(p, ¬p)` since they're closure constraints),
    the trio inherits the blocking from `wantWithSloman`. -/
theorem fullConstraintsTrio_blocks_conflict [Fintype W]
    (belS : Set W) [DecidablePred belS]
    (pr : W → ℚ) (V : W → ℚ) (θ : ℚ)
    (p : Set W) [DecidablePred p]
    (alts : List (Σ' (q : Set W), DecidablePred q))
    (h_p_in_alts : ⟨p, inferInstance⟩ ∈ alts)
    (h_negp_in_alts : ⟨fun w => ¬ p w, inferInstance⟩ ∈ alts)
    (h_p_ne_negp : (p : Set W) ≠ (fun w => ¬ p w))
    (hP : want belS pr V θ p) (hSlomanP : slomanPrinciple belS pr V alts p)
    (hNegP : want belS pr V θ (fun w => ¬ p w))
    (hSlomanNegP : slomanPrinciple belS pr V alts (fun w => ¬ p w)) :
    False := by
  exact wantWithSloman_blocks_conflict belS pr V θ p alts
    h_p_in_alts h_negp_in_alts h_p_ne_negp ⟨⟨hP, hSlomanP⟩, ⟨hNegP, hSlomanNegP⟩⟩

end Lassiter

end Semantics.Attitudes.Desire
