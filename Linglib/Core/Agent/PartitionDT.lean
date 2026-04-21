import Linglib.Core.Question.Partition.Lattice
import Linglib.Core.Question.Partition.Cells
import Linglib.Core.Agent.DecisionTheory
import Mathlib.Order.Partition.Finpartition
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.Order.GroupWithZero.Finset

/-!
# Decision-Theoretic Bridge for Partition QUDs
@cite{merin-1999} @cite{blackwell-1953} @cite{van-rooy-2003}

Decision-theoretic content built on top of the QUD partition lattice
(`Core/Partition.lean`) and the decision-theory kernel
(`Core/Agent/DecisionTheory.lean`):

- `partitionEU` — partition-relative expected utility, compositional under
  coarsening (@cite{merin-1999} central theorem)
- `partitionValue` — the Blackwell-style raw weighted value
- `blackwell_refinement_value` — finer partitions are at least as valuable
- `resolution_value_eq_exact` — @cite{van-rooy-2003}'s mention-some =
  mention-all decision-theoretic equivalence
- `blackwell_characterizes_refinement` — the converse: ordering on values
  IS partition refinement
- `questionUtility_*` bridges connecting `Core.DecisionTheory.questionUtility`
  to `partitionValue`, plus non-negativity of QUD-derived utility

Namespace: `QUD`, for compatibility with existing call sites.
-/

namespace QUD

variable {M : Type*}

/-! ### EU Compositionality under Coarsening (@cite{merin-1999}, Central Theorem) -/

open Core.DecisionTheory in
/-- Expected utility computed via a partition: weight each cell's conditional EU
by the cell's probability.

EU_Q(a) = Σ_{c ∈ cells(Q)} P(c) · EU(a | c)

This is the partition-relative expected utility that @cite{merin-1999} shows is
compositional under coarsening. Uses `Finpartition` for exhaustivity and
disjointness, replacing ~200 lines of custom foldl arithmetic. -/
def partitionEU [Fintype M] [DecidableEq M] {A : Type*}
    (dp : DecisionProblem M A) (q : QUD M) (a : A) : ℚ :=
  q.toFinpartition.parts.sum (fun cell =>
    cell.sum dp.prior * conditionalEU dp cell a)

/-! #### Cell probability cancellation (Finset version) -/

open Core.DecisionTheory in
/-- Cell probability times conditional EU equals the raw weighted sum.

For non-negative priors:
- If `cellProb = 0`: all priors are 0, both sides vanish.
- If `cellProb ≠ 0`: the `cellProb` cancels via `Finset.mul_sum` + `field_simp`. -/
private theorem cellProb_mul_conditionalEU [DecidableEq M] {A : Type*}
    (dp : DecisionProblem M A) (cell : Finset M) (a : A)
    (hprior : ∀ w, dp.prior w ≥ 0) :
    cell.sum dp.prior * conditionalEU dp cell a =
    cell.sum (fun w => dp.prior w * dp.utility w a) := by
  simp only [conditionalEU]
  by_cases htot : cell.sum dp.prior = 0
  · simp only [htot, ite_true, mul_zero]
    symm; apply Finset.sum_eq_zero; intro w hw
    have : dp.prior w ≤ cell.sum dp.prior :=
      Finset.single_le_sum (fun x _ => hprior x) hw
    have : dp.prior w = 0 := le_antisymm (by linarith) (hprior w)
    simp [this]
  · simp only [htot, ite_false]
    rw [Finset.mul_sum]
    congr 1; ext w; field_simp

open Core.DecisionTheory in
/-- Law of total expectation for partition-relative EU.

The unconditional expected utility equals the partition-relative EU for
any partition, because partitions are exhaustive and mutually exclusive.

Uses `Finset.sum_biUnion` with `Finpartition.biUnion_parts` for the
decomposition — disjointness and exhaustivity come free from the
`Finpartition` structure.

**Non-negativity is necessary**: with `prior(w1) = 1, prior(w2) = -1`,
`utility(w1,a) = 1, utility(w2,a) = 0`, and a trivial partition,
`expectedUtility = 1` but `cellProb = 0` forces `partitionEU = 0`. -/
theorem eu_eq_partitionEU [Fintype M] [DecidableEq M] {A : Type*}
    (dp : DecisionProblem M A) (a : A) (q : QUD M)
    (hprior : ∀ w, dp.prior w ≥ 0) :
    expectedUtility dp a = partitionEU dp q a := by
  simp only [expectedUtility, partitionEU]
  set P := q.toFinpartition
  -- Decompose ∑ w : M via Finpartition
  conv_lhs => rw [show (Finset.univ : Finset M) = P.parts.biUnion id from P.biUnion_parts.symm]
  rw [Finset.sum_biUnion P.supIndep.pairwiseDisjoint]
  congr 1; ext cell
  exact (cellProb_mul_conditionalEU dp cell a hprior).symm

open Core.DecisionTheory in
/-- Partition-relative EU is partition-independent (given non-negative priors).

Any two partitions give the same partition-relative EU, because both
equal the unconditional EU (`eu_eq_partitionEU`). -/
theorem coarsening_preserves_eu [Fintype M] [DecidableEq M] {A : Type*}
    (dp : DecisionProblem M A) (q q' : QUD M) (a : A)
    (_hcoarse : q.coarsens q')
    (hprior : ∀ w, dp.prior w ≥ 0) :
    partitionEU dp q a = partitionEU dp q' a :=
  (eu_eq_partitionEU dp a q hprior).symm.trans
    (eu_eq_partitionEU dp a q' hprior)

/-! ### Blackwell Ordering -/

/-! #### Finset-based partition value -/

open Core.DecisionTheory in
/-- The value of a decision problem under partition Q over a Finset of worlds.

V_Q(D, W) = Σ_{c ∈ cells(Q,W)} max_a [Σ_{w∈c} p(w)·u(w,a)]

Following @cite{merin-1999}, this uses raw weighted sums directly
rather than factoring through conditional EU. The equivalence
`P(c) · max_a condEU(a,c) = max_a [Σ_{w∈c} p(w)·u(w,a)]` holds when
priors are non-negative. The raw form makes Blackwell's theorem a
direct application of sub-additivity. -/
def partitionValue [DecidableEq M] {A : Type*} (dp : DecisionProblem M A)
    (q : QUD M) (worlds : Finset M) (actions : Finset A) : ℚ :=
  (q.toCellsFinset worlds).sum (fun cell =>
    if h : actions.Nonempty then
      actions.sup' h (fun a => cell.sum (fun w => dp.prior w * dp.utility w a))
    else 0)

/-! #### Sub-additivity of max -/

/-- sup' with pointwise-equal inner functions gives equal results. -/
private lemma sup'_eq_of_forall_eq {α : Type*} (g₁ g₂ : α → ℚ) (actions : Finset α)
    (h : ∀ a, g₁ a = g₂ a) (hne : actions.Nonempty) :
    actions.sup' hne g₁ = actions.sup' hne g₂ :=
  Finset.sup'_congr hne rfl (fun a _ => h a)

/-- Sub-additivity of sup' over Finset.sum:
sup'_a (S.sum (fun c => f c a)) ≤ S.sum (fun c => sup'_a (f c a))

When actions is empty, both sides are 0 (the dite returns 0). -/
private lemma sup'_finset_sum_le {α β : Type*} [DecidableEq β]
    (f : β → α → ℚ) (S : Finset β) (actions : Finset α) (hne : actions.Nonempty) :
    actions.sup' hne (fun a => S.sum (fun c => f c a)) ≤
    S.sum (fun c => actions.sup' hne (fun a => f c a)) := by
  apply Finset.sup'_le hne
  intro a ha
  apply Finset.sum_le_sum
  intro c _
  exact Finset.le_sup' (fun a => f c a) ha

/-! #### Blackwell refinement theorem -/

set_option maxHeartbeats 1600000 in
/-- Per-cell step: a coarse cell's raw value ≤ sum of its fine cells' raw values.
Extracted as standalone lemma to keep elaboration context simple. -/
private lemma coarse_cell_le_fine_sum [DecidableEq M] {A : Type*}
    (dp : Core.DecisionTheory.DecisionProblem M A)
    (q : QUD M) (worlds : Finset M) (actions : Finset A)
    (c' : Finset M) (hdecomp : c' = ((q.toCellsFinset worlds).filter (· ⊆ c')).biUnion id)
    (hdisj : ((q.toCellsFinset worlds).filter (· ⊆ c') : Set (Finset M)).PairwiseDisjoint id) :
    (if h : actions.Nonempty then
      actions.sup' h (fun a => c'.sum (fun w => dp.prior w * dp.utility w a))
    else 0) ≤
    ((q.toCellsFinset worlds).filter (· ⊆ c')).sum (fun cell =>
      if h : actions.Nonempty then
        actions.sup' h (fun a => cell.sum (fun w => dp.prior w * dp.utility w a))
      else 0) := by
  by_cases hne : actions.Nonempty
  · rw [dif_pos hne]
    -- Decompose c'.sum into sum over fine cells via biUnion
    have hsum_eq : ∀ (g : M → ℚ), c'.sum g =
        ((q.toCellsFinset worlds).filter (· ⊆ c')).sum (fun cell => cell.sum g) := by
      intro g; conv_lhs => rw [hdecomp]
      rw [Finset.sum_biUnion (f := g) hdisj]; simp only [id]
    -- Rewrite LHS: replace c'.sum with sum-of-cell-sums inside sup'
    have hlhs : actions.sup' hne (fun a => c'.sum (fun w => dp.prior w * dp.utility w a)) =
        actions.sup' hne (fun a => ((q.toCellsFinset worlds).filter (· ⊆ c')).sum
          (fun cell => cell.sum (fun w => dp.prior w * dp.utility w a))) :=
      Finset.sup'_congr hne rfl (fun a _ => hsum_eq _)
    -- Simplify RHS: collapse dites to the positive branch
    have hrhs : ((q.toCellsFinset worlds).filter (· ⊆ c')).sum (fun cell =>
        if h : actions.Nonempty then
          actions.sup' h (fun a => cell.sum (fun w => dp.prior w * dp.utility w a))
        else 0) =
      ((q.toCellsFinset worlds).filter (· ⊆ c')).sum (fun cell =>
        actions.sup' hne (fun a => cell.sum (fun w => dp.prior w * dp.utility w a))) :=
      Finset.sum_congr rfl (fun _ _ => dif_pos hne)
    rw [hlhs, hrhs]
    -- Sub-additivity of max over sum
    exact sup'_finset_sum_le _ _ _ hne
  · rw [dif_neg hne]
    exact le_of_eq (Finset.sum_eq_zero (fun _ _ => dif_neg hne)).symm

open Core.DecisionTheory in
/-- Blackwell's theorem for partitions: finer partitions are always at least
as valuable as coarser ones, for any decision problem.

V_Q(D) ≥ V_{Q'}(D) for all decision problems D, whenever Q ⊑ Q'.

**Proof**: Working directly with raw weighted sums
`Σ_{w∈c} p(w)·u(w,a)`:

1. Each coarse cell's sum decomposes into fine cells (`Finset.sum_biUnion`)
2. Sub-additivity of max: `max_a(Σᵢ fᵢ(a)) ≤ Σᵢ max_a(fᵢ(a))`
3. Regrouping: fine cells grouped by coarse cell = all fine cells -/
theorem blackwell_refinement_value [DecidableEq M] {A : Type*}
    (dp : DecisionProblem M A) (q q' : QUD M)
    (worlds : Finset M) (actions : Finset A)
    (hrefines : q ⊑ q')
    (_hprior : ∀ w, dp.prior w ≥ 0) :
    partitionValue dp q worlds actions ≥ partitionValue dp q' worlds actions := by
  -- Define per-cell value to ensure consistent terms
  let V : Finset M → ℚ := fun cell =>
    if h : actions.Nonempty then
      actions.sup' h (fun a => cell.sum (fun w => dp.prior w * dp.utility w a))
    else 0
  -- partitionValue = (cells).sum V by definition
  change (q.toCellsFinset worlds).sum V ≥ (q'.toCellsFinset worlds).sum V
  -- Step 1: Each coarse cell's value ≤ sum of its fine cells' values
  have hstep : (q'.toCellsFinset worlds).sum V ≤
    (q'.toCellsFinset worlds).sum (fun c' =>
      ((q.toCellsFinset worlds).filter (· ⊆ c')).sum V) :=
    Finset.sum_le_sum (fun c' hc' =>
      coarse_cell_le_fine_sum dp q worlds actions c'
        (coarse_eq_biUnion_fine q q' worlds hrefines c' hc')
        (fine_cells_in_coarse_pairwiseDisjoint q worlds c'))
  -- Step 2: Regroup — Σ_{c'} Σ_{c⊆c'} V(c) = Σ_c V(c)
  have hregroup : (q'.toCellsFinset worlds).sum (fun c' =>
      ((q.toCellsFinset worlds).filter (· ⊆ c')).sum V) =
    (q.toCellsFinset worlds).sum V := by
    rw [← Finset.sum_biUnion (f := V)]
    · congr 1
      ext c; simp only [Finset.mem_biUnion, Finset.mem_filter]
      exact ⟨fun ⟨_, _, hc, _⟩ => hc, fun hc =>
        let ⟨c', hc', hsub⟩ := fine_cell_sub_coarse_finset q q' worlds hrefines c hc
        ⟨c', hc', hc, hsub⟩⟩
    · -- Fiber sets are pairwise disjoint (a fine cell can't be in two coarse groups)
      intro c'₁ hc'₁ c'₂ hc'₂ hne
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro c hc₁ hc₂
      simp only [Finset.mem_filter] at hc₁ hc₂
      have ⟨v, hv⟩ : c.Nonempty := by
        simp only [toCellsFinset, Finset.mem_image] at hc₁
        obtain ⟨w, hw, rfl⟩ := hc₁.1
        exact ⟨w, Finset.mem_filter.mpr ⟨hw, q.refl w⟩⟩
      exfalso; apply hne; by_contra hne'
      exact Finset.disjoint_left.mp
        (toCellsFinset_pairwiseDisjoint q' worlds hc'₁ hc'₂ hne')
        (hc₁.2 hv) (hc₂.2 hv)
  linarith [hregroup]

/-! #### Resolution–Value Saturation -/

open Core.DecisionTheory in
/-- Resolution–Value Saturation: when every cell of partition Q has a
dominant action, Q's partition value equals the exact partition's value.

This is the mathematical core of @cite{van-rooy-2003}: resolving
partitions achieve the same value as the finest partition, so
coarsening from G&S exhaustive answers to mention-some answers
is decision-theoretically free.

**Proof**: Blackwell gives ≤ (exact refines all). For ≥, the dominant
action achieves the pointwise maximum at every world in the cell,
making the sub-additivity inequality tight. -/
theorem resolution_value_eq_exact [Fintype M] [DecidableEq M]
    {A : Type*} [DecidableEq A]
    (dp : DecisionProblem M A) (q : QUD M) (actions : Finset A)
    (hResolves : ∀ cell ∈ q.toCellsFinset Finset.univ,
      ∃ a ∈ actions, ∀ b ∈ actions, ∀ w ∈ cell,
        dp.utility w a ≥ dp.utility w b)
    (hPrior : ∀ w, dp.prior w ≥ 0) :
    partitionValue dp q Finset.univ actions =
    partitionValue dp QUD.exact Finset.univ actions := by
  apply le_antisymm
  · -- ≤: Blackwell (exact refines q, so partitionValue exact ≥ partitionValue q)
    exact blackwell_refinement_value dp exact q Finset.univ actions
      (exact_refines_all q) hPrior
  · -- ≥: resolution makes Blackwell's sub-additivity tight
    unfold partitionValue
    by_cases hne : actions.Nonempty
    · simp only [dif_pos hne]
      -- Abbreviation
      set f : M → A → ℚ := fun w a => dp.prior w * dp.utility w a with hf_def
      -- Step 1: Exact partition value = sum over worlds of pointwise max
      -- (exact cells are singletons)
      have h_filter_singleton : ∀ w : M,
          (Finset.univ : Finset M).filter (fun v => QUD.exact.sameAnswer w v) = {w} := by
        intro w; ext v
        rw [Finset.mem_filter, Finset.mem_singleton, QUD.exact_sameAnswer_iff]
        exact ⟨fun h => h.2.symm, fun h => ⟨Finset.mem_univ _, h.symm⟩⟩
      have h_exact_rw :
          (QUD.exact.toCellsFinset Finset.univ).sum
            (fun cell => actions.sup' hne (fun a => cell.sum (fun w => f w a))) =
          Finset.univ.sum (fun w => actions.sup' hne (f w)) := by
        unfold toCellsFinset
        rw [Finset.sum_image (fun w₁ _ w₂ _ h => by
          have hw₁ : w₁ ∈ Finset.univ.filter (fun v => exact.sameAnswer w₁ v) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, exact.refl w₁⟩
          rw [h] at hw₁; rw [h_filter_singleton] at hw₁
          exact Finset.mem_singleton.mp hw₁)]
        apply Finset.sum_congr rfl; intro w _
        congr 1; ext a; rw [h_filter_singleton, Finset.sum_singleton]
      rw [h_exact_rw]
      -- Step 2: Decompose sum over worlds into sum over q-cells
      conv_lhs => rw [← toCellsFinset_covers q Finset.univ]
      rw [Finset.sum_biUnion (toCellsFinset_pairwiseDisjoint q Finset.univ)]
      -- Goal: (q cells).sum (cell.sum pointwiseMax) ≤ (q cells).sum (sup' cellSum)
      apply Finset.sum_le_sum
      intro cell hcell
      obtain ⟨a_dom, ha_dom, h_dom⟩ := hResolves cell hcell
      -- Dominant action achieves pointwise max: sup'_a [f w a] = f w a_dom
      have h_ptwise : ∀ w ∈ cell,
          actions.sup' hne (f w) = f w a_dom := by
        intro w hw
        apply le_antisymm
        · exact Finset.sup'_le hne _ (fun a ha => by
            simp only [hf_def]
            exact mul_le_mul_of_nonneg_left (h_dom a ha w hw) (hPrior w))
        · exact Finset.le_sup' _ ha_dom
      -- cell.sum pointwiseMax = cell.sum (f · a_dom) ≤ sup' (cell.sum (f · ·))
      calc cell.sum (fun w => actions.sup' hne (f w))
          = cell.sum (fun w => f w a_dom) :=
            Finset.sum_congr rfl (fun w hw => h_ptwise w hw)
        _ ≤ actions.sup' hne (fun a => cell.sum (fun w => f w a)) :=
            Finset.le_sup' (f := fun a => cell.sum (fun w => f w a)) ha_dom
    · -- Empty actions: both sides are 0
      simp [dif_neg hne]

/-! #### Blackwell characterization -/

set_option maxHeartbeats 1600000 in
open Core.DecisionTheory in
/-- Helper: when q merges w,v but q' separates them, a witness DP achieves
strictly higher value under q' than q.

The DP has uniform prior (1/2 each) with utility rewarding correct identification.
Under q (merged cell {w,v}): best raw sum = max(1/2, 1/2) = 1/2.
Under q' (separate cells {w}, {v}): each cell's best raw sum = 1/2, total = 1. -/
private theorem witness_dp_beats_merged [DecidableEq M]
    (q q' : QUD M) (w v : M)
    (hwv_q : q.sameAnswer w v = true)
    (hwv_q'f : q'.sameAnswer w v = false)
    (hvw_q'f : q'.sameAnswer v w = false) :
    ¬ (partitionValue
        { utility := fun m a =>
            if a then (if q'.sameAnswer w m then 1 else 0)
            else (if q'.sameAnswer v m then 1 else 0)
          prior := fun _ => (1 : ℚ) / 2 }
        q {w, v} {true, false} ≥
       partitionValue
        { utility := fun m a =>
            if a then (if q'.sameAnswer w m then 1 else 0)
            else (if q'.sameAnswer v m then 1 else 0)
          prior := fun _ => (1 : ℚ) / 2 }
        q' {w, v} {true, false}) := by
  intro hge
  have hne : w ≠ v := by intro h; subst h; simp [q'.refl] at hwv_q'f
  have hvw_q : q.sameAnswer v w = true := by rw [q.symm]; exact hwv_q
  -- Helper: all pairs pass q.sameAnswer
  have hq_all : ∀ m ∈ ({w, v} : Finset M), ∀ n ∈ ({w, v} : Finset M),
      q.sameAnswer m n = true := by
    intro m hm n hn
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm hn
    obtain hm | hm := hm <;> obtain hn | hn := hn <;> subst m <;> subst n
    exacts [q.refl w, hwv_q, hvw_q, q.refl v]
  -- Cell structure under q: single cell {w,v}
  have hcells_q : q.toCellsFinset {w, v} = {{w, v}} := by
    unfold toCellsFinset
    simp only [Finset.image_insert, Finset.image_singleton,
      Finset.filter_true_of_mem (fun n hn => hq_all w (Finset.mem_insert_self _ _) n hn),
      Finset.filter_true_of_mem (fun n hn => hq_all v
        (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))) n hn),
      Finset.insert_eq_of_mem (Finset.mem_singleton_self _)]
  -- Cell structure under q': two cells {w} and {v}
  have hcells_q' : q'.toCellsFinset {w, v} = {{w}, {v}} := by
    unfold toCellsFinset
    have hf1 : ({w, v} : Finset M).filter (fun n => q'.sameAnswer w n) = {w} := by
      ext m; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro ⟨hm, hsa⟩; obtain rfl | rfl := hm
        · rfl
        · simp [hwv_q'f] at hsa
      · intro h; subst m; exact ⟨Or.inl rfl, q'.refl w⟩
    have hf2 : ({w, v} : Finset M).filter (fun n => q'.sameAnswer v n) = {v} := by
      ext m; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro ⟨hm, hsa⟩; obtain rfl | rfl := hm
        · simp [hvw_q'f] at hsa
        · rfl
      · intro h; subst m; exact ⟨Or.inr rfl, q'.refl v⟩
    simp only [Finset.image_insert, Finset.image_singleton, hf1, hf2]
  -- Unfold and rewrite cells
  unfold partitionValue at hge
  rw [hcells_q, hcells_q'] at hge
  -- Simplify sums, sups, dites, and sameAnswer evaluations
  have hane : ({true, false} : Finset Bool).Nonempty := ⟨true, Finset.mem_insert_self _ _⟩
  have hfne : ({false} : Finset Bool).Nonempty := ⟨false, Finset.mem_singleton_self _⟩
  simp only [
    Finset.sum_singleton,
    Finset.sum_insert (Finset.mem_singleton.not.mpr
      (show ({w} : Finset M) ≠ {v} from fun h => hne (Finset.singleton_injective h))),
    Finset.sum_insert (Finset.mem_singleton.not.mpr hne),
    dif_pos hane,
    Finset.sup'_insert (H := hfne), Finset.sup'_singleton,
    q'.refl, hwv_q'f, hvw_q'f
  ] at hge
  norm_num at hge

set_option maxHeartbeats 1600000 in
open Core.DecisionTheory in
/-- Blackwell ordering characterizes refinement: Q refines Q' if and only if
Q is at least as valuable as Q' for every decision problem.

This is the converse of `blackwell_refinement_value`: if Q is always at
least as valuable, then Q must refine Q'. Together they establish that
partition refinement IS Blackwell ordering.

**Proof** (contrapositive): Suppose `q` does not refine `q'`, i.e.,
∃ w v with `q.sameAnswer w v = true` but `q'.sameAnswer w v = false`.
Construct a DP over `worlds = {w, v}` with two actions where distinguishing
w from v matters. Then q' achieves value 1 while q achieves 1/2. -/
theorem blackwell_characterizes_refinement [DecidableEq M]
    (q q' : QUD M)
    (h : ∀ (worlds : Finset M) (A : Type) [DecidableEq A] (dp : DecisionProblem M A) (actions : Finset A),
      (∀ w, dp.prior w ≥ 0) →
      partitionValue dp q worlds actions ≥ partitionValue dp q' worlds actions) :
    q ⊑ q' := by
  intro w v hwv_q
  by_contra hwv_q'
  have hwv_q'f : q'.sameAnswer w v = false := by
    cases h' : q'.sameAnswer w v with
    | false => rfl
    | true => exact absurd h' hwv_q'
  have hvw_q'f : q'.sameAnswer v w = false := by
    rw [q'.symm]; exact hwv_q'f
  exact witness_dp_beats_merged q q' w v hwv_q hwv_q'f hvw_q'f
    (h {w, v} Bool
      { utility := fun m a =>
          if a then (if q'.sameAnswer w m then 1 else 0)
          else (if q'.sameAnswer v m then 1 else 0)
        prior := fun _ => (1 : ℚ) / 2 }
      {true, false}
      (by intro _; norm_num))

/-! #### Question Utility Bridge

Connect Finset-based `questionUtility` (from `Core.DecisionTheory`) to
Finset-based `partitionValue`. The algebraic identity:

  questionUtility dp actions (q.toCellsFinset Finset.univ)
    = partitionValue dp q Finset.univ actions
    - dpValue dp actions * (Finset.univ : Finset M).sum dp.prior

under non-negative priors. Since `dpValue * totalPrior` is
partition-independent, the Blackwell ordering on `partitionValue`
transfers directly to `questionUtility`. -/

section QuestionUtilityBridge

variable {M : Type*}

/-! ##### Per-cell equivalence -/

open Core.DecisionTheory in
/-- P(c) × valueAfterLearning(c) = the per-cell term in `partitionValue`. -/
private theorem cellProb_mul_valueAfterLearning [DecidableEq M] {A : Type*} [DecidableEq A]
    (dp : DecisionProblem M A) (cell : Finset M) (actions : Finset A)
    (hprior : ∀ w, dp.prior w ≥ 0) :
    cellProbability dp cell * valueAfterLearning dp actions cell =
    (if h : actions.Nonempty then
      actions.sup' h (fun a => cell.sum (fun w => dp.prior w * dp.utility w a))
    else 0) := by
  unfold cellProbability valueAfterLearning
  by_cases hne : actions.Nonempty
  · rw [dif_pos hne, dif_pos hne]
    have hP_nonneg : 0 ≤ cell.sum dp.prior :=
      Finset.sum_nonneg (fun w _ => hprior w)
    rw [Finset.mul₀_sup' hP_nonneg]
    exact Finset.sup'_congr hne rfl fun a _ =>
      cellProb_mul_conditionalEU dp cell a hprior
  · rw [dif_neg hne, dif_neg hne, mul_zero]

/-! ##### Cells partition Finset.univ -/

/-- The sum of cell probabilities equals total prior (cells partition the universe). -/
private theorem toCells_totalProb [Fintype M] [DecidableEq M] {A : Type*}
    (dp : Core.DecisionTheory.DecisionProblem M A) (q : QUD M) :
    (q.toCellsFinset (Finset.univ : Finset M)).sum
      (fun cell => Core.DecisionTheory.cellProbability dp cell) =
    (Finset.univ : Finset M).sum dp.prior := by
  simp only [Core.DecisionTheory.cellProbability]
  conv_rhs => rw [← toCellsFinset_covers q (Finset.univ : Finset M)]
  exact (Finset.sum_biUnion (f := dp.prior)
    (toCellsFinset_pairwiseDisjoint q (Finset.univ : Finset M))).symm

/-! ##### Main bridge theorem -/

open Core.DecisionTheory in
/-- Blackwell ordering on `questionUtility` for QUD-derived questions.

Refinement implies higher question utility (with non-negative priors).

**Proof**: `questionUtility = partitionValue - dpValue × totalPrior`.
Since `dpValue` and `totalPrior` are partition-independent, the ordering
on `partitionValue` (from `blackwell_refinement_value`) transfers. -/
theorem questionUtility_refinement_ge [Fintype M] [DecidableEq M]
    {A : Type*} [DecidableEq A]
    (dp : DecisionProblem M A) (q q' : QUD M) (actions : Finset A)
    (hRefines : q ⊑ q') (hprior : ∀ w, dp.prior w ≥ 0) :
    questionUtility dp actions (q.toCellsFinset Finset.univ) ≥
    questionUtility dp actions (q'.toCellsFinset Finset.univ) := by
  unfold questionUtility
  simp only [utilityValue]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  simp_rw [mul_comm (cellProbability dp _) (dpValue dp actions),
           ← Finset.mul_sum]
  rw [toCells_totalProb dp q, toCells_totalProb dp q']
  linarith [show (q.toCellsFinset (Finset.univ : Finset M)).sum
      (fun cell => cellProbability dp cell * valueAfterLearning dp actions cell) ≥
    (q'.toCellsFinset (Finset.univ : Finset M)).sum
      (fun cell => cellProbability dp cell * valueAfterLearning dp actions cell) from by
    simp_rw [cellProb_mul_valueAfterLearning dp _ actions hprior]
    exact blackwell_refinement_value dp q q' Finset.univ actions hRefines hprior]

open Core.DecisionTheory in
/-- `questionUtility` ordering implies `partitionValue` ordering on `Finset.univ`.

The identity `questionUtility(q) = partitionValue(q, univ) - dpValue × totalPrior`
means the partition-independent constant cancels in comparisons. -/
theorem partitionValue_ge_of_questionUtility_ge [Fintype M] [DecidableEq M]
    {A : Type*} [DecidableEq A]
    (dp : DecisionProblem M A) (q q' : QUD M) (actions : Finset A)
    (hprior : ∀ w, dp.prior w ≥ 0)
    (hQU : questionUtility dp actions (q.toCellsFinset Finset.univ) ≥
           questionUtility dp actions (q'.toCellsFinset Finset.univ)) :
    partitionValue dp q Finset.univ actions ≥ partitionValue dp q' Finset.univ actions := by
  unfold questionUtility at hQU
  simp only [utilityValue] at hQU
  simp_rw [mul_sub] at hQU
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib] at hQU
  simp_rw [mul_comm (cellProbability dp _) (dpValue dp actions), ← Finset.mul_sum] at hQU
  rw [toCells_totalProb dp q, toCells_totalProb dp q'] at hQU
  simp_rw [cellProb_mul_valueAfterLearning dp _ actions hprior] at hQU
  unfold partitionValue
  linarith

/-! ##### Partition value restricted to prior support

When priors are zero outside a subset S, the partition value over the full
universe equals the partition value over S. This bridges from `questionUtility`
(which operates over `Finset.univ`) to `partitionValue` over arbitrary
world sets (needed by `blackwell_characterizes_refinement`). -/

open Core.DecisionTheory in
/-- Per-cell value depends only on worlds with nonzero prior.

If priors are zero outside S, the raw weighted sum over `cell` equals
the raw weighted sum over `cell ∩ S`. -/
private lemma cell_value_restrict_support [DecidableEq M] {A : Type*}
    (dp : DecisionProblem M A) (cell S : Finset M) (a : A)
    (hsupp : ∀ w, w ∉ S → dp.prior w = 0) :
    cell.sum (fun w => dp.prior w * dp.utility w a) =
    (cell ∩ S).sum (fun w => dp.prior w * dp.utility w a) := by
  have hsplit : cell.sum (fun w => dp.prior w * dp.utility w a) =
      (cell \ S).sum (fun w => dp.prior w * dp.utility w a) +
      (cell ∩ S).sum (fun w => dp.prior w * dp.utility w a) := by
    rw [← Finset.sum_union (Finset.disjoint_sdiff_inter cell S),
        Finset.sdiff_union_inter]
  rw [hsplit]
  suffices h : (cell \ S).sum (fun w => dp.prior w * dp.utility w a) = 0 by linarith
  apply Finset.sum_eq_zero; intro w hw
  simp only [Finset.mem_sdiff] at hw
  rw [hsupp w hw.2, zero_mul]

open Core.DecisionTheory in
/-- Partition value restricted to prior support.

When priors are zero outside S, `partitionValue` over `Finset.univ` equals
`partitionValue` over S. Cells not intersecting S contribute zero (all priors
are 0). Cells intersecting S have the same per-cell value as the S-restricted
cells. The bijection between nonempty-in-S cells and `toCellsFinset S`
reindexes the sum. -/
theorem partitionValue_restrict_support [Fintype M] [DecidableEq M] {A : Type*}
    (dp : DecisionProblem M A) (q : QUD M) (S : Finset M) (actions : Finset A)
    (hsupp : ∀ w, w ∉ S → dp.prior w = 0) :
    partitionValue dp q Finset.univ actions = partitionValue dp q S actions := by
  -- Per-cell value function
  set V : Finset M → ℚ := fun cell =>
    if h : actions.Nonempty then
      actions.sup' h (fun a => cell.sum (fun w => dp.prior w * dp.utility w a))
    else 0
  change (q.toCellsFinset Finset.univ).sum V = (q.toCellsFinset S).sum V
  -- Step 1: For each cell c of Finset.univ, V(c) = V(c ∩ S)
  have hV_restrict : ∀ c ∈ q.toCellsFinset Finset.univ, V c = V (c ∩ S) := by
    intro c _; simp only [V]
    by_cases hne : actions.Nonempty
    · rw [dif_pos hne, dif_pos hne]
      exact Finset.sup'_congr hne rfl (fun a _ => cell_value_restrict_support dp c S a hsupp)
    · rw [dif_neg hne, dif_neg hne]
  -- Step 2: Split Finset.univ cells into those intersecting S and those not
  haveI : DecidablePred (fun c : Finset M => (c ∩ S).Nonempty) := fun c =>
    decidable_of_iff ((c ∩ S) ≠ ∅) Finset.nonempty_iff_ne_empty.symm
  have hsplit : (q.toCellsFinset Finset.univ).sum V =
      ((q.toCellsFinset Finset.univ).filter (fun c => (c ∩ S).Nonempty)).sum V +
      ((q.toCellsFinset Finset.univ).filter (fun c => ¬(c ∩ S).Nonempty)).sum V := by
    rw [← Finset.sum_filter_add_sum_filter_not (p := fun c => (c ∩ S).Nonempty)]
  rw [hsplit]
  -- Empty cells contribute 0
  have hempty : ((q.toCellsFinset Finset.univ).filter (fun c => ¬(c ∩ S).Nonempty)).sum V = 0 := by
    apply Finset.sum_eq_zero; intro c hc
    simp only [Finset.mem_filter, Finset.not_nonempty_iff_eq_empty] at hc
    have hV0 : V c = V (c ∩ S) := hV_restrict c hc.1
    show V c = 0
    rw [hV0, hc.2]
    -- V ∅ = 0
    show (if h : actions.Nonempty then
      actions.sup' h (fun a => (∅ : Finset M).sum (fun w => dp.prior w * dp.utility w a))
    else 0) = 0
    by_cases hne : actions.Nonempty
    · rw [dif_pos hne]
      have : (fun a => (∅ : Finset M).sum (fun w => dp.prior w * dp.utility w a)) = fun _ => (0 : ℚ) := by
        ext; exact Finset.sum_empty
      rw [this]; exact Finset.sup'_const hne 0
    · rw [dif_neg hne]
  rw [hempty, add_zero]
  -- Now show the nonempty-intersection cells biject with toCellsFinset S
  -- with matching values V(c) = V(c ∩ S) = V(d)
  -- Map: c ↦ c ∩ S
  apply Finset.sum_nbij (fun c => c ∩ S)
  · -- Maps into toCellsFinset S
    intro c hc
    simp only [Finset.mem_filter] at hc
    obtain ⟨hcm, hne⟩ := hc
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hcm
    simp only [toCellsFinset]
    obtain ⟨v, hv⟩ := hne
    have hvS : v ∈ S := (Finset.mem_inter.mp hv).2
    have hwv : q.sameAnswer w v = true :=
      (Finset.mem_filter.mp (Finset.mem_inter.mp hv).1).2
    exact Finset.mem_image.mpr ⟨v, hvS, by
      ext u; constructor
      · intro hu
        have hmf := Finset.mem_filter.mp hu
        exact Finset.mem_inter.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, q.trans w v u hwv hmf.2⟩, hmf.1⟩
      · intro hu
        have ⟨hfu, hsu⟩ := Finset.mem_inter.mp hu
        have hwu := (Finset.mem_filter.mp hfu).2
        exact Finset.mem_filter.mpr ⟨hsu, q.trans v w u (by rw [q.symm]; exact hwv) hwu⟩⟩
  · -- Injective
    intro c1 hc1 c2 hc2 heq
    obtain ⟨hc1m, hne1⟩ := Finset.mem_filter.mp hc1
    obtain ⟨hc2m, _⟩ := Finset.mem_filter.mp hc2
    obtain ⟨w1, _, rfl⟩ := Finset.mem_image.mp hc1m
    obtain ⟨w2, _, rfl⟩ := Finset.mem_image.mp hc2m
    obtain ⟨v, hv⟩ := hne1
    -- v ∈ c1 ∩ S, so v ∈ c2 ∩ S by heq (beta-reduce for ▸)
    have heq' : (Finset.univ.filter (fun u => q.sameAnswer w1 u)) ∩ S =
        (Finset.univ.filter (fun u => q.sameAnswer w2 u)) ∩ S := heq
    have hv2 : v ∈ (Finset.univ.filter (fun u => q.sameAnswer w2 u)) ∩ S := heq' ▸ hv
    have h1v := (Finset.mem_filter.mp (Finset.mem_inter.mp hv).1).2
    have h2v := (Finset.mem_filter.mp (Finset.mem_inter.mp hv2).1).2
    have h12 : q.sameAnswer w1 w2 = true :=
      q.trans w1 v w2 h1v (by rw [q.symm]; exact h2v)
    ext u; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => q.trans w2 w1 u (by rw [q.symm]; exact h12) h,
           fun h => q.trans w1 w2 u h12 h⟩
  · -- Surjective
    intro d hd
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hd
    refine ⟨Finset.univ.filter (fun v => q.sameAnswer w v), ?_, ?_⟩
    · exact Finset.mem_filter.mpr
        ⟨Finset.mem_image.mpr ⟨w, Finset.mem_univ _, rfl⟩,
         ⟨w, Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, q.refl w⟩, hw⟩⟩⟩
    · ext u; simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun ⟨h1, h2⟩ => ⟨h2, h1⟩, fun ⟨h1, h2⟩ => ⟨h2, h1⟩⟩
  · -- Values match: V(c) = V(c ∩ S)
    intro c hc; simp only [Finset.mem_filter] at hc
    exact hV_restrict c hc.1

open Core.DecisionTheory in
/-- `partitionValue` depends only on `dp.prior` and `dp.utility` within `worlds`.

If two DPs agree on all worlds in `worlds`, they produce the same partition value,
because each cell in `toCellsFinset worlds` is a subset of `worlds`. -/
theorem partitionValue_congr_on_worlds [DecidableEq M] {A : Type*}
    (dp dp' : DecisionProblem M A) (q : QUD M) (worlds : Finset M) (actions : Finset A)
    (h : ∀ w ∈ worlds, dp.prior w = dp'.prior w ∧ ∀ a, dp.utility w a = dp'.utility w a) :
    partitionValue dp q worlds actions = partitionValue dp' q worlds actions := by
  unfold partitionValue
  apply Finset.sum_congr rfl; intro cell hcell
  by_cases hne : actions.Nonempty
  · rw [dif_pos hne, dif_pos hne]
    apply Finset.sup'_congr hne rfl; intro a _
    apply Finset.sum_congr rfl; intro w hw
    obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hcell
    have hw_in : w ∈ worlds := (Finset.mem_filter.mp hw).1
    have ⟨hpr, hut⟩ := h w hw_in
    rw [hpr, hut]
  · rw [dif_neg hne, dif_neg hne]

/-! ##### QUD question utility non-negativity -/

/-- The trivial QUD has exactly one cell for `toCellsFinset Finset.univ`. -/
private lemma trivial_toCellsFinset_univ [Fintype M] [DecidableEq M] [Nonempty M] :
    (QUD.trivial (M := M)).toCellsFinset Finset.univ = {Finset.univ} := by
  simp only [toCellsFinset]
  ext s; constructor
  · intro hs
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hs
    simp only [Finset.mem_singleton]
    ext u; simp [QUD.trivial]
  · intro hs
    rw [Finset.mem_singleton.mp hs]
    exact Finset.mem_image.mpr ⟨Classical.arbitrary M, Finset.mem_univ _, by ext u; simp [QUD.trivial]⟩

open Core.DecisionTheory in
/-- QUD-derived `questionUtility` is non-negative under proper priors.

Requires non-negative priors summing to exactly 1 (proper probability).

**Proof**: `questionUtility(q) ≥ questionUtility(trivial)` by Blackwell
(`questionUtility_refinement_ge` + `all_refine_trivial`).
Then `questionUtility(trivial) = 0` because conditioning on the full
universe with `totalProb = 1` yields `conditionalEU = expectedUtility`,
so `valueAfterLearning = dpValue` and `utilityValue = 0`. -/
theorem questionUtility_qud_nonneg [Fintype M] [DecidableEq M]
    {A : Type*} [DecidableEq A]
    (dp : DecisionProblem M A) (q : QUD M) (actions : Finset A)
    (hprior : ∀ w, dp.prior w ≥ 0) (hsum : Finset.univ.sum dp.prior = 1) :
    questionUtility dp actions (q.toCellsFinset Finset.univ) ≥ 0 := by
  have h1 := questionUtility_refinement_ge dp q QUD.trivial actions
    (all_refine_trivial q) hprior
  suffices h2 : questionUtility dp actions
      (QUD.trivial.toCellsFinset Finset.univ) = 0 by linarith
  haveI : Nonempty M := by
    by_contra h; rw [not_nonempty_iff] at h
    simp [Finset.univ_eq_empty] at hsum
  simp only [questionUtility, trivial_toCellsFinset_univ, Finset.sum_singleton, utilityValue]
  suffices h3 : valueAfterLearning dp actions Finset.univ = dpValue dp actions by
    rw [h3, sub_self, mul_zero]
  unfold valueAfterLearning dpValue
  by_cases hne : actions.Nonempty
  · rw [dif_pos hne, dif_pos hne]
    apply Finset.sup'_congr hne rfl
    intro a _
    unfold conditionalEU expectedUtility
    simp only [show Finset.univ.sum dp.prior ≠ 0 from by linarith [hsum], ite_false]
    exact Finset.sum_congr rfl fun w _ => by rw [hsum, div_one]
  · rw [dif_neg hne, dif_neg hne]

end QuestionUtilityBridge

end QUD
