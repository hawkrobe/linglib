import Linglib.Core.Combinatorics.SetFamily.FourFunctions
import Linglib.Core.Order.Hom.Order
import Linglib.Core.Probability.Kernel.OfWeights
import Linglib.Core.Probability.Kernel.Posterior
import Linglib.Core.Probability.UniformOn
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FieldSimp
import Mathlib.Order.UpperLower.Basic

/-!
# Barnett, Griffiths and Hawkins (2022): A pragmatic account of the weak evidence effect

This file formalizes the paper's pragmatic listener for the Stick Contest. A speaker with a
persuasive goal chooses among the true sticks with weight `L0(longer | u)^β`, so a listener who
expects such a speaker discounts what they are shown: the states in which stronger evidence was
available make the speaker's actual choice less likely. The hidden sticks form a distributive
lattice on which *longer* is an upper set and the speaker's share of the shown stick is
antitone, so the FKG inequality gives the discount for every stick and every bias `β ≥ 0`. The
same inequality makes the pragmatic belief monotone in the stick shown, so the evidence that
backfires is always an initial segment of the weakest evidence. The literal listener's beliefs,
the `β = 0` column of the simulation, are ratios of multiset counts.

## Implementation notes

* The model follows the paper's simulation code: the hidden sticks are a multiset of lengths
  `1`–`9`, *longer* is a total of at least `25`, and the speaker normalizes over the five
  positions. The listener's state is the hidden sticks, as in the code's Bayes rule, so the
  speaker enters as the likelihood of the shown stick given them, a finite kernel that is not
  Markov. Normalizing over the distinct true lengths instead, as the paper's speaker equation
  reads, would make the share non-monotone in the hidden sticks.
* A multiset of `n` sticks is a monotone map `Fin n →o Fin 9`, a distributive lattice under the
  pointwise order. Its `Fintype` instance enumerates the sorted vectors one stick at a time, so
  the multiset counts are decided.

## TODO

* The simulation's pragmatic values (a shown `6` backfires at `β = 2`, a shown `9` does not,
  the backfiring range widens with `β`) are numerical and not certified. The `β → ∞` listener
  conditions on the shown stick being the longest, a count ratio under which every stick up to
  `7` backfires; the limit theorem would give the effect for large bias.

## References

* [barnett-griffiths-hawkins-2022]
-/

open Finset Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace BarnettEtAl2022

/-! ### Beliefs under a weight -/

section Belief

variable {X : Type*} [Fintype X] (μ : X → ℝ) (P Q : X → Prop) [DecidablePred P]
  [DecidablePred Q]

/-- The belief in `P` under the weight `μ`. -/
noncomputable def belief : ℝ := (∑ x ∈ univ.filter P, μ x) / ∑ x, μ x

/-- A weight is log-supermodular when it is positively correlated across meets and joins. -/
def LogSupermodular [Lattice X] : Prop := ∀ a b, μ a * μ b ≤ μ (a ⊓ b) * μ (a ⊔ b)

variable {μ P Q}

theorem belief_nonneg (hμ : 0 ≤ μ) : 0 ≤ belief μ P :=
  div_nonneg (sum_nonneg λ x _ => hμ x) (sum_nonneg λ x _ => hμ x)

theorem belief_pos (hμ : 0 ≤ μ) {x : X} (hx : 0 < μ x) (hP : P x) : 0 < belief μ P :=
  div_pos (sum_pos' (λ y _ => hμ y) ⟨x, mem_filter.2 ⟨mem_univ x, hP⟩, hx⟩)
    (sum_pos' (λ y _ => hμ y) ⟨x, mem_univ x, hx⟩)

/-- A weaker event has a smaller belief. -/
theorem belief_le_belief (hμ : 0 ≤ μ) (h : ∀ x, P x → Q x) : belief μ P ≤ belief μ Q :=
  div_le_div_of_nonneg_right
    (sum_le_sum_of_subset_of_nonneg (monotone_filter_right _ λ x _ => h x) λ x _ _ => hμ x)
    (sum_nonneg λ x _ => hμ x)

/-- Scaling the weight leaves beliefs unchanged. -/
theorem belief_mul_const {c : ℝ} (hc : c ≠ 0) : belief (μ * λ _ => c) P = belief μ P := by
  simp only [belief, Pi.mul_apply, ← sum_mul]
  rw [mul_div_mul_right _ _ hc]

private theorem sum_pos_of_sum_mul_pos {s : X → ℝ} (hμ₀ : 0 ≤ μ)
    (hpos : 0 < ∑ x, μ x * s x) : 0 < ∑ x, μ x := by
  refine (sum_nonneg λ x _ => hμ₀ x).lt_of_ne λ h => hpos.ne' ?_
  rw [eq_comm, sum_eq_zero_iff_of_nonneg (λ x _ => hμ₀ x)] at h
  exact sum_eq_zero λ x _ => by rw [h x (mem_univ x), zero_mul]

theorem belief_one : belief 1 P = (univ.filter P).card / Fintype.card X := by
  simp [belief]

private theorem isUpperSet_coe_filter [Preorder X] (hP : IsUpperSet {x | P x}) :
    IsUpperSet ((univ.filter P : Finset X) : Set X) := by simpa using hP

/-- Reweighting by an antitone factor lowers the belief in an upper set, under a
log-supermodular weight. -/
theorem belief_mul_le [DistribLattice X] {s : X → ℝ} (hμ₀ : 0 ≤ μ) (hs₀ : 0 ≤ s)
    (hs : Antitone s) (hP : IsUpperSet {x | P x}) (hμ : LogSupermodular μ)
    (hpos : 0 < ∑ x, μ x * s x) : belief (μ * s) P ≤ belief μ P := by
  classical
  have key := fkg_antitone_isUpperSet hμ₀ hs₀ hs (isUpperSet_coe_filter hP) hμ
  simp only [belief, Pi.mul_apply]
  rw [div_le_div_iff₀ hpos (sum_pos_of_sum_mul_pos hμ₀ hpos)]
  linarith [key]

/-- Reweighting by a monotone factor raises the belief in an upper set, under a
log-supermodular weight. -/
theorem belief_le_belief_mul [DistribLattice X] {s : X → ℝ} (hμ₀ : 0 ≤ μ) (hs₀ : 0 ≤ s)
    (hs : Monotone s) (hP : IsUpperSet {x | P x}) (hμ : LogSupermodular μ)
    (hpos : 0 < ∑ x, μ x * s x) : belief μ P ≤ belief (μ * s) P := by
  classical
  have key := fkg_monotone_isUpperSet hμ₀ hs₀ hs (isUpperSet_coe_filter hP) hμ
  simp only [belief, Pi.mul_apply]
  rw [div_le_div_iff₀ (sum_pos_of_sum_mul_pos hμ₀ hpos) hpos]
  linarith [key]

end Belief

/-! ### Multisets of sticks -/

/-- `n` hidden sticks of lengths `1`–`9`, as a multiset: a monotone map. -/
abbrev Sticks (n : ℕ) := Fin n →o Fin 9

variable {n : ℕ}

instance : DecidablePred (Monotone : (Fin n → Fin 9) → Prop) :=
  λ x => decidable_of_iff (∀ i j, i ≤ j → x i ≤ x j) Iff.rfl

/-- The sticks are sorted and at least `lo`. -/
def SortedFrom (lo : Fin 9) (x : Fin n → Fin 9) : Prop := Monotone x ∧ ∀ i, lo ≤ x i

theorem sortedFrom_cons {lo a : Fin 9} {x : Fin n → Fin 9} :
    SortedFrom lo (vecCons a x) ↔ lo ≤ a ∧ SortedFrom a x := by
  constructor
  · rintro ⟨hm, hlo⟩
    refine ⟨by simpa using hlo 0, ?_, λ i => by simpa using hm (Fin.zero_le i.succ)⟩
    have := hm.comp Fin.strictMono_succ.monotone
    simpa [Function.comp_def] using this
  · rintro ⟨hla, hm, hlo⟩
    refine ⟨?_, λ i => Fin.cases hla (λ j => hla.trans (hlo j)) i⟩
    rw [Fin.monotone_iff_le_succ]
    intro i
    cases n with
    | zero => exact i.elim0
    | succ n =>
      refine Fin.cases ?_ (λ j => ?_) i
      · simpa using hlo 0
      · simpa using Fin.monotone_iff_le_succ.1 hm j

/-- Prepending a stick. -/
private def consEmb (a : Fin 9) : (Fin n → Fin 9) ↪ (Fin (n + 1) → Fin 9) :=
  ⟨vecCons a, λ _ _ h => by simpa using congrArg vecTail h⟩

private theorem pairwiseDisjoint_map_consEmb (s : Set (Fin 9))
    (S : Fin 9 → Finset (Fin n → Fin 9)) :
    s.PairwiseDisjoint λ a => (S a).map (consEmb a) := λ a _ b _ hab =>
  disjoint_left.2 λ x hx hx' => hab (by
    obtain ⟨y, -, rfl⟩ := mem_map.1 hx
    obtain ⟨z, -, hz⟩ := mem_map.1 hx'
    have hz' : vecCons b z = vecCons a y := hz
    simpa using (congrFun hz' 0).symm)

/-- The sorted vectors with entries at least `lo`, enumerated one stick at a time. -/
def sortedVecs : (n : ℕ) → Fin 9 → Finset (Fin n → Fin 9)
  | 0, _ => univ
  | n + 1, lo => (univ.filter (lo ≤ ·)).disjiUnion (λ a => (sortedVecs n a).map (consEmb a))
      (pairwiseDisjoint_map_consEmb _ _)

theorem mem_sortedVecs {lo : Fin 9} {x : Fin n → Fin 9} :
    x ∈ sortedVecs n lo ↔ SortedFrom lo x := by
  induction n generalizing lo with
  | zero => exact ⟨λ _ => ⟨λ i => i.elim0, λ i => i.elim0⟩, λ _ => mem_univ _⟩
  | succ n ih =>
    obtain ⟨a, y, rfl⟩ : ∃ a y, x = vecCons a y := ⟨_, _, (cons_head_tail x).symm⟩
    rw [sortedVecs, mem_disjiUnion, sortedFrom_cons, ← ih]
    constructor
    · rintro ⟨b, hb, hx⟩
      obtain ⟨z, hz, h⟩ := mem_map.1 hx
      have h' : vecCons b z = vecCons a y := h
      obtain ⟨rfl, rfl⟩ : b = a ∧ z = y :=
        ⟨by simpa using congrFun h' 0, by simpa using congrArg vecTail h'⟩
      exact ⟨(mem_filter.1 hb).2, hz⟩
    · rintro ⟨ha, hy⟩
      exact ⟨a, mem_filter.2 ⟨mem_univ _, ha⟩, mem_map_of_mem (consEmb a) hy⟩

instance : Fintype (Sticks n) where
  elems := ((sortedVecs n 0).subtype Monotone).map
    ⟨λ x => ⟨x.1, x.2⟩, λ _ _ h => Subtype.ext (congrArg DFunLike.coe h)⟩
  complete x := mem_map.2
    ⟨⟨x, x.mono⟩, mem_subtype.2 (mem_sortedVecs.2 ⟨x.mono, λ _ => Fin.zero_le _⟩), rfl⟩

instance : MeasurableSpace (Sticks n) := ⊤

instance : DiscreteMeasurableSpace (Sticks n) := ⟨λ _ => trivial⟩

instance : Inhabited (Sticks n) := ⟨⊥⟩

/-! ### The Stick Contest -/

/-- The length of a stick. -/
def length (i : Fin 9) : ℕ := i.val + 1

theorem length_mono : Monotone length := λ _ _ h => Nat.succ_le_succ h

/-- The total length of the hidden sticks. -/
def total (x : Sticks n) : ℕ := ∑ i, length (x i)

theorem total_mono : Monotone (total (n := n)) :=
  λ _ _ h => sum_le_sum λ i _ => length_mono (h i)

/-- The verdict *longer*: the five sticks average at least the midpoint `5`, so with `shown`
the total of the sticks already shown, the hidden ones bring the total to at least `25`. -/
def Long (shown : ℕ) (x : Sticks n) : Prop := 25 ≤ shown + total x

instance (shown : ℕ) : DecidablePred (Long (n := n) shown) := λ _ => Nat.decLe _ _

theorem long_mono {shown shown' : ℕ} (h : shown ≤ shown') {x : Sticks n} (hx : Long shown x) :
    Long shown' x :=
  le_trans hx (Nat.add_le_add_right h _)

theorem isUpperSet_long (shown : ℕ) : IsUpperSet {x : Sticks n | Long shown x} :=
  λ _ _ hxy hx => le_trans hx (Nat.add_le_add_left (total_mono hxy) _)

/-! ### The model -/

private theorem setOf_eq_coe_filter {X : Type*} [Fintype X] (P : X → Prop) [DecidablePred P] :
    {x | P x} = ↑(univ.filter P) := by
  ext
  simp

/-- The literal listener's belief in *longer* after seeing the stick `u`: the hidden sticks
are uniform. -/
noncomputable def literal (u : Fin 9) : ℝ :=
  (uniformOn (Set.univ : Set (Sticks 4))).real {x | Long (length u) x}

/-- The belief in *longer* before any evidence. -/
noncomputable def prior : ℝ := (uniformOn (Set.univ : Set (Sticks 5))).real {w | Long 0 w}

/-- The persuasive weight of showing `u`: the literal support it lends the goal, raised to the
bias `β`. -/
noncomputable def persuasive (β : ℝ) (u : Fin 9) : ℝ := literal u ^ β

/-- The persuasive weight of the hidden sticks: the rivals of the shown stick. -/
noncomputable def rivals (β : ℝ) (x : Sticks 4) : ℝ := ∑ i, persuasive β (x i)

/-- The persuasive speaker's share of showing `u` when the other sticks are `x`. -/
noncomputable def share (β : ℝ) (u : Fin 9) (x : Sticks 4) : ℝ :=
  persuasive β u / (persuasive β u + rivals β x)

theorem literal_eq_belief (u : Fin 9) :
    literal u = belief (1 : Sticks 4 → ℝ) (Long (length u)) := by
  rw [literal, setOf_eq_coe_filter, uniformOn_univ_real_coe_finset, belief_one]

theorem prior_eq_belief : prior = belief (1 : Sticks 5 → ℝ) (Long 0) := by
  rw [prior, setOf_eq_coe_filter, uniformOn_univ_real_coe_finset, belief_one]

theorem literal_nonneg (u : Fin 9) : 0 ≤ literal u := measureReal_nonneg

theorem literal_pos (u : Fin 9) : 0 < literal u := by
  rw [literal_eq_belief]
  refine belief_pos (λ _ => zero_le_one) (x := (⊤ : Sticks 4)) one_pos ?_
  have h : total (⊤ : Sticks 4) = 36 := by decide
  unfold Long
  omega

/-- Literal support for *longer* grows with the stick shown. -/
theorem literal_mono : Monotone literal := λ _ _ h => by
  rw [literal_eq_belief, literal_eq_belief]
  exact belief_le_belief (λ _ => zero_le_one) λ _ => long_mono (length_mono h)

theorem persuasive_pos (β : ℝ) (u : Fin 9) : 0 < persuasive β u :=
  Real.rpow_pos_of_pos (literal_pos u) β

theorem persuasive_mono {β : ℝ} (hβ : 0 ≤ β) : Monotone (persuasive β) := λ _ _ h =>
  Real.rpow_le_rpow (literal_nonneg _) (literal_mono h) hβ

theorem rivals_nonneg (β : ℝ) (x : Sticks 4) : 0 ≤ rivals β x :=
  sum_nonneg λ _ _ => (persuasive_pos β _).le

theorem rivals_mono {β : ℝ} (hβ : 0 ≤ β) : Monotone (rivals β) :=
  λ _ _ hxy => sum_le_sum λ i _ => persuasive_mono hβ (hxy i)

/-- The rivals' weight is modular: meets and joins redistribute the same sticks. -/
theorem rivals_inf_add_sup (β : ℝ) (x y : Sticks 4) :
    rivals β (x ⊓ y) + rivals β (x ⊔ y) = rivals β x + rivals β y := by
  simp only [rivals, ← sum_add_distrib, OrderHom.coe_inf, OrderHom.coe_sup, Pi.inf_apply,
    Pi.sup_apply]
  refine sum_congr rfl λ i _ => ?_
  rcases le_total (x i) (y i) with h | h
  · rw [inf_eq_left.2 h, sup_eq_right.2 h]
  · rw [inf_eq_right.2 h, sup_eq_left.2 h, add_comm]

theorem share_pos (β : ℝ) (u : Fin 9) (x : Sticks 4) : 0 < share β u x :=
  div_pos (persuasive_pos β u)
    (add_pos_of_pos_of_nonneg (persuasive_pos β u) (rivals_nonneg β x))

/-- The share of the shown stick falls as the hidden sticks grow: stronger evidence was
available. -/
theorem share_antitone {β : ℝ} (hβ : 0 ≤ β) (u : Fin 9) : Antitone (share β u) :=
  λ x _ hxy => div_le_div_of_nonneg_left (persuasive_pos β u).le
    (add_pos_of_pos_of_nonneg (persuasive_pos β u) (rivals_nonneg β x))
    (add_le_add le_rfl (rivals_mono hβ hxy))

/-- The share is log-supermodular: a modular denominator spreads less across meets and
joins. -/
theorem share_logSupermodular {β : ℝ} (hβ : 0 ≤ β) (u : Fin 9) :
    LogSupermodular (share β u) := λ x y => by
  have hp := persuasive_pos β u
  have h := rivals_inf_add_sup β x y
  have hx := rivals_mono hβ (inf_le_left : x ⊓ y ≤ x)
  have hy := rivals_mono hβ (inf_le_right : x ⊓ y ≤ y)
  have h₀ := rivals_nonneg β (x ⊓ y)
  simp only [share, div_mul_div_comm]
  refine div_le_div_of_nonneg_left (mul_pos hp hp).le
    (mul_pos (add_pos_of_pos_of_nonneg hp h₀)
      (add_pos_of_pos_of_nonneg hp (rivals_nonneg β _))) ?_
  nlinarith [mul_nonneg (sub_nonneg.2 hx) (sub_nonneg.2 hy)]

/-- The persuasive speaker as the listener sees it: the likelihood of the shown stick given
the hidden sticks, the speaker's share of it among the five. -/
noncomputable def speaker (β : ℝ) : Kernel (Sticks 4) (Fin 9) :=
  Kernel.ofFunOfCountable λ x => ∑ u, ENNReal.ofReal (share β u x) • Measure.dirac u

theorem speaker_apply_singleton (β : ℝ) (x : Sticks 4) (u : Fin 9) :
    speaker β x {u} = ENNReal.ofReal (share β u x) :=
  Measure.sum_smul_dirac_apply_singleton _ u

theorem share_le_one (β : ℝ) (u : Fin 9) (x : Sticks 4) : share β u x ≤ 1 :=
  div_le_one_of_le₀ (le_add_of_nonneg_right (rivals_nonneg β x))
    (add_pos_of_pos_of_nonneg (persuasive_pos β u) (rivals_nonneg β x)).le

instance (β : ℝ) : IsFiniteKernel (speaker β) :=
  ⟨⟨(9 : ℕ), ENNReal.natCast_lt_top 9, λ x => by
    rw [speaker, Kernel.ofFunOfCountable_apply, Measure.finsetSum_apply]
    simp only [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
    calc ∑ u, ENNReal.ofReal (share β u x) ≤ ∑ _u : Fin 9, (1 : ℝ≥0∞) :=
          sum_le_sum λ u _ => ENNReal.ofReal_le_one.2 (share_le_one β u x)
      _ = (9 : ℕ) := by simp⟩⟩

/-- The pragmatic listener: the Bayesian inverse of the speaker against the uniform prior. -/
noncomputable def pragmaticListener (β : ℝ) : Kernel (Fin 9) (Sticks 4) :=
  (speaker β)†(uniformOn Set.univ)

/-- The pragmatic listener's belief in *longer* after seeing `u` from a speaker of bias `β`. -/
noncomputable def pragmatic (β : ℝ) (u : Fin 9) : ℝ :=
  (pragmaticListener β u).real {x | Long (length u) x}

/-- The sticks that backfire at bias `β`: shown, they lower belief in *longer* below the
prior. -/
def backfires (β : ℝ) : Set (Fin 9) := {u | pragmatic β u < prior}

/-- The pragmatic listener's belief is the belief under the speaker's shares. -/
theorem pragmatic_eq_belief (β : ℝ) (u : Fin 9) :
    pragmatic β u = belief (share β u) (Long (length u)) := by
  have hx : ∑ x, speaker β x {u} ≠ 0 := λ h =>
    (ENNReal.ofReal_pos.2 (share_pos β u default)).ne'
      (by simpa [speaker_apply_singleton] using Finset.sum_eq_zero_iff.1 h default (mem_univ _))
  have hs : ∀ x, (ENNReal.ofReal (share β u x)).toReal = share β u x :=
    λ x => ENNReal.toReal_ofReal (share_pos β u x).le
  rw [pragmatic, pragmaticListener, setOf_eq_coe_filter,
    posterior_uniformOn_univ_real_finset _ hx]
  simp only [speaker_apply_singleton, hs]
  rfl

private theorem sum_mul_pos {s t : Sticks 4 → ℝ} (hs : ∀ x, 0 < s x) (ht : ∀ x, 0 < t x) :
    0 < ∑ x, s x * t x :=
  sum_pos (λ x _ => mul_pos (hs x) (ht x)) univ_nonempty

/-- The pragmatic listener discounts every stick: their belief in *longer* is at most the
literal listener's. -/
theorem pragmatic_le_literal {β : ℝ} (hβ : 0 ≤ β) (u : Fin 9) : pragmatic β u ≤ literal u := by
  rw [pragmatic_eq_belief, literal_eq_belief]
  simpa only [one_mul] using
    belief_mul_le (μ := 1) (λ _ => zero_le_one) (λ x => (share_pos β u x).le)
      (share_antitone hβ u) (isUpperSet_long _) (λ _ _ => le_rfl)
      (sum_mul_pos (λ _ => one_pos) (share_pos β u))

/-- Without a persuasive goal the speaker is indifferent among the true sticks and the
pragmatic listener is the literal one. -/
theorem pragmatic_zero (u : Fin 9) : pragmatic 0 u = literal u := by
  have : share 0 u = 1 * λ _ => (1 / 5 : ℝ) := by
    funext x
    simp [share, rivals, persuasive]
    norm_num
  rw [pragmatic_eq_belief, literal_eq_belief, this, belief_mul_const (by norm_num)]

/-- The pragmatic listener's belief in *longer* grows with the stick shown: a longer stick
supports *longer* literally, and the persuasive weight it shifts onto the hidden sticks is
monotone in them. -/
theorem pragmatic_mono {β : ℝ} (hβ : 0 ≤ β) : Monotone (pragmatic β) := by
  intro u v huv
  have hpu := persuasive_pos β u
  have hpv := persuasive_pos β v
  have hpuv := persuasive_mono hβ huv
  let r : Sticks 4 → ℝ := λ x => persuasive β v / persuasive β u *
    ((persuasive β u + rivals β x) / (persuasive β v + rivals β x))
  have hr₀ : ∀ x, 0 < r x := λ x =>
    mul_pos (div_pos hpv hpu) (div_pos (add_pos_of_pos_of_nonneg hpu (rivals_nonneg β x))
      (add_pos_of_pos_of_nonneg hpv (rivals_nonneg β x)))
  have hr : Monotone r := λ x y hxy => by
    have h := rivals_mono hβ hxy
    refine mul_le_mul_of_nonneg_left ?_ (div_pos hpv hpu).le
    rw [div_le_div_iff₀ (add_pos_of_pos_of_nonneg hpv (rivals_nonneg β x))
      (add_pos_of_pos_of_nonneg hpv (rivals_nonneg β y))]
    nlinarith [mul_nonneg (sub_nonneg.2 hpuv) (sub_nonneg.2 h)]
  have hw : share β v = share β u * r := by
    funext x
    have hu := (add_pos_of_pos_of_nonneg hpu (rivals_nonneg β x)).ne'
    have hv := (add_pos_of_pos_of_nonneg hpv (rivals_nonneg β x)).ne'
    simp only [Pi.mul_apply, share, r]
    field_simp
  rw [pragmatic_eq_belief, pragmatic_eq_belief]
  calc belief (share β u) (Long (length u)) ≤ belief (share β u) (Long (length v)) :=
        belief_le_belief (λ x => (share_pos β u x).le) λ _ => long_mono (length_mono huv)
    _ ≤ belief (share β u * r) (Long (length v)) :=
        belief_le_belief_mul (λ x => (share_pos β u x).le) (λ x => (hr₀ x).le) hr
          (isUpperSet_long _) (share_logSupermodular hβ u) (sum_mul_pos (share_pos β u) hr₀)
    _ = belief (share β v) (Long (length v)) := by rw [hw]

/-- The evidence that backfires is an initial segment of the weakest evidence, at every
bias. -/
theorem isLowerSet_backfires {β : ℝ} (hβ : 0 ≤ β) : IsLowerSet (backfires β) :=
  λ _ _ h hu => (pragmatic_mono hβ h).trans_lt hu

/-! ### The literal listener's beliefs -/

theorem card_sticks_four : Fintype.card (Sticks 4) = 495 := by decide +kernel

theorem card_sticks_five : Fintype.card (Sticks 5) = 1287 := by decide +kernel

/-- The multisets of four hidden sticks on which each stick shown makes *longer* true. -/
theorem card_long (u : Fin 9) :
    (univ.filter (Long (length u) : Sticks 4 → Prop)).card =
      ![141, 169, 200, 231, 264, 295, 326, 354, 381] u := by
  revert u
  decide +kernel

/-- The multisets of five sticks that are *longer*. -/
theorem card_long_prior : (univ.filter (Long 0 : Sticks 5 → Prop)).card = 680 := by
  decide +kernel

/-- The literal listener's belief in *longer* for each stick shown: the `β = 0` column of
the simulation. -/
theorem literal_eq :
    literal = ![47/165, 169/495, 40/99, 7/15, 8/15, 59/99, 326/495, 118/165, 127/165] := by
  funext u
  rw [literal_eq_belief, belief_one, card_long, card_sticks_four]
  fin_cases u <;> norm_num

/-- The belief in *longer* before any evidence. -/
theorem prior_eq : prior = 680 / 1287 := by
  rw [prior_eq_belief, belief_one, card_long_prior, card_sticks_five]
  norm_num

/-- A shown `6` is literal evidence for *longer*. -/
theorem literal_six : prior < literal ⟨5, by decide⟩ := by
  rw [prior_eq, literal_eq]
  norm_num

end BarnettEtAl2022
