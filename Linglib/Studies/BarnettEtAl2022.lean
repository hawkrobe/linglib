import Linglib.Core.Combinatorics.SetFamily.FourFunctions
import Linglib.Core.Order.Hom.Order
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FieldSimp
import Mathlib.Order.UpperLower.Basic

/-!
# Barnett, Griffiths and Hawkins (2022): A pragmatic account of the weak evidence effect

This file formalizes the paper's pragmatic listener for the Stick Contest. A speaker with a
persuasive goal chooses among the true sticks with weight `L0(longer | u)^β`, so a listener who
expects such a speaker discounts what they are shown: the states in which stronger evidence was
available make the speaker's actual choice less likely. Conditioned on the shown stick, the
hidden sticks form a distributive lattice on which *longer* is an upper set and the speaker's
share of the shown stick is antitone, so the FKG inequality gives the discount for every stick
and every bias. The same inequality makes the pragmatic belief monotone in the stick shown, so
the evidence that backfires is always an initial segment of the weakest evidence. The
simulation claims are kernel-checked: at `β = 2` a shown `6` lowers belief in *longer* below
the prior while a shown `9` raises it, and the range of backfiring evidence widens with `β`.

## Implementation notes

* The model follows the paper's simulation code: the hidden sticks are a multiset of lengths
  `1`–`9`, *longer* is a total of at least `25`, and the speaker normalizes over the five
  positions.
* A multiset of `n` sticks is a monotone map `Fin n →o Fin 9`, a distributive lattice under the
  pointwise order. Its `Fintype` instance enumerates the sorted vectors one stick at a time, so
  the kernel-checked claims evaluate the listeners directly.

## References

* [barnett-griffiths-hawkins-2022]
-/

open Finset Matrix

namespace BarnettEtAl2022

/-! ### Beliefs under a weight -/

section Belief

variable {X : Type*} [Fintype X] (μ : X → ℚ) (P Q : X → Prop) [DecidablePred P]
  [DecidablePred Q]

/-- The belief in `P` under the weight `μ`. -/
def belief : ℚ := (∑ x ∈ univ.filter P, μ x) / ∑ x, μ x

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
theorem belief_mul_const {c : ℚ} (hc : c ≠ 0) : belief (μ * λ _ => c) P = belief μ P := by
  simp only [belief, Pi.mul_apply, ← sum_mul]
  rw [mul_div_mul_right _ _ hc]

private theorem sum_pos_of_sum_mul_pos {s : X → ℚ} (hμ₀ : 0 ≤ μ)
    (hpos : 0 < ∑ x, μ x * s x) : 0 < ∑ x, μ x := by
  refine (sum_nonneg λ x _ => hμ₀ x).lt_of_ne λ h => hpos.ne' ?_
  rw [eq_comm, sum_eq_zero_iff_of_nonneg (λ x _ => hμ₀ x)] at h
  exact sum_eq_zero λ x _ => by rw [h x (mem_univ x), zero_mul]

private theorem isUpperSet_coe_filter [Preorder X] (hP : IsUpperSet {x | P x}) :
    IsUpperSet ((univ.filter P : Finset X) : Set X) := by simpa using hP

/-- Reweighting by an antitone factor lowers the belief in an upper set, under a
log-supermodular weight. -/
theorem belief_mul_le [DistribLattice X] {s : X → ℚ} (hμ₀ : 0 ≤ μ) (hs₀ : 0 ≤ s)
    (hs : Antitone s) (hP : IsUpperSet {x | P x}) (hμ : LogSupermodular μ)
    (hpos : 0 < ∑ x, μ x * s x) : belief (μ * s) P ≤ belief μ P := by
  classical
  have key := fkg_antitone_isUpperSet hμ₀ hs₀ hs (isUpperSet_coe_filter hP) hμ
  simp only [belief, Pi.mul_apply]
  rw [div_le_div_iff₀ hpos (sum_pos_of_sum_mul_pos hμ₀ hpos)]
  linarith [key]

/-- Reweighting by a monotone factor raises the belief in an upper set, under a
log-supermodular weight. -/
theorem belief_le_belief_mul [DistribLattice X] {s : X → ℚ} (hμ₀ : 0 ≤ μ) (hs₀ : 0 ≤ s)
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

/-! ### The listeners -/

/-- The literal listener's belief in *longer* after seeing the stick `u`. -/
def literal (u : Fin 9) : ℚ := belief (1 : Sticks 4 → ℚ) (Long (length u))

/-- The belief in *longer* before any evidence. -/
def prior : ℚ := belief (1 : Sticks 5 → ℚ) (Long 0)

/-- The persuasive weight of showing `u`: the literal support it lends the goal, raised to the
bias `β`. -/
def persuasive (β : ℕ) (u : Fin 9) : ℚ := literal u ^ β

/-- The persuasive weight of the hidden sticks: the rivals of the shown stick. -/
def rivals (β : ℕ) (x : Sticks 4) : ℚ := ∑ i, persuasive β (x i)

/-- The persuasive speaker's share of showing `u` when the other sticks are `x`. -/
def share (β : ℕ) (u : Fin 9) (x : Sticks 4) : ℚ :=
  persuasive β u / (persuasive β u + rivals β x)

/-- The pragmatic listener's belief in *longer* after seeing `u` from a speaker of bias `β`. -/
def pragmatic (β : ℕ) (u : Fin 9) : ℚ := belief (share β u) (Long (length u))

/-- The sticks that backfire at bias `β`: shown, they lower belief in *longer* below the
prior. -/
def backfires (β : ℕ) : Set (Fin 9) := {u | pragmatic β u < prior}

theorem literal_nonneg (u : Fin 9) : 0 ≤ literal u := belief_nonneg λ _ => zero_le_one

theorem literal_pos (u : Fin 9) : 0 < literal u :=
  belief_pos (λ _ => zero_le_one) (x := ⊤) one_pos (by
    have h : total (⊤ : Sticks 4) = 36 := by decide
    unfold Long
    omega)

/-- Literal support for *longer* grows with the stick shown. -/
theorem literal_mono : Monotone literal := λ _ _ h =>
  belief_le_belief (λ _ => zero_le_one) λ _ => long_mono (length_mono h)

theorem persuasive_pos (β : ℕ) (u : Fin 9) : 0 < persuasive β u := pow_pos (literal_pos u) β

theorem persuasive_mono (β : ℕ) : Monotone (persuasive β) := λ _ _ h =>
  pow_le_pow_left₀ (literal_nonneg _) (literal_mono h) β

theorem rivals_nonneg (β : ℕ) (x : Sticks 4) : 0 ≤ rivals β x :=
  sum_nonneg λ _ _ => (persuasive_pos β _).le

theorem rivals_mono (β : ℕ) : Monotone (rivals β) :=
  λ _ _ hxy => sum_le_sum λ i _ => persuasive_mono β (hxy i)

/-- The rivals' weight is modular: meets and joins redistribute the same sticks. -/
theorem rivals_inf_add_sup (β : ℕ) (x y : Sticks 4) :
    rivals β (x ⊓ y) + rivals β (x ⊔ y) = rivals β x + rivals β y := by
  simp only [rivals, ← sum_add_distrib, OrderHom.coe_inf, OrderHom.coe_sup, Pi.inf_apply,
    Pi.sup_apply]
  refine sum_congr rfl λ i _ => ?_
  rcases le_total (x i) (y i) with h | h
  · rw [inf_eq_left.2 h, sup_eq_right.2 h]
  · rw [inf_eq_right.2 h, sup_eq_left.2 h, add_comm]

theorem share_pos (β : ℕ) (u : Fin 9) (x : Sticks 4) : 0 < share β u x :=
  div_pos (persuasive_pos β u)
    (add_pos_of_pos_of_nonneg (persuasive_pos β u) (rivals_nonneg β x))

/-- The share of the shown stick falls as the hidden sticks grow: stronger evidence was
available. -/
theorem share_antitone (β : ℕ) (u : Fin 9) : Antitone (share β u) := λ x _ hxy =>
  div_le_div_of_nonneg_left (persuasive_pos β u).le
    (add_pos_of_pos_of_nonneg (persuasive_pos β u) (rivals_nonneg β x))
    (add_le_add le_rfl (rivals_mono β hxy))

/-- The share is log-supermodular: a modular denominator spreads less across meets and
joins. -/
theorem share_logSupermodular (β : ℕ) (u : Fin 9) : LogSupermodular (share β u) := λ x y => by
  have hp := persuasive_pos β u
  have h := rivals_inf_add_sup β x y
  have hx := rivals_mono β (inf_le_left : x ⊓ y ≤ x)
  have hy := rivals_mono β (inf_le_right : x ⊓ y ≤ y)
  have h₀ := rivals_nonneg β (x ⊓ y)
  simp only [share, div_mul_div_comm]
  refine div_le_div_of_nonneg_left (mul_pos hp hp).le
    (mul_pos (add_pos_of_pos_of_nonneg hp h₀)
      (add_pos_of_pos_of_nonneg hp (rivals_nonneg β _))) ?_
  nlinarith [mul_nonneg (sub_nonneg.2 hx) (sub_nonneg.2 hy)]

private theorem sum_mul_pos {s t : Sticks 4 → ℚ} (hs : ∀ x, 0 < s x) (ht : ∀ x, 0 < t x) :
    0 < ∑ x, s x * t x :=
  sum_pos (λ x _ => mul_pos (hs x) (ht x)) ⟨⊥, mem_univ _⟩

/-- The pragmatic listener discounts every stick: their belief in *longer* is at most the
literal listener's. -/
theorem pragmatic_le_literal (β : ℕ) (u : Fin 9) : pragmatic β u ≤ literal u := by
  simpa only [pragmatic, literal, one_mul] using
    belief_mul_le (μ := 1) (λ _ => zero_le_one) (λ x => (share_pos β u x).le)
      (share_antitone β u) (isUpperSet_long _) (λ _ _ => le_rfl)
      (sum_mul_pos (λ _ => one_pos) (share_pos β u))

/-- Without a persuasive goal the speaker is indifferent among the true sticks and the
pragmatic listener is the literal one. -/
theorem pragmatic_zero (u : Fin 9) : pragmatic 0 u = literal u := by
  have : share 0 u = 1 * λ _ => (1 / 5 : ℚ) := by
    funext x
    simp [share, rivals, persuasive]
    norm_num
  rw [pragmatic, this, belief_mul_const (by norm_num)]
  rfl

/-- The pragmatic listener's belief in *longer* grows with the stick shown: a longer stick
supports *longer* literally, and the persuasive weight it shifts onto the hidden sticks is
monotone in them. -/
theorem pragmatic_mono (β : ℕ) : Monotone (pragmatic β) := by
  intro u v huv
  have hpu := persuasive_pos β u
  have hpv := persuasive_pos β v
  have hpuv := persuasive_mono β huv
  let r : Sticks 4 → ℚ := λ x => persuasive β v / persuasive β u *
    ((persuasive β u + rivals β x) / (persuasive β v + rivals β x))
  have hr₀ : ∀ x, 0 < r x := λ x =>
    mul_pos (div_pos hpv hpu) (div_pos (add_pos_of_pos_of_nonneg hpu (rivals_nonneg β x))
      (add_pos_of_pos_of_nonneg hpv (rivals_nonneg β x)))
  have hr : Monotone r := λ x y hxy => by
    have h := rivals_mono β hxy
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
  calc pragmatic β u ≤ belief (share β u) (Long (length v)) :=
        belief_le_belief (λ x => (share_pos β u x).le) λ _ => long_mono (length_mono huv)
    _ ≤ belief (share β u * r) (Long (length v)) :=
        belief_le_belief_mul (λ x => (share_pos β u x).le) (λ x => (hr₀ x).le) hr
          (isUpperSet_long _) (share_logSupermodular β u) (sum_mul_pos (share_pos β u) hr₀)
    _ = pragmatic β v := by rw [pragmatic, hw]

/-- The evidence that backfires is an initial segment of the weakest evidence, at every
bias. -/
theorem isLowerSet_backfires (β : ℕ) : IsLowerSet (backfires β) :=
  λ _ _ h hu => (pragmatic_mono β h).trans_lt hu

/-! ### The simulation -/

/-- The literal listener's belief in *longer* for each stick shown. -/
theorem literal_eq :
    literal = ![47/165, 169/495, 40/99, 7/15, 8/15, 59/99, 326/495, 118/165, 127/165] := by
  decide +kernel

/-- The belief in *longer* before any evidence. -/
theorem prior_eq : prior = 680 / 1287 := by decide +kernel

/-- A shown `6` is literal evidence for *longer*. -/
theorem literal_six : prior < literal ⟨5, by decide⟩ := by
  rw [prior_eq, literal_eq]
  norm_num

/-- The weak evidence effect: at `β = 2` a shown `6` lowers belief in *longer* below the
prior. -/
theorem weak_evidence_effect : pragmatic 2 ⟨5, by decide⟩ < prior := by
  rw [prior_eq]
  unfold pragmatic share rivals persuasive
  rw [literal_eq]
  decide +kernel

/-- At `β = 2` every stick up to `6` backfires. -/
theorem Iic_subset_backfires : Set.Iic ⟨5, by decide⟩ ⊆ backfires 2 :=
  λ _ hu => isLowerSet_backfires 2 hu weak_evidence_effect

/-- The strongest evidence cannot be explained away. -/
theorem strongest_evidence : prior < pragmatic 2 ⟨8, by decide⟩ := by
  rw [prior_eq]
  unfold pragmatic share rivals persuasive
  rw [literal_eq]
  decide +kernel

/-- The range of backfiring evidence widens with the bias: a shown `7` supports *longer* at
`β = 2` and backfires at `β = 10`. -/
theorem effect_widens :
    prior < pragmatic 2 ⟨6, by decide⟩ ∧ pragmatic 10 ⟨6, by decide⟩ < prior := by
  rw [prior_eq]
  unfold pragmatic share rivals persuasive
  rw [literal_eq]
  exact ⟨by decide +kernel, by decide +kernel⟩

end BarnettEtAl2022
