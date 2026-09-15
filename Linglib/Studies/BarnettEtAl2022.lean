import Linglib.Core.Combinatorics.SetFamily.FourFunctions
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
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
* A multiset is a sorted vector in `Fin n → Fin 9`, carried as the indicator weight `sorted` so
  that the FKG inequality applies on the product lattice; `sortedSum` enumerates the sorted
  vectors one stick at a time for the kernel-checked claims.

## References

* [barnett-griffiths-hawkins-2022]
-/

open Finset

namespace BarnettEtAl2022

/-! ### Log-supermodular weights -/

section LogSupermodular

variable {X : Type*} [Lattice X] (μ : X → ℚ)

/-- A weight is log-supermodular when it is positively correlated across meets and joins. -/
def LogSupermodular : Prop := ∀ a b, μ a * μ b ≤ μ (a ⊓ b) * μ (a ⊔ b)

variable {μ}

theorem LogSupermodular.mul {ν : X → ℚ} (hμ₀ : 0 ≤ μ) (hν₀ : 0 ≤ ν) (hμ : LogSupermodular μ)
    (hν : LogSupermodular ν) : LogSupermodular (μ * ν) := λ a b => by
  simp only [Pi.mul_apply]
  calc μ a * ν a * (μ b * ν b) = μ a * μ b * (ν a * ν b) := by ring
    _ ≤ μ (a ⊓ b) * μ (a ⊔ b) * (ν (a ⊓ b) * ν (a ⊔ b)) :=
        mul_le_mul (hμ a b) (hν a b) (mul_nonneg (hν₀ _) (hν₀ _)) (mul_nonneg (hμ₀ _) (hμ₀ _))
    _ = _ := by ring

end LogSupermodular

/-! ### Beliefs under a weight -/

section Belief

variable {X : Type*} [Fintype X] (μ : X → ℚ) (P Q : X → Prop) [DecidablePred P]
  [DecidablePred Q]

/-- The belief in `P` under the weight `μ`. -/
def belief : ℚ := (∑ x ∈ univ.filter P, μ x) / ∑ x, μ x

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

/-! ### The Stick Contest -/

/-- `n` hidden sticks of lengths `1`–`9`. -/
abbrev Sticks (n : ℕ) := Fin n → Fin 9

/-- The length of a stick. -/
def length (i : Fin 9) : ℕ := i.val + 1

theorem length_mono : Monotone length := λ _ _ h => Nat.succ_le_succ h

variable {n : ℕ}

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

/-! ### Multisets of sticks as sorted vectors -/

instance : DecidablePred (Monotone : Sticks n → Prop) :=
  λ x => decidable_of_iff (∀ i j, i ≤ j → x i ≤ x j) Iff.rfl

/-- The uniform weight over multisets of hidden sticks: the sorted vectors. -/
def sorted (x : Sticks n) : ℚ := if Monotone x then 1 else 0

theorem sorted_nonneg : 0 ≤ sorted (n := n) := λ x => by unfold sorted; split_ifs <;> norm_num

theorem sorted_logSupermodular : LogSupermodular (sorted (n := n)) := λ a b => by
  by_cases h : Monotone a ∧ Monotone b
  · simp [sorted, h.1, h.2, h.1.inf h.2, h.1.sup h.2]
  · have : sorted a * sorted b = 0 := by
      rcases not_and_or.1 h with h' | h' <;> simp [sorted, h']
    rw [this]
    exact mul_nonneg (sorted_nonneg _) (sorted_nonneg _)

/-- The sticks are sorted and at least `lo`. -/
def SortedFrom (lo : Fin 9) (x : Sticks n) : Prop := Monotone x ∧ ∀ i, lo ≤ x i

instance (lo : Fin 9) : DecidablePred (SortedFrom (n := n) lo) := λ _ => inferInstanceAs
  (Decidable (_ ∧ _))

theorem sortedFrom_cons {lo a : Fin 9} {x : Sticks n} :
    SortedFrom lo (Fin.cons a x) ↔ lo ≤ a ∧ SortedFrom a x := by
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

theorem sortedFrom_zero {x : Sticks n} : SortedFrom 0 x ↔ Monotone x :=
  ⟨And.left, λ h => ⟨h, λ _ => Fin.zero_le _⟩⟩

/-- Summing over the sticks one at a time. -/
theorem sum_sticks_succ (f : Sticks (n + 1) → ℚ) :
    ∑ x, f x = ∑ a, ∑ x : Sticks n, f (Fin.cons a x) := by
  rw [← (Fin.consEquiv λ _ => Fin 9).sum_comp, Fintype.sum_prod_type]
  rfl

/-- The sum of `f` over the sorted vectors at least `lo`, enumerated one stick at a time. -/
def sortedSum : (n : ℕ) → Fin 9 → (Sticks n → ℚ) → ℚ
  | 0, _, f => f default
  | n + 1, lo, f => ∑ a ∈ univ.filter (lo ≤ ·), sortedSum n a λ x => f (Fin.cons a x)

theorem sum_sortedFrom (lo : Fin 9) (f : Sticks n → ℚ) :
    ∑ x, (if SortedFrom lo x then f x else 0) = sortedSum n lo f := by
  induction n generalizing lo with
  | zero =>
    rw [Fintype.sum_unique, ite_eq_left ⟨λ i => i.elim0, λ i => i.elim0⟩]
    exact congrArg f (Subsingleton.elim _ _)
  | succ n ih =>
    rw [sum_sticks_succ, sortedSum, sum_filter]
    refine sum_congr rfl λ a _ => ?_
    by_cases h : lo ≤ a
    · simp only [sortedFrom_cons, h, true_and, ite_true]
      exact ih a _
    · simp [sortedFrom_cons, h]

/-- Beliefs under the multiset weight, computed one stick at a time. -/
theorem belief_sorted_mul (g : Sticks n → ℚ) (P : Sticks n → Prop) [DecidablePred P] :
    belief (sorted * g) P = sortedSum n 0 (λ x => if P x then g x else 0) / sortedSum n 0 g := by
  unfold belief
  rw [sum_filter, ← sum_sortedFrom, ← sum_sortedFrom]
  congr 1 <;> refine sum_congr rfl λ x _ => ?_ <;>
    simp only [Pi.mul_apply, sorted, sortedFrom_zero] <;> split_ifs <;> simp

theorem belief_sorted (P : Sticks n → Prop) [DecidablePred P] :
    belief sorted P = sortedSum n 0 (λ x => if P x then 1 else 0) / sortedSum n 0 1 := by
  simpa only [mul_one, Pi.one_apply] using belief_sorted_mul 1 P

/-! ### The listeners -/

/-- The literal listener's belief in *longer* after seeing the stick `u`. -/
def literal (u : Fin 9) : ℚ := belief (sorted (n := 4)) (Long (length u))

/-- The belief in *longer* before any evidence. -/
def prior : ℚ := belief (sorted (n := 5)) (Long 0)

/-- The persuasive weight of showing `u`: the literal support it lends the goal, raised to the
bias `β`. -/
def persuasive (β : ℕ) (u : Fin 9) : ℚ := literal u ^ β

/-- The persuasive weight of the hidden sticks: the rivals of the shown stick. -/
def rivals (β : ℕ) (x : Sticks 4) : ℚ := ∑ i, persuasive β (x i)

/-- The persuasive speaker's share of showing `u` when the other sticks are `x`. -/
def share (β : ℕ) (u : Fin 9) (x : Sticks 4) : ℚ :=
  persuasive β u / (persuasive β u + rivals β x)

/-- The pragmatic listener's belief in *longer* after seeing `u` from a speaker of bias `β`. -/
def pragmatic (β : ℕ) (u : Fin 9) : ℚ := belief (sorted * share β u) (Long (length u))

/-- The sticks that backfire at bias `β`: shown, they lower belief in *longer* below the
prior. -/
def backfires (β : ℕ) : Set (Fin 9) := {u | pragmatic β u < prior}

theorem literal_nonneg (u : Fin 9) : 0 ≤ literal u := belief_nonneg sorted_nonneg

theorem literal_pos (u : Fin 9) : 0 < literal u :=
  belief_pos sorted_nonneg (x := λ _ => 8) (by simp [sorted, monotone_const]) (by
    have h : total (λ _ : Fin 4 => (8 : Fin 9)) = 36 := by decide
    unfold Long
    omega)

/-- Literal support for *longer* grows with the stick shown. -/
theorem literal_mono : Monotone literal := by
  intro x y h
  unfold literal
  exact belief_le_belief sorted_nonneg λ _ => long_mono (length_mono h)

theorem persuasive_pos (β : ℕ) (u : Fin 9) : 0 < persuasive β u := pow_pos (literal_pos u) β

theorem persuasive_mono (β : ℕ) : Monotone (persuasive β) := by
  intro x y h
  unfold persuasive
  exact pow_le_pow_left₀ (literal_nonneg _) (literal_mono h) β

theorem rivals_nonneg (β : ℕ) (x : Sticks 4) : 0 ≤ rivals β x :=
  sum_nonneg λ _ _ => (persuasive_pos β _).le

theorem rivals_mono (β : ℕ) : Monotone (rivals β) :=
  λ _ _ hxy => sum_le_sum λ i _ => persuasive_mono β (hxy i)

/-- The rivals' weight is modular: meets and joins redistribute the same sticks. -/
theorem rivals_inf_add_sup (β : ℕ) (x y : Sticks 4) :
    rivals β (x ⊓ y) + rivals β (x ⊔ y) = rivals β x + rivals β y := by
  simp only [rivals, ← sum_add_distrib, Pi.inf_apply, Pi.sup_apply]
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

private theorem sum_sorted_mul_pos {s : Sticks 4 → ℚ} (hs : ∀ x, 0 < s x) :
    0 < ∑ x, sorted x * s x :=
  sum_pos' (λ x _ => mul_nonneg (sorted_nonneg x) (hs x).le)
    ⟨λ _ => 0, mem_univ _, mul_pos (by simp [sorted, monotone_const]) (hs _)⟩

/-- The pragmatic listener discounts every stick: their belief in *longer* is at most the
literal listener's. -/
theorem pragmatic_le_literal (β : ℕ) (u : Fin 9) : pragmatic β u ≤ literal u :=
  belief_mul_le sorted_nonneg (λ x => (share_pos β u x).le) (share_antitone β u)
    (isUpperSet_long _) sorted_logSupermodular (sum_sorted_mul_pos (share_pos β u))

/-- Without a persuasive goal the speaker is indifferent among the true sticks and the
pragmatic listener is the literal one. -/
theorem pragmatic_zero (u : Fin 9) : pragmatic 0 u = literal u := by
  have : share 0 u = λ _ => 1 / 5 := by
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
  have hw : sorted * share β v = sorted * share β u * r := by
    funext x
    have hu := (add_pos_of_pos_of_nonneg hpu (rivals_nonneg β x)).ne'
    have hv := (add_pos_of_pos_of_nonneg hpv (rivals_nonneg β x)).ne'
    simp only [Pi.mul_apply, share, r]
    field_simp
  have hw₀ : 0 ≤ sorted * share β u :=
    λ x => mul_nonneg (sorted_nonneg x) (share_pos β u x).le
  calc pragmatic β u ≤ belief (sorted * share β u) (Long (length v)) :=
        belief_le_belief hw₀ λ _ => long_mono (length_mono huv)
    _ ≤ belief (sorted * share β u * r) (Long (length v)) :=
        belief_le_belief_mul hw₀ (λ x => (hr₀ x).le) hr (isUpperSet_long _)
          (sorted_logSupermodular.mul sorted_nonneg (λ x => (share_pos β u x).le)
            (share_logSupermodular β u))
          (by simpa only [Pi.mul_apply, mul_assoc] using
            sum_sorted_mul_pos λ x => mul_pos (share_pos β u x) (hr₀ x))
    _ = pragmatic β v := by rw [pragmatic, hw]

/-- The evidence that backfires is an initial segment of the weakest evidence, at every
bias. -/
theorem isLowerSet_backfires (β : ℕ) : IsLowerSet (backfires β) :=
  λ _ _ h hu => (pragmatic_mono β h).trans_lt hu

/-! ### The simulation -/

/-- The literal listener's belief in *longer* for each stick shown. -/
theorem literal_eq :
    literal = ![47/165, 169/495, 40/99, 7/15, 8/15, 59/99, 326/495, 118/165, 127/165] := by
  funext u
  fin_cases u <;> (rw [literal, belief_sorted]; decide +kernel)

/-- The belief in *longer* before any evidence. -/
theorem prior_eq : prior = 680 / 1287 := by
  rw [prior, belief_sorted]
  decide +kernel

/-- A shown `6` is literal evidence for *longer*. -/
theorem literal_six : prior < literal ⟨5, by decide⟩ := by
  rw [prior_eq, literal_eq]
  norm_num

/-- The weak evidence effect: at `β = 2` a shown `6` lowers belief in *longer* below the
prior. -/
theorem weak_evidence_effect : (⟨5, by decide⟩ : Fin 9) ∈ backfires 2 := by
  show pragmatic _ _ < _
  rw [pragmatic, belief_sorted_mul, prior_eq]
  delta share rivals persuasive
  rw [literal_eq]
  decide +kernel

/-- The strongest evidence cannot be explained away. -/
theorem strongest_evidence : prior < pragmatic 2 ⟨8, by decide⟩ := by
  rw [pragmatic, belief_sorted_mul, prior_eq]
  delta share rivals persuasive
  rw [literal_eq]
  decide +kernel

/-- The range of backfiring evidence widens with the bias: a shown `7` supports *longer* at
`β = 2` and backfires at `β = 10`. -/
theorem effect_widens :
    prior < pragmatic 2 ⟨6, by decide⟩ ∧ pragmatic 10 ⟨6, by decide⟩ < prior := by
  rw [pragmatic, pragmatic, belief_sorted_mul, belief_sorted_mul, prior_eq]
  delta share rivals persuasive
  rw [literal_eq]
  exact ⟨by decide +kernel, by decide +kernel⟩

end BarnettEtAl2022
