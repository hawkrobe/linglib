import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
# Fourier-Motzkin Elimination and Farkas' Lemma over ℚ

Fourier-Motzkin (FM) elimination is a variable-elimination procedure for rational
linear inequalities: given a system Ax ≤ b in n+1 variables, eliminate the last
variable by combining pairs of constraints (one with positive last coefficient,
one with negative) to produce an equisatisfiable system in n variables.

From FM equisatisfiability we derive **Farkas' lemma** over ℚ: a rational linear
system is either feasible or admits a nonneg certificate of infeasibility. This
is the core duality theorem for rational linear programming — no topology, no
completeness, no ℝ detour.

The conceptual backbone is the **Minkowski-Weyl theorem** for rational cones
(H-cone = V-cone), of which Farkas is an immediate corollary.

## Main results

* `fmElim` — one step of FM elimination (eliminate last variable)
* `fmElim_equisat` — FM step preserves feasibility
* `farkas` — Farkas' lemma: feasible ∨ infeasibility certificate
* `minkowskiWeyl_VtoH` — every finitely generated rational cone is polyhedral
* `minkowskiWeyl_HtoV` — every rational polyhedral cone is finitely generated
-/

namespace Polyhedral

-- ═══════════════════════════════════════════════════════════════
-- § 1. Rational Linear Inequalities
-- ═══════════════════════════════════════════════════════════════

/-- Dot product of two rational vectors indexed by `Fin n`. -/
def dot {n : ℕ} (u v : Fin n → ℚ) : ℚ :=
  Finset.univ.sum (fun i => u i * v i)

/-- A linear inequality constraint: lhs · x ≤ rhs. -/
structure Ineq (n : ℕ) where
  lhs : Fin n → ℚ
  rhs : ℚ

/-- A constraint is satisfied by a point x when lhs · x ≤ rhs. -/
def Ineq.sat {n : ℕ} (c : Ineq n) (x : Fin n → ℚ) : Prop :=
  dot c.lhs x ≤ c.rhs

/-- A system of linear inequalities (a list of constraints). -/
abbrev System (n : ℕ) := List (Ineq n)

/-- A system is feasible if some point satisfies every constraint. -/
def System.feasible {n : ℕ} (S : System n) : Prop :=
  ∃ x : Fin n → ℚ, ∀ c ∈ S, c.sat x

-- ═══════════════════════════════════════════════════════════════
-- § 2. Fourier-Motzkin Elimination Step
-- ═══════════════════════════════════════════════════════════════

/-- The last coefficient of a constraint in n+1 variables. -/
def Ineq.lastCoeff {n : ℕ} (c : Ineq (n + 1)) : ℚ := c.lhs (Fin.last n)

/-- Project a constraint to n variables (dropping the last coefficient). -/
def Ineq.project {n : ℕ} (c : Ineq (n + 1)) : Ineq n where
  lhs := fun i => c.lhs (Fin.castSucc i)
  rhs := c.rhs

/-- Combine a positive-last and negative-last constraint, eliminating
    the last variable. -/
def Ineq.combine {n : ℕ} (cp cn : Ineq (n + 1)) : Ineq n where
  lhs := fun i =>
    (-cn.lastCoeff) * cp.lhs (Fin.castSucc i) +
    cp.lastCoeff * cn.lhs (Fin.castSucc i)
  rhs := (-cn.lastCoeff) * cp.rhs + cp.lastCoeff * cn.rhs

/-- One step of FM elimination: partition constraints by sign of the last
    coefficient, project the zero ones, combine all positive × negative pairs. -/
def fmElim {n : ℕ} (S : System (n + 1)) : System n :=
  let zero := S.filter (fun c => decide (c.lastCoeff = 0))
  let pos  := S.filter (fun c => decide (c.lastCoeff > 0))
  let neg  := S.filter (fun c => decide (c.lastCoeff < 0))
  (zero.map Ineq.project) ++
  (pos.flatMap (fun cp => neg.map (fun cn => Ineq.combine cp cn)))

-- ═══════════════════════════════════════════════════════════════
-- § 3. FM Equisatisfiability
-- ═══════════════════════════════════════════════════════════════

/-- Given compatible lower and upper bounds, find a value between them. -/
private theorem compatible_bounds : (lbs ubs : List ℚ) →
    (∀ l ∈ lbs, ∀ u ∈ ubs, l ≤ u) →
    ∃ t : ℚ, (∀ l ∈ lbs, l ≤ t) ∧ (∀ u ∈ ubs, t ≤ u)
  | [], ubs, _ => by
    induction ubs with
    | nil => exact ⟨0, by simp, by simp⟩
    | cons ub ubs' ih =>
      obtain ⟨t₀, _, ht₀⟩ := ih (by simp)
      exact ⟨min ub t₀, by simp, fun u' hu' => by
        rcases List.mem_cons.mp hu' with rfl | hm
        · exact min_le_left _ _
        · exact le_trans (min_le_right _ _) (ht₀ _ hm)⟩
  | lb :: lbs', ubs, h => by
    obtain ⟨t₀, ht₀l, ht₀u⟩ := compatible_bounds lbs' ubs (fun l' hl' u' hu' =>
      h l' (List.mem_cons.mpr (Or.inr hl')) u' hu')
    exact ⟨max lb t₀, fun l' hl' => by
      rcases List.mem_cons.mp hl' with rfl | hm
      · exact le_max_left _ _
      · exact le_trans (ht₀l _ hm) (le_max_right _ _),
    fun u' hu' => max_le (h lb (List.mem_cons.mpr (Or.inl rfl)) u' hu') (ht₀u u' hu')⟩

/-- **FM equisatisfiability**: the original system (n+1 variables) is feasible
    iff the reduced system (n variables) is feasible.

    Forward: project out last coordinate. Backward: find t in the interval
    defined by positive (upper bound) and negative (lower bound) constraints;
    the P×N combinations guarantee the interval is nonempty. -/
theorem fmElim_equisat {n : ℕ} (S : System (n + 1)) :
    S.feasible ↔ (fmElim S).feasible := by
  constructor
  · -- Forward: project out last variable
    rintro ⟨x, hx⟩
    refine ⟨fun i => x (Fin.castSucc i), fun c' hc' => ?_⟩
    simp only [fmElim] at hc'
    rcases List.mem_append.mp hc' with hZ | hPN
    · obtain ⟨c, hcMem, rfl⟩ := List.mem_map.mp hZ
      have hcS := (List.mem_filter.mp hcMem).1
      have hcZero : c.lastCoeff = 0 := by simpa using (List.mem_filter.mp hcMem).2
      have hsat := hx c hcS
      simp only [Ineq.sat, Ineq.project, dot] at hsat ⊢
      rw [Fin.sum_univ_castSucc] at hsat
      simp only [Ineq.lastCoeff] at hcZero
      linarith [mul_eq_zero_of_left hcZero (x (Fin.last n))]
    · rw [List.mem_flatMap] at hPN
      obtain ⟨cp, hcpMem, hm⟩ := hPN
      obtain ⟨cn, hcnMem, rfl⟩ := List.mem_map.mp hm
      have hcpS := (List.mem_filter.mp hcpMem).1
      have hcnS := (List.mem_filter.mp hcnMem).1
      have hp : cp.lastCoeff > 0 := by simpa using (List.mem_filter.mp hcpMem).2
      have hn : cn.lastCoeff < 0 := by simpa using (List.mem_filter.mp hcnMem).2
      have hsp := hx cp hcpS; have hsn := hx cn hcnS
      simp only [Ineq.sat, Ineq.combine, dot] at hsp hsn ⊢
      rw [Fin.sum_univ_castSucc] at hsp hsn
      -- Factor: combined sum = (-aₙ) * Σcₚ + aₚ * Σcₙ
      have hlhs : ∑ i : Fin n,
          ((-cn.lastCoeff) * cp.lhs (Fin.castSucc i) +
           cp.lastCoeff * cn.lhs (Fin.castSucc i)) * x (Fin.castSucc i) =
        (-cn.lastCoeff) * (∑ i : Fin n, cp.lhs (Fin.castSucc i) * x (Fin.castSucc i)) +
        cp.lastCoeff * (∑ i : Fin n, cn.lhs (Fin.castSucc i) * x (Fin.castSucc i)) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro i _; ring
      rw [hlhs]
      -- The cross terms cancel: (-cn.last) * cp.last * x(last) + cp.last * cn.last * x(last) = 0
      have hcancel : (-cn.lastCoeff) * (cp.lhs (Fin.last n) * x (Fin.last n)) +
                     cp.lastCoeff * (cn.lhs (Fin.last n) * x (Fin.last n)) = 0 := by
        show (-cn.lhs (Fin.last n)) * (cp.lhs (Fin.last n) * x (Fin.last n)) +
             cp.lhs (Fin.last n) * (cn.lhs (Fin.last n) * x (Fin.last n)) = 0; ring
      nlinarith [mul_le_mul_of_nonneg_left hsp (le_of_lt (neg_pos.mpr hn)),
                 mul_le_mul_of_nonneg_left hsn (le_of_lt hp)]
  · -- Backward: find t in [max lower bounds, min upper bounds]
    rintro ⟨x', hx'⟩
    -- Compute bounds
    let pos := S.filter (fun c => decide (c.lastCoeff > 0))
    let neg := S.filter (fun c => decide (c.lastCoeff < 0))
    let bnd (c : Ineq (n + 1)) : ℚ := (c.rhs - dot c.project.lhs x') / c.lastCoeff
    -- Show bounds are compatible (every lower ≤ every upper)
    have hcompat : ∀ cn ∈ neg, ∀ cp ∈ pos, bnd cn ≤ bnd cp := by
      intro cn hcn cp hcp
      have hn : cn.lastCoeff < 0 := by simpa using (List.mem_filter.mp hcn).2
      have hp : cp.lastCoeff > 0 := by simpa using (List.mem_filter.mp hcp).2
      have hcomb : (Ineq.combine cp cn).sat x' := by
        apply hx'; simp only [fmElim]
        apply List.mem_append.mpr; right; rw [List.mem_flatMap]
        exact ⟨cp, hcp, List.mem_map.mpr ⟨cn, hcn, rfl⟩⟩
      simp only [Ineq.sat, Ineq.combine, dot] at hcomb
      -- Factor the combined sum into products of individual sums
      have hfact : (-cn.lastCoeff) * (∑ i : Fin n, cp.lhs (Fin.castSucc i) * x' i) +
                   cp.lastCoeff * (∑ i : Fin n, cn.lhs (Fin.castSucc i) * x' i) ≤
                   (-cn.lastCoeff) * cp.rhs + cp.lastCoeff * cn.rhs := by
        convert hcomb using 1
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro i _; ring
      -- Convert bnd cn to positive denominator and apply div_le_div_iff₀
      simp only [bnd, dot, Ineq.project]
      rw [show (cn.rhs - ∑ i : Fin n, cn.lhs (Fin.castSucc i) * x' i) / cn.lastCoeff =
              (∑ i : Fin n, cn.lhs (Fin.castSucc i) * x' i - cn.rhs) / (-cn.lastCoeff)
        from by rw [show cn.rhs - ∑ i : Fin n, cn.lhs (Fin.castSucc i) * x' i =
                         -(∑ i : Fin n, cn.lhs (Fin.castSucc i) * x' i - cn.rhs)
               from by ring]; rw [neg_div, div_neg]]
      rw [div_le_div_iff₀ (neg_pos.mpr hn) hp]
      nlinarith
    -- Find t in the interval
    have hbounds : ∃ t : ℚ, (∀ cn ∈ neg, bnd cn ≤ t) ∧ (∀ cp ∈ pos, t ≤ bnd cp) := by
      exact compatible_bounds (neg.map bnd) (pos.map bnd) (by
        intro l hl u hu
        obtain ⟨cn, hcn, rfl⟩ := List.mem_map.mp hl
        obtain ⟨cp, hcp, rfl⟩ := List.mem_map.mp hu
        exact hcompat cn hcn cp hcp)
      |>.imp fun t ⟨h1, h2⟩ => ⟨fun cn hcn => h1 _ (List.mem_map.mpr ⟨cn, hcn, rfl⟩),
                                  fun cp hcp => h2 _ (List.mem_map.mpr ⟨cp, hcp, rfl⟩)⟩
    obtain ⟨t, htl, htu⟩ := hbounds
    refine ⟨Fin.snoc x' t, fun c hcS => ?_⟩
    -- Show each constraint is satisfied
    rcases lt_trichotomy c.lastCoeff 0 with hlt | heq | hgt
    · -- Negative: t ≥ lower bound
      have hcN : c ∈ neg := List.mem_filter.mpr ⟨hcS, by simpa⟩
      have hlb := htl c hcN
      simp only [Ineq.sat, dot]
      rw [Fin.sum_univ_castSucc, Fin.snoc_last]
      simp_rw [Fin.snoc_castSucc]
      simp only [bnd, dot, Ineq.project] at hlb
      -- Convert hlb to positive denominator form
      rw [show (c.rhs - ∑ i : Fin n, c.lhs (Fin.castSucc i) * x' i) / c.lastCoeff =
              (∑ i : Fin n, c.lhs (Fin.castSucc i) * x' i - c.rhs) / (-c.lastCoeff)
        from by rw [show c.rhs - ∑ i : Fin n, c.lhs (Fin.castSucc i) * x' i =
                         -(∑ i : Fin n, c.lhs (Fin.castSucc i) * x' i - c.rhs)
               from by ring]; rw [neg_div, div_neg]] at hlb
      rw [div_le_iff₀ (neg_pos.mpr hlt)] at hlb
      simp only [Ineq.lastCoeff] at hlb
      nlinarith
    · -- Zero: depends only on first n coords
      have hcZ : c ∈ S.filter (fun c => decide (c.lastCoeff = 0)) :=
        List.mem_filter.mpr ⟨hcS, by simpa⟩
      have hproj : c.project.sat x' := by
        apply hx'; simp only [fmElim]
        exact List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨c, hcZ, rfl⟩))
      simp only [Ineq.sat, dot, Ineq.project] at hproj ⊢
      rw [Fin.sum_univ_castSucc, Fin.snoc_last]
      simp_rw [Fin.snoc_castSucc]
      simp only [Ineq.lastCoeff] at heq
      rw [heq, zero_mul, add_zero]
      exact hproj
    · -- Positive: t ≤ upper bound
      have hcP : c ∈ pos := List.mem_filter.mpr ⟨hcS, by simpa⟩
      have hub := htu c hcP
      simp only [Ineq.sat, dot]
      rw [Fin.sum_univ_castSucc, Fin.snoc_last]
      simp_rw [Fin.snoc_castSucc]
      simp only [bnd, dot, Ineq.project] at hub
      rw [le_div_iff₀ hgt] at hub
      simp only [Ineq.lastCoeff] at hub
      linarith

-- ═══════════════════════════════════════════════════════════════
-- § 4. Farkas' Lemma
-- ═══════════════════════════════════════════════════════════════

/-- An infeasibility certificate: nonneg weights (indexed by constraint position)
    such that the weighted combination of constraints yields 0·x ≤ negative. -/
structure InfeasCert {n : ℕ} (S : System n) where
  ws : Fin S.length → ℚ
  nonneg : ∀ i, 0 ≤ ws i
  coeffsZero : ∀ j : Fin n,
    ∑ i : Fin S.length, ws i * (S.get i).lhs j = 0
  boundNeg : ∑ i : Fin S.length, ws i * (S.get i).rhs < 0

private theorem dot_fin_zero (u v : Fin 0 → ℚ) : dot u v = 0 := by
  simp [dot]

/-- Farkas for 0 variables: each constraint is 0 ≤ rhs. -/
private theorem farkas_base : (S : System 0) →
    S.feasible ∨ Nonempty (InfeasCert S)
  | [] => Or.inl ⟨Fin.elim0, fun _ h => by simp at h⟩
  | c :: S' => by
    rcases farkas_base S' with ⟨_, hfeas'⟩ | hcert'
    · by_cases hc : 0 ≤ c.rhs
      · left; exact ⟨Fin.elim0, fun c' hc' => by
          simp only [Ineq.sat, dot_fin_zero]
          rcases List.mem_cons.mp hc' with rfl | hm
          · exact hc
          · have := hfeas' c' hm; simp only [Ineq.sat, dot_fin_zero] at this; exact this⟩
      · right; push_neg at hc
        let ws₁ : Fin (c :: S').length → ℚ := Fin.cons 1 (fun _ => 0)
        refine ⟨⟨ws₁,
          fun i => by refine Fin.cases ?_ (fun j => ?_) i <;> simp [ws₁],
          fun j => Fin.elim0 j, ?_⟩⟩
        -- Sum over Fin (c :: S').length; normalize to Fin (S'.length + 1) for Fin.sum_univ_succ
        show ∑ i : Fin (S'.length + 1), ws₁ i * ((c :: S').get i).rhs < 0
        rw [Fin.sum_univ_succ]; simp [ws₁, Fin.cons_zero, Fin.cons_succ]; linarith
    · right
      have cert' := Classical.choice hcert'
      let ws₂ : Fin (c :: S').length → ℚ := Fin.cons 0 cert'.ws
      refine ⟨⟨ws₂,
        fun i => by refine Fin.cases ?_ (fun j => ?_) i
                    · simp [ws₂]
                    · simp only [ws₂, Fin.cons_succ]; exact cert'.nonneg j,
        fun j => Fin.elim0 j, ?_⟩⟩
      show ∑ i : Fin (S'.length + 1), ws₂ i * ((c :: S').get i).rhs < 0
      rw [Fin.sum_univ_succ]; simp [ws₂, Fin.cons_zero, Fin.cons_succ]
      exact cert'.boundNeg

/-- Each constraint in `fmElim S` is a nonneg linear combination of original
    constraints in `S`, with the last-variable coefficients cancelling to zero.

    For zero-projected constraints: `c.project = 1 · c` (provenance is the indicator).
    For combined constraints: `combine cp cn = (-cn.lastCoeff) · cp + cp.lastCoeff · cn`.

    This is the key structural lemma that makes certificate lifting algebraic. -/
private theorem fmElim_prov {n : ℕ} (S : System (n + 1)) (c' : Ineq n)
    (hc' : c' ∈ fmElim S) :
    ∃ ws : Fin S.length → ℚ,
      (∀ k, 0 ≤ ws k) ∧
      (∀ j : Fin n, c'.lhs j =
        ∑ k : Fin S.length, ws k * (S.get k).lhs (Fin.castSucc j)) ∧
      (c'.rhs = ∑ k : Fin S.length, ws k * (S.get k).rhs) ∧
      (∑ k : Fin S.length, ws k * (S.get k).lastCoeff = 0) := by
  simp only [fmElim] at hc'
  rcases List.mem_append.mp hc' with hZ | hPN
  · -- Case 1: c' is a zero-projected constraint
    obtain ⟨c, hcMem, rfl⟩ := List.mem_map.mp hZ
    have hcS := (List.mem_filter.mp hcMem).1
    have hcZero : c.lastCoeff = 0 := by simpa using (List.mem_filter.mp hcMem).2
    obtain ⟨k₀, hk₀⟩ := List.mem_iff_get.mp hcS
    refine ⟨fun k => if k = k₀ then 1 else 0, ?_, ?_, ?_, ?_⟩
    · intro k; dsimp only; split_ifs <;> linarith
    · intro j; simp only [Ineq.project]
      simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      rw [← hk₀]
    · simp only [Ineq.project]
      simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      rw [← hk₀]
    · simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      rw [hk₀]; exact hcZero
  · -- Case 2: c' is a positive × negative combination
    rw [List.mem_flatMap] at hPN
    obtain ⟨cp, hcpMem, hm⟩ := hPN
    obtain ⟨cn, hcnMem, rfl⟩ := List.mem_map.mp hm
    have hcpS := (List.mem_filter.mp hcpMem).1
    have hcnS := (List.mem_filter.mp hcnMem).1
    have hp : cp.lastCoeff > 0 := by simpa using (List.mem_filter.mp hcpMem).2
    have hn : cn.lastCoeff < 0 := by simpa using (List.mem_filter.mp hcnMem).2
    obtain ⟨kp, hkp⟩ := List.mem_iff_get.mp hcpS
    obtain ⟨kq, hkq⟩ := List.mem_iff_get.mp hcnS
    refine ⟨fun k =>
        (if k = kp then -cn.lastCoeff else 0) + (if k = kq then cp.lastCoeff else 0),
      ?_, ?_, ?_, ?_⟩
    · intro k; apply add_nonneg <;> (split <;> linarith)
    · intro j; simp only [Ineq.combine, add_mul, ite_mul, zero_mul,
        Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      rw [← hkp, ← hkq]
    · simp only [Ineq.combine, add_mul, ite_mul, zero_mul,
        Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      rw [← hkp, ← hkq]
    · simp only [add_mul, ite_mul, zero_mul,
        Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      rw [← hkp, ← hkq]; simp only [Ineq.lastCoeff]; ring

/-- Sum-swap through provenance: distributing lifted weights through provenance
    yields the same result as the cert's weighted sum over reduced constraints. -/
private theorem sum_prov_swap
    {m₁ m₂ : ℕ}
    (w : Fin m₁ → ℚ) (P : Fin m₁ → Fin m₂ → ℚ)
    (f : Fin m₂ → ℚ) (g : Fin m₁ → ℚ)
    (hprov : ∀ r, ∑ k : Fin m₂, P r k * f k = g r) :
    ∑ k : Fin m₂, (∑ r : Fin m₁, w r * P r k) * f k =
    ∑ r : Fin m₁, w r * g r := by
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1; ext r; simp_rw [mul_assoc]; rw [← Finset.mul_sum, hprov]

/-- Lift an infeasibility certificate through one FM elimination step.

    Strategy: each reduced constraint is a nonneg combination of originals
    (by `fmElim_prov`). The lifted weight for `S[k]` is `∑_r cert.ws r * prov r k`.
    Properties follow by swapping summation order (`sum_prov_swap`). -/
private noncomputable def liftCert {n : ℕ} (S : System (n + 1))
    (cert : InfeasCert (fmElim S)) : InfeasCert S := by
  -- Extract provenance for each reduced constraint
  let prov : Fin (fmElim S).length → Fin S.length → ℚ :=
    fun r => (fmElim_prov S _ (List.get_mem (fmElim S) r)).choose
  have ps : ∀ r, (∀ k, 0 ≤ prov r k) ∧
      (∀ j : Fin n, ((fmElim S).get r).lhs j =
        ∑ k, prov r k * (S.get k).lhs (Fin.castSucc j)) ∧
      (((fmElim S).get r).rhs = ∑ k, prov r k * (S.get k).rhs) ∧
      (∑ k, prov r k * (S.get k).lastCoeff = 0) :=
    fun r => (fmElim_prov S _ (List.get_mem (fmElim S) r)).choose_spec
  -- Lifted weights: distribute cert weights through provenance
  let ws : Fin S.length → ℚ := fun k =>
    ∑ r : Fin (fmElim S).length, cert.ws r * prov r k
  refine ⟨ws, ?_, ?_, ?_⟩
  -- nonneg
  · exact fun k => Finset.sum_nonneg fun r _ => mul_nonneg (cert.nonneg r) ((ps r).1 k)
  -- coeffsZero
  · intro j
    refine Fin.lastCases ?_ (fun j' => ?_) j
    · -- j = last n: provenance cancels on the last coordinate
      show ∑ k, ws k * (S.get k).lhs (Fin.last n) = 0
      have := sum_prov_swap cert.ws prov
        (fun k => (S.get k).lhs (Fin.last n)) (fun _ => (0 : ℚ))
        (fun r => (ps r).2.2.2)
      simp only [mul_zero, Finset.sum_const_zero] at this
      exact this
    · -- j = castSucc j': reduces to cert.coeffsZero j'
      show ∑ k, ws k * (S.get k).lhs (Fin.castSucc j') = 0
      have := sum_prov_swap cert.ws prov
        (fun k => (S.get k).lhs (Fin.castSucc j'))
        (fun r => ((fmElim S).get r).lhs j')
        (fun r => ((ps r).2.1 j').symm)
      rw [this]; exact cert.coeffsZero j'
  -- boundNeg
  · show ∑ k, ws k * (S.get k).rhs < 0
    have := sum_prov_swap cert.ws prov
      (fun k => (S.get k).rhs)
      (fun r => ((fmElim S).get r).rhs)
      (fun r => ((ps r).2.2.1).symm)
    rw [this]; exact cert.boundNeg

/-- **Farkas' lemma over ℚ**: a rational linear system is either feasible
    or has a nonneg certificate of infeasibility.

    Proof by induction on n (number of variables), using FM elimination.
    Base case (0 variables): each constraint is 0 ≤ rhs.
    Inductive step: FM-eliminate → IH → extend backward or lift certificate. -/
theorem farkas {n : ℕ} (S : System n) :
    S.feasible ∨ Nonempty (InfeasCert S) := by
  induction n with
  | zero => exact farkas_base S
  | succ n ih =>
    rcases ih (fmElim S) with hfeas | hcert
    · exact Or.inl ((fmElim_equisat S).mpr hfeas)
    · exact Or.inr ⟨liftCert S (Classical.choice hcert)⟩

-- ═══════════════════════════════════════════════════════════════
-- § 5. Minkowski-Weyl Theorem (Rational Cone Duality)
-- ═══════════════════════════════════════════════════════════════

/-- The conic hull of a finite set of rational generators. -/
def conicHull {n : ℕ} (gens : List (Fin n → ℚ)) : Set (Fin n → ℚ) :=
  {x | ∃ cs : List ℚ, cs.length = gens.length ∧
    (∀ c ∈ cs, 0 ≤ c) ∧
    ∀ j : Fin n, x j = (List.zipWith (fun c v => c * v j) cs gens).sum}

/-- A rational polyhedral cone (H-description). -/
def hCone {n : ℕ} (normals : List (Fin n → ℚ)) : Set (Fin n → ℚ) :=
  {x | ∀ a ∈ normals, dot a x ≤ 0}

/-- **Minkowski-Weyl (V→H)**: every finitely generated rational cone is polyhedral. -/
theorem minkowskiWeyl_VtoH {n : ℕ} (gens : List (Fin n → ℚ)) :
    ∃ normals : List (Fin n → ℚ), conicHull gens = hCone normals := by
  sorry

/-- **Minkowski-Weyl (H→V)**: every rational polyhedral cone is finitely generated. -/
theorem minkowskiWeyl_HtoV {n : ℕ} (normals : List (Fin n → ℚ)) :
    ∃ gens : List (Fin n → ℚ), hCone normals = conicHull gens := by
  sorry

end Polyhedral
