module

public import Linglib.Studies.ZurawHayes2017

/-!
# Magri (2025): Constraint Interaction in Probabilistic Phonology

[magri-2025] asks which modes of constraint interaction predict the generalization of
[zuraw-hayes-2017] and [hayes-2022]: when no constraint is sensitive to both of two binary
factors, the logit rates of a variable process on the four forms crossing them differ by a
constant along each factor (§2). Within harmony-based probabilistic phonology, where a
candidate's probability is proportional to a positive harmony of its violation profile (23), the
answer is a characterization (§5.5): a harmony predicts the generalization iff it is separable, a
product of powers of unary functions each fed the violations of a single constraint (30)
(`predictsHZ_iff_separable`). Equivalently the harmony of any profile is the product of the
harmonies of its single-constraint profiles (32) (`separable_iff_eq_prod_single`).

Maximum entropy harmony is separable (29), which recovers §3's observation that it predicts the
generalization (`predictsHZ_meHarmony`). Feeding the weighted violations to the inverse function
instead of the exponential (27) is not separable: on the Tagalog square of [zuraw-hayes-2017] it
satisfies the constant difference only when the two prefix constraints have equal weights or the
two stem-nasal constraints have none (§4.4, `inverseHarmony_hz_tagalog_iff`). Every separable
harmony is maximum entropy harmony over the constraints rescaled by `Ĉₖ = −log hₖ(Cₖ)` ((33),
(34), `prod_rpow_eq_meHarmony_rescale`), a rescaling that preserves the order of violation
counts and which of them are zero.

## Implementation notes

* A harmony is a function `(Fin n → ℕ) → ℝ` of violation profiles. It predicts the generalization
  (§4.2) if on every square whose rows and columns intersect relative to a constraint set, the
  log-odds of two candidates have zero interaction. The log-odds is the logit rate when the two
  are the form's only candidates (§3.3), and the log of their probability ratio in general, since
  the normalizing constant cancels.
* The characterization assumes the harmony positive and normalized, as §4.2 does; decreasingness
  is not needed. The converse direction takes one square per constraint: letting constraint `k`
  vary along the rows and the others along the columns gives
  `H (update u k c) = H (single k c) * H (update u k 0)`, whence (32) by induction on the
  constraints.
* The weights of (30) add no generality to the class of separable harmonies, since `hₖ ^ wₖ` is
  itself a unary function (`separable_iff_exists_prod`); they matter to the grammars a learner
  can reach, not to the characterization.

## References

* [magri-2025]
* [zuraw-hayes-2017]
* [hayes-2022]
-/

@[expose] public section

namespace Magri2025

open Real Constraints HarmonicGrammar Function Finset ZurawHayes2017

variable {n : ℕ} {H : (Fin n → ℕ) → ℝ}

/-! ### Harmony-based grammars (§4) -/

/-- The log-odds of candidate `a` against `b` for form `x` under harmony `H`: the log of the
ratio of their harmonies (§3.3). -/
noncomputable def logOdds {X Y : Type*} (H : (Fin n → ℕ) → ℝ) (con : CON (X × Y) n) (a b : Y)
    (x : X) : ℝ :=
  log (H (con · (x, a)) / H (con · (x, b)))

/-- A harmony predicts HZ's generalization (§4.2, (24)): on every square whose rows and columns
are independent relative to a constraint set, the log-odds of two candidates have zero
interaction. -/
def PredictsHZ (H : (Fin n → ℕ) → ℝ) : Prop :=
  ∀ (X Y : Type) (sq : Square X) (con : CON (X × Y) n), sq.Independent con →
    ∀ a b : Y, sq.interaction (logOdds H con a b) = 0

/-- A harmony is separable (30): a product of powers of unary functions, each fed the violations
of a single constraint. -/
def Separable (H : (Fin n → ℕ) → ℝ) : Prop :=
  ∃ (h : Fin n → ℕ → ℝ) (w : Fin n → ℝ), ∀ v, H v = ∏ k, h k (v k) ^ w k

/-- The weights of (30) add no generality: a separable harmony is a product of unary functions. -/
theorem separable_iff_exists_prod :
    Separable H ↔ ∃ g : Fin n → ℕ → ℝ, ∀ v, H v = ∏ k, g k (v k) :=
  ⟨fun ⟨h, w, hH⟩ ↦ ⟨fun k c ↦ h k c ^ w k, hH⟩, fun ⟨g, hg⟩ ↦ ⟨g, 1, by simpa using hg⟩⟩

/-! ### Separable harmonies predict the generalization (§5.4) -/

/-- Separable harmonies predict HZ's generalization (§5.4): the log-odds is a sum of
per-constraint terms. -/
theorem Separable.predictsHZ (hH : Separable H) (hne : ∀ v, H v ≠ 0) : PredictsHZ H := by
  obtain ⟨g, hg⟩ := separable_iff_exists_prod.1 hH
  have hg0 (k : Fin n) (c : ℕ) : g k c ≠ 0 :=
    prod_ne_zero_iff.1 (hg (fun _ ↦ c) ▸ hne _) k (mem_univ k)
  intro X Y sq con hind a b
  convert hind.interaction_sum_eq_zero fun k v ↦ log (g k (v a)) - log (g k (v b)) using 2
  ext x
  rw [logOdds, log_div (hne _) (hne _), hg, hg, log_prod fun k _ ↦ hg0 k _,
    log_prod fun k _ ↦ hg0 k _, ← sum_sub_distrib]
  rfl

/-! ### Only separable harmonies predict the generalization (§5.5) -/

/-- The square of the converse: constraint `k` is violated `c` times by candidate `true` of the
top row, and every other constraint `j` is violated `u j` times by candidate `true` of the left
column. -/
private def witness (u : Fin n → ℕ) (k : Fin n) (c : ℕ) : CON ((Bool × Bool) × Bool) n :=
  fun j p ↦ if p.2 then if j = k then (if p.1.1 then c else 0) else (if p.1.2 then u j else 0)
    else 0

private def witnessSquare : Square (Bool × Bool) :=
  ⟨(true, true), (true, false), (false, true), (false, false)⟩

private theorem witnessSquare_independent (u : Fin n → ℕ) (k : Fin n) (c : ℕ) :
    witnessSquare.Independent (witness u k c) := by
  intro j
  by_cases hj : j = k
  · exact .inr ⟨funext fun y ↦ by simp [witness, witnessSquare, hj],
      funext fun y ↦ by simp [witness, witnessSquare, hj]⟩
  · exact .inl ⟨funext fun y ↦ by simp [witness, witnessSquare, hj],
      funext fun y ↦ by simp [witness, witnessSquare, hj]⟩

/-- A harmony predicting HZ's generalization splits off the violations of any one constraint. -/
theorem PredictsHZ.mul_update (hH : PredictsHZ H) (hpos : ∀ v, 0 < H v) (h0 : H 0 = 1)
    (u : Fin n → ℕ) (k : Fin n) (c : ℕ) :
    H (update u k c) = H (Pi.single k c) * H (update u k 0) := by
  have row (p : Bool × Bool) : (witness u k c · (p, false)) = 0 := by ext; simp [witness]
  have tl : (witness u k c · (witnessSquare.tl, true)) = update u k c := by
    ext j; by_cases hj : j = k <;> simp [witness, witnessSquare, hj]
  have tr : (witness u k c · (witnessSquare.tr, true)) = Pi.single k c := by
    ext j; by_cases hj : j = k <;> simp [witness, witnessSquare, hj]
  have bl : (witness u k c · (witnessSquare.bl, true)) = update u k 0 := by
    ext j; by_cases hj : j = k <;> simp [witness, witnessSquare, hj]
  have br : (witness u k c · (witnessSquare.br, true)) = 0 := by ext; simp [witness, witnessSquare]
  have := hH _ _ _ _ (witnessSquare_independent u k c) true false
  simp only [Square.interaction_apply, logOdds, row, tl, tr, bl, br, h0, div_one, log_one] at this
  refine log_injOn_pos (hpos _) (mul_pos (hpos _) (hpos _)) ?_
  rw [log_mul (hpos _).ne' (hpos _).ne']
  linarith

/-- A harmony predicting HZ's generalization satisfies (32). -/
theorem PredictsHZ.eq_prod_single (hH : PredictsHZ H) (hpos : ∀ v, 0 < H v) (h0 : H 0 = 1)
    (v : Fin n → ℕ) : H v = ∏ k, H (Pi.single k (v k)) := by
  classical
  suffices ∀ s : Finset (Fin n), H (s.piecewise v 0) = ∏ k ∈ s, H (Pi.single k (v k)) by
    simpa using this univ
  intro s
  induction s using Finset.induction_on with
  | empty => simpa using h0
  | insert k s hk ih =>
    rw [prod_insert hk, ← ih, piecewise_insert, hH.mul_update hpos h0,
      update_eq_self_iff.2 (by simp [hk] : (0 : ℕ) = s.piecewise v 0 k)]

/-- The characterization of [magri-2025] (§5.5): a positive normalized harmony predicts HZ's
generalization iff it is separable. -/
theorem predictsHZ_iff_separable (hpos : ∀ v, 0 < H v) (h0 : H 0 = 1) :
    PredictsHZ H ↔ Separable H :=
  ⟨fun h ↦ separable_iff_exists_prod.2 ⟨fun k c ↦ H (Pi.single k c), h.eq_prod_single hpos h0⟩,
    fun h ↦ h.predictsHZ fun v ↦ (hpos v).ne'⟩

/-- Separability (30) as (32): the harmony of a profile is the product of the harmonies of its
single-constraint profiles. -/
theorem separable_iff_eq_prod_single (hpos : ∀ v, 0 < H v) (h0 : H 0 = 1) :
    Separable H ↔ ∀ v, H v = ∏ k, H (Pi.single k (v k)) :=
  ⟨fun h ↦ ((predictsHZ_iff_separable hpos h0).2 h).eq_prod_single hpos h0,
    fun h ↦ separable_iff_exists_prod.2 ⟨fun k c ↦ H (Pi.single k c), h⟩⟩

/-! ### Maximum entropy harmony (§3, §5.1) -/

/-- Maximum entropy harmony (14b) of a real-valued violation profile. -/
noncomputable def meHarmony (w r : Fin n → ℝ) : ℝ :=
  exp (-∑ k, w k * r k)

/-- Maximum entropy harmony is separable (29), with `hₖ(x) = exp(−x)` for every constraint. -/
theorem separable_meHarmony (w : Fin n → ℝ) : Separable fun v ↦ meHarmony w fun k ↦ v k :=
  ⟨fun _ c ↦ exp (-c), w, fun v ↦ by
    simp only [meHarmony, ← exp_mul, ← exp_sum, ← sum_neg_distrib, mul_neg, mul_comm]⟩

/-- Maximum entropy harmony predicts HZ's generalization (§3.6). -/
theorem predictsHZ_meHarmony (w : Fin n → ℝ) : PredictsHZ fun v ↦ meHarmony w fun k ↦ v k :=
  (separable_meHarmony w).predictsHZ fun _ ↦ (exp_pos _).ne'

/-! ### Constraint rescaling (§5.3) -/

/-- The rescaled constraint (33): `Ĉₖ = −log hₖ(Cₖ)`. -/
noncomputable def rescale (h : Fin n → ℕ → ℝ) (k : Fin n) (c : ℕ) : ℝ :=
  -log (h k c)

/-- Every separable harmony is maximum entropy harmony of the rescaled violations (34). -/
theorem prod_rpow_eq_meHarmony_rescale {h : Fin n → ℕ → ℝ} (hpos : ∀ k c, 0 < h k c)
    (w : Fin n → ℝ) (v : Fin n → ℕ) :
    ∏ k, h k (v k) ^ w k = meHarmony w fun k ↦ rescale h k (v k) := by
  simp only [meHarmony, rescale, mul_neg, sum_neg_distrib, neg_neg, exp_sum,
    rpow_def_of_pos (hpos _ _), mul_comm]

variable {h : Fin n → ℕ → ℝ} {k : Fin n}

/-- Rescaling preserves the order of violation counts (footnote 14). -/
theorem strictMono_rescale (hpos : ∀ c, 0 < h k c) (hanti : StrictAnti (h k)) :
    StrictMono (rescale h k) :=
  fun _ _ hab ↦ neg_lt_neg (log_lt_log (hpos _) (hanti hab))

/-- A rescaled constraint is satisfied iff the original is (footnote 15). -/
theorem rescale_eq_zero_iff (hpos : ∀ c, 0 < h k c) (hanti : StrictAnti (h k)) (h0 : h k 0 = 1)
    {c : ℕ} : rescale h k c = 0 ↔ c = 0 := by
  rw [← (strictMono_rescale hpos hanti).injective.eq_iff, rescale, rescale, h0]
  simp

/-- Rescaled violations are nonnegative (footnote 16). -/
theorem rescale_nonneg (hpos : ∀ c, 0 < h k c) (hanti : StrictAnti (h k)) (h0 : h k 0 = 1)
    (c : ℕ) : 0 ≤ rescale h k c := by
  simpa [rescale, h0] using (strictMono_rescale hpos hanti).monotone c.zero_le

/-! ### The inverse harmony (§4.4) -/

/-- The inverse harmony (27): the weighted violations fed to `h(x) = 1/(1+x)` in place of maximum
entropy's `exp(−x)`. -/
noncomputable def inverseHarmony (w : Fin n → ℝ) (v : Fin n → ℕ) : ℝ :=
  (1 + weightedViolations w v)⁻¹

theorem inverseHarmony_pos {w : Fin n → ℝ} (hw : ∀ k, 0 ≤ w k) (v : Fin n → ℕ) :
    0 < inverseHarmony w v := by
  unfold inverseHarmony weightedViolations
  have := sum_nonneg fun k (_ : k ∈ univ) ↦ mul_nonneg (hw k) (Nat.cast_nonneg (v k))
  positivity

/-- On the Tagalog square, the inverse harmony satisfies HZ's identity (28) only when the two
prefix constraints have equal weights, or the two stem-nasal constraints have none (§4.4 and
footnote 11). -/
theorem inverseHarmony_hz_tagalog_iff {w : Fin 6 → ℝ} (hw : ∀ k, 0 ≤ w k) :
    nasalSubSquare.interaction (logOdds (inverseHarmony w) constraints .yes .no) = 0 ↔
      w 4 = w 5 ∨ w 2 = 0 ∧ w 3 = 0 := by
  simp [logOdds, inverseHarmony, weightedViolations, Fin.sum_univ_six, nasalSubSquare, constraints,
    nasSub, starNC, starStemVelar, starStemVelarCoronal, unifMang, unifPang, Zuraw2010.nasSub,
    Zuraw2010.starNC, Zuraw2010.starInitVelar, Zuraw2010.starInitCorVel,
    NasalSubCandidate.project, NasalSubInput.toStemC, NasalSubOutput.toSubSt]
  have hp (k : Fin 6) : 0 < 1 + w k := by linarith [hw k]
  have hp' (i j k : Fin 6) : 0 < 1 + (w i + w j + w k) := by linarith [hw i, hw j, hw k]
  have hp'' : 0 < 1 + (w 0 + w 1) := by linarith [hw 0, hw 1]
  have hlog {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : log (x⁻¹ * y) = log y - log x := by
    rw [log_mul (inv_pos.2 hx).ne' hy.ne', log_inv]
    ring
  rw [hlog (hp 4) (hp 0), hlog (hp' 2 3 4) hp'', hlog (hp 5) (hp 0), hlog (hp' 2 3 5) hp'']
  have hA := log_mul (hp' 2 3 4).ne' (hp 5).ne'
  have hB := log_mul (hp 4).ne' (hp' 2 3 5).ne'
  trans (1 + (w 2 + w 3 + w 4)) * (1 + w 5) = (1 + w 4) * (1 + (w 2 + w 3 + w 5))
  · rw [← log_injOn_pos.eq_iff (mul_pos (hp' 2 3 4) (hp 5)) (mul_pos (hp 4) (hp' 2 3 5))]
    constructor <;> intro h <;> linarith
  rw [← sub_eq_zero, show (1 + (w 2 + w 3 + w 4)) * (1 + w 5) - (1 + w 4) * (1 + (w 2 + w 3 + w 5))
    = (w 2 + w 3) * (w 5 - w 4) by ring, mul_eq_zero, sub_eq_zero]
  constructor
  · rintro (h | h)
    · exact .inr ⟨by linarith [hw 2, hw 3], by linarith [hw 2, hw 3]⟩
    · exact .inl h.symm
  · rintro (h | ⟨h2, h3⟩)
    · exact .inr h.symm
    · exact .inl (by rw [h2, h3]; ring)

/-- The inverse harmony is not separable once the prefix constraints differ in weight and a
stem-nasal constraint is active. -/
theorem not_separable_inverseHarmony {w : Fin 6 → ℝ} (hw : ∀ k, 0 ≤ w k) (h45 : w 4 ≠ w 5)
    (h2 : w 2 ≠ 0) : ¬ Separable (inverseHarmony w) := fun hH ↦ by
  have := (inverseHarmony_hz_tagalog_iff hw).1 <|
    hH.predictsHZ (fun v ↦ (inverseHarmony_pos hw v).ne') _ _ _ _ independent .yes .no
  tauto

end Magri2025
