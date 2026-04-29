import Linglib.Theories.Pragmatics.InformationTheory.Channel

/-!
# Channel Capacity and Capacity-Achieving Priors
@cite{cover-thomas-2006} @cite{zaslavsky-etal-2019}

The maximum mutual information `C* = sup_{p(c)} I(W;C)` for a `CommChannel`,
plus the capacity-achieving prior (CAP) condition `p(c) ∝ exp(-S(c))` and
its central consequence: at a CAP, `-log p(c) = S(c) + log Z` (paper eq. 6).

Channel structure and per-channel quantities (`marginalWord`, `posterior`,
`commPrecision`, `mutualInfo`) live in the sibling `Channel.lean`. This
file is capacity-specific.

## Main definitions

- `IsCAP`: capacity-achieving prior predicate `p(c) ∝ exp(-S(c))`
- `channelCapacity`: `sup_{p(c)} I(W;C)`

## Main results

- `cap_linear`: at a CAP, `-log p(c) = S(c) + log Z`
- `mutualInfo_eq_log_Z_of_cap`: at a CAP, `I(W;C) = log Z`
- `gibbs_inequality`: KL divergence is non-negative
- `mutualInfo_le_log_card`: `I(W;C) ≤ log |W|`
- `channelCapacity_le_log_card`: `C* ≤ log |W|`
-/

set_option autoImplicit false

namespace Pragmatics.InformationTheory

open Finset BigOperators Real

variable {C W : Type} [Fintype C] [Fintype W]

/-- A prior is capacity-achieving iff `p(c) ∝ exp(-S(c))`.
    Necessary and sufficient for `p(c)` to maximize `I(W;C)` over all
    priors on `C`. From @cite{zaslavsky-etal-2019}; derived from the
    Blahut-Arimoto algorithm (@cite{cover-thomas-2006}). -/
def IsCAP (nc : CommChannel C W) (prior : C → ℝ) : Prop :=
  ∃ Z > 0, ∀ c, prior c > 0 →
    prior c = exp (-commPrecision nc prior c) / Z

/-- The CAP linear relation: at a capacity-achieving prior,
    `-log p(c) = S(c) + log Z`. From @cite{zaslavsky-etal-2019}. -/
theorem cap_linear (nc : CommChannel C W) (prior : C → ℝ)
    {Z : ℝ} (hZ : Z > 0)
    (hCAP : ∀ c, prior c > 0 → prior c = exp (-commPrecision nc prior c) / Z)
    {c : C} (hc : prior c > 0) :
    -log (prior c) = commPrecision nc prior c + log Z := by
  rw [hCAP c hc, log_div (exp_pos _).ne' hZ.ne', log_exp]
  ring

/-- Variant of `cap_linear` taking an existential `IsCAP` witness. -/
theorem cap_linear' (nc : CommChannel C W) (prior : C → ℝ)
    (hCAP : IsCAP nc prior) {c : C} (hc : prior c > 0) :
    ∃ Z > 0, -log (prior c) = commPrecision nc prior c + log Z := by
  obtain ⟨Z, hZ, hcap⟩ := hCAP
  exact ⟨Z, hZ, cap_linear nc prior hZ hcap hc⟩

/-- Split `Σ_w p(w|c) · log(p(c|w)/p(c))` into
    `Σ_w p(w|c) · log p(c|w) - log p(c)`. -/
private lemma sum_encode_log_ratio (nc : CommChannel C W) (prior : C → ℝ)
    (hprior_nonneg : ∀ c, 0 ≤ prior c) {c : C} (hpc : prior c > 0) :
    ∑ w : W, nc.encode c w * log (posterior nc prior w c / prior c) =
    (∑ w : W, nc.encode c w * log (posterior nc prior w c)) - log (prior c) := by
  rw [show log (prior c) = ∑ w : W, nc.encode c w * log (prior c) from by
    rw [← sum_mul, nc.encode_sum_one, one_mul]
  ]
  rw [← sum_sub_distrib]
  congr 1; ext w
  by_cases hew : nc.encode c w = 0
  · simp [hew]
  · have hew_pos := lt_of_le_of_ne (nc.encode_nonneg c w) (Ne.symm hew)
    have hmw := marginalWord_pos_of nc prior hprior_nonneg hpc hew_pos
    have hpost : 0 < posterior nc prior w c := by
      unfold posterior; exact div_pos (mul_pos hew_pos hpc) hmw
    rw [log_div (ne_of_gt hpost) (ne_of_gt hpc), mul_sub]

/-- At a CAP, mutual information equals `log Z`.
    The normalization constant `Z` in the CAP condition determines the
    channel capacity. -/
theorem mutualInfo_eq_log_Z_of_cap (nc : CommChannel C W)
    (prior : C → ℝ) {Z : ℝ} (hZ : Z > 0)
    (hCAP : ∀ c, prior c > 0 → prior c = exp (-commPrecision nc prior c) / Z)
    (hprior_nonneg : ∀ c, 0 ≤ prior c)
    (hprior_sum : ∑ c : C, prior c = 1)
    (hprior_pos : ∀ c, prior c > 0) :
    mutualInfo nc prior = log Z := by
  unfold mutualInfo
  simp_rw [mul_assoc, ← mul_sum]
  suffices hkey : ∀ c, ∑ w, nc.encode c w * log (posterior nc prior w c / prior c) = log Z by
    simp_rw [hkey, ← sum_mul, hprior_sum, one_mul]
  intro c
  have hpc := hprior_pos c
  have hcap_c := cap_linear nc prior hZ hCAP hpc
  have h1 := sum_encode_log_ratio nc prior hprior_nonneg hpc
  unfold commPrecision at hcap_c
  linarith

/-- Gibbs inequality: KL divergence is non-negative.
    `D_KL(p ∥ q) = Σ p(i) log(p(i)/q(i)) ≥ 0` for distributions p, q.
    Uses `log x ≤ x − 1`. -/
theorem gibbs_inequality {ι : Type*} [Fintype ι] (p q : ι → ℝ)
    (hp_nn : ∀ i, 0 ≤ p i) (hq_pos : ∀ i, 0 < q i)
    (hp_sum : ∑ i : ι, p i = 1) (hq_sum : ∑ i : ι, q i = 1) :
    0 ≤ ∑ i : ι, p i * log (p i / q i) := by
  suffices hterm : ∀ i, p i - q i ≤ p i * log (p i / q i) by
    calc (0 : ℝ) = ∑ i : ι, (p i - q i) := by rw [sum_sub_distrib, hp_sum, hq_sum, sub_self]
      _ ≤ ∑ i : ι, p i * log (p i / q i) := sum_le_sum fun i _ => hterm i
  intro i
  by_cases hi : p i = 0
  · simp [hi, le_of_lt (hq_pos i)]
  · have hpi : 0 < p i := lt_of_le_of_ne (hp_nn i) (Ne.symm hi)
    have h1 := log_le_sub_one_of_pos (div_pos (hq_pos i) hpi)
    have h2 := mul_le_mul_of_nonneg_left h1 hpi.le
    have h3 : p i * (q i / p i - 1) = q i - p i := by field_simp
    rw [h3] at h2
    rw [log_div (ne_of_gt (hq_pos i)) (ne_of_gt hpi)] at h2
    rw [log_div (ne_of_gt hpi) (ne_of_gt (hq_pos i))]
    nlinarith

/-- Entropy of a distribution ≤ log of the support size: `H(q) ≤ log |W|`.
    Follows from Gibbs inequality applied to `KL(q ∥ uniform)`. -/
private lemma entropy_le_log_card {ι : Type*} [Fintype ι] (q : ι → ℝ)
    (hq_nonneg : ∀ i, 0 ≤ q i) (hq_sum : ∑ i : ι, q i = 1) :
    -∑ i : ι, q i * log (q i) ≤ log (Fintype.card ι : ℝ) := by
  by_cases hW : Fintype.card ι = 0
  · haveI := Fintype.card_eq_zero_iff.mp hW; simp
  · have hWpos : (0 : ℝ) < ↑(Fintype.card ι) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hW)
    let u : ι → ℝ := fun _ => 1 / ↑(Fintype.card ι)
    have hu_pos : ∀ i, (0 : ℝ) < u i := fun _ => div_pos one_pos hWpos
    have hu_sum : ∑ i : ι, u i = 1 := by
      simp [u, sum_const, nsmul_eq_mul, Nat.cast_ne_zero.mpr hW]
    have hgibbs := gibbs_inequality q u hq_nonneg hu_pos hq_sum hu_sum
    simp_rw [show ∀ i, q i / u i = q i * ↑(Fintype.card ι) from fun i => by simp [u]] at hgibbs
    suffices hsplit : ∑ i : ι, q i * log (q i * ↑(Fintype.card ι)) =
        (∑ i : ι, q i * log (q i)) + log ↑(Fintype.card ι) by linarith
    have hterm : ∀ i, q i * log (q i * ↑(Fintype.card ι)) =
        q i * log (q i) + q i * log ↑(Fintype.card ι) := by
      intro i
      by_cases hi : q i = 0
      · simp [hi]
      · rw [log_mul (ne_of_gt (lt_of_le_of_ne (hq_nonneg i) (Ne.symm hi))) (ne_of_gt hWpos)]
        ring
    simp_rw [hterm, sum_add_distrib, ← sum_mul, hq_sum, one_mul]

/-- `I(W;C) ≤ H(W)`: mutual information ≤ entropy of the marginal word
    distribution. The gap is the conditional entropy `H(W|C) ≥ 0`. -/
private lemma mutualInfo_le_marginal_entropy (nc : CommChannel C W) (prior : C → ℝ)
    (hprior_nonneg : ∀ c, 0 ≤ prior c) :
    mutualInfo nc prior ≤ -∑ w : W, marginalWord nc prior w * log (marginalWord nc prior w) := by
  unfold mutualInfo
  rw [sum_comm, ← sum_neg_distrib]
  apply sum_le_sum; intro w _
  calc ∑ c : C, prior c * nc.encode c w * log (posterior nc prior w c / prior c)
      ≤ ∑ c : C, -(prior c * nc.encode c w * log (marginalWord nc prior w)) := by
        apply sum_le_sum; intro c _
        by_cases hpc : prior c = 0
        · simp [hpc]
        · by_cases hew : nc.encode c w = 0
          · simp [hew]
          · have hpc_pos := lt_of_le_of_ne (hprior_nonneg c) (Ne.symm hpc)
            have hew_pos := lt_of_le_of_ne (nc.encode_nonneg c w) (Ne.symm hew)
            have hmw_pos := marginalWord_pos_of nc prior hprior_nonneg hpc_pos hew_pos
            have hcoeff := mul_pos hpc_pos hew_pos
            rw [show -(prior c * nc.encode c w * log (marginalWord nc prior w)) =
                prior c * nc.encode c w * (-log (marginalWord nc prior w)) from by ring]
            apply mul_le_mul_of_nonneg_left _ hcoeff.le
            have : posterior nc prior w c / prior c =
                nc.encode c w / marginalWord nc prior w := by
              unfold posterior; field_simp
            rw [this, log_div (ne_of_gt hew_pos) (ne_of_gt hmw_pos)]
            linarith [log_nonpos (nc.encode_nonneg c w) (nc.encode_le_one c w)]
    _ = -(marginalWord nc prior w * log (marginalWord nc prior w)) := by
        simp only [sum_neg_distrib]; congr 1; rw [← sum_mul]; rfl

/-- Mutual information is bounded by the log of the vocabulary size:
    `I(W;C) ≤ log |W|`. -/
theorem mutualInfo_le_log_card (nc : CommChannel C W) (prior : C → ℝ)
    (hprior_nonneg : ∀ c, 0 ≤ prior c) (hprior_sum : ∑ c : C, prior c = 1) :
    mutualInfo nc prior ≤ log (Fintype.card W) :=
  (mutualInfo_le_marginal_entropy nc prior hprior_nonneg).trans
    (entropy_le_log_card _ (marginalWord_nonneg nc prior hprior_nonneg)
      (marginalWord_sum_one nc prior hprior_sum))

/-- Channel capacity: the supremum of mutual information over all valid
    priors. `C* = sup_{p(c)} I(W;C)` (eq. 3 of @cite{zaslavsky-etal-2019}). -/
noncomputable def channelCapacity (nc : CommChannel C W) : ℝ :=
  sSup {I | ∃ prior : C → ℝ,
    (∀ c, 0 ≤ prior c) ∧ ∑ c, prior c = 1 ∧ mutualInfo nc prior = I}

/-- Channel capacity is bounded by log of the vocabulary size. -/
theorem channelCapacity_le_log_card (nc : CommChannel C W) [Nonempty C] :
    channelCapacity nc ≤ log (Fintype.card W) := by
  apply csSup_le
  · have hcard_pos : (0 : ℝ) < ↑(Fintype.card C) :=
      Nat.cast_pos.mpr Fintype.card_pos
    let u : C → ℝ := fun _ => 1 / ↑(Fintype.card C)
    have hu_nn : ∀ c, 0 ≤ u c := fun _ => div_nonneg zero_le_one hcard_pos.le
    have hu_sum : ∑ c : C, u c = 1 := by
      simp [u, Finset.sum_const, nsmul_eq_mul]
    exact ⟨mutualInfo nc u, u, hu_nn, hu_sum, rfl⟩
  · rintro I ⟨prior, hp, hsum, rfl⟩
    exact mutualInfo_le_log_card nc prior hp hsum

/-- Mutual information bound for a `Fin k` vocabulary: `I(W;C) ≤ log k`. -/
theorem mutualInfo_le_log_fin {C : Type} [Fintype C] {k : Nat}
    (nc : CommChannel C (Fin k)) (prior : C → ℝ)
    (hp : ∀ c, 0 ≤ prior c) (hsum : ∑ c, prior c = 1) :
    mutualInfo nc prior ≤ log k := by
  have := mutualInfo_le_log_card nc prior hp hsum
  simp [Fintype.card_fin] at this
  exact this

end Pragmatics.InformationTheory
