import Linglib.Core.Probability.Hypergeometric
import Linglib.Core.Probability.PMFEvalLemmas
import Linglib.Theories.Pragmatics.RSA.Operators
import Linglib.Theories.Pragmatics.RSA.Silence
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform

/-!
# @cite{goodman-stuhlmuller-2013} on mathlib `PMF`
@cite{goodman-stuhlmuller-2013}

PMF reformulation of GS2013 using `PMF.hypergeometric` as the observation
kernel primitive. The model is parameterized over `a : Access` throughout —
there is no per-`.a1`/`.a2`/`.a3` substrate; each downstream operator
(`speakerBelief`, `qualityOk`, `s1Score`, `S1g`, `marginalSpeaker`, `L1`)
takes `(a, k)` where `k : Fin (a.toNat + 1)` is the observed count.

## PMF stack (one definition each, parameterized)

* `worldPrior : PMF WorldState` — uniform on 4 states
* `obsKernel a w : PMF (Fin (a.toNat + 1))` — `PMF.hypergeometric 3 w.toNat a.toNat`
* `speakerBelief a k : PMF WorldState` — `PMF.posterior (obsKernel a) worldPrior k`
* `S1g m α a k h : PMF U` — softmax-of-expected-log over the speaker's belief
* `marginalSpeaker m α a w hCov : PMF U` — `(obsKernel a w).bind (S1g a)`
* `L1 m α a u hMarg : PMF WorldState` — `PMF.posterior (marginalSpeaker a) worldPrior u`

## Silence-extended findings

All 11 paper findings are stated against the silence-extended utterance
space `WithSilence U` — the cover hypothesis `cover_silent` is universal
because silence is `qOk` at every observation. This dissolves the
`(access, word) ∉ {sensible}` defects that block formalization without
silence (paper p. 180 "sensible situations").
-/

set_option autoImplicit false

/-! ## §1. Substrate: world states, utterance enums, meaning functions, access -/

namespace Phenomena.ScalarImplicatures.GoodmanStuhlmuller2013.PMF

/-- World states: how many of 3 objects have the property. -/
inductive WorldState where
  | s0 | s1 | s2 | s3
  deriving DecidableEq, Repr, Inhabited, Fintype

def WorldState.toNat : WorldState → Nat
  | .s0 => 0 | .s1 => 1 | .s2 => 2 | .s3 => 3

theorem WorldState.toNat_le_three (w : WorldState) : w.toNat ≤ 3 := by
  cases w <;> decide

/-- Quantifier alternative set. -/
inductive QUtt where
  | none_ | some_ | all
  deriving DecidableEq, Repr, Inhabited, Fintype

def qMeaning : QUtt → WorldState → Bool
  | .none_, s => s.toNat == 0
  | .some_, s => s.toNat ≥ 1
  | .all,   s => s.toNat == 3

/-- Numeral alternative set (lower-bound semantics). -/
inductive NumUtt where
  | one | two | three
  deriving DecidableEq, Repr, Inhabited, Fintype

def lbMeaning : NumUtt → WorldState → Bool
  | .one,   s => s.toNat ≥ 1
  | .two,   s => s.toNat ≥ 2
  | .three, s => s.toNat ≥ 3

/-- **Speaker access** = number of objects (out of 3) the speaker observes.
A `Fin 4` indexed at 0..3. The paper restricts to {1, 2, 3}; access=0
(speaker observes nothing) is well-defined but unused.

Carrying this as `Fin 4` instead of a custom `Access` enum eliminates the
`Access.toNat` indirection — `a.val` is just the access value and
`Fin (a.val + 1)` reduces in type position when `a` is concrete. -/
abbrev Access : Type := Fin 4

namespace Access

/-- Access value 1 (speaker observes 1 of 3 objects). -/
abbrev a1 : Access := 1
/-- Access value 2 (speaker observes 2 of 3 objects). -/
abbrev a2 : Access := 2
/-- Access value 3 — full access (speaker observes all 3 objects). -/
abbrev a3 : Access := 3

/-- Compatibility shim: `a.toNat = a.val` since `Access = Fin 4`. -/
abbrev toNat (a : Access) : Nat := a.val

theorem toNat_le_three (a : Access) : a.toNat ≤ 3 :=
  Nat.lt_succ_iff.mp a.isLt

end Access

open scoped ENNReal
open Phenomena.ScalarImplicatures.GoodmanStuhlmuller2013

/-! ## §2. World prior — uniform on `WorldState` -/

noncomputable def worldPrior : PMF WorldState := PMF.uniformOfFintype WorldState

theorem worldPrior_ne_zero (w : WorldState) : worldPrior w ≠ 0 :=
  (worldPrior.mem_support_iff w).mp (PMF.mem_support_uniformOfFintype w)

/-- The uniform world prior assigns `ENNReal.ofReal (1/4)` to every world. -/
theorem worldPrior_apply (s : WorldState) :
    worldPrior s = ENNReal.ofReal (1/4 : ℝ) := by
  unfold worldPrior
  rw [PMF.uniformOfFintype_apply]
  show ((4 : ℕ) : ℝ≥0∞)⁻¹ = _
  rw [show ((4 : ℕ) : ℝ≥0∞) = ENNReal.ofReal 4 from by simp,
      ← ENNReal.ofReal_inv_of_pos (by norm_num)]
  congr 1; norm_num

/-! ## §3. Hypergeometric observation kernel

`obsKernel a w : PMF (Fin (a.toNat + 1))` is the hypergeometric distribution
over count outcomes when the speaker observes `a.toNat` of the 3 objects, of
which `w.toNat` have the property. Built directly from `PMF.hypergeometric`. -/

noncomputable def obsKernel (a : Access) (w : WorldState) : PMF (Fin (a.toNat + 1)) :=
  PMF.hypergeometric 3 w.toNat a.toNat a.toNat_le_three w.toNat_le_three

/-- Closed-form observation kernel value: `C(K, k) · C(N-K, n-k) / C(N, n)`. -/
theorem obsKernel_apply (a : Access) (w : WorldState) (k : Fin (a.toNat + 1)) :
    obsKernel a w k =
      (w.toNat.choose k.val * (3 - w.toNat).choose (a.toNat - k.val) : ℕ) /
      ((3).choose a.toNat : ℝ≥0∞) :=
  PMF.hypergeometric_apply _ _ _ _ _ _

/-- The kernel is non-zero iff the count is hypergeometric-feasible. -/
theorem obsKernel_apply_ne_zero_iff (a : Access) (w : WorldState) (k : Fin (a.toNat + 1)) :
    obsKernel a w k ≠ 0 ↔ k.val ≤ w.toNat ∧ a.toNat - k.val ≤ 3 - w.toNat :=
  PMF.hypergeometric_apply_ne_zero_iff _ _ _ _ _ _

/-! ## §4. Speaker belief — `PMF.posterior` of `obsKernel` -/

/-- A witness world for which `obsKernel a w k > 0`: the world whose
toNat matches `k.val` (clamped to ≤ 3). -/
private def witnessWorld (k : ℕ) : WorldState :=
  match k with
  | 0 => .s0
  | 1 => .s1
  | 2 => .s2
  | _ => .s3

private theorem obsMarginal_ne_zero (a : Access) (k : Fin (a.toNat + 1)) :
    PMF.marginal (obsKernel a) worldPrior k ≠ 0 := by
  refine PMF.marginal_ne_zero _ worldPrior k
    (worldPrior_ne_zero (witnessWorld k.val)) ?_
  rw [obsKernel_apply_ne_zero_iff]
  -- For our witness, k.val ≤ w.toNat and a.toNat - k.val ≤ 3 - w.toNat
  obtain ⟨n, hn⟩ := k
  have hn' : n ≤ a.toNat := Nat.lt_succ_iff.mp hn
  have ha : a.toNat ≤ 3 := a.toNat_le_three
  -- Case analysis on n.
  match n, hn' with
  | 0, _ => exact ⟨by simp [witnessWorld, WorldState.toNat], by simp [witnessWorld, WorldState.toNat]; omega⟩
  | 1, _ => exact ⟨by simp [witnessWorld, WorldState.toNat], by simp [witnessWorld, WorldState.toNat]; omega⟩
  | 2, _ => exact ⟨by simp [witnessWorld, WorldState.toNat], by simp [witnessWorld, WorldState.toNat]; omega⟩
  | 3, _ => exact ⟨by simp [witnessWorld, WorldState.toNat], by simp [witnessWorld, WorldState.toNat]; omega⟩
  | n+4, h => exact absurd h (by omega)

/-- Speaker's posterior over worlds given a count observation. -/
noncomputable def speakerBelief (a : Access) (k : Fin (a.toNat + 1)) : PMF WorldState :=
  PMF.posterior (obsKernel a) worldPrior k (obsMarginal_ne_zero a k)

/-! ## §5. obsCompatible — combinatorial feasibility -/

/-- A world `s` is compatible with observing `k.val` successes out of `a.toNat`
draws iff the hypergeometric numerator at `(K=s.toNat, k=k.val)` is non-zero. -/
def obsCompatible (a : Access) (k : Fin (a.toNat + 1)) (s : WorldState) : Bool :=
  k.val ≤ s.toNat && a.toNat - k.val ≤ 3 - s.toNat

/-! ## §6. qualityOk — utterance quality filter -/

/-- An utterance `u` is quality-OK at observation `(a, k)` iff `u` is true at
every world compatible with `(a, k)`. -/
def qualityOk {U : Type*} (m : U → WorldState → Bool)
    (a : Access) (k : Fin (a.toNat + 1)) (u : U) : Bool :=
  [WorldState.s0, .s1, .s2, .s3].all fun s => !obsCompatible a k s || m u s

/-! ## §7. lexReal — uniform-on-extension literal probability -/

noncomputable def lexReal {U : Type*} [Fintype U]
    (meaning : U → WorldState → Bool) (u : U) (s : WorldState) : ℝ :=
  if meaning u s then ((RSA.extensionOf meaning u).card : ℝ)⁻¹ else 0

/-! ## §8. beliefReal — toReal projection of speakerBelief -/

noncomputable def beliefReal (a : Access) (k : Fin (a.toNat + 1)) (s : WorldState) : ℝ :=
  (speakerBelief a k s).toReal

/-! ## §9. s1Score — softmaxBelief instance -/

noncomputable abbrev s1Score {U : Type*} [Fintype U]
    (meaning : U → WorldState → Bool) (α : ℝ)
    (a : Access) (k : Fin (a.toNat + 1)) (u : U) : ℝ≥0∞ :=
  RSA.softmaxBelief (lexReal meaning) (beliefReal a k) α
    (fun u' => qualityOk meaning a k u' = true) u

/-! ## §10. S1g — speaker conditional on observation -/

noncomputable def S1g {U : Type*} [Fintype U]
    (meaning : U → WorldState → Bool) (α : ℝ)
    (a : Access) (k : Fin (a.toNat + 1))
    (h0 : ∑' u, s1Score meaning α a k u ≠ 0) : PMF U :=
  PMF.normalize (s1Score meaning α a k ·) h0
    (RSA.softmaxBelief_tsum_ne_top _ _ _ _)

/-! ## §11. marginalSpeaker — `PMF.bind` over the obs kernel

Since we use `PMF.bind` (not `bindOnSupport`), we need `S1g` defined at every
`k`, not just kernel-supported ones. The cover hypothesis `hCov` therefore
quantifies over all `k : Fin (a.toNat + 1)`. With `WithSilence`, this is
automatic via `cover_silent` (silence is qOk everywhere). -/

noncomputable def marginalSpeaker {U : Type*} [Fintype U]
    (meaning : U → WorldState → Bool) (α : ℝ) (a : Access) (w : WorldState)
    (hCov : ∀ k : Fin (a.toNat + 1), ∃ u : U, qualityOk meaning a k u) :
    PMF U :=
  (obsKernel a w).bind fun k =>
    S1g meaning α a k
      (RSA.softmaxBelief_tsum_ne_zero_of_witness (hCov k).choose_spec)

/-! ## §12. L1 — Bayesian inversion of the marginal speaker -/

noncomputable def L1 {U : Type*} [Fintype U]
    (meaning : U → WorldState → Bool) (α : ℝ) (a : Access)
    (hCov : ∀ k : Fin (a.toNat + 1), ∃ u : U, qualityOk meaning a k u) (u : U)
    (hMarg : PMF.marginal (fun w => marginalSpeaker meaning α a w hCov) worldPrior u ≠ 0) :
    PMF WorldState :=
  PMF.posterior (fun w => marginalSpeaker meaning α a w hCov) worldPrior u hMarg

/-! ## §13. cover_silent — silence is universally qOk

`liftMeaning m none = true` at every world, so silence passes `qualityOk` at
every observation. The cover hypothesis is universally satisfiable. -/

open RSA (WithSilence liftMeaning)

theorem cover_silent {U : Type*} (m : U → WorldState → Bool) (a : Access) :
    ∀ k : Fin (a.toNat + 1), ∃ u : WithSilence U, qualityOk (liftMeaning m) a k u := by
  intro k
  refine ⟨none, ?_⟩
  unfold qualityOk
  simp [RSA.liftMeaning_none]

/-! ## §14. obsKernel value lemmas (per (a, w, k))

Closed-form values for `obsKernel a w k` at each combination — derived from
`obsKernel_apply` by unfolding the `Nat.choose` arithmetic. These are the
numerical foundations for the marginalSpeaker / findings layer below. -/

-- .a3 (full access, deterministic): kernel concentrates on `k = w.toNat`.

private theorem obsKernel_a3_s0_diag : obsKernel .a3 .s0 ⟨0, by decide⟩ = 1 := by
  rw [obsKernel_apply]; unfold WorldState.toNat Access.toNat
  show ((1 : ℕ) : ℝ≥0∞) / ((1 : ℕ) : ℝ≥0∞) = _
  norm_num

private theorem obsKernel_a3_s1_diag : obsKernel .a3 .s1 ⟨1, by decide⟩ = 1 := by
  rw [obsKernel_apply]; unfold WorldState.toNat Access.toNat
  show ((1 : ℕ) : ℝ≥0∞) / ((1 : ℕ) : ℝ≥0∞) = _
  norm_num

private theorem obsKernel_a3_s2_diag : obsKernel .a3 .s2 ⟨2, by decide⟩ = 1 := by
  rw [obsKernel_apply]; unfold WorldState.toNat Access.toNat
  show ((1 : ℕ) : ℝ≥0∞) / ((1 : ℕ) : ℝ≥0∞) = _
  norm_num

private theorem obsKernel_a3_s3_diag : obsKernel .a3 .s3 ⟨3, by decide⟩ = 1 := by
  rw [obsKernel_apply]; unfold WorldState.toNat Access.toNat
  show ((1 : ℕ) : ℝ≥0∞) / ((1 : ℕ) : ℝ≥0∞) = _
  norm_num

private theorem obsKernel_a3_off (w : WorldState) (k : Fin 4) (h : k.val ≠ w.toNat) :
    obsKernel .a3 w k = 0 := by
  rw [obsKernel_apply]
  -- One of C(K,k) or C(N-K,n-k) is zero. We do case analysis on w.
  cases w
  · -- s0: K=0, n-k = 3-k. C(0, k) = 0 unless k=0; C(3, 3-k) requires 3-k ≤ 3 (always).
    -- Excluded: k = 0. So k.val ≠ 0 → C(0,k) = 0.
    obtain ⟨n, hn⟩ := k
    interval_cases n
    · exact absurd rfl h
    all_goals (unfold WorldState.toNat Access.toNat; simp [Nat.choose])
  · -- s1: K=1, k.val ≠ 1.
    obtain ⟨n, hn⟩ := k
    interval_cases n
    · unfold WorldState.toNat Access.toNat; simp [Nat.choose]
    · exact absurd rfl h
    · unfold WorldState.toNat Access.toNat; simp [Nat.choose]
    · unfold WorldState.toNat Access.toNat; simp [Nat.choose]
  · obtain ⟨n, hn⟩ := k
    interval_cases n
    · unfold WorldState.toNat Access.toNat; simp [Nat.choose]
    · unfold WorldState.toNat Access.toNat; simp [Nat.choose]
    · exact absurd rfl h
    · unfold WorldState.toNat Access.toNat; simp [Nat.choose]
  · obtain ⟨n, hn⟩ := k
    interval_cases n
    · unfold WorldState.toNat Access.toNat; simp [Nat.choose]
    · unfold WorldState.toNat Access.toNat; simp [Nat.choose]
    · unfold WorldState.toNat Access.toNat; simp [Nat.choose]
    · exact absurd rfl h

-- .a2 (partial access, n=2): C(3, 2) = 3 in denominator.

private theorem obsKernel_a2_s0_k0 : obsKernel .a2 .s0 ⟨0, by decide⟩ = 1 := by
  rw [obsKernel_apply]; unfold WorldState.toNat Access.toNat
  show ((1 * 3 : ℕ) : ℝ≥0∞) / ((3 : ℕ) : ℝ≥0∞) = _
  rw [show ((1 * 3 : ℕ) : ℝ≥0∞) = (3 : ℝ≥0∞) from by simp]
  exact ENNReal.div_self (by simp) (by simp)

private theorem obsKernel_a2_s1_k0 :
    obsKernel .a2 .s1 ⟨0, by decide⟩ = ENNReal.ofReal (1/3) := by
  rw [obsKernel_apply]; unfold WorldState.toNat Access.toNat
  show ((1 * 1 : ℕ) : ℝ≥0∞) / ((3 : ℕ) : ℝ≥0∞) = _
  rw [show ((1 * 1 : ℕ) : ℝ≥0∞) = ENNReal.ofReal 1 from by simp,
      show ((3 : ℕ) : ℝ≥0∞) = ENNReal.ofReal 3 from by simp,
      ← ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 3)]

private theorem obsKernel_a2_s1_k1 :
    obsKernel .a2 .s1 ⟨1, by decide⟩ = ENNReal.ofReal (2/3) := by
  rw [obsKernel_apply]; unfold WorldState.toNat Access.toNat
  show ((1 * 2 : ℕ) : ℝ≥0∞) / ((3 : ℕ) : ℝ≥0∞) = _
  rw [show ((1 * 2 : ℕ) : ℝ≥0∞) = ENNReal.ofReal 2 from by simp,
      show ((3 : ℕ) : ℝ≥0∞) = ENNReal.ofReal 3 from by simp,
      ← ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 3)]

private theorem obsKernel_a2_s2_k1 :
    obsKernel .a2 .s2 ⟨1, by decide⟩ = ENNReal.ofReal (2/3) := by
  rw [obsKernel_apply]; unfold WorldState.toNat Access.toNat
  show ((2 * 1 : ℕ) : ℝ≥0∞) / ((3 : ℕ) : ℝ≥0∞) = _
  rw [show ((2 * 1 : ℕ) : ℝ≥0∞) = ENNReal.ofReal 2 from by simp,
      show ((3 : ℕ) : ℝ≥0∞) = ENNReal.ofReal 3 from by simp,
      ← ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 3)]

private theorem obsKernel_a2_s2_k2 :
    obsKernel .a2 .s2 ⟨2, by decide⟩ = ENNReal.ofReal (1/3) := by
  rw [obsKernel_apply]; unfold WorldState.toNat Access.toNat
  show ((1 * 1 : ℕ) : ℝ≥0∞) / ((3 : ℕ) : ℝ≥0∞) = _
  rw [show ((1 * 1 : ℕ) : ℝ≥0∞) = ENNReal.ofReal 1 from by simp,
      show ((3 : ℕ) : ℝ≥0∞) = ENNReal.ofReal 3 from by simp,
      ← ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 3)]

private theorem obsKernel_a2_s3_k2 : obsKernel .a2 .s3 ⟨2, by decide⟩ = 1 := by
  rw [obsKernel_apply]; unfold WorldState.toNat Access.toNat
  show ((3 * 1 : ℕ) : ℝ≥0∞) / ((3 : ℕ) : ℝ≥0∞) = _
  rw [show ((3 * 1 : ℕ) : ℝ≥0∞) = (3 : ℝ≥0∞) from by simp]
  exact ENNReal.div_self (by simp) (by simp)

private theorem obsKernel_a2_off (w : WorldState) (k : Fin 3)
    (h : ¬ (k.val ≤ w.toNat ∧ 2 - k.val ≤ 3 - w.toNat)) :
    obsKernel .a2 w k = 0 := by
  by_contra hne
  exact h ((obsKernel_apply_ne_zero_iff .a2 w k).mp hne)

-- .a1 (minimal access, n=1): C(3, 1) = 3 in denominator.

private theorem obsKernel_a1_s0_k0 : obsKernel .a1 .s0 ⟨0, by decide⟩ = 1 := by
  rw [obsKernel_apply]; unfold WorldState.toNat Access.toNat
  show ((1 * 3 : ℕ) : ℝ≥0∞) / ((3 : ℕ) : ℝ≥0∞) = _
  rw [show ((1 * 3 : ℕ) : ℝ≥0∞) = (3 : ℝ≥0∞) from by simp]
  exact ENNReal.div_self (by simp) (by simp)

private theorem obsKernel_a1_s1_k0 :
    obsKernel .a1 .s1 ⟨0, by decide⟩ = ENNReal.ofReal (2/3) := by
  rw [obsKernel_apply]; unfold WorldState.toNat Access.toNat
  show ((1 * 2 : ℕ) : ℝ≥0∞) / ((3 : ℕ) : ℝ≥0∞) = _
  rw [show ((1 * 2 : ℕ) : ℝ≥0∞) = ENNReal.ofReal 2 from by simp,
      show ((3 : ℕ) : ℝ≥0∞) = ENNReal.ofReal 3 from by simp,
      ← ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 3)]

private theorem obsKernel_a1_s1_k1 :
    obsKernel .a1 .s1 ⟨1, by decide⟩ = ENNReal.ofReal (1/3) := by
  rw [obsKernel_apply]; unfold WorldState.toNat Access.toNat
  show ((1 * 1 : ℕ) : ℝ≥0∞) / ((3 : ℕ) : ℝ≥0∞) = _
  rw [show ((1 * 1 : ℕ) : ℝ≥0∞) = ENNReal.ofReal 1 from by simp,
      show ((3 : ℕ) : ℝ≥0∞) = ENNReal.ofReal 3 from by simp,
      ← ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 3)]

private theorem obsKernel_a1_s2_k0 :
    obsKernel .a1 .s2 ⟨0, by decide⟩ = ENNReal.ofReal (1/3) := by
  rw [obsKernel_apply]; unfold WorldState.toNat Access.toNat
  show ((1 * 1 : ℕ) : ℝ≥0∞) / ((3 : ℕ) : ℝ≥0∞) = _
  rw [show ((1 * 1 : ℕ) : ℝ≥0∞) = ENNReal.ofReal 1 from by simp,
      show ((3 : ℕ) : ℝ≥0∞) = ENNReal.ofReal 3 from by simp,
      ← ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 3)]

private theorem obsKernel_a1_s2_k1 :
    obsKernel .a1 .s2 ⟨1, by decide⟩ = ENNReal.ofReal (2/3) := by
  rw [obsKernel_apply]; unfold WorldState.toNat Access.toNat
  show ((2 * 1 : ℕ) : ℝ≥0∞) / ((3 : ℕ) : ℝ≥0∞) = _
  rw [show ((2 * 1 : ℕ) : ℝ≥0∞) = ENNReal.ofReal 2 from by simp,
      show ((3 : ℕ) : ℝ≥0∞) = ENNReal.ofReal 3 from by simp,
      ← ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 3)]

private theorem obsKernel_a1_s3_k1 : obsKernel .a1 .s3 ⟨1, by decide⟩ = 1 := by
  rw [obsKernel_apply]; unfold WorldState.toNat Access.toNat
  show ((3 * 1 : ℕ) : ℝ≥0∞) / ((3 : ℕ) : ℝ≥0∞) = _
  rw [show ((3 * 1 : ℕ) : ℝ≥0∞) = (3 : ℝ≥0∞) from by simp]
  exact ENNReal.div_self (by simp) (by simp)

private theorem obsKernel_a1_off (w : WorldState) (k : Fin 2)
    (h : ¬ (k.val ≤ w.toNat ∧ 1 - k.val ≤ 3 - w.toNat)) :
    obsKernel .a1 w k = 0 := by
  by_contra hne
  exact h ((obsKernel_apply_ne_zero_iff .a1 w k).mp hne)

/-! ## §15. marginalSpeaker collapse — `.a3` (concentrated kernel)

At full access, `obsKernel .a3 w` puts all mass on a single `k = w.toNat`,
so `marginalSpeaker = (obsKernel .a3 w).bind (S1g .a3 _)` collapses to a
single `S1g` evaluation at the diagonal `k`. **Polymorphic over `w`** —
replaces what was previously 4 per-world specializations. -/

/-- Diagonal `obsKernel .a3 w ⟨w.toNat, _⟩ = 1` for any world. -/
private theorem obsKernel_a3_diag (w : WorldState) :
    obsKernel .a3 w ⟨w.toNat, by cases w <;> decide⟩ = 1 := by
  cases w
  · exact obsKernel_a3_s0_diag
  · exact obsKernel_a3_s1_diag
  · exact obsKernel_a3_s2_diag
  · exact obsKernel_a3_s3_diag

private theorem marginalSpeaker_a3_apply
    {U : Type*} [Fintype U] (m : U → WorldState → Bool) (w : WorldState)
    (hCov : ∀ k : Fin (Access.a3.toNat + 1), ∃ u : U, qualityOk m .a3 k u) (u : U) :
    marginalSpeaker m 1 .a3 w hCov u =
      S1g m 1 .a3 ⟨w.toNat, by cases w <;> decide⟩
        (RSA.softmaxBelief_tsum_ne_zero_of_witness
          (hCov ⟨w.toNat, by cases w <;> decide⟩).choose_spec) u := by
  show ((obsKernel .a3 w).bind _) u = _
  rw [PMF.bind_apply, tsum_eq_single ⟨w.toNat, by cases w <;> decide⟩]
  · rw [obsKernel_a3_diag, one_mul]
  · intro k hk
    have h := obsKernel_a3_off w k (by
      intro heq; apply hk; apply Fin.ext; simpa [WorldState.toNat] using heq)
    rw [h, zero_mul]

/-! ## §17. Extension cardinalities for silence-extended models

Per-(meaning, utterance) extension cardinalities, locally tagged for
`pmf_eval_simps` so the universal `s1Score_liftMeaning_apply_eq_ite`
(§17b) reduces to concrete `ofReal((card)⁻¹)` values. -/

private theorem extensionOf_qLifted_some_card :
    (RSA.extensionOf (liftMeaning qMeaning) (some QUtt.some_)).card = 3 := by decide

private theorem extensionOf_qLifted_all_card :
    (RSA.extensionOf (liftMeaning qMeaning) (some QUtt.all)).card = 1 := by decide

private theorem extensionOf_qLifted_none_card :
    (RSA.extensionOf (liftMeaning qMeaning) (some QUtt.none_)).card = 1 := by decide

private theorem extensionOf_qLifted_silent_card :
    (RSA.extensionOf (liftMeaning qMeaning) (none : WithSilence QUtt)).card = 4 := by decide

-- File-scoped tagging keeps these private paper-specific cards out of the
-- substrate simp set (audit hygiene rule).
attribute [local pmf_eval_simps]
  extensionOf_qLifted_some_card
  extensionOf_qLifted_all_card
  extensionOf_qLifted_none_card
  extensionOf_qLifted_silent_card


private theorem extensionOf_lbLifted_one_card :
    (RSA.extensionOf (liftMeaning lbMeaning) (some NumUtt.one)).card = 3 := by decide

private theorem extensionOf_lbLifted_two_card :
    (RSA.extensionOf (liftMeaning lbMeaning) (some NumUtt.two)).card = 2 := by decide

private theorem extensionOf_lbLifted_three_card :
    (RSA.extensionOf (liftMeaning lbMeaning) (some NumUtt.three)).card = 1 := by decide

private theorem extensionOf_lbLifted_silent_card :
    (RSA.extensionOf (liftMeaning lbMeaning) (none : WithSilence NumUtt)).card = 4 := by decide

attribute [local pmf_eval_simps]
  extensionOf_lbLifted_one_card
  extensionOf_lbLifted_two_card
  extensionOf_lbLifted_three_card
  extensionOf_lbLifted_silent_card


/-! ## §17a. Generic s1Score lemmas (work for any (a, k))

When `qOk u` passes, `liftMeaning`-lifted utterances have a uniform lex
value on the belief support (because: `qOk` ⇒ `m u s = true` at all
compatible `s` ⊇ belief support ⇒ `lex u s = 1/(card extension)`).

`softmaxBelief_uniform_on_support` then collapses `s1Score = ENNReal.ofReal (1/c)`. -/

private theorem belief_support_compat (a : Access) (k : Fin (a.toNat + 1)) (s : WorldState)
    (h : beliefReal a k s ≠ 0) : obsCompatible a k s = true := by
  unfold beliefReal at h
  have : speakerBelief a k s ≠ 0 := by
    intro h'; exact h (h' ▸ ENNReal.toReal_zero)
  unfold speakerBelief at this
  rw [PMF.posterior_apply] at this
  have h_kernel : obsKernel a s k ≠ 0 := by
    intro h_zero; apply this; rw [h_zero, mul_zero, zero_mul]
  unfold obsCompatible
  have ⟨h1, h2⟩ := (obsKernel_apply_ne_zero_iff a s k).mp h_kernel
  exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true h1, decide_eq_true h2⟩

private theorem belief_sum_eq_one (a : Access) (k : Fin (a.toNat + 1)) :
    (∑ s : WorldState, beliefReal a k s) = 1 := by
  unfold beliefReal
  rw [show (∑ s : WorldState, (speakerBelief a k s).toReal) =
        (∑' s : WorldState, (speakerBelief a k s).toReal) from
        (tsum_eq_sum (s := Finset.univ) (fun s hs => absurd (Finset.mem_univ s) hs)).symm]
  rw [← ENNReal.tsum_toReal_eq (fun s => PMF.apply_ne_top _ _),
      PMF.tsum_coe, ENNReal.toReal_one]

/-- Generic s1Score evaluation: when qOk passes, `s1Score = ENNReal.ofReal (1/c)`
where `c = (extensionOf m u).card`. -/
private theorem s1Score_uniform_apply
    {U : Type*} [Fintype U] [DecidableEq U]
    (m : U → WorldState → Bool) (a : Access) (k : Fin (a.toNat + 1))
    (u : WithSilence U) (c : ℕ) (hc : c ≠ 0)
    (h_qok : qualityOk (liftMeaning m) a k u = true)
    (h_card : (RSA.extensionOf (liftMeaning m) u).card = c) :
    s1Score (liftMeaning m) 1 a k u = ENNReal.ofReal (1/c : ℝ) := by
  show RSA.softmaxBelief (lexReal (liftMeaning m)) (beliefReal a k) 1
        (fun u' => qualityOk (liftMeaning m) a k u' = true) u = _
  refine RSA.softmaxBelief_uniform_on_support _ _ _ _ (1/c : ℝ) h_qok ?_ ?_
    (belief_sum_eq_one a k)
  · intro s hbelief
    have hc' : obsCompatible a k s = true := belief_support_compat a k s hbelief
    have hmu : (liftMeaning m) u s = true := by
      unfold qualityOk at h_qok
      rw [List.all_eq_true] at h_qok
      have hmem : s ∈ ([WorldState.s0, .s1, .s2, .s3] : List _) := by cases s <;> simp
      have := h_qok s hmem
      simp [hc'] at this
      exact this
    unfold lexReal
    rw [if_pos hmu, h_card]
    field_simp
  · positivity

/-! ## §17b. Universal `pmf_eval`-friendly if-form for `s1Score (liftMeaning _)`

The universal `s1Score_uniform_apply` is hypothesis-laden (h_qok, h_card, h_pos)
so `simp` can't use it. `s1Score_liftMeaning_apply_eq_ite` below is parameterized
over the meaning function `m` and has no free preconditions — the qOk branch is
encoded as a decidable `if`, and extension nonemptiness is proved universally
via the `witnessWorld` helper.

This collapses what previously required two paper-tagged lemmas (one per meaning)
into one polymorphic lemma. The `local attribute [pmf_eval_simps]` keeps the
tag file-scoped so it does not pollute the substrate set with a private paper
lemma (audit hygiene rule). -/

/-- The witness world for `k.val` is `obsCompatible` at any `(a, k)`. This is
the geometric foundation behind extension nonemptiness when qOk holds: qOk
asserts the meaning is true at every compatible world; the witnessWorld is one. -/
private theorem witnessWorld_obsCompatible (a : Access) (k : Fin (a.toNat + 1)) :
    obsCompatible a k (witnessWorld k.val) = true := by
  unfold obsCompatible
  obtain ⟨n, hn⟩ := k
  have hn' : n ≤ a.toNat := Nat.lt_succ_iff.mp hn
  have ha : a.toNat ≤ 3 := a.toNat_le_three
  rw [Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  all_goals
    match n, hn' with
    | 0, _ => first | (simp [witnessWorld, WorldState.toNat]; omega) | simp [witnessWorld, WorldState.toNat]
    | 1, _ => first | (simp [witnessWorld, WorldState.toNat]; omega) | simp [witnessWorld, WorldState.toNat]
    | 2, _ => first | (simp [witnessWorld, WorldState.toNat]; omega) | simp [witnessWorld, WorldState.toNat]
    | 3, _ => first | (simp [witnessWorld, WorldState.toNat]; omega) | simp [witnessWorld, WorldState.toNat]
    | n+4, h => omega

/-- When qOk holds at `(m, a, k, u)`, the extension of `liftMeaning m u` is
nonempty: the witnessWorld for `k.val` is obsCompatible (above), and qOk
forces meaning at compatible worlds. -/
private theorem extensionOf_liftMeaning_nonempty_of_qok
    {U : Type*} [Fintype U] [DecidableEq U]
    (m : U → WorldState → Bool) (a : Access) (k : Fin (a.toNat + 1))
    (u : WithSilence U) (h_qok : qualityOk (liftMeaning m) a k u = true) :
    (RSA.extensionOf (liftMeaning m) u).Nonempty := by
  refine ⟨witnessWorld k.val, ?_⟩
  rw [RSA.mem_extensionOf]
  have hcompat := witnessWorld_obsCompatible a k
  unfold qualityOk at h_qok
  rw [List.all_eq_true] at h_qok
  have hmem : witnessWorld k.val ∈ ([WorldState.s0, .s1, .s2, .s3] : List _) := by
    cases (witnessWorld k.val) <;> simp
  have := h_qok (witnessWorld k.val) hmem
  simp [hcompat] at this
  exact this

/-- **Universal if-form for `s1Score (liftMeaning m)`** — paper-independent
closed-form variant of `s1Score_uniform_apply` with the qOk hypothesis encoded
as a decidable `if`. Replaces per-meaning duplication with one lemma
parameterized over `m : U → WorldState → Bool`. -/
private theorem s1Score_liftMeaning_apply_eq_ite
    {U : Type*} [Fintype U] [DecidableEq U]
    (m : U → WorldState → Bool) (a : Access) (k : Fin (a.toNat + 1))
    (u : WithSilence U) :
    s1Score (liftMeaning m) 1 a k u =
      if qualityOk (liftMeaning m) a k u = true
      then ENNReal.ofReal (((RSA.extensionOf (liftMeaning m) u).card : ℝ)⁻¹)
      else 0 := by
  by_cases h : qualityOk (liftMeaning m) a k u = true
  · rw [if_pos h]
    have h_ne : (RSA.extensionOf (liftMeaning m) u).card ≠ 0 :=
      Finset.card_ne_zero.mpr (extensionOf_liftMeaning_nonempty_of_qok m a k u h)
    rw [s1Score_uniform_apply m a k u
          (RSA.extensionOf (liftMeaning m) u).card h_ne h rfl]
    congr 1; field_simp
  · rw [if_neg h]
    exact RSA.softmaxBelief_eq_zero_of_not_qOk h

-- File-scoped: the if-form depends on Access/WorldState/qualityOk, so we keep
-- the simp tag local rather than polluting the substrate set with a private
-- paper lemma (audit hygiene rule).
attribute [local pmf_eval_simps]
  s1Score_liftMeaning_apply_eq_ite
  obsKernel_apply

/-- Tag the missing `.a2` obsKernel zero cases (used in §20 .a2 findings)
into the local `pmf_eval_simps` set so the macro can fire `zero_mul` cleanups. -/
private theorem obsKernel_a2_s3_k1_zero : obsKernel .a2 .s3 ⟨1, by decide⟩ = 0 :=
  obsKernel_a2_off .s3 ⟨1, by decide⟩ (by
    rintro ⟨_, h2⟩; simp [WorldState.toNat] at h2)

private theorem obsKernel_a2_s1_k2_zero : obsKernel .a2 .s1 ⟨2, by decide⟩ = 0 :=
  obsKernel_a2_off .s1 ⟨2, by decide⟩ (by
    rintro ⟨h1, _⟩; simp [WorldState.toNat] at h1)

private theorem obsKernel_a2_s0_k1_zero : obsKernel .a2 .s0 ⟨1, by decide⟩ = 0 :=
  obsKernel_a2_off .s0 ⟨1, by decide⟩ (by
    rintro ⟨h1, _⟩; simp [WorldState.toNat] at h1)

private theorem obsKernel_a2_s0_k2_zero : obsKernel .a2 .s0 ⟨2, by decide⟩ = 0 :=
  obsKernel_a2_off .s0 ⟨2, by decide⟩ (by
    rintro ⟨h1, _⟩; simp [WorldState.toNat] at h1)

private theorem obsKernel_a2_s2_k0_zero : obsKernel .a2 .s2 ⟨0, by decide⟩ = 0 :=
  obsKernel_a2_off .s2 ⟨0, by decide⟩ (by
    rintro ⟨_, h2⟩; simp [WorldState.toNat] at h2)

private theorem obsKernel_a2_s3_k0_zero : obsKernel .a2 .s3 ⟨0, by decide⟩ = 0 :=
  obsKernel_a2_off .s3 ⟨0, by decide⟩ (by
    rintro ⟨_, h2⟩; simp [WorldState.toNat] at h2)

attribute [local pmf_eval_simps]
  obsKernel_a2_s3_k1_zero obsKernel_a2_s1_k2_zero
  obsKernel_a2_s0_k1_zero obsKernel_a2_s0_k2_zero
  obsKernel_a2_s2_k0_zero obsKernel_a2_s3_k0_zero

/-- Sum unfolder for `WithSilence U` over a derived-Fintype `U`. Required
because `Fin.sum_univ_*` doesn't apply to custom enums; users supply this
at-call-site with their specific `U`. Local-tagged for `pmf_eval_simps`
in this file. -/
private theorem WithSilence_QUtt_sum_univ {β : Type*} [AddCommMonoid β]
    (f : WithSilence QUtt → β) :
    ∑ i, f i =
      f none + (f (some .none_) + (f (some .some_) + (f (some .all) + 0))) := by
  rfl

private theorem WithSilence_NumUtt_sum_univ {β : Type*} [AddCommMonoid β]
    (f : WithSilence NumUtt → β) :
    ∑ i, f i =
      f none + (f (some .one) + (f (some .two) + (f (some .three) + 0))) := by
  rfl

/-- Bare `QUtt` sum unfolder. Needed when `Fintype.sum_option` fires and
leaves a residual `∑ i : QUtt, f (some i)`. -/
private theorem QUtt_sum_univ {β : Type*} [AddCommMonoid β] (f : QUtt → β) :
    ∑ i, f i = f .none_ + (f .some_ + (f .all + 0)) := by
  rfl

private theorem NumUtt_sum_univ {β : Type*} [AddCommMonoid β] (f : NumUtt → β) :
    ∑ i, f i = f .one + (f .two + (f .three + 0)) := by
  rfl

attribute [local pmf_eval_simps]
  WithSilence_QUtt_sum_univ WithSilence_NumUtt_sum_univ
  QUtt_sum_univ NumUtt_sum_univ

/-! ### `pmf_eval` smoke tests for the if-form variants -/

example : s1Score (liftMeaning qMeaning) 1 .a3 ⟨2, by decide⟩
            (some QUtt.some_) = ENNReal.ofReal (1/3 : ℝ) := by
  pmf_eval

example : s1Score (liftMeaning qMeaning) 1 .a3 ⟨2, by decide⟩
            (some QUtt.none_) = 0 := by
  pmf_eval

example : s1Score (liftMeaning qMeaning) 1 .a3 ⟨2, by decide⟩
            (none : WithSilence QUtt) = ENNReal.ofReal (1/4 : ℝ) := by
  pmf_eval

/-! ## §19a. s1Score evaluations for `.a1`

At (.a1, k=0): compatible worlds = {s0, s1, s2}. Only silence is qOk; all
other quantifiers / numerals are false at s0 ⇒ qOk fails ⇒ score 0.

At (.a1, k=1): compatible worlds = {s1, s2, s3}. Silence and `some_`/`one`
are qOk; `none_`, `all`, `two`, `three` fail. -/

-- (.a1, k=0): only silence has positive score.

private theorem s1Score_qLifted_a1_k0_silent :
    s1Score (liftMeaning qMeaning) 1 .a1 ⟨0, by decide⟩
      (none : WithSilence QUtt) = ENNReal.ofReal (1/4 : ℝ) :=
  s1Score_uniform_apply qMeaning .a1 ⟨0, by decide⟩ none 4 (by norm_num)
    (by decide) extensionOf_qLifted_silent_card

private theorem s1Score_qLifted_a1_k0_none :
    s1Score (liftMeaning qMeaning) 1 .a1 ⟨0, by decide⟩
      (some QUtt.none_) = 0 :=
  RSA.softmaxBelief_eq_zero_of_not_qOk (by decide)

private theorem s1Score_qLifted_a1_k0_some :
    s1Score (liftMeaning qMeaning) 1 .a1 ⟨0, by decide⟩
      (some QUtt.some_) = 0 :=
  RSA.softmaxBelief_eq_zero_of_not_qOk (by decide)

private theorem s1Score_qLifted_a1_k0_all :
    s1Score (liftMeaning qMeaning) 1 .a1 ⟨0, by decide⟩
      (some QUtt.all) = 0 :=
  RSA.softmaxBelief_eq_zero_of_not_qOk (by decide)

private theorem s1Score_lbLifted_a1_k0_silent :
    s1Score (liftMeaning lbMeaning) 1 .a1 ⟨0, by decide⟩
      (none : WithSilence NumUtt) = ENNReal.ofReal (1/4 : ℝ) :=
  s1Score_uniform_apply lbMeaning .a1 ⟨0, by decide⟩ none 4 (by norm_num)
    (by decide) extensionOf_lbLifted_silent_card

private theorem s1Score_lbLifted_a1_k0_one :
    s1Score (liftMeaning lbMeaning) 1 .a1 ⟨0, by decide⟩
      (some NumUtt.one) = 0 :=
  RSA.softmaxBelief_eq_zero_of_not_qOk (by decide)

private theorem s1Score_lbLifted_a1_k0_two :
    s1Score (liftMeaning lbMeaning) 1 .a1 ⟨0, by decide⟩
      (some NumUtt.two) = 0 :=
  RSA.softmaxBelief_eq_zero_of_not_qOk (by decide)

private theorem s1Score_lbLifted_a1_k0_three :
    s1Score (liftMeaning lbMeaning) 1 .a1 ⟨0, by decide⟩
      (some NumUtt.three) = 0 :=
  RSA.softmaxBelief_eq_zero_of_not_qOk (by decide)

-- (.a1, k=1): silence + `some_`/`one` are qOk.

private theorem s1Score_qLifted_a1_k1_silent :
    s1Score (liftMeaning qMeaning) 1 .a1 ⟨1, by decide⟩
      (none : WithSilence QUtt) = ENNReal.ofReal (1/4 : ℝ) :=
  s1Score_uniform_apply qMeaning .a1 ⟨1, by decide⟩ none 4 (by norm_num)
    (by decide) extensionOf_qLifted_silent_card

private theorem s1Score_qLifted_a1_k1_none :
    s1Score (liftMeaning qMeaning) 1 .a1 ⟨1, by decide⟩
      (some QUtt.none_) = 0 :=
  RSA.softmaxBelief_eq_zero_of_not_qOk (by decide)

private theorem s1Score_qLifted_a1_k1_some :
    s1Score (liftMeaning qMeaning) 1 .a1 ⟨1, by decide⟩
      (some QUtt.some_) = ENNReal.ofReal (1/3 : ℝ) :=
  s1Score_uniform_apply qMeaning .a1 ⟨1, by decide⟩ (some QUtt.some_) 3 (by norm_num)
    (by decide) extensionOf_qLifted_some_card

private theorem s1Score_qLifted_a1_k1_all :
    s1Score (liftMeaning qMeaning) 1 .a1 ⟨1, by decide⟩
      (some QUtt.all) = 0 :=
  RSA.softmaxBelief_eq_zero_of_not_qOk (by decide)

private theorem s1Score_lbLifted_a1_k1_silent :
    s1Score (liftMeaning lbMeaning) 1 .a1 ⟨1, by decide⟩
      (none : WithSilence NumUtt) = ENNReal.ofReal (1/4 : ℝ) :=
  s1Score_uniform_apply lbMeaning .a1 ⟨1, by decide⟩ none 4 (by norm_num)
    (by decide) extensionOf_lbLifted_silent_card

private theorem s1Score_lbLifted_a1_k1_one :
    s1Score (liftMeaning lbMeaning) 1 .a1 ⟨1, by decide⟩
      (some NumUtt.one) = ENNReal.ofReal (1/3 : ℝ) :=
  s1Score_uniform_apply lbMeaning .a1 ⟨1, by decide⟩ (some NumUtt.one) 3 (by norm_num)
    (by decide) extensionOf_lbLifted_one_card

private theorem s1Score_lbLifted_a1_k1_two :
    s1Score (liftMeaning lbMeaning) 1 .a1 ⟨1, by decide⟩
      (some NumUtt.two) = 0 :=
  RSA.softmaxBelief_eq_zero_of_not_qOk (by decide)

private theorem s1Score_lbLifted_a1_k1_three :
    s1Score (liftMeaning lbMeaning) 1 .a1 ⟨1, by decide⟩
      (some NumUtt.three) = 0 :=
  RSA.softmaxBelief_eq_zero_of_not_qOk (by decide)

/-! ## §19b. Sum-of-scores at `.a1` -/

private theorem sum_s1Score_qLifted_a1_k0 :
    (∑ u : WithSilence QUtt, s1Score (liftMeaning qMeaning) 1 .a1 ⟨0, by decide⟩ u) =
      ENNReal.ofReal (1/4 : ℝ) := by
  show s1Score (liftMeaning qMeaning) 1 .a1 ⟨0, by decide⟩ none +
        (s1Score (liftMeaning qMeaning) 1 .a1 ⟨0, by decide⟩ (some QUtt.none_) +
          (s1Score (liftMeaning qMeaning) 1 .a1 ⟨0, by decide⟩ (some QUtt.some_) +
            (s1Score (liftMeaning qMeaning) 1 .a1 ⟨0, by decide⟩ (some QUtt.all) + 0))) = _
  rw [s1Score_qLifted_a1_k0_silent, s1Score_qLifted_a1_k0_none,
      s1Score_qLifted_a1_k0_some, s1Score_qLifted_a1_k0_all]
  simp

private theorem sum_s1Score_qLifted_a1_k1 :
    (∑ u : WithSilence QUtt, s1Score (liftMeaning qMeaning) 1 .a1 ⟨1, by decide⟩ u) =
      ENNReal.ofReal (7/12 : ℝ) := by
  show s1Score (liftMeaning qMeaning) 1 .a1 ⟨1, by decide⟩ none +
        (s1Score (liftMeaning qMeaning) 1 .a1 ⟨1, by decide⟩ (some QUtt.none_) +
          (s1Score (liftMeaning qMeaning) 1 .a1 ⟨1, by decide⟩ (some QUtt.some_) +
            (s1Score (liftMeaning qMeaning) 1 .a1 ⟨1, by decide⟩ (some QUtt.all) + 0))) = _
  rw [s1Score_qLifted_a1_k1_silent, s1Score_qLifted_a1_k1_none,
      s1Score_qLifted_a1_k1_some, s1Score_qLifted_a1_k1_all]
  simp only [add_zero, zero_add]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  congr 1; norm_num

private theorem sum_s1Score_lbLifted_a1_k0 :
    (∑ u : WithSilence NumUtt, s1Score (liftMeaning lbMeaning) 1 .a1 ⟨0, by decide⟩ u) =
      ENNReal.ofReal (1/4 : ℝ) := by
  show s1Score (liftMeaning lbMeaning) 1 .a1 ⟨0, by decide⟩ none +
        (s1Score (liftMeaning lbMeaning) 1 .a1 ⟨0, by decide⟩ (some NumUtt.one) +
          (s1Score (liftMeaning lbMeaning) 1 .a1 ⟨0, by decide⟩ (some NumUtt.two) +
            (s1Score (liftMeaning lbMeaning) 1 .a1 ⟨0, by decide⟩ (some NumUtt.three) + 0))) = _
  rw [s1Score_lbLifted_a1_k0_silent, s1Score_lbLifted_a1_k0_one,
      s1Score_lbLifted_a1_k0_two, s1Score_lbLifted_a1_k0_three]
  simp

private theorem sum_s1Score_lbLifted_a1_k1 :
    (∑ u : WithSilence NumUtt, s1Score (liftMeaning lbMeaning) 1 .a1 ⟨1, by decide⟩ u) =
      ENNReal.ofReal (7/12 : ℝ) := by
  show s1Score (liftMeaning lbMeaning) 1 .a1 ⟨1, by decide⟩ none +
        (s1Score (liftMeaning lbMeaning) 1 .a1 ⟨1, by decide⟩ (some NumUtt.one) +
          (s1Score (liftMeaning lbMeaning) 1 .a1 ⟨1, by decide⟩ (some NumUtt.two) +
            (s1Score (liftMeaning lbMeaning) 1 .a1 ⟨1, by decide⟩ (some NumUtt.three) + 0))) = _
  rw [s1Score_lbLifted_a1_k1_silent, s1Score_lbLifted_a1_k1_one,
      s1Score_lbLifted_a1_k1_two, s1Score_lbLifted_a1_k1_three]
  simp only [add_zero, zero_add]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  congr 1; norm_num

/-! ## §19c. S1g per-(a1, k, target-utt)

Computed via `S1g = normalize (s1Score)`, with the score and the partition
function from §19a/b. -/

private theorem S1g_qLifted_a1_k0_some_eq_zero
    (h0 : ∑' u, s1Score (liftMeaning qMeaning) 1 .a1 ⟨0, by decide⟩ u ≠ 0) :
    S1g (liftMeaning qMeaning) 1 .a1 ⟨0, by decide⟩ h0 (some QUtt.some_) = 0 := by
  rw [S1g, PMF.normalize_apply, s1Score_qLifted_a1_k0_some, zero_mul]

private theorem S1g_qLifted_a1_k1_some_eq
    (h0 : ∑' u, s1Score (liftMeaning qMeaning) 1 .a1 ⟨1, by decide⟩ u ≠ 0) :
    S1g (liftMeaning qMeaning) 1 .a1 ⟨1, by decide⟩ h0 (some QUtt.some_) =
      ENNReal.ofReal (4/7 : ℝ) := by
  rw [S1g, PMF.normalize_apply, s1Score_qLifted_a1_k1_some]
  rw [show (∑' u, s1Score (liftMeaning qMeaning) 1 .a1 ⟨1, by decide⟩ u) =
        ENNReal.ofReal (7/12 : ℝ) from by
        rw [tsum_fintype]; exact sum_s1Score_qLifted_a1_k1]
  rw [← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 7/12),
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1/3)]
  congr 1; norm_num

private theorem S1g_lbLifted_a1_k0_one_eq_zero
    (h0 : ∑' u, s1Score (liftMeaning lbMeaning) 1 .a1 ⟨0, by decide⟩ u ≠ 0) :
    S1g (liftMeaning lbMeaning) 1 .a1 ⟨0, by decide⟩ h0 (some NumUtt.one) = 0 := by
  rw [S1g, PMF.normalize_apply, s1Score_lbLifted_a1_k0_one, zero_mul]

private theorem S1g_lbLifted_a1_k1_one_eq
    (h0 : ∑' u, s1Score (liftMeaning lbMeaning) 1 .a1 ⟨1, by decide⟩ u ≠ 0) :
    S1g (liftMeaning lbMeaning) 1 .a1 ⟨1, by decide⟩ h0 (some NumUtt.one) =
      ENNReal.ofReal (4/7 : ℝ) := by
  rw [S1g, PMF.normalize_apply, s1Score_lbLifted_a1_k1_one]
  rw [show (∑' u, s1Score (liftMeaning lbMeaning) 1 .a1 ⟨1, by decide⟩ u) =
        ENNReal.ofReal (7/12 : ℝ) from by
        rw [tsum_fintype]; exact sum_s1Score_lbLifted_a1_k1]
  rw [← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 7/12),
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1/3)]
  congr 1; norm_num

/-! ## §19d. marginalSpeaker collapse — `.a1`

For each `(.a1, w)`, expand `bind = ∑ k : Fin 2, obsKernel * S1g`. -/

private theorem marginalSpeaker_a1_apply
    {U : Type*} [Fintype U] (m : U → WorldState → Bool) (w : WorldState)
    (hCov : ∀ k : Fin (Access.a1.toNat + 1), ∃ u : U, qualityOk m .a1 k u) (u : U) :
    marginalSpeaker m 1 .a1 w hCov u =
      obsKernel .a1 w ⟨0, by decide⟩ *
        S1g m 1 .a1 ⟨0, by decide⟩
          (RSA.softmaxBelief_tsum_ne_zero_of_witness (hCov ⟨0, by decide⟩).choose_spec) u +
      obsKernel .a1 w ⟨1, by decide⟩ *
        S1g m 1 .a1 ⟨1, by decide⟩
          (RSA.softmaxBelief_tsum_ne_zero_of_witness (hCov ⟨1, by decide⟩).choose_spec) u := by
  show ((obsKernel .a1 w).bind _) u = _
  rw [PMF.bind_apply, tsum_fintype]
  show (∑ k : Fin 2, _) = _
  rw [Fin.sum_univ_two]
  rfl

/-! ## §19e. s1Score evaluations for `.a2` -/

-- (.a2, k=0): compatible = {s0, s1}. Only silence is qOk.

private theorem s1Score_qLifted_a2_k0_silent :
    s1Score (liftMeaning qMeaning) 1 .a2 ⟨0, by decide⟩
      (none : WithSilence QUtt) = ENNReal.ofReal (1/4 : ℝ) :=
  s1Score_uniform_apply qMeaning .a2 ⟨0, by decide⟩ none 4 (by norm_num)
    (by decide) extensionOf_qLifted_silent_card

private theorem s1Score_qLifted_a2_k0_none :
    s1Score (liftMeaning qMeaning) 1 .a2 ⟨0, by decide⟩
      (some QUtt.none_) = 0 :=
  RSA.softmaxBelief_eq_zero_of_not_qOk (by decide)

private theorem s1Score_qLifted_a2_k0_some :
    s1Score (liftMeaning qMeaning) 1 .a2 ⟨0, by decide⟩
      (some QUtt.some_) = 0 :=
  RSA.softmaxBelief_eq_zero_of_not_qOk (by decide)

private theorem s1Score_qLifted_a2_k0_all :
    s1Score (liftMeaning qMeaning) 1 .a2 ⟨0, by decide⟩
      (some QUtt.all) = 0 :=
  RSA.softmaxBelief_eq_zero_of_not_qOk (by decide)

private theorem s1Score_lbLifted_a2_k0_silent :
    s1Score (liftMeaning lbMeaning) 1 .a2 ⟨0, by decide⟩
      (none : WithSilence NumUtt) = ENNReal.ofReal (1/4 : ℝ) :=
  s1Score_uniform_apply lbMeaning .a2 ⟨0, by decide⟩ none 4 (by norm_num)
    (by decide) extensionOf_lbLifted_silent_card

private theorem s1Score_lbLifted_a2_k0_one :
    s1Score (liftMeaning lbMeaning) 1 .a2 ⟨0, by decide⟩
      (some NumUtt.one) = 0 :=
  RSA.softmaxBelief_eq_zero_of_not_qOk (by decide)

private theorem s1Score_lbLifted_a2_k0_two :
    s1Score (liftMeaning lbMeaning) 1 .a2 ⟨0, by decide⟩
      (some NumUtt.two) = 0 :=
  RSA.softmaxBelief_eq_zero_of_not_qOk (by decide)

private theorem s1Score_lbLifted_a2_k0_three :
    s1Score (liftMeaning lbMeaning) 1 .a2 ⟨0, by decide⟩
      (some NumUtt.three) = 0 :=
  RSA.softmaxBelief_eq_zero_of_not_qOk (by decide)

-- (.a2, k=1): compatible = {s1, s2}.

private theorem s1Score_qLifted_a2_k1_silent :
    s1Score (liftMeaning qMeaning) 1 .a2 ⟨1, by decide⟩
      (none : WithSilence QUtt) = ENNReal.ofReal (1/4 : ℝ) :=
  s1Score_uniform_apply qMeaning .a2 ⟨1, by decide⟩ none 4 (by norm_num)
    (by decide) extensionOf_qLifted_silent_card

private theorem s1Score_qLifted_a2_k1_none :
    s1Score (liftMeaning qMeaning) 1 .a2 ⟨1, by decide⟩
      (some QUtt.none_) = 0 :=
  RSA.softmaxBelief_eq_zero_of_not_qOk (by decide)

private theorem s1Score_qLifted_a2_k1_some :
    s1Score (liftMeaning qMeaning) 1 .a2 ⟨1, by decide⟩
      (some QUtt.some_) = ENNReal.ofReal (1/3 : ℝ) :=
  s1Score_uniform_apply qMeaning .a2 ⟨1, by decide⟩ (some QUtt.some_) 3 (by norm_num)
    (by decide) extensionOf_qLifted_some_card

private theorem s1Score_qLifted_a2_k1_all :
    s1Score (liftMeaning qMeaning) 1 .a2 ⟨1, by decide⟩
      (some QUtt.all) = 0 :=
  RSA.softmaxBelief_eq_zero_of_not_qOk (by decide)

private theorem s1Score_lbLifted_a2_k1_silent :
    s1Score (liftMeaning lbMeaning) 1 .a2 ⟨1, by decide⟩
      (none : WithSilence NumUtt) = ENNReal.ofReal (1/4 : ℝ) :=
  s1Score_uniform_apply lbMeaning .a2 ⟨1, by decide⟩ none 4 (by norm_num)
    (by decide) extensionOf_lbLifted_silent_card

private theorem s1Score_lbLifted_a2_k1_one :
    s1Score (liftMeaning lbMeaning) 1 .a2 ⟨1, by decide⟩
      (some NumUtt.one) = ENNReal.ofReal (1/3 : ℝ) :=
  s1Score_uniform_apply lbMeaning .a2 ⟨1, by decide⟩ (some NumUtt.one) 3 (by norm_num)
    (by decide) extensionOf_lbLifted_one_card

private theorem s1Score_lbLifted_a2_k1_two :
    s1Score (liftMeaning lbMeaning) 1 .a2 ⟨1, by decide⟩
      (some NumUtt.two) = 0 :=
  RSA.softmaxBelief_eq_zero_of_not_qOk (by decide)

private theorem s1Score_lbLifted_a2_k1_three :
    s1Score (liftMeaning lbMeaning) 1 .a2 ⟨1, by decide⟩
      (some NumUtt.three) = 0 :=
  RSA.softmaxBelief_eq_zero_of_not_qOk (by decide)

-- (.a2, k=2): compatible = {s2, s3}.

private theorem s1Score_qLifted_a2_k2_silent :
    s1Score (liftMeaning qMeaning) 1 .a2 ⟨2, by decide⟩
      (none : WithSilence QUtt) = ENNReal.ofReal (1/4 : ℝ) :=
  s1Score_uniform_apply qMeaning .a2 ⟨2, by decide⟩ none 4 (by norm_num)
    (by decide) extensionOf_qLifted_silent_card

private theorem s1Score_qLifted_a2_k2_none :
    s1Score (liftMeaning qMeaning) 1 .a2 ⟨2, by decide⟩
      (some QUtt.none_) = 0 :=
  RSA.softmaxBelief_eq_zero_of_not_qOk (by decide)

private theorem s1Score_qLifted_a2_k2_some :
    s1Score (liftMeaning qMeaning) 1 .a2 ⟨2, by decide⟩
      (some QUtt.some_) = ENNReal.ofReal (1/3 : ℝ) :=
  s1Score_uniform_apply qMeaning .a2 ⟨2, by decide⟩ (some QUtt.some_) 3 (by norm_num)
    (by decide) extensionOf_qLifted_some_card

private theorem s1Score_qLifted_a2_k2_all :
    s1Score (liftMeaning qMeaning) 1 .a2 ⟨2, by decide⟩
      (some QUtt.all) = 0 :=
  RSA.softmaxBelief_eq_zero_of_not_qOk (by decide)

private theorem s1Score_lbLifted_a2_k2_silent :
    s1Score (liftMeaning lbMeaning) 1 .a2 ⟨2, by decide⟩
      (none : WithSilence NumUtt) = ENNReal.ofReal (1/4 : ℝ) :=
  s1Score_uniform_apply lbMeaning .a2 ⟨2, by decide⟩ none 4 (by norm_num)
    (by decide) extensionOf_lbLifted_silent_card

private theorem s1Score_lbLifted_a2_k2_one :
    s1Score (liftMeaning lbMeaning) 1 .a2 ⟨2, by decide⟩
      (some NumUtt.one) = ENNReal.ofReal (1/3 : ℝ) :=
  s1Score_uniform_apply lbMeaning .a2 ⟨2, by decide⟩ (some NumUtt.one) 3 (by norm_num)
    (by decide) extensionOf_lbLifted_one_card

private theorem s1Score_lbLifted_a2_k2_two :
    s1Score (liftMeaning lbMeaning) 1 .a2 ⟨2, by decide⟩
      (some NumUtt.two) = ENNReal.ofReal (1/2 : ℝ) :=
  s1Score_uniform_apply lbMeaning .a2 ⟨2, by decide⟩ (some NumUtt.two) 2 (by norm_num)
    (by decide) extensionOf_lbLifted_two_card

private theorem s1Score_lbLifted_a2_k2_three :
    s1Score (liftMeaning lbMeaning) 1 .a2 ⟨2, by decide⟩
      (some NumUtt.three) = 0 :=
  RSA.softmaxBelief_eq_zero_of_not_qOk (by decide)

/-! ## §19f. Sum-of-scores at `.a2` -/

private theorem sum_s1Score_qLifted_a2_k0 :
    (∑ u : WithSilence QUtt, s1Score (liftMeaning qMeaning) 1 .a2 ⟨0, by decide⟩ u) =
      ENNReal.ofReal (1/4 : ℝ) := by
  show s1Score (liftMeaning qMeaning) 1 .a2 ⟨0, by decide⟩ none +
        (s1Score (liftMeaning qMeaning) 1 .a2 ⟨0, by decide⟩ (some QUtt.none_) +
          (s1Score (liftMeaning qMeaning) 1 .a2 ⟨0, by decide⟩ (some QUtt.some_) +
            (s1Score (liftMeaning qMeaning) 1 .a2 ⟨0, by decide⟩ (some QUtt.all) + 0))) = _
  rw [s1Score_qLifted_a2_k0_silent, s1Score_qLifted_a2_k0_none,
      s1Score_qLifted_a2_k0_some, s1Score_qLifted_a2_k0_all]
  simp

private theorem sum_s1Score_qLifted_a2_k1 :
    (∑ u : WithSilence QUtt, s1Score (liftMeaning qMeaning) 1 .a2 ⟨1, by decide⟩ u) =
      ENNReal.ofReal (7/12 : ℝ) := by
  show s1Score (liftMeaning qMeaning) 1 .a2 ⟨1, by decide⟩ none +
        (s1Score (liftMeaning qMeaning) 1 .a2 ⟨1, by decide⟩ (some QUtt.none_) +
          (s1Score (liftMeaning qMeaning) 1 .a2 ⟨1, by decide⟩ (some QUtt.some_) +
            (s1Score (liftMeaning qMeaning) 1 .a2 ⟨1, by decide⟩ (some QUtt.all) + 0))) = _
  rw [s1Score_qLifted_a2_k1_silent, s1Score_qLifted_a2_k1_none,
      s1Score_qLifted_a2_k1_some, s1Score_qLifted_a2_k1_all]
  simp only [add_zero, zero_add]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  congr 1; norm_num

private theorem sum_s1Score_qLifted_a2_k2 :
    (∑ u : WithSilence QUtt, s1Score (liftMeaning qMeaning) 1 .a2 ⟨2, by decide⟩ u) =
      ENNReal.ofReal (7/12 : ℝ) := by
  show s1Score (liftMeaning qMeaning) 1 .a2 ⟨2, by decide⟩ none +
        (s1Score (liftMeaning qMeaning) 1 .a2 ⟨2, by decide⟩ (some QUtt.none_) +
          (s1Score (liftMeaning qMeaning) 1 .a2 ⟨2, by decide⟩ (some QUtt.some_) +
            (s1Score (liftMeaning qMeaning) 1 .a2 ⟨2, by decide⟩ (some QUtt.all) + 0))) = _
  rw [s1Score_qLifted_a2_k2_silent, s1Score_qLifted_a2_k2_none,
      s1Score_qLifted_a2_k2_some, s1Score_qLifted_a2_k2_all]
  simp only [add_zero, zero_add]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  congr 1; norm_num

private theorem sum_s1Score_lbLifted_a2_k0 :
    (∑ u : WithSilence NumUtt, s1Score (liftMeaning lbMeaning) 1 .a2 ⟨0, by decide⟩ u) =
      ENNReal.ofReal (1/4 : ℝ) := by
  show s1Score (liftMeaning lbMeaning) 1 .a2 ⟨0, by decide⟩ none +
        (s1Score (liftMeaning lbMeaning) 1 .a2 ⟨0, by decide⟩ (some NumUtt.one) +
          (s1Score (liftMeaning lbMeaning) 1 .a2 ⟨0, by decide⟩ (some NumUtt.two) +
            (s1Score (liftMeaning lbMeaning) 1 .a2 ⟨0, by decide⟩ (some NumUtt.three) + 0))) = _
  rw [s1Score_lbLifted_a2_k0_silent, s1Score_lbLifted_a2_k0_one,
      s1Score_lbLifted_a2_k0_two, s1Score_lbLifted_a2_k0_three]
  simp

private theorem sum_s1Score_lbLifted_a2_k1 :
    (∑ u : WithSilence NumUtt, s1Score (liftMeaning lbMeaning) 1 .a2 ⟨1, by decide⟩ u) =
      ENNReal.ofReal (7/12 : ℝ) := by
  show s1Score (liftMeaning lbMeaning) 1 .a2 ⟨1, by decide⟩ none +
        (s1Score (liftMeaning lbMeaning) 1 .a2 ⟨1, by decide⟩ (some NumUtt.one) +
          (s1Score (liftMeaning lbMeaning) 1 .a2 ⟨1, by decide⟩ (some NumUtt.two) +
            (s1Score (liftMeaning lbMeaning) 1 .a2 ⟨1, by decide⟩ (some NumUtt.three) + 0))) = _
  rw [s1Score_lbLifted_a2_k1_silent, s1Score_lbLifted_a2_k1_one,
      s1Score_lbLifted_a2_k1_two, s1Score_lbLifted_a2_k1_three]
  simp only [add_zero, zero_add]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  congr 1; norm_num

private theorem sum_s1Score_lbLifted_a2_k2 :
    (∑ u : WithSilence NumUtt, s1Score (liftMeaning lbMeaning) 1 .a2 ⟨2, by decide⟩ u) =
      ENNReal.ofReal (13/12 : ℝ) := by
  show s1Score (liftMeaning lbMeaning) 1 .a2 ⟨2, by decide⟩ none +
        (s1Score (liftMeaning lbMeaning) 1 .a2 ⟨2, by decide⟩ (some NumUtt.one) +
          (s1Score (liftMeaning lbMeaning) 1 .a2 ⟨2, by decide⟩ (some NumUtt.two) +
            (s1Score (liftMeaning lbMeaning) 1 .a2 ⟨2, by decide⟩ (some NumUtt.three) + 0))) = _
  rw [s1Score_lbLifted_a2_k2_silent, s1Score_lbLifted_a2_k2_one,
      s1Score_lbLifted_a2_k2_two, s1Score_lbLifted_a2_k2_three]
  simp only [add_zero, zero_add]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  congr 1; norm_num

/-! ## §19g. S1g per-(a2, k, target-utt) -/

private theorem S1g_qLifted_a2_k0_some_eq_zero
    (h0 : ∑' u, s1Score (liftMeaning qMeaning) 1 .a2 ⟨0, by decide⟩ u ≠ 0) :
    S1g (liftMeaning qMeaning) 1 .a2 ⟨0, by decide⟩ h0 (some QUtt.some_) = 0 := by
  rw [S1g, PMF.normalize_apply, s1Score_qLifted_a2_k0_some, zero_mul]

private theorem S1g_qLifted_a2_k1_some_eq
    (h0 : ∑' u, s1Score (liftMeaning qMeaning) 1 .a2 ⟨1, by decide⟩ u ≠ 0) :
    S1g (liftMeaning qMeaning) 1 .a2 ⟨1, by decide⟩ h0 (some QUtt.some_) =
      ENNReal.ofReal (4/7 : ℝ) := by
  rw [S1g, PMF.normalize_apply, s1Score_qLifted_a2_k1_some]
  rw [show (∑' u, s1Score (liftMeaning qMeaning) 1 .a2 ⟨1, by decide⟩ u) =
        ENNReal.ofReal (7/12 : ℝ) from by
        rw [tsum_fintype]; exact sum_s1Score_qLifted_a2_k1]
  rw [← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 7/12),
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1/3)]
  congr 1; norm_num

private theorem S1g_qLifted_a2_k2_some_eq
    (h0 : ∑' u, s1Score (liftMeaning qMeaning) 1 .a2 ⟨2, by decide⟩ u ≠ 0) :
    S1g (liftMeaning qMeaning) 1 .a2 ⟨2, by decide⟩ h0 (some QUtt.some_) =
      ENNReal.ofReal (4/7 : ℝ) := by
  rw [S1g, PMF.normalize_apply, s1Score_qLifted_a2_k2_some]
  rw [show (∑' u, s1Score (liftMeaning qMeaning) 1 .a2 ⟨2, by decide⟩ u) =
        ENNReal.ofReal (7/12 : ℝ) from by
        rw [tsum_fintype]; exact sum_s1Score_qLifted_a2_k2]
  rw [← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 7/12),
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1/3)]
  congr 1; norm_num

private theorem S1g_lbLifted_a2_k0_one_eq_zero
    (h0 : ∑' u, s1Score (liftMeaning lbMeaning) 1 .a2 ⟨0, by decide⟩ u ≠ 0) :
    S1g (liftMeaning lbMeaning) 1 .a2 ⟨0, by decide⟩ h0 (some NumUtt.one) = 0 := by
  rw [S1g, PMF.normalize_apply, s1Score_lbLifted_a2_k0_one, zero_mul]

private theorem S1g_lbLifted_a2_k0_two_eq_zero
    (h0 : ∑' u, s1Score (liftMeaning lbMeaning) 1 .a2 ⟨0, by decide⟩ u ≠ 0) :
    S1g (liftMeaning lbMeaning) 1 .a2 ⟨0, by decide⟩ h0 (some NumUtt.two) = 0 := by
  rw [S1g, PMF.normalize_apply, s1Score_lbLifted_a2_k0_two, zero_mul]

private theorem S1g_lbLifted_a2_k1_one_eq
    (h0 : ∑' u, s1Score (liftMeaning lbMeaning) 1 .a2 ⟨1, by decide⟩ u ≠ 0) :
    S1g (liftMeaning lbMeaning) 1 .a2 ⟨1, by decide⟩ h0 (some NumUtt.one) =
      ENNReal.ofReal (4/7 : ℝ) := by
  rw [S1g, PMF.normalize_apply, s1Score_lbLifted_a2_k1_one]
  rw [show (∑' u, s1Score (liftMeaning lbMeaning) 1 .a2 ⟨1, by decide⟩ u) =
        ENNReal.ofReal (7/12 : ℝ) from by
        rw [tsum_fintype]; exact sum_s1Score_lbLifted_a2_k1]
  rw [← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 7/12),
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1/3)]
  congr 1; norm_num

private theorem S1g_lbLifted_a2_k1_two_eq_zero
    (h0 : ∑' u, s1Score (liftMeaning lbMeaning) 1 .a2 ⟨1, by decide⟩ u ≠ 0) :
    S1g (liftMeaning lbMeaning) 1 .a2 ⟨1, by decide⟩ h0 (some NumUtt.two) = 0 := by
  rw [S1g, PMF.normalize_apply, s1Score_lbLifted_a2_k1_two, zero_mul]

private theorem S1g_lbLifted_a2_k2_one_eq
    (h0 : ∑' u, s1Score (liftMeaning lbMeaning) 1 .a2 ⟨2, by decide⟩ u ≠ 0) :
    S1g (liftMeaning lbMeaning) 1 .a2 ⟨2, by decide⟩ h0 (some NumUtt.one) =
      ENNReal.ofReal (4/13 : ℝ) := by
  rw [S1g, PMF.normalize_apply, s1Score_lbLifted_a2_k2_one]
  rw [show (∑' u, s1Score (liftMeaning lbMeaning) 1 .a2 ⟨2, by decide⟩ u) =
        ENNReal.ofReal (13/12 : ℝ) from by
        rw [tsum_fintype]; exact sum_s1Score_lbLifted_a2_k2]
  rw [← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 13/12),
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1/3)]
  congr 1; norm_num

private theorem S1g_lbLifted_a2_k2_two_eq
    (h0 : ∑' u, s1Score (liftMeaning lbMeaning) 1 .a2 ⟨2, by decide⟩ u ≠ 0) :
    S1g (liftMeaning lbMeaning) 1 .a2 ⟨2, by decide⟩ h0 (some NumUtt.two) =
      ENNReal.ofReal (6/13 : ℝ) := by
  rw [S1g, PMF.normalize_apply, s1Score_lbLifted_a2_k2_two]
  rw [show (∑' u, s1Score (liftMeaning lbMeaning) 1 .a2 ⟨2, by decide⟩ u) =
        ENNReal.ofReal (13/12 : ℝ) from by
        rw [tsum_fintype]; exact sum_s1Score_lbLifted_a2_k2]
  rw [← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 13/12),
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1/2)]
  congr 1; norm_num

/-! ## §19h. marginalSpeaker collapse — `.a2` (3-element bind) -/

private theorem marginalSpeaker_a2_apply
    {U : Type*} [Fintype U] (m : U → WorldState → Bool) (w : WorldState)
    (hCov : ∀ k : Fin (Access.a2.toNat + 1), ∃ u : U, qualityOk m .a2 k u) (u : U) :
    marginalSpeaker m 1 .a2 w hCov u =
      obsKernel .a2 w ⟨0, by decide⟩ *
        S1g m 1 .a2 ⟨0, by decide⟩
          (RSA.softmaxBelief_tsum_ne_zero_of_witness (hCov ⟨0, by decide⟩).choose_spec) u +
      obsKernel .a2 w ⟨1, by decide⟩ *
        S1g m 1 .a2 ⟨1, by decide⟩
          (RSA.softmaxBelief_tsum_ne_zero_of_witness (hCov ⟨1, by decide⟩).choose_spec) u +
      obsKernel .a2 w ⟨2, by decide⟩ *
        S1g m 1 .a2 ⟨2, by decide⟩
          (RSA.softmaxBelief_tsum_ne_zero_of_witness (hCov ⟨2, by decide⟩).choose_spec) u := by
  show ((obsKernel .a2 w).bind _) u = _
  rw [PMF.bind_apply, tsum_fintype]
  show (∑ k : Fin 3, _) = _
  rw [Fin.sum_univ_three]
  rfl

/-! ## §20. Findings (silence-extended)

The 11 paper findings restated against `WithSilence` + `liftMeaning` so the
cover hypothesis is automatically satisfied via `cover_silent`.

Proof template for `.a3` (full-access, deterministic kernel):
1. `unfold L1 worldPrior; rw [posterior_lt_iff_kernel_lt_of_uniform]` —
   reduce to a marginalSpeaker comparison.
2. `rw [marginalSpeaker_a3_sX_apply, marginalSpeaker_a3_sY_apply]` —
   collapse `marginalSpeaker = bind` to single `S1g` evaluations.
3. `apply PMF.normalize_lt_of_apply_eq_of_sum_lt` — reduce to numerators
   matching plus partition functions differing.
4. Discharge via per-(a, k, u) `s1Score_*` and per-(a, k) `sum_s1Score_*` lemmas. -/

namespace Findings

open RSA (WithSilence liftMeaning)

/-- Finding 1: at full access, `some` favors `s2 > s3` (scalar implicature). -/
theorem some_full_implicature_sil
    (hMarg : PMF.marginal
              (fun w => marginalSpeaker (liftMeaning qMeaning) 1 .a3 w
                          (cover_silent qMeaning .a3))
              worldPrior (some QUtt.some_) ≠ 0) :
    (L1 (liftMeaning qMeaning) 1 .a3 (cover_silent qMeaning .a3)
        (some QUtt.some_) hMarg) .s2 >
    (L1 (liftMeaning qMeaning) 1 .a3 (cover_silent qMeaning .a3)
        (some QUtt.some_) hMarg) .s3 := by
  unfold L1 worldPrior
  rw [gt_iff_lt, PMF.posterior_lt_iff_kernel_lt_of_uniform,
      marginalSpeaker_a3_apply, marginalSpeaker_a3_apply]
  show (PMF.normalize (s1Score (liftMeaning qMeaning) 1 .a3 ⟨3, by decide⟩) _ _)
        (some QUtt.some_) <
       (PMF.normalize (s1Score (liftMeaning qMeaning) 1 .a3 ⟨2, by decide⟩) _ _)
        (some QUtt.some_)
  apply PMF.normalize_lt_of_apply_eq_of_sum_lt (a := some QUtt.some_)
  all_goals try pmf_eval
  rw [tsum_fintype, tsum_fintype]
  pmf_eval_only
  ennreal_close

/-- Finding 4: at full access, `two` favors `s2 > s3` (upper-bounded reading). -/
theorem two_full_upper_bounded_sil
    (hMarg : PMF.marginal
              (fun w => marginalSpeaker (liftMeaning lbMeaning) 1 .a3 w
                          (cover_silent lbMeaning .a3))
              worldPrior (some NumUtt.two) ≠ 0) :
    (L1 (liftMeaning lbMeaning) 1 .a3 (cover_silent lbMeaning .a3)
        (some NumUtt.two) hMarg) .s2 >
    (L1 (liftMeaning lbMeaning) 1 .a3 (cover_silent lbMeaning .a3)
        (some NumUtt.two) hMarg) .s3 := by
  unfold L1 worldPrior
  rw [gt_iff_lt, PMF.posterior_lt_iff_kernel_lt_of_uniform]
  rw [marginalSpeaker_a3_apply, marginalSpeaker_a3_apply]
  show (PMF.normalize (s1Score (liftMeaning lbMeaning) 1 .a3 ⟨3, by decide⟩) _ _)
        (some NumUtt.two) <
       (PMF.normalize (s1Score (liftMeaning lbMeaning) 1 .a3 ⟨2, by decide⟩) _ _)
        (some NumUtt.two)
  apply PMF.normalize_lt_of_apply_eq_of_sum_lt (a := some NumUtt.two)
  all_goals try pmf_eval
  rw [tsum_fintype, tsum_fintype]
  pmf_eval_only
  ennreal_close

/-- Finding 6: at full access, `one` favors `s1 > s2`. -/
theorem one_full_1v2_sil
    (hMarg : PMF.marginal
              (fun w => marginalSpeaker (liftMeaning lbMeaning) 1 .a3 w
                          (cover_silent lbMeaning .a3))
              worldPrior (some NumUtt.one) ≠ 0) :
    (L1 (liftMeaning lbMeaning) 1 .a3 (cover_silent lbMeaning .a3)
        (some NumUtt.one) hMarg) .s1 >
    (L1 (liftMeaning lbMeaning) 1 .a3 (cover_silent lbMeaning .a3)
        (some NumUtt.one) hMarg) .s2 := by
  unfold L1 worldPrior
  rw [gt_iff_lt, PMF.posterior_lt_iff_kernel_lt_of_uniform]
  rw [marginalSpeaker_a3_apply, marginalSpeaker_a3_apply]
  show (PMF.normalize (s1Score (liftMeaning lbMeaning) 1 .a3 ⟨2, by decide⟩) _ _)
        (some NumUtt.one) <
       (PMF.normalize (s1Score (liftMeaning lbMeaning) 1 .a3 ⟨1, by decide⟩) _ _)
        (some NumUtt.one)
  apply PMF.normalize_lt_of_apply_eq_of_sum_lt (a := some NumUtt.one)
  all_goals try pmf_eval
  rw [tsum_fintype, tsum_fintype]
  pmf_eval_only
  ennreal_close

/-- Finding 7: at full access, `one` favors `s1 > s3`. -/
theorem one_full_1v3_sil
    (hMarg : PMF.marginal
              (fun w => marginalSpeaker (liftMeaning lbMeaning) 1 .a3 w
                          (cover_silent lbMeaning .a3))
              worldPrior (some NumUtt.one) ≠ 0) :
    (L1 (liftMeaning lbMeaning) 1 .a3 (cover_silent lbMeaning .a3)
        (some NumUtt.one) hMarg) .s1 >
    (L1 (liftMeaning lbMeaning) 1 .a3 (cover_silent lbMeaning .a3)
        (some NumUtt.one) hMarg) .s3 := by
  unfold L1 worldPrior
  rw [gt_iff_lt, PMF.posterior_lt_iff_kernel_lt_of_uniform]
  rw [marginalSpeaker_a3_apply, marginalSpeaker_a3_apply]
  show (PMF.normalize (s1Score (liftMeaning lbMeaning) 1 .a3 ⟨3, by decide⟩) _ _)
        (some NumUtt.one) <
       (PMF.normalize (s1Score (liftMeaning lbMeaning) 1 .a3 ⟨1, by decide⟩) _ _)
        (some NumUtt.one)
  apply PMF.normalize_lt_of_apply_eq_of_sum_lt (a := some NumUtt.one)
  all_goals try pmf_eval
  rw [tsum_fintype, tsum_fintype]
  pmf_eval_only
  ennreal_close

/-! ### `.a1` minimal-access findings

Each shows `marginalSpeaker (smaller-state) ≤ marginalSpeaker (larger-state)`,
so `¬ L1 (smaller) > L1 (larger)`. Proof: at (.a1, k=0) the target utterance
has S1g = 0 (qOk fails); at (.a1, k=1) it has S1g = 4/7. So the comparison
reduces to `obsKernel(smaller)(k=1) ≤ obsKernel(larger)(k=1)`. -/

/-- Finding 2: at minimal access, `some` does NOT favor `s2 > s3`. -/
theorem some_minimal_canceled_sil
    (hMarg : PMF.marginal
              (fun w => marginalSpeaker (liftMeaning qMeaning) 1 .a1 w
                          (cover_silent qMeaning .a1))
              worldPrior (some QUtt.some_) ≠ 0) :
    ¬ ((L1 (liftMeaning qMeaning) 1 .a1 (cover_silent qMeaning .a1)
        (some QUtt.some_) hMarg) .s2 >
       (L1 (liftMeaning qMeaning) 1 .a1 (cover_silent qMeaning .a1)
        (some QUtt.some_) hMarg) .s3) := by
  rw [gt_iff_lt, not_lt]
  unfold L1 worldPrior
  rw [PMF.posterior_le_iff_kernel_le_of_uniform,
      marginalSpeaker_a1_apply, marginalSpeaker_a1_apply,
      S1g_qLifted_a1_k0_some_eq_zero, S1g_qLifted_a1_k1_some_eq,
      obsKernel_a1_s2_k1, obsKernel_a1_s3_k1]
  ennreal_close

/-- Finding 8: at minimal access, "one" does NOT favor `s1 > s2`. -/
theorem one_minimal_1v2_canceled_sil
    (hMarg : PMF.marginal
              (fun w => marginalSpeaker (liftMeaning lbMeaning) 1 .a1 w
                          (cover_silent lbMeaning .a1))
              worldPrior (some NumUtt.one) ≠ 0) :
    ¬ ((L1 (liftMeaning lbMeaning) 1 .a1 (cover_silent lbMeaning .a1)
        (some NumUtt.one) hMarg) .s1 >
       (L1 (liftMeaning lbMeaning) 1 .a1 (cover_silent lbMeaning .a1)
        (some NumUtt.one) hMarg) .s2) := by
  rw [gt_iff_lt, not_lt]
  unfold L1 worldPrior
  rw [PMF.posterior_le_iff_kernel_le_of_uniform,
      marginalSpeaker_a1_apply, marginalSpeaker_a1_apply,
      S1g_lbLifted_a1_k0_one_eq_zero, S1g_lbLifted_a1_k1_one_eq,
      obsKernel_a1_s1_k1, obsKernel_a1_s2_k1]
  ennreal_close

/-- Finding 9: at minimal access, "one" does NOT favor `s1 > s3`. -/
theorem one_minimal_1v3_canceled_sil
    (hMarg : PMF.marginal
              (fun w => marginalSpeaker (liftMeaning lbMeaning) 1 .a1 w
                          (cover_silent lbMeaning .a1))
              worldPrior (some NumUtt.one) ≠ 0) :
    ¬ ((L1 (liftMeaning lbMeaning) 1 .a1 (cover_silent lbMeaning .a1)
        (some NumUtt.one) hMarg) .s1 >
       (L1 (liftMeaning lbMeaning) 1 .a1 (cover_silent lbMeaning .a1)
        (some NumUtt.one) hMarg) .s3) := by
  rw [gt_iff_lt, not_lt]
  unfold L1 worldPrior
  rw [PMF.posterior_le_iff_kernel_le_of_uniform,
      marginalSpeaker_a1_apply, marginalSpeaker_a1_apply,
      S1g_lbLifted_a1_k0_one_eq_zero, S1g_lbLifted_a1_k1_one_eq,
      obsKernel_a1_s1_k1, obsKernel_a1_s3_k1]
  ennreal_close

/-! ### `.a2` partial-access findings -/

/-- Finding 3: at partial access, `some` does NOT favor `s2 > s3` (equality). -/
theorem some_partial_canceled_sil
    (hMarg : PMF.marginal
              (fun w => marginalSpeaker (liftMeaning qMeaning) 1 .a2 w
                          (cover_silent qMeaning .a2))
              worldPrior (some QUtt.some_) ≠ 0) :
    ¬ ((L1 (liftMeaning qMeaning) 1 .a2 (cover_silent qMeaning .a2)
        (some QUtt.some_) hMarg) .s2 >
       (L1 (liftMeaning qMeaning) 1 .a2 (cover_silent qMeaning .a2)
        (some QUtt.some_) hMarg) .s3) := by
  rw [gt_iff_lt, not_lt]
  unfold L1 worldPrior
  rw [PMF.posterior_le_iff_kernel_le_of_uniform,
      marginalSpeaker_a2_apply, marginalSpeaker_a2_apply,
      S1g_qLifted_a2_k0_some_eq_zero, S1g_qLifted_a2_k1_some_eq, S1g_qLifted_a2_k2_some_eq,
      obsKernel_a2_s2_k1, obsKernel_a2_s2_k2, obsKernel_a2_s3_k2,
      obsKernel_a2_s3_k1_zero, obsKernel_a2_s2_k0_zero, obsKernel_a2_s3_k0_zero]
  ennreal_close

/-- Finding 5: at partial access, "two" does NOT favor `s2 > s3` (weakened). -/
theorem two_partial_weakened_sil
    (hMarg : PMF.marginal
              (fun w => marginalSpeaker (liftMeaning lbMeaning) 1 .a2 w
                          (cover_silent lbMeaning .a2))
              worldPrior (some NumUtt.two) ≠ 0) :
    ¬ ((L1 (liftMeaning lbMeaning) 1 .a2 (cover_silent lbMeaning .a2)
        (some NumUtt.two) hMarg) .s2 >
       (L1 (liftMeaning lbMeaning) 1 .a2 (cover_silent lbMeaning .a2)
        (some NumUtt.two) hMarg) .s3) := by
  rw [gt_iff_lt, not_lt]
  unfold L1 worldPrior
  rw [PMF.posterior_le_iff_kernel_le_of_uniform,
      marginalSpeaker_a2_apply, marginalSpeaker_a2_apply,
      S1g_lbLifted_a2_k0_two_eq_zero, S1g_lbLifted_a2_k1_two_eq_zero,
      S1g_lbLifted_a2_k2_two_eq,
      obsKernel_a2_s2_k2, obsKernel_a2_s3_k2]
  ennreal_close

/-- Finding 10 (HEADLINE): at partial access, "one" favors `s1 > s3`. -/
theorem one_partial_1v3_sil
    (hMarg : PMF.marginal
              (fun w => marginalSpeaker (liftMeaning lbMeaning) 1 .a2 w
                          (cover_silent lbMeaning .a2))
              worldPrior (some NumUtt.one) ≠ 0) :
    (L1 (liftMeaning lbMeaning) 1 .a2 (cover_silent lbMeaning .a2)
        (some NumUtt.one) hMarg) .s1 >
    (L1 (liftMeaning lbMeaning) 1 .a2 (cover_silent lbMeaning .a2)
        (some NumUtt.one) hMarg) .s3 := by
  unfold L1 worldPrior
  rw [gt_iff_lt, PMF.posterior_lt_iff_kernel_lt_of_uniform,
      marginalSpeaker_a2_apply, marginalSpeaker_a2_apply,
      S1g_lbLifted_a2_k0_one_eq_zero, S1g_lbLifted_a2_k1_one_eq, S1g_lbLifted_a2_k2_one_eq,
      obsKernel_a2_s3_k2, obsKernel_a2_s1_k1,
      obsKernel_a2_s3_k1_zero, obsKernel_a2_s1_k2_zero]
  ennreal_close

/-- Finding 11: at partial access, "one" does NOT favor `s1 > s2`. -/
theorem one_partial_1v2_canceled_sil
    (hMarg : PMF.marginal
              (fun w => marginalSpeaker (liftMeaning lbMeaning) 1 .a2 w
                          (cover_silent lbMeaning .a2))
              worldPrior (some NumUtt.one) ≠ 0) :
    ¬ ((L1 (liftMeaning lbMeaning) 1 .a2 (cover_silent lbMeaning .a2)
        (some NumUtt.one) hMarg) .s1 >
       (L1 (liftMeaning lbMeaning) 1 .a2 (cover_silent lbMeaning .a2)
        (some NumUtt.one) hMarg) .s2) := by
  rw [gt_iff_lt, not_lt]
  unfold L1 worldPrior
  rw [PMF.posterior_le_iff_kernel_le_of_uniform,
      marginalSpeaker_a2_apply, marginalSpeaker_a2_apply,
      S1g_lbLifted_a2_k0_one_eq_zero, S1g_lbLifted_a2_k1_one_eq, S1g_lbLifted_a2_k2_one_eq,
      obsKernel_a2_s1_k1, obsKernel_a2_s2_k1, obsKernel_a2_s2_k2,
      obsKernel_a2_s1_k2_zero]
  ennreal_close

end Findings

end Phenomena.ScalarImplicatures.GoodmanStuhlmuller2013.PMF
