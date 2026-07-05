import Linglib.Core.Probability.Hypergeometric
import Linglib.Core.Probability.Posterior
import Linglib.Pragmatics.RSA.Operators
import Linglib.Pragmatics.RSA.Silence
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform

/-!
# [goodman-stuhlmuller-2013] on mathlib `PMF`
[goodman-stuhlmuller-2013]

PMF formalization of GS2013 using `PMF.hypergeometric` as the observation
kernel primitive. The model is parameterized over `a : Access` throughout;
each downstream operator (`speakerBelief`, `qualityOk`, `s1Score`, `S1g`,
`marginalSpeaker`, `L1`) takes `(a, k)` where `k : Fin (a.val + 1)` is the
observed count.

## PMF stack (one definition each, parameterized)

* `worldPrior : PMF WorldState` — uniform on 4 states
* `obsKernel a w : PMF (Fin (a.val + 1))` — `PMF.hypergeometric 3 w.toNat a.val`
* `speakerBelief a k : PMF WorldState` — `PMF.posterior (obsKernel a) worldPrior k`
* `S1g m α a k h : PMF U` — softmax-of-expected-log over the speaker's belief
* `marginalSpeaker m α a w hCov : PMF U` — `(obsKernel a w).bind (S1g a)`
* `L1 m α a u hMarg : PMF WorldState` — `PMF.posterior (marginalSpeaker a) worldPrior u`

## Silence-extended findings

All 11 paper findings are stated against the silence-extended utterance
space `RSA.WithSilence U` — the cover hypothesis `cover_silent` is universal
because silence is `qOk` at every observation. This dissolves the
`(access, word)` cells that GS2013's "sensible situations" restriction
excludes, which would otherwise block formalization without silence.
-/

namespace GoodmanStuhlmuller2013

open RSA (WithSilence liftMeaning)
open scoped ENNReal

variable {U : Type*}

/-! ### Model substrate: world states, utterance enums, meanings, access -/

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

/-- **Speaker access** = number of objects (out of 3) the speaker observes:
a `Fin 4` indexed at 0..3, so `a.val` is the access value and
`Fin (a.val + 1)` reduces in type position when `a` is concrete. The paper
restricts to {1, 2, 3}; access 0 (speaker observes nothing) is well-defined
but unused. -/
abbrev Access : Type := Fin 4

namespace Access

/-- Access value 1 (speaker observes 1 of 3 objects). -/
abbrev a1 : Access := 1
/-- Access value 2 (speaker observes 2 of 3 objects). -/
abbrev a2 : Access := 2
/-- Access value 3 — full access (speaker observes all 3 objects). -/
abbrev a3 : Access := 3

theorem val_le_three (a : Access) : a.val ≤ 3 :=
  Nat.lt_succ_iff.mp a.isLt

theorem a1_val : (a1 : Access).val = 1 := rfl
theorem a2_val : (a2 : Access).val = 2 := rfl
theorem a3_val : (a3 : Access).val = 3 := rfl

end Access

/-! ### World prior — uniform on `WorldState` -/

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

/-! ### Hypergeometric observation kernel

`obsKernel a w : PMF (Fin (a.val + 1))` is the hypergeometric distribution
over count outcomes when the speaker observes `a.val` of the 3 objects, of
which `w.toNat` have the property. -/

noncomputable def obsKernel (a : Access) (w : WorldState) : PMF (Fin (a.val + 1)) :=
  PMF.hypergeometric 3 w.toNat a.val a.val_le_three w.toNat_le_three

/-- Closed-form observation kernel value: `C(K, k) · C(N-K, n-k) / C(N, n)`. -/
theorem obsKernel_apply (a : Access) (w : WorldState) (k : Fin (a.val + 1)) :
    obsKernel a w k =
      (w.toNat.choose k.val * (3 - w.toNat).choose (a.val - k.val) : ℕ) /
      ((3).choose a.val : ℝ≥0∞) :=
  PMF.hypergeometric_apply _ _ _ _ _ _

/-- The kernel is non-zero iff the count is hypergeometric-feasible. -/
theorem obsKernel_apply_ne_zero_iff (a : Access) (w : WorldState) (k : Fin (a.val + 1)) :
    obsKernel a w k ≠ 0 ↔ k.val ≤ w.toNat ∧ a.val - k.val ≤ 3 - w.toNat :=
  PMF.hypergeometric_apply_ne_zero_iff _ _ _ _ _ _

/-- `obsKernel` value in `ENNReal.ofReal` form — the shape the value table
below reduces to by `norm_num`. -/
theorem obsKernel_eq_ofReal (a : Access) (w : WorldState) (k : Fin (a.val + 1)) :
    obsKernel a w k =
      ENNReal.ofReal
        ((w.toNat.choose k.val * (3 - w.toNat).choose (a.val - k.val) : ℝ) /
          ((3).choose a.val : ℝ)) :=
  PMF.hypergeometric_apply_eq_ofReal _ _ _ _ _ _

/-! ### Observation compatibility and witness worlds -/

/-- A world `s` is compatible with observing `k.val` successes out of `a.val`
draws iff the hypergeometric numerator at `(K=s.toNat, k=k.val)` is non-zero. -/
def obsCompatible (a : Access) (k : Fin (a.val + 1)) (s : WorldState) : Bool :=
  k.val ≤ s.toNat && a.val - k.val ≤ 3 - s.toNat

theorem obsCompatible_iff {a : Access} {k : Fin (a.val + 1)} {s : WorldState} :
    obsCompatible a k s = true ↔ k.val ≤ s.toNat ∧ a.val - k.val ≤ 3 - s.toNat := by
  simp [obsCompatible]

/-- A witness world at which `obsKernel a · k` is positive: the world whose
count matches `k.val` (clamped to ≤ 3). -/
private def witnessWorld (k : ℕ) : WorldState :=
  match k with
  | 0 => .s0
  | 1 => .s1
  | 2 => .s2
  | _ => .s3

private theorem witnessWorld_toNat : ∀ {n : ℕ}, n ≤ 3 → (witnessWorld n).toNat = n
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | n + 4, h => absurd h (by omega)

private theorem witnessWorld_obsCompatible (a : Access) (k : Fin (a.val + 1)) :
    obsCompatible a k (witnessWorld k.val) = true := by
  have hk : k.val ≤ a.val := Nat.lt_succ_iff.mp k.isLt
  have ha := a.val_le_three
  rw [obsCompatible_iff, witnessWorld_toNat (hk.trans ha)]
  omega

/-! ### Speaker belief — `PMF.posterior` of `obsKernel` -/

private theorem obsMarginal_ne_zero (a : Access) (k : Fin (a.val + 1)) :
    PMF.marginal (obsKernel a) worldPrior k ≠ 0 :=
  PMF.marginal_ne_zero _ worldPrior k (worldPrior_ne_zero (witnessWorld k.val))
    ((obsKernel_apply_ne_zero_iff a _ k).mpr
      (obsCompatible_iff.mp (witnessWorld_obsCompatible a k)))

/-- Speaker's posterior over worlds given a count observation. -/
noncomputable def speakerBelief (a : Access) (k : Fin (a.val + 1)) : PMF WorldState :=
  PMF.posterior (obsKernel a) worldPrior k (obsMarginal_ne_zero a k)

/-! ### Quality filter, literal probabilities, softmax speaker -/

/-- An utterance `u` is quality-OK at observation `(a, k)` iff `u` is true at
every world compatible with `(a, k)`. -/
def qualityOk (m : U → WorldState → Bool)
    (a : Access) (k : Fin (a.val + 1)) (u : U) : Bool :=
  [WorldState.s0, .s1, .s2, .s3].all fun s => !obsCompatible a k s || m u s

private theorem meaning_true_of_qualityOk {m : U → WorldState → Bool}
    {a : Access} {k : Fin (a.val + 1)} {u : U} (hq : qualityOk m a k u = true)
    {s : WorldState} (hs : obsCompatible a k s = true) : m u s = true := by
  have h := List.all_eq_true.mp hq s (by cases s <;> simp)
  simpa [hs] using h

/-- Uniform-on-extension literal probability. -/
noncomputable def lexReal [Fintype U]
    (m : U → WorldState → Bool) (u : U) (s : WorldState) : ℝ :=
  if m u s then ((RSA.extensionOf m u).card : ℝ)⁻¹ else 0

/-- `toReal` projection of `speakerBelief`. -/
noncomputable def beliefReal (a : Access) (k : Fin (a.val + 1)) (s : WorldState) : ℝ :=
  (speakerBelief a k s).toReal

/-- Speaker score: `softmaxBelief` over the literal probabilities, filtered
by `qualityOk`. -/
noncomputable abbrev s1Score [Fintype U]
    (m : U → WorldState → Bool) (α : ℝ)
    (a : Access) (k : Fin (a.val + 1)) (u : U) : ℝ≥0∞ :=
  RSA.softmaxBelief (lexReal m) (beliefReal a k) α
    (fun u' => qualityOk m a k u' = true) u

/-- Speaker conditional on observation. -/
noncomputable def S1g [Fintype U]
    (m : U → WorldState → Bool) (α : ℝ)
    (a : Access) (k : Fin (a.val + 1))
    (h0 : ∑' u, s1Score m α a k u ≠ 0) : PMF U :=
  PMF.normalize (s1Score m α a k ·) h0
    (RSA.softmaxBelief_tsum_ne_top _ _ _ _)

/-! ### Marginal speaker and pragmatic listener

Since `marginalSpeaker` uses `PMF.bind` (not `bindOnSupport`), `S1g` must be
defined at every `k`, not just kernel-supported ones. The cover hypothesis
`hCov` therefore quantifies over all `k : Fin (a.val + 1)`. With
`WithSilence`, this is automatic via `cover_silent`. -/

noncomputable def marginalSpeaker [Fintype U]
    (m : U → WorldState → Bool) (α : ℝ) (a : Access) (w : WorldState)
    (hCov : ∀ k : Fin (a.val + 1), ∃ u : U, qualityOk m a k u) :
    PMF U :=
  (obsKernel a w).bind fun k =>
    S1g m α a k
      (RSA.softmaxBelief_tsum_ne_zero_of_witness (hCov k).choose_spec)

/-- Pragmatic listener: Bayesian inversion of the marginal speaker. -/
noncomputable def L1 [Fintype U]
    (m : U → WorldState → Bool) (α : ℝ) (a : Access)
    (hCov : ∀ k : Fin (a.val + 1), ∃ u : U, qualityOk m a k u) (u : U)
    (hMarg : PMF.marginal (fun w => marginalSpeaker m α a w hCov) worldPrior u ≠ 0) :
    PMF WorldState :=
  PMF.posterior (fun w => marginalSpeaker m α a w hCov) worldPrior u hMarg

/-- Silence is universally `qOk`: `liftMeaning m none = true` at every world,
so the cover hypothesis is universally satisfiable. -/
theorem cover_silent (m : U → WorldState → Bool) (a : Access) :
    ∀ k : Fin (a.val + 1), ∃ u : WithSilence U, qualityOk (liftMeaning m) a k u :=
  fun _ => ⟨none, by simp [qualityOk]⟩

/-! ### Observation-kernel value table

Closed-form values for `obsKernel a w k`, derived from `obsKernel_eq_ofReal`
by evaluating the `Nat.choose` arithmetic. Only the cells the findings below
rewrite with are stated. -/

-- `.a3` (full access): the kernel concentrates on the diagonal `k = w.toNat`.

private theorem obsKernel_a3_diag (w : WorldState) :
    obsKernel .a3 w ⟨w.toNat, by cases w <;> decide⟩ = 1 := by
  cases w <;>
    · rw [obsKernel_eq_ofReal]
      norm_num [WorldState.toNat, Nat.choose, Access.a3_val]

private theorem obsKernel_a3_off (w : WorldState) (k : Fin 4) (h : k.val ≠ w.toNat) :
    obsKernel .a3 w k = 0 := by
  by_contra hne
  obtain ⟨h₁, h₂⟩ := (obsKernel_apply_ne_zero_iff .a3 w k).mp hne
  have h₃ : Access.a3.val = 3 := rfl
  have := w.toNat_le_three
  omega

-- `.a2` (partial access, n=2): `C(3, 2) = 3` in the denominator.

private theorem obsKernel_a2_s1_k1 :
    obsKernel .a2 .s1 ⟨1, by decide⟩ = ENNReal.ofReal (2/3) := by
  rw [obsKernel_eq_ofReal]
  norm_num [WorldState.toNat, Nat.choose, Access.a2_val]

private theorem obsKernel_a2_s2_k1 :
    obsKernel .a2 .s2 ⟨1, by decide⟩ = ENNReal.ofReal (2/3) := by
  rw [obsKernel_eq_ofReal]
  norm_num [WorldState.toNat, Nat.choose, Access.a2_val]

private theorem obsKernel_a2_s2_k2 :
    obsKernel .a2 .s2 ⟨2, by decide⟩ = ENNReal.ofReal (1/3) := by
  rw [obsKernel_eq_ofReal]
  norm_num [WorldState.toNat, Nat.choose, Access.a2_val]

private theorem obsKernel_a2_s3_k2 : obsKernel .a2 .s3 ⟨2, by decide⟩ = 1 := by
  rw [obsKernel_eq_ofReal]
  norm_num [WorldState.toNat, Nat.choose, Access.a2_val]

private theorem obsKernel_a2_off (w : WorldState) (k : Fin 3)
    (h : ¬ (k.val ≤ w.toNat ∧ 2 - k.val ≤ 3 - w.toNat)) :
    obsKernel .a2 w k = 0 := by
  by_contra hne
  exact h ((obsKernel_apply_ne_zero_iff .a2 w k).mp hne)

private theorem obsKernel_a2_s3_k1_zero : obsKernel .a2 .s3 ⟨1, by decide⟩ = 0 :=
  obsKernel_a2_off .s3 ⟨1, by decide⟩ (by decide)

private theorem obsKernel_a2_s1_k2_zero : obsKernel .a2 .s1 ⟨2, by decide⟩ = 0 :=
  obsKernel_a2_off .s1 ⟨2, by decide⟩ (by decide)

private theorem obsKernel_a2_s2_k0_zero : obsKernel .a2 .s2 ⟨0, by decide⟩ = 0 :=
  obsKernel_a2_off .s2 ⟨0, by decide⟩ (by decide)

private theorem obsKernel_a2_s3_k0_zero : obsKernel .a2 .s3 ⟨0, by decide⟩ = 0 :=
  obsKernel_a2_off .s3 ⟨0, by decide⟩ (by decide)

-- `.a1` (minimal access, n=1): `C(3, 1) = 3` in the denominator.

private theorem obsKernel_a1_s1_k1 :
    obsKernel .a1 .s1 ⟨1, by decide⟩ = ENNReal.ofReal (1/3) := by
  rw [obsKernel_eq_ofReal]
  norm_num [WorldState.toNat, Nat.choose, Access.a1_val]

private theorem obsKernel_a1_s2_k1 :
    obsKernel .a1 .s2 ⟨1, by decide⟩ = ENNReal.ofReal (2/3) := by
  rw [obsKernel_eq_ofReal]
  norm_num [WorldState.toNat, Nat.choose, Access.a1_val]

private theorem obsKernel_a1_s3_k1 : obsKernel .a1 .s3 ⟨1, by decide⟩ = 1 := by
  rw [obsKernel_eq_ofReal]
  norm_num [WorldState.toNat, Nat.choose, Access.a1_val]

/-! ### `marginalSpeaker` collapse

At full access the kernel concentrates on a single `k`, so the bind collapses
to one `S1g` evaluation; at partial access it expands to the 2- or 3-term
kernel-weighted sum. -/

private theorem marginalSpeaker_a3_apply
    [Fintype U] (m : U → WorldState → Bool) (w : WorldState)
    (hCov : ∀ k : Fin (Access.a3.val + 1), ∃ u : U, qualityOk m .a3 k u) (u : U) :
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

private theorem marginalSpeaker_a1_apply
    [Fintype U] (m : U → WorldState → Bool) (w : WorldState)
    (hCov : ∀ k : Fin (Access.a1.val + 1), ∃ u : U, qualityOk m .a1 k u) (u : U) :
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

private theorem marginalSpeaker_a2_apply
    [Fintype U] (m : U → WorldState → Bool) (w : WorldState)
    (hCov : ∀ k : Fin (Access.a2.val + 1), ∃ u : U, qualityOk m .a2 k u) (u : U) :
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

/-! ### Extension cardinalities for the silence-extended models -/

private theorem extensionOf_qLifted_some_card :
    (RSA.extensionOf (liftMeaning qMeaning) (some QUtt.some_)).card = 3 := by decide

private theorem extensionOf_qLifted_all_card :
    (RSA.extensionOf (liftMeaning qMeaning) (some QUtt.all)).card = 1 := by decide

private theorem extensionOf_qLifted_silent_card :
    (RSA.extensionOf (liftMeaning qMeaning) (none : WithSilence QUtt)).card = 4 := by decide

private theorem extensionOf_lbLifted_one_card :
    (RSA.extensionOf (liftMeaning lbMeaning) (some NumUtt.one)).card = 3 := by decide

private theorem extensionOf_lbLifted_two_card :
    (RSA.extensionOf (liftMeaning lbMeaning) (some NumUtt.two)).card = 2 := by decide

private theorem extensionOf_lbLifted_three_card :
    (RSA.extensionOf (liftMeaning lbMeaning) (some NumUtt.three)).card = 1 := by decide

private theorem extensionOf_lbLifted_silent_card :
    (RSA.extensionOf (liftMeaning lbMeaning) (none : WithSilence NumUtt)).card = 4 := by decide

/-! ### Generic `s1Score` evaluation

When `qOk u` passes, `liftMeaning`-lifted utterances have a uniform lex
value on the belief support (because: `qOk` ⇒ `m u s = true` at all
compatible `s` ⊇ belief support ⇒ `lex u s = 1/(card extension)`).
`softmaxBelief_uniform_on_support` then collapses
`s1Score = ENNReal.ofReal (1/c)`. -/

private theorem belief_support_compat (a : Access) (k : Fin (a.val + 1)) (s : WorldState)
    (h : beliefReal a k s ≠ 0) : obsCompatible a k s = true := by
  unfold beliefReal at h
  have hb : speakerBelief a k s ≠ 0 := by
    intro h'; exact h (h' ▸ ENNReal.toReal_zero)
  unfold speakerBelief at hb
  rw [PMF.posterior_apply] at hb
  have h_kernel : obsKernel a s k ≠ 0 := by
    intro h_zero; apply hb; rw [h_zero, mul_zero, zero_mul]
  exact obsCompatible_iff.mpr ((obsKernel_apply_ne_zero_iff a s k).mp h_kernel)

private theorem belief_sum_eq_one (a : Access) (k : Fin (a.val + 1)) :
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
    [Fintype U] [DecidableEq U]
    (m : U → WorldState → Bool) (a : Access) (k : Fin (a.val + 1))
    (u : WithSilence U) (c : ℕ) (hc : c ≠ 0)
    (h_qok : qualityOk (liftMeaning m) a k u = true)
    (h_card : (RSA.extensionOf (liftMeaning m) u).card = c) :
    s1Score (liftMeaning m) 1 a k u = ENNReal.ofReal (1/c : ℝ) := by
  show RSA.softmaxBelief (lexReal (liftMeaning m)) (beliefReal a k) 1
        (fun u' => qualityOk (liftMeaning m) a k u' = true) u = _
  refine RSA.softmaxBelief_uniform_on_support _ _ _ _ (1/c : ℝ) h_qok ?_ ?_
    (belief_sum_eq_one a k)
  · intro s hbelief
    have hmu := meaning_true_of_qualityOk h_qok (belief_support_compat a k s hbelief)
    unfold lexReal
    rw [if_pos hmu, h_card]
    field_simp
  · positivity

/-- Sum unfolder for `WithSilence QUtt`: `Fin.sum_univ_*` doesn't apply to
custom enums, so the sum lemmas below rewrite with this fold. -/
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

/-! ### `s1Score` value table

Per-(meaning, access, count, utterance) closed forms. Positive cells go
through `s1Score_uniform_apply`; `qOk` failures are zero by
`softmaxBelief_eq_zero_of_not_qOk`. -/

-- (.a1, k=0): compatible worlds = {s0, s1, s2}; the target utterances fail qOk.

private theorem s1Score_qLifted_a1_k0_some :
    s1Score (liftMeaning qMeaning) 1 .a1 ⟨0, by decide⟩
      (some QUtt.some_) = 0 :=
  RSA.softmaxBelief_eq_zero_of_not_qOk (by decide)

private theorem s1Score_lbLifted_a1_k0_one :
    s1Score (liftMeaning lbMeaning) 1 .a1 ⟨0, by decide⟩
      (some NumUtt.one) = 0 :=
  RSA.softmaxBelief_eq_zero_of_not_qOk (by decide)

-- (.a1, k=1): compatible worlds = {s1, s2, s3}; silence and `some_`/`one` are qOk.

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

-- (.a2, k=0): compatible = {s0, s1}; the target utterances fail qOk.

private theorem s1Score_qLifted_a2_k0_some :
    s1Score (liftMeaning qMeaning) 1 .a2 ⟨0, by decide⟩
      (some QUtt.some_) = 0 :=
  RSA.softmaxBelief_eq_zero_of_not_qOk (by decide)

private theorem s1Score_lbLifted_a2_k0_one :
    s1Score (liftMeaning lbMeaning) 1 .a2 ⟨0, by decide⟩
      (some NumUtt.one) = 0 :=
  RSA.softmaxBelief_eq_zero_of_not_qOk (by decide)

private theorem s1Score_lbLifted_a2_k0_two :
    s1Score (liftMeaning lbMeaning) 1 .a2 ⟨0, by decide⟩
      (some NumUtt.two) = 0 :=
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

-- (.a3, k=1): compatible = {s1}.

private theorem s1Score_lbLifted_a3_k1_silent :
    s1Score (liftMeaning lbMeaning) 1 .a3 ⟨1, by decide⟩
      (none : WithSilence NumUtt) = ENNReal.ofReal (1/4 : ℝ) :=
  s1Score_uniform_apply lbMeaning .a3 ⟨1, by decide⟩ none 4 (by norm_num)
    (by decide) extensionOf_lbLifted_silent_card

private theorem s1Score_lbLifted_a3_k1_one :
    s1Score (liftMeaning lbMeaning) 1 .a3 ⟨1, by decide⟩
      (some NumUtt.one) = ENNReal.ofReal (1/3 : ℝ) :=
  s1Score_uniform_apply lbMeaning .a3 ⟨1, by decide⟩ (some NumUtt.one) 3 (by norm_num)
    (by decide) extensionOf_lbLifted_one_card

private theorem s1Score_lbLifted_a3_k1_two :
    s1Score (liftMeaning lbMeaning) 1 .a3 ⟨1, by decide⟩
      (some NumUtt.two) = 0 :=
  RSA.softmaxBelief_eq_zero_of_not_qOk (by decide)

private theorem s1Score_lbLifted_a3_k1_three :
    s1Score (liftMeaning lbMeaning) 1 .a3 ⟨1, by decide⟩
      (some NumUtt.three) = 0 :=
  RSA.softmaxBelief_eq_zero_of_not_qOk (by decide)

-- (.a3, k=2): compatible = {s2}.

private theorem s1Score_qLifted_a3_k2_silent :
    s1Score (liftMeaning qMeaning) 1 .a3 ⟨2, by decide⟩
      (none : WithSilence QUtt) = ENNReal.ofReal (1/4 : ℝ) :=
  s1Score_uniform_apply qMeaning .a3 ⟨2, by decide⟩ none 4 (by norm_num)
    (by decide) extensionOf_qLifted_silent_card

private theorem s1Score_qLifted_a3_k2_none :
    s1Score (liftMeaning qMeaning) 1 .a3 ⟨2, by decide⟩
      (some QUtt.none_) = 0 :=
  RSA.softmaxBelief_eq_zero_of_not_qOk (by decide)

private theorem s1Score_qLifted_a3_k2_some :
    s1Score (liftMeaning qMeaning) 1 .a3 ⟨2, by decide⟩
      (some QUtt.some_) = ENNReal.ofReal (1/3 : ℝ) :=
  s1Score_uniform_apply qMeaning .a3 ⟨2, by decide⟩ (some QUtt.some_) 3 (by norm_num)
    (by decide) extensionOf_qLifted_some_card

private theorem s1Score_qLifted_a3_k2_all :
    s1Score (liftMeaning qMeaning) 1 .a3 ⟨2, by decide⟩
      (some QUtt.all) = 0 :=
  RSA.softmaxBelief_eq_zero_of_not_qOk (by decide)

private theorem s1Score_lbLifted_a3_k2_silent :
    s1Score (liftMeaning lbMeaning) 1 .a3 ⟨2, by decide⟩
      (none : WithSilence NumUtt) = ENNReal.ofReal (1/4 : ℝ) :=
  s1Score_uniform_apply lbMeaning .a3 ⟨2, by decide⟩ none 4 (by norm_num)
    (by decide) extensionOf_lbLifted_silent_card

private theorem s1Score_lbLifted_a3_k2_one :
    s1Score (liftMeaning lbMeaning) 1 .a3 ⟨2, by decide⟩
      (some NumUtt.one) = ENNReal.ofReal (1/3 : ℝ) :=
  s1Score_uniform_apply lbMeaning .a3 ⟨2, by decide⟩ (some NumUtt.one) 3 (by norm_num)
    (by decide) extensionOf_lbLifted_one_card

private theorem s1Score_lbLifted_a3_k2_two :
    s1Score (liftMeaning lbMeaning) 1 .a3 ⟨2, by decide⟩
      (some NumUtt.two) = ENNReal.ofReal (1/2 : ℝ) :=
  s1Score_uniform_apply lbMeaning .a3 ⟨2, by decide⟩ (some NumUtt.two) 2 (by norm_num)
    (by decide) extensionOf_lbLifted_two_card

private theorem s1Score_lbLifted_a3_k2_three :
    s1Score (liftMeaning lbMeaning) 1 .a3 ⟨2, by decide⟩
      (some NumUtt.three) = 0 :=
  RSA.softmaxBelief_eq_zero_of_not_qOk (by decide)

-- (.a3, k=3): compatible = {s3}.

private theorem s1Score_qLifted_a3_k3_silent :
    s1Score (liftMeaning qMeaning) 1 .a3 ⟨3, by decide⟩
      (none : WithSilence QUtt) = ENNReal.ofReal (1/4 : ℝ) :=
  s1Score_uniform_apply qMeaning .a3 ⟨3, by decide⟩ none 4 (by norm_num)
    (by decide) extensionOf_qLifted_silent_card

private theorem s1Score_qLifted_a3_k3_none :
    s1Score (liftMeaning qMeaning) 1 .a3 ⟨3, by decide⟩
      (some QUtt.none_) = 0 :=
  RSA.softmaxBelief_eq_zero_of_not_qOk (by decide)

private theorem s1Score_qLifted_a3_k3_some :
    s1Score (liftMeaning qMeaning) 1 .a3 ⟨3, by decide⟩
      (some QUtt.some_) = ENNReal.ofReal (1/3 : ℝ) :=
  s1Score_uniform_apply qMeaning .a3 ⟨3, by decide⟩ (some QUtt.some_) 3 (by norm_num)
    (by decide) extensionOf_qLifted_some_card

private theorem s1Score_qLifted_a3_k3_all :
    s1Score (liftMeaning qMeaning) 1 .a3 ⟨3, by decide⟩
      (some QUtt.all) = ENNReal.ofReal 1 := by
  rw [s1Score_uniform_apply qMeaning .a3 ⟨3, by decide⟩ (some QUtt.all) 1 (by norm_num)
    (by decide) extensionOf_qLifted_all_card]
  norm_num

private theorem s1Score_lbLifted_a3_k3_silent :
    s1Score (liftMeaning lbMeaning) 1 .a3 ⟨3, by decide⟩
      (none : WithSilence NumUtt) = ENNReal.ofReal (1/4 : ℝ) :=
  s1Score_uniform_apply lbMeaning .a3 ⟨3, by decide⟩ none 4 (by norm_num)
    (by decide) extensionOf_lbLifted_silent_card

private theorem s1Score_lbLifted_a3_k3_one :
    s1Score (liftMeaning lbMeaning) 1 .a3 ⟨3, by decide⟩
      (some NumUtt.one) = ENNReal.ofReal (1/3 : ℝ) :=
  s1Score_uniform_apply lbMeaning .a3 ⟨3, by decide⟩ (some NumUtt.one) 3 (by norm_num)
    (by decide) extensionOf_lbLifted_one_card

private theorem s1Score_lbLifted_a3_k3_two :
    s1Score (liftMeaning lbMeaning) 1 .a3 ⟨3, by decide⟩
      (some NumUtt.two) = ENNReal.ofReal (1/2 : ℝ) :=
  s1Score_uniform_apply lbMeaning .a3 ⟨3, by decide⟩ (some NumUtt.two) 2 (by norm_num)
    (by decide) extensionOf_lbLifted_two_card

private theorem s1Score_lbLifted_a3_k3_three :
    s1Score (liftMeaning lbMeaning) 1 .a3 ⟨3, by decide⟩
      (some NumUtt.three) = ENNReal.ofReal 1 := by
  rw [s1Score_uniform_apply lbMeaning .a3 ⟨3, by decide⟩ (some NumUtt.three) 1 (by norm_num)
    (by decide) extensionOf_lbLifted_three_card]
  norm_num

/-! ### Partition functions -/

private theorem sum_s1Score_qLifted_a1_k1 :
    (∑' u : WithSilence QUtt, s1Score (liftMeaning qMeaning) 1 .a1 ⟨1, by decide⟩ u) =
      ENNReal.ofReal (7/12 : ℝ) := by
  rw [tsum_fintype, WithSilence_QUtt_sum_univ, s1Score_qLifted_a1_k1_silent,
      s1Score_qLifted_a1_k1_none, s1Score_qLifted_a1_k1_some, s1Score_qLifted_a1_k1_all]
  simp only [add_zero, zero_add]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  congr 1; norm_num

private theorem sum_s1Score_lbLifted_a1_k1 :
    (∑' u : WithSilence NumUtt, s1Score (liftMeaning lbMeaning) 1 .a1 ⟨1, by decide⟩ u) =
      ENNReal.ofReal (7/12 : ℝ) := by
  rw [tsum_fintype, WithSilence_NumUtt_sum_univ, s1Score_lbLifted_a1_k1_silent,
      s1Score_lbLifted_a1_k1_one, s1Score_lbLifted_a1_k1_two, s1Score_lbLifted_a1_k1_three]
  simp only [add_zero]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  congr 1; norm_num

private theorem sum_s1Score_qLifted_a2_k1 :
    (∑' u : WithSilence QUtt, s1Score (liftMeaning qMeaning) 1 .a2 ⟨1, by decide⟩ u) =
      ENNReal.ofReal (7/12 : ℝ) := by
  rw [tsum_fintype, WithSilence_QUtt_sum_univ, s1Score_qLifted_a2_k1_silent,
      s1Score_qLifted_a2_k1_none, s1Score_qLifted_a2_k1_some, s1Score_qLifted_a2_k1_all]
  simp only [add_zero, zero_add]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  congr 1; norm_num

private theorem sum_s1Score_qLifted_a2_k2 :
    (∑' u : WithSilence QUtt, s1Score (liftMeaning qMeaning) 1 .a2 ⟨2, by decide⟩ u) =
      ENNReal.ofReal (7/12 : ℝ) := by
  rw [tsum_fintype, WithSilence_QUtt_sum_univ, s1Score_qLifted_a2_k2_silent,
      s1Score_qLifted_a2_k2_none, s1Score_qLifted_a2_k2_some, s1Score_qLifted_a2_k2_all]
  simp only [add_zero, zero_add]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  congr 1; norm_num

private theorem sum_s1Score_lbLifted_a2_k1 :
    (∑' u : WithSilence NumUtt, s1Score (liftMeaning lbMeaning) 1 .a2 ⟨1, by decide⟩ u) =
      ENNReal.ofReal (7/12 : ℝ) := by
  rw [tsum_fintype, WithSilence_NumUtt_sum_univ, s1Score_lbLifted_a2_k1_silent,
      s1Score_lbLifted_a2_k1_one, s1Score_lbLifted_a2_k1_two, s1Score_lbLifted_a2_k1_three]
  simp only [add_zero]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  congr 1; norm_num

private theorem sum_s1Score_lbLifted_a2_k2 :
    (∑' u : WithSilence NumUtt, s1Score (liftMeaning lbMeaning) 1 .a2 ⟨2, by decide⟩ u) =
      ENNReal.ofReal (13/12 : ℝ) := by
  rw [tsum_fintype, WithSilence_NumUtt_sum_univ, s1Score_lbLifted_a2_k2_silent,
      s1Score_lbLifted_a2_k2_one, s1Score_lbLifted_a2_k2_two, s1Score_lbLifted_a2_k2_three]
  simp only [add_zero]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  congr 1; norm_num

private theorem sum_s1Score_lbLifted_a3_k1 :
    (∑' u : WithSilence NumUtt, s1Score (liftMeaning lbMeaning) 1 .a3 ⟨1, by decide⟩ u) =
      ENNReal.ofReal (7/12 : ℝ) := by
  rw [tsum_fintype, WithSilence_NumUtt_sum_univ, s1Score_lbLifted_a3_k1_silent,
      s1Score_lbLifted_a3_k1_one, s1Score_lbLifted_a3_k1_two, s1Score_lbLifted_a3_k1_three]
  simp only [add_zero]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  congr 1; norm_num

private theorem sum_s1Score_qLifted_a3_k2 :
    (∑' u : WithSilence QUtt, s1Score (liftMeaning qMeaning) 1 .a3 ⟨2, by decide⟩ u) =
      ENNReal.ofReal (7/12 : ℝ) := by
  rw [tsum_fintype, WithSilence_QUtt_sum_univ, s1Score_qLifted_a3_k2_silent,
      s1Score_qLifted_a3_k2_none, s1Score_qLifted_a3_k2_some, s1Score_qLifted_a3_k2_all]
  simp only [add_zero, zero_add]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  congr 1; norm_num

private theorem sum_s1Score_qLifted_a3_k3 :
    (∑' u : WithSilence QUtt, s1Score (liftMeaning qMeaning) 1 .a3 ⟨3, by decide⟩ u) =
      ENNReal.ofReal (19/12 : ℝ) := by
  rw [tsum_fintype, WithSilence_QUtt_sum_univ, s1Score_qLifted_a3_k3_silent,
      s1Score_qLifted_a3_k3_none, s1Score_qLifted_a3_k3_some, s1Score_qLifted_a3_k3_all]
  simp only [add_zero, zero_add]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  congr 1; norm_num

private theorem sum_s1Score_lbLifted_a3_k2 :
    (∑' u : WithSilence NumUtt, s1Score (liftMeaning lbMeaning) 1 .a3 ⟨2, by decide⟩ u) =
      ENNReal.ofReal (13/12 : ℝ) := by
  rw [tsum_fintype, WithSilence_NumUtt_sum_univ, s1Score_lbLifted_a3_k2_silent,
      s1Score_lbLifted_a3_k2_one, s1Score_lbLifted_a3_k2_two, s1Score_lbLifted_a3_k2_three]
  simp only [add_zero]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  congr 1; norm_num

private theorem sum_s1Score_lbLifted_a3_k3 :
    (∑' u : WithSilence NumUtt, s1Score (liftMeaning lbMeaning) 1 .a3 ⟨3, by decide⟩ u) =
      ENNReal.ofReal (25/12 : ℝ) := by
  rw [tsum_fintype, WithSilence_NumUtt_sum_univ, s1Score_lbLifted_a3_k3_silent,
      s1Score_lbLifted_a3_k3_one, s1Score_lbLifted_a3_k3_two, s1Score_lbLifted_a3_k3_three]
  simp only [add_zero]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  congr 1; norm_num

/-! ### `S1g` value table -/

private theorem S1g_qLifted_a1_k0_some_eq_zero
    (h0 : ∑' u, s1Score (liftMeaning qMeaning) 1 .a1 ⟨0, by decide⟩ u ≠ 0) :
    S1g (liftMeaning qMeaning) 1 .a1 ⟨0, by decide⟩ h0 (some QUtt.some_) = 0 := by
  rw [S1g, PMF.normalize_apply, s1Score_qLifted_a1_k0_some, zero_mul]

private theorem S1g_qLifted_a1_k1_some_eq
    (h0 : ∑' u, s1Score (liftMeaning qMeaning) 1 .a1 ⟨1, by decide⟩ u ≠ 0) :
    S1g (liftMeaning qMeaning) 1 .a1 ⟨1, by decide⟩ h0 (some QUtt.some_) =
      ENNReal.ofReal (4/7 : ℝ) := by
  rw [S1g, PMF.normalize_apply, s1Score_qLifted_a1_k1_some, sum_s1Score_qLifted_a1_k1,
      ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 7/12),
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
  rw [S1g, PMF.normalize_apply, s1Score_lbLifted_a1_k1_one, sum_s1Score_lbLifted_a1_k1,
      ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 7/12),
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1/3)]
  congr 1; norm_num

private theorem S1g_qLifted_a2_k0_some_eq_zero
    (h0 : ∑' u, s1Score (liftMeaning qMeaning) 1 .a2 ⟨0, by decide⟩ u ≠ 0) :
    S1g (liftMeaning qMeaning) 1 .a2 ⟨0, by decide⟩ h0 (some QUtt.some_) = 0 := by
  rw [S1g, PMF.normalize_apply, s1Score_qLifted_a2_k0_some, zero_mul]

private theorem S1g_qLifted_a2_k1_some_eq
    (h0 : ∑' u, s1Score (liftMeaning qMeaning) 1 .a2 ⟨1, by decide⟩ u ≠ 0) :
    S1g (liftMeaning qMeaning) 1 .a2 ⟨1, by decide⟩ h0 (some QUtt.some_) =
      ENNReal.ofReal (4/7 : ℝ) := by
  rw [S1g, PMF.normalize_apply, s1Score_qLifted_a2_k1_some, sum_s1Score_qLifted_a2_k1,
      ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 7/12),
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1/3)]
  congr 1; norm_num

private theorem S1g_qLifted_a2_k2_some_eq
    (h0 : ∑' u, s1Score (liftMeaning qMeaning) 1 .a2 ⟨2, by decide⟩ u ≠ 0) :
    S1g (liftMeaning qMeaning) 1 .a2 ⟨2, by decide⟩ h0 (some QUtt.some_) =
      ENNReal.ofReal (4/7 : ℝ) := by
  rw [S1g, PMF.normalize_apply, s1Score_qLifted_a2_k2_some, sum_s1Score_qLifted_a2_k2,
      ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 7/12),
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
  rw [S1g, PMF.normalize_apply, s1Score_lbLifted_a2_k1_one, sum_s1Score_lbLifted_a2_k1,
      ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 7/12),
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
  rw [S1g, PMF.normalize_apply, s1Score_lbLifted_a2_k2_one, sum_s1Score_lbLifted_a2_k2,
      ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 13/12),
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1/3)]
  congr 1; norm_num

private theorem S1g_lbLifted_a2_k2_two_eq
    (h0 : ∑' u, s1Score (liftMeaning lbMeaning) 1 .a2 ⟨2, by decide⟩ u ≠ 0) :
    S1g (liftMeaning lbMeaning) 1 .a2 ⟨2, by decide⟩ h0 (some NumUtt.two) =
      ENNReal.ofReal (6/13 : ℝ) := by
  rw [S1g, PMF.normalize_apply, s1Score_lbLifted_a2_k2_two, sum_s1Score_lbLifted_a2_k2,
      ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 13/12),
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1/2)]
  congr 1; norm_num

/-! ### Findings

The 11 paper findings, stated against `WithSilence` + `liftMeaning` so the
cover hypothesis is automatically satisfied via `cover_silent`.

These cells are computational evaluations of the model at specific
(meaning, access, world-pair, utterance) tuples, in the paper's expository
regime (α = 1, uniform prior), not the fitted regime (higher α, non-uniform
prior). Where the fitted model predicts only a marginal implicature
(access 2), directions can differ from the plotted predictions.

**They are NOT corollaries of a single information-theoretic cancellation
theorem.** The structural theorem that IS provable
(`RSA.mutualInfoStateObs_bind_noise_le` in
`Linglib/Pragmatics/RSA/Cancellation.lean`) only gives obs-level
MI cancellation: `MI(state; obs_n) ≤ MI(state; obs_i)`. The per-(world-pair)
orderings these cells encode are utterance-level claims that depend on the
specific lex shape, not just on kernel informativity — see Cancellation.lean
§3 for why utterance-level MI cancellation isn't a clean DPI corollary.
Anyone wanting to prove a structural property about the model should use the
obs-level cancellation theorem there. -/

/-- Finding 1: at full access, `some` favors `s2 > s3` (scalar implicature). -/
theorem some_full_implicature
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
  · rw [s1Score_qLifted_a3_k3_some, s1Score_qLifted_a3_k2_some]
  · rw [s1Score_qLifted_a3_k2_some]
    exact (ENNReal.ofReal_pos.mpr (by norm_num)).ne'
  · rw [s1Score_qLifted_a3_k2_some]
    exact ENNReal.ofReal_ne_top
  · rw [sum_s1Score_qLifted_a3_k2, sum_s1Score_qLifted_a3_k3]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)

/-- Finding 4: at full access, `two` favors `s2 > s3` (upper-bounded reading). -/
theorem two_full_upper_bounded
    (hMarg : PMF.marginal
              (fun w => marginalSpeaker (liftMeaning lbMeaning) 1 .a3 w
                          (cover_silent lbMeaning .a3))
              worldPrior (some NumUtt.two) ≠ 0) :
    (L1 (liftMeaning lbMeaning) 1 .a3 (cover_silent lbMeaning .a3)
        (some NumUtt.two) hMarg) .s2 >
    (L1 (liftMeaning lbMeaning) 1 .a3 (cover_silent lbMeaning .a3)
        (some NumUtt.two) hMarg) .s3 := by
  unfold L1 worldPrior
  rw [gt_iff_lt, PMF.posterior_lt_iff_kernel_lt_of_uniform,
      marginalSpeaker_a3_apply, marginalSpeaker_a3_apply]
  show (PMF.normalize (s1Score (liftMeaning lbMeaning) 1 .a3 ⟨3, by decide⟩) _ _)
        (some NumUtt.two) <
       (PMF.normalize (s1Score (liftMeaning lbMeaning) 1 .a3 ⟨2, by decide⟩) _ _)
        (some NumUtt.two)
  apply PMF.normalize_lt_of_apply_eq_of_sum_lt (a := some NumUtt.two)
  · rw [s1Score_lbLifted_a3_k3_two, s1Score_lbLifted_a3_k2_two]
  · rw [s1Score_lbLifted_a3_k2_two]
    exact (ENNReal.ofReal_pos.mpr (by norm_num)).ne'
  · rw [s1Score_lbLifted_a3_k2_two]
    exact ENNReal.ofReal_ne_top
  · rw [sum_s1Score_lbLifted_a3_k2, sum_s1Score_lbLifted_a3_k3]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)

/-- Finding 6: at full access, `one` favors `s1 > s2`. -/
theorem one_full_1v2
    (hMarg : PMF.marginal
              (fun w => marginalSpeaker (liftMeaning lbMeaning) 1 .a3 w
                          (cover_silent lbMeaning .a3))
              worldPrior (some NumUtt.one) ≠ 0) :
    (L1 (liftMeaning lbMeaning) 1 .a3 (cover_silent lbMeaning .a3)
        (some NumUtt.one) hMarg) .s1 >
    (L1 (liftMeaning lbMeaning) 1 .a3 (cover_silent lbMeaning .a3)
        (some NumUtt.one) hMarg) .s2 := by
  unfold L1 worldPrior
  rw [gt_iff_lt, PMF.posterior_lt_iff_kernel_lt_of_uniform,
      marginalSpeaker_a3_apply, marginalSpeaker_a3_apply]
  show (PMF.normalize (s1Score (liftMeaning lbMeaning) 1 .a3 ⟨2, by decide⟩) _ _)
        (some NumUtt.one) <
       (PMF.normalize (s1Score (liftMeaning lbMeaning) 1 .a3 ⟨1, by decide⟩) _ _)
        (some NumUtt.one)
  apply PMF.normalize_lt_of_apply_eq_of_sum_lt (a := some NumUtt.one)
  · rw [s1Score_lbLifted_a3_k2_one, s1Score_lbLifted_a3_k1_one]
  · rw [s1Score_lbLifted_a3_k1_one]
    exact (ENNReal.ofReal_pos.mpr (by norm_num)).ne'
  · rw [s1Score_lbLifted_a3_k1_one]
    exact ENNReal.ofReal_ne_top
  · rw [sum_s1Score_lbLifted_a3_k1, sum_s1Score_lbLifted_a3_k2]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)

/-- Finding 7: at full access, `one` favors `s1 > s3`. -/
theorem one_full_1v3
    (hMarg : PMF.marginal
              (fun w => marginalSpeaker (liftMeaning lbMeaning) 1 .a3 w
                          (cover_silent lbMeaning .a3))
              worldPrior (some NumUtt.one) ≠ 0) :
    (L1 (liftMeaning lbMeaning) 1 .a3 (cover_silent lbMeaning .a3)
        (some NumUtt.one) hMarg) .s1 >
    (L1 (liftMeaning lbMeaning) 1 .a3 (cover_silent lbMeaning .a3)
        (some NumUtt.one) hMarg) .s3 := by
  unfold L1 worldPrior
  rw [gt_iff_lt, PMF.posterior_lt_iff_kernel_lt_of_uniform,
      marginalSpeaker_a3_apply, marginalSpeaker_a3_apply]
  show (PMF.normalize (s1Score (liftMeaning lbMeaning) 1 .a3 ⟨3, by decide⟩) _ _)
        (some NumUtt.one) <
       (PMF.normalize (s1Score (liftMeaning lbMeaning) 1 .a3 ⟨1, by decide⟩) _ _)
        (some NumUtt.one)
  apply PMF.normalize_lt_of_apply_eq_of_sum_lt (a := some NumUtt.one)
  · rw [s1Score_lbLifted_a3_k3_one, s1Score_lbLifted_a3_k1_one]
  · rw [s1Score_lbLifted_a3_k1_one]
    exact (ENNReal.ofReal_pos.mpr (by norm_num)).ne'
  · rw [s1Score_lbLifted_a3_k1_one]
    exact ENNReal.ofReal_ne_top
  · rw [sum_s1Score_lbLifted_a3_k1, sum_s1Score_lbLifted_a3_k3]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)

/-! #### `.a1` minimal-access findings

Each shows `marginalSpeaker (smaller-state) ≤ marginalSpeaker (larger-state)`,
so `¬ L1 (smaller) > L1 (larger)`. At (.a1, k=0) the target utterance has
`S1g = 0` (qOk fails); at (.a1, k=1) it has `S1g = 4/7`. So the comparison
reduces to `obsKernel(smaller)(k=1) ≤ obsKernel(larger)(k=1)`. -/

/-- Finding 2: at minimal access, `some` does NOT favor `s2 > s3`. -/
theorem some_minimal_canceled
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
  simp only [mul_zero, zero_add, one_mul]
  rw [← ENNReal.ofReal_mul (by norm_num)]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

/-- Finding 8: at minimal access, `one` does NOT favor `s1 > s2`. -/
theorem one_minimal_1v2_canceled
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
  simp only [mul_zero, zero_add]
  rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num)]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

/-- Finding 9: at minimal access, `one` does NOT favor `s1 > s3`. -/
theorem one_minimal_1v3_canceled
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
  simp only [mul_zero, zero_add, one_mul]
  rw [← ENNReal.ofReal_mul (by norm_num)]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

/-! #### `.a2` partial-access findings -/

/-- Finding 3: at partial access, `some` does NOT favor `s2 > s3` (equality). -/
theorem some_partial_canceled
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
  simp only [mul_zero, zero_mul, zero_add, add_zero, one_mul]
  rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

/-- Finding 5: at partial access, `two` does NOT favor `s2 > s3` (weakened). -/
theorem two_partial_weakened
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
  simp only [mul_zero, zero_add, add_zero, one_mul]
  rw [← ENNReal.ofReal_mul (by norm_num)]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

/-- Finding 10 (HEADLINE): at partial access, `one` favors `s1 > s3`. -/
theorem one_partial_1v3
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
  simp only [mul_zero, zero_mul, zero_add, add_zero, one_mul]
  rw [← ENNReal.ofReal_mul (by norm_num)]
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)

/-- Finding 11: at partial access, `one` does NOT favor `s1 > s2`. -/
theorem one_partial_1v2_canceled
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
  simp only [mul_zero, zero_mul, zero_add, add_zero]
  rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

end GoodmanStuhlmuller2013
