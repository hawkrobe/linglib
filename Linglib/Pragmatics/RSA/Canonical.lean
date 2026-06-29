import Linglib.Core.Probability.Softmax
import Linglib.Core.Probability.JointPosterior
import Linglib.Pragmatics.RSA.Operators
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog

/-!
# Canonical RSA pipeline

The single `L0 → S1 → L1` pipeline for Rational Speech Act models
[frank-goodman-2012] [degen-2023], built directly on the `Core/Probability`
shell with no bundled configuration.

The pragmatic speaker `S1` is the softmax of a *utility* `score : St → U → EReal`
mapping a speaker state (a world, or a `world × latent` pair) to a per-utterance
utility; an utterance is inapplicable exactly when its utility is `⊥` (softmax
weight `0`). The standard informativity utility is `rsaUtility = α·(log L0 − cost)`,
but any utility plugs in the same way — action-utility ([hawkins-etal-2025]) and
belief-utility speakers included. The pragmatic listener `L1` is the joint
Bayesian posterior over `world × latent`, with marginals `.fst`/`.snd`.

Positivity is supplied once as a `ViableSpeaker` instance (no utterance has
infinite utility; every state has an applicable utterance), so per-paper speakers
carry no `tsum ≠ 0 / ≠ ⊤` plumbing.

A prediction is stated in the `*_prefers_iff` vocabulary, each a one-line wrapper
over a `Core/Probability` decomposition lemma (`PMF.softmax_lt_iff_score_lt`,
`PMF.posterior_fst_lt_iff`): the partition and the marginal cancel, leaving a
comparison of utilities / conditional-joint sums.

## Main definitions

* `RSA.Canonical.ViableSpeaker` — positivity mixin discharging the softmax obligations.
* `RSA.Canonical.S1` — pragmatic speaker, `PMF.softmax` of a viable utility.
* `RSA.Canonical.rsaUtility` — the standard informativity utility `α·(log L0 − cost)`.
* `RSA.Canonical.L1` — pragmatic listener, joint `PMF.posterior` over `world × latent`.

## Main statements

* `RSA.Canonical.S1_prefers_iff` — speaker preference ↔ utility comparison.
* `RSA.Canonical.L1_world_prefers_iff` / `L1_latent_prefers_iff` — listener marginal
  preference ↔ conditional-joint-sum comparison.

## Implementation notes

Non-latent models take `St = W` and use the foundation `PMF.posterior_lt_iff_score_lt`
directly (the `latent = Unit` collapse). The `IsCovering ⇒ ViableSpeaker (rsaUtility …)`
bridge for standard informativity speakers is added when first needed.
-/

set_option autoImplicit false

namespace RSA.Canonical

open scoped ENNReal

/-! ### Pragmatic speaker -/

section Speaker

variable {St U : Type*} [Fintype U]

/-- A speaker utility `score : St → U → EReal` is **viable** when no utterance has
infinite utility and every state has at least one finite-utility (applicable)
utterance — precisely the conditions under which the softmax speaker is
well-defined. Supplied as an instance, it discharges the `PMF.softmax` positivity
obligations so per-paper speakers need no explicit `tsum`-positivity plumbing. -/
class ViableSpeaker (score : St → U → EReal) : Prop where
  /-- No utterance has `+∞` utility. -/
  no_top : ∀ s u, score s u ≠ ⊤
  /-- Every state has at least one applicable (finite-utility) utterance. -/
  some_finite : ∀ s, ∃ u, score s u ≠ ⊥

/-- The **canonical pragmatic speaker** at state `s`: the softmax of a viable
utility. The single speaker the library instantiates; the standard informativity
form is `rsaUtility`, while action/belief-utility speakers supply their own `score`. -/
noncomputable def S1 (score : St → U → EReal) [ViableSpeaker score] (s : St) : PMF U :=
  PMF.softmax (score s) (ViableSpeaker.no_top s) (ViableSpeaker.some_finite s)

/-- **Cross-utterance prediction**: the speaker prefers `u₂` to `u₁` at state `s`
iff `u₂` has the higher utility. The partition function cancels. -/
@[rsa]
theorem S1_prefers_iff (score : St → U → EReal) [ViableSpeaker score] (s : St) (u₁ u₂ : U) :
    S1 score s u₁ < S1 score s u₂ ↔ score s u₁ < score s u₂ :=
  PMF.softmax_lt_iff_score_lt (score s) (ViableSpeaker.no_top s) (ViableSpeaker.some_finite s) u₁ u₂

/-- `≤` companion of `S1_prefers_iff`. -/
@[rsa]
theorem S1_prefers_le_iff (score : St → U → EReal) [ViableSpeaker score] (s : St) (u₁ u₂ : U) :
    S1 score s u₁ ≤ S1 score s u₂ ↔ score s u₁ ≤ score s u₂ :=
  PMF.softmax_le_iff_score_le (score s) (ViableSpeaker.no_top s) (ViableSpeaker.some_finite s) u₁ u₂

/-- The speaker assigns positive probability to any applicable (finite-utility)
utterance — the witness for discharging `L1` marginal positivity. -/
theorem S1_ne_zero (score : St → U → EReal) [ViableSpeaker score] {s : St} {u : U}
    (h : score s u ≠ ⊥) : S1 score s u ≠ 0 :=
  ((PMF.softmax_pos_iff_score_ne_bot (score s)
    (ViableSpeaker.no_top s) (ViableSpeaker.some_finite s) u).mpr h).ne'

end Speaker

/-! ### Standard informativity utility -/

section StandardSpeaker

variable {W U : Type*}

/-- The **standard informativity utility** `α·(log L0(u | w) − cost u)`, EReal-valued
so an inapplicable utterance (`L0 = 0 ⇒ log = ⊥`) is `⊥` (softmax weight `0`).
Plug into `S1`; the rpow speaker `RSA.S1Belief` is the cost-free case. -/
noncomputable def rsaUtility (L0 : W → U → ℝ≥0∞) (cost : U → ℝ) (α : ℝ)
    (w : W) (u : U) : EReal :=
  (α : EReal) * (ENNReal.log (L0 w u) - (cost u : EReal))

end StandardSpeaker

/-! ### Pragmatic listener -/

section Listener

variable {W Lat U : Type*} [Fintype W] [Fintype Lat]

/-- The **canonical pragmatic listener**: the joint Bayesian posterior over
`world × latent` given the observed utterance `u`. World/latent marginals are
`.fst`/`.snd`. -/
noncomputable def L1 (S : W × Lat → PMF U) (joint : PMF (W × Lat)) (u : U)
    (h : PMF.marginal S joint u ≠ 0) : PMF (W × Lat) :=
  PMF.posterior S joint u h

/-- **Cross-world prediction**: marginalising the latent, `L1` favours world `w₂`
over `w₁` iff the conditional-joint sums favour it. -/
@[rsa]
theorem L1_world_prefers_iff [DecidableEq W] (S : W × Lat → PMF U) (joint : PMF (W × Lat))
    (u : U) (h : PMF.marginal S joint u ≠ 0) (w₁ w₂ : W) :
    (L1 S joint u h).fst w₁ < (L1 S joint u h).fst w₂
      ↔ (∑ l : Lat, joint (w₁, l) * S (w₁, l) u)
          < ∑ l : Lat, joint (w₂, l) * S (w₂, l) u :=
  PMF.posterior_fst_lt_iff S joint u h w₁ w₂

/-- `≤` companion of `L1_world_prefers_iff`. -/
@[rsa]
theorem L1_world_prefers_le_iff [DecidableEq W] (S : W × Lat → PMF U)
    (joint : PMF (W × Lat)) (u : U) (h : PMF.marginal S joint u ≠ 0) (w₁ w₂ : W) :
    (L1 S joint u h).fst w₁ ≤ (L1 S joint u h).fst w₂
      ↔ (∑ l : Lat, joint (w₁, l) * S (w₁, l) u)
          ≤ ∑ l : Lat, joint (w₂, l) * S (w₂, l) u :=
  PMF.posterior_fst_le_iff S joint u h w₁ w₂

/-- **Cross-latent prediction**: marginalising the world, `L1` favours latent `l₂`
over `l₁` iff the conditional-joint sums favour it. -/
@[rsa]
theorem L1_latent_prefers_iff [DecidableEq Lat] (S : W × Lat → PMF U)
    (joint : PMF (W × Lat)) (u : U) (h : PMF.marginal S joint u ≠ 0) (l₁ l₂ : Lat) :
    (L1 S joint u h).snd l₁ < (L1 S joint u h).snd l₂
      ↔ (∑ w : W, joint (w, l₁) * S (w, l₁) u)
          < ∑ w : W, joint (w, l₂) * S (w, l₂) u :=
  PMF.posterior_snd_lt_iff S joint u h l₁ l₂

end Listener

/-! ### Power-utility informativity speakers

The cost-free informativity speaker at a natural exponent `α` —
`S1(u|s) ∝ L0(s|u)^α`, the [frank-goodman-2012] form taken by most RSA
papers. The speaker state is a `world × latent` pair `s : W × I` and the
literal listener a per-latent kernel `L0 : I → U → PMF W`. `powUtility` is
`rsaUtility` at zero cost (`powUtility_eq_rsaUtility`); through the bridge
`PMF.softmaxWeight_natMul_log_eq_pow` the softmax weights are the powers
`powWeight = L0^α`, so predictions reduce to weight dominance via the
`PMF.normalize` bound lemmas, with `ℕ`-certificates
(`ENNReal.natCast_mul_inv_pow_lt`) closing uniform-extension comparisons. -/

section PowSpeaker

variable {W I U : Type*} (α : ℕ) (L0 : I → U → PMF W)

/-- The power-utility informativity speaker score `α · log L0(w | u, i)`. -/
noncomputable def powUtility (s : W × I) (u : U) : EReal :=
  (α : EReal) * ENNReal.log (L0 s.2 u s.1)

private theorem natCast_mul_log_ne_top (n : ℕ) {x : ℝ≥0∞} (hx : x ≠ ∞) :
    (n : EReal) * ENNReal.log x ≠ ⊤ := by
  rw [show (n : EReal) = ((n : ℝ) : EReal) from by norm_cast]
  exact PMF.coe_mul_log_ne_top (Nat.cast_nonneg n) hx

private theorem natCast_mul_log_ne_bot (n : ℕ) {x : ℝ≥0∞} (hx : x ≠ 0) :
    (n : EReal) * ENNReal.log x ≠ ⊥ := by
  rw [show (n : EReal) = ((n : ℝ) : EReal) from by norm_cast]
  exact PMF.coe_mul_log_ne_bot (Nat.cast_nonneg n) hx

/-- Grounding: `powUtility` is `rsaUtility` at exponent `α` and zero cost. -/
theorem powUtility_eq_rsaUtility (s : W × I) (u : U) :
    powUtility α L0 s u
      = rsaUtility (fun s u => L0 s.2 u s.1) (fun _ => 0) α s u := by
  simp only [powUtility, rsaUtility, EReal.coe_zero, sub_zero]
  norm_cast

/-- `powUtility` is viable as soon as every state has an applicable
utterance — the discharge for the `ViableSpeaker` instance of any
informativity speaker. -/
theorem viableSpeaker_powUtility_of_witness
    (hw : ∀ s : W × I, ∃ u, L0 s.2 u s.1 ≠ 0) :
    ViableSpeaker (powUtility α L0) where
  no_top _ _ := natCast_mul_log_ne_top α (PMF.apply_ne_top _ _)
  some_finite s := (hw s).imp fun _ h => natCast_mul_log_ne_bot α h

/-- Softmax weight of the power-utility speaker: the power `L0^α`. -/
noncomputable def powWeight (s : W × I) (u : U) : ℝ≥0∞ :=
  (L0 s.2 u s.1) ^ α

theorem tsum_powWeight_ne_zero [ViableSpeaker (powUtility α L0)] (s : W × I) :
    (∑' u, powWeight α L0 s u) ≠ 0 := by
  obtain ⟨u, hu⟩ := ViableSpeaker.some_finite (score := powUtility α L0) s
  intro hz
  rcases pow_eq_zero_iff'.mp (ENNReal.tsum_eq_zero.mp hz u) with ⟨hL0, hα⟩
  refine hu ?_
  rw [powUtility, hL0, ENNReal.log_zero]
  exact EReal.mul_bot_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hα)

theorem tsum_powWeight_ne_top [Fintype U] (s : W × I) :
    (∑' u, powWeight α L0 s u) ≠ ∞ := by
  rw [tsum_fintype]
  exact ENNReal.sum_ne_top.mpr fun u _ => ENNReal.pow_ne_top (PMF.apply_ne_top _ _)

variable [Fintype U] [ViableSpeaker (powUtility α L0)]

/-- The power-utility speaker in `PMF.normalize`-of-powers form (the bridge
`PMF.softmaxWeight_natMul_log_eq_pow`). -/
theorem S1_powUtility_eq_normalize (s : W × I) :
    S1 (powUtility α L0) s
      = PMF.normalize (powWeight α L0 s) (tsum_powWeight_ne_zero α L0 s)
          (tsum_powWeight_ne_top α L0 s) := by
  apply PMF.ext
  intro u
  have hw : ∀ v, PMF.softmaxWeight (powUtility α L0 s) v = powWeight α L0 s v :=
    fun v => PMF.softmaxWeight_natMul_log_eq_pow α (fun u' => L0 s.2 u' s.1) v
  simp only [S1, PMF.softmax_apply, PMF.normalize_apply, hw, tsum_fintype,
    division_def]

/-- Dominance upper bound: the competitors in `S` outweigh `a` by a factor
of `n`, so `a`'s share is below `(n+1)⁻¹`. -/
theorem S1_powUtility_lt_inv_succ {s : W × I} {a : U} {S : Finset U} {n : ℕ}
    (ha : a ∉ S)
    (h : (n : ℝ≥0∞) * powWeight α L0 s a < ∑ b ∈ S, powWeight α L0 s b) :
    S1 (powUtility α L0) s a < ((n : ℝ≥0∞) + 1)⁻¹ := by
  rw [S1_powUtility_eq_normalize]
  exact PMF.normalize_apply_lt_inv_succ_of_mul_lt_sum _ _ _ ha h

/-- Majority lower bound: all competitors together weigh less than `n` times
`a`, so `a`'s share exceeds `(n+1)⁻¹`. -/
theorem inv_succ_lt_S1_powUtility [DecidableEq U] {s : W × I} {a : U} {n : ℕ}
    (h : ∑ b ∈ Finset.univ.erase a, powWeight α L0 s b
      < (n : ℝ≥0∞) * powWeight α L0 s a) :
    ((n : ℝ≥0∞) + 1)⁻¹ < S1 (powUtility α L0) s a := by
  rw [S1_powUtility_eq_normalize]
  exact PMF.inv_succ_lt_normalize_apply_of_sum_lt_mul _ _ _ h

/-- The only applicable utterance is produced with certainty. -/
theorem S1_powUtility_eq_one {s : W × I} (hα : α ≠ 0) (a : U)
    (h : ∀ b, b ≠ a → L0 s.2 b s.1 = 0) :
    S1 (powUtility α L0) s a = 1 := by
  have hp : PMF.normalize (powWeight α L0 s) (tsum_powWeight_ne_zero α L0 s)
      (tsum_powWeight_ne_top α L0 s) = PMF.pure a :=
    PMF.normalize_eq_pure_of_singleton_support _ _ _ a fun b hb => by
      rw [powWeight, h b hb, zero_pow hα]
  rw [S1_powUtility_eq_normalize, hp, PMF.pure_apply_self]

/-- An inapplicable utterance is never produced. -/
theorem S1_powUtility_eq_zero {s : W × I} {a : U} (hα : α ≠ 0)
    (h : L0 s.2 a s.1 = 0) : S1 (powUtility α L0) s a = 0 := by
  rw [S1_powUtility_eq_normalize, PMF.normalize_apply, powWeight, h, zero_pow hα,
    zero_mul]

end PowSpeaker

/-! ### Event comparison for the pragmatic listener -/

/-- Posterior-mass comparison over events of the joint listener reduces to
comparing prior-weighted speaker sums — `PMF.posterior_toOuterMeasure_lt_iff_finset_score_lt`
in the `L1` vocabulary. -/
@[rsa]
theorem L1_event_lt_iff {W Lat U : Type*} [Fintype (W × Lat)]
    (S : W × Lat → PMF U) (joint : PMF (W × Lat)) (u : U)
    (h : PMF.marginal S joint u ≠ 0) (A B : Finset (W × Lat)) :
    (L1 S joint u h).toOuterMeasure ↑A < (L1 S joint u h).toOuterMeasure ↑B
      ↔ (∑ p ∈ A, joint p * S p u) < ∑ p ∈ B, joint p * S p u := by
  rw [L1, PMF.posterior_toOuterMeasure_lt_iff_finset_score_lt]

/-- At a uniform joint prior the prior cancels: event comparison reduces to
comparing summed speaker probabilities. -/
@[rsa]
theorem L1_uniform_event_lt_iff {W Lat U : Type*} [Fintype W] [Fintype Lat]
    [Nonempty (W × Lat)] (S : W × Lat → PMF U) (u : U)
    (h : PMF.marginal S (PMF.uniformOfFintype (W × Lat)) u ≠ 0)
    (A B : Finset (W × Lat)) :
    (L1 S (PMF.uniformOfFintype _) u h).toOuterMeasure ↑A
        < (L1 S (PMF.uniformOfFintype _) u h).toOuterMeasure ↑B
      ↔ (∑ p ∈ A, S p u) < ∑ p ∈ B, S p u := by
  rw [L1_event_lt_iff]
  simp only [PMF.uniformOfFintype_apply]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  exact ENNReal.mul_lt_mul_iff_right
    (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _))
    (ENNReal.inv_ne_top.mpr (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))

/-! ### Boolean-meaning literal listeners with latent interpretations

The [bergen-levy-goodman-2016] lexical-uncertainty shape: a Boolean meaning
per latent interpretation, the literal listener uniform on the extension. -/

section BoolModel

variable {W I U : Type*} [Fintype W]
variable (m : I → U → W → Bool) (hne : ∀ i u, (RSA.extensionOf (m i) u).Nonempty)

/-- Per-interpretation literal listener: uniform on the extension. -/
noncomputable def L0OfBool (i : I) (u : U) : PMF W :=
  RSA.L0OfBoolMeaning (m i) u (hne i u)

theorem L0OfBool_ne_zero {i : I} {u : U} {w : W} (h : m i u w = true) :
    L0OfBool m hne i u w ≠ 0 :=
  (PMF.mem_support_iff _ _).mp ((RSA.mem_support_L0OfBoolMeaning_iff _ w).mpr h)

theorem L0OfBool_eq_zero {i : I} {u : U} {w : W} (h : m i u w ≠ true) :
    L0OfBool m hne i u w = 0 :=
  RSA.L0OfBoolMeaning_apply_of_not_mem _ h

/-- Weight of the power-utility speaker over a Boolean model: the inverse
extension size, to the `α`. -/
theorem powWeight_L0OfBool_of_mem {α : ℕ} {w : W} {i : I} {u : U} (k : ℕ)
    (h : m i u w = true) (hk : (RSA.extensionOf (m i) u).card = k) :
    powWeight α (L0OfBool m hne) (w, i) u = ((k : ℝ≥0∞)⁻¹) ^ α := by
  show (L0OfBool m hne i u w) ^ α = _
  rw [L0OfBool, RSA.L0OfBoolMeaning_apply_of_mem _ h, hk]

theorem powWeight_L0OfBool_of_not_mem {α : ℕ} (hα : α ≠ 0) {w : W} {i : I} {u : U}
    (h : m i u w ≠ true) : powWeight α (L0OfBool m hne) (w, i) u = 0 := by
  show (L0OfBool m hne i u w) ^ α = 0
  rw [L0OfBool_eq_zero m hne h, zero_pow hα]

/-- One-dominator bound over a Boolean model: if `u'` is also applicable with
an extension smaller by an `ℕ`-certificate factor, `u` is produced with
probability below `(n+1)⁻¹`. -/
theorem S1_L0OfBool_lt_inv_succ_of_dominator {α : ℕ} [Fintype U]
    [ViableSpeaker (powUtility α (L0OfBool m hne))]
    {w : W} {i : I} {u u' : U} {n k k' : ℕ} (huu' : u ≠ u')
    (hu : m i u w = true) (hu' : m i u' w = true)
    (hk : (RSA.extensionOf (m i) u).card = k)
    (hk' : (RSA.extensionOf (m i) u').card = k')
    (hα : α ≠ 0) (hcert : n * k' ^ α < k ^ α) :
    S1 (powUtility α (L0OfBool m hne)) (w, i) u < ((n : ℝ≥0∞) + 1)⁻¹ := by
  refine S1_powUtility_lt_inv_succ α _ (Finset.notMem_singleton.mpr huu') ?_
  rw [Finset.sum_singleton, powWeight_L0OfBool_of_mem m hne k hu hk,
      powWeight_L0OfBool_of_mem m hne k' hu' hk']
  refine ENNReal.natCast_mul_inv_pow_lt hα (fun h0 => ?_) hcert
  subst h0
  rw [Finset.card_eq_zero] at hk'
  exact absurd (hk' ▸ RSA.mem_extensionOf.mpr hu') (Finset.notMem_empty _)

end BoolModel

end RSA.Canonical
