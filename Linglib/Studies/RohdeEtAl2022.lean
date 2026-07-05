import Linglib.Pragmatics.RSA.Silence
import Mathlib.Data.ENNReal.Inv

/-!
# [rohde-etal-2022]: A speaker's decision to speak cues informative content

Rohde, Hoek, Keshev & Franke (2022) argue that comprehenders separate the
prior probability of a situation from the likelihood a speaker would choose
to describe it: atypical (newsworthy) situations, precisely because their
low prior probability makes them mention-worthy, yield likely utterances.
This file formalises that Bayesian conceptualisation as a silence-augmented
[bergen-levy-goodman-2016]-style speaker: a two-value world (near-mean
typical vs. newsworthy atypical), a `WithSilence`-lifted utterance space,
and derived closed forms for the speaker's decision to report vs. stay
silent. Exp 1 varies `thinks that` vs. `announced that` completion contexts;
Exps 2–4 (out-of-the-blue and large-audience conditions) further strengthen
the effect.

## Main definitions

- `Value` — the two-outcome value space (`typical` vs. `atypical`).
- `Utterance` — `WithSilence Value`; `none` is silence, `some v` reports `v`.
- `L0` — literal listener: silence returns the prior, `some v` returns
  `PMF.pure v`.
- `speaker` — rationality-`1` `S1Belief` with `κs`-weighted content and
  `κn`-weighted silence.

## Main theorems

- `speaker_apply_none`, `speaker_apply_some_self` — closed forms.
- `newsworthy_speech`, `newsworthy_silence` — atypical situations yield
  likelier self-reports; typical situations yield likelier silence.
- `announce_shifts_toward_atypical` — cross-multiplied odds form of the
  Exp 1 announce-vs-think shift.
- `speech_preferred_of_cheap` — when speech is no more expensive than
  silence and the world is not a priori certain, reporting dominates.
-/

set_option autoImplicit false

open scoped ENNReal

namespace RohdeEtAl2022

/-! ### Situations and utterances -/

/-- A situation value: `typical` (near-mean, a priori likely) vs. `atypical`
(newsworthy, a priori unlikely). -/
inductive Value where
  | typical
  | atypical
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Utterance space: `none` is silence; `some v` is a report of value `v`. -/
abbrev Utterance : Type := RSA.WithSilence Value

variable (p : PMF Value) (κs κn : ℝ≥0∞)

/-! ### Model

Literal listener `L0`: silence conveys nothing, so the listener falls back
on the prior; a report `some v` picks out `v` via `PMF.pure`. Cost factor:
silence carries weight `κn`, content utterances carry weight `κs`. -/

/-- Literal listener. Silence returns the prior. -/
noncomputable def L0 : Utterance → PMF Value
  | some v => PMF.pure v
  | none   => p

/-- Cost factor: `κn` on silence, `κs` on every content utterance. -/
noncomputable def cost : Utterance → ℝ≥0∞ := RSA.liftCostFactor κn (fun _ => κs)

/-! ### Partition function -/

private theorem sum_utterance {β : Type*} [AddCommMonoid β] (f : Utterance → β) :
    ∑ u, f u = f none + (f (some .typical) + (f (some .atypical) + 0)) := by rfl

/-- Score sum `∑' u, L0(w|u)^1 · cost u`. Collapses to `κs + p w · κn`. -/
noncomputable def Z (w : Value) : ℝ≥0∞ :=
  ∑' u, (L0 p u w : ℝ≥0∞) ^ (1 : ℝ) * cost κs κn u

/-- Partition closed form: the value-report matching `w` scores `κs`,
silence scores `p w · κn`, and the other value-report scores 0. -/
theorem Z_eq (w : Value) : Z p κs κn w = κs + p w * κn := by
  rw [Z, tsum_fintype, sum_utterance]
  simp only [L0, cost, RSA.liftCostFactor_none, RSA.liftCostFactor_some, ENNReal.rpow_one]
  cases w
  · rw [PMF.pure_apply_self,
        PMF.pure_apply_of_ne _ _ (by decide : Value.typical ≠ Value.atypical),
        one_mul, zero_mul, add_zero, add_zero, add_comm]
  · rw [PMF.pure_apply_of_ne _ _ (by decide : Value.atypical ≠ Value.typical),
        PMF.pure_apply_self, zero_mul, one_mul, zero_add, add_zero, add_comm]

/-! ### Speaker -/

/-- Speaker at world `w`, rationality `1`. -/
noncomputable def speaker (hκs : κs ≠ 0) (hκsT : κs ≠ ⊤) (hκnT : κn ≠ ⊤) (w : Value) :
    PMF Utterance :=
  RSA.S1Belief (L0 p) (cost κs κn) 1 w
    (by change Z p κs κn w ≠ 0
        rw [Z_eq]; exact fun h => hκs (add_eq_zero.mp h).1)
    (by change Z p κs κn w ≠ ⊤
        rw [Z_eq]
        exact ENNReal.add_ne_top.mpr
          ⟨hκsT, ENNReal.mul_ne_top (PMF.apply_ne_top p w) hκnT⟩)

/-! ### Closed forms

Numerator `κs` for `some w` (self-report), `p w · κn` for `none` (silence),
over the shared partition `κs + p w · κn`. -/

/-- Silence probability. -/
theorem speaker_apply_none (hκs : κs ≠ 0) (hκsT : κs ≠ ⊤) (hκnT : κn ≠ ⊤) (w : Value) :
    speaker p κs κn hκs hκsT hκnT w none = p w * κn * (κs + p w * κn)⁻¹ := by
  rw [speaker, RSA.S1Belief_apply,
      show (∑' u', (L0 p u' w : ℝ≥0∞) ^ (1 : ℝ) * cost κs κn u') = Z p κs κn w from rfl,
      Z_eq]
  simp [L0, cost, RSA.liftCostFactor_none]

/-- Self-report probability. -/
theorem speaker_apply_some_self (hκs : κs ≠ 0) (hκsT : κs ≠ ⊤) (hκnT : κn ≠ ⊤) (w : Value) :
    speaker p κs κn hκs hκsT hκnT w (some w) = κs * (κs + p w * κn)⁻¹ := by
  rw [speaker, RSA.S1Belief_apply,
      show (∑' u', (L0 p u' w : ℝ≥0∞) ^ (1 : ℝ) * cost κs κn u') = Z p κs κn w from rfl,
      Z_eq]
  simp [L0, cost, RSA.liftCostFactor_some]

/-! ### Newsworthiness

When the atypical value has lower prior mass, the softmax speaker prefers
reporting `atypical` in the atypical world and staying silent in the typical
world: "improbable situations yield likely utterances". -/

/-- Helper: `x/(κs + x)` is strictly monotone in `x` for `x` finite,
`κs` positive-finite. -/
private theorem frac_lt_frac {κs x y : ℝ≥0∞} (hκs : κs ≠ 0) (hκsT : κs ≠ ⊤)
    (hxT : x ≠ ⊤) (hyT : y ≠ ⊤) (h : x < y) :
    x * (κs + x)⁻¹ < y * (κs + y)⁻¹ := by
  have hDxT : κs + x ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hκsT, hxT⟩
  have hDyT : κs + y ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hκsT, hyT⟩
  have hDx0 : κs + x ≠ 0 := fun h0 => hκs (add_eq_zero.mp h0).1
  have hDy0 : κs + y ≠ 0 := fun h0 => hκs (add_eq_zero.mp h0).1
  have hLT : x * (κs + x)⁻¹ ≠ ⊤ :=
    ENNReal.mul_ne_top hxT (ENNReal.inv_ne_top.mpr hDx0)
  have hRT : y * (κs + y)⁻¹ ≠ ⊤ :=
    ENNReal.mul_ne_top hyT (ENNReal.inv_ne_top.mpr hDy0)
  rw [← ENNReal.toReal_lt_toReal hLT hRT,
      ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_add hκsT hxT,
      ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_add hκsT hyT,
      ← div_eq_mul_inv, ← div_eq_mul_inv]
  have hκ : 0 < κs.toReal := ENNReal.toReal_pos hκs hκsT
  have hXY : x.toReal < y.toReal := (ENNReal.toReal_lt_toReal hxT hyT).mpr h
  have hX : 0 ≤ x.toReal := ENNReal.toReal_nonneg
  have hY : 0 ≤ y.toReal := ENNReal.toReal_nonneg
  rw [div_lt_div_iff₀ (by linarith : 0 < κs.toReal + x.toReal)
      (by linarith : 0 < κs.toReal + y.toReal)]
  nlinarith

/-- Speech is likelier in the atypical situation than in the typical one. -/
theorem newsworthy_speech (hκs : κs ≠ 0) (hκsT : κs ≠ ⊤)
    (hκn : κn ≠ 0) (hκnT : κn ≠ ⊤) (h : p .atypical < p .typical) :
    speaker p κs κn hκs hκsT hκnT .typical (some .typical) <
      speaker p κs κn hκs hκsT hκnT .atypical (some .atypical) := by
  rw [speaker_apply_some_self, speaker_apply_some_self,
      ← div_eq_mul_inv, ← div_eq_mul_inv,
      ENNReal.div_lt_div_iff_right hκs hκsT]
  exact (ENNReal.add_lt_add_iff_left hκsT).mpr
    ((ENNReal.mul_lt_mul_iff_left hκn hκnT).mpr h)

/-- Silence is likelier in the typical situation than in the atypical one. -/
theorem newsworthy_silence (hκs : κs ≠ 0) (hκsT : κs ≠ ⊤)
    (hκn : κn ≠ 0) (hκnT : κn ≠ ⊤) (h : p .atypical < p .typical) :
    speaker p κs κn hκs hκsT hκnT .atypical none <
      speaker p κs κn hκs hκsT hκnT .typical none := by
  rw [speaker_apply_none, speaker_apply_none]
  exact frac_lt_frac hκs hκsT
    (ENNReal.mul_ne_top (PMF.apply_ne_top _ _) hκnT)
    (ENNReal.mul_ne_top (PMF.apply_ne_top _ _) hκnT)
    ((ENNReal.mul_lt_mul_iff_left hκn hκnT).mpr h)

/-! ### Announce-condition shift (Exp 1)

The paper's key Exp 1 contrast is `announced that ...` (speech) vs.
`thinks that ...` (bare prior). Conditioning on the speaker having spoken
shifts the posterior odds toward atypical: with `p atypical > 0`, the
cross-multiplied form below says the atypical-weighted announce likelihood
outweighs the typical-weighted one. See [bergen-levy-goodman-2016] for the
null-utterance framework this specialises. -/

/-- The `announced that ...` condition shifts posterior odds toward the
newsworthy value: cross-multiplied form. -/
theorem announce_shifts_toward_atypical (hκs : κs ≠ 0) (hκsT : κs ≠ ⊤)
    (hκn : κn ≠ 0) (hκnT : κn ≠ ⊤)
    (h : p .atypical < p .typical) (hpa : p .atypical ≠ 0) :
    p .typical * speaker p κs κn hκs hκsT hκnT .typical (some .typical) * p .atypical <
      p .atypical * speaker p κs κn hκs hκsT hκnT .atypical (some .atypical) * p .typical := by
  have hspeech := newsworthy_speech p κs κn hκs hκsT hκn hκnT h
  have hpt : p .typical ≠ 0 := ((pos_iff_ne_zero.mpr hpa).trans h).ne'
  have hprod0 : p .atypical * p .typical ≠ 0 := mul_ne_zero hpa hpt
  have hprodT : p .atypical * p .typical ≠ ⊤ :=
    ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)
  calc p .typical * speaker p κs κn hκs hκsT hκnT .typical (some .typical) * p .atypical
      = p .atypical * p .typical *
          speaker p κs κn hκs hκsT hκnT .typical (some .typical) := by
        rw [mul_comm _ (p .atypical), ← mul_assoc]
    _ < p .atypical * p .typical *
          speaker p κs κn hκs hκsT hκnT .atypical (some .atypical) :=
        (ENNReal.mul_lt_mul_iff_right hprod0 hprodT).mpr hspeech
    _ = p .atypical * speaker p κs κn hκs hκsT hκnT .atypical (some .atypical) *
          p .typical := by
        rw [mul_assoc, mul_comm (p .typical) _, ← mul_assoc]

/-! ### Regime toggle: cheap speech dominates silence

When the speech cost weight is no less than silence's (`κn ≤ κs`, i.e., a
report is no more expensive than staying silent) and the world is not a
priori certain (`p w < 1`), the speaker at `w` prefers reporting `w` to
silence. Recovers the [bergen-levy-goodman-2016] regime where silence is a
never-preferred honesty fallback. -/

/-- Speech dominates silence when it is no more expensive and the world is
not a priori certain. -/
theorem speech_preferred_of_cheap (hκs : κs ≠ 0) (hκsT : κs ≠ ⊤)
    (hκn : κn ≠ 0) (hκnT : κn ≠ ⊤) (hcost : κn ≤ κs)
    (w : Value) (hpw : p w < 1) :
    speaker p κs κn hκs hκsT hκnT w none <
      speaker p κs κn hκs hκsT hκnT w (some w) := by
  rw [speaker_apply_none, speaker_apply_some_self,
      ← div_eq_mul_inv, ← div_eq_mul_inv,
      ENNReal.div_lt_div_iff_left
        (fun h => hκs (add_eq_zero.mp h).1)
        (ENNReal.add_ne_top.mpr
          ⟨hκsT, ENNReal.mul_ne_top (PMF.apply_ne_top p w) hκnT⟩)]
  calc p w * κn < 1 * κn := (ENNReal.mul_lt_mul_iff_left hκn hκnT).mpr hpw
    _ = κn := one_mul _
    _ ≤ κs := hcost

end RohdeEtAl2022
