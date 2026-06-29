import Linglib.Pragmatics.RSA.Operators
import Linglib.Pragmatics.RSA.Channel
import Linglib.Pragmatics.GriceanMaxims
import Linglib.Studies.DaleReiter1995

/-!
# [degen-etal-2020]: When Redundancy Is Useful
[frank-goodman-2012] [dale-reiter-1995] [engelhardt-etal-2006]
[grice-1975] [kursat-degen-2021] [westerbeek-koolen-maes-2015]

Standard RSA with a Boolean semantics predicts no preference for overmodified
referring expressions — if "small" already identifies the target, adding "blue"
is literally uninformative. Yet speakers routinely overmodify, more with color
than with size. [degen-etal-2020] resolve this by relaxing the semantics to a
**continuous** meaning `φ(u, o) ∈ [0,1]` (a Product-of-Experts over noisy feature
channels): redundant modifiers then carry real information, and the color/size
*asymmetry* follows from color channels being less noisy than size channels.

The model is the mathlib-`PMF` RSA pipeline (`RSA.L0OfMeaning` / `RSA.S1Belief`,
[frank-goodman-2012]): the literal listener `L0(·|u) : PMF World` normalises `φ`,
and the speaker `S1(·|w) : PMF U` is `S1(u|w) ∝ L0(w|u)^α · cost(u)`. With α = 1
and zero cost (`fun _ => 1`), each prediction is one application of
`S1Belief_apply_lt_iff_score_lt` — the partition cancels, leaving an `L0`
comparison in `ℝ≥0∞`.

## Main results
* `csrsa_overmod_preferred` — S1 prefers overmodified "small blue" over "small".
* `csrsa_sufficient_beats_redundant` — "small" (sufficient) beats "blue" (redundant).
* `bool_no_overmod_preference` — the Boolean model shows no overmod preference.
* `nominal_overspec_preferred` / `nom_bool_no_overspec` — the Exp 3 noun analogue.
* `unified_continuous_semantics` — both phenomena: cs-RSA yes, Boolean no.
* `noise_grounds_asymmetry`, `cost_zero_is_no_brevity` — the structural bridges.

## Verified data (prose, per [degen-etal-2020])
Effect sizes are documented here, not encoded as Lean data. Exp 1 (§3): main
effect of sufficient property β = 3.54, SE = .22; scene-variation × property
interaction β = 2.26, SE = .74; BDA-fitted noise (Figure 10) MAP x_color = .88,
HDI [.85, .92]; x_size = .79, HDI [.76, .80]; near-zero costs β_c ≈ .02/.03,
confirming color > size discrimination and the No-Brevity regime. Exp 2 (§4.3):
typicality β = −4.17, informativeness β = −5.56, color-competitor β = 0.71 (all
p < .0001); [westerbeek-koolen-maes-2015] found the same typicality direction
(β = −2.36). Exp 3 (§5.2): sub-necessary β = 2.11, basic-vs-super β = .60,
typicality β = 4.82, length β = −.95, frequency β = .08 (NS); the BDA fits a
substantial length cost (β_L = 2.69), so — unlike modifiers — nominal choice is
not in the No-Brevity regime.
-/

namespace DegenEtAl2020

open RSA
open Pragmatics.GriceanMaxims
open scoped ENNReal

/-! ### Modifier scene (Exp 1) -/

/-- Three pins varying in size and colour; the target is the small blue pin. -/
inductive World | bigBlue | bigRed | smallBlue
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- The seven referring expressions (each + implicit "pin"): four single
    adjectives and three size+colour pairs. -/
inductive Utterance | big | small | blue | red | bigBlue | bigRed | smallBlue
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- The target object. -/
abbrev target : World := .smallBlue

/-- Size-match channel (real). -/ private noncomputable def sM : ℝ := RSA.Noise.sizeMatch
/-- Size-mismatch channel (real). -/ private noncomputable def sm : ℝ := RSA.Noise.sizeMismatch
/-- Colour-match channel (real). -/ private noncomputable def cM : ℝ := RSA.Noise.colorMatch
/-- Colour-mismatch channel (real). -/ private noncomputable def cm : ℝ := RSA.Noise.colorMismatch

private theorem noiseR : sM = 8/10 ∧ sm = 2/10 ∧ cM = 99/100 ∧ cm = 1/100 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [sM, sm, cM, cm, RSA.Noise.sizeMatch, RSA.Noise.sizeMismatch, RSA.Noise.colorMatch,
      RSA.Noise.colorMismatch]

private theorem sumW (f : World → ℝ≥0∞) :
    ∑' w, f w = f .bigBlue + f .bigRed + f .smallBlue := by
  rw [tsum_fintype, show (Finset.univ : Finset World) = {.bigBlue, .bigRed, .smallBlue} from rfl,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton, add_assoc]

/-- Continuous meaning `φ(u, o) ∈ ℝ≥0∞` via a Product of Experts: a single
    adjective is its noise channel, a pair the product of its two channels. -/
noncomputable def φ : Utterance → World → ℝ≥0∞
  | .big, .bigBlue => .ofReal sM | .big, .bigRed => .ofReal sM | .big, .smallBlue => .ofReal sm
  | .small, .bigBlue => .ofReal sm | .small, .bigRed => .ofReal sm | .small, .smallBlue => .ofReal sM
  | .blue, .bigBlue => .ofReal cM | .blue, .bigRed => .ofReal cm | .blue, .smallBlue => .ofReal cM
  | .red, .bigBlue => .ofReal cm | .red, .bigRed => .ofReal cM | .red, .smallBlue => .ofReal cm
  | .bigBlue, .bigBlue => .ofReal (sM*cM) | .bigBlue, .bigRed => .ofReal (sM*cm) | .bigBlue, .smallBlue => .ofReal (sm*cM)
  | .bigRed, .bigBlue => .ofReal (sM*cm) | .bigRed, .bigRed => .ofReal (sM*cM) | .bigRed, .smallBlue => .ofReal (sm*cm)
  | .smallBlue, .bigBlue => .ofReal (sm*cM) | .smallBlue, .bigRed => .ofReal (sm*cm) | .smallBlue, .smallBlue => .ofReal (sM*cM)

private theorem φ_pos (u : Utterance) (w : World) : 0 < φ u w := by
  obtain ⟨h1, h2, h3, h4⟩ := noiseR
  cases u <;> cases w <;> exact ENNReal.ofReal_pos.mpr (by rw [h1, h2, h3, h4] at *; norm_num)

private theorem φ_ne_top (u : Utterance) (w : World) : φ u w ≠ ⊤ := by
  cases u <;> cases w <;> exact ENNReal.ofReal_ne_top

private theorem sumφ_ne_zero (u : Utterance) : ∑' w, φ u w ≠ 0 := by
  rw [tsum_fintype]; intro h
  exact (φ_pos u .smallBlue).ne' (Finset.sum_eq_zero_iff.mp h .smallBlue (Finset.mem_univ _))

private theorem sumφ_ne_top (u : Utterance) : ∑' w, φ u w ≠ ⊤ := by
  rw [tsum_fintype]; exact ENNReal.sum_ne_top.mpr fun w _ => φ_ne_top u w

/-- Literal listener `L0(·|u) : PMF World`, normalising the continuous meaning. -/
noncomputable def L0 (u : Utterance) : PMF World :=
  L0OfMeaning φ u (sumφ_ne_zero u) (sumφ_ne_top u)

private theorem L0_pos (u : Utterance) (w : World) : 0 < L0 u w := by
  rw [L0, L0OfMeaning_apply]
  exact ENNReal.mul_pos (φ_pos u w).ne' (ENNReal.inv_ne_zero.mpr (sumφ_ne_top u))

/-- L0(target | "small") = 2/3 — size is sufficient but noisy (not 1). -/
theorem L0_small_target : L0 .small target = ENNReal.ofReal (2/3) := by
  rw [L0, L0OfMeaning_apply, sumW]
  simp only [φ, noiseR.1, noiseR.2.1]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num), ← ENNReal.ofReal_add (by norm_num) (by norm_num),
      ← div_eq_mul_inv, ← ENNReal.ofReal_div_of_pos (by norm_num)]
  congr 1; norm_num

/-- L0(target | "small blue") = 99/124 — the redundant colour sharpens via PoE. -/
theorem L0_smallBlue_target : L0 .smallBlue target = ENNReal.ofReal (99/124) := by
  rw [L0, L0OfMeaning_apply, sumW]
  simp only [φ, noiseR.1, noiseR.2.1, noiseR.2.2.1, noiseR.2.2.2]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num), ← ENNReal.ofReal_add (by norm_num) (by norm_num),
      ← div_eq_mul_inv, ← ENNReal.ofReal_div_of_pos (by norm_num)]
  congr 1; norm_num

/-- L0(target | "blue") = 99/199 — colour is redundant (two objects are blue). -/
theorem L0_blue_target : L0 .blue target = ENNReal.ofReal (99/199) := by
  rw [L0, L0OfMeaning_apply, sumW]
  simp only [φ, noiseR.2.2.1, noiseR.2.2.2]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num), ← ENNReal.ofReal_add (by norm_num) (by norm_num),
      ← div_eq_mul_inv, ← ENNReal.ofReal_div_of_pos (by norm_num)]
  congr 1; norm_num

private theorem s1_ne_zero (w : World) : ∑' u, (L0 u w : ℝ≥0∞) ^ (1:ℝ) * 1 ≠ 0 := by
  simp only [ENNReal.rpow_one, mul_one]
  rw [tsum_fintype]; intro h
  exact (L0_pos .small w).ne' (Finset.sum_eq_zero_iff.mp h .small (Finset.mem_univ _))

private theorem s1_ne_top (w : World) : ∑' u, (L0 u w : ℝ≥0∞) ^ (1:ℝ) * 1 ≠ ⊤ := by
  simp only [ENNReal.rpow_one, mul_one]
  rw [tsum_fintype]; exact ENNReal.sum_ne_top.mpr fun u _ => PMF.apply_ne_top _ _

/-- Pragmatic speaker `S1(·|w) ∝ L0(w|u)` (α = 1, zero cost), a `PMF Utterance`. -/
noncomputable def S1 (w : World) : PMF Utterance :=
  S1Belief L0 (fun _ => 1) 1 w (s1_ne_zero w) (s1_ne_top w)

/-- **Main result**: S1 strictly prefers the overmodified "small blue" over the
    sufficient "small" — overmodification is rational under noisy perception. -/
theorem csrsa_overmod_preferred : S1 target .small < S1 target .smallBlue := by
  simp only [S1, rsa, ENNReal.rpow_one, mul_one, L0_small_target, L0_smallBlue_target]
  rw [ENNReal.ofReal_lt_ofReal_iff (by norm_num)]; norm_num

/-- The sufficient "small" beats the redundant "blue" (the size principle). -/
theorem csrsa_sufficient_beats_redundant : S1 target .blue < S1 target .small := by
  simp only [S1, rsa, ENNReal.rpow_one, mul_one, L0_blue_target, L0_small_target]
  rw [ENNReal.ofReal_lt_ofReal_iff (by norm_num)]; norm_num

/-! ### φ grounded in the noise channels -/

/-- `φ` uses the `RSA.Noise` channel parameters by construction. -/
theorem φ_grounded_in_noise :
    φ .blue .smallBlue = RSA.Noise.colorMatch_e ∧
    φ .blue .bigRed = RSA.Noise.colorMismatch_e ∧
    φ .small .smallBlue = RSA.Noise.sizeMatch_e ∧
    φ .small .bigBlue = RSA.Noise.sizeMismatch_e :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The colour > size discrimination ordering grounds the modifier asymmetry. -/
theorem noise_grounds_asymmetry :
    φ .blue .smallBlue = RSA.Noise.colorMatch_e ∧
    φ .small .smallBlue = RSA.Noise.sizeMatch_e ∧
    RSA.Noise.colorDiscrimination > RSA.Noise.sizeDiscrimination :=
  ⟨rfl, rfl, RSA.Noise.color_gt_size⟩

/-! ### Boolean baseline -/

/-- Boolean (zero-noise) meaning: a feature matches (`true`) or not. -/
def φbool : Utterance → World → Bool
  | .big, .bigBlue => true | .big, .bigRed => true | .big, .smallBlue => false
  | .small, .bigBlue => false | .small, .bigRed => false | .small, .smallBlue => true
  | .blue, .bigBlue => true | .blue, .bigRed => false | .blue, .smallBlue => true
  | .red, .bigBlue => false | .red, .bigRed => true | .red, .smallBlue => false
  | .bigBlue, .bigBlue => true | .bigBlue, .bigRed => false | .bigBlue, .smallBlue => false
  | .bigRed, .bigBlue => false | .bigRed, .bigRed => true | .bigRed, .smallBlue => false
  | .smallBlue, .bigBlue => false | .smallBlue, .bigRed => false | .smallBlue, .smallBlue => true

private theorem extBool_nonempty (u : Utterance) : (extensionOf φbool u).Nonempty := by
  cases u <;> decide

/-- Boolean literal listener: uniform on the extension. -/
noncomputable def boolL0 (u : Utterance) : PMF World := L0OfBoolMeaning φbool u (extBool_nonempty u)

private theorem boolL0_ne_zero {u : Utterance} {w : World} (h : φbool u w = true) :
    boolL0 u w ≠ 0 :=
  (PMF.mem_support_iff _ _).mp ((mem_support_L0OfBoolMeaning_iff _ w).mpr h)

theorem boolL0_small_target : boolL0 .small target = 1 := by
  rw [boolL0, L0OfBoolMeaning_apply_of_mem (extBool_nonempty .small)
      (show φbool .small target = true from by decide),
    show (extensionOf φbool .small).card = 1 from by decide]; simp

theorem boolL0_smallBlue_target : boolL0 .smallBlue target = 1 := by
  rw [boolL0, L0OfBoolMeaning_apply_of_mem (extBool_nonempty .smallBlue)
      (show φbool .smallBlue target = true from by decide),
    show (extensionOf φbool .smallBlue).card = 1 from by decide]; simp

private theorem boolS1_ne_zero (w : World) : ∑' u, (boolL0 u w : ℝ≥0∞) ^ (1:ℝ) * 1 ≠ 0 := by
  simp only [ENNReal.rpow_one, mul_one]
  rw [tsum_fintype]; intro h
  have hz := Finset.sum_eq_zero_iff.mp h
  cases w
  · exact boolL0_ne_zero (u := .bigBlue) (by decide) (hz .bigBlue (Finset.mem_univ _))
  · exact boolL0_ne_zero (u := .bigRed) (by decide) (hz .bigRed (Finset.mem_univ _))
  · exact boolL0_ne_zero (u := .smallBlue) (by decide) (hz .smallBlue (Finset.mem_univ _))

private theorem boolS1_ne_top (w : World) : ∑' u, (boolL0 u w : ℝ≥0∞) ^ (1:ℝ) * 1 ≠ ⊤ := by
  simp only [ENNReal.rpow_one, mul_one]
  rw [tsum_fintype]; exact ENNReal.sum_ne_top.mpr fun u _ => PMF.apply_ne_top _ _

/-- Boolean pragmatic speaker. -/
noncomputable def boolS1 (w : World) : PMF Utterance :=
  S1Belief boolL0 (fun _ => 1) 1 w (boolS1_ne_zero w) (boolS1_ne_top w)

/-- The Boolean model shows **no** overmodification preference: "small" already
    identifies the target perfectly, so adding "blue" adds nothing. -/
theorem bool_no_overmod_preference :
    ¬ (boolS1 target .small < boolS1 target .smallBlue) := by
  simp only [boolS1, rsa, ENNReal.rpow_one, mul_one, boolL0_small_target, boolL0_smallBlue_target,
    lt_self_iff_false, not_false_iff]

/-! ### No-Brevity bridge -/

/-- cs-RSA operates in [dale-reiter-1995]'s No-Brevity regime (zero cost, fitted
    β_c ≈ 0), and Q1/Q2 are independent sub-maxims — so over-description is Q1
    (informativity under noise), not a Q2 violation. -/
theorem cost_zero_is_no_brevity :
    DaleReiter1995.BrevityInterpretation.noBrevity.strength = 0 ∧
    QuantityViolation.underInformative.submaxim ≠
    QuantityViolation.overInformative.submaxim :=
  ⟨rfl, violations_independent⟩

/-! ### Nominal scene (Exp 3): overspecification via typicality

The same mechanism with a *typicality* meaning for nouns: a graded `φ_typ ∈ [0,1]`
plays the role noise plays for adjectives. Values are illustrative (the paper uses
elicited typicality norms): the dalmatian is a very typical dalmatian, a typical
dog, a moderate animal. -/

/-- Target dalmatian among a cat and a bird; "dog" is basic-sufficient. -/
inductive NomWorld | dalmatian | cat | bird
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Noun utterances at three taxonomic levels. -/
inductive NomUtterance | sub | basic | super
  deriving DecidableEq, Repr, Inhabited, Fintype

private theorem sumNomW (f : NomWorld → ℝ≥0∞) :
    ∑' w, f w = f .dalmatian + f .cat + f .bird := by
  rw [tsum_fintype, show (Finset.univ : Finset NomWorld) = {.dalmatian, .cat, .bird} from rfl,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton, add_assoc]

/-- Typicality meaning `φ_typ(u, o) ∈ ℝ≥0∞`. -/
noncomputable def φtyp : NomUtterance → NomWorld → ℝ≥0∞
  | .sub, .dalmatian => .ofReal (19/20) | .sub, .cat => .ofReal (1/100) | .sub, .bird => .ofReal (1/100)
  | .basic, .dalmatian => .ofReal (4/5) | .basic, .cat => .ofReal (1/20) | .basic, .bird => .ofReal (1/20)
  | .super, .dalmatian => .ofReal (7/10) | .super, .cat => .ofReal (7/10) | .super, .bird => .ofReal (7/10)

private theorem φtyp_pos (u : NomUtterance) (w : NomWorld) : 0 < φtyp u w := by
  cases u <;> cases w <;> exact ENNReal.ofReal_pos.mpr (by norm_num)

private theorem φtyp_ne_top (u : NomUtterance) (w : NomWorld) : φtyp u w ≠ ⊤ := by
  cases u <;> cases w <;> exact ENNReal.ofReal_ne_top

private theorem sumφtyp_ne_zero (u : NomUtterance) : ∑' w, φtyp u w ≠ 0 := by
  rw [tsum_fintype]; intro h
  exact (φtyp_pos u .dalmatian).ne' (Finset.sum_eq_zero_iff.mp h .dalmatian (Finset.mem_univ _))

private theorem sumφtyp_ne_top (u : NomUtterance) : ∑' w, φtyp u w ≠ ⊤ := by
  rw [tsum_fintype]; exact ENNReal.sum_ne_top.mpr fun w _ => φtyp_ne_top u w

/-- Nominal literal listener. -/
noncomputable def nomL0 (u : NomUtterance) : PMF NomWorld :=
  L0OfMeaning φtyp u (sumφtyp_ne_zero u) (sumφtyp_ne_top u)

private theorem nomL0_pos (u : NomUtterance) (w : NomWorld) : 0 < nomL0 u w := by
  rw [nomL0, L0OfMeaning_apply]
  exact ENNReal.mul_pos (φtyp_pos u w).ne' (ENNReal.inv_ne_zero.mpr (sumφtyp_ne_top u))

/-- L0(dalmatian | "dalmatian") = 95/97 — near-perfect via typicality. -/
theorem nomL0_sub : nomL0 .sub .dalmatian = ENNReal.ofReal (95/97) := by
  rw [nomL0, L0OfMeaning_apply, sumNomW]
  simp only [φtyp]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num), ← ENNReal.ofReal_add (by norm_num) (by norm_num),
      ← div_eq_mul_inv, ← ENNReal.ofReal_div_of_pos (by norm_num)]
  congr 1; norm_num

/-- L0(dalmatian | "dog") = 8/9 — the basic term discriminates well. -/
theorem nomL0_basic : nomL0 .basic .dalmatian = ENNReal.ofReal (8/9) := by
  rw [nomL0, L0OfMeaning_apply, sumNomW]
  simp only [φtyp]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num), ← ENNReal.ofReal_add (by norm_num) (by norm_num),
      ← div_eq_mul_inv, ← ENNReal.ofReal_div_of_pos (by norm_num)]
  congr 1; norm_num

/-- L0(dalmatian | "animal") = 1/3 — no discrimination. -/
theorem nomL0_super : nomL0 .super .dalmatian = ENNReal.ofReal (1/3) := by
  rw [nomL0, L0OfMeaning_apply, sumNomW]
  simp only [φtyp]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num), ← ENNReal.ofReal_add (by norm_num) (by norm_num),
      ← div_eq_mul_inv, ← ENNReal.ofReal_div_of_pos (by norm_num)]
  congr 1; norm_num

private theorem nomS1_ne_zero (w : NomWorld) : ∑' u, (nomL0 u w : ℝ≥0∞) ^ (1:ℝ) * 1 ≠ 0 := by
  simp only [ENNReal.rpow_one, mul_one]
  rw [tsum_fintype]; intro h
  exact (nomL0_pos .basic w).ne' (Finset.sum_eq_zero_iff.mp h .basic (Finset.mem_univ _))

private theorem nomS1_ne_top (w : NomWorld) : ∑' u, (nomL0 u w : ℝ≥0∞) ^ (1:ℝ) * 1 ≠ ⊤ := by
  simp only [ENNReal.rpow_one, mul_one]
  rw [tsum_fintype]; exact ENNReal.sum_ne_top.mpr fun u _ => PMF.apply_ne_top _ _

/-- Nominal pragmatic speaker. -/
noncomputable def nomS1 (w : NomWorld) : PMF NomUtterance :=
  S1Belief nomL0 (fun _ => 1) 1 w (nomS1_ne_zero w) (nomS1_ne_top w)

/-- Nominal **overspecification**: S1 prefers the subordinate "dalmatian" over the
    sufficient basic "dog" — the noun analogue of `csrsa_overmod_preferred`. -/
theorem nominal_overspec_preferred : nomS1 .dalmatian .basic < nomS1 .dalmatian .sub := by
  simp only [nomS1, rsa, ENNReal.rpow_one, mul_one, nomL0_basic, nomL0_sub]
  rw [ENNReal.ofReal_lt_ofReal_iff (by norm_num)]; norm_num

/-- The basic "dog" beats the superordinate "animal". -/
theorem nominal_basic_beats_super : nomS1 .dalmatian .super < nomS1 .dalmatian .basic := by
  simp only [nomS1, rsa, ENNReal.rpow_one, mul_one, nomL0_super, nomL0_basic]
  rw [ENNReal.ofReal_lt_ofReal_iff (by norm_num)]; norm_num

/-- Boolean (crisp) typicality. -/
def φtypBool : NomUtterance → NomWorld → Bool
  | .sub, .dalmatian => true | .sub, .cat => false | .sub, .bird => false
  | .basic, .dalmatian => true | .basic, .cat => false | .basic, .bird => false
  | .super, .dalmatian => true | .super, .cat => true | .super, .bird => true

private theorem extNomBool_nonempty (u : NomUtterance) : (extensionOf φtypBool u).Nonempty := by
  cases u <;> decide

/-- Boolean nominal literal listener. -/
noncomputable def nomBoolL0 (u : NomUtterance) : PMF NomWorld :=
  L0OfBoolMeaning φtypBool u (extNomBool_nonempty u)

private theorem nomBoolL0_ne_zero {u : NomUtterance} {w : NomWorld} (h : φtypBool u w = true) :
    nomBoolL0 u w ≠ 0 :=
  (PMF.mem_support_iff _ _).mp ((mem_support_L0OfBoolMeaning_iff _ w).mpr h)

theorem nomBoolL0_sub : nomBoolL0 .sub .dalmatian = 1 := by
  rw [nomBoolL0, L0OfBoolMeaning_apply_of_mem (extNomBool_nonempty .sub)
      (show φtypBool .sub .dalmatian = true from by decide),
    show (extensionOf φtypBool .sub).card = 1 from by decide]; simp

theorem nomBoolL0_basic : nomBoolL0 .basic .dalmatian = 1 := by
  rw [nomBoolL0, L0OfBoolMeaning_apply_of_mem (extNomBool_nonempty .basic)
      (show φtypBool .basic .dalmatian = true from by decide),
    show (extensionOf φtypBool .basic).card = 1 from by decide]; simp

private theorem nomBoolS1_ne_zero (w : NomWorld) : ∑' u, (nomBoolL0 u w : ℝ≥0∞) ^ (1:ℝ) * 1 ≠ 0 := by
  simp only [ENNReal.rpow_one, mul_one]
  rw [tsum_fintype]; intro h
  have hz := Finset.sum_eq_zero_iff.mp h
  cases w
  · exact nomBoolL0_ne_zero (u := .sub) (by decide) (hz .sub (Finset.mem_univ _))
  · exact nomBoolL0_ne_zero (u := .super) (by decide) (hz .super (Finset.mem_univ _))
  · exact nomBoolL0_ne_zero (u := .super) (by decide) (hz .super (Finset.mem_univ _))

private theorem nomBoolS1_ne_top (w : NomWorld) : ∑' u, (nomBoolL0 u w : ℝ≥0∞) ^ (1:ℝ) * 1 ≠ ⊤ := by
  simp only [ENNReal.rpow_one, mul_one]
  rw [tsum_fintype]; exact ENNReal.sum_ne_top.mpr fun u _ => PMF.apply_ne_top _ _

/-- Boolean nominal speaker. -/
noncomputable def nomBoolS1 (w : NomWorld) : PMF NomUtterance :=
  S1Belief nomBoolL0 (fun _ => 1) 1 w (nomBoolS1_ne_zero w) (nomBoolS1_ne_top w)

/-- The Boolean model shows **no** overspecification preference. -/
theorem nom_bool_no_overspec :
    ¬ (nomBoolS1 .dalmatian .basic < nomBoolS1 .dalmatian .sub) := by
  simp only [nomBoolS1, rsa, ENNReal.rpow_one, mul_one, nomBoolL0_basic, nomBoolL0_sub,
    lt_self_iff_false, not_false_iff]

/-! ### The unified mechanism -/

/-- **Capstone**: continuous semantics makes both overmodification (Exp 1) and
    overspecification (Exp 3) rational, while the Boolean model predicts neither —
    one mechanism, two phenomena, only the meaning function changes. -/
theorem unified_continuous_semantics :
    S1 target .small < S1 target .smallBlue ∧
    ¬ (boolS1 target .small < boolS1 target .smallBlue) ∧
    nomS1 .dalmatian .basic < nomS1 .dalmatian .sub ∧
    ¬ (nomBoolS1 .dalmatian .basic < nomBoolS1 .dalmatian .sub) :=
  ⟨csrsa_overmod_preferred, bool_no_overmod_preference,
   nominal_overspec_preferred, nom_bool_no_overspec⟩

end DegenEtAl2020
