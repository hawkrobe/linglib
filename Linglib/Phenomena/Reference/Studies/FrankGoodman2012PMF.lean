import Linglib.Theories.Pragmatics.RSA.ReferenceGame

/-!
# @cite{frank-goodman-2012} reference game (concrete instance)
@cite{frank-goodman-2012}

"Predicting Pragmatic Reasoning in Language Games", Science 336, 998.

## What this file is

A **concrete instance** of the parametric reference-game substrate
(`Theories/Pragmatics/RSA/ReferenceGame.lean`). Everything architectural —
the size principle, pragmatic narrowing, unique reference — is proved
generically there, parametric in the meaning matrix and world prior. Here
we only need to:

1. Define the specific stimulus (3 objects, 4 features, denotation matrix).
2. Verify it satisfies `IsCovering`.
3. Compute three partition function values.
4. Derive the 4 paper findings as one-liner corollaries.

## Why split it this way

Every RSA paper using a "speaker normalises inverse-extension-size" pattern
inherits the substrate theorems unchanged. The pragmatic-narrowing theorem
is proved **once**, parametric in everything; FG12's specific findings are
its instantiation at the paper's stimulus. Per-stimulus arithmetic is a
small section of bookkeeping; the architectural content lives in the
substrate.

For RSA practitioners: this is the version where you don't re-derive
Eq. S1 → S4 per paper. You instantiate.
-/

set_option autoImplicit false

namespace FrankGoodman2012

open scoped ENNReal
open RSA.ReferenceGame

/-! ## §1. Stimulus

Fig. 1C of the paper: three objects (blue square, blue circle, green
square) and four feature-words (blue, green, square, circle). Two features
("green", "circle") are uniquely identifying; two ("blue", "square") are
ambiguous between two objects each. -/

/-- The three objects in the reference context. -/
inductive Object where
  | blue_square | blue_circle | green_square
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- The four feature-word utterances. -/
inductive Feature where
  | blue | green | square | circle
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- The denotation matrix: which feature applies to which object. -/
def Feature.appliesTo : Feature → Object → Bool
  | .blue,   .blue_square  => true
  | .blue,   .blue_circle  => true
  | .green,  .green_square => true
  | .square, .blue_square  => true
  | .square, .green_square => true
  | .circle, .blue_circle  => true
  | _, _ => false

/-- The stimulus is **covering**: every feature names some object, and
every object is named by some feature. -/
instance instCovering : IsCovering Feature.appliesTo where
  extension_nonempty u := by
    cases u
    · exact ⟨.blue_square,  RSA.mem_extensionOf.mpr rfl⟩
    · exact ⟨.green_square, RSA.mem_extensionOf.mpr rfl⟩
    · exact ⟨.blue_square,  RSA.mem_extensionOf.mpr rfl⟩
    · exact ⟨.blue_circle,  RSA.mem_extensionOf.mpr rfl⟩
  covering w := by
    cases w
    · exact ⟨.blue,  rfl⟩
    · exact ⟨.blue,  rfl⟩
    · exact ⟨.green, rfl⟩

/-- Local notation: refer to the substrate's `S1` at this stimulus's
meaning matrix without spelling out `Feature.appliesTo` everywhere. -/
local notation "S1fg" => S1 Feature.appliesTo

/-! ## §2. Numerical bookkeeping (partition function values)

The partition function `partition w = Σ_u L0 u w` measures the
size-principle weight of all alternatives at world `w`. Three distinct
values arise on this stimulus, each corresponding to a different
alternative-set composition. -/

/-- The applicable-feature filter at each world is concrete and `decide`-able. -/
private theorem filter_applies_blue_square :
    Finset.univ.filter (fun u : Feature => u.appliesTo .blue_square = true)
      = {.blue, .square} := by decide

private theorem filter_applies_blue_circle :
    Finset.univ.filter (fun u : Feature => u.appliesTo .blue_circle = true)
      = {.blue, .circle} := by decide

private theorem filter_applies_green_square :
    Finset.univ.filter (fun u : Feature => u.appliesTo .green_square = true)
      = {.green, .square} := by decide

/-- Extension cardinalities. -/
private theorem extension_card_blue   : (extension Feature.appliesTo .blue).card   = 2 := by decide
private theorem extension_card_green  : (extension Feature.appliesTo .green).card  = 1 := by decide
private theorem extension_card_square : (extension Feature.appliesTo .square).card = 2 := by decide
private theorem extension_card_circle : (extension Feature.appliesTo .circle).card = 1 := by decide

/-- Partition at `.blue_square`: alternatives `{blue, square}` each with
extension size 2 contribute `1/2` each; total `1`. -/
theorem partition_blue_square : partition Feature.appliesTo .blue_square = 1 := by
  rw [partition_eq_filter_sum, filter_applies_blue_square,
      Finset.sum_insert (by decide), Finset.sum_singleton,
      extension_card_blue, extension_card_square]
  show ((2 : ℕ) : ℝ≥0∞)⁻¹ + ((2 : ℕ) : ℝ≥0∞)⁻¹ = 1
  rw [Nat.cast_ofNat]; exact ENNReal.inv_two_add_inv_two

/-- ENNReal arithmetic helper: `2⁻¹ + 1 = 3/2`. -/
private theorem two_inv_add_one : (2 : ℝ≥0∞)⁻¹ + 1 = 3 / 2 := by
  rw [show (1 : ℝ≥0∞) = 2 / 2 from
        (ENNReal.div_self (by norm_num) (by norm_num)).symm,
      show ((2 : ℝ≥0∞))⁻¹ = 1 / 2 from by rw [one_div],
      ENNReal.div_add_div_same]; norm_num

/-- Partition at `.blue_circle`: `{blue, circle}` with extension sizes 2 and 1
— `circle` is uniquely identifying; total `1/2 + 1 = 3/2`. -/
theorem partition_blue_circle : partition Feature.appliesTo .blue_circle = 3 / 2 := by
  rw [partition_eq_filter_sum, filter_applies_blue_circle,
      Finset.sum_insert (by decide), Finset.sum_singleton,
      extension_card_blue, extension_card_circle]
  show ((2 : ℕ) : ℝ≥0∞)⁻¹ + ((1 : ℕ) : ℝ≥0∞)⁻¹ = 3 / 2
  rw [Nat.cast_one, Nat.cast_ofNat, inv_one, two_inv_add_one]

/-- Partition at `.green_square`: `{green, square}` with extension sizes 1 and 2
— `green` is uniquely identifying; total `1 + 1/2 = 3/2`. -/
theorem partition_green_square : partition Feature.appliesTo .green_square = 3 / 2 := by
  rw [partition_eq_filter_sum, filter_applies_green_square,
      Finset.sum_insert (by decide), Finset.sum_singleton,
      extension_card_green, extension_card_square]
  show ((1 : ℕ) : ℝ≥0∞)⁻¹ + ((2 : ℕ) : ℝ≥0∞)⁻¹ = 3 / 2
  rw [Nat.cast_one, Nat.cast_ofNat, inv_one, add_comm, two_inv_add_one]

/-! ## §3. The four paper findings — one-liner corollaries

Each finding follows from one architectural theorem in the substrate
applied to one partition comparison. -/

/-- **Pragmatic narrowing for "blue"**: a speaker wanting `.blue_circle`
would say "circle" (uniquely identifying — its partition contribution is
`1`). Saying "blue" instead signals `.blue_square`, where the alternative-
set partition is smaller. -/
theorem blue_pragmatic_narrowing :
    S1fg .blue_circle .blue < S1fg .blue_square .blue := by
  -- "blue" applies at both; reduce to comparing partitions.
  apply S1_lt_of_partition_gt _ rfl rfl
  -- partition .blue_square (= 1) < partition .blue_circle (= 3/2).
  show partition _ _ < partition _ _
  rw [partition_blue_square, partition_blue_circle]
  exact ENNReal.lt_div_iff_mul_lt (by norm_num) (by norm_num) |>.mpr (by norm_num)

/-- **Pragmatic narrowing for "square"**: a speaker wanting `.green_square`
would say "green" (uniquely identifying). Saying "square" instead signals
`.blue_square`. -/
theorem square_pragmatic_narrowing :
    S1fg .green_square .square < S1fg .blue_square .square := by
  apply S1_lt_of_partition_gt _ rfl rfl
  show partition _ _ < partition _ _
  rw [partition_blue_square, partition_green_square]
  exact ENNReal.lt_div_iff_mul_lt (by norm_num) (by norm_num) |>.mpr (by norm_num)

/-- **Unique reference for "green"**: "green" applies only to `.green_square`,
so the speaker prefers it there over any other world. -/
theorem green_unique_reference :
    S1fg .blue_square .green < S1fg .green_square .green :=
  S1_lt_of_appliesTo_only Feature.appliesTo (by decide) rfl

/-- **Unique reference for "circle"**: "circle" applies only to `.blue_circle`. -/
theorem circle_unique_reference :
    S1fg .blue_square .circle < S1fg .blue_circle .circle :=
  S1_lt_of_appliesTo_only Feature.appliesTo (by decide) rfl

end FrankGoodman2012
