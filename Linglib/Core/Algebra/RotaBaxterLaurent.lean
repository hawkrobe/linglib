/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.RotaBaxter
import Mathlib.RingTheory.LaurentSeries

/-!
# The polar-part Rota–Baxter operator on Laurent series  `[UPSTREAM]`

The **prototype** Rota–Baxter operator of weight `-1` ([marcolli-chomsky-berwick-2025] Prop. 3.5.2,
eq. (3.5.4)) — the minimal-subtraction operator of Connes–Kreimer renormalization in physics. On the
Laurent series `LaurentSeries A = HahnSeries ℤ A`, the projection onto the **polar part** (the
strictly-negative-degree coefficients),

  `R(Σ aᵢ tⁱ) = Σ_{i < 0} aᵢ tⁱ`,

is a Rota–Baxter operator of weight `-1`. This realizes the example named in `RotaBaxter.lean`'s
docstring (the Laurent-series polar projection) and is the operator
[marcolli-chomsky-berwick-2025] §3.5.2 use to recast Minimal Yield as a Birkhoff factorization
(Sideward Merge appears as the polar/divergent part, removed by the renormalized character).

The Rota–Baxter identity is proved from the splitting `LaurentSeries A = R ⊕ (1 − R)` into the two
**subalgebras** of polar (support `< 0`) and non-polar (support `≥ 0`) series: `R` fixes products of
polar parts and kills products of non-polar parts, because `support (x * y) ⊆ support x + support y`
(`HahnSeries.support_mul_subset`).

## Implementation notes

The lemmas are stated at the *coefficient function* level (`polarHahn`, not a packaged `LinearMap`)
and the `op` field of `rotaBaxterPolar` is constructed **inline**, so its module is the expected
`Algebra.toModule` rather than `HahnSeries.instModule`. This avoids the `Module`-instance diamond on
`LaurentSeries A` (the two modules are defeq but distinct *terms*, and reconciling them runs `isDefEq`
through the noncomputable Laurent multiplication) — the same way mathlib proves the `HahnSeries` ring
axioms directly at the coefficient level rather than by transporting packaged maps.

## Main definitions

- `LaurentSeries.polarHahn`: the polar projection on coefficients.
- `LaurentSeries.rotaBaxterPolar`: the weight-`-1` Rota–Baxter operator structure.

## References

[marcolli-chomsky-berwick-2025] (Prop. 3.5.2, eq. (3.5.4))
-/

namespace LaurentSeries

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]

/-- The coefficient function of the polar part: keep the strictly-negative degrees. -/
private def polarCoeff (s : LaurentSeries A) : ℤ → A := fun i => if i < 0 then s.coeff i else 0

private theorem polarCoeff_support_subset (s : LaurentSeries A) :
    Function.support (polarCoeff s) ⊆ Function.support s.coeff := fun i hi => by
  simp only [polarCoeff, Function.mem_support] at hi ⊢
  exact fun h => hi (by simp [h])

/-- The **polar part** of a Laurent series: the strictly-negative-degree part
    ([marcolli-chomsky-berwick-2025] eq. (3.5.4)). -/
def polarHahn (s : LaurentSeries A) : LaurentSeries A where
  coeff := polarCoeff s
  isPWO_support' := s.isPWO_support'.mono (polarCoeff_support_subset s)

@[simp] theorem coeff_polarHahn (s : LaurentSeries A) (i : ℤ) :
    (polarHahn s).coeff i = if i < 0 then s.coeff i else 0 := rfl

@[simp] theorem polarHahn_zero : polarHahn (0 : LaurentSeries A) = 0 :=
  HahnSeries.coeff_inj.mp <| funext fun i => by simp only [coeff_polarHahn]; split_ifs <;> rfl

theorem polarHahn_add (x y : LaurentSeries A) :
    polarHahn (x + y) = polarHahn x + polarHahn y :=
  HahnSeries.coeff_inj.mp <| funext fun i => by
    simp only [coeff_polarHahn, HahnSeries.coeff_add]; split_ifs <;> simp

theorem polarHahn_sub (x y : LaurentSeries A) :
    polarHahn (x - y) = polarHahn x - polarHahn y :=
  HahnSeries.coeff_inj.mp <| funext fun i => by
    simp only [coeff_polarHahn, HahnSeries.coeff_sub]; split_ifs <;> simp

/-! ### The two subalgebras of the splitting -/

/-- `R` fixes a series supported on strictly-negative degrees. -/
theorem polarHahn_eq_self (s : LaurentSeries A) (h : ∀ i : ℤ, 0 ≤ i → s.coeff i = 0) :
    polarHahn s = s :=
  HahnSeries.coeff_inj.mp <| funext fun i => by
    rw [coeff_polarHahn]; split_ifs with hlt
    · rfl
    · exact (h i (not_lt.mp hlt)).symm

/-- `R` kills a series supported on non-negative degrees. -/
theorem polarHahn_eq_zero (s : LaurentSeries A) (h : ∀ i : ℤ, i < 0 → s.coeff i = 0) :
    polarHahn s = 0 :=
  HahnSeries.coeff_inj.mp <| funext fun i => by
    rw [coeff_polarHahn, HahnSeries.coeff_zero]; split_ifs with hlt
    · exact h i hlt
    · rfl

/-- The polar part is supported on strictly-negative degrees. -/
theorem support_polarHahn_subset (s : LaurentSeries A) :
    (polarHahn s).support ⊆ {i : ℤ | i < 0} := fun i hi => by
  rw [HahnSeries.mem_support, coeff_polarHahn] at hi
  show i < 0
  by_contra h
  rw [if_neg h] at hi
  exact hi rfl

/-- The complementary part `1 − R` is supported on non-negative degrees. -/
theorem support_sub_polarHahn_subset (s : LaurentSeries A) :
    (s - polarHahn s).support ⊆ {i : ℤ | 0 ≤ i} := fun i hi => by
  rw [HahnSeries.mem_support, HahnSeries.coeff_sub, coeff_polarHahn] at hi
  show 0 ≤ i
  by_contra h
  rw [if_pos (not_le.mp h), sub_self] at hi
  exact hi rfl

/-- A product of polar parts has no non-negative-degree coefficients (the polar series form a
    subalgebra). -/
theorem polarMul_coeff_eq_zero_of_nonneg (a b : LaurentSeries A) {i : ℤ} (hi : 0 ≤ i) :
    (polarHahn a * polarHahn b).coeff i = 0 := by
  by_contra hne
  obtain ⟨j, hj, l, hl, hjl⟩ :=
    Set.mem_add.mp (HahnSeries.support_mul_subset ((HahnSeries.mem_support _ _).mpr hne))
  have hj' := support_polarHahn_subset a hj
  have hl' := support_polarHahn_subset b hl
  simp only [Set.mem_setOf_eq] at hj' hl'
  omega

/-- A product of non-polar parts has no strictly-negative-degree coefficients (the non-polar series
    form a subalgebra). -/
theorem coPolarMul_coeff_eq_zero_of_neg (a b : LaurentSeries A) {i : ℤ} (hi : i < 0) :
    ((a - polarHahn a) * (b - polarHahn b)).coeff i = 0 := by
  by_contra hne
  obtain ⟨j, hj, l, hl, hjl⟩ :=
    Set.mem_add.mp (HahnSeries.support_mul_subset ((HahnSeries.mem_support _ _).mpr hne))
  have hj' := support_sub_polarHahn_subset a hj
  have hl' := support_sub_polarHahn_subset b hl
  simp only [Set.mem_setOf_eq] at hj' hl'
  omega

/-! ### The Rota–Baxter operator -/

/-- **The polar-projection Rota–Baxter identity** (weight `-1`, sub-form)
    ([marcolli-chomsky-berwick-2025] Prop. 3.5.2): `R(a)R(b) = R(R(a)b + aR(b) − ab)`, from the ring
    identity `R(a)b + aR(b) − ab = R(a)R(b) − (a−R(a))(b−R(b))` and the splitting into the two
    subalgebras (`R` fixes `R(a)R(b)`, kills `(a−R(a))(b−R(b))`). -/
theorem polarHahn_rotaBaxter (a b : LaurentSeries A) :
    polarHahn a * polarHahn b = polarHahn (polarHahn a * b + a * polarHahn b - a * b) := by
  have key : polarHahn a * b + a * polarHahn b - a * b
           = polarHahn a * polarHahn b - (a - polarHahn a) * (b - polarHahn b) := by ring
  rw [key, polarHahn_sub,
    polarHahn_eq_self _ (fun i hi => polarMul_coeff_eq_zero_of_nonneg a b hi),
    polarHahn_eq_zero _ (fun i hi => coPolarMul_coeff_eq_zero_of_neg a b hi), sub_zero]

/-- The coefficient of `algebraMap c * y`: the `LaurentSeries` algebra map (resolved via
    `HahnSeries.powerSeriesAlgebra`, `k → PowerSeries A → LaurentSeries A`) is the constant series
    `single 0 (algebraMap k A c)`, so the action is coefficient-wise. -/
private theorem coeff_algebraMap_mul (c : k) (y : LaurentSeries A) (i : ℤ) :
    (algebraMap k (LaurentSeries A) c * y).coeff i = algebraMap k A c * y.coeff i := by
  have e : algebraMap k (LaurentSeries A) c = HahnSeries.single 0 (algebraMap k A c) := by
    rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply, HahnSeries.ofPowerSeries_C,
      HahnSeries.C_apply]
  rw [e, HahnSeries.coeff_single_zero_mul]

/-- **The polar projection is a Rota–Baxter operator of weight `-1`** on `LaurentSeries A`
    ([marcolli-chomsky-berwick-2025] Prop. 3.5.2): the prototype minimal-subtraction operator. The
    `op` linear map is built inline with `letI := Algebra.toModule` to pin the expected module (see
    the implementation note); `map_smul'` is then over the algebra action `c • x = algebraMap c * x`. -/
noncomputable def rotaBaxterPolar : RotaBaxter k (LaurentSeries A) (-1) where
  op := by
    letI : Module k (LaurentSeries A) := Algebra.toModule
    exact
    { toFun := polarHahn
      map_add' := polarHahn_add
      map_smul' := fun c x => by
        refine HahnSeries.coeff_inj.mp (funext fun i => ?_)
        rw [coeff_polarHahn, RingHom.id_apply, Algebra.smul_def, Algebra.smul_def,
          coeff_algebraMap_mul, coeff_algebraMap_mul, coeff_polarHahn]
        split_ifs <;> ring }
  rotaBaxter a b := by
    letI : Module k (LaurentSeries A) := Algebra.toModule
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [neg_one_smul, ← sub_eq_add_neg]
    exact polarHahn_rotaBaxter a b

@[simp] theorem rotaBaxterPolar_op_apply (s : LaurentSeries A) :
    (rotaBaxterPolar (k := k)).op s = polarHahn s := by
  simp only [rotaBaxterPolar, LinearMap.coe_mk, AddHom.coe_mk]

end LaurentSeries
