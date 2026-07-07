import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Measure-phrase modification of degree constructions
[schwarzschild-2005] [solt-2015] [winter-2005] [buring-2007]

Measure-phrase differentials ("3 inches taller") and factor phrases
("twice as tall"): `differentialComparative` and `factorEquative`, the
interval- and ratio-scale rows of the naturality table in
`Degree/Hom.lean`. Where bare comparatives are invariant under any
`StrictMono` rescaling (`comparativeSem_comp`), the differential is
invariant under translations only (`differentialComparative_comp_add`,
`differentialComparative_not_natural`) and the factor phrase under
scalings only (`factorEquative_comp_mul`,
`factorEquative_not_translation_invariant`) — the measurement-theoretic
scale hierarchy (`MeasurementLevel`) derived as invariance classes
rather than stipulated: a construction is meaningful on a scale type
exactly when it is natural under that type's admissible transformations.
Hence "3 inches taller" ✓ but "*3 units more beautiful" ✗ (beauty is
ordinal), "twice as tall" ✓ but "*twice as hot" in °C ✗ (temperature is
interval, no meaningful zero).
-/

namespace Degree

/-! ### Differential and factor semantics -/

/-- Differential comparative: "A is d-much Adj-er than B" iff
    `μ(A) - μ(B) = d`. Requires subtraction structure, not just
    ordering — what makes measure-phrase differentials more restrictive
    than bare comparatives. -/
def differentialComparative {Entity D : Type*} [Sub D]
    (μ : Entity → D) (a b : Entity) (diff : D) : Prop :=
  μ a - μ b = diff

/-- Factor phrase equative: "A is n times as tall as B" iff
    `μ(A) = n × μ(B)`. Requires a meaningful zero (ratio scale). -/
def factorEquative {Entity D : Type*} [Mul D]
    (μ : Entity → D) (a b : Entity) (factor : D) : Prop :=
  μ a = factor * μ b

/-- A positive differential entails the bare comparative. Stated on ℚ;
generalizing requires ordered-group machinery (`[AddCommGroup D] [LinearOrder D]
[IsStrictOrderedAddMonoid D]`) that mathlib's current taxonomy splits across
multiple unbundled classes — see e.g. `Mathlib/Algebra/Order/Field/Defs.lean`
for the analogous LinearOrderedField → Field + LinearOrder + IsStrictOrderedRing
migration. Consumers (Intensional, VonStechow1984) instantiate at ℚ. -/
theorem differential_positive_iff {Entity : Type*}
    (μ : Entity → ℚ) (a b : Entity) (diff : ℚ) (hdiff : 0 < diff) :
    differentialComparative μ a b diff → μ b < μ a := by
  intro h
  simp only [differentialComparative] at h
  linarith

/-! ### Invariance: the measurement-theoretic hierarchy derived

Each construction's scale-type requirement is its invariance class
(cf. `comparativeSem_comp` in `Degree/Hom.lean` for the ordinal row and
`positive_not_natural` for the positive form's failure). -/

/-- Differentials are translation-invariant: shifting the scale's zero
    point preserves gaps — differentials are meaningful on interval
    scales. -/
theorem differentialComparative_comp_add {Entity : Type*}
    (μ : Entity → ℚ) (c : ℚ) (a b : Entity) (diff : ℚ) :
    differentialComparative (fun x => μ x + c) a b diff ↔
      differentialComparative μ a b diff := by
  simp [differentialComparative]

/-- Differentials are NOT invariant under arbitrary monotone rescaling:
    a `StrictMono` map can destroy the gap. Differentials need interval
    structure — "*3 units more beautiful" fails because beauty supports
    only ordinal comparison. -/
theorem differentialComparative_not_natural :
    ∃ f : ℚ → ℚ, StrictMono f ∧ ∃ (μ : ℚ → ℚ) (a b diff : ℚ),
      differentialComparative μ a b diff ∧
      ¬ differentialComparative (f ∘ μ) a b diff := by
  refine ⟨(2 * ·), fun x y h => by simpa, id, 1, 0, 1, ?_, ?_⟩ <;>
    norm_num [differentialComparative]

/-- Factor phrases are scaling-invariant: changing the unit preserves
    ratios — factor phrases are meaningful on ratio scales. -/
theorem factorEquative_comp_mul {Entity : Type*}
    (μ : Entity → ℚ) {c : ℚ} (hc : c ≠ 0) (a b : Entity) (factor : ℚ) :
    factorEquative (fun x => c * μ x) a b factor ↔
      factorEquative μ a b factor := by
  simp only [factorEquative]
  constructor
  · intro h
    refine mul_left_cancel₀ hc ?_
    rw [h]; ring
  · intro h
    rw [h]; ring

/-- Factor phrases are NOT translation-invariant: moving the zero point
    destroys ratios — "*twice as hot" fails in °C because temperature's
    zero is conventional. -/
theorem factorEquative_not_translation_invariant :
    ∃ (μ : ℚ → ℚ) (c a b factor : ℚ),
      factorEquative μ a b factor ∧
      ¬ factorEquative (fun x => μ x + c) a b factor := by
  refine ⟨id, 1, 2, 1, 2, ?_, ?_⟩ <;> norm_num [factorEquative]

/-! ### Scale types as a lexical classification -/

/-- Measurement level of an adjective's scale, ordered by admissible
    transformations (each level's constructions are exactly those
    invariant under its transformation class — the theorems above):
    ordinal (any monotone map), interval (affine), ratio (scaling),
    extensive (ratio + cross-dimensional commensurability; spatial
    extent is [buring-2007]'s "only scale ... that has measurements in
    different dimensions mapped onto it", licensing subcomparatives). -/
inductive MeasurementLevel where
  | ordinal | interval | ratio | extensive
  deriving DecidableEq, Repr

/-- Measure-phrase differentials ("10 degrees warmer") require at least
    interval scale (`differentialComparative_comp_add`). -/
def MeasurementLevel.AdmitsMeasurePhrase (l : MeasurementLevel) : Prop :=
  l ≠ .ordinal

instance : DecidablePred MeasurementLevel.AdmitsMeasurePhrase :=
  fun l => inferInstanceAs (Decidable (l ≠ .ordinal))

/-- Factor phrases ("twice as tall") require a meaningful zero
    (`factorEquative_comp_mul`). -/
def MeasurementLevel.AdmitsFactorPhrase (l : MeasurementLevel) : Prop :=
  l = .ratio ∨ l = .extensive

instance : DecidablePred MeasurementLevel.AdmitsFactorPhrase :=
  fun l => inferInstanceAs (Decidable (_ ∨ _))

/-- Subcomparatives ("shorter than the house is high") require extensive
    commensurability: two measure functions sharing a unit. Hence
    "shorter than high" ✓ (both spatial), "??hotter than expensive" ✗. -/
def MeasurementLevel.AdmitsSubcomparative (l : MeasurementLevel) : Prop :=
  l = .extensive

instance : DecidablePred MeasurementLevel.AdmitsSubcomparative :=
  fun l => inferInstanceAs (Decidable (l = .extensive))

end Degree
