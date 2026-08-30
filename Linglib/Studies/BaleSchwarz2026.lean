import Linglib.Studies.BaleSchwarz2022
import Linglib.Data.Examples.BaleSchwarz2026

/-!
# Bale and Schwarz 2026: natural language and external conventions, re-examining *per*

*Per*-phrases come in two kinds. Saturating a predicate of a simplex dimension, as in
*this sample weighs thirteen grams per milliliter* or *the train covered thirty miles per
hour*, they compose in the grammar, and the entries for *per* of both Coppock and Bale and
Schwarz can be restated with pure numbers and multiplication alone, the pure number being
the unique `n` with `n ⋅ mL = μ_VOL(x)`; so neither commits the grammar to quantity
division, which the No Division Hypothesis denies it altogether. Saturating a predicate of a
quotient dimension, as in *the density of that sample is thirteen grams per milliliter*,
they are math speak: verbalizations of the quantity-calculus term `13 g/mL`, whose meaning
comes from the external notation as a mixed quotation's does. Two diagnostics separate the
kinds. An unambiguous verbalization, *thirteen gee over em el*, substitutes for a math-speak
phrase but yields nonsense for a compositional one; and a compositional *per*-PP can be
fronted while a math-speak one, lacking structure the grammar can see, cannot. Both reduce
to the dimension facts of the 2022 paper: a composed *per*-phrase has its head unit's
dimension, so it can be a weight but never a density, while the quotient `13 g/mL` is a
density and never a weight.

## References

* [bale-schwarz-2026]
* [bale-schwarz-2022]
* [coppock-2021]
* [coppock-2022]
* [davidson-1979]
-/

namespace BaleSchwarz2026

open Degree Quantity English.MeasurePhrases BaleSchwarz2022
open Features (Dimension)

variable {E : Type*} {w : World E} {D D₁ D₂ : Dimension} {x y : E} {n : ℚ} {u r : MeasureTerm}

/-! ### Multiplication only -/

/-- The pure number `μ_dim(r)(y) / r` is the unique `n` with `n ⋅ r = μ_dim(r)(y)` ((21)). -/
theorem anaphoricPer_eq_pure_iff (hr : r.magnitude ≠ 0) :
    anaphoricPer w r y = pure n ↔ pure n * r.quantity = w.quantity r.dimension y :=
  div_eq_pure_iff hr rfl

theorem existsUnique_pure_mul (hr : r.magnitude ≠ 0) :
    ∃! n : ℚ, pure n * r.quantity = w.quantity r.dimension y :=
  ⟨(anaphoricPer w r y).1, (anaphoricPer_eq_pure_iff hr).1 (Prod.ext rfl anaphoricPer_snd),
    λ _ h => congrArg Prod.fst ((anaphoricPer_eq_pure_iff hr).2 h).symm⟩

/-- Coppock's *per* ((9), (15)): `λq λr λf λx. max{d | f d x} = μ_dim(q)(x) / q ⋅ r`, taking
the measure predicate `f` as an argument. -/
def coppockPer (w : World E) (r : MeasureTerm) (q : Quantity ℚ) (f : Quantity ℚ → E → Prop)
    (x : E) : Prop :=
  ∃ d, IsGreatest {d | f d x} d ∧ d = anaphoricPer w r x * q

/-- With the measure predicate `λd λx. μ_D(x) = d`, Coppock's entry and the anaphoric measure
phrase derive the same truth conditions ((14)). -/
theorem coppockPer_much_iff :
    coppockPer w r (pure n * u.quantity) (much (w.quantity D)) x ↔
      much (w.quantity D) (anaphoricMP w n u r x) x := by
  simp only [coppockPer, much, Set.ofPred_eq_eq_singleton', anaphoricMP,
    mul_comm _ (anaphoricPer w r x)]
  exact ⟨λ ⟨_, hd, h⟩ => (hd.unique isGreatest_singleton).symm.trans h,
    λ h => ⟨_, isGreatest_singleton, h⟩⟩

/-! ### Math speak -/

/-- A verbalization of the quantity-calculus term `n u / r` denotes that quotient. -/
def mathSpeak (n : ℚ) (u r : MeasureTerm) : Quantity ℚ := divisionMP n u r

/-- The measure `μ_{D₁} / μ_{D₂}` of a quotient dimension: density, speed. -/
def ratio (w : World E) (D₁ D₂ : Dimension) (x : E) : Quantity ℚ :=
  w.quantity D₁ x / w.quantity D₂ x

@[simp] theorem ratio_snd : (ratio w D₁ D₂ x).2 = .of D₁ / .of D₂ := by simp [ratio]

theorem density_eq_ratio : density w x = ratio w .mass .volume x := rfl

/-- A predicate of a quotient dimension accepts the verbalized quotient ((2), (6), (25)):
`μ_{D₁}(x) / μ_{D₂}(x) = n u / r`. -/
theorem ratio_eq_mathSpeak_iff (hu : u.dimension = D₁) (hr : r.dimension = D₂) :
    ratio w D₁ D₂ x = mathSpeak n u r ↔ w D₁ x / w D₂ x = n * u.magnitude / r.magnitude := by
  simp [ratio, mathSpeak, divisionMP, divisionPer, Prod.ext_iff, MeasureTerm.quantity, hu, hr]

/-- It never accepts a composed *per*-phrase ((27), (28)): fronting forces composition, and a
quantity of the head unit's dimension is no quotient. -/
theorem ratio_ne_anaphoricMP (hu : u.dimension = D₁) : ratio w D₁ D₂ x ≠ anaphoricMP w n u r y :=
  λ h => by simpa [hu] using congrArg Prod.snd h

/-- A predicate of a simplex dimension never accepts the verbalized quotient ((26)). -/
theorem not_much_mathSpeak (hu : u.dimension = D) : ¬ much (w.quantity D) (mathSpeak n u r) x :=
  not_much_divisionMP hu

/-! ### The paper's examples -/

open Data.Examples (LinguisticExample)

/-- The dimension a predicate measures in. -/
def predicateDimension? : String → Option QuantityDimension
  | "weight" => some (.of .mass)
  | "distance" => some (.of .distance)
  | "density" => some (.of .mass / .of .volume)
  | "speed" => some (.of .distance / .of .time)
  | "pressure" => some (.of .force / .of .area)
  | _ => none

/-- The measure term with symbol `s`. -/
def symbol? (s : String) : Option MeasureTerm := allMeasureTerms.find? (·.symbol = s)

/-- The head unit and *per*-unit of a row's *per*-phrase, from its unit nouns or from the
symbols of the term it verbalizes (`13 g/mL`). -/
def units? (e : LinguisticExample) : Option (MeasureTerm × MeasureTerm) :=
  match e.feature? "verbalizes" with
  | some v =>
    match (v.toList.dropWhile (· ≠ ' ')).drop 1 |>.span (· ≠ '/') with
    | (a, _ :: b) => do pure (← symbol? (String.ofList a), ← symbol? (String.ofList b))
    | _ => none
  | none => do pure (← measureTerm? (← e.feature? "unit"), ← measureTerm? (← e.feature? "per_unit"))

/-- Whether a row's *per*-phrase is composed: a fronted *per*-PP has been, a verbalization of
notation has not, and otherwise the paper's classification decides. -/
def composed? (e : LinguisticExample) : Option Bool :=
  if e.feature? "diagnostic" = some "sub-extraction" then some true
  else if (e.feature? "verbalizes").isSome then some false
  else match e.feature? "interpretation" with
    | some "compositional" => some true
    | some "math speak" => some false
    | _ => none

/-- A row's predicate dimension and the dimension of its *per*-phrase's denotation. -/
def dimensions? (e : LinguisticExample) : Option (QuantityDimension × QuantityDimension) := do
  let p ← predicateDimension? (← e.feature? "predicate_dimension")
  let (u, r) ← units? e
  let c ← composed? e
  pure (p, if c then .of u.dimension else .of u.dimension / .of r.dimension)

/-- The *per*-phrase's dimension matches the predicate's exactly in the felicitous rows. -/
theorem rows_dimension : ∀ e ∈ Examples.all, ∀ p ∈ dimensions? e,
    (p.1 = p.2 ↔ e.judgment = .acceptable) := by
  decide +kernel

end BaleSchwarz2026
