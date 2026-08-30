import Linglib.Semantics.Degree.Measure.Quantity
import Linglib.Semantics.Presupposition.Defs
import Linglib.Fragments.English.MeasurePhrases
import Linglib.Data.Examples.BaleSchwarz2022

/-!
# Bale and Schwarz 2022: measurements from *per* without complex dimensions

Two semantics for the preposition *per*. On the division theory, *per* divides
quantities: *0.9 grams per milliliter* denotes the density `0.9 g/mL`. On the anaphoric
theory, *per* measures a covert pronoun: *per milliliter* maps *pro* to its volume in
milliliters, a pure number that multiplies `0.9 g` without leaving the dimension of mass.
The paper argues for the anaphoric theory on two grounds. A measurement verb equates its
subject's mass with its complement, so the division theory hands *weighs* a density and
*the sample weighs 0.9 grams per milliliter* comes out contradictory, while the polysemous
*weigh* that would rescue it predicts a same-density reading of *this cube weighs what that
cube weighs* that nobody gets; the anaphoric measure phrase stays in the verb's dimension.
And *0.1 grams per milliliter* and *0.1 kilograms per liter* denote one and the same
quotient, yet only the former is felicitous of a 5-millilitre sample; the anaphoric *per* can
carry the presupposition that the pronoun's referent measures at least one unit, which no
constituent of the division theory's structure could state. Where both theories compose,
in measurement-verb and pseudo-partitive sentences alike, they derive the same truth
conditions. The paper closes on *the sample's density is 0.9 grams per milliliter*, which
the anaphoric theory predicts to be as odd as *#the sample's density is 0.9 grams*.

Worlds assign each base dimension its measure function; the covert pronoun's referent is a
parameter, resolved to the matrix subject. Units come from the English measure-term
fragment.

## References

* [bale-schwarz-2022]
* [coppock-2021]
* [nakanishi-2007]
* [schwarzschild-2006]
-/

namespace BaleSchwarz2022

open Degree Quantity English.MeasurePhrases Presupposition

variable {E : Type*}

/-- A world assigns each base dimension `D` its measure function `μ_D`. -/
abbrev World (E : Type*) := Dimension → E → ℚ

/-- `μ_D` as a dimensioned measure. -/
def World.measure (w : World E) (D : Dimension) : DimensionedMeasure E ℚ := ⟨D, w D⟩

/-- `μ_D(x)` as a quantity of dimension `D`. -/
def World.quantity (w : World E) (D : Dimension) (x : E) : Quantity ℚ :=
  (w.measure D).quantity x

@[simp] theorem World.quantity_fst (w : World E) (D : Dimension) (x : E) :
    (w.quantity D x).1 = w D x := rfl

@[simp] theorem World.quantity_snd (w : World E) (D : Dimension) (x : E) :
    (w.quantity D x).2 = .of D := rfl

variable {w : World E} {D : Dimension} {x y : E} {q : Quantity ℚ} {n k : ℚ}
  {u u' r r' : MeasureTerm}

/-! ### Measure predication -/

/-- `λq λx. μ(x) = q`: the measurement verb *weigh* with `μ = μ_WT` ((5)), and the covert
`MUCH` of pseudo-partitives with `μ` underspecified ((25)). -/
def much (μ : E → Quantity ℚ) (q : Quantity ℚ) (x : E) : Prop := μ x = q

theorem much_quantity_iff : much (w.quantity D) q x ↔ w D x = q.1 ∧ q.2 = .of D := by
  simp [much, Prod.ext_iff, eq_comm]

/-- A measure of dimension `D` never equates with a quantity of another dimension. -/
theorem not_much_quantity_of_snd_ne (h : q.2 ≠ .of D) : ¬ much (w.quantity D) q x := by
  simp [much_quantity_iff, h]

/-- `∃x[salt(x) ∧ μ(x) = q ∧ contain(m, x)]` ((26)). -/
def contains (salt : E → Prop) (contain : E → E → Prop) (μ : E → Quantity ℚ) (q : Quantity ℚ)
    (m : E) : Prop :=
  ∃ x, salt x ∧ much μ q x ∧ contain m x

/-! ### The division theory -/

/-- `⟦per⟧ = λr λq. q / r` ((1)). -/
def divisionPer (r q : Quantity ℚ) : Quantity ℚ := q / r

/-- `⟦n u per r⟧ = n u / r` ((2)). -/
def divisionMP (n : ℚ) (u r : MeasureTerm) : Quantity ℚ :=
  divisionPer r.quantity (pure n * u.quantity)

@[simp] theorem divisionMP_snd :
    (divisionMP n u r).2 = .of u.dimension / .of r.dimension := by
  simp [divisionMP, divisionPer, MeasureTerm.quantity]

/-- The division theory undergenerates ((7)): a measure of dimension `D` never equates with
a *per*-phrase headed by a `D`-unit. -/
theorem not_much_divisionMP (hu : u.dimension = D) :
    ¬ much (w.quantity D) (divisionMP n u r) x :=
  not_much_quantity_of_snd_ne (by simp [hu])

/-- `μ_{WT/VOL}`, the measure of the polysemous *weigh* of (8). -/
def density (w : World E) (x : E) : Quantity ℚ := w.quantity .mass x / w.quantity .volume x

/-- With the free relative denoting `y`'s measure, (10) equates the two measures ((12)). -/
theorem much_quantity_quantity_iff : much (w.quantity D) (w.quantity D y) x ↔ w D x = w D y := by
  simp [much_quantity_iff]

/-- The polysemous *weigh* adds a same-density reading ((13)) that holds of cubes of
unequal weight. -/
theorem density_reading :
    ∃ w : World Bool, much (density w) (density w false) true ∧ w .mass true ≠ w .mass false :=
  ⟨λ D b => match D, b with
    | .mass, true => 1000 | .mass, false => 2000 | .volume, true => 1 | .volume, false => 2
    | _, _ => 0,
   by simp [much, density, World.quantity, World.measure, DimensionedMeasure.quantity]; norm_num,
   by norm_num⟩

/-! ### The anaphoric theory -/

/-- `⟦per⟧ = λq λx. μ_dim(q)(x) / q` ((16)): the pronoun's referent measured in the unit, a
pure number. -/
def anaphoricPer (w : World E) (r : MeasureTerm) (y : E) : Quantity ℚ :=
  w.quantity r.dimension y / r.quantity

@[simp] theorem anaphoricPer_fst :
    (anaphoricPer w r y).1 = w r.dimension y / r.magnitude := rfl

@[simp] theorem anaphoricPer_snd : (anaphoricPer w r y).2 = 1 := by
  simp [anaphoricPer, MeasureTerm.quantity]

/-- `⟦[MP [MP n u] [PP pro per r]]⟧ = n u ⋅ μ_dim(r)(pro) / r` ((18)), `pro` resolved to
`y`. -/
def anaphoricMP (w : World E) (n : ℚ) (u r : MeasureTerm) (y : E) : Quantity ℚ :=
  pure n * u.quantity * anaphoricPer w r y

@[simp] theorem anaphoricMP_fst :
    (anaphoricMP w n u r y).1 = n * u.magnitude * (w r.dimension y / r.magnitude) := rfl

/-- The anaphoric measure phrase stays in its head unit's dimension ((19)). -/
@[simp] theorem anaphoricMP_snd : (anaphoricMP w n u r y).2 = .of u.dimension := by
  simp [anaphoricMP, MeasureTerm.quantity]

/-- The measurement-verb sentence composes ((22)): `μ_D(x) = n u ⋅ μ_dim(r)(y) / r`. -/
theorem much_anaphoricMP_iff (hu : u.dimension = D) :
    much (w.quantity D) (anaphoricMP w n u r y) x ↔
      w D x = n * u.magnitude * (w r.dimension y / r.magnitude) := by
  simp [much_quantity_iff, hu]

/-- Where both theories compose they agree: (9) and (22) with the pronoun's referent the
subject, (31) and (32) with it the container. -/
theorem much_divisionMP_iff_anaphoricMP (hy : w r.dimension y ≠ 0) (hr : r.magnitude ≠ 0) :
    much (λ x => w.quantity D x / w.quantity r.dimension y) (divisionMP n u r) x ↔
      much (w.quantity D) (anaphoricMP w n u r y) x :=
  div_eq_div_iff_eq_mul_div hy hr

theorem contains_divisionMP_iff_anaphoricMP {salt : E → Prop} {contain : E → E → Prop} {m : E}
    (hm : w r.dimension m ≠ 0) (hr : r.magnitude ≠ 0) :
    contains salt contain (λ x => w.quantity D x / w.quantity r.dimension m) (divisionMP n u r)
        m ↔
      contains salt contain (w.quantity D) (anaphoricMP w n u r m) m :=
  exists_congr λ _ => and_congr_right λ _ => and_congr_left λ _ =>
    much_divisionMP_iff_anaphoricMP hm hr

/-! ### Unit sensitivity -/

/-- `u'` is `k` times the unit `u`: a kilogram is `1000` grams, a liter `1000` milliliters. -/
def Scales (k : ℚ) (u' u : MeasureTerm) : Prop :=
  u'.dimension = u.dimension ∧ u'.magnitude = k * u.magnitude

theorem kilogram_scales_gram : Scales 1000 kilogram gram := ⟨rfl, by norm_num [kilogram, gram]⟩

theorem liter_scales_milliliter : Scales 1000 liter milliliter :=
  ⟨rfl, by norm_num [liter, milliliter]⟩

theorem Scales.quantity (h : Scales k u' u) : u'.quantity = pure k * u.quantity := by
  ext <;> simp [MeasureTerm.quantity, h.1, h.2]

/-- The division theory identifies scaled measure phrases, `0.1 kg / L = 0.1 g / mL`, so (27)
and (36a) receive one meaning ((36b)). -/
theorem divisionMP_scales (hk : k ≠ 0) (hu : Scales k u' u) (hr : Scales k r' r) :
    divisionMP n u' r' = divisionMP n u r := by
  rw [divisionMP, divisionMP, divisionPer, divisionPer, hu.quantity, hr.quantity, mul_left_comm,
    pure_mul_div_pure_mul hk]

/-- So does the anaphoric measure phrase. -/
theorem anaphoricMP_scales (hk : k ≠ 0) (hu : Scales k u' u) (hr : Scales k r' r) :
    anaphoricMP w n u' r' y = anaphoricMP w n u r y := by
  ext
  · simp only [anaphoricMP_fst, hu.2, hr.1, hr.2]; field_simp
  · simp [hu.1]

/-- (43): *per* presupposes that the pronoun's referent measures at least one unit,
`μ_dim(r)(y) ≥ r`. -/
def perPresup (r : MeasureTerm) (y : E) (w : World E) : Prop := r.magnitude ≤ w r.dimension y

/-- The revised *per* ((43)) as a presupposed value. -/
def anaphoricPer' (r : MeasureTerm) (y : E) : PartialValue (World E) (Quantity ℚ) where
  presup := perPresup r y
  value w := anaphoricPer w r y

/-- A sentence whose *per*-PP triggers (43), the presupposition projecting globally. -/
def perSentence (r : MeasureTerm) (y : E) (p : World E → Prop) : PartialProp (World E) where
  presup := (anaphoricPer' r y).presup
  assertion := p

@[simp] theorem perSentence_presup {p : World E → Prop} :
    (perSentence r y p).presup w ↔ r.magnitude ≤ w r.dimension y := Iff.rfl

/-- *y weighs n u per r*, the pronoun resolved to the subject ((20)). -/
def weighs (n : ℚ) (u r : MeasureTerm) (y : E) : PartialProp (World E) :=
  perSentence r y λ w => much (w.quantity .mass) (anaphoricMP w n u r y) y

/-- *m contains n u per r of salt*, the pronoun resolved to the container ((41)). -/
def containsPer (salt : E → Prop) (contain : E → E → Prop) (n : ℚ) (u r : MeasureTerm)
    (m : E) : PartialProp (World E) :=
  perSentence r m λ w => contains salt contain (w.quantity .mass) (anaphoricMP w n u r m) m

/-- Scaling the units leaves the assertion unchanged. -/
theorem weighs_assertion_scales (hk : k ≠ 0) (hu : Scales k u' u) (hr : Scales k r' r) :
    (weighs n u' r' y).assertion = (weighs n u r y).assertion := by
  funext w; simp [weighs, perSentence, anaphoricMP_scales hk hu hr]

theorem containsPer_assertion_scales {salt : E → Prop} {contain : E → E → Prop} {m : E}
    (hk : k ≠ 0) (hu : Scales k u' u) (hr : Scales k r' r) :
    (containsPer salt contain n u' r' m).assertion =
      (containsPer salt contain n u r m).assertion := by
  funext w; simp [containsPer, perSentence, anaphoricMP_scales hk hu hr]

/-- Scaling the *per*-unit raises the presupposition's bound from `r` to `k r`. -/
theorem perPresup_scales (hr : Scales k r' r) :
    perPresup r' y w ↔ k * r.magnitude ≤ w r.dimension y := by
  simp [perPresup, hr.1, hr.2]

/-- Unit sensitivity: a referent measuring at least one small unit but less than one large
unit satisfies the small unit's presupposition and not the large one's, though the two
sentences assert the same thing ((37) against (38a), (44) against (45a)). -/
theorem perPresup_of_between (hr : Scales k r' r) (h₁ : r.magnitude ≤ w r.dimension y)
    (h₂ : w r.dimension y < k * r.magnitude) : perPresup r y w ∧ ¬ perPresup r' y w :=
  ⟨h₁, by simp [perPresup_scales hr, h₂]⟩

/-! ### The copular puzzle -/

/-- No quantity of mass is a density: (47), and (46) on the anaphoric theory, are
contradictory. -/
theorem density_ne_of_snd (hq : q.2 = .of .mass) : density w x ≠ q := λ h => by
  simpa [density, hq] using congrArg Prod.snd h

theorem density_ne_anaphoricMP (hu : u.dimension = .mass) :
    density w x ≠ anaphoricMP w n u r y :=
  density_ne_of_snd (by simp [hu])

theorem density_ne_pure_mul (hu : u.dimension = .mass) : density w x ≠ pure n * u.quantity :=
  density_ne_of_snd (by simp [MeasureTerm.quantity, hu])

/-- On the division theory, (46) equates the sample's density with `n u / r`. -/
theorem density_eq_divisionMP_iff (hu : u.dimension = .mass) (hr : r.dimension = .volume) :
    density w x = divisionMP n u r ↔ w .mass x / w .volume x = n * u.magnitude / r.magnitude := by
  simp [density, divisionMP, divisionPer, Prod.ext_iff, MeasureTerm.quantity, hu, hr]

/-! ### The paper's examples -/

open Data.Examples (LinguisticExample)

/-- The natural number a digit string denotes. -/
def nat? (cs : List Char) : Option ℕ :=
  if cs.all Char.isDigit then some (cs.foldl (λ a c => 10 * a + (c.toNat - 48)) 0) else none

/-- The rational a decimal numeral denotes. -/
def decimal? (s : String) : Option ℚ :=
  match s.toList.span (· ≠ '.') with
  | (int, []) => nat? int
  | (int, _ :: frac) => do pure ((← nat? int) + (← nat? frac) / 10 ^ frac.length)

/-- A row's *per*-unit and its subject's stated measure in the same dimension. -/
structure Scenario where
  per : MeasureTerm
  subjectMeasure : ℚ
  subjectUnit : MeasureTerm

def scenario? (e : LinguisticExample) : Option Scenario := do
  let per ← measureTerm? (← e.feature? "per_unit")
  let m ← decimal? (← e.feature? "subject_measure")
  let su ← measureTerm? (← e.feature? "subject_unit")
  guard (su.dimension = per.dimension)
  pure ⟨per, m, su⟩

/-- The subject measures at least one *per*-unit exactly in the felicitous examples. -/
theorem rows_perPresup : ∀ e ∈ Examples.all, ∀ s ∈ scenario? e,
    (s.per.magnitude ≤ s.subjectMeasure * s.subjectUnit.magnitude ↔ e.judgment = .acceptable) := by
  decide +kernel

/-- At any world where the subject measures as stated, a *per*-sentence's presupposition
holds iff the example is felicitous. -/
theorem rows_presup (e : LinguisticExample) (he : e ∈ Examples.all) (s : Scenario)
    (hs : s ∈ scenario? e) (hy : w s.per.dimension y = s.subjectMeasure * s.subjectUnit.magnitude)
    (p : World E → Prop) : (perSentence s.per y p).presup w ↔ e.judgment = .acceptable := by
  rw [perSentence_presup, hy]; exact rows_perPresup e he s hs

end BaleSchwarz2022
