module

public import Linglib.Semantics.Degree.Measure.Quantity

/-!
# English measure phrases

Lexical entries for the English nouns that quantize a mass noun in a pseudo-partitive
(*three grams of salt*, *three glasses of water*, *three grains of rice*): measure terms,
which name a unit quantity of a dimension, and the container nouns and atomizers of
Scontras's classification. A measure term carries the size of its unit relative to the
dimension's reference unit, so that `kilogram.quantity = pure 1000 * gram.quantity`.

## References

* [scontras-2014]
* [bale-schwarz-2022]
-/

@[expose] public section

namespace English.MeasurePhrases

open Degree (Dimension QuantizingNounClass)

/-- A measure term, a noun naming a unit quantity of a dimension. -/
structure MeasureTerm where
  form : String
  formPlural : String
  /-- The unit's symbol in the quantity calculus (`g`, `mL`, `km`). -/
  symbol : String
  dimension : Dimension
  /-- Size of the unit relative to the dimension's reference unit (gram, milliliter, meter,
  second): a kilogram is `1000` grams, a mile `1609.344` meters. -/
  magnitude : ℚ := 1
  deriving Repr, BEq

/-- The unit quantity a measure term denotes. -/
def MeasureTerm.quantity (t : MeasureTerm) : Degree.Quantity ℚ := (t.magnitude, .of t.dimension)

/-- *gram*. -/
def gram : MeasureTerm :=
  { form := "gram", formPlural := "grams", symbol := "g", dimension := .mass }
/-- *kilogram*. -/
def kilogram : MeasureTerm :=
  { form := "kilogram", formPlural := "kilograms", symbol := "kg", dimension := .mass,
    magnitude := 1000 }
/-- *kilo*. -/
def kilo : MeasureTerm :=
  { form := "kilo", formPlural := "kilos", symbol := "kg", dimension := .mass, magnitude := 1000 }
/-- *pound*. -/
def pound : MeasureTerm :=
  { form := "pound", formPlural := "pounds", symbol := "lb", dimension := .mass,
    magnitude := 45359237 / 100000 }
/-- *milliliter*. -/
def milliliter : MeasureTerm :=
  { form := "milliliter", formPlural := "milliliters", symbol := "mL",
    dimension := .volume }
/-- *liter*. -/
def liter : MeasureTerm :=
  { form := "liter", formPlural := "liters", symbol := "L", dimension := .volume,
    magnitude := 1000 }
/-- *mile*. -/
def mile : MeasureTerm :=
  { form := "mile", formPlural := "miles", symbol := "mi", dimension := .distance,
    magnitude := 1609344 / 1000 }
/-- *kilometer*. -/
def kilometer : MeasureTerm :=
  { form := "kilometer", formPlural := "kilometers", symbol := "km", dimension := .distance,
    magnitude := 1000 }
/-- *meter*. -/
def meter : MeasureTerm :=
  { form := "meter", formPlural := "meters", symbol := "m", dimension := .distance }
/-- *hour*. -/
def hour : MeasureTerm :=
  { form := "hour", formPlural := "hours", symbol := "h", dimension := .time, magnitude := 3600 }
/-- *second*. -/
def second_ : MeasureTerm :=
  { form := "second", formPlural := "seconds", symbol := "s", dimension := .time }

/-- The measure terms. -/
def allMeasureTerms : List MeasureTerm :=
  [gram, kilogram, kilo, pound, milliliter, liter, mile, kilometer, meter, hour, second_]

/-- The measure term with singular or plural form `s`. -/
def measureTerm? (s : String) : Option MeasureTerm :=
  allMeasureTerms.find? fun t ↦ t.form = s ∨ t.formPlural = s

/-- A quantizing noun turns a mass term into a countable expression, as a measure term, a
container noun or an atomizer. -/
structure QuantizingNoun where
  form : String
  formPlural : String
  nounClass : QuantizingNounClass
  /-- The dimension a measure term names, or that a container noun measures on its
  measure reading; atomizers name no measure function. -/
  dimension : Option Dimension := none
  deriving Repr, BEq

/-- A measure term as a quantizing noun. -/
def MeasureTerm.toQuantizingNoun (t : MeasureTerm) : QuantizingNoun :=
  { form := t.form, formPlural := t.formPlural, nounClass := .measureTerm,
    dimension := some t.dimension }

instance : Coe MeasureTerm QuantizingNoun := ⟨MeasureTerm.toQuantizingNoun⟩

/-- *glass*. -/
def glass : QuantizingNoun :=
  { form := "glass", formPlural := "glasses", nounClass := .containerNoun,
    dimension := some .volume }
/-- *box*. -/
def box : QuantizingNoun :=
  { form := "box", formPlural := "boxes", nounClass := .containerNoun, dimension := some .volume }
/-- *cup*. -/
def cup : QuantizingNoun :=
  { form := "cup", formPlural := "cups", nounClass := .containerNoun, dimension := some .volume }
/-- *bag*. -/
def bag : QuantizingNoun :=
  { form := "bag", formPlural := "bags", nounClass := .containerNoun, dimension := some .volume }
/-- *bottle*. -/
def bottle : QuantizingNoun :=
  { form := "bottle", formPlural := "bottles", nounClass := .containerNoun,
    dimension := some .volume }
/-- *grain*. -/
def grain : QuantizingNoun :=
  { form := "grain", formPlural := "grains", nounClass := .atomizer }
/-- *piece*. -/
def piece : QuantizingNoun :=
  { form := "piece", formPlural := "pieces", nounClass := .atomizer }
/-- *drop*. -/
def drop : QuantizingNoun :=
  { form := "drop", formPlural := "drops", nounClass := .atomizer }
/-- *slice*. -/
def slice : QuantizingNoun :=
  { form := "slice", formPlural := "slices", nounClass := .atomizer }
/-- *chunk*. -/
def chunk : QuantizingNoun :=
  { form := "chunk", formPlural := "chunks", nounClass := .atomizer }

/-- The quantizing nouns. -/
def allQuantizingNouns : List QuantizingNoun :=
  allMeasureTerms.map (↑) ++ [glass, box, cup, bag, bottle, grain, piece, drop, slice, chunk]

end English.MeasurePhrases
