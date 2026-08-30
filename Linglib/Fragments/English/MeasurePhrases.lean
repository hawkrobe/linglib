import Linglib.Semantics.Degree.Measure.Quantity

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

def gram : MeasureTerm :=
  { form := "gram", formPlural := "grams", symbol := "g", dimension := .mass }
def kilogram : MeasureTerm :=
  { form := "kilogram", formPlural := "kilograms", symbol := "kg", dimension := .mass,
    magnitude := 1000 }
def kilo : MeasureTerm :=
  { form := "kilo", formPlural := "kilos", symbol := "kg", dimension := .mass, magnitude := 1000 }
def pound : MeasureTerm :=
  { form := "pound", formPlural := "pounds", symbol := "lb", dimension := .mass,
    magnitude := 45359237 / 100000 }
def milliliter : MeasureTerm :=
  { form := "milliliter", formPlural := "milliliters", symbol := "mL",
    dimension := .volume }
def liter : MeasureTerm :=
  { form := "liter", formPlural := "liters", symbol := "L", dimension := .volume,
    magnitude := 1000 }
def mile : MeasureTerm :=
  { form := "mile", formPlural := "miles", symbol := "mi", dimension := .distance,
    magnitude := 1609344 / 1000 }
def kilometer : MeasureTerm :=
  { form := "kilometer", formPlural := "kilometers", symbol := "km", dimension := .distance,
    magnitude := 1000 }
def meter : MeasureTerm :=
  { form := "meter", formPlural := "meters", symbol := "m", dimension := .distance }
def hour : MeasureTerm :=
  { form := "hour", formPlural := "hours", symbol := "h", dimension := .time, magnitude := 3600 }
def second_ : MeasureTerm :=
  { form := "second", formPlural := "seconds", symbol := "s", dimension := .time }

def allMeasureTerms : List MeasureTerm :=
  [gram, kilogram, kilo, pound, milliliter, liter, mile, kilometer, meter, hour, second_]

/-- The measure term with singular or plural form `s`. -/
def measureTerm? (s : String) : Option MeasureTerm :=
  allMeasureTerms.find? λ t => t.form = s ∨ t.formPlural = s

/-- A quantizing noun, one that turns a mass term into a countable expression: a measure
term, a container noun, or an atomizer. -/
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

def glass : QuantizingNoun :=
  { form := "glass", formPlural := "glasses", nounClass := .containerNoun,
    dimension := some .volume }
def box : QuantizingNoun :=
  { form := "box", formPlural := "boxes", nounClass := .containerNoun, dimension := some .volume }
def cup : QuantizingNoun :=
  { form := "cup", formPlural := "cups", nounClass := .containerNoun, dimension := some .volume }
def bag : QuantizingNoun :=
  { form := "bag", formPlural := "bags", nounClass := .containerNoun, dimension := some .volume }
def bottle : QuantizingNoun :=
  { form := "bottle", formPlural := "bottles", nounClass := .containerNoun,
    dimension := some .volume }
def grain : QuantizingNoun := { form := "grain", formPlural := "grains", nounClass := .atomizer }
def piece : QuantizingNoun := { form := "piece", formPlural := "pieces", nounClass := .atomizer }
def drop : QuantizingNoun := { form := "drop", formPlural := "drops", nounClass := .atomizer }
def slice : QuantizingNoun := { form := "slice", formPlural := "slices", nounClass := .atomizer }
def chunk : QuantizingNoun := { form := "chunk", formPlural := "chunks", nounClass := .atomizer }

def allQuantizingNouns : List QuantizingNoun :=
  allMeasureTerms.map (↑) ++ [glass, box, cup, bag, bottle, grain, piece, drop, slice, chunk]

end English.MeasurePhrases
