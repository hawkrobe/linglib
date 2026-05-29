/-!
# Numeral — the numeral as a grammatical object

Theory-neutral lexical core for numerals: the substrate a Fragment instantiates
and a semantics later interprets. A numeral word contributes a `Comparison`
(@cite{kennedy-2015}'s `REL`: bare / at-least / more-than / at-most / fewer-than)
and a numeric `argument`. The *measure* it compares against (cardinality, height,
cost) is supplied compositionally, so it is not a lexical field here.

The denotation — the `relationalGQ`-based meaning and the Kennedy-vs-Horn choice
for the bare form — lives in `Semantics/Numerals/`, which imports this object.
This is the same object/denotation split as `Typology/Pronoun/Basic.lean` (the
`Pronoun.Entry` object) vs. `Semantics/Reference/PronounDenotation.lean` (its
denotation). The WALS typological survey (`Numeral.Profile`, `fromWALS*`) lives
in the sibling `Typology/Numeral/WALS.lean`.

## Main declarations

* `Numeral.Comparison` — the relation a numeral draws between measured and stated
  magnitude (@cite{kennedy-2015}'s `REL`).
* `Numeral.Comparison.isStrict` — Class A (`>`, `<`) vs. non-strict (bare `=`,
  Class B `≥`, `≤`); @cite{geurts-nouwen-2007}, @cite{nouwen-2010}.
* `Numeral.Entry` — cross-linguistic lexical numeral entry (form, comparison,
  argument).
-/

namespace Numeral

/-- @cite{kennedy-2015}'s `REL`: the relation a numeral draws between an entity's
    measured magnitude and the stated magnitude. The five cases underlie the five
    surface forms. The order relation each names is supplied at interpretation
    time in `Semantics/Numerals/` (`Comparison.rel`), keeping this object
    theory-neutral. -/
inductive Comparison where
  /-- Bare / exact: `μ x = m`. -/
  | eq
  /-- "At least `m`": `μ x ≥ m` (Class B). -/
  | ge
  /-- "More than `m`": `μ x > m` (Class A). -/
  | gt
  /-- "At most `m`": `μ x ≤ m` (Class B). -/
  | le
  /-- "Fewer than `m`": `μ x < m` (Class A). -/
  | lt
  deriving DecidableEq, Repr, Inhabited

/-- Strict (Class A: `>`, `<`) vs. non-strict (bare `=`, Class B `≥`, `≤`). The
    modifier-level Class A/B split of @cite{geurts-nouwen-2007} /
    @cite{nouwen-2010} is `isStrict` restricted to the four modified forms. -/
def Comparison.isStrict : Comparison → Prop
  | .gt | .lt => True
  | _         => False

instance : DecidablePred Comparison.isStrict := fun c => by
  cases c <;> unfold Comparison.isStrict <;> infer_instance

/-- Cross-linguistic lexical numeral entry: surface form, the comparison it
    expresses, and its numeric argument. The measure compared against
    (cardinality, height, …) is compositional, not lexical, so it is supplied at
    denotation time rather than stored here. -/
structure Entry where
  /-- Surface form (romanization or orthographic). -/
  form : String
  /-- The comparison the numeral expresses (bare or a modifier). -/
  comparison : Comparison
  /-- The numeric argument: the `m` in "more than `m`", "exactly `m`", … -/
  argument : Nat
  deriving Repr, DecidableEq

end Numeral
