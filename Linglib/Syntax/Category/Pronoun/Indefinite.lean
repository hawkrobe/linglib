import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Linglib.Features.Indefinite
import Linglib.Syntax.Category.Pronoun.Basic
import Linglib.Syntax.Category.Pronoun.Capabilities

open Morphology (Word)

/-!
# Indefinite pronouns — the pronominal carrier of the indefinite series
[haspelmath-1997]

The **pronoun** member of the cross-categorial indefinite series: `IndefinitePronoun` `extends`
the general `Pronoun` (`Syntax/Category/Pronoun/Basic.lean`) and carries the [haspelmath-1997] series data
(via `Features/Indefinite.lean`). A form like *someone* is one such object, instantiated in a
Fragment, that flows through the Pronoun API like any other pronoun.

This is *one carrier* of the series, not its home: indefiniteness is word-class-neutral (the
`Indefinite` capability and its feature taxonomy live in `Features/Indefinite.lean`). An indefinite
determiner (*some* book) or pro-adverb (*somewhere*) would be a sibling carrier — a different
word-class object supplying its own `instance : Indefinite That` — read by the same `[Indefinite α]`
generic code. Cross-linguistic generalizations *over* indefinite pronouns (paradigm, WALS F46A
bridge, syncretism) are typological and live in `Typology/Indefinite.lean`.

## Main declarations

* `Indefinite.IndefinitePronoun` — the lexical object (`extends Pronoun`).
* `instance : Indefinite Indefinite.IndefinitePronoun` — the pronoun carrier of the series.
* `Proform` / `Bound` instances routing the object through the Pronoun API.
-/

set_option autoImplicit false

namespace Indefinite


/-- A single indefinite pronoun — the canonical lexical object, `extends`ing the
    general `Pronoun` (surface `form` + φ-features) with the indefinite-series
    structure: its `ontology`-cal category ([haspelmath-1997] §3.1.3), its
    morphological `basis`, and the `functions` it covers on the implicational map.

    This is the single source of truth for an indefinite pronoun: it *is* a
    `Pronoun`, so it flows through the Pronoun API, and it carries its own
    distribution. `functions` is the realized cross-linguistic distribution
    (textbook-consensus data); theory-specific predictions about which functions
    a form *should* cover (Degano & Aloni 7-type team-semantics, choice-function
    denotation, Hamblin alternatives) are projections into theory-side types,
    not fields here. -/
structure IndefinitePronoun extends Pronoun where
  /-- The [haspelmath-1997] §3.1.3 ontological category (person, thing, …). -/
  ontology : OntologicalCategory
  /-- The morphological derivation strategy (interrogative-based, etc.). -/
  basis : MorphologicalBasis
  /-- The functions on [haspelmath-1997]'s implicational map this form
      covers (a contiguous region; see `IndefiniteParadigm.AllContiguous`). -/
  functions : Finset HaspelmathFunction
  deriving DecidableEq

/-- Manual `Repr` showing just the surface `form` to avoid the `unsafe`
    `Repr (Finset α)` instance from `Mathlib.Data.Finset.Sort`, which
    would propagate unsafety into every consumer of `IndefinitePronoun`. -/
instance : Repr IndefinitePronoun where
  reprPrec e _ := s!"{e.form}"

/-- Does this entry cover function `f`? -/
def IndefinitePronoun.covers (e : IndefinitePronoun) (f : HaspelmathFunction) : Bool :=
  decide (f ∈ e.functions)

/-- For each form, the list of functions it covers, in `HaspelmathFunction.all`
    order. -/
def IndefinitePronoun.functionList (e : IndefinitePronoun) : List HaspelmathFunction :=
  HaspelmathFunction.all.filter (e.covers ·)

/-- Coverage of a single form: number of functions it spans. -/
def IndefinitePronoun.coverage (e : IndefinitePronoun) : Nat :=
  e.functionList.length

end Indefinite

/-! ### Capability instances -/

/-- The indefinite pronoun is a `Proform` (form + φ via its `Pronoun` core). -/
instance : Proform Indefinite.IndefinitePronoun :=
  ⟨fun e => e.toPronoun.form, fun e => e.toPronoun.toWord.phi⟩

/-- An indefinite pronoun is a Principle-B pronominal (its `Pronoun` core's class,
    defaulting an undeclared φ-shell to `.pronoun`). -/
instance : Bound Indefinite.IndefinitePronoun :=
  ⟨fun e => e.toPronoun.bindingClass.getD .pronoun⟩

/-- The indefinite pronoun is the pronominal carrier of the indefinite series. -/
instance : Indefinite Indefinite.IndefinitePronoun :=
  ⟨Indefinite.IndefinitePronoun.ontology, Indefinite.IndefinitePronoun.basis,
   Indefinite.IndefinitePronoun.functions⟩
