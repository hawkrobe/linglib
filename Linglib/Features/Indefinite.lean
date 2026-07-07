import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Linglib.Features.LicensingContext

/-!
# Indefinite series — feature taxonomy and the word-class-neutral capability
[haspelmath-1997]

The *indefinite series* is cross-categorial: a single series (English *some-*) spans pronouns
(*someone*, *something*), determiners (*some* book), and pro-adverbs (*somewhere*, *somehow*,
*sometime*). [haspelmath-1997]'s cover term "indefinite pronoun" notwithstanding, indefiniteness is
**not** inherently pronominal — the ontological category fixes the member's word class (`person`/
`thing` → pronoun, `place`/`manner`/`time` → pro-adverb, `determiner` → determiner).

This file is therefore word-class-**neutral**: the [haspelmath-1997] feature dimensions (function
coverage, ontology, morphological basis) and the `Indefinite` *capability* (`[Indefinite α]`) that
exposes them over any carrier. The capability is the indefinite analogue of mathlib's
`MonoidHomClass`-over-`MonoidHom`: a carrier-class-specific indefinite object (`IndefinitePronoun`
in `Syntax/Pronoun/Indefinite.lean`; a future `IndefiniteDeterminer` over `Semantics.Definiteness`'s
`Determiner`) supplies one `instance : Indefinite That`, and generic code reads the series data via
`[Indefinite α]`.

## Main declarations

* `Indefinite.HaspelmathFunction` — the 9 functions on [haspelmath-1997]'s implicational map, with
  the map's intrinsic adjacency / contiguity structure.
* `Indefinite.OntologicalCategory`, `Indefinite.MorphologicalBasis` — the ontology and
  derivation-strategy feature dimensions.
* `Indefinite` — the capability mixin `[Indefinite α]`: a carrier exposing the indefinite-series
  feature data (ontology / basis / function-coverage), word-class-neutral.
-/

set_option autoImplicit false

namespace Indefinite

/-! ### The implicational-map function inventory ([haspelmath-1997]) -/

/-- The 9 indefinite-series functions on [haspelmath-1997]'s
    implicational map. A single form covers a contiguous region of the map. -/
inductive HaspelmathFunction where
  /-- Function 1: Specific known. Speaker has a referent in mind. -/
  | specificKnown
  /-- Function 2: Specific unknown. Speaker presupposes a referent
      but cannot identify it. -/
  | specificUnknown
  /-- Function 3: Irrealis non-specific. No specific referent intended. -/
  | irrealis
  /-- Function 4: Polar / content question. -/
  | question
  /-- Function 5: Conditional protasis. -/
  | conditional
  /-- Function 8: Standard of comparison. -/
  | comparative
  /-- Function 6: Indirect negation (superordinate or implicit negation:
      *without*, *doubt*, *deny*). -/
  | indirectNeg
  /-- Function 7: Direct (clause-mate) negation. -/
  | directNeg
  /-- Function 9: Free choice. -/
  | freeChoice
  deriving DecidableEq, Repr, BEq

/-- All nine functions, listed in map order. -/
def HaspelmathFunction.all : List HaspelmathFunction :=
  [ .specificKnown, .specificUnknown, .irrealis, .question
  , .conditional, .indirectNeg, .directNeg, .comparative, .freeChoice ]

/-- Adjacency on [haspelmath-1997]'s implicational map (Fig. 4.4, verified
    against the book): two-dimensional, with the specificity chain feeding
    parallel question and conditional tracks.

    ```
                          (4) question —— (6) indirect neg —— (7) direct neg
                               |                |
    (1) SK — (2) SU — (3) irr <
                               |                |
                          (5) conditional — (8) comparative — (9) free choice
    ```

    Edges: 1–2, 2–3, 3–4, 3–5, 4–5, 4–6, 5–8, 6–7, 6–8, 8–9. Note direct
    negation hangs off indirect negation only, and comparative links
    conditional, indirect negation, and free choice. Crucial typological
    claim: any indefinite series covers a *contiguous* region. -/
def HaspelmathFunction.adjacent : HaspelmathFunction → List HaspelmathFunction
  | .specificKnown   => [.specificUnknown]
  | .specificUnknown => [.specificKnown, .irrealis]
  | .irrealis        => [.specificUnknown, .question, .conditional]
  | .question        => [.irrealis, .conditional, .indirectNeg]
  | .conditional     => [.irrealis, .question, .comparative]
  | .indirectNeg     => [.question, .directNeg, .comparative]
  | .directNeg       => [.indirectNeg]
  | .comparative     => [.conditional, .indirectNeg, .freeChoice]
  | .freeChoice      => [.comparative]

/-- Is `f` a downward-entailing / nonveridical context (the classical
    NPI-licensing region: question, conditional, indirect/direct negation)?
    Used by [chierchia-2006]-style polarity-item typologies to predict
    NPI distribution. -/
def HaspelmathFunction.isDE : HaspelmathFunction → Bool
  | .question | .conditional | .indirectNeg | .directNeg => true
  | _ => false

/-- Is `f` a free-choice context (comparative + freeChoice)? Comparative
    standards are universal-flavored and pattern with FC cross-linguistically
    ([haspelmath-1997]). -/
def HaspelmathFunction.isFC : HaspelmathFunction → Bool
  | .comparative | .freeChoice => true
  | _ => false

/-- The [haspelmath-1997] map function a licensing environment realizes, for
    the polarity-relevant reading of an indefinite in that environment.
    Partial: `none` for environments outside the map's function inventory
    (the Ladusaw-tradition rows `few`, `atMost`, `superlative`, `onlyFocus`,
    `tooTo`, `universalRestrictor`, `sinceTemporal`; also `nobody`,
    `beforeClause`, `adversative`, whose placement between direct and
    indirect negation is not verified against the book and is left unmapped).
    Interpretation-light judgment calls, documented: the modal, imperative,
    generic, and free-relative rows map to `freeChoice` — their
    polarity-relevant realization — although the same environments host plain
    irrealis uses of non-polarity indefinites; both comparative rows realize
    the standard-of-comparison function regardless of NPI-licensability
    (`comparativeNP` licenses no NPIs, [hoeksema-1983]). -/
def _root_.Features.LicensingContext.haspelmathFunction :
    Features.LicensingContext → Option HaspelmathFunction
  | .negation => some .directNeg
  | .withoutClause | .doubtVerb | .denyVerb => some .indirectNeg
  | .question => some .question
  | .conditionalAntecedent => some .conditional
  | .comparativeS | .comparativeNP => some .comparative
  | .modalPossibility | .modalNecessity | .imperative | .generic
  | .freeRelative => some .freeChoice
  | _ => none

/-- The licensing environments realizing a map function — the preimage of
    `Features.LicensingContext.haspelmathFunction`. Empty for the specificity
    triangle (`specificKnown`, `specificUnknown`, `irrealis`), whose
    realizations are positive or irrealis clauses outside the
    licensing-context inventory (matching the Fragment convention that an
    empty `licensingContexts` list means the item needs positive contexts). -/
def HaspelmathFunction.contexts (f : HaspelmathFunction) :
    Finset Features.LicensingContext :=
  Finset.univ.filter (·.haspelmathFunction = some f)

/-- BFS on the implicational map restricted to a given set of functions.
    Returns the set of nodes reachable from `start` through edges whose
    endpoints both lie in `funcs`. -/
def HaspelmathFunction.bfsReachable
    (funcs : List HaspelmathFunction) (start : HaspelmathFunction)
    (fuel : Nat := 10) : List HaspelmathFunction :=
  let rec go (queue visited : List HaspelmathFunction) (fuel : Nat) :
      List HaspelmathFunction :=
    match fuel, queue with
    | 0,         _       => visited
    | _,         []      => visited
    | fuel + 1, f :: rest =>
      let neighbors := f.adjacent.filter (fun g =>
        funcs.contains g && !visited.contains g)
      go (rest ++ neighbors) (visited ++ neighbors) fuel
  go [start] [start] fuel

/-- A list of functions is *contiguous* on the implicational map iff BFS
    from any element reaches all others. [haspelmath-1997]'s key
    constraint: every indefinite series must cover a contiguous region. -/
def HaspelmathFunction.isContiguous (funcs : List HaspelmathFunction) : Bool :=
  match funcs with
  | []     => true
  | f :: _ => funcs.all (HaspelmathFunction.bfsReachable funcs f 15).contains

/-! ### Ontological categories ([haspelmath-1997] §3.1.3) -/

/-- The ontological categories of the indefinite series
    ([haspelmath-1997] §3.1.3, Table 3.1). The seven core categories —
    person, thing, property, place, time, manner, amount — are the categories
    "most often expressed by simple means in the languages of the world"; the
    human/non-human cut (person vs thing, *somebody* vs *something*) is made
    practically everywhere. The category also fixes the member's word class:
    `person`/`thing` are pronouns, `place`/`time`/`manner` pro-adverbs,
    `determiner` ('which', *some N*) a determiner — `reason` ('why') is, like
    `determiner`, common but non-universal (English and German have no
    indefinite *somewhy*). -/
inductive OntologicalCategory where
  /-- Person: *somebody/someone* (interrogative *who?*). -/
  | person
  /-- Thing: *something* (interrogative *what?*). -/
  | thing
  /-- Property / kind: *some kind of* (interrogative *what kind?*). -/
  | property
  /-- Place: *somewhere* (interrogative *where?*). -/
  | place
  /-- Time: *sometime* (interrogative *when?*). -/
  | time
  /-- Manner: *somehow* (interrogative *how?*). -/
  | manner
  /-- Amount: *some amount* (interrogative *how much?*). -/
  | amount
  /-- Determiner: *some N* / 'which' — non-universal, distinct from the
      substantival 'who'/'what'. -/
  | determiner
  /-- Reason / cause: 'for some reason' (interrogative *why?*) — non-universal. -/
  | reason
  deriving DecidableEq, Repr, BEq

/-- The seven core ontological categories realized "practically everywhere"
    ([haspelmath-1997] §3.1.3); excludes the non-universal `determiner`
    and `reason`. -/
def OntologicalCategory.core : List OntologicalCategory :=
  [.person, .thing, .property, .place, .time, .manner, .amount]

/-- All nine ontological categories (the seven core plus `determiner`, `reason`). -/
def OntologicalCategory.all : List OntologicalCategory :=
  OntologicalCategory.core ++ [.determiner, .reason]

/-! ### Morphological basis ([haspelmath-1997]; = WALS F46A categories) -/

/-- [haspelmath-1997]'s four morphological strategies for deriving
    indefinite-series forms. Aligns with the four single-strategy values of
    [wals-2013] F46A; F46A's `.mixed` cell arises only at the
    paradigm level (see `IndefiniteParadigm.toWALS46A`, in `Typology/Indefinite.lean`). -/
inductive MorphologicalBasis where
  /-- Built from interrogative pronouns (`who-`, `what-`, …). -/
  | interrogative
  /-- Built from generic nouns ('person', 'thing', 'place'). -/
  | genericNoun
  /-- A dedicated indefinite morpheme. -/
  | special
  /-- An existential predication construction. -/
  | existentialConstruction
  deriving DecidableEq, Repr, BEq

end Indefinite

/-! ### The capability -/

/-- The indefinite-series capability `[Indefinite α]`: a carrier `α` exposing the
    [haspelmath-1997] series data — its ontological category, morphological basis, and the
    contiguous region of the implicational map it covers — over any word-class representation.

    Word-class-neutral by design (`Indefinite` ≠ pronoun): the sole current carrier is
    `Indefinite.IndefinitePronoun` (`Syntax/Pronoun/Indefinite.lean`), but an indefinite determiner
    (over `Semantics.Definiteness`'s `Determiner`) or pro-adverb supplies its own `instance : Indefinite That`
    and is then read by the same generic `[Indefinite α]` code. This is the indefinite analogue of
    mathlib's `MonoidHomClass`-over-`MonoidHom`/`RingHom`. -/
class Indefinite (α : Type*) where
  /-- The ontological category the carrier realizes (fixes its word class). -/
  ontology : α → Indefinite.OntologicalCategory
  /-- The morphological derivation strategy. -/
  basis : α → Indefinite.MorphologicalBasis
  /-- The implicational-map functions the carrier covers. -/
  functions : α → Finset Indefinite.HaspelmathFunction
