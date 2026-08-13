import Linglib.Data.WALS.Features.F121A
import Linglib.Features.Case.Basic

/-!
# Comparison: comparative-construction typology

The `Comparative` object — a comparative construction's anatomy in
[stassen-1985]'s parameters, with its WALS Ch 121 type ([stassen-2013],
[wals-2013]) derived from that anatomy — plus the [beck-2009] degree-word
typology, superlative strategies, and the WALS Ch 121A lookup and aggregates.

## Main definitions

- `Comparative` : the construction object (standard marker, case assignment,
  encoding role, spatial case, degree slot). Fragments instantiate one def per
  construction (`German.Comparison.als`; Latin has `quam` *and* `ablative`).
- `Comparative.type` : the WALS Ch 121 type, derived from the anatomy —
  derived-case constructions split on marker presence (particle vs conjoined),
  fixed-case constructions on encoding role (exceed vs locational).
- `DegreeWordType` ([beck-2009] 3-way), `SuperlativeStrategy` (6-way).
- `ComparativeType.ofWALS` : WALS Ch 121A comparative type by ISO 639-3
  lookup; `none` for languages the chapter leaves uncoded.
- WALS Ch 121A aggregate generalisations (`locational_most_common`,
  `particle_rarest`, `locational_and_particle_dominant`).

Stassen's 1985 fine-grained adverbial typology (`ComparativeType1985`, the
chaining universals) lives in `Studies/Stassen1985.lean` (paper-anchored).
-/

set_option autoImplicit false

open Features (CaseAssignment FixedCaseEncoding)

/-- A comparative construction: how it encodes the standard of comparison in
    "X is more Adj than Y" — [stassen-1985]'s construction parameters. A
    language may have more than one (Latin *quam* and the bare ablative).
    Coexists with `namespace Comparative` (a type and a namespace may share a
    name, cf. `Pronoun`). -/
structure Comparative where
  /-- Surface form of the standard marker (*than*, *als*, *yori*, *bǐ*);
      `none` when no segmental marker flags the standard (conjoined
      constructions, bare case-marked standards like the Latin ablative). -/
  standardMarker : Option String := none
  /-- Case assignment to the standard NP: derived from the comparee's case vs
      fixed by the construction ([stassen-1985]). -/
  caseAssignment : CaseAssignment
  /-- For fixed-case constructions: the standard's syntactic role — direct
      object of an exceed verb, or adverbial. -/
  fixedEncoding : Option FixedCaseEncoding := none
  /-- Case on an adverbially encoded standard (ablative for separatives,
      partitive for the Finnish secondary option). Adpositions with the
      corresponding semantics count (Japanese *yori*, Arabic *min* → `abl`). -/
  standardCase : Option Case := none
  /-- The construction's degree-slot filler (*more*, *-er*, *daha*), if any. -/
  degreeMarker : Option String := none
  /-- Dedicated bound degree morphology on the parameter (English *-er*,
      Latin *-ior*) — [stassen-1985]'s binary parameter. -/
  degreeMorphology : Bool := false
  deriving Repr, BEq, DecidableEq

namespace Comparative

private abbrev ch121 := Data.WALS.F121A.allData

/-! ### Classifications -/

/-- WALS Ch 121: how a comparative construction encodes the **standard of
    comparison** (the Y in "X is more Adj than Y"). A language with more than
    one productive construction has one `Comparative` object per construction,
    each with its own type. -/
inductive ComparativeType where
  /-- Locational: the standard is marked with a locational/ablative case
      or adposition. Example: Japanese `Y yori X tall` 'Y from/than X tall'.
      Also Turkish (ablative), Hindi-Urdu (`se`), Latin (ablative). -/
  | locational
  /-- Exceed: a verb meaning 'exceed/surpass' encodes comparison.
      Example: Yoruba `Ade ga ju Bola lo`. Common in Niger-Congo + SE Asian. -/
  | exceed
  /-- Conjoined: two juxtaposed clauses, one attributing the property to X
      and the other denying / contrasting it for Y. Rarest type. -/
  | conjoined
  /-- Particle: a dedicated comparative particle marks the standard
      (e.g. English `than`, German `als`). Standard Average European pattern. -/
  | particle
  deriving DecidableEq, BEq, Repr

/-- [beck-2009]: presence of degree words in comparison constructions. -/
inductive DegreeWordType where
  /-- Free degree word (English `more`, French `plus`, Mandarin `geng`). -/
  | hasDegreeWord
  /-- Bound comparative morphology, no free degree word
      (English `-er` for short adjectives, Turkish `-rak`). -/
  | morphological
  /-- No overt degree marking (exceed-verb, juxtaposition, pragmatic). -/
  | noDegreeMarking
  deriving DecidableEq, BEq, Repr

/-- How a language forms superlatives. Partially independent of comparative
    type; some languages lack a dedicated superlative entirely. -/
inductive SuperlativeStrategy where
  /-- Dedicated superlative morphology (English `-est`, Latin `-issimus`). -/
  | morphological
  /-- Definite article + comparative (French `le plus grand`). -/
  | definiteComparative
  /-- Elative pattern without comparison class (Arabic `ʔafʕal`). -/
  | elative
  /-- Exceed verb + universal quantifier ("X exceeds all"). -/
  | exceedAll
  /-- Comparative + universal standard (Japanese `dare yori mo takai`). -/
  | comparativeUniversal
  /-- No dedicated superlative strategy. -/
  | none
  deriving DecidableEq, BEq, Repr

/-! ### The derived type -/

/-- The WALS Ch 121 type of a construction, derived from its anatomy:
    derived-case constructions split on marker presence (particle vs
    conjoined); fixed-case constructions on encoding role (exceed vs
    locational, with adverbial the default). -/
def type (c : Comparative) : ComparativeType :=
  match c.caseAssignment, c.fixedEncoding with
  | .derived, _ => if c.standardMarker.isSome then .particle else .conjoined
  | .fixed, some .directObject => .exceed
  | .fixed, _ => .locational

/-! ### WALS lookups -/

/-- WALS Ch 121A → `ComparativeType`. -/
def ofWALS121A : Data.WALS.F121A.ComparativeType → ComparativeType
  | .locational => .locational
  | .exceed     => .exceed
  | .conjoined  => .conjoined
  | .particle   => .particle

/-- WALS Ch 121A comparative type for an ISO 639-3 code; `none` when the
    language is uncoded in the chapter. -/
def ComparativeType.ofWALS (iso : String) : Option ComparativeType :=
  (Data.WALS.Datapoint.lookupISO ch121 iso).map (ofWALS121A ·.value)

/-! ### WALS Ch 121A aggregate generalisations -/

/-- Per-type counts sum to sample total. -/
theorem ch121_counts_sum :
    (ch121.filter (·.value == .locational)).length +
    (ch121.filter (·.value == .exceed)).length +
    (ch121.filter (·.value == .conjoined)).length +
    (ch121.filter (·.value == .particle)).length =
    ch121.length := by native_decide

/-- Locational comparatives are the most common single type in WALS Ch 121. -/
theorem locational_most_common :
    let loc := (ch121.filter (·.value == .locational)).length
    let exc := (ch121.filter (·.value == .exceed)).length
    let con := (ch121.filter (·.value == .conjoined)).length
    let par := (ch121.filter (·.value == .particle)).length
    loc > exc ∧ loc > con ∧ loc > par := by native_decide

/-- Particle comparatives are the rarest single type in the WALS data. -/
theorem particle_rarest :
    let loc := (ch121.filter (·.value == .locational)).length
    let exc := (ch121.filter (·.value == .exceed)).length
    let con := (ch121.filter (·.value == .conjoined)).length
    let par := (ch121.filter (·.value == .particle)).length
    par < loc ∧ par < exc ∧ par < con := by native_decide

/-- Locational + particle together account for more than half the sample. -/
theorem locational_and_particle_dominant :
    let loc := (ch121.filter (·.value == .locational)).length
    let par := (ch121.filter (·.value == .particle)).length
    loc + par > ch121.length / 2 := by native_decide

end Comparative
