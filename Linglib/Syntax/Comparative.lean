import Linglib.Data.WALS.Features.F121A
import Linglib.Features.Case.Basic

/-!
# Comparison: comparative-construction typology

Per-language typological substrate for comparative-construction typology:
[stassen-2013]'s WALS Ch 121 framework ([wals-2013]), the [beck-2009]
degree-word typology, and superlative strategies. Fragment-importable.

## Main definitions

- `ComparativeType` (5-way Stassen 2013 / WALS Ch 121A:
  `locational | exceed | conjoined | particle | mixed`).
- `DegreeWordType` ([beck-2009] 3-way:
  `hasDegreeWord | morphological | noDegreeMarking`).
- `SuperlativeStrategy` (6-way: morphological, definiteComparative, elative,
  exceedAll, comparativeUniversal, none).
- `ComparativeType.ofWALS` : WALS Ch 121A comparative type by ISO 639-3 lookup
  (via the `ofWALS121A` converter); `none` for languages the chapter leaves
  uncoded.
- WALS Ch 121A aggregate generalisations (`locational_most_common`,
  `particle_rarest`, `locational_and_particle_dominant`).
- `ComparativeEntry` : [stassen-1985]'s construction parameters.

There is no per-language bundle: Fragments export bare defs typed by these
enums (`{Lang}.Comparison.degreeWord`, `superlative`, `standardMarker`, …, plus
`comparativeType` only for languages uncoded in WALS Ch 121A); studies join
them with the WALS lookups.

## Theory-laden caveats

- **`ComparativeType` is the WALS 2013 5-way typology.** Stassen's original
  1985 6-way typology (`separative | allative | locative | exceed |
  conjoined | particle`) lives in `Studies/Stassen1985.lean`
  because the 3-way adverbial split is paper-distinctive — the WALS update
  collapses it into a single `locational` for cross-linguistic indexing.
- **`DegreeWordType` is Beck et al. 2009's three-way classification.** Other
  approaches (Kennedy 1999, Beck 2011, Bochnak 2013) refine the typology with
  scale-structure and degree-argument parameters; those live in
  `Semantics/Degree/`.

## Out of scope

Stassen's 1985 fine-grained adverbial typology (`ComparativeType1985`,
`caseAssignment`, `fixedEncoding`, `spatialCase`) and the 1985-↔-2013
consistency theorems live in `Studies/Stassen1985.lean` (paper-anchored).
-/

set_option autoImplicit false

namespace Comparative

private abbrev ch121 := Data.WALS.F121A.allData

/-! ### Classifications -/

/-- WALS Ch 121: how a language expresses comparison of inequality.

    Stassen's classification is based on how the **standard of comparison**
    (the Y in "X is more Adj than Y") is encoded. Five types are
    cross-cutting; a single language may use more than one productively
    (classified as "mixed"). -/
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
  /-- Mixed: more than one type is productive without a clear dominant. -/
  | mixed
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

/-! ### WALS lookups -/

/-- WALS Ch 121A → `ComparativeType`. The generated WALS data uses four
    categories; `mixed` is not a separate WALS value (languages are assigned
    to whichever single type best characterises them). -/
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

/-! ### Stassen 1985 — Comparative Entry [stassen-1985]

A typed record for the parameters of a comparative construction in a
particular language: standard case, how that case is assigned, optional
fixed-encoding role, the standard marker (e.g., *than*, *より*), and
whether the construction has dedicated degree morphology. -/

open Features (CaseAssignment FixedCaseEncoding)

/-- A language's comparative construction entry ([stassen-1985]). -/
structure ComparativeEntry where
  standardCase : Case
  caseAssignment : CaseAssignment
  fixedEncoding : Option FixedCaseEncoding
  standardMarker : String
  hasDegreeMorphology : Bool
  deriving Repr, BEq

end Comparative
