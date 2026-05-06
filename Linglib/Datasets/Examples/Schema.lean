/-!
# `LinguisticExample` schema

Substrate types for typed linguistic example data, aligned with the CLDF
Examples component (Cross-Linguistic Data Formats; Forkel, List, Greenhill,
Bank, et al. — DLCE/MPI-EVA).

Per-paper example data lives in `Linglib/Studies/{Phenom}/{AuthorYear}.lean`,
inside a `namespace Examples ... end` block delimited by marker comments and
auto-generated from `Datasets/Examples/{AuthorYear}.csv` by
`scripts/gen_examples.py`. Each `LinguisticExample` carries a stable ID
mirroring the source paper's example numbering, plus Leipzig-style gloss and
provenance via `SourceRef`.

This schema is the substrate; it does not import anything from `Linglib/`.
Consumers (Phenomena/, Studies/) import it. Per CLAUDE.md, `Datasets/` is
substrate alongside `Core/`, `Features/`, etc.

## Leipzig glossing conventions

The gloss component of `glossedTokens` follows the Leipzig Glossing Rules
(Comrie, Haspelmath, & Bickel 2008):
- `-` separates affixes from stems and one another (segmentable morpheme
  boundary)
- `.` separates two glosses corresponding to one form (fusion / portmanteau)
- `=` separates clitics from hosts

Token-gloss alignment is structural: `glossedTokens : List (String × String)`
pairs each analyzed-word token with its gloss directly, eliminating the
class of CSV regressions where the two parallel lists drift out of length.
Helpers `surfaceTokens` and `glossLine` recover each component when needed.

## Out of scope (for now)

The `LinguisticExample` schema as committed handles single-sentence felicity
data with morpheme-aligned gloss. It does NOT yet model:
- Multi-sentence discourse contexts (anaphora resolution, modal subordination)
- Multiple LFs per surface form (scope ambiguity, reconstruction)
- Structural / tree-based examples (where the bracketing is the data)
- Minimal-pair clusters (paradigms that only mean something together)
- Gradient acceptability beyond the 5-level enum

These extensions land when a consuming study needs them; the schema can
grow optional fields without breaking existing rows.
-/

namespace Datasets.Examples

/-- Glottolog 5.0 language identifier (e.g. "stan1293" for Standard English).
    Type alias only; values are not validated against Glottolog at the type
    level. Matches the convention in `Datasets.PHOIBLE.Inventory.glottocode`
    and `Datasets.WALS.Datapoint.iso`. -/
abbrev Glottocode := String

/-- Acceptability / felicity judgment scale. Five levels matching the
    Schütze/Sprouse standard (✓, ?, ??, ?*/* boundary, *).

    Star-character constructors (`*`, `?`) are avoided because `*` is a Lean
    reserved token and `?` collides with tactic syntax. The named cases below
    cover the same judgment scale unambiguously.

    Use `.acceptable` for clean grammatical/felicitous data; reserve
    `.ungrammatical` for hard star judgments and `.unacceptable` for
    pragmatic/felicity-failed data that isn't strictly ungrammatical.

    Constructor order encodes "worse" (`.acceptable` is best, `.ungrammatical`
    worst); the derived `Ord` makes "this paper rates X worse than Y"
    theorems possible without an extra wrapper. -/
inductive Judgment where
  | acceptable      -- ✓
  | marginal        -- ?
  | questionable    -- ??
  | unacceptable    -- ?* (pragmatic/felicity failure short of ungrammaticality)
  | ungrammatical   -- *
  deriving DecidableEq, BEq, Repr, Inhabited, Ord

/-- Reference to a published source for an example. Two fields kept separate
    rather than concatenated so each can be grepped independently:
    `bibkey` matches an entry in `blog/data/references.bib`; `paperLabel`
    is the source paper's own example numbering (e.g. "(58a)", "ex 12",
    "donkey-classic"). The CLDF convention encodes both as a single string
    `"bibkey[label]"`; we use a struct here because typed Lean rewards
    structural decomposition. -/
structure SourceRef where
  bibkey     : String
  paperLabel : String
  deriving DecidableEq, Repr

/-- A single linguistic example with surface form, gloss, judgment, and
    provenance. CLDF-aligned core fields with two optional CLDF fields
    (`metaLanguage`, `lgrConformance`) carrying their CLDF defaults.

    The `id` field is the canonical reference for theorems: a study file
    proving `theorem T_predicts_kratzer1991_58a` makes the example ID part
    of the public record, grep-able across the codebase.

    Field semantics:
    - `id`: stable, paper-keyed identifier (e.g. "charlow2014_donkey1").
    - `source`: `bibkey` + `paperLabel` for citation provenance.
    - `language`: Glottocode of the example's object language.
    - `primaryText`: surface string in the object language.
    - `glossedTokens`: list of `(analyzed-word, gloss)` pairs. The pair-list
      shape makes alignment by-construction — no `isAligned` predicate is
      needed because misalignment is unrepresentable.
    - `translation`: minimal English (or `metaLanguage`) translation.
    - `context`: discourse / scenario context where the judgment holds.
      Empty string means context-free judgment (rare; most felicity
      judgments are context-relative).
    - `judgment`: acceptability/felicity per the `Judgment` scale.
    - `comment`: free-form notes (analyst caveats, alternative readings).
    - `metaLanguage`: CLDF field; defaults to "stan1293" (English).
    - `lgrConformance`: CLDF field; "" / "WORD_ALIGNED" / "MORPHEME_ALIGNED".
    -/
structure LinguisticExample where
  id              : String
  source          : SourceRef
  language        : Glottocode
  primaryText     : String
  glossedTokens   : List (String × String)
  translation     : String
  context         : String
  judgment        : Judgment
  comment         : String
  metaLanguage    : Glottocode := "stan1293"
  lgrConformance  : String := ""
  deriving DecidableEq, Repr

namespace LinguisticExample

/-- Surface-form tokens (analyzed-word side of `glossedTokens`). -/
def surfaceTokens (e : LinguisticExample) : List String :=
  e.glossedTokens.map Prod.fst

/-- Gloss tokens (Leipzig-conventions side of `glossedTokens`). -/
def glossLine (e : LinguisticExample) : List String :=
  e.glossedTokens.map Prod.snd

end LinguisticExample

end Datasets.Examples
