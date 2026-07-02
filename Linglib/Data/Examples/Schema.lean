import Linglib.Features.Acceptability

/-!
# `LinguisticExample` schema

Substrate types for typed linguistic example data, aligned with the CLDF
Examples component (Cross-Linguistic Data Formats; Forkel, List, Greenhill,
Bank, et al. — DLCE/MPI-EVA).

Per-paper example data lives in `Linglib/Studies/{Phenom}/{AuthorYear}.lean`,
inside a `namespace Examples ... end` block delimited by marker comments and
auto-generated from `Data/Examples/{AuthorYear}.json` by
`scripts/gen_examples.py`. Each `LinguisticExample` carries a stable ID
mirroring the source paper's example numbering, plus Leipzig-style gloss and
provenance via `SourceRef`.

This schema is the substrate; it does not import anything from `Linglib/`.
Consumers (Phenomena/, Studies/) import it. Per CLAUDE.md, `Data/` is
substrate alongside `Core/`, `Features/`, etc.

## Leipzig glossing conventions

The gloss component of `glossedTokens` follows the Leipzig Glossing Rules
(Comrie, Haspelmath, & Bickel 2008; spec at
<https://www.eva.mpg.de/lingua/pdf/Glossing-Rules.pdf>):
- `-` separates affixes from stems and one another (segmentable morpheme
  boundary)
- `.` separates two glosses corresponding to one form (fusion / portmanteau)
- `=` separates clitics from hosts
- SMALL CAPS for grammatical category labels (e.g., `INDEF`, `3SG`, `PST`,
  `REL`, `NOM`); plain lowercase for lexical glosses (e.g., `farmer`, `dog`)
- `1`/`2`/`3` for person; `SG`/`DU`/`PL` for number; gender labels
  (`M`/`F`/`N`) when relevant; case labels (`NOM`/`ACC`/`GEN`/...)

Token-gloss alignment is structural: `glossedTokens : List (String × String)`
pairs each analyzed-word token with its gloss directly, eliminating the
class of JSON regressions where the two parallel lists drift out of length.
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

namespace Data.Examples

open Features (Judgment)

/-- Glottolog 5.0 language identifier (e.g. "stan1293" for Standard English).
    Type alias only; values are not validated against Glottolog at the type
    level. Matches the convention in `Data.PHOIBLE.Inventory.glottocode`
    and `Data.WALS.Datapoint.iso`. -/
abbrev Glottocode := String

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
    - `source`: `bibkey` + `paperLabel` of the **originating** paper —
      where the example was first introduced or attested. For most
      examples cited in subsequent literature, `source` records the
      original (e.g. Geach 1962 for the canonical donkey sentence).
    - `reportedIn`: optional second `SourceRef` of the paper whose
      JSON file this example sits in, *when that paper is not the
      originating source*. `none` means the JSON's owning paper is also
      the originator. Use case: Schwarz 2013 cites Ebert 1971a's
      Fering example (8); the JSON row records `source = ebert-1971a`,
      `reportedIn = some ⟨schwarz-2013, "(8)"⟩`.
    - `language`: Glottocode of the example's object language.
    - `primaryText`: surface string in the object language. For
      multi-sentence discourse examples, this is the concatenation of
      `discourseSegments` (or empty if `discourseSegments` is non-empty
      and you prefer to read the segments directly).
    - `discourseSegments`: list of utterance-level segments for
      multi-sentence examples (anaphora resolution, ellipsis, modal
      subordination, donkey discourses). Empty list `[]` means
      "single-sentence example; use `primaryText`". Non-empty list
      breaks the discourse into named utterances; the order is the
      utterance order. Hofmann 2025's `(antecedentSentence, anaphorSentence)`
      pattern is the canonical case.
    - `glossedTokens`: list of `(analyzed-word, gloss)` pairs. The pair-list
      shape makes alignment by-construction — no `isAligned` predicate is
      needed because misalignment is unrepresentable. Spans the full
      `primaryText` (or full discourse if multi-sentence).
    - `translation`: minimal English (or `metaLanguage`) translation.
    - `context`: discourse / scenario context where the judgment holds.
      Empty string means context-free judgment (rare; most felicity
      judgments are context-relative).
    - `judgment`: acceptability/felicity of `primaryText` per the
      `Judgment` scale. **Sentence-level**, not reading-level.
    - `alternatives`: list of `(form, judgment)` pairs for **within-example
      contrast pairs** — competing surface forms that could fill the
      same slot, each with its own judgment. Empty `[]` means "no
      alternatives recorded". Schwarz's "#vom / **von dem Buch**" pattern
      is the canonical case: `primaryText` carries the felicitous form;
      `alternatives` carries the infelicitous variants. Each `form` is a
      full alternative `primaryText` (whole sentence with substitution),
      not just the substituted phrase, so it's interpretable in
      isolation.
    - `readings`: list of `(name, judgment)` pairs for **multiple LFs /
      interpretations** of the same `primaryText`. Empty `[]` means
      "no reading-level annotations" (the example is unambiguous or
      the analyst doesn't distinguish readings). Donkey examples
      (`("strong/universal", .acceptable), ("weak/existential", .acceptable)`)
      and scope-ambiguous examples are the canonical cases. Sentence
      acceptability (`judgment`) is independent of reading availability:
      a sentence can be `.acceptable` and still have one of two readings
      blocked.
    - `paperFeatures`: list of `(key, value)` pairs for **paper-specific
      analytical classifications** of this example. This is the bottom
      layer of the paper-relativized claim model: a typological survey
      with a feature inventory (`tam`, `ET_ST`, `evidence_type`, etc.)
      attaches its classifications here as flat strings. The future
      richer form will be `classifications : List (SourceRef × String ×
      String)` carrying *which paper's framework the classification is
      under*; for now the JSON-owning paper's framework is assumed
      implicit. Empty `[]` means "no paper-specific tags". Different
      papers can use orthogonal feature sets; consumers project out
      whatever they need.
    - `comment`: free-form notes (analyst caveats, methodological notes).
    - `metaLanguage`: CLDF field; defaults to "stan1293" (English).
    - `lgrConformance`: CLDF field; "" / "WORD_ALIGNED" / "MORPHEME_ALIGNED".
    -/
structure LinguisticExample where
  id                : String
  source            : SourceRef
  reportedIn        : Option SourceRef := none
  language          : Glottocode
  primaryText       : String
  discourseSegments : List String := []
  glossedTokens     : List (String × String)
  translation       : String
  context           : String
  judgment          : Judgment
  alternatives      : List (String × Judgment) := []
  readings          : List (String × Judgment) := []
  paperFeatures     : List (String × String) := []
  comment           : String
  metaLanguage      : Glottocode := "stan1293"
  lgrConformance    : String := ""
  deriving DecidableEq, Repr

namespace LinguisticExample

/-- Surface-form tokens (analyzed-word side of `glossedTokens`). -/
def surfaceTokens (e : LinguisticExample) : List String :=
  e.glossedTokens.map Prod.fst

/-- Gloss tokens (Leipzig-conventions side of `glossedTokens`). -/
def glossLine (e : LinguisticExample) : List String :=
  e.glossedTokens.map Prod.snd

/-- Value of a `paperFeatures` key, if present. -/
def feature? (e : LinguisticExample) (key : String) : Option String :=
  e.paperFeatures.lookup key

end LinguisticExample

end Data.Examples
