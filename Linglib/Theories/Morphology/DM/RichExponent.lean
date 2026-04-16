import Linglib.Theories.Morphology.DM.VocabularyInsertion
import Linglib.Theories.Phonology.Syllable.Foot

/-!
# Rich Phonological Representations for Vocabulary Insertion
@cite{alderete-1999} @cite{koehnlein-cameron-2024}

Standard Distributed Morphology assumes that Vocabulary Items specify
only segmental exponents (strings). However, a growing body of work
argues that exponents can carry **lexical prespecification** of
suprasegmental properties: stress, metrical structure, tone, etc.

## Motivation

@cite{aitha-2026} argues that Telugu singular *-ni* is prespecified
for stress. This prespecification interacts with the phonological
grammar (Stratal OT) to produce the weak alternation: stressed *-ni*
cannot form a well-formed binary foot when PrWd-final, triggering
its deletion. Without prespecification, the alternation would require
a morpheme-specific phonological rule — exactly the kind of ad hoc
device that modular DM aims to avoid.

## Architecture

`RichExponent` extends the bare `String` exponent with an optional
`ProsodicPrespec` field. `RichVocabItem` is a version of `VocabItem`
that uses `RichExponent` instead of `String`.

The key insight: rich representations are **not** stipulations of
surface behavior. They are underlying specifications that interact
with general phonological constraints. The surface pattern is
*derived* from the interaction, not encoded in the representation.

## Precedents

- @cite{alderete-1999}: Lexical prespecification of stress (English
  stress-shifting suffixes like *-ity*, *-ic*)
- @cite{koehnlein-cameron-2024}: Foot structure as a lexical property
  (motivating syllable-internal prosodic oppositions)
- @cite{moren-zsiga-2006}: Lexical tone in Thai
-/

namespace Theories.Morphology.DM.RichRepresentation

open Phonology.Syllable
open Theories.Morphology.DM.VI

-- ============================================================================
-- § 1: Prosodic Prespecification
-- ============================================================================

/-- Prosodic prespecification for a morphological exponent.

    An exponent may be **lexically specified** for suprasegmental
    properties that interact with the phonological grammar. These
    specifications are part of the underlying representation (List 2
    in DM's architecture) and persist through phonological computation
    unless overridden by higher-ranked constraints.

    Fields are optional: `none` means the property is unspecified
    (determined by the phonological grammar alone). -/
structure ProsodicPrespec where
  /-- Inherent stress: `some true` = the exponent bears lexical stress;
      `some false` = the exponent is lexically unstressed;
      `none` = stress assignment is left to the phonological grammar.

      Example: Telugu singular *-ni* is `some true` — it enters the
      phonology with a prespecified stress that interacts with FT-BIN
      and IDENT-STRESS (@cite{aitha-2026} §5). -/
  inherentStress : Option Bool := none
  /-- Preferred foot type, if any. Relevant for exponents that impose
      metrical requirements (e.g., stress-shifting suffixes in English
      that require a specific foot structure).

      Example: English *-ity* requires a trochaic foot on the preceding
      syllable (@cite{alderete-1999}). -/
  preferredFoot : Option FootType := none
  deriving DecidableEq, Repr

instance : Inhabited ProsodicPrespec := ⟨{}⟩

/-- Is this exponent prosodically inert (no prespecification)? -/
def ProsodicPrespec.isInert (p : ProsodicPrespec) : Bool :=
  p.inherentStress.isNone && p.preferredFoot.isNone

-- ============================================================================
-- § 2: Rich Exponent
-- ============================================================================

/-- A rich exponent: segmental content plus optional prosodic
    prespecification.

    This replaces the bare `String` in `VocabItem` for analyses where
    morpheme-specific prosodic properties are needed. The segmental
    content and prosodic specification are independent: a morpheme
    can have rich prosody with simple segments, or complex segments
    with no prosodic specification. -/
structure RichExponent where
  /-- Segmental content (the traditional "exponent"). -/
  segments : String
  /-- Prosodic prespecification (empty = prosodically inert). -/
  prosody : ProsodicPrespec := {}
  deriving DecidableEq, Repr

/-- Create a prosodically inert exponent (equivalent to a bare string). -/
def RichExponent.bare (s : String) : RichExponent :=
  ⟨s, {}⟩

/-- Create a stressed exponent. -/
def RichExponent.stressed (s : String) : RichExponent :=
  ⟨s, { inherentStress := some true }⟩

/-- Create an unstressed exponent. -/
def RichExponent.unstressed (s : String) : RichExponent :=
  ⟨s, { inherentStress := some false }⟩

-- ============================================================================
-- § 3: Rich Vocabulary Item
-- ============================================================================

/-- A Vocabulary Item with rich phonological representation.

    Identical to `VocabItem` except that `exponent` is a `RichExponent`
    rather than a bare `String`. The `contextMatch`, `rootMatch`, and
    `specificity` fields work exactly as in `VocabItem`. -/
structure RichVocabItem (Ctx Root : Type) where
  /-- The phonological exponent with optional prosodic prespecification. -/
  exponent : RichExponent
  /-- Context check: does the terminal's feature bundle match? -/
  contextMatch : Ctx → Bool
  /-- Root restriction (optional). -/
  rootMatch : Option (Root → Bool) := none
  /-- Specificity for Elsewhere Condition resolution. -/
  specificity : Nat := 0

/-- Does a Rich Vocabulary Item match at a given terminal node? -/
def RichVocabItem.matches {Ctx Root : Type}
    (vi : RichVocabItem Ctx Root) (ctx : Ctx) (root : Root) : Bool :=
  vi.contextMatch ctx &&
  match vi.rootMatch with
  | none => true
  | some f => f root

/-- Insert a Rich Vocabulary Item: same Elsewhere Condition logic as
    `vocabularyInsert`, but returns a `RichExponent`. -/
def richVocabularyInsert {Ctx Root : Type}
    (rules : List (RichVocabItem Ctx Root))
    (ctx : Ctx) (root : Root) : Option RichExponent :=
  let sorted := rules.mergeSort (λ a b => a.specificity ≥ b.specificity)
  sorted.findSome? λ vi =>
    if vi.matches ctx root then some vi.exponent else none

-- ============================================================================
-- § 4: Bridge to Standard VocabItem
-- ============================================================================

/-- Convert a standard `VocabItem` to a `RichVocabItem` with inert
    prosody. All existing VI rules are automatically prosodically inert. -/
def VocabItem.toRich {Ctx Root : Type}
    (vi : VocabItem Ctx Root) : RichVocabItem Ctx Root :=
  { exponent := .bare vi.exponent
  , contextMatch := vi.contextMatch
  , rootMatch := vi.rootMatch
  , specificity := vi.specificity }

-- ============================================================================
-- § 5: Verification
-- ============================================================================

/-- A bare exponent is prosodically inert. -/
theorem bare_is_inert (s : String) :
    (RichExponent.bare s).prosody.isInert = true := rfl

/-- A stressed exponent is not prosodically inert. -/
theorem stressed_not_inert (s : String) :
    (RichExponent.stressed s).prosody.isInert = false := rfl

/-- Telugu singular *-ni*: stressed exponent. -/
def teluguSgNi : RichExponent := .stressed "ni"

theorem telugu_sg_ni_stressed :
    teluguSgNi.prosody.inherentStress = some true := rfl

/-- Telugu *n*-exponent *-am*: prosodically inert (no prespecification). -/
def teluguNAm : RichExponent := .bare "am"

theorem telugu_n_am_inert :
    teluguNAm.prosody.isInert = true := rfl

end Theories.Morphology.DM.RichRepresentation
