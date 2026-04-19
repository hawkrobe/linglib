import Linglib.Theories.Phonology.Featural.Features

/-!
# Persian (Farsi) Vowel Hiatus Data @cite{storme-2026}

Empirical data for Persian vowel hiatus resolution, the case study in
@cite{storme-2026}'s MaxEnt systemic constraints analysis.

Persian has three low vowels — /æ/, /ɑ/, and (in some analyses) /ɒ/ — that
undergo various resolution strategies when they occur in hiatus (V.V across
a morpheme boundary). The key empirical observation is that hiatus resolution
is asymmetric: the pattern of deletion differs depending on which vowels are
involved, even when classical faithfulness/markedness constraints predict
symmetric behavior. Storme argues this asymmetry arises from \*HOMOPHONY
avoidance — the grammar prefers mappings that maintain output distinctness
across the paradigm.

## Segments

We define the two low vowels using the phonological feature system from
`Phonology.Features`. These are the segments relevant to hiatus
resolution; the full Persian consonant inventory is not needed.

## Hiatus domain

- `HiatusInput`: the four underlying V₁.V₂ combinations
- `HiatusOutput`: resolution strategies (V1-deletion, V2-deletion, etc.)
- `HiatusCandidate`: input–output pairs for MaxEnt evaluation
-/

open Phonology

namespace Fragments.Farsi.Phonology

-- ============================================================================
-- § 1: Persian Vowel Segments
-- ============================================================================

/-- Persian /æ/ — low front unrounded vowel.
    [+syll, −cons, +son, +approx, +cont, −nasal, −lat, +dor, +low, +front, −back, −tense] -/
def vowelAe : Segment where
  spec := fun
    | .syllabic => some true
    | .consonantal => some false
    | .sonorant => some true
    | .approximant => some true
    | .continuant => some true
    | .nasal => some false
    | .lateral => some false
    | .dorsal => some true
    | .low => some true
    | .front => some true
    | .back => some false
    | .tense => some false
    | _ => none

/-- Persian /ɑ/ — low back unrounded vowel.
    [+syll, −cons, +son, +approx, +cont, −nasal, −lat, +dor, +low, −front, +back, −tense] -/
def vowelAh : Segment where
  spec := fun
    | .syllabic => some true
    | .consonantal => some false
    | .sonorant => some true
    | .approximant => some true
    | .continuant => some true
    | .nasal => some false
    | .lateral => some false
    | .dorsal => some true
    | .low => some true
    | .front => some false
    | .back => some true
    | .tense => some false
    | _ => none

-- ============================================================================
-- § 2: Hiatus Domain
-- ============================================================================

/-- Underlying hiatus contexts: V₁.V₂ sequences across a morpheme boundary.
    We model the four pairwise combinations of /æ/ and /ɑ/.

    Naming: `ae` = /æ/ (low front), `ah` = /ɑ/ (low back). -/
inductive HiatusInput where
  | ae_ae   -- /æ.æ/
  | ae_ah   -- /æ.ɑ/
  | ah_ae   -- /ɑ.æ/
  | ah_ah   -- /ɑ.ɑ/
  deriving DecidableEq, Repr

/-- Resolution strategies for vowel hiatus. -/
inductive HiatusOutput where
  /-- Delete V₁ (first vowel). -/
  | deleteV1
  /-- Delete V₂ (second vowel). -/
  | deleteV2
  /-- Glide epenthesis (insert [j] or [w] between vowels). -/
  | epenthesis
  /-- Coalescence (merge V₁ and V₂ into a single vowel). -/
  | coalescence
  /-- Faithful (no repair — hiatus surfaces). -/
  | faithful
  deriving DecidableEq, Repr

instance : Inhabited HiatusOutput := ⟨.faithful⟩

/-- A hiatus candidate: an input–output pair for constraint evaluation. -/
abbrev HiatusCandidate := HiatusInput × HiatusOutput

/-- The candidate set for each input: all five resolution strategies. -/
def candidates (_i : HiatusInput) : List HiatusOutput :=
  [.deleteV1, .deleteV2, .epenthesis, .coalescence, .faithful]

-- ============================================================================
-- § 3: Surface Form Descriptions
-- ============================================================================

/-- Surface form description for each input–output pair.
    These are descriptive labels, not phonetic transcriptions. -/
def surfaceDescription : HiatusCandidate → String
  | (.ae_ae, .deleteV1)    => "[æ] (V1 deleted)"
  | (.ae_ae, .deleteV2)    => "[æ] (V2 deleted)"
  | (.ae_ae, .epenthesis)  => "[æjæ] (glide epenthesis)"
  | (.ae_ae, .coalescence) => "[æ] (coalescence)"
  | (.ae_ae, .faithful)    => "[æ.æ] (faithful)"
  | (.ae_ah, .deleteV1)    => "[ɑ] (V1 deleted)"
  | (.ae_ah, .deleteV2)    => "[æ] (V2 deleted)"
  | (.ae_ah, .epenthesis)  => "[æjɑ] (glide epenthesis)"
  | (.ae_ah, .coalescence) => "[ɑ] (coalescence)"
  | (.ae_ah, .faithful)    => "[æ.ɑ] (faithful)"
  | (.ah_ae, .deleteV1)    => "[æ] (V1 deleted)"
  | (.ah_ae, .deleteV2)    => "[ɑ] (V2 deleted)"
  | (.ah_ae, .epenthesis)  => "[ɑjæ] (glide epenthesis)"
  | (.ah_ae, .coalescence) => "[ɑ] (coalescence)"
  | (.ah_ae, .faithful)    => "[ɑ.æ] (faithful)"
  | (.ah_ah, .deleteV1)    => "[ɑ] (V1 deleted)"
  | (.ah_ah, .deleteV2)    => "[ɑ] (V2 deleted)"
  | (.ah_ah, .epenthesis)  => "[ɑjɑ] (glide epenthesis)"
  | (.ah_ah, .coalescence) => "[ɑ] (coalescence)"
  | (.ah_ah, .faithful)    => "[ɑ.ɑ] (faithful)"

-- ============================================================================
-- § 4: Verification
-- ============================================================================

/-- Each input has exactly 5 candidates. -/
theorem candidates_length (i : HiatusInput) : (candidates i).length = 5 := by
  cases i <;> rfl

/-- The two vowels are featurally distinct (differ in [±front] and [±back]). -/
theorem vowels_distinct : ¬(vowelAe == vowelAh) = true := by native_decide

end Fragments.Farsi.Phonology
