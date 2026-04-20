import Linglib.Theories.Phonology.Process.RuleBased.Defs
import Linglib.Fragments.English.Phonology
import Linglib.Fragments.Korean.Phonology
import Linglib.Phenomena.Phonology.Alternation

/-!
# SPE Derivation Bridge

Connects Fragment-level phonological rules to Phenomena-level alternation
data via SPE ordered derivation. For each alternation datum, defines the
underlying segment string, applies `derive` with the language's rule set,
and verifies the output matches the expected surface form.

All theorems are proved by `native_decide` (finite segment data).
-/

namespace SPEDerivations

open Phonology
open Phonology.RuleBased (derive)

-- ============================================================================
-- § 1: English Preglottalization
-- ============================================================================

section EnglishPreglottalization
open Fragments.English.Phonology

/-- Expected surface form: /t/ with [+c.g.] added. -/
def t_cg : Segment := Segment.ofSpecs
  [(Feature.syllabic, false), (Feature.consonantal, true),
   (Feature.sonorant, false), (Feature.continuant, false),
   (Feature.voice, false), (Feature.coronal, true), (Feature.anterior, true),
   (Feature.constrGlottis, true)]

/-- UR /kæt/ → derive [preglottalization] → [kætˀ].
    Word-final /t/ acquires [+c.g.]; /k/ is not word-final so is unchanged. -/
theorem preglottalization_derives :
    (derive [preglottalization] [k, æ, t] == [k, æ, t_cg]) = true := by
  native_decide

/-- The derivation output has the same length (feature change, not deletion). -/
theorem preglottalization_preserves_length :
    (derive [preglottalization] [k, æ, t]).length = 3 := by native_decide

end EnglishPreglottalization

-- ============================================================================
-- § 2: English Postnasal Deletion
-- ============================================================================

section EnglishPostnasalDeletion
open Fragments.English.Phonology

/-- UR /wɪntər/ → derive [postnasalDeletion] → [wɪnər].
    /t/ deletes between /n/ ([+nasal]) and /ə/ ([+syll]). -/
theorem postnasal_deletion_derives :
    (derive [postnasalDeletion] [w, laxI, n, t, schwa, r] == [w, laxI, n, schwa, r]) = true := by
  native_decide

/-- Deletion reduces the string by one segment. -/
theorem postnasal_deletion_reduces_length :
    (derive [postnasalDeletion] [w, laxI, n, t, schwa, r]).length = 5 := by native_decide

end EnglishPostnasalDeletion

-- ============================================================================
-- § 3: Korean Nasalization
-- ============================================================================

section KoreanNasalization
open Fragments.Korean.Phonology

/-- Expected surface form: /k/ nasalized to [+nasal, +voice, +son].
    Preserves all other features of underlying /k/. -/
def k_nasalized : Segment := Segment.ofSpecs
  [(Feature.syllabic, false), (Feature.consonantal, true),
   (Feature.sonorant, true), (Feature.continuant, false),
   (Feature.voice, true), (Feature.delayedRelease, false),
   (Feature.dorsal, true), (Feature.nasal, true)]

/-- UR /pakmul/ → derive [stopNasalization] → [paŋmul].
    /k/ at position 2 nasalizes before /m/ ([+nasal]). -/
theorem korean_nasalization_derives :
    (derive [stopNasalization] [p, a, k, m, u, l] == [p, a, k_nasalized, m, u, l]) = true := by
  native_decide

/-- Nasalization preserves string length (feature change, not deletion). -/
theorem korean_nasalization_preserves_length :
    (derive [stopNasalization] [p, a, k, m, u, l]).length = 6 := by native_decide

end KoreanNasalization

end SPEDerivations
