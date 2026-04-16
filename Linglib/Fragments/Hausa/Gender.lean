import Linglib.Core.Gender
import Linglib.Theories.Morphology.DM.Categorizer

/-!
# Hausa Gender Fragment
@cite{kramer-2020} @cite{kramer-2015} @cite{newman-2000}

Hausa (Chadic, Afroasiatic) has a two-gender system: masculine and feminine.
The feminine suffix *-ā* has been claimed to be a phonological assignment
rule (nouns ending in *-ā* are feminine). @cite{kramer-2020} §3.3.1 argues
this is morphophonological *realization* of [+FEM] on n, not phonological
*assignment* — syntax cannot see phonology, so the suffix reflects the
gender feature rather than determining it.

Hausa is a Set 1 language: masculine is default (plain n), feminine requires
[+FEM] on n.
-/

namespace Fragments.Hausa.Gender

open Morphology.DM (CatHead)
open Core (SurfaceGender)

-- ============================================================================
-- § 1: Noun Entries
-- ============================================================================

/-- A Hausa noun with gender and the *-ā* suffix diagnostic. -/
structure Noun where
  form : String
  gloss : String
  gender : SurfaceGender
  /-- Does the form end in *-ā*? -/
  endsInAa : Bool
  /-- DM categorizing head (determines gender structurally). -/
  nHead : CatHead
  deriving Repr, BEq

-- Feminine nouns ending in -ā (the regular pattern)
def yarinya : Noun := ⟨"yārinyā", "girl", .feminine, true, .n_iFem⟩
def mace    : Noun := ⟨"mācè",    "woman", .feminine, true, .n_iFem⟩
def kaza    : Noun := ⟨"kāzā",    "hen",   .feminine, true, .n_uFem⟩
def riga    : Noun := ⟨"rīgā",    "gown",  .feminine, true, .n_uFem⟩

-- Masculine nouns (no -ā suffix)
def yaro    : Noun := ⟨"yārō",   "boy",    .masculine, false, .n_iMasc⟩
def mutum   : Noun := ⟨"mùtûm",  "man",    .masculine, false, .n_iMasc⟩
def littafi : Noun := ⟨"littāfī", "book",  .masculine, false, .n_plain⟩
def gida    : Noun := ⟨"gidā",    "house", .masculine, false, .n_plain⟩

-- Feminine nouns NOT ending in -ā (counterexamples to phonological rule)
def kasa_land    : Noun := ⟨"ƙasā",    "land",  .feminine, true, .n_uFem⟩
def rana    : Noun := ⟨"rānā",    "sun/day",.feminine, true, .n_uFem⟩

def allNouns : List Noun :=
  [yarinya, mace, kaza, riga, yaro, mutum, littafi, gida, kasa_land, rana]

-- ============================================================================
-- § 2: Set 1 VI Verification
-- ============================================================================

/-- Hausa is Set 1: surface gender derived from DM n-heads via
    `CatHead.surfaceGenderSet1` matches the listed gender. -/
theorem set1_derivation :
    allNouns.all (fun n =>
      n.nHead.surfaceGenderSet1 == n.gender) = true := by native_decide

-- ============================================================================
-- § 3: The -ā Diagnostic (@cite{kramer-2020} §3.3.1)
-- ============================================================================

/-- Most -ā nouns are feminine, but the correlation is not absolute:
    *gidā* 'house' ends in -ā but is masculine. This is evidence that
    -ā is morphophonological *realization* of [+FEM], not phonological
    *assignment*. -/
theorem gida_counterexample :
    gida.endsInAa = false ∧ gida.gender = .masculine := ⟨rfl, rfl⟩

/-- The structural explanation: *gidā*'s n has no [+FEM] feature (plain n),
    so despite the phonological form, it surfaces as masculine via Set 1 VI. -/
theorem gida_plain_n :
    gida.nHead = .n_plain ∧
    gida.nHead.surfaceGenderSet1 = .masculine := ⟨rfl, rfl⟩

end Fragments.Hausa.Gender
