import Linglib.Core.Gender
import Linglib.Theories.Morphology.DM.Categorizer

/-!
# Hausa Gender Fragment — mathlib-style
@cite{kramer-2020} @cite{kramer-2015} @cite{newman-2000}

Hausa (Chadic, Afroasiatic) has a two-gender system: masculine and
feminine. The feminine suffix *-ā* has been claimed to be a
phonological assignment rule (nouns ending in *-ā* are feminine).
@cite{kramer-2020} §3.3.1 argues this is morphophonological
*realization* of [+FEM] on n, not phonological *assignment* — syntax
cannot see phonology, so the suffix reflects the gender feature rather
than determining it.

Hausa is a Set 1 language: masculine is default (plain n), feminine
requires [+FEM] on n.

## Architectural shape

Per the project's "encoding conclusions as definitions" anti-pattern,
we *derive* both the surface gender and the *-ā* suffix diagnostic
from primitive fields rather than stipulating them:

- `Noun.gender = nHead.surfaceGenderSet1` — the Set 1 VI gives the
  surface gender as a function of the DM categorizing head.
- `Noun.EndsInAa = form.endsWith "ā" = true` — a propositional
  string-suffix predicate.

The previous version stipulated both as fields and had `theorem`s
checking consistency. With derivation, those theorems become vacuous;
in exchange, the data cannot drift from the diagnostic. The key
empirical theorem (the structural counterexample to the phonological
rule) becomes a *negative* claim: "ends in -ā" does not entail
"feminine".
-/

namespace Fragments.Hausa.Gender

open Morphology.DM (CatHead)
open Core (SurfaceGender)

-- ============================================================================
-- § 1: Noun Entries
-- ============================================================================

/-- A Hausa noun: surface form, gloss, and the DM categorizing head
    that structurally determines its gender. Both the surface gender
    and the *-ā* diagnostic are *derived*, not stored. -/
structure Noun where
  form  : String
  gloss : String
  /-- DM categorizing head; structurally determines gender via the
      Set 1 VI rule `surfaceGenderSet1`. -/
  nHead : CatHead

namespace Noun

/-- The noun's surface gender, derived from its categorizing head via
    the Set 1 VI rule. The derivation makes Hausa's gender system
    structurally explained rather than stipulated. -/
def gender (n : Noun) : SurfaceGender := n.nHead.surfaceGenderSet1

/-- The *-ā* suffix diagnostic: does the last character of the surface
    form equal *ā*? Propositional predicate; we work on the underlying
    character list (`String.toList`) rather than `String.endsWith`
    because the latter does not reduce in the kernel. -/
def EndsInAa (n : Noun) : Prop :=
  n.form.toList.getLast? = some 'ā'

instance (n : Noun) : Decidable n.EndsInAa :=
  inferInstanceAs (Decidable (_ = _))

end Noun

-- Concrete entries: only `form`, `gloss`, `nHead` are stipulated;
-- `gender` and `EndsInAa` are *derived* from these.

def yarinya  : Noun := ⟨"yārinyā", "girl",    .n_iFem⟩
def mace     : Noun := ⟨"mācè",    "woman",   .n_iFem⟩
def kaza     : Noun := ⟨"kāzā",    "hen",     .n_uFem⟩
def riga     : Noun := ⟨"rīgā",    "gown",    .n_uFem⟩
def yaro     : Noun := ⟨"yārō",    "boy",     .n_iMasc⟩
def mutum    : Noun := ⟨"mùtûm",   "man",     .n_iMasc⟩
def littafi  : Noun := ⟨"littāfī", "book",    .n_plain⟩
def gida     : Noun := ⟨"gidā",    "house",   .n_plain⟩
def kasa_land : Noun := ⟨"ƙasā",   "land",    .n_uFem⟩
def rana     : Noun := ⟨"rānā",    "sun/day", .n_uFem⟩

def allNouns : List Noun :=
  [yarinya, mace, kaza, riga, yaro, mutum, littafi, gida, kasa_land, rana]

-- ============================================================================
-- § 2: The -ā Diagnostic (@cite{kramer-2020} §3.3.1)
-- ============================================================================

/-- **Phonological-assignment hypothesis is FALSE.** If the *-ā* suffix
    *assigned* [+FEM] phonologically, then every *-ā* noun would be
    feminine. The masculine noun *gidā* 'house' falsifies this: it
    ends in *-ā* but is masculine. The structural account explains
    this correctly: *gidā*'s n is `n_plain` (no [+FEM] feature), so it
    surfaces as masculine via Set 1 VI regardless of the phonological
    form. -/
theorem phonological_assignment_false :
    ∃ n ∈ allNouns, n.EndsInAa ∧ n.gender = .masculine := by
  refine ⟨gida, ?_, ?_, ?_⟩
  · simp [allNouns]
  · decide
  · decide

/-- **Converse hypothesis ("feminine → ends in -ā") is also FALSE.**
    The feminine noun *mācè* 'woman' is feminine but ends in *-è*, not
    *-ā*. So the phonological rule fails in *both* directions: the
    surface form *-ā* neither necessitates nor is necessitated by
    feminine gender. -/
theorem feminine_does_not_imply_endsInAa :
    ∃ n ∈ allNouns, n.gender = .feminine ∧ ¬ n.EndsInAa := by
  refine ⟨mace, ?_, ?_, ?_⟩
  · simp [allNouns]
  · decide
  · decide

/-- **The structural explanation for the gidā counterexample.** Its
    categorizing head is `n_plain` (no [+FEM]); since `Noun.gender`
    is defined as `nHead.surfaceGenderSet1`, masculine follows
    structurally rather than from phonology. -/
theorem gida_structural_explanation :
    gida.nHead = .n_plain ∧ gida.gender = .masculine := ⟨rfl, rfl⟩

end Fragments.Hausa.Gender
