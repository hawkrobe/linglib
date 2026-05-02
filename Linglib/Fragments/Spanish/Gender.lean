import Linglib.Features.Gender
import Linglib.Typology.Gender

/-!
# Spanish Noun Gender
@cite{butt-benjamin-2019} @cite{kramer-2015} @cite{kramer-2020}
@cite{harris-1991}

Spanish has two genders, masculine and feminine
(@cite{butt-benjamin-2019} §1.1). Per @cite{butt-benjamin-2019} §1.2,
Group A: nouns referring to humans + a few well-known animals get
natural gender; per §1.3, Group B (lifeless things, plants, other
animals) get arbitrary gender. Per §1.2.11, a small set of common-gender
nouns (e.g. *persona*, *víctima*, *ángel*) take fixed gender regardless
of referent.

## Theory-neutral data layer

The Fragment carries two empirical fields per entry:

- `attestedGender : SurfaceGender` — the agreement-trigger fact
  (verified against @cite{butt-benjamin-2019} §1.2-1.3).
- `isNaturalGender : Bool` — whether the gender is semantically
  motivated by the referent's biological sex. False for inanimates,
  for non-natural-gender animals (cf. §1.3.1), and for the §1.2.11
  fixed-gender common-gender exceptions (*persona*, *ángel*).

These two fields suffice to project every entry's structural analysis
under @cite{kramer-2015} Ch. 6's Set-1 DM categorizer (the projection
lives in `Phenomena/Gender/Studies/Kramer2020.lean`); they also support
@cite{harris-1991}'s lexical-rule analysis directly (Harris's [FEMALE]
and [HUMAN] features map onto `attestedGender` and the natural-gender
inference).

## Per-entry verification

Entries explicitly named in @cite{kramer-2015}: *hombre*, *mujer*,
*niño*, *niña*, *mesa*, *cama*, *persona*, *libro*, *soldado*,
*estudiante*, *artista*. Other entries (*rey/reina/gato/gata,
silla/casa/puerta/ventana, zapato/coche/árbol/cielo/vaso, ángel*) are
extrapolations from Kramer's framework, anchored on the
textbook-consensus genders documented in @cite{butt-benjamin-2019}.
-/

namespace Fragments.Spanish.Gender

open Features (SurfaceGender)

-- ============================================================================
-- § 1: Spanish Noun (theory-neutral schema)
-- ============================================================================

/-- A Spanish noun. No commitment to any specific theoretical framework
    — Kramer's DM categorizing head, Harris's lexical rule, etc. are
    projections that live in `Studies/`. -/
structure SpanishNoun where
  form : String
  gloss : String
  /-- Empirical agreement-trigger fact (@cite{butt-benjamin-2019}). -/
  attestedGender : SurfaceGender
  /-- True iff the gender is semantically motivated by the referent's
      biological sex. False for inanimates, for non-natural-gender
      animals, and for the @cite{butt-benjamin-2019} §1.2.11 common-gender
      fixed-assignment exceptions (*persona* feminine for any sex;
      *ángel* masculine for any sex). -/
  isNaturalGender : Bool
  deriving DecidableEq, Repr

namespace SpanishNoun

/-- Surface gender alias for ergonomic consumer access. -/
abbrev gender (n : SpanishNoun) : SurfaceGender := n.attestedGender

end SpanishNoun

-- ============================================================================
-- § 2: Natural-Gender Nouns (Group A, @cite{butt-benjamin-2019} §1.2)
-- ============================================================================

def hombre : SpanishNoun := ⟨"hombre", "man",    .masculine, true⟩
def mujer  : SpanishNoun := ⟨"mujer",  "woman",  .feminine,  true⟩
def niño   : SpanishNoun := ⟨"niño",   "boy",    .masculine, true⟩
def niña   : SpanishNoun := ⟨"niña",   "girl",   .feminine,  true⟩
def rey    : SpanishNoun := ⟨"rey",    "king",   .masculine, true⟩
def reina  : SpanishNoun := ⟨"reina",  "queen",  .feminine,  true⟩
def gato   : SpanishNoun := ⟨"gato",   "cat.M",  .masculine, true⟩
def gata   : SpanishNoun := ⟨"gata",   "cat.F",  .feminine,  true⟩

-- ============================================================================
-- § 3: Arbitrary Feminines (Group B, @cite{butt-benjamin-2019} §1.3)
-- ============================================================================

def mesa    : SpanishNoun := ⟨"mesa",    "table",  .feminine, false⟩
def silla   : SpanishNoun := ⟨"silla",   "chair",  .feminine, false⟩
def casa    : SpanishNoun := ⟨"casa",    "house",  .feminine, false⟩
def puerta  : SpanishNoun := ⟨"puerta",  "door",   .feminine, false⟩
def ventana : SpanishNoun := ⟨"ventana", "window", .feminine, false⟩
def cama    : SpanishNoun := ⟨"cama",    "bed",    .feminine, false⟩
/-- *persona* 'person': common-gender noun (@cite{butt-benjamin-2019}
    §1.2.11) — feminine regardless of referent's sex. The famous
    @cite{kramer-2015} §6.2 exception: human-denoting noun with
    structurally arbitrary feminine gender. `isNaturalGender = false`
    captures that the gender does NOT come from biological sex (even
    though referent is human). -/
def persona : SpanishNoun := ⟨"persona", "person", .feminine, false⟩

-- ============================================================================
-- § 4: Default Masculines (Group B, @cite{butt-benjamin-2019} §1.3)
-- ============================================================================

def libro  : SpanishNoun := ⟨"libro",  "book",  .masculine, false⟩
def zapato : SpanishNoun := ⟨"zapato", "shoe",  .masculine, false⟩
def coche  : SpanishNoun := ⟨"coche",  "car",   .masculine, false⟩
def árbol  : SpanishNoun := ⟨"árbol",  "tree",  .masculine, false⟩
def cielo  : SpanishNoun := ⟨"cielo",  "sky",   .masculine, false⟩
def vaso   : SpanishNoun := ⟨"vaso",   "glass", .masculine, false⟩
/-- *ángel* 'angel': common-gender noun (@cite{butt-benjamin-2019}
    §1.2.11) — masculine for any sex. Companion to *persona*: the
    masculine fixed-gender exception. `isNaturalGender = false`. -/
def ángel  : SpanishNoun := ⟨"ángel",  "angel", .masculine, false⟩

-- ============================================================================
-- § 5: Same-Root Nominals (@cite{kramer-2020} §2.2.3)
-- ============================================================================

/-- Same-root nominals: a single root that surfaces as either masculine
    or feminine depending on the referent's sex. Empirically polymorphic
    in gender (one form, two genders), distinct from the atomic
    `SpanishNoun` schema. The DM analysis (combination with i[+FEM] vs
    i[−FEM]) lives in `Studies/Kramer2020.lean`. -/
structure SameRootEntry where
  form : String
  gloss : String
  deriving DecidableEq, Repr

def soldado    : SameRootEntry := ⟨"soldado",    "soldier"⟩
def estudiante : SameRootEntry := ⟨"estudiante", "student"⟩
def artista    : SameRootEntry := ⟨"artista",    "artist"⟩

-- ============================================================================
-- § 6: Inventory
-- ============================================================================

def naturalFemNouns : List SpanishNoun :=
  [mujer, niña, reina, gata]

def naturalMascNouns : List SpanishNoun :=
  [hombre, niño, rey, gato]

def arbitraryFemNouns : List SpanishNoun :=
  [mesa, silla, casa, puerta, ventana, cama, persona]

def defaultMascNouns : List SpanishNoun :=
  [libro, zapato, coche, árbol, cielo, vaso, ángel]

def allNouns : List SpanishNoun :=
  naturalFemNouns ++ naturalMascNouns ++ arbitraryFemNouns ++ defaultMascNouns

def sameRootNouns : List SameRootEntry :=
  [soldado, estudiante, artista]

-- ============================================================================
-- § 7: Typology profile (Corbett 1991, WALS Ch 30/31/32)
-- ============================================================================

open Typology.Gender
open Core (AgreementTarget)

/-- Spanish gender typology: 2-gender canonical sex-based. -/
def genderTypology : GenderProfile :=
  .fromWALS "Spanish" "spa"
    (rawGenderCount := 2)
    (genderCountFb := .two)
    (basisFb := .sexBased)
    (assignmentFb := .semanticAndFormal)
    (agreementTargets := [.attributive, .predicate, .personalPronoun])
    (semanticBases := [.sex])
    (attestedSurfaceGenders := [.masculine, .feminine])

example : genderTypology.iso639 = "spa" ∧ genderTypology.name = "Spanish" :=
  ⟨rfl, rfl⟩

end Fragments.Spanish.Gender
