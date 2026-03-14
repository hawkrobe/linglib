import Linglib.Theories.Morphology.DM.NominalStructure
import Linglib.Fragments.Italian.Nouns

/-!
# Italian Number–Gender Interaction @cite{adamson-2024}

Standard Italian has a small class of nouns — mostly body parts — whose
plural form changes gender from masculine to feminine. These are the
**-a plurals**: *braccio* (m.sg) → *braccia* (f.pl) 'arm/arms'.

@cite{adamson-2024} §5.1 analyzes this as evidence for the GLH's prediction
about number position: the -a plural involves **low number** (number on n,
within nP), which can interact with gender. Regular -i plurals involve
**high number** (number on Num, outside nP), which cannot.

This is the same locality logic as possession–gender interaction: features
within nP can condition gender; features outside nP cannot.
-/

namespace Fragments.Italian.NumberGender

open Morphology.DM
open Fragments.Italian.Nouns (Gender)

-- ============================================================================
-- § 1: Plural Classes
-- ============================================================================

/-- Italian plural classes, distinguished by where the number feature sits
    in the nominal spine.

    - **-a plurals**: number on n (low/derivational). These can change
      gender from masculine to feminine because the number feature is
      nP-internal, local to gender on n.
    - **Regular plurals** (-i, -e): number on Num (high/inflectional).
      These preserve gender because the number feature is outside nP. -/
inductive PluralClass where
  | aPlural   -- -a plurals: number on n (low), can change gender
  | regular   -- -i, -e plurals: number on Num (high), preserves gender
  deriving DecidableEq, BEq, Repr

/-- Map plural class to number position in the nominal spine. -/
def PluralClass.toNumberPosition : PluralClass → NumberPosition
  | .aPlural => .onN
  | .regular => .onNum

/-- Can this plural class's number feature interact with gender?
    Derived from the number position via the GLH — not stipulated. -/
def PluralClass.canAffectGender (pc : PluralClass) : Bool :=
  genderLocalityHypothesis pc.toNumberPosition.toNominalPosition

-- ============================================================================
-- § 2: Number–Gender Nouns
-- ============================================================================

/-- An Italian noun with explicit singular and plural gender tracking.
    The plural gender is derived from the singular gender and plural class,
    not stored independently. -/
structure NumberGenderNoun where
  formSg : String
  formPl : String
  gloss : String
  sgGender : Gender
  pluralClass : PluralClass
  deriving DecidableEq, BEq, Repr

/-- Plural gender: -a plurals are always feminine; regular plurals
    preserve the singular gender. -/
def NumberGenderNoun.plGender (n : NumberGenderNoun) : Gender :=
  match n.pluralClass with
  | .aPlural => .fem
  | .regular => n.sgGender

/-- Does this noun's gender change between singular and plural? -/
def NumberGenderNoun.genderChanges (n : NumberGenderNoun) : Bool :=
  n.sgGender != n.plGender

-- ============================================================================
-- § 3: Lexical Entries
-- ============================================================================

/-! ### -a plural body parts (masc.sg → fem.pl)

These are the canonical examples of low-number gender interaction.
The body-part semantics parallels the Teop/Jarawara data: body parts
interact with n in special ways across languages. -/

def braccio : NumberGenderNoun :=
  ⟨"braccio", "braccia", "arm", .masc, .aPlural⟩
def dito : NumberGenderNoun :=
  ⟨"dito", "dita", "finger", .masc, .aPlural⟩
def ginocchio : NumberGenderNoun :=
  ⟨"ginocchio", "ginocchia", "knee", .masc, .aPlural⟩
def labbro : NumberGenderNoun :=
  ⟨"labbro", "labbra", "lip", .masc, .aPlural⟩
def osso : NumberGenderNoun :=
  ⟨"osso", "ossa", "bone", .masc, .aPlural⟩
def sopracciglio : NumberGenderNoun :=
  ⟨"sopracciglio", "sopracciglia", "eyebrow", .masc, .aPlural⟩

/-! ### -a plural non-body parts -/

def uovo : NumberGenderNoun :=
  ⟨"uovo", "uova", "egg", .masc, .aPlural⟩
def paio : NumberGenderNoun :=
  ⟨"paio", "paia", "pair", .masc, .aPlural⟩
def miglio : NumberGenderNoun :=
  ⟨"miglio", "miglia", "mile", .masc, .aPlural⟩

/-! ### Regular plurals (gender-preserving) -/

def libroNG : NumberGenderNoun :=
  ⟨"libro", "libri", "book", .masc, .regular⟩
def ragazzoNG : NumberGenderNoun :=
  ⟨"ragazzo", "ragazzi", "boy", .masc, .regular⟩
def casaNG : NumberGenderNoun :=
  ⟨"casa", "case", "house", .fem, .regular⟩
def ragazzaNG : NumberGenderNoun :=
  ⟨"ragazza", "ragazze", "girl", .fem, .regular⟩

/-- All -a plural nouns. -/
def aPluralNouns : List NumberGenderNoun :=
  [braccio, dito, ginocchio, labbro, osso, sopracciglio,
   uovo, paio, miglio]

/-- All regular-plural nouns (for contrast). -/
def regularNouns : List NumberGenderNoun :=
  [libroNG, ragazzoNG, casaNG, ragazzaNG]

/-- All nouns in the inventory. -/
def allNouns : List NumberGenderNoun := aPluralNouns ++ regularNouns

-- ============================================================================
-- § 4: Per-Datum Verification
-- ============================================================================

-- -a plurals change gender
theorem braccio_changes : braccio.genderChanges = true := rfl
theorem dito_changes : dito.genderChanges = true := rfl
theorem ginocchio_changes : ginocchio.genderChanges = true := rfl
theorem labbro_changes : labbro.genderChanges = true := rfl
theorem osso_changes : osso.genderChanges = true := rfl
theorem uovo_changes : uovo.genderChanges = true := rfl

-- Regular plurals preserve gender
theorem libro_preserves : libroNG.genderChanges = false := rfl
theorem ragazzo_preserves : ragazzoNG.genderChanges = false := rfl
theorem casa_preserves : casaNG.genderChanges = false := rfl
theorem ragazza_preserves : ragazzaNG.genderChanges = false := rfl

-- Plural gender values
theorem braccio_pl_fem : braccio.plGender = .fem := rfl
theorem libro_pl_masc : libroNG.plGender = .masc := rfl
theorem casa_pl_fem : casaNG.plGender = .fem := rfl

-- ============================================================================
-- § 5: GLH Predictions
-- ============================================================================

/-- The GLH pipeline for number–gender interaction:
    PluralClass → NumberPosition → NominalPosition → GLH evaluation.
    Each stage feeds the next. -/
def numberGenderPipeline (pc : PluralClass) : Bool :=
  let numPos := pc.toNumberPosition
  let nomPos := numPos.toNominalPosition
  genderLocalityHypothesis nomPos

-- -a plurals: low number → within nP → CAN affect gender
theorem aPlural_can_affect : numberGenderPipeline .aPlural = true := rfl
-- Regular: high number → outside nP → CANNOT affect gender
theorem regular_cannot_affect : numberGenderPipeline .regular = false := rfl

/-- Gender changes in the plural iff the GLH permits number–gender
    interaction. Verified over the full inventory. -/
theorem gender_change_tracks_glh :
    allNouns.all (fun n =>
      n.genderChanges == n.pluralClass.canAffectGender) = true := by
  native_decide

/-- All -a plural nouns are masculine in the singular. The gender change
    is always masc → fem, never fem → masc. -/
theorem aPlural_always_masc_sg :
    aPluralNouns.all (fun n => n.sgGender == .masc) = true := by native_decide

/-- The -a plural class is exclusively body parts and measure nouns.
    6 of 9 are body parts — the same semantic class that drives
    possession–gender interaction in Teop and Jarawara. -/
theorem aPlural_body_part_count :
    (aPluralNouns.filter (fun n =>
      ["arm", "finger", "knee", "lip", "bone", "eyebrow"].contains n.gloss)).length = 6 := by
  native_decide

end Fragments.Italian.NumberGender
