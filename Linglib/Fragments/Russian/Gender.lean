import Linglib.Theories.Morphology.DM.Categorizer

/-!
# Russian Noun Gender @cite{corbett-1991} @cite{kramer-2020}

Gender assignments for Russian nouns, typed by DM categorizing heads.

Russian has three surface genders (masculine, feminine, neuter) and is
analyzed here as a **5-n language** in @cite{kramer-2015}'s framework:

| n head    | Gender value   | Surface gender | Example        |
|-----------|----------------|----------------|----------------|
| n i[+FEM] | natural fem    | feminine       | mat' 'mother'  |
| n i[−FEM] | natural masc   | masculine      | otec 'father'  |
| n u[+FEM] | arbitrary fem  | feminine       | škola 'school' |
| n u[−FEM] | arbitrary masc | masculine      | zakon 'law'    |
| plain n   | (default)      | neuter         | vino 'wine'    |

The semantic core (@cite{kramer-2020} ex. 17): male humans and higher
animals are masculine; female humans and higher animals are feminine.

Remainder nouns correlate with declension class (@cite{corbett-1991}):
Class I → masculine, Class II/III → feminine, others → neuter.
The correlation is imperfect: *put'* (Class III) is masculine and
*znamja* (Class III) is neuter (@cite{kramer-2020} ex. 19).

Hybrid nouns like *vrač* 'doctor' trigger masculine agreement on some
targets and feminine on others in the same clause
(@cite{kramer-2020} ex. 15–16).
-/

namespace Fragments.Russian.Gender

open Morphology.DM

-- ============================================================================
-- § 1: Declension Classes
-- ============================================================================

/-- Russian declension classes. Gender correlates with class but neither
    fully determines the other (@cite{corbett-1991};
    @cite{kramer-2020} §2.3.2). -/
inductive DeclClass where
  | I    -- e.g. zakon 'law' (typically masculine)
  | II   -- e.g. škola 'school' (typically feminine)
  | III  -- e.g. kost' 'bone' (typically feminine; exceptions: put', znamja)
  | IV   -- remaining patterns (typically neuter)
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- § 2: Russian Noun
-- ============================================================================

/-- A Russian noun annotated with its categorizing head and (optionally)
    its declension class. Semantic-core nouns omit the class since their
    gender is determined by the referent, not morphology. -/
structure RussianNoun where
  form : String
  gloss : String
  nHead : CatHead
  declClass : Option DeclClass := none
  deriving Repr

-- ============================================================================
-- § 3: Semantic Core (@cite{kramer-2020} ex. 17)
-- ============================================================================

def otec   : RussianNoun := { form := "otec",   gloss := "father",  nHead := .n_iMasc }
def mat'   : RussianNoun := { form := "mat'",   gloss := "mother",  nHead := .n_iFem }
def brat   : RussianNoun := { form := "brat",   gloss := "brother", nHead := .n_iMasc }
def sestra : RussianNoun := { form := "sestra", gloss := "sister",  nHead := .n_iFem }
def byk    : RussianNoun := { form := "byk",    gloss := "bull",    nHead := .n_iMasc }
def korova : RussianNoun := { form := "korova", gloss := "cow",     nHead := .n_iFem }

-- ============================================================================
-- § 4: Remainder — Declension Class Correlation (@cite{kramer-2020} ex. 18)
-- ============================================================================

def zakon : RussianNoun :=
  { form := "zakon", gloss := "law",    nHead := .n_uNegFem, declClass := some .I }
def škola : RussianNoun :=
  { form := "škola", gloss := "school", nHead := .n_uFem,    declClass := some .II }
def kost' : RussianNoun :=
  { form := "kost'", gloss := "bone",   nHead := .n_uFem,    declClass := some .III }
def vino  : RussianNoun :=
  { form := "vino",  gloss := "wine",   nHead := .n_plain,   declClass := some .IV }

-- ============================================================================
-- § 5: Class III Exceptions (@cite{kramer-2020} ex. 19)
-- ============================================================================

/-- *znamja* 'banner': Class III but neuter, not feminine.
    (@cite{corbett-1991}; @cite{kramer-2020} ex. 19a) -/
def znamja : RussianNoun :=
  { form := "znamja", gloss := "banner", nHead := .n_plain, declClass := some .III }

/-- *put'* 'way': the only masculine noun in Class III.
    (@cite{corbett-1991}; @cite{kramer-2020} ex. 19b) -/
def put'   : RussianNoun :=
  { form := "put'", gloss := "way", nHead := .n_uNegFem, declClass := some .III }

-- ============================================================================
-- § 6: Hybrid Noun (@cite{kramer-2020} ex. 15–16)
-- ============================================================================

/-- *vrač* 'doctor': morphologically masculine (Class I), but can trigger
    feminine agreement when the referent is female.
    (@cite{kramer-2020} ex. 15–16; @cite{corbett-1991}) -/
def vrač : RussianNoun :=
  { form := "vrač", gloss := "doctor", nHead := .n_uNegFem, declClass := some .I }

-- ============================================================================
-- § 7: Surface Gender Derivation
-- ============================================================================

/-- Russian surface gender: a 3-way system. -/
inductive SurfaceGender where
  | masculine | feminine | neuter
  deriving DecidableEq, BEq, Repr

/-- Derive surface gender from n head via Russian VI rules.

    Unlike Set 1 Spanish (plain n → masculine) or Set 2 Maa
    (plain n → feminine), Russian maps plain n to a THIRD gender
    (neuter), yielding 3 surface genders from 5 n-head types. -/
def surfaceGender (ch : CatHead) : SurfaceGender :=
  match ch.phi.gender with
  | some gf => if gf.val == ⟨.fem, .pos⟩ then .feminine else .masculine
  | none    => .neuter

-- ============================================================================
-- § 8: Inventory & Verification
-- ============================================================================

def semanticCoreNouns : List RussianNoun :=
  [otec, mat', brat, sestra, byk, korova]

def remainderNouns : List RussianNoun :=
  [zakon, škola, kost', vino, znamja, put']

def allNouns : List RussianNoun :=
  semanticCoreNouns ++ remainderNouns ++ [vrač]

theorem semanticMasc_all_iMasc :
    [otec, brat, byk].all (·.nHead == CatHead.n_iMasc) = true := by native_decide

theorem semanticFem_all_iFem :
    [mat', sestra, korova].all (·.nHead == CatHead.n_iFem) = true := by native_decide

-- Declension class ↔ gender correlation (ex. 18)
theorem classI_masculine  : surfaceGender zakon.nHead = .masculine := rfl
theorem classII_feminine  : surfaceGender škola.nHead = .feminine  := rfl
theorem classIII_feminine : surfaceGender kost'.nHead = .feminine  := rfl
theorem default_neuter    : surfaceGender vino.nHead  = .neuter    := rfl

-- Class III exceptions show declension class ≠ gender (ex. 19)
theorem znamja_classIII_neuter :
    znamja.declClass = some .III ∧ surfaceGender znamja.nHead = .neuter := ⟨rfl, rfl⟩

theorem put'_classIII_masculine :
    put'.declClass = some .III ∧ surfaceGender put'.nHead = .masculine := ⟨rfl, rfl⟩

/-- Declension class does not determine gender: *znamja* and *kost'*
    share Class III but differ in surface gender. -/
theorem declClass_ne_gender :
    znamja.declClass = kost'.declClass ∧
    surfaceGender znamja.nHead ≠ surfaceGender kost'.nHead := ⟨rfl, by decide⟩

/-- All five n-types are represented in the inventory. -/
theorem five_n_types_covered :
    allNouns.any (·.nHead == CatHead.n_iFem) = true ∧
    allNouns.any (·.nHead == CatHead.n_iMasc) = true ∧
    allNouns.any (·.nHead == CatHead.n_uFem) = true ∧
    allNouns.any (·.nHead == CatHead.n_uNegFem) = true ∧
    allNouns.any (·.nHead == CatHead.n_plain) = true :=
  ⟨by native_decide, by native_decide, by native_decide,
   by native_decide, by native_decide⟩

end Fragments.Russian.Gender
