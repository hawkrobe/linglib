import Linglib.Features.Gender
import Linglib.Fragments.Bantu.Params

/-!
# Shona: Basic Types

@cite{carstens-2026}

The Shona noun class system with eight singular/plural pairings and
semantic core associations following @cite{carstens-2026} §3.5, §5.2.

Shona has fourteen active noun classes (1–14), organized into eight genders.
Unlike Xhosa's three-way semantic split ([human]/[inanimate]/[animal]),
Shona has a binary split: [human] (classes 1/2) vs everything else. The
[animal] association with classes 9/10 has bleached in Shona, leaving only
two interpretable genders.

## Agreement with conjoined singulars

The only consistent agreement patterns with conjoined singulars are:
- Class 2 *va-* for [human] conjuncts
- Class 8 *zvi-* for [non-human] conjuncts

Six of eight genders are uninterpretable, so default agreement dominates.
Gender-matching plural agreement is the exception, not the rule
(@cite{carstens-2026} §3.5, §5.2).
-/

namespace Fragments.Shona

open Fragments.Bantu

-- ============================================================================
-- § 1: Noun Classes
-- ============================================================================

/-- Shona noun classes. Standard Bantu numbering (1–14).
    Classes 15–18 are absent or non-productive. Class 11 plurals
    are syncretic with class 10; class 14 plurals use class 6. -/
inductive NounClass where
  | cl1     -- mu- (human singular): murume 'man'
  | cl2     -- va- (human plural): varume 'men'
  | cl3     -- mu- (singular): muti 'tree'
  | cl4     -- mi- (plural): miti 'trees'
  | cl5     -- zai/ri- (singular): zai 'egg'
  | cl6     -- ma- (plural): mazai 'eggs'
  | cl7     -- chi- (singular): chingwa 'bread'
  | cl8     -- zvi- (plural): zvingwa 'loaves'
  | cl9     -- n- (singular): imbwa 'dog'
  | cl10    -- n-/dz- (plural): imbwa 'dogs'
  | cl11    -- ru- (singular): rukova 'stream'
  | cl12    -- ka- (diminutive singular): kasikana 'small girl'
  | cl13    -- tu- (diminutive plural): tusikana 'small girls'
  | cl14    -- hu-/u- (singular): huchi 'honey'
  deriving DecidableEq, Repr

def NounClass.classNumber : NounClass → Nat
  | .cl1 => 1 | .cl2 => 2 | .cl3 => 3 | .cl4 => 4 | .cl5 => 5
  | .cl6 => 6 | .cl7 => 7 | .cl8 => 8 | .cl9 => 9 | .cl10 => 10
  | .cl11 => 11 | .cl12 => 12 | .cl13 => 13 | .cl14 => 14

def NounClass.isSingular : NounClass → Bool
  | .cl1 | .cl3 | .cl5 | .cl7 | .cl9 | .cl11 | .cl12 | .cl14 => true
  | _ => false

-- ============================================================================
-- § 2: Subject Agreement Prefixes
-- ============================================================================

/-- Subject marker prefix for each class on the verb.
    From examples in @cite{carstens-2026} §3.5. -/
def NounClass.subjPrefix : NounClass → String
  | .cl1  => "a"
  | .cl2  => "va"
  | .cl3  => "u"
  | .cl4  => "i"
  | .cl5  => "ri"
  | .cl6  => "a"
  | .cl7  => "chi"
  | .cl8  => "zvi"
  | .cl9  => "i"
  | .cl10 => "dzi"
  | .cl11 => "ru"
  | .cl12 => "ka"
  | .cl13 => "tu"
  | .cl14 => "hu"

-- ============================================================================
-- § 3: Gender (Singular/Plural Pairings)
-- ============================================================================

/-- Shona genders: eight singular/plural noun class pairings.
    From @cite{carstens-2026} (16). -/
inductive Gender where
  | genderA   -- cl1/cl2 (human)
  | genderB   -- cl3/cl4 (trees/plants)
  | genderC   -- cl5/cl6
  | genderD   -- cl7/cl8 (inanimate/non-human default)
  | genderE   -- cl9/cl10 (animals, diverse)
  | genderF   -- cl11/cl10 (streams, extended objects)
  | genderG   -- cl14/cl6
  | genderH   -- cl12/cl13 (diminutive)
  deriving DecidableEq, Repr

def Gender.singularClass : Gender → NounClass
  | .genderA => .cl1
  | .genderB => .cl3
  | .genderC => .cl5
  | .genderD => .cl7
  | .genderE => .cl9
  | .genderF => .cl11
  | .genderG => .cl14
  | .genderH => .cl12

def Gender.pluralClass : Gender → NounClass
  | .genderA => .cl2
  | .genderB => .cl4
  | .genderC => .cl6
  | .genderD => .cl8
  | .genderE => .cl10
  | .genderF => .cl10
  | .genderG => .cl6
  | .genderH => .cl13

-- ============================================================================
-- § 4: Semantic Core Assignments (@cite{carstens-2026} §5.2)
-- ============================================================================

/-- Semantic core status for each Shona gender.

    @cite{carstens-2026} §5.2: Shona has a binary [±human] split.
    Only classes 1/2 have the [human] core. Classes 7/8 serve as the
    non-human default — the core for "all and only non-humans." The
    [animal] association with 9/10 has bleached; the remaining six
    genders are purely formal (uninterpretable). -/
def Gender.status : Gender → GenderStatus
  | .genderA => .interpretable .human
  | .genderD => .interpretable .nonhuman
  | _ => .uninterpretable

-- ============================================================================
-- § 5: Bridge to Features.SurfaceGender
-- ============================================================================

/-- Map Shona gender classes to the shared surface-level gender type.
    Gender A (cl1/cl2, human) → animate; all others → inanimate.
    Shona's binary [±human] split maps naturally to the animate/inanimate
    distinction. -/
def Gender.toSurfaceGender : Gender → Features.SurfaceGender
  | .genderA => .animate
  | _ => .inanimate

end Fragments.Shona
