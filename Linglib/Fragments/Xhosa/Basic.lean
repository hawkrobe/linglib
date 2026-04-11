import Linglib.Core.Gender
import Linglib.Fragments.Bantu.Params

/-!
# Xhosa: Basic Types

@cite{carstens-2026} @cite{taraldsen-et-al-2018}

The Xhosa noun class system with five singular/plural pairings (genders A–E)
and semantic core associations following @cite{carstens-2026}.

Xhosa has ten active noun classes (1–10) plus class 15 (infinitives/gerunds),
organized into five genders. Three genders have interpretable semantic cores:
A (1/2) = [human], D (7/8) = [inanimate], E (9/10) = [animal]. Two genders
(B = 3/4, C = 5/6) are uninterpretable — their members are semantically
arbitrary.

## Agreement with conjoined singulars

The interpretability split directly predicts agreement patterns with
uniform conjoined singulars (@cite{carstens-2026} §3, Tables 13–14):

- [1&1], [7&7], [9&9]: gender-matching plural agreement available
- [3&3], [5&5]: gender-matching plural agreement unavailable; default only

Default agreement: class 2 *ba-* for [human], class 8 *zi-* for non-human.
-/

namespace Fragments.Xhosa

open Fragments.Bantu

-- ============================================================================
-- § 1: Noun Classes
-- ============================================================================

/-- Xhosa noun classes. Standard Bantu numbering (1–10, 15).
    Classes 11–14 and 16–18 are absent in modern Xhosa. -/
inductive NounClass where
  | cl1     -- um-/u- (human singular): umntu 'person'
  | cl2     -- aba- (human plural): abantu 'people'
  | cl3     -- um- (singular): umthi 'tree'
  | cl4     -- imi- (plural): imithi 'trees'
  | cl5     -- i- (singular): iqanda 'egg'
  | cl6     -- ama- (plural): amaqanda 'eggs'
  | cl7     -- isi- (singular): isitya 'dish'
  | cl8     -- izi- (plural): izitya 'dishes'
  | cl9     -- in- (singular): inja 'dog'
  | cl10    -- iin- (plural): iinja 'dogs'
  | cl15    -- uku- (infinitive/gerund): ukucula 'to sing'
  deriving DecidableEq, Repr

def NounClass.classNumber : NounClass → Nat
  | .cl1 => 1 | .cl2 => 2 | .cl3 => 3 | .cl4 => 4 | .cl5 => 5
  | .cl6 => 6 | .cl7 => 7 | .cl8 => 8 | .cl9 => 9 | .cl10 => 10
  | .cl15 => 15

def NounClass.isSingular : NounClass → Bool
  | .cl1 | .cl3 | .cl5 | .cl7 | .cl9 | .cl15 => true
  | _ => false

-- ============================================================================
-- § 2: Subject Agreement Prefixes
-- ============================================================================

/-- Subject marker prefix for each class on the verb.
    From @cite{carstens-2026} and @cite{taraldsen-et-al-2018}. -/
def NounClass.subjPrefix : NounClass → String
  | .cl1  => "u"
  | .cl2  => "ba"
  | .cl3  => "u"
  | .cl4  => "i"
  | .cl5  => "li"
  | .cl6  => "a"
  | .cl7  => "si"
  | .cl8  => "zi"
  | .cl9  => "i"
  | .cl10 => "zi"
  | .cl15 => "ku"

-- ============================================================================
-- § 3: Gender (Singular/Plural Pairings)
-- ============================================================================

/-- Xhosa genders: singular/plural noun class pairings.
    @cite{carstens-1991} (17): five genders A–E for classes 1–10. -/
inductive Gender where
  | genderA   -- cl1/cl2 (human)
  | genderB   -- cl3/cl4
  | genderC   -- cl5/cl6
  | genderD   -- cl7/cl8 (inanimate)
  | genderE   -- cl9/cl10 (animal)
  deriving DecidableEq, Repr

def Gender.singularClass : Gender → NounClass
  | .genderA => .cl1
  | .genderB => .cl3
  | .genderC => .cl5
  | .genderD => .cl7
  | .genderE => .cl9

def Gender.pluralClass : Gender → NounClass
  | .genderA => .cl2
  | .genderB => .cl4
  | .genderC => .cl6
  | .genderD => .cl8
  | .genderE => .cl10

-- ============================================================================
-- § 4: Semantic Core Assignments (@cite{carstens-2026} (71))
-- ============================================================================

/-- Semantic core status for each Xhosa gender.

    @cite{carstens-2026} (71):
    - Gender A (1/2): nₐ₁ = i[entity] i[human], nₐ₂ = i[entity] (arbitrary)
    - Gender B (3/4): nB = uninterpretable for all members
    - Gender C (5/6): nC = uninterpretable for all members
    - Gender D (7/8): nD₁ = i[entity] i[inanimate], nD₂ = i[entity] (arbitrary)
    - Gender E (9/10): nE₁ = i[entity] i[animal], nE₂ = i[entity] (arbitrary) -/
def Gender.status : Gender → GenderStatus
  | .genderA => .interpretable .human
  | .genderB => .uninterpretable
  | .genderC => .uninterpretable
  | .genderD => .interpretable .inanimate
  | .genderE => .interpretable .animal

-- ============================================================================
-- § 5: nP Stacking Structures (@cite{carstens-2026} (72)–(73))
-- ============================================================================

/-- Sample nP structure for a [human] noun in its canonical class 1/2.
    E.g. *umntwana* 'child': [n₁/₂ √MNTWANA] — single layer. -/
def humanCanonical : NPStack where
  visibleClass := 1
  coreClass := 1
  status := .interpretable .human

/-- Sample nP structure for a [human] noun in non-canonical class 3/4.
    E.g. *umgewu* 'criminal': [n₃/₄ [n₁/₂ √GEWU]] — stacked. -/
def humanInClass3 : NPStack where
  visibleClass := 3
  coreClass := 1
  status := .interpretable .human

/-- Sample nP structure for a [human] noun in non-canonical class 5/6.
    E.g. *ibutho* 'warrior': [n₅/₆ [n₁/₂ √BUTHO]] — stacked. -/
def humanInClass5 : NPStack where
  visibleClass := 5
  coreClass := 1
  status := .interpretable .human

/-- Sample nP structure for an [animal] noun in its canonical class 9/10.
    E.g. *indlovu* 'elephant': [n₉/₁₀ √DLOVU] — single layer. -/
def animalCanonical : NPStack where
  visibleClass := 9
  coreClass := 9
  status := .interpretable .animal

/-- Sample nP structure for an [animal] noun in non-canonical class 1a/2a.
    E.g. *unonkala* 'crab': [n₁/₂ [n₉/₁₀ √NONKALA]] — stacked. -/
def animalInClass1 : NPStack where
  visibleClass := 1
  coreClass := 9
  status := .interpretable .animal

-- ============================================================================
-- § 6: Bridge to Core.SurfaceGender
-- ============================================================================

/-- Map Xhosa gender classes to the shared surface-level gender type.
    Gender A (cl1/cl2, human) → animate; all others → inanimate.
    Xhosa's finer-grained semantic cores ([animal] for E, [inanimate] for D)
    are captured in `GenderStatus`, not at the SurfaceGender level. -/
def Gender.toSurfaceGender : Gender → Core.SurfaceGender
  | .genderA => .animate
  | _ => .inanimate

end Fragments.Xhosa
