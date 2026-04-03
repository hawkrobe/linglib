import Linglib.Fragments.Bantu.Params

/-!
# Swahili: Basic Types

Shared types for the Swahili fragment, primarily the noun class system.
Swahili has 18 noun classes (1–10, 14–18), following the standard Bantu
numbering. Classes 1/2 are singular/plural animate (human), classes 3–10
are inanimate with various semantic associations, and classes 15–18 are
infinitive and locative classes.

Noun class is the fundamental organizing principle of Swahili morphosyntax:
it conditions subject/object agreement on the verb, possessive agreement,
demonstrative agreement, and — crucially for relativization —
the form of resumptive pronouns (@cite{scott-2021}).

## Noun Class and Gender

Following @cite{carstens-1991} and @cite{kramer-2015}, noun class in Bantu
expresses the combination of number and gender. Classes come in singular/plural
pairs that define a "gender" (e.g., gender A = cl1/cl2 = human sg/pl).
-/

namespace Fragments.Swahili

open Fragments.Bantu

-- ============================================================================
-- § 1: Noun Classes
-- ============================================================================

/-- Swahili noun classes. Standard Bantu numbering (1–10, 14–18).
    Classes 11–13 are absent in Swahili. -/
inductive NounClass where
  | cl1    -- m-/mw- (human singular): mtoto 'child'
  | cl2    -- wa- (human plural): watoto 'children'
  | cl3    -- m-/mw- (tree/plant singular): mti 'tree'
  | cl4    -- mi- (tree/plant plural): miti 'trees'
  | cl5    -- ji-/∅ (augmentative singular): jicho 'eye'
  | cl6    -- ma- (augmentative plural): macho 'eyes'
  | cl7    -- ki- (diminutive singular): kiti 'chair'
  | cl8    -- vi- (diminutive plural): viti 'chairs'
  | cl9    -- n-/∅ (singular, large default class): nyumba 'house'
  | cl10   -- n-/∅ (plural, large default class): nyumba 'houses'
  | cl14   -- u- (abstract): uzuri 'beauty'
  | cl15   -- ku- (infinitive): kusoma 'to read'
  | cl16   -- pa- (definite location): mahali 'place'
  | cl17   -- ku- (indefinite/general location): —
  | cl18   -- mu-/m- (interior location): —
  deriving DecidableEq, Repr

/-- Whether a noun class is animate (classes 1 and 2). Animate classes
    trigger person-matching resumptive pronouns in relativization. -/
def NounClass.isAnimate : NounClass → Bool
  | .cl1 | .cl2 => true
  | _ => false

/-- Whether a noun class is a locative class (16, 17, 18). -/
def NounClass.isLocative : NounClass → Bool
  | .cl16 | .cl17 | .cl18 => true
  | _ => false

/-- Whether a noun class is singular. -/
def NounClass.isSingular : NounClass → Bool
  | .cl1 | .cl3 | .cl5 | .cl7 | .cl9 | .cl14 | .cl15 | .cl16 | .cl17 | .cl18 => true
  | _ => false

-- ============================================================================
-- § 2: Subject Agreement Prefixes
-- ============================================================================

/-- Subject prefix for each class on the verb. -/
def NounClass.subjPrefix : NounClass → String
  | .cl1  => "a"
  | .cl2  => "wa"
  | .cl3  => "u"
  | .cl4  => "i"
  | .cl5  => "li"
  | .cl6  => "ya"
  | .cl7  => "ki"
  | .cl8  => "vi"
  | .cl9  => "i"
  | .cl10 => "zi"
  | .cl14 => "u"
  | .cl15 => "ku"
  | .cl16 => "pa"
  | .cl17 => "ku"
  | .cl18 => "mu"

-- ============================================================================
-- § 3: Gender (Singular/Plural Pairings)
-- ============================================================================

/-- Bantu genders: singular/plural noun class pairings.
    @cite{carstens-1991}: different number/gender combinations constitute
    different noun classes. @cite{scott-2021} Table 3. -/
inductive Gender where
  | genderA   -- cl1/cl2 (human)
  | genderB   -- cl3/cl4
  | genderC   -- cl5/cl6
  | genderD   -- cl7/cl8
  | genderE   -- cl9/cl10
  deriving DecidableEq, Repr

/-- Singular class for a gender. -/
def Gender.singularClass : Gender → NounClass
  | .genderA => .cl1
  | .genderB => .cl3
  | .genderC => .cl5
  | .genderD => .cl7
  | .genderE => .cl9

/-- Plural class for a gender. -/
def Gender.pluralClass : Gender → NounClass
  | .genderA => .cl2
  | .genderB => .cl4
  | .genderC => .cl6
  | .genderD => .cl8
  | .genderE => .cl10

-- ============================================================================
-- § 4: Bridge to Shared Bantu Types
-- ============================================================================

/-- Semantic core status for each Swahili gender.

    Swahili's General Animate Concords (GAC) — class 1/2 agreement for all
    animate nouns regardless of class — suggests [animate] may be grammaticalized
    as a feature (@cite{carstens-2026} §8, (109)–(110)). The core assignments
    below follow the pattern established for Xhosa and Shona, with gender E
    (9/10) bearing [animal] given the predominance of animal terms in this
    class. Genders B–D lack salient entity-class associations. -/
def Gender.status : Gender → GenderStatus
  | .genderA => .interpretable .human
  | .genderE => .interpretable .animal
  | _ => .uninterpretable

end Fragments.Swahili
