import Linglib.Fragments.Turkish.Negation

/-!
# Turkish Tense-Aspect-Modality System
[goksel-kerslake-2005]

The TAM system is the core of the Turkish verbal paradigm
([goksel-kerslake-2005] Ch 21, Appendix 2). There are five **basic** TAM
categories and three **modal** categories, occupying a single paradigmatic slot.

## Key properties

1. **Evidential -mIş is a TAM marker**, not a separate evidential morpheme.
   It fills the same paradigmatic slot as -DI (past definite) and cannot
   co-occur with it.

2. **Aorist negation is asymmetric**: affirmative -(I)r becomes negative -mAz
   rather than the expected *-mA-(I)r. All other categories use regular
   -mA- negation (see also `Turkish.Negation`).

3. **Compound tenses** are formed by adding a copular suffix (-DI, -mIş,
   -(y)sA) to the basic form: *geliyordu* (progressive + past copula).

## Suffix notation

Capital letters indicate vowel harmony alternation
(see `Turkish.VowelHarmony`):
- **A** = a/e (twofold), **I** = ı/i/u/ü (fourfold)
- **D** = d/t (voicing assimilation)
-/

namespace Turkish.TAM

/-- The eight TAM categories of Turkish. -/
inductive TAMCategory where
  | pastDef        -- witnessed/definite past: -DI
  | evidential     -- indirect/reportative: -(y)mIş
  | aorist         -- habitual/dispositional: -(I)r
  | progressive    -- ongoing: -Iyor
  | future         -- prospective: -(y)AcAK
  | conditional    -- hypothesis: -(y)sA
  | optative       -- wish/mild imperative: -(y)A
  | necessitative  -- obligation: -mAlI
  deriving DecidableEq, Repr, Inhabited

/-- TAM suffix entry with positive and negative forms. -/
structure TAMEntry where
  category : TAMCategory
  affSuffix : String
  negSuffix : String
  /-- Is negation symmetric (neg = stem + -mA- + TAM)? -/
  isNegSymmetric : Bool
  deriving Repr, BEq, Inhabited

def entries : List TAMEntry :=
  [ { category := .pastDef,      affSuffix := "-DI",
      negSuffix := "-mA-DI",     isNegSymmetric := true }
  , { category := .evidential,   affSuffix := "-mIş",
      negSuffix := "-mA-mIş",    isNegSymmetric := true }
  , { category := .aorist,       affSuffix := "-(I)r",
      negSuffix := "-mAz",       isNegSymmetric := false }
  , { category := .progressive,  affSuffix := "-Iyor",
      negSuffix := "-m-Iyor",    isNegSymmetric := true }
  , { category := .future,       affSuffix := "-(y)AcAK",
      negSuffix := "-mA-yAcAK",  isNegSymmetric := true }
  , { category := .conditional,  affSuffix := "-(y)sA",
      negSuffix := "-mA-sA",     isNegSymmetric := true }
  , { category := .optative,     affSuffix := "-(y)A",
      negSuffix := "-mA-yA",     isNegSymmetric := true }
  , { category := .necessitative, affSuffix := "-mAlI",
      negSuffix := "-mA-mAlI",   isNegSymmetric := true }
  ]

-- ============================================================================
-- § Compound tenses
-- ============================================================================

/-- Copular suffixes that combine with basic TAM for compound tenses. -/
inductive CopulaSuffix where
  | pastCop         -- -DI: geliyordu 'was coming'
  | evidentialCop   -- -(y)mIş: geliyormuş 'was apparently coming'
  | conditionalCop  -- -(y)sA: geliyorsa 'if s/he is coming'
  deriving DecidableEq, Repr

-- ============================================================================
-- § Verification
-- ============================================================================

/-- The aorist is the only TAM category with asymmetric negation;
    all others use regular `-mA-` insertion (cf. `Negation.aorist_asymmetric`
    for the surface-form counterpart). -/
theorem asymmetric_is_aorist :
    (entries.filter (! ·.isNegSymmetric)).map (·.category) = [.aorist] := rfl

end Turkish.TAM
