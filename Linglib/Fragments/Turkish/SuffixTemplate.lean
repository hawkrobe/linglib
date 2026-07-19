import Linglib.Morphology.Morphotactics.Template

/-!
# Turkish Suffix Templates
[goksel-kerslake-2005]

Turkish is strictly suffixing ([goksel-kerslake-2005] Ch 6): suffixes
attach in a fixed order determined by a positional template. The verbal
(Ch 6, 8, 13) and nominal (Ch 6, 8, 14) templates live here as Fragment
data over `Morphology.AffixTemplate`; ordering predictions are checked in
`Studies/GokselKerslake2005.lean`.

Voice suffixes can stack within their slot (*yap-tır-ıl-* 'be made to
do' = CAUS + PASS); slots are position classes, not token counts.
-/

namespace Turkish.SuffixTemplate

/-- Verbal suffix slots. [goksel-kerslake-2005] Ch 6, 8, 13. -/
inductive VerbSlot where
  | voice         -- causative -DIr, passive -(I)l, reflexive -(I)n, reciprocal -(I)ş
  | negation      -- -mA
  | tam           -- -DI, -mIş, -(I)r, -Iyor, -(y)AcAK, -sA, -(y)A, -mAlI
  | copula        -- compound tense: -DI, -mIş, -(y)sA
  | agreement     -- person/number
  | question      -- mI
  deriving DecidableEq, Repr

/-- Nominal suffix slots. [goksel-kerslake-2005] Ch 6, 8, 14. -/
inductive NounSlot where
  | derivational  -- denominal/deadjectival suffixes
  | plural        -- -lAr
  | possessive    -- -(I)m, -(I)n, -(s)I, etc.
  | case          -- -(y)I, -(y)A, -DA, -DAn, -(n)In, zero
  deriving DecidableEq, Repr

/-- The verbal template, stem-outward:
`Root - Voice - Negation - TAM - Copula - Agreement - Question`. -/
def verbTemplate : Morphology.AffixTemplate VerbSlot where
  suffixSlots := [.voice, .negation, .tam, .copula, .agreement, .question]

/-- The nominal template, stem-outward:
`Root - Derivational - Plural - Possessive - Case`. -/
def nounTemplate : Morphology.AffixTemplate NounSlot where
  suffixSlots := [.derivational, .plural, .possessive, .case]

end Turkish.SuffixTemplate
