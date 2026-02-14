import Linglib.Core.Morpheme

/-!
# Clitic vs. Affix Diagnostics (Zwicky & Pullum 1983)

Six criteria for distinguishing clitics from inflectional affixes,
formalized as a diagnostic profile.

## The six criteria

| Criterion | Clitic-like | Affix-like |
|-----------|-------------|------------|
| A. Selection | low (any category) | high (specific stems) |
| B. Paradigm gaps | none | present |
| C. Morphophonological idiosyncrasies | none | present |
| D. Semantic idiosyncrasies | none | present |
| E. Syntactic rules affect combination | no | yes |
| F. Attaches to cliticized material | yes | no |

A morpheme that scores affix-like on all six criteria is an inflectional
affix. A morpheme that scores clitic-like on all six is a simple clitic.
The surprising result of Zwicky & Pullum 1983 is that English *-n't*
scores affix-like on all six, despite the traditional clitic analysis.

## References

- Zwicky, A. M. & Pullum, G. K. (1983). Cliticization vs. Inflection:
  English N'T. *Language* 59(3), 502–513.
-/

namespace Morphology.Diagnostics

open Core.Morpheme (MorphStatus SelectionDegree)

-- ============================================================================
-- §1: Diagnostic Profile
-- ============================================================================

/-- A diagnostic profile scoring a bound morpheme on Zwicky & Pullum's
six criteria. Each field records the empirical observation for one
criterion; the classification into clitic vs. affix is *derived*
from the profile, not stipulated. -/
structure CliticAffixProfile where
  /-- Name of the morpheme being diagnosed. -/
  morpheme : String
  /-- A. Degree of selection: how restrictive is the morpheme about
      what it attaches to? Clitics: low. Affixes: singleCategory or closedClass. -/
  selection : SelectionDegree
  /-- B. Are there arbitrary gaps in the paradigm? Characteristic of
      affixes (e.g., *strided, *amn't). -/
  hasArbitraryGaps : Bool
  /-- C. Does the combination show morphophonological idiosyncrasies
      (irregular allomorphy, suppletion)? Characteristic of affixes
      (e.g., *won't* ← *will* + *n't*). -/
  hasMorphophonIdiosyncrasies : Bool
  /-- D. Does the combination show semantic idiosyncrasies (meaning
      not derivable from parts)? Characteristic of affixes
      (e.g., *mustn't* = MUST(NOT(P)), not NOT(MUST(P))). -/
  hasSemanticIdiosyncrasies : Bool
  /-- E. Do syntactic rules (e.g., Subject–Auxiliary Inversion)
      treat the combination as a unit? If yes, the morpheme behaves
      like part of the word (affix-like), not a separate clitic. -/
  syntacticRulesApply : Bool
  /-- F. Can the morpheme attach to material that already contains
      a (simple) clitic? Clitics can stack (*I'd've*); affixes
      cannot (**I'd'ven't*). -/
  attachesToCliticizedMaterial : Bool
  deriving Repr, BEq

-- ============================================================================
-- §2: Classification Predicates
-- ============================================================================

/-- Does this profile indicate affix-like behavior on criterion A? -/
def CliticAffixProfile.affixLikeSelection (p : CliticAffixProfile) : Bool :=
  p.selection.isHighSelection

/-- Count how many criteria score affix-like. -/
def CliticAffixProfile.affixScore (p : CliticAffixProfile) : Nat :=
  let scores : List Bool := [
    p.affixLikeSelection,        -- A
    p.hasArbitraryGaps,          -- B
    p.hasMorphophonIdiosyncrasies, -- C
    p.hasSemanticIdiosyncrasies,  -- D
    p.syntacticRulesApply,        -- E
    !p.attachesToCliticizedMaterial -- F (affix-like = CANNOT attach to clitics)
  ]
  scores.filter id |>.length

/-- Count how many criteria score clitic-like. -/
def CliticAffixProfile.cliticScore (p : CliticAffixProfile) : Nat :=
  6 - p.affixScore

/-- Classify a morpheme based on its diagnostic profile.

A morpheme that scores affix-like on all six criteria is classified
as an inflectional affix. A morpheme scoring clitic-like on all six
is a simple clitic. Mixed profiles are classified as special clitics
(following Zwicky 1977's taxonomy). -/
def CliticAffixProfile.classify (p : CliticAffixProfile) : MorphStatus :=
  if p.affixScore == 6 then .inflAffix
  else if p.cliticScore == 6 then .simpleClitic
  else .specialClitic

-- ============================================================================
-- §3: Per-Criterion Predicates
-- ============================================================================

/-- Does this morpheme satisfy all six criteria for inflectional affix? -/
def CliticAffixProfile.isUnambiguousAffix (p : CliticAffixProfile) : Bool :=
  p.affixScore == 6

/-- Does this morpheme satisfy all six criteria for simple clitic? -/
def CliticAffixProfile.isUnambiguousClitic (p : CliticAffixProfile) : Bool :=
  p.cliticScore == 6

-- ============================================================================
-- §4: Theorems
-- ============================================================================

/-- A morpheme scoring 6/6 affix-like classifies as inflAffix. -/
theorem classify_all_affix (p : CliticAffixProfile)
    (h : p.affixScore = 6) :
    p.classify = .inflAffix := by
  simp [CliticAffixProfile.classify, h]

/-- A morpheme scoring 0/6 affix-like classifies as simpleClitic. -/
theorem classify_all_clitic (p : CliticAffixProfile)
    (h : p.affixScore = 0) :
    p.classify = .simpleClitic := by
  simp [CliticAffixProfile.classify, h, CliticAffixProfile.cliticScore]

/-- Classification is exhaustive: every profile maps to a MorphStatus. -/
theorem classify_total (p : CliticAffixProfile) :
    p.classify = .inflAffix ∨ p.classify = .simpleClitic ∨ p.classify = .specialClitic := by
  unfold CliticAffixProfile.classify
  split
  · left; rfl
  · split
    · right; left; rfl
    · right; right; rfl

end Morphology.Diagnostics
