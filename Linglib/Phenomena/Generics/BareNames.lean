import Mathlib.Data.Rat.Defs

/-
# Bare Singular Names and Genericity

Empirical patterns on generic uses of bare singular names (BSNs) like "Ruth",
following Gasparri (2025). Predicativists treat BSNs as predicative DPs:

  ⟦∅ Ruth⟧ = ⟦the⟧ [λx.x is called Ruth]

If names are count nouns, BSNs should pattern with definite singulars
like "the tiger" for genericity. The data shows BSNs CAN get generic readings,
but exhibit "generic recalcitrance" — harder than ordinary definite singulars.

## Key findings

1. BSNs can get generic readings, especially with QAdvs (generally, typically)
2. BSNs are more resistant to generic readings than "the tiger" (recalcitrance)
3. Locative adjuncts, adjectival modifiers, and naming-convention contexts help
4. Generic BSNs are not upward-entailing (diagnostic for true genericity)

## References

- Gasparri, L. (2025). Bare singular names and genericity. Journal of Semantics 42: 127-135.
- Carlson, G. (1977). Reference to Kinds in English.
- Krifka, M. et al. (1995). Genericity: An Introduction.
- Dayal, V. (2004). Number Marking and (in)Definiteness in Kind Terms.
-/

namespace Phenomena.Generics.BareNames

/-- Reading availability judgment. -/
inductive ReadingStatus where
  | ok          -- ✓
  | marginal    -- ?
  | degraded    -- ??
  deriving Repr, DecidableEq, BEq

/-- A datum recording whether token and generic readings are available. -/
structure ReadingDatum where
  sentence : String
  tokenReading : ReadingStatus
  genericReading : ReadingStatus
  notes : String := ""
  deriving Repr

/-- What kind of DP is the subject? -/
inductive SubjectType where
  | bareName          -- Ruth, John, Paul
  | definiteCommon    -- the tiger, the dodo, the Coke bottle
  | modifiedName      -- Italian Andrea, the Rutgers professor
  | barePlural        -- tigers, mountains
  | quotedName        -- 'Ruth', 'Tristan'
  deriving Repr, DecidableEq, BEq

/-- What licensing factor (if any) enables the generic reading? -/
inductive GenericLicensor where
  | none              -- No overt licensor
  | qAdv              -- generally, typically, usually
  | locativeAdjunct   -- In England, In Italy
  | adjectivalMod     -- Italian (Andrea), German (Andrea)
  | genericContext     -- naming conventions, social stereotypes
  | kindLevelPred     -- extinct, widespread, common (select for kinds)
  deriving Repr, DecidableEq, BEq

/-- Full datum with DP type and licensing information. -/
structure BSNDatum where
  sentence : String
  subjectType : SubjectType
  tokenReading : ReadingStatus
  genericReading : ReadingStatus
  licensor : GenericLicensor := .none
  deriving Repr

-- BSNs vs Ordinary Definite Singulars: The Basic Contrast (ex. 4)

def ruth_common : BSNDatum :=
  { sentence := "Ruth is common"
  , subjectType := .bareName
  , tokenReading := .degraded
  , genericReading := .degraded }

def ruth_dancer : BSNDatum :=
  { sentence := "Ruth is a dancer"
  , subjectType := .bareName
  , tokenReading := .ok
  , genericReading := .degraded }

def the_tiger_striped : BSNDatum :=
  { sentence := "The tiger is striped"
  , subjectType := .definiteCommon
  , tokenReading := .ok
  , genericReading := .ok }

def the_tiger_widespread : BSNDatum :=
  { sentence := "The tiger is widespread"
  , subjectType := .definiteCommon
  , tokenReading := .degraded
  , genericReading := .ok
  , licensor := .kindLevelPred }

-- QAdv Licensing: Generally/Typically Improve Generic Access (ex. 6-8)

def ruth_40 : BSNDatum :=
  { sentence := "Ruth is 40 years old"
  , subjectType := .bareName
  , tokenReading := .ok
  , genericReading := .degraded }

def ruth_typically_40 : BSNDatum :=
  { sentence := "Ruth is typically 40 years old"
  , subjectType := .bareName
  , tokenReading := .degraded
  , genericReading := .degraded
  , licensor := .qAdv }

def rutgers_prof_40 : BSNDatum :=
  { sentence := "The Rutgers professor is 40 years old"
  , subjectType := .definiteCommon
  , tokenReading := .ok
  , genericReading := .degraded }

def rutgers_prof_generally_40 : BSNDatum :=
  { sentence := "The Rutgers professor is generally 40 years old"
  , subjectType := .definiteCommon
  , tokenReading := .degraded
  , genericReading := .ok
  , licensor := .qAdv }

def coke_bottle_narrow : BSNDatum :=
  { sentence := "The Coke bottle has a narrow neck"
  , subjectType := .definiteCommon
  , tokenReading := .ok
  , genericReading := .ok }

def coke_bottle_generally_narrow : BSNDatum :=
  { sentence := "The Coke bottle generally has a narrow neck"
  , subjectType := .definiteCommon
  , tokenReading := .degraded
  , genericReading := .ok
  , licensor := .qAdv }

-- Locative Adjuncts License Generic BSNs (ex. 11-13)

def leslie_english_woman : BSNDatum :=
  { sentence := "In English, Leslie is generally a woman"
  , subjectType := .bareName
  , tokenReading := .degraded
  , genericReading := .ok
  , licensor := .locativeAdjunct }

def italian_andrea_male : BSNDatum :=
  { sentence := "Italian Andrea is generally (a) male"
  , subjectType := .modifiedName
  , tokenReading := .marginal
  , genericReading := .ok
  , licensor := .adjectivalMod }

def german_andrea_female : BSNDatum :=
  { sentence := "German Andrea is generally (a) female"
  , subjectType := .modifiedName
  , tokenReading := .marginal
  , genericReading := .ok
  , licensor := .adjectivalMod }

-- Generic BSNs in Naming-Convention Contexts (ex. 21, 26)

def ruth_good_grades : BSNDatum :=
  { sentence := "According to the numbers, Ruth has good grades in biology"
  , subjectType := .bareName
  , tokenReading := .degraded
  , genericReading := .ok
  , licensor := .genericContext }

def paul_falls_in_love : BSNDatum :=
  { sentence := "Paul falls in love with individuals with names of comparable length"
  , subjectType := .bareName
  , tokenReading := .degraded
  , genericReading := .ok
  , licensor := .genericContext }

-- Non-Upward-Entailment: Diagnostic for Genericity (ex. 24-25)

/-- Generic readings are not upward-entailing.
    "The kangaroo rat arrived" ⊭ "A rodent arrived" (on generic reading)
    "Ruth arrived" ⊭ "A person whose name starts with r arrived" -/
structure NonEntailmentDatum where
  premise : String
  wouldBeConclusion : String
  entails : Bool  -- false = not upward-entailing, confirming genericity
  deriving Repr

def kangaroo_rat_not_ue : NonEntailmentDatum :=
  { premise := "According to the numbers, Ruth has good grades in biology"
  , wouldBeConclusion := "A person whose name starts with 'r' has good grades"
  , entails := false }

-- Kind-Level Predicates: BSNs Resist, Definites Allow (ex. 34-35)

def dodo_extinct : BSNDatum :=
  { sentence := "The dodo is extinct"
  , subjectType := .definiteCommon
  , tokenReading := .degraded
  , genericReading := .ok
  , licensor := .kindLevelPred }

def tristan_extinct : BSNDatum :=
  { sentence := "Tristan is extinct"
  , subjectType := .bareName
  , tokenReading := .degraded
  , genericReading := .degraded
  , licensor := .kindLevelPred }

def john_became_common : BSNDatum :=
  { sentence := "John became common in the 19th century"
  , subjectType := .bareName
  , tokenReading := .degraded
  , genericReading := .degraded
  , licensor := .kindLevelPred }

def quoted_tristan_extinct : BSNDatum :=
  { sentence := "'Tristan' is extinct"
  , subjectType := .quotedName
  , tokenReading := .degraded
  , genericReading := .ok
  , licensor := .kindLevelPred }

def quoted_john_common : BSNDatum :=
  { sentence := "'John' became common in the 19th century"
  , subjectType := .quotedName
  , tokenReading := .degraded
  , genericReading := .ok
  , licensor := .kindLevelPred }

-- Recalcitrance Summary

/-- Generic recalcitrance: BSNs are harder to interpret generically
    than ordinary definite singulars, but it IS possible with licensing. -/
def recalcitrancePattern : List BSNDatum :=
  [ ruth_dancer         -- BSN without licensor: ??gen
  , the_tiger_striped   -- Def singular without licensor: ✓gen
  , ruth_good_grades    -- BSN with naming-convention context: ✓gen
  , leslie_english_woman -- BSN with locative + QAdv: ✓gen
  , italian_andrea_male  -- Modified name with QAdv: ✓gen
  , tristan_extinct     -- BSN with kind-level predicate: ??gen (still hard)
  , quoted_tristan_extinct -- Quoted name with kind-level predicate: ✓gen
  ]

/-- BSNs without licensing resist generics; with licensing they improve. -/
theorem recalcitrance_without_licensor :
    ruth_dancer.genericReading = .degraded := rfl

theorem recalcitrance_with_licensor :
    ruth_good_grades.genericReading = .ok := rfl

/-- Definite singulars don't need licensing for generic readings. -/
theorem def_singular_no_licensor_needed :
    the_tiger_striped.genericReading = .ok ∧
    the_tiger_striped.licensor = .none := ⟨rfl, rfl⟩

/-- Quotation rescues kind-level predicates for names. -/
theorem quotation_rescues_kind_level :
    tristan_extinct.genericReading = .degraded ∧
    quoted_tristan_extinct.genericReading = .ok := ⟨rfl, rfl⟩

-- Predicativist Parallel

/-- The predicativist claim: BSNs and definite common NPs have parallel structure.
    ⟦∅ Ruth⟧ = ⟦the⟧ [λx.x is called Ruth]
    ⟦the tiger⟧ = ⟦the⟧ [λx.x is a tiger]
    If this is right, they should pattern alike for genericity.
    The data shows they mostly do, modulo recalcitrance. -/
structure PredicativistParallel where
  bsnDatum : BSNDatum
  defDatum : BSNDatum
  /-- Do both allow the same generic reading status? -/
  genericParallel : Bool :=
    bsnDatum.genericReading == defDatum.genericReading

def striped_parallel : PredicativistParallel :=
  { bsnDatum := ruth_dancer
  , defDatum := the_tiger_striped }

/-- Not all parallels hold — this is the recalcitrance phenomenon. -/
theorem recalcitrance_breaks_parallel :
    striped_parallel.genericParallel = false := rfl

def kind_level_parallel : PredicativistParallel :=
  { bsnDatum := quoted_tristan_extinct
  , defDatum := dodo_extinct }

/-- Quotation restores the parallel for kind-level predicates. -/
theorem quotation_restores_parallel :
    kind_level_parallel.genericParallel = true := rfl

end Phenomena.Generics.BareNames
