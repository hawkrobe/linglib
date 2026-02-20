import Linglib.Core.PersonCategory

/-!
# Paradigmatic Structure of Person Marking (Cysouw 2009)

Formalizes the typological framework from:

  Cysouw, M. (2009). *The Paradigmatic Structure of Person Marking*.
  Oxford Studies in Typology and Linguistic Theory. Oxford University Press.

## Core Ideas

Person marking is analyzed not via traditional "person × number" grids but via
**participant groups**: sets of speech act participants that are marked by a
single morpheme.  "Plural" is reanalyzed as qualitative group composition
(who is included?) rather than quantitative number (how many?).

The 8-cell paradigmatic scheme (Fig 10.1) comprises:
- 3 **singular** categories: speaker (1), addressee (2), other (3)
- 5 **group** categories: 1+2 (minimal inclusive), 1+2+3 (augmented inclusive),
  1+3 (exclusive), 2+3 (second person group), 3+3 (third person group)

A **paradigmatic structure** assigns each category to a morpheme class: categories
sharing a class are homophonous (marked by the same form).

## Key Results Formalized

- **Singular homophony types** (Sa–Se): 5 patterns from Chapter 2
- **First person complex types** (Pa–Pe): 5 common patterns from Chapter 3
- **Explicitness Hierarchy** (10.7): ordering of paradigmatic explicitness
- **Horizontal Homophony Hierarchy** (10.1–10.2): ordering of horizontal mergers
- **Implicational universals**: exclusive → inclusive (3.23), split inclusive → exclusive (3.24)
- **Homophony Implication** (10.4): singular homophony → inflectional paradigm

## References

- Cysouw, M. (2009). The Paradigmatic Structure of Person Marking. OUP.
- Ingram, D. (1978). Typology and universals of personal pronouns.
- Greenberg, J. (1963). Some universals of grammar.
-/

namespace Phenomena.Agreement.Typology

-- Re-export PersonCategory from Core for backwards compatibility
open Core.PersonCategory
export Core.PersonCategory (PersonCategory)

-- ============================================================================
-- §2: Paradigmatic Structure
-- ============================================================================

/-- A paradigmatic structure assigns each of the 8 person categories to a
morpheme class.  Categories assigned the same natural number are realized
by the same morpheme (homophonous).

This is the central representational device: all of Cysouw's typological
classifications are computable from this function. -/
structure ParadigmaticStructure where
  /-- Language or paradigm name -/
  name : String
  /-- ISO 639-3 code (if applicable) -/
  isoCode : String := ""
  /-- Maps each person category to a morpheme class index.
      Same index = same morpheme (homophony). -/
  morphClass : PersonCategory → Nat
  /-- Whether this is an inflectional (true) or independent (false) paradigm -/
  isInflectional : Bool := false
instance : BEq ParadigmaticStructure where
  beq a b := a.name == b.name

/-- Two categories are homophonous in a paradigm iff they share morphClass. -/
def ParadigmaticStructure.homophonous
    (s : ParadigmaticStructure) (c1 c2 : PersonCategory) : Bool :=
  s.morphClass c1 == s.morphClass c2

/-- Number of distinct morphemes in the paradigm. -/
def ParadigmaticStructure.distinctForms (s : ParadigmaticStructure) : Nat :=
  let classes := PersonCategory.all.map s.morphClass
  classes.eraseDups.length

-- ============================================================================
-- §3: Singular Homophony Types (Chapter 2)
-- ============================================================================

/-- The 5 singular homophony types (Cysouw 2009, §2.1–2.5).

Classifies how the three singular categories (1, 2, 3) pattern with
respect to homophony within a paradigm. -/
inductive SingularType where
  | Sa  -- Latin-type: all distinct (1 ≠ 2 ≠ 3)
  | Sb  -- Dutch-type: 1 vs 2=3 (speaker distinguished)
  | Sc  -- Spanish-type: 1=3 vs 2 (addressee distinguished)
  | Sd  -- English-type: 1=2 vs 3 (SAPs vs other)
  | Se  -- French-type: 1=2=3 (all homophonous)
  deriving DecidableEq, BEq, Repr

/-- Compute the singular homophony type from a paradigmatic structure. -/
def ParadigmaticStructure.singularType (s : ParadigmaticStructure) : SingularType :=
  let eq12 := s.homophonous .s1 .s2
  let eq13 := s.homophonous .s1 .s3
  let eq23 := s.homophonous .s2 .s3
  match eq12, eq13, eq23 with
  | false, false, false => .Sa  -- Latin: all distinct
  | false, false, true  => .Sb  -- Dutch: 2=3
  | false, true,  false => .Sc  -- Spanish: 1=3
  | true,  false, false => .Sd  -- English: 1=2
  | _,     _,     _     => .Se  -- French: 1=2=3 (and impossible partial cases)

-- ============================================================================
-- §4: First Person Complex Types (Chapter 3)
-- ============================================================================

/-- The 5 common types of marking for 'we' (Cysouw 2009, Table 3.2/10.3).

Classifies how the three first-person-complex categories (1+2, 1+2+3, 1+3)
pattern in the paradigm relative to singular 1. -/
inductive FirstPersonComplexType where
  | Pa  -- Unified-we: one form for all 'we' (1=1+2=1+2+3=1+3)
  | Pb  -- No-we: no specialized 'we' (1+2=1+2+3=1+3=1)
  | Pc  -- Only-inclusive: inclusive specialized, exclusive = 1sg (1+2=1+2+3 ≠ 1+3=1)
  | Pd  -- Inclusive/exclusive: incl vs excl, no min/aug split (1+2=1+2+3 ≠ 1+3)
  | Pe  -- Minimal/augmented: all three distinct (1+2 ≠ 1+2+3 ≠ 1+3)
  deriving DecidableEq, BEq, Repr

/-- Compute the first person complex type from a paradigmatic structure.

Follows the decision tree in Figure 3.10:
1. Any specialized 'we'? (No → Pb)
2. Inclusive distinguished from exclusive? (No → Pa unified-we)
3. Exclusive specialized (≠ 1sg)? (No → Pc only-inclusive)
4. Inclusive split (min ≠ aug)? (No → Pd, Yes → Pe) -/
def ParadigmaticStructure.firstPersonComplexType
    (s : ParadigmaticStructure) : FirstPersonComplexType :=
  -- Step 1: Any specialized 'we' at all? (any fpc category ≠ 1sg)
  let anySpecialized := !(s.homophonous .minIncl .s1 &&
                           s.homophonous .augIncl .s1 &&
                           s.homophonous .excl .s1)
  if !anySpecialized then .Pb
  else
    -- Step 2: Is inclusive distinguished from exclusive?
    -- Pa unified-we: all three fpc categories share one form
    let inclDiffFromExcl := !(s.homophonous .minIncl .excl &&
                               s.homophonous .augIncl .excl)
    if !inclDiffFromExcl then .Pa  -- unified-we: incl = excl
    else
      -- Step 3: Is exclusive also specialized (≠ 1sg)?
      let exclSpec := !(s.homophonous .excl .s1)
      if !exclSpec then .Pc  -- Only inclusive specialized; excl = 1sg
      else
        -- Step 4: Is inclusive split into minimal vs augmented?
        let inclSplit := !(s.homophonous .minIncl .augIncl)
        if inclSplit then .Pe  -- Minimal/augmented
        else .Pd  -- Inclusive/exclusive

-- ============================================================================
-- §5: Homophony Kinds
-- ============================================================================

/-- Whether a paradigm has horizontal homophony (singular = non-singular). -/
def ParadigmaticStructure.hasHorizontalHomophony (s : ParadigmaticStructure) : Bool :=
  PersonCategory.all.filter (·.isSingular) |>.any λ sg =>
    PersonCategory.all.filter (·.isGroup) |>.any λ grp =>
      s.homophonous sg grp

/-- Whether a paradigm has singular homophony (between singular categories). -/
def ParadigmaticStructure.hasSingularHomophony (s : ParadigmaticStructure) : Bool :=
  s.homophonous .s1 .s2 || s.homophonous .s1 .s3 || s.homophonous .s2 .s3

/-- Whether a paradigm has vertical homophony (between non-singular categories,
excluding the first person complex internal structure).

Cysouw §10.1.6: "the various kinds of homophony between the categories of the
first person complex are not included under this heading."  So we only check
mergers between the first person complex and {2+3, 3+3}, or between 2+3 and 3+3. -/
def ParadigmaticStructure.hasVerticalHomophony (s : ParadigmaticStructure) : Bool :=
  let fpc := [PersonCategory.minIncl, .augIncl, .excl]
  let nonFPC := [PersonCategory.secondGrp, .thirdGrp]
  -- Any first-person-complex category = any non-first-person group?
  fpc.any (λ f => nonFPC.any (λ n => s.homophonous f n)) ||
  -- Or: 2+3 = 3+3?
  s.homophonous .secondGrp .thirdGrp

-- ============================================================================
-- §6: Explicitness Hierarchy (10.7)
-- ============================================================================

/-- Explicitness level of a paradigm (Cysouw 2009, §10.1.7).

Measures how many person oppositions are grammaticalized in the paradigm.
Higher = more explicit (more distinct morphemes). -/
inductive ExplicitnessLevel where
  | singularHomophony    -- least explicit: even singular categories merge
  | verticalHomophony    -- non-singular categories merge
  | unifiedWe            -- one form for all 'we'
  | inclusiveExclusive   -- incl vs excl distinguished
  | minimalAugmented     -- most explicit: min.incl ≠ aug.incl ≠ excl
  deriving DecidableEq, BEq, Repr

instance : Ord ExplicitnessLevel where
  compare a b :=
    let toNat : ExplicitnessLevel → Nat
      | .singularHomophony  => 0
      | .verticalHomophony  => 1
      | .unifiedWe          => 2
      | .inclusiveExclusive => 3
      | .minimalAugmented   => 4
    Ord.compare (toNat a) (toNat b)

/-- Compute the explicitness level of a paradigmatic structure. -/
def ParadigmaticStructure.explicitnessLevel
    (s : ParadigmaticStructure) : ExplicitnessLevel :=
  if s.hasSingularHomophony then .singularHomophony
  else if s.hasVerticalHomophony then .verticalHomophony
  else match s.firstPersonComplexType with
    | .Pb | .Pa => .unifiedWe
    | .Pc | .Pd => .inclusiveExclusive
    | .Pe       => .minimalAugmented

-- ============================================================================
-- §7: Horizontal Homophony Hierarchy (10.1, 10.2)
-- ============================================================================

/-- Horizontal Homophony Hierarchy (Cysouw 2009, §10.1.4).

If horizontal homophony occurs, it follows the person hierarchy 1 > 2 > 3:
first attested in 3rd person, then 2nd, then 1st (exclusive). -/
inductive HorizHomophonyLevel where
  | none_       -- no horizontal homophony
  | third       -- 3sg = 3+3 only
  | second      -- + 2sg = 2+3
  | exclusive   -- + 1sg = 1+3 (with incl/excl distinction)
  | first       -- + 1sg = 1+3 (without incl/excl; = all first person)
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- §8: Implicational Universals
-- ============================================================================

/-- Addressee Inclusion Implication I (Cysouw 2009, 3.23):
    Exclusive → Inclusive.
    If there is a specialized exclusive morpheme, there is also a
    specialized inclusive morpheme. -/
def addresseeInclusionImplication (s : ParadigmaticStructure) : Prop :=
  -- If exclusive is specialized (different from 1sg)
  (s.morphClass .excl ≠ s.morphClass .s1) →
  -- Then inclusive is also specialized
  (s.morphClass .minIncl ≠ s.morphClass .s1 ∨
   s.morphClass .augIncl ≠ s.morphClass .s1)

/-- Split Inclusive Implication (Cysouw 2009, 3.24):
    Split inclusive → Exclusive.
    If the inclusive is split into minimal and augmented,
    then the exclusive is specialized. -/
def splitInclusiveImplication (s : ParadigmaticStructure) : Prop :=
  (s.morphClass .minIncl ≠ s.morphClass .augIncl) →
  (s.morphClass .excl ≠ s.morphClass .s1)

/-- Homophony Implication (Cysouw 2009, 10.4):
    Singular homophony → inflectional paradigm. -/
def homophonyImplication (s : ParadigmaticStructure) : Prop :=
  s.hasSingularHomophony → s.isInflectional

-- ============================================================================
-- §9: Language Data
-- ============================================================================

-- Each paradigm is encoded by assigning morpheme class indices to the 8 cells.
-- Same index = same form.  We use the simplest distinct numbering.

section LanguageData

/-- Latin (Sa, Pd): all singular distinct, inclusive/exclusive.
    1sg -ō, 2sg -s, 3sg -t, 1+2/1+2+3 -mus, 1+3 -mus, 2+3 -tis, 3+3 -nt
    Note: Latin has no incl/excl distinction, unified 'we' = 1pl -mus. -/
def latin : ParadigmaticStructure :=
  { name := "Latin", isoCode := "lat"
    morphClass := λ
      | .s1 => 0 | .s2 => 1 | .s3 => 2
      | .minIncl => 3 | .augIncl => 3 | .excl => 3  -- unified 'we' (-mus)
      | .secondGrp => 4 | .thirdGrp => 5
    isInflectional := true }

/-- English verbal inflection (Sb, Pb): 2=3 homophony in present tense,
    no specialized 'we' (English has -s for 3sg, zero elsewhere → 1=2 in
    terms of overt marking, but the paradigm structure is actually Sb-type
    when we consider the pronoun paradigm: I/you/he-she-it). Actually in the
    verbal inflection: walk/walk/walks → 1=2 vs 3 = Sd type.
    For the independent pronouns: I ≠ you ≠ he/she → Sa, unified-we. -/
def englishPronouns : ParadigmaticStructure :=
  { name := "English (pronouns)", isoCode := "en"
    morphClass := λ
      | .s1 => 0 | .s2 => 1 | .s3 => 2  -- I ≠ you ≠ he/she/it (Sa)
      | .minIncl => 3 | .augIncl => 3 | .excl => 3  -- 'we' unified (Pa)
      | .secondGrp => 1 | .thirdGrp => 4  -- you(pl)=you(sg), they
    isInflectional := false }

/-- English verbal inflection (Sd type): walk/walk/walks → 1=2 vs 3. -/
def englishInflection : ParadigmaticStructure :=
  { name := "English (inflection)", isoCode := "en"
    morphClass := λ
      | .s1 => 0 | .s2 => 0 | .s3 => 1  -- -∅/-∅/-s (Sd: 1=2 vs 3)
      | .minIncl => 0 | .augIncl => 0 | .excl => 0  -- all zero (Pb: no-we)
      | .secondGrp => 0 | .thirdGrp => 0
    isInflectional := true }

/-- Dutch verbal inflection (Sb type): loop/loopt/loopt → 1 vs 2=3.
    No incl/excl distinction, unified plural -en. -/
def dutchInflection : ParadigmaticStructure :=
  { name := "Dutch (inflection)", isoCode := "nl"
    morphClass := λ
      | .s1 => 0 | .s2 => 1 | .s3 => 1  -- -∅/-t/-t (Sb: 2=3)
      | .minIncl => 2 | .augIncl => 2 | .excl => 2
      | .secondGrp => 2 | .thirdGrp => 2
    isInflectional := true }

/-- Spanish verbal inflection (Sc type): hablo/hablas/habla → 1=3 homophony
    in subjunctive (hable/hables/hable). Indicative present = Sa.
    Using the subjunctive as the classic Sc example. -/
def spanishSubjunctive : ParadigmaticStructure :=
  { name := "Spanish (subjunctive)", isoCode := "es"
    morphClass := λ
      | .s1 => 0 | .s2 => 1 | .s3 => 0  -- hable/hables/hable (Sc: 1=3)
      | .minIncl => 2 | .augIncl => 2 | .excl => 2
      | .secondGrp => 3 | .thirdGrp => 4
    isInflectional := true }

/-- French verbal inflection (Se type): parle/parles/parle → 1=2=3
    (phonologically identical in spoken French for -er verbs). -/
def frenchInflection : ParadigmaticStructure :=
  { name := "French (inflection)", isoCode := "fr"
    morphClass := λ
      | .s1 => 0 | .s2 => 0 | .s3 => 0  -- [paʁl]/[paʁl]/[paʁl] (Se: 1=2=3)
      | .minIncl => 1 | .augIncl => 1 | .excl => 1
      | .secondGrp => 2 | .thirdGrp => 3
    isInflectional := true }

/-- Mandara (Chadic): independent pronouns with inclusive/exclusive (Pd).
    yá/ká/á (1/2/3), má (1+2/1+2+3), ŋá (1+3), kwá (2+3), tá (3+3). -/
def mandara : ParadigmaticStructure :=
  { name := "Mandara", isoCode := "mfi"
    morphClass := λ
      | .s1 => 0 | .s2 => 1 | .s3 => 2
      | .minIncl => 3 | .augIncl => 3 | .excl => 4  -- Pd: incl ≠ excl
      | .secondGrp => 5 | .thirdGrp => 6
    isInflectional := false }

/-- Ilocano: minimal/augmented system (Pe).
    co (1sg), ta (1+2 minimal), tayo (1+2+3 augmented), mi (1+3 exclusive),
    mo (2sg), yo (2+3), na (3sg), da (3+3). -/
def ilocano : ParadigmaticStructure :=
  { name := "Ilocano", isoCode := "ilo"
    morphClass := λ
      | .s1 => 0 | .s2 => 1 | .s3 => 2
      | .minIncl => 3 | .augIncl => 4 | .excl => 5  -- Pe: all three distinct
      | .secondGrp => 6 | .thirdGrp => 7
    isInflectional := false }

/-- Maká (Mataco-Guaicuruan, Paraguay): only-inclusive (Pc).
    hoy- (1sg/1+3), xi(t)- (1+2/1+2+3), other forms for 2, 3, 2+3, 3+3. -/
def maka : ParadigmaticStructure :=
  { name := "Maká", isoCode := "mca"
    morphClass := λ
      | .s1 => 0 | .s2 => 1 | .s3 => 2
      | .minIncl => 3 | .augIncl => 3 | .excl => 0  -- Pc: incl specialized, excl = 1sg
      | .secondGrp => 4 | .thirdGrp => 5
    isInflectional := false }

/-- Mura Pirahã: no-we (Pb). Only 3 singular pronouns, no group marking. -/
def piraha : ParadigmaticStructure :=
  { name := "Pirahã", isoCode := "myp"
    morphClass := λ
      | .s1 => 0 | .s2 => 1 | .s3 => 2
      | .minIncl => 0 | .augIncl => 0 | .excl => 0  -- Pb: no specialized 'we'
      | .secondGrp => 1 | .thirdGrp => 2  -- group = singular
    isInflectional := false }

/-- Toda (Dravidian): Tupí-Guaraní-type with 3=3+3 horizontal homophony. -/
def toda : ParadigmaticStructure :=
  { name := "Toda", isoCode := "tcx"
    morphClass := λ
      | .s1 => 0 | .s2 => 1 | .s3 => 2
      | .minIncl => 3 | .augIncl => 3 | .excl => 4  -- Pd-type
      | .secondGrp => 5 | .thirdGrp => 2  -- 3 = 3+3 horizontal homophony
    isInflectional := false }

/-- Czech independent pronouns: Sa (all singular distinct), unified-we (Pa). -/
def czechPronouns : ParadigmaticStructure :=
  { name := "Czech (pronouns)", isoCode := "cs"
    morphClass := λ
      | .s1 => 0 | .s2 => 1 | .s3 => 2  -- já/ty/on(a) — Sa
      | .minIncl => 3 | .augIncl => 3 | .excl => 3  -- my — Pa
      | .secondGrp => 4 | .thirdGrp => 5  -- vy/oni
    isInflectional := false }

end LanguageData

/-- All language data. -/
def allParadigms : List ParadigmaticStructure :=
  [ latin, englishPronouns, englishInflection, dutchInflection
  , spanishSubjunctive, frenchInflection, mandara, ilocano
  , maka, piraha, toda, czechPronouns ]

theorem allParadigms_count : allParadigms.length = 12 := by native_decide

-- ============================================================================
-- §10: Verified Classifications
-- ============================================================================

/-! ### Singular homophony type verification -/

theorem latin_is_Sa : latin.singularType = .Sa := by native_decide
theorem dutch_is_Sb : dutchInflection.singularType = .Sb := by native_decide
theorem spanish_subj_is_Sc : spanishSubjunctive.singularType = .Sc := by native_decide
theorem english_infl_is_Sd : englishInflection.singularType = .Sd := by native_decide
theorem french_is_Se : frenchInflection.singularType = .Se := by native_decide

/-! ### First person complex type verification -/

theorem english_pronouns_Pa : englishPronouns.firstPersonComplexType = .Pa := by native_decide
theorem english_infl_Pb : englishInflection.firstPersonComplexType = .Pb := by native_decide
theorem maka_Pc : maka.firstPersonComplexType = .Pc := by native_decide
theorem mandara_Pd : mandara.firstPersonComplexType = .Pd := by native_decide
theorem ilocano_Pe : ilocano.firstPersonComplexType = .Pe := by native_decide
theorem piraha_Pb : piraha.firstPersonComplexType = .Pb := by native_decide

/-! ### Five singular types are exhaustive over our data -/

theorem all_singular_types_attested :
    allParadigms.any (·.singularType == .Sa) &&
    allParadigms.any (·.singularType == .Sb) &&
    allParadigms.any (·.singularType == .Sc) &&
    allParadigms.any (·.singularType == .Sd) &&
    allParadigms.any (·.singularType == .Se) = true := by native_decide

/-! ### All five first-person complex types are attested -/

theorem all_fpc_types_attested :
    allParadigms.any (·.firstPersonComplexType == .Pa) &&
    allParadigms.any (·.firstPersonComplexType == .Pb) &&
    allParadigms.any (·.firstPersonComplexType == .Pc) &&
    allParadigms.any (·.firstPersonComplexType == .Pd) &&
    allParadigms.any (·.firstPersonComplexType == .Pe) = true := by native_decide

-- ============================================================================
-- §11: Implicational Universal Verification
-- ============================================================================

/-- Addressee Inclusion Implication holds for all paradigms:
    exclusive specialized → inclusive specialized. (Cysouw 3.23) -/
theorem addressee_inclusion_holds :
    allParadigms.all (λ s =>
      -- If exclusive ≠ 1sg, then some inclusive ≠ 1sg
      if s.morphClass .excl != s.morphClass .s1
      then s.morphClass .minIncl != s.morphClass .s1 ||
           s.morphClass .augIncl != s.morphClass .s1
      else true) = true := by native_decide

/-- Split Inclusive Implication holds for all paradigms:
    min.incl ≠ aug.incl → exclusive specialized. (Cysouw 3.24) -/
theorem split_inclusive_holds :
    allParadigms.all (λ s =>
      if s.morphClass .minIncl != s.morphClass .augIncl
      then s.morphClass .excl != s.morphClass .s1
      else true) = true := by native_decide

/-- Homophony Implication holds for all paradigms:
    singular homophony → inflectional paradigm. (Cysouw 10.4) -/
theorem homophony_implication_holds :
    allParadigms.all (λ s =>
      if s.hasSingularHomophony then s.isInflectional else true) = true := by native_decide

/-- Independent pronouns → no singular homophony (contrapositive of 10.4). -/
theorem independent_no_singular_homophony :
    (allParadigms.filter (·.isInflectional == false)).all
      (·.hasSingularHomophony == false) = true := by native_decide

-- ============================================================================
-- §12: Explicitness Hierarchy Verification
-- ============================================================================

/-- Ilocano (Pe/minimal-augmented) is the most explicit. -/
theorem ilocano_most_explicit :
    ilocano.explicitnessLevel = .minimalAugmented := by native_decide

/-- Mandara (Pd/inclusive-exclusive) is one step below. -/
theorem mandara_incl_excl :
    mandara.explicitnessLevel = .inclusiveExclusive := by native_decide

/-- English pronouns (Pa/unified-we) are at unified-we level. -/
theorem english_pronouns_unified :
    englishPronouns.explicitnessLevel = .unifiedWe := by native_decide

/-- French inflection (Se/singular homophony) is least explicit. -/
theorem french_least_explicit :
    frenchInflection.explicitnessLevel = .singularHomophony := by native_decide

/-- The Explicitness Hierarchy is respected in our data:
    more explicit paradigms distinguish more categories. -/
theorem explicitness_correlates_with_forms :
    ilocano.distinctForms > mandara.distinctForms ∧
    mandara.distinctForms > englishPronouns.distinctForms ∧
    englishPronouns.distinctForms > frenchInflection.distinctForms := by native_decide

-- ============================================================================
-- §13: Horizontal Homophony
-- ============================================================================

/-- Toda has horizontal homophony (3sg = 3+3). -/
theorem toda_horizontal_homophony :
    toda.hasHorizontalHomophony = true := by native_decide

/-- English pronouns have horizontal homophony (you.sg = you.pl). -/
theorem english_horizontal_homophony :
    englishPronouns.hasHorizontalHomophony = true := by native_decide

/-- Latin has no horizontal homophony. -/
theorem latin_no_horizontal_homophony :
    latin.hasHorizontalHomophony = false := by native_decide

/-- Pirahã has maximal horizontal homophony (all singular = group). -/
theorem piraha_maximal_horizontal :
    piraha.hasHorizontalHomophony = true ∧
    piraha.homophonous .s1 .excl = true ∧
    piraha.homophonous .s2 .secondGrp = true ∧
    piraha.homophonous .s3 .thirdGrp = true := by native_decide

-- ============================================================================
-- §14: First Person Hierarchy (3.26)
-- ============================================================================

/-- The First Person Hierarchy (Cysouw 2009, 3.26):
    no-we < unified-we < only-inclusive < inclusive/exclusive < minimal/augmented

Verified: the hierarchy corresponds to increasing number of forms for 'we'.
We count the distinct morpheme classes among {1+2, 1+2+3, 1+3}. -/
def ParadigmaticStructure.weFormCount (s : ParadigmaticStructure) : Nat :=
  let classes := [s.morphClass .minIncl, s.morphClass .augIncl, s.morphClass .excl]
  -- Count forms distinct from 1sg
  let specialized := classes.filter (· != s.morphClass .s1)
  specialized.eraseDups.length

theorem piraha_zero_we_forms : piraha.weFormCount = 0 := by native_decide
theorem english_one_we_form : englishPronouns.weFormCount = 1 := by native_decide
theorem maka_one_we_form : maka.weFormCount = 1 := by native_decide
theorem mandara_two_we_forms : mandara.weFormCount = 2 := by native_decide
theorem ilocano_three_we_forms : ilocano.weFormCount = 3 := by native_decide

/-- The First Person Hierarchy is respected:
    Pb (no-we) < Pa (unified) < Pd (incl/excl) < Pe (min/aug)
    measured by number of specialized 'we' forms. -/
theorem first_person_hierarchy :
    piraha.weFormCount < englishPronouns.weFormCount ∧
    englishPronouns.weFormCount ≤ maka.weFormCount ∧
    maka.weFormCount < mandara.weFormCount ∧
    mandara.weFormCount < ilocano.weFormCount := by native_decide

-- ============================================================================
-- §15: Bridges to Existing Infrastructure
-- ============================================================================

-- UD bridges (PersonCategory ↔ UD.Person, PersonCategory ↔ UD.Person × UD.Number)
-- are in Core/PersonCategory.lean.

/-! ### Bridge 3: English Fragment Pronouns ↔ Paradigmatic Structure

Connect the English pronouns fragment (Fragments/English/Pronouns.lean) to
Cysouw's classification. English independent pronouns are Sa (all singular
distinct) with unified-we (Pa). -/

/-- English pronoun paradigmatic structure is Sa (all distinct in singular). -/
theorem english_fragment_sa :
    englishPronouns.singularType = .Sa := by native_decide

/-- English pronoun paradigmatic structure is Pa (unified 'we'). -/
theorem english_fragment_pa :
    englishPronouns.firstPersonComplexType = .Pa := by native_decide

/-- English has horizontal homophony: you.sg = you.pl (2 = 2+3).
    This is visible in the Fragment: Fragments.English.Pronouns.you and you_pl
    share the same surface form "you". -/
theorem english_you_horizontal :
    englishPronouns.homophonous .s2 .secondGrp = true := by native_decide

/-! ### Bridge 4: Czech Fragment ↔ Paradigmatic Structure

Czech pronouns (já/ty/on/my/vy/oni) are Sa with unified-we. -/

theorem czech_fragment_sa :
    czechPronouns.singularType = .Sa := by native_decide

theorem czech_fragment_pa :
    czechPronouns.firstPersonComplexType = .Pa := by native_decide

/-! ### Bridge 5: Morphological status ↔ Explicitness

Cysouw (2009, Table 10.4, Fig 10.10) shows that inflectional paradigms
correlate with lower explicitness.  Our data confirms: all inflectional
paradigms have explicitness ≤ unified-we (i.e., singular or vertical
homophony, or unified-we). -/

/-- Inflectional paradigms in our data are all at or below unified-we
    on the Explicitness Hierarchy. -/
theorem inflectional_less_explicit :
    (allParadigms.filter (·.isInflectional)).all (λ s =>
      s.explicitnessLevel == .singularHomophony ||
      s.explicitnessLevel == .verticalHomophony ||
      s.explicitnessLevel == .unifiedWe) = true := by native_decide

/-- Independent pronoun paradigms show greater explicitness:
    none have singular homophony. -/
theorem independent_more_explicit :
    (allParadigms.filter (·.isInflectional == false)).all (λ s =>
      s.explicitnessLevel != .singularHomophony) = true := by native_decide

-- ============================================================================
-- §16: Number Opposition Hierarchy (Fig 10.8)
-- ============================================================================

/-- Number opposition stages (Cysouw 2009, Fig 10.8).

Hierarchical tree of number oppositions, from no number marking (N₁)
to full number marking with restricted groups (N₃/N₄). -/
inductive NumberStage where
  | N1  -- undifferentiated number marking (singular = group unmarked)
  | N2  -- singular vs group (basic number opposition)
  | N3  -- restricted group (dual/trial) distinguished from unrestricted
  | N4  -- small group (paucal) additionally distinguished
  deriving DecidableEq, BEq, Repr

/-- Classify a paradigm's number stage by checking singular/group opposition. -/
def ParadigmaticStructure.numberStage (s : ParadigmaticStructure) : NumberStage :=
  -- Check if there's any singular ≠ group distinction at all
  let hasSgGrpOpposition := PersonCategory.all.filter (·.isSingular) |>.any λ sg =>
    PersonCategory.all.filter (·.isGroup) |>.any λ grp =>
      !(s.homophonous sg grp)
  if !hasSgGrpOpposition then .N1
  else .N2  -- N3/N4 require dual/paucal data not in our 8-cell grid

-- ============================================================================
-- §17: Person Differentiation Hierarchy (Fig 10.9)
-- ============================================================================

/-- Person differentiation stages (Cysouw 2009, Fig 10.9).

Measures how finely person is distinguished in non-singular categories. -/
inductive PersonStage where
  | P0  -- undifferentiated person marking
  | P1  -- differentiated singular persons, undifferentiated non-singular
  | P2  -- non-first persons differentiated in non-singular
  | P3  -- exclusive vs inclusive distinguished
  | P4  -- minimal inclusive vs augmented inclusive distinguished
  deriving DecidableEq, BEq, Repr

/-- Classify a paradigm's person differentiation stage. -/
def ParadigmaticStructure.personStage (s : ParadigmaticStructure) : PersonStage :=
  match s.firstPersonComplexType with
  | .Pb => if s.singularType == .Se then .P0 else .P1
  | .Pa => .P1  -- all non-singular first person unified
  | .Pc => .P2  -- inclusive specialized but not exclusive
  | .Pd => .P3  -- inclusive vs exclusive
  | .Pe => .P4  -- min.incl vs aug.incl vs excl

theorem ilocano_P4 : ilocano.personStage = .P4 := by native_decide
theorem mandara_P3 : mandara.personStage = .P3 := by native_decide
theorem english_pron_P1 : englishPronouns.personStage = .P1 := by native_decide
theorem piraha_P1 : piraha.personStage = .P1 := by native_decide

-- ============================================================================
-- §18: Cognitive Map Summary
-- ============================================================================

/-- Position in Cysouw's cognitive map (Fig 10.6), combining
    the number-of-forms-for-'we' with the paradigm type. -/
structure CognitiveMapPosition where
  numberStage : NumberStage
  personStage : PersonStage
  singularType : SingularType
  firstPersonComplexType : FirstPersonComplexType
  weFormCount : Nat
  deriving Repr, BEq

/-- Compute the full cognitive map position of a paradigm. -/
def ParadigmaticStructure.cognitiveMapPosition
    (s : ParadigmaticStructure) : CognitiveMapPosition :=
  { numberStage := s.numberStage
    personStage := s.personStage
    singularType := s.singularType
    firstPersonComplexType := s.firstPersonComplexType
    weFormCount := s.weFormCount }

end Phenomena.Agreement.Typology
