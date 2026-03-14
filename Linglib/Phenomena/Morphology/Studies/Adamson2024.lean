import Linglib.Theories.Morphology.DM.NominalStructure
import Linglib.Theories.Morphology.DM.Categorizer
import Linglib.Theories.Morphology.DM.VocabularyInsertion
import Linglib.Fragments.Teop.Nouns
import Linglib.Fragments.Jarawara.PossessedNouns

/-!
# Adamson 2024: Gender Assignment Is Local @cite{adamson-2024}

@cite{adamson-2024} "Gender Assignment Is Local: On the Relation between
Grammatical Gender and Inalienable Possession." *Language* 100(2): 218–264.

## Core claim

The **Gender Locality Hypothesis** (GLH): gender features on n must be
valued only within nP. This restricts the conditioning factors
for gender assignment to elements extremely local to the noun.

## Key consequence for possession

Inalienable possessors are introduced nP-internally (specifier of n with
selectional feature {D}, following Myler 2016), while alienable possessors
are introduced outside nP (specifier of PossP). The GLH therefore predicts:

- **Inalienable possession CAN affect gender** (nP-internal)
- **Alienable possession CANNOT affect gender** (outside nP)

This asymmetry is confirmed in four unrelated languages:

1. **Teop** (Austronesian, Oceanic; §3.1): body-part nouns combine with
   two different n heads — n_{body-part{D}} bearing u[+ANIM] yields
   gender I when iPossessed; n_{alienator} (plain) yields gender II
2. **Jarawara** (Arawan; §3.2): iPossessable roots are licensed only by
   plain n (feminine = unmarked in the [±MASC] system)
3. **Yanyuwa** (Western Pama-Nyungan; §4.1): unvalued gender on n is
   valued by Probe-Goal agreement with the iPossessor DP
4. **Coastal Marind** (Anim; §4.2): *igih* 'name' and *nanVh* 'face'
   inherit possessor's gender via agreement

## Predictions beyond possession (§5)

The GLH predicts that number features on Num (high number) cannot interact
with gender, while number on n (low/derivational number) can. Features
introduced on D (definiteness), T (tense), etc. are all outside nP and
cannot affect gender assignment.

## Connection to Linglib

This module uses types from `Theories/Morphology/DM/NominalStructure.lean`
(the GLH, `NominalPosition`, `PossessionType`), `CatHead` and `PhiBundle`
from `Theories/Morphology/DM/Categorizer.lean` (@cite{kramer-2015}),
`VocabItem` from `Theories/Morphology/DM/VocabularyInsertion.lean`,
and Fragment data from `Fragments/Teop/Nouns.lean` and
`Fragments/Jarawara/PossessedNouns.lean`.
-/

namespace Phenomena.Morphology.Studies.Adamson2024

open Morphology.DM
open Morphology.DM.VI
open Minimalism

-- ============================================================================
-- § 1: GLH + CatHead Bridge
-- ============================================================================

/-- An n head with selectsD licenses an iPossessor in Spec,nP.
    This connects `CatHead.selectsD` to the GLH: the {D} feature
    places the possessor nP-internally, making it gender-relevant. -/
theorem selectsD_implies_local_possessor :
    PossessionType.inalienable.possessorPosition = .specN ∧
    genderLocalityHypothesis .specN = true := ⟨rfl, rfl⟩

/-- Gender features live on the nominal categorizer (n), as established
    by @cite{kramer-2015} and confirmed by @cite{adamson-2024}. -/
theorem categorizer_has_gender_locus :
    CatHead.n_iFem.phi.gender.isSome = true ∧
    CatHead.n_iMasc.phi.gender.isSome = true ∧
    CatHead.n_uFem.phi.gender.isSome = true ∧
    CatHead.n_plain.phi.gender.isNone = true := ⟨rfl, rfl, rfl, rfl⟩

/-- The ANIM-dimension types also carry gender features on n. -/
theorem anim_categorizer_has_gender :
    CatHead.n_iAnim.phi.gender.isSome = true ∧
    CatHead.n_iInanim.phi.gender.isSome = true ∧
    CatHead.n_uAnim.phi.gender.isSome = true := ⟨rfl, rfl, rfl⟩

/-- The GLH targets the nominal categorizer specifically. Verbal and
    adjectival categorizers do not host gender features. -/
theorem glh_targets_nominal_categorizer :
    CatHead.n_plain.cat = .n ∧
    CatHead.v_plain.phi.gender.isNone = true ∧
    CatHead.a_plain.phi.gender.isNone = true := ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- § 2: Teop — Possessee Gender (@cite{adamson-2024} §3.1)
-- ============================================================================

/-- Teop body-part n: bears u[+ANIM] and selectional feature {D}.
    When a body-part root combines with this n, the {D} feature creates
    a specifier position for an iPossessor DP. The u[+ANIM] feature
    results in gender I (animate article *a*). -/
def teopBodyPartN : CatHead where
  cat := .n
  phi := { gender := some ⟨.u, ⟨.anim, .pos⟩⟩ }
  selectsD := true

/-- Teop alienator n: plain n with no gender feature and no iPossessor. -/
def teopAlienatorN : CatHead := CatHead.n_plain

/-- Determine gender from the n head's feature content.
    If n has any [ANIM]-dimension gender feature → gender I;
    otherwise → gender II. -/
def teopGenderFromN (nh : CatHead) : Fragments.Teop.Gender :=
  match nh.phi.gender with
  | some gf => if gf.val.dim == .anim then .gI else .gII
  | none    => .gII

/-- Body-part nouns switch gender because they combine with two different
    n heads. -/
theorem teop_body_part_two_n_heads :
    teopGenderFromN teopBodyPartN = .gI ∧
    teopGenderFromN teopAlienatorN = .gII := ⟨rfl, rfl⟩

/-- The body-part n licenses an iPossessor (has {D}); the alienator n does not. -/
theorem teop_body_part_selectsD :
    teopBodyPartN.selectsD = true ∧
    teopAlienatorN.selectsD = false := ⟨rfl, rfl⟩

/-- The Teop gender alternation is consistent with the GLH. -/
theorem teop_consistent_with_glh :
    PossessionType.inalienable.canAffectGender = true ∧
    PossessionType.alienable.canAffectGender = false := ⟨rfl, rfl⟩

/-- The Teop body-part n uses the ANIM dimension, not the FEM dimension. -/
theorem teop_uses_anim_dimension :
    teopBodyPartN.phi.gender.map (·.val.dim) = some .anim := rfl

/-! ### Teop Vocabulary Insertion -/

/-- Teop article VI rules, ordered by specificity. -/
def teopArticleRules : List (VocabItem Fragments.Teop.ArticleCtx Unit) :=
  [ { exponent := "e"
      contextMatch := λ c => c.gender == .gI && c.proprial
      specificity := 3 }
  , { exponent := "a"
      contextMatch := λ c => c.gender == .gI && !c.plural && !c.proprial
      specificity := 2 }
  , { exponent := "ra"
      contextMatch := λ c => c.gender == .gI && c.plural
      specificity := 2 }
  , { exponent := "o"
      contextMatch := λ c => c.gender == .gII && !c.plural
      specificity := 1 }
  , { exponent := "ro"
      contextMatch := λ c => c.gender == .gII && c.plural
      specificity := 1 }
  ]

theorem teop_ipossessed_body_part_article :
    vocabularyInsert teopArticleRules ⟨.gI, false, false⟩ () = some "a" := by native_decide
theorem teop_unpossessed_body_part_article :
    vocabularyInsert teopArticleRules ⟨.gII, false, false⟩ () = some "o" := by native_decide
theorem teop_proprial_article :
    vocabularyInsert teopArticleRules ⟨.gI, false, true⟩ () = some "e" := by native_decide
theorem teop_plural_gI_article :
    vocabularyInsert teopArticleRules ⟨.gI, true, false⟩ () = some "ra" := by native_decide
theorem teop_plural_gII_article :
    vocabularyInsert teopArticleRules ⟨.gII, true, false⟩ () = some "ro" := by native_decide

/-- End-to-end: body-part root + n_{body-part{D}} → gender I → article *a*. -/
theorem teop_end_to_end_ipossessed :
    vocabularyInsert teopArticleRules
      ⟨teopGenderFromN teopBodyPartN, false, false⟩ () = some "a" := by native_decide

/-- End-to-end: body-part root + n_{alienator} → gender II → article *o*. -/
theorem teop_end_to_end_unpossessed :
    vocabularyInsert teopArticleRules
      ⟨teopGenderFromN teopAlienatorN, false, false⟩ () = some "o" := by native_decide

/-! ### Bridge to Fragment Data

    The study-level `teopGenderFromN` agrees with the Fragment-level
    `iPossessedGender` for body-part nouns: both predict gender I
    when iPossessed, gender II when free. -/

theorem teop_fragment_bridge :
    teopGenderFromN teopBodyPartN = Fragments.Teop.iPossessedGender Fragments.Teop.bina ∧
    teopGenderFromN teopAlienatorN = Fragments.Teop.bina.gender := ⟨rfl, rfl⟩

-- ============================================================================
-- § 3: Jarawara — Possessee Gender (@cite{adamson-2024} §3.2)
-- ============================================================================

/-- Jarawara gender from the n head's feature content. -/
def jarawaraGenderFromN (nh : CatHead) : Bool :=  -- true = masculine
  match nh.phi.gender with
  | some gf => gf.val.dim == .masc
  | none    => false  -- feminine (unmarked)

/-- iPossessable roots in Jarawara are licensed only by plain n (feminine). -/
theorem jarawara_ipossessable_always_fem :
    jarawaraGenderFromN CatHead.n_plain = false := rfl

/-- Masculine nouns in Jarawara bear [+MASC] on n. -/
theorem jarawara_masc_has_feature :
    jarawaraGenderFromN CatHead.n_uMasc = true := rfl

/-! ### Jarawara impoverishment -/

/-- The Jarawara impoverishment rule: [MASC] → ∅ in marked contexts. -/
def jarawaraImpoverishmentRule : ImpoverishmentRule where
  targetGender := ⟨.masc, .pos⟩
  context := "[PL] or [PARTICIPANT]"

/-- Impoverishment deletes [MASC], yielding feminine (unmarked) agreement. -/
theorem jarawara_impoverishment_yields_fem :
    let mascPhi : PhiBundle := { gender := some ⟨.u, ⟨.masc, .pos⟩⟩ }
    let result := jarawaraImpoverishmentRule.apply mascPhi true
    result.gender = none := rfl

/-- Impoverishment does not apply when context is inactive. -/
theorem jarawara_no_impoverishment_when_inactive :
    let mascPhi : PhiBundle := { gender := some ⟨.u, ⟨.masc, .pos⟩⟩ }
    let result := jarawaraImpoverishmentRule.apply mascPhi false
    result.gender = some ⟨.u, ⟨.masc, .pos⟩⟩ := rfl

/-! ### Bridge to Fragment Data

    The 175 iPossessable nouns in 12 semantic classes from `Fragments.Jarawara`
    are drawn from the upper tiers of the inalienability hierarchy,
    confirming the cross-linguistic prediction. -/

theorem jarawara_fragment_total :
    (Fragments.Jarawara.allClasses.map (·.memberCount)).foldl (· + ·) 0 = 175 := by
  native_decide

-- ============================================================================
-- § 4: Inherited Gender — Yanyuwa & Coastal Marind (@cite{adamson-2024} §4)
-- ============================================================================

/-! ### Inherited gender via Probe-Goal agreement

@cite{adamson-2024} §4: in Yanyuwa and Coastal Marind, a small class of
iPossessed nouns (*igih* 'name', *nanVh* 'face' in Coastal Marind; body parts
and 'name' in Yanyuwa) "inherit" the gender of their iPossessor.

In Minimalist terms: the nominalizing head n has an **unvalued** gender
feature. Because the iPossessor DP is in Spec,nP (nP-internal), Probe-Goal
Agree can copy the possessor's valued gender onto n. The GLH permits
this because the goal (iPossessor) is within nP. -/

/-- A gender-inheriting noun: the n head bears an unvalued gender probe
    that is valued by Agree with the iPossessor DP's gender. -/
structure InheritedGenderNoun where
  /-- The root (e.g., √IGIH 'name', √NANVH 'face'). -/
  rootGloss : String
  /-- The n head has {D} (selects an iPossessor). -/
  selectsD : Bool := true
  /-- The n head has an unvalued gender feature (probe). -/
  hasUnvaluedGender : Bool := true
  deriving DecidableEq, BEq, Repr

/-- The n head for an inherited-gender noun: has {D} and unvalued gender. -/
def inheritedGenderN : CatHead where
  cat := .n
  phi := { gender := some ⟨.u, ⟨.anim, .pos⟩⟩ }  -- unvalued; value from possessor
  selectsD := true

/-- Yanyuwa: seven gender classes (Kirton 1971a,b).

    FEMALE, MALE, FEMININE (nonhuman female), MASCULINE (nonhuman male),
    FOOD, ARBOREAL, ABSTRACT. Body parts and 'name' take possessor
    prefixes expressing the possessor's φ-features. -/
inductive YanyuwaGender where
  | female | male | feminine | masculine | food | arboreal | abstract
  deriving DecidableEq, BEq, Repr, Fintype

theorem yanyuwa_seven_genders : Fintype.card YanyuwaGender = 7 := by native_decide

/-- Coastal Marind: four genders (Olsson 2017).

    I (human men, e.g., *yasti* 'old man'), II (human women + animals,
    e.g., *gomna* 'male pig'), III (some inanimates, e.g., *aliki* 'river'),
    IV (other inanimates, e.g., *himbu* 'feathered headdress'). -/
inductive CoastalMarindGender where
  | gI | gII | gIII | gIV
  deriving DecidableEq, BEq, Repr, Fintype

theorem coastalMarind_four_genders :
    Fintype.card CoastalMarindGender = 4 := by native_decide

/-- Coastal Marind inherited-gender nouns (Olsson 2017:187). -/
def coastalMarindInheritingNouns : List InheritedGenderNoun :=
  [ ⟨"igih (name)", true, true⟩
  , ⟨"nanVh (face)", true, true⟩ ]

/-- Both inheriting nouns have {D} and unvalued gender — prerequisites
    for Probe-Goal agreement with the iPossessor. -/
theorem coastalMarind_inheriting_prerequisites :
    coastalMarindInheritingNouns.all (·.selectsD && ·.hasUnvaluedGender) = true := by
  native_decide

/-- Inherited gender is consistent with the GLH: the possessor whose
    gender is inherited is an iPossessor (nP-internal), not an aPossessor. -/
theorem inherited_gender_glh_consistent :
    PossessionType.inalienable.canAffectGender = true := rfl

-- ============================================================================
-- § 5: n-Type System ↔ Surface Gender Counts
-- ============================================================================

/-! ### Bridge: Kramer's n-types and WALS gender counts

@cite{kramer-2015} Ch 3: for a single gender dimension [±VAL], there are
four types of n: i[+VAL], i[−VAL], plain, u[+VAL]. The fourth combination
u[−VAL] is the unmarked default (plain n).

The maximum number of **surface genders** from one dimension is 3:
the positive value, the negative value, and the default (plain).
Two-gender systems arise when only one marked value + plain are attested. -/

/-- Count distinct surface genders from a set of n heads.
    Two n heads produce the same surface gender iff they have the same
    gender feature content (ignoring interpretability, which is only
    visible at LF vs PF). -/
def surfaceGenderClass (nh : CatHead) : Option GenderVal :=
  nh.phi.gender.map (·.val)

/-- The four Amharic n-types yield exactly 3 surface genders:
    [+FEM], [−FEM], and ∅ (plain). Both i[+FEM] and u[+FEM] map to
    the same surface class [+FEM]. -/
theorem amharic_three_surface_genders :
    let classes := [CatHead.n_iFem, CatHead.n_iMasc, CatHead.n_plain, CatHead.n_uFem].map surfaceGenderClass
    classes.eraseDups.length = 3 := by native_decide

/-- A two-gender system (e.g., Jarawara [±MASC]) uses only two n types:
    marked (u[+MASC]) and plain. -/
theorem two_gender_system :
    let classes := [CatHead.n_uMasc, CatHead.n_plain].map surfaceGenderClass
    classes.eraseDups.length = 2 := by native_decide

/-- The Teop two-gender system uses the ANIM dimension. -/
theorem teop_two_gender_system :
    let classes := [CatHead.n_uAnim, CatHead.n_plain].map surfaceGenderClass
    classes.eraseDups.length = 2 := by native_decide

-- ============================================================================
-- § 6: Full Argumentation Chain
-- ============================================================================

/-- The full argumentation chain for Teop:
    1. Body-part n_{body-part{D}} has {D} → iPossessor in Spec,nP
    2. Spec,nP is within nP → GLH allows gender interaction
    3. n_{body-part{D}} has u[+ANIM] → gender I
    4. D agrees with n → article *a* is inserted -/
theorem teop_argumentation_chain :
    teopBodyPartN.selectsD = true ∧
    genderLocalityHypothesis .specN = true ∧
    teopGenderFromN teopBodyPartN = .gI := ⟨rfl, rfl, rfl⟩

end Phenomena.Morphology.Studies.Adamson2024
