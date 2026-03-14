import Linglib.Theories.Morphology.DM.NominalStructure
import Linglib.Theories.Morphology.DM.Categorizer
import Linglib.Theories.Morphology.DM.CategorizerSemantics
import Linglib.Theories.Morphology.DM.VocabularyInsertion
import Linglib.Fragments.Teop.Nouns
import Linglib.Fragments.Jarawara.PossessedNouns
import Linglib.Fragments.Italian.NumberGender

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
def teopBodyPartN : CatHead :=
  .iPoss { gender := some ⟨.u, ⟨.anim, .pos⟩⟩ }

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

/-! ### Five Teop Predictions (@cite{adamson-2024} §3.1)

The two-n analysis generates five testable predictions (p.234–235): -/

/-- Prediction 1: aPossessed body parts → gender II.
    When a body-part root combines with the alienator n (aPossession),
    the result is gender II, not gender I. -/
theorem teop_prediction_apossessed_gII :
    teopGenderFromN teopAlienatorN = .gII := rfl

/-- Prediction 2: the iPossessor's own gender is immaterial.
    The body-part n bears u[+ANIM] regardless of the possessor's features.
    This is *possessee* gender (determined by WHETHER iPossessed), not
    *inherited* gender (determined by possessor's gender value). -/
theorem teop_prediction_possessor_gender_immaterial :
    teopBodyPartN.phi.gender = some ⟨.u, ⟨.anim, .pos⟩⟩ := rfl

/-- Prediction 3: the alienator n has no gender feature and no {D}.
    aPossession is mediated by PossP, not Spec,nP. -/
theorem teop_prediction_alienator_properties :
    teopAlienatorN.phi.gender.isNone = true ∧
    teopAlienatorN.selectsD = false := ⟨rfl, rfl⟩

/-- Prediction 4: any noun combining with n_{body-part{D}} gets gender I,
    not just canonical body parts. Relational nouns with the same structural
    profile (orientation terms, place nouns) also show the alternation. -/
theorem teop_prediction_relational_nouns :
    teopGenderFromN teopBodyPartN = .gI := rfl

/-- Prediction 5: kinship nouns use the alienator n (aPossession),
    so they are always gender II regardless of possession. -/
theorem teop_prediction_kinship_alienator :
    teopGenderFromN teopAlienatorN = .gII ∧
    teopAlienatorN.selectsD = false := ⟨rfl, rfl⟩

-- ============================================================================
-- § 3: Jarawara — Possessee Gender (@cite{adamson-2024} §3.2)
-- ============================================================================

/-- Jarawara gender from the n head's feature content. -/
def jarawaraGenderFromN (nh : CatHead) : Bool :=  -- true = masculine
  match nh.phi.gender with
  | some gf => gf.val.dim == .masc
  | none    => false  -- feminine (unmarked)

/-- The n head for Jarawara iPossessable nouns: has {D} (licenses iPossessor
    in Spec,nP) but no gender feature (feminine = unmarked in the [±MASC]
    system). This is distinct from `CatHead.n_plain` (which has selectsD = false). -/
def jarawaraIPossN : CatHead := .iPoss

/-- iPossessable roots in Jarawara are feminine: their n has no marked gender. -/
theorem jarawara_ipossessable_always_fem :
    jarawaraGenderFromN jarawaraIPossN = false := rfl

/-- iPossessable n in Jarawara has {D} — by construction via `CatHead.iPoss`. -/
theorem jarawara_ipossessable_selectsD :
    jarawaraIPossN.selectsD = true := rfl

/-- Masculine nouns in Jarawara bear [+MASC] on n. -/
theorem jarawara_masc_has_feature :
    jarawaraGenderFromN CatHead.n_uMasc = true := rfl

/-! ### Jarawara impoverishment (@cite{adamson-2024} ex. 63)

Two separate impoverishment rules delete [MASC] in different contexts:
- [MASC] → ∅ / [PL]
- [MASC] → ∅ / [PARTICIPANT]
-/

/-- Impoverishment rule 1: [MASC] → ∅ / [PL]. -/
def jarawaraImpoverishPL : ImpoverishmentRule where
  targetGender := ⟨.masc, .pos⟩
  context := .plural

/-- Impoverishment rule 2: [MASC] → ∅ / [PARTICIPANT]. -/
def jarawaraImpoverishParticipant : ImpoverishmentRule where
  targetGender := ⟨.masc, .pos⟩
  context := .participant

/-- Both rules from ex. 63. -/
def jarawaraImpoverishmentRules : List ImpoverishmentRule :=
  [jarawaraImpoverishPL, jarawaraImpoverishParticipant]

/-- Impoverishment deletes [MASC] when [PL] is active. -/
theorem jarawara_impoverishment_pl :
    let mascPhi : PhiBundle := { gender := some ⟨.u, ⟨.masc, .pos⟩⟩ }
    let result := jarawaraImpoverishPL.apply mascPhi true
    result.gender = none := rfl

/-- Impoverishment deletes [MASC] when [PARTICIPANT] is active. -/
theorem jarawara_impoverishment_participant :
    let mascPhi : PhiBundle := { gender := some ⟨.u, ⟨.masc, .pos⟩⟩ }
    let result := jarawaraImpoverishParticipant.apply mascPhi true
    result.gender = none := rfl

/-- Impoverishment does not apply when context is inactive. -/
theorem jarawara_no_impoverishment_when_inactive :
    let mascPhi : PhiBundle := { gender := some ⟨.u, ⟨.masc, .pos⟩⟩ }
    let result := jarawaraImpoverishPL.apply mascPhi false
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

/-- The n head for an inherited-gender noun: has {D} and an unvalued
    gender probe. The probe is dimension-agnostic — it has no pre-specified
    dimension or polarity. Its value (including dimension) comes entirely
    from the iPossessor DP via Probe-Goal Agree (@cite{adamson-2024} (90)).
    We represent this as `phi := {}` (no valued gender on n itself). -/
def inheritedGenderN : CatHead := .iPoss

/-- Yanyuwa: seven gender classes (Kirton 1971a,b).

    FEMALE, MALE, FEMININE (nonhuman female), MASCULINE (nonhuman male),
    FOOD, ARBOREAL, ABSTRACT. Body parts and 'name' take possessor
    prefixes expressing the possessor's φ-features. -/
inductive YanyuwaGender where
  | female | male | feminine | masculine | food | arboreal | abstract
  deriving DecidableEq, BEq, Repr

/-- All seven Yanyuwa gender values. -/
def YanyuwaGender.all : List YanyuwaGender :=
  [.female, .male, .feminine, .masculine, .food, .arboreal, .abstract]

theorem yanyuwa_seven_genders : YanyuwaGender.all.length = 7 := rfl

/-- Coastal Marind: four genders (Olsson 2017).

    I (human men, e.g., *yasti* 'old man'), II (human women + animals,
    e.g., *gomna* 'male pig'), III (some inanimates, e.g., *aliki* 'river'),
    IV (other inanimates, e.g., *himbu* 'feathered headdress'). -/
inductive CoastalMarindGender where
  | gI | gII | gIII | gIV
  deriving DecidableEq, BEq, Repr

/-- All four Coastal Marind gender values. -/
def CoastalMarindGender.all : List CoastalMarindGender := [.gI, .gII, .gIII, .gIV]

theorem coastalMarind_four_genders :
    CoastalMarindGender.all.length = 4 := rfl

/-- Coastal Marind inherited-gender nouns (Olsson 2017:187). -/
def coastalMarindInheritingNouns : List InheritedGenderNoun :=
  [ ⟨"igih (name)", true, true⟩
  , ⟨"nanVh (face)", true, true⟩ ]

/-- Both inheriting nouns have {D} and unvalued gender — prerequisites
    for Probe-Goal agreement with the iPossessor. -/
theorem coastalMarind_inheriting_prerequisites :
    coastalMarindInheritingNouns.all (λ n => n.selectsD && n.hasUnvaluedGender) = true := by
  native_decide

/-- Inherited gender is consistent with the GLH: the possessor whose
    gender is inherited occupies Spec,nP (nP-internal). -/
theorem inherited_gender_glh_consistent :
    genderLocalityHypothesis PossessionGenderMechanism.inheritedGender.possessorPosition = true := rfl

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
-- § 6: Regression: iPossessable n-heads must have selectsD
-- ============================================================================

/-! Every n-head used for inalienable possession must have `selectsD = true`.
Without this, the n-head cannot license an iPossessor in Spec,nP, and the
semantic pipeline (`catHeadSemanticType`) will compute sortal instead of
relational. This invariant was violated before 0.229.208 (Jarawara used
`CatHead.n_plain` which has selectsD = false). -/

/-- All iPossessable n-heads across all four languages have selectsD = true.
    Regression test: adding a new iPossessable n-head? Add it to the
    disjunction here. If it fails, the n-head is missing {D}. -/
theorem ipossessable_n_heads_have_selectsD
    (nh : CatHead) (h : nh = teopBodyPartN ∨ nh = jarawaraIPossN ∨ nh = inheritedGenderN) :
    nh.selectsD = true := by
  rcases h with rfl | rfl | rfl <;> rfl

-- ============================================================================
-- § 7: Morphosyntax → Semantics Bridge (@cite{adamson-2024} §3.1 + @cite{barker-2011})
-- ============================================================================

/-! ### Two derivation pipelines from a single n-head

A CatHead determines two things in parallel:

```
           ┌──→ gender ──→ article form   (PF pipeline)
CatHead ──┤
           └──→ NSemanticType ──→ can take possessor?   (semantic pipeline)
```

The PF pipeline genuinely threads: `teopGenderFromN` computes the gender,
which feeds into `vocabularyInsert` as the article context. The semantic
pipeline threads similarly: `catHeadSemanticType` computes the semantic
type, which feeds into `.toBarker.canTakePossessor`.

The non-trivial claim is that these two pipelines produce correlated
outputs: gender I co-occurs with relational semantics (possessor slot),
and gender II co-occurs with non-relational (no possessor slot). The
correlation is structural — both paths read `selectsD` from the same
n-head. -/

open Morphology.DM.CategorizerSemantics

/-- The PF derivation pipeline: n-head → gender → article.
    Gender is an intermediate value computed from φ-features, then fed
    into VI as part of the article context. -/
def teopPFDerive (nh : CatHead) (pl proprial : Bool := false) : Option String :=
  let gender := teopGenderFromN nh
  vocabularyInsert teopArticleRules ⟨gender, pl, proprial⟩ ()

/-- The semantic derivation pipeline: n-head → semantic type → possessor capability.
    The semantic type is an intermediate value, fed into Barker's type classification
    to determine whether the noun can directly take a possessor.
    Generic over any CatHead — not Teop-specific despite the examples below. -/
def canTakePossessorSem (nh : CatHead) (mediatesAPoss : Bool := false) : Bool :=
  let semType := catHeadSemanticType nh (mediatesAPossession := mediatesAPoss)
  semType.toBarker.canTakePossessor

-- PF pipeline: body-part n → gender I → article *a*
theorem pf_body_part : teopPFDerive teopBodyPartN = some "a" := by native_decide
-- PF pipeline: alienator n → gender II → article *o*
theorem pf_alienator : teopPFDerive teopAlienatorN = some "o" := by native_decide

-- Semantic pipeline: body-part n (selectsD) → relational → can take possessor
theorem sem_body_part : canTakePossessorSem teopBodyPartN = true := rfl
-- Semantic pipeline: alienator n → alienator type → cannot take possessor
theorem sem_alienator : canTakePossessorSem teopAlienatorN = false := rfl

/-- The two pipelines produce correlated results: the PF pipeline yields
    gender I exactly when the semantic pipeline yields possessor capability.

    This is the Adamson–Barker correspondence. The gender alternation
    (gender I vs II) and the semantic type alternation (relational vs
    non-relational) are not independent — they are both downstream
    consequences of the same structural feature (selectsD on n).

    Stated as a Bool identity: "is gender I" = "can take possessor". -/
theorem pf_semantic_correlation (nh : CatHead)
    (h : nh = teopBodyPartN ∨ nh = teopAlienatorN) :
    (teopGenderFromN nh == .gI) = canTakePossessorSem nh := by
  rcases h with rfl | rfl <;> rfl

/-! ### Jarawara: PF pipeline via manoForm

Jarawara doesn't have articles, but it DOES have a PF pipeline: possessor
features → impoverishment → MARKED feature check → possessed noun form
(mano vs mani). This is the `manoForm` function from `Fragments.Jarawara`.

The semantic pipeline parallels Teop: the iPossessable n has {D} →
relational semantic type → can take possessor. The gender is feminine
because n has no marked gender feature, not because it lacks {D}. -/

/-- Jarawara PF pipeline: possessor features → impoverishment →
    MARKED feature check → possessed form (mano/mani).
    The possessor's features thread through each stage. -/
def jarawaraPFDerive (poss : Fragments.Jarawara.Possessor) : Fragments.Jarawara.PossessedForm :=
  Fragments.Jarawara.manoForm poss

-- PF pipeline: 1SG possessor → [PARTICIPANT] is MARKED → mano
theorem jarawara_pf_1sg : jarawaraPFDerive ⟨.first, .sg, none⟩ = .mascForm := rfl
-- PF pipeline: 3.M.SG → [MASC] survives → mano
theorem jarawara_pf_3msg : jarawaraPFDerive ⟨.third, .sg, some .masc⟩ = .mascForm := rfl
-- PF pipeline: 3.M.PL → [MASC] impoverished by [PL] → mani
theorem jarawara_pf_3mpl : jarawaraPFDerive ⟨.third, .pl, some .masc⟩ = .femForm := rfl

/-- Jarawara iPossessable n has {D} → relational semantic type.
    The n head licenses an iPossessor AND yields relational (π) semantics. -/
theorem jarawara_ipossessable_is_relational :
    catHeadSemanticType jarawaraIPossN = .relational := rfl

/-- Jarawara PF–semantic correlation: iPossessable n yields feminine gender
    (no marked feature) AND relational semantics (has {D}). The correlation
    shows that Jarawara iPossessable nouns CAN take possessors despite
    being feminine — femininity reflects the absence of a gender feature,
    not the absence of a possessor slot. -/
theorem jarawara_pf_semantic :
    jarawaraGenderFromN jarawaraIPossN = false ∧
    canTakePossessorSem jarawaraIPossN = true := ⟨rfl, rfl⟩

/-! ### Inherited gender: the GLH contrast

For Yanyuwa and Coastal Marind, the n-head has {D} → relational semantics.
The key GLH prediction is a contrast: iPossessors (specN) can affect gender,
aPossessors (specPoss) cannot. The contrast is captured by the GLH function
applied to two different positions — not a chain, just two evaluations of
the same predicate on different inputs. -/

/-- The inherited-gender n head has {D} → relational semantic type.
    Gender is unvalued on n and comes from the iPossessor via Agree. -/
theorem inherited_gender_is_relational :
    catHeadSemanticType inheritedGenderN = .relational := rfl

/-- The GLH contrast: iPossessors can affect gender, aPossessors cannot.
    This is not a derivation — it's two evaluations of `genderLocalityHypothesis`
    on the two possessor positions. The function does the work. -/
theorem glh_contrast :
    genderLocalityHypothesis PossessionType.inalienable.possessorPosition = true ∧
    genderLocalityHypothesis PossessionType.alienable.possessorPosition = false := ⟨rfl, rfl⟩

-- ============================================================================
-- § 8: Italian Low-Number Gender Interaction (@cite{adamson-2024} §5.1)
-- ============================================================================

/-! ### Beyond possession: number position and gender

@cite{adamson-2024} §5.1 extends the GLH beyond possession: if gender
features sit on n, then OTHER features on n should also interact with
gender. Number features on n (low/derivational number) are within nP
and can interact with gender; number features on Num (high/inflectional)
are outside nP and cannot.

Standard Italian confirms this: the -a plural class (*braccio* → *braccia*
'arm → arms') changes gender from masculine to feminine. These are low-number
plurals (number on n). Regular -i plurals (*libro* → *libri*) preserve
gender — they involve high number (on Num).

The same function (`genderLocalityHypothesis`) that predicts possession–gender
interaction in Teop and Jarawara also predicts number–gender interaction in
Italian. The GLH is a single principle applied to different feature types. -/

open Fragments.Italian.NumberGender

/-- The Italian data confirms the GLH prediction: gender changes in the
    plural track the number position. Verified over the full noun inventory.
    The pipeline (`numberGenderPipeline`) composes
    PluralClass → NumberPosition → NominalPosition → GLH. -/
theorem italian_fragment_bridge :
    allNouns.all (fun n =>
      n.genderChanges == n.pluralClass.canAffectGender) = true := by
  native_decide

/-- Cross-linguistic convergence: the -a plural class is dominated by
    body parts (6 of 9). Body parts drive gender interaction in ALL
    four languages examined:
    - Teop: body parts switch gender I/II with iPossession
    - Jarawara: body parts are always iPossessable (feminine)
    - Yanyuwa/Coastal Marind: body parts inherit possessor's gender
    - Italian: body parts show the -a plural gender alternation -/
theorem italian_body_part_dominance :
    (aPluralNouns.filter (fun n =>
      ["arm", "finger", "knee", "lip", "bone", "eyebrow"].contains n.gloss)).length = 6 := by
  native_decide

end Phenomena.Morphology.Studies.Adamson2024
