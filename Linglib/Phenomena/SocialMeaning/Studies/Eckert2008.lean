import Linglib.Core.SocialMeaning
import Linglib.Phenomena.SocialMeaning.ING
import Linglib.Theories.Sociolinguistics.EckertMontague
import Mathlib.Data.Fintype.Basic

/-!
# @cite{eckert-2008} — Variation and the Indexical Field

## Overview

@cite{eckert-2008} argues that the meanings of variables are not precise
or fixed but rather constitute a field of potential meanings — an
*indexical field*, a constellation of ideologically related meanings, any
one of which can be activated in the situated use of the variable. The
field is fluid, and each new activation has the potential to change the
field by building on ideological connections.

## Key theoretical contributions

1. **The indexical field**: a variable's social meaning is not a fixed
   correspondence to a social category but a structured space of
   ideologically linked persona traits. Context selects which region of
   the field is activated.
2. **Stances vs. qualities**: variables directly index interactional
   *stances* (momentary positions). Habitual stances accrete into
   attributed *qualities* (stable character traits) through *stance
   accretion* (@cite{eckert-2008} citing Rauniomaa 2003).
3. **Social types as field anchors**: social types (School Teacher, Nerd
   Girl, Gay Diva) anchor regions of the indexical field, providing
   culturally available clusters of traits.

## Formalization

The central formal contribution is showing that Eckert's stance
accretion is the *same composition operation* as @cite{ochs-1992}'s
indirect indexicality, both instantiated as `Core.SocialMeaning.composeIndex`:

- **Ochs**: SFP → Stance → GenderPole (form indexes stance indexes gender)
- **Eckert**: /t/ variant → Stance → Quality (form indexes stance,
  habitual stance accretes into quality)

Both are matrix products through an intermediate domain. The study file
exercises this parallel with concrete data from Figures 3 and 4.

## Concrete data

- **Figure 1** (Belten High): ordinal leadership data for 7 NCS
  variables × 4 social groups. The key finding: burnout girls lead ALL
  variables, demonstrating that gender effects are mediated through
  social orientation — a generalization of @cite{ochs-1992}'s mediation
  thesis.
- **Figure 3** ((ING)): sign-valued indexical field for the velar/apical
  variants, based on @cite{campbell-kibler-2007}'s experimental data.
- **Figure 4** (/t/ release): stance accretion chain decomposed via
  `composeIndex`, with social type anchoring in quality space.

## Connections

* `Core.SocialMeaning.composeIndex`: the shared composition operation
* `Core.SocialMeaning.IndexicalField`: Eckert's concept, formalized
  as infrastructure in `Core`
* `Phenomena.SocialMeaning.Studies.Ochs1992`: predecessor —
  `composeIndex` was introduced to formalize Ochs's indirect
  indexicality; Eckert generalizes it to stance accretion
* `Theories.Sociolinguistics.EckertMontague`: the Eckert-Montague
  lift operationalizes the mapping from indexical field to compatible
  personae, connecting to @cite{burnett-2019}'s social meaning games
-/

set_option autoImplicit false

namespace Phenomena.SocialMeaning.Studies.Eckert2008

open Core.SocialMeaning
open Phenomena.SocialMeaning.ING
open Sociolinguistics.EckertMontague
open Sociolinguistics.SCM

-- ============================================================================
-- §1. Trait ontology — stances vs. qualities
-- ============================================================================

/-- Whether a trait is a momentary interactional stance or a stable
    attributed quality. @cite{eckert-2008} emphasizes the fluidity
    of this distinction: "anger and cynicism become part of one's
    identity ... through stance accretion." -/
inductive TraitKind where
  /-- Momentary interactional positioning (gray in Figure 4). -/
  | stance
  /-- Stable attributed character trait (black in Figure 4). -/
  | quality
  deriving DecidableEq, Repr

-- ============================================================================
-- §2. The (ING) variable — Figure 3
-- ============================================================================

/-- Bipolar social dimensions of (ING) meaning, from
    @cite{campbell-kibler-2007}'s matched guise experiments.
    Each dimension has a positive pole (indexed by velar) and a
    negative pole (indexed by apical). -/
inductive INGDimension where
  | education       -- educated (+) / uneducated (-)
  | formality       -- formal (+) / relaxed (-)
  | effort          -- effortful (+) / easygoing (-)
  | articulateness  -- articulate/pretentious (+) / inarticulate/unpretentious (-)
  deriving DecidableEq, Repr, Inhabited

instance : Fintype INGDimension where
  elems := {.education, .formality, .effort, .articulateness}
  complete := by intro x; cases x <;> simp

/-- The (ING) indexical field (Figure 3, based on
    @cite{campbell-kibler-2007}).

    Sign-valued: +1 means the variant indexes toward the positive pole
    of the dimension, −1 indexes toward the negative pole. The velar
    variant indexes the positive pole (educated, formal, effortful,
    articulate) on all dimensions; the apical variant indexes the
    negative pole (uneducated, relaxed, easygoing, inarticulate).

    @cite{eckert-2008} notes that context modulates interpretation:
    the velar variant can be heard as *articulate* or *pretentious*
    depending on presupposed indexicality. This context-dependent
    activation is operationalized computationally in
    @cite{burnett-2019}'s RSA model via context-specific priors. -/
def ingField : IndexicalField INGVariant INGDimension where
  association
    | .velar, _ => 1
    | .apical, _ => -1
  order := .second

/-- Perfect anti-correlation: the two (ING) variants are mirror images
    on every dimension. Whatever the velar variant indexes toward, the
    apical variant indexes away from, and vice versa. -/
theorem ing_anticorrelation :
    ∀ d : INGDimension,
    ingField.association .velar d = -(ingField.association .apical d) := by
  intro d; cases d <;> native_decide

/-- The velar variant indexes the positive pole on all dimensions. -/
theorem ing_velar_all_positive :
    ∀ d : INGDimension, ingField.indexes .velar d := by
  intro d; simp only [IndexicalField.indexes, ingField]; cases d <;> native_decide

/-- The two variants contrast on every dimension — (ING) is a
    maximally contrastive binary variable. -/
theorem ing_contrasts_all :
    ∀ d : INGDimension, ingField.contrasts .velar .apical d := by
  intro d; simp only [IndexicalField.contrasts, ingField]
  cases d <;> native_decide

-- ============================================================================
-- §3. /t/ release — stance accretion via composeIndex (Figure 4)
-- ============================================================================

/-- /t/ release variants. Released /t/ (hyperarticulated stop release)
    is the socially meaningful variant; unreleased is unmarked. -/
inductive TReleaseVariant where
  | released
  | unreleased
  deriving DecidableEq, Repr, Inhabited

instance : Fintype TReleaseVariant where
  elems := {.released, .unreleased}
  complete := by intro x; cases x <;> simp

/-- Stances directly indexed by released /t/ (gray labels in Figure 4).
    These are momentary interactional positions: emphasis, anger,
    exasperation, annoyance — a gradient of emotional intensity. -/
inductive TReleaseStance where
  | emphatic
  | angry
  | exasperated
  | annoyed
  deriving DecidableEq, Repr, Inhabited

instance : Fintype TReleaseStance where
  elems := {.emphatic, .angry, .exasperated, .annoyed}
  complete := by intro x; cases x <;> simp

def TReleaseStance.all : List TReleaseStance :=
  [.emphatic, .angry, .exasperated, .annoyed]

/-- Qualities indirectly indexed through stance accretion (black labels
    in Figure 4). These are stable attributed character traits that
    emerge from habitual use of the stances above. -/
inductive TReleaseQuality where
  | educated
  | articulate
  | formal
  | elegant
  | polite
  | effortful
  | prissy
  | clear
  | careful
  deriving DecidableEq, Repr, Inhabited

instance : Fintype TReleaseQuality where
  elems := {.educated, .articulate, .formal, .elegant, .polite,
            .effortful, .prissy, .clear, .careful}
  complete := by intro x; cases x <;> simp

/-- Level 1: released /t/ directly indexes stances.

    The emphatic stance is the strongest direct association; the others
    form a gradient of decreasing emotional intensity. Unreleased /t/
    is unmarked (zero association with all stances). -/
def variantStanceAssoc : TReleaseVariant → TReleaseStance → ℚ
  | .released, .emphatic     => 1
  | .released, .angry        => 3/4
  | .released, .exasperated  => 1/2
  | .released, .annoyed      => 1/4
  | .unreleased, _           => 0

/-- Level 2: habitual stances accrete into perceived qualities.

    Numerical values are modeling choices reflecting qualitative
    descriptions in @cite{eckert-2008}, not values from the paper.
    The emphatic stance is the broadest mediator, contributing to
    articulateness, clarity, education, effort, and weakly to
    formality traits. The exasperated stance mediates prissiness
    (the Gay Diva pathway in @cite{podesva-2007}). Angry mediates
    perceived effort. Annoyed is too transient to accrete. -/
def stanceQualityAssoc : TReleaseStance → TReleaseQuality → ℚ
  | .emphatic,    .articulate => 3/4
  | .emphatic,    .clear      => 3/4
  | .emphatic,    .educated   => 1/2
  | .emphatic,    .effortful  => 1/2
  | .emphatic,    .formal     => 1/4
  | .emphatic,    .elegant    => 1/4
  | .emphatic,    .careful    => 1/4
  | .emphatic,    .polite     => 1/4
  | .angry,       .effortful  => 1/2
  | .exasperated, .prissy     => 3/4
  | .exasperated, .effortful  => 1/2
  | .exasperated, .careful    => 1/4
  | _,            _           => 0

/-- The composed variant → quality association via stance accretion.
    This IS the @cite{ochs-1992} parallel: the same `composeIndex`
    operation that mediates form → stance → gender in Japanese SFPs
    here mediates form → stance → quality for /t/ release.

    composedQuality(v, q) = Σ_s variantStance(v, s) × stanceQuality(s, q) -/
def composedQuality (v : TReleaseVariant) (q : TReleaseQuality) : ℚ :=
  composeIndex variantStanceAssoc stanceQualityAssoc TReleaseStance.all v q

-- ============================================================================
-- §4. Stance accretion theorems
-- ============================================================================

/-- All qualities have positive composed association with released /t/.
    Parallel to @cite{ochs-1992}'s `all_nonexclusive`: indirect
    indexicality through non-negative mediators preserves positivity. -/
theorem all_qualities_positive :
    ∀ q : TReleaseQuality, composedQuality .released q > 0 := by
  intro q; cases q <;> native_decide

/-- Unreleased /t/ has zero association with all qualities — the
    unmarked variant carries no social meaning through this pathway. -/
theorem unreleased_zero :
    ∀ q : TReleaseQuality, composedQuality .unreleased q = 0 := by
  intro q; cases q <;> native_decide

/-- Quality ranking by composed association strength:
    effortful (9/8) > articulate = clear (3/4) > educated (1/2)
    > prissy = careful (3/8) > formal = elegant = polite (1/4).

    Effortful is strongest because it is mediated through three stances
    (emphatic, angry, exasperated). Articulateness and clarity tie as
    the primary emphatic accretions. The formality cluster (formal,
    elegant, polite) is weakest — a secondary association. -/
theorem quality_ranking :
    composedQuality .released .effortful > composedQuality .released .articulate ∧
    composedQuality .released .articulate = composedQuality .released .clear ∧
    composedQuality .released .articulate > composedQuality .released .educated ∧
    composedQuality .released .educated > composedQuality .released .prissy ∧
    composedQuality .released .prissy = composedQuality .released .careful ∧
    composedQuality .released .prissy > composedQuality .released .formal ∧
    composedQuality .released .formal = composedQuality .released .elegant ∧
    composedQuality .released .formal = composedQuality .released .polite := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-- The composed form–quality association factors through the stance
    domain. Parallel to `Ochs1992.mediation_ze_masc`: the mediation
    thesis made computationally explicit. -/
theorem mediation_released_articulate :
    composedQuality .released .articulate =
      variantStanceAssoc .released .emphatic     * stanceQualityAssoc .emphatic     .articulate
    + variantStanceAssoc .released .angry        * stanceQualityAssoc .angry        .articulate
    + variantStanceAssoc .released .exasperated  * stanceQualityAssoc .exasperated  .articulate
    + variantStanceAssoc .released .annoyed      * stanceQualityAssoc .annoyed      .articulate := by
  native_decide

-- ============================================================================
-- §5. Social types — Figure 4
-- ============================================================================

/-- Social types that anchor regions of the /t/ release indexical field
    (boxes in Figure 4). Each type is a culturally available persona
    cluster — a bundle of qualities that provides an interpretive
    anchor for hearers. -/
inductive SocialType where
  | british        -- refined formality
  | schoolTeacher  -- careful precision
  | nerdGirl       -- intellectual emphasis
  | gayDiva        -- expressive prissiness
  deriving DecidableEq, Repr, Inhabited

instance : Fintype SocialType where
  elems := {.british, .schoolTeacher, .nerdGirl, .gayDiva}
  complete := by intro x; cases x <;> simp

/-- Which qualities each social type activates in the /t/ release
    field (spatial regions in Figure 4).

    These are *proto-personae* in the sense of @cite{burnett-2019}'s
    social meaning games: quality bundles that the Eckert-Montague
    lift maps to compatible persona sets. Mappings are based on
    spatial proximity in Figure 4 and textual descriptions. -/
def socialTypeQualities : SocialType → TReleaseQuality → Bool
  -- British: the refined formality cluster (upper region of Figure 4)
  | .british, .educated | .british, .articulate
  | .british, .formal   | .british, .elegant       => true
  -- School Teacher: careful precision cluster (left region)
  -- includes polite (left column in Figure 4, near School Teacher)
  | .schoolTeacher, .educated   | .schoolTeacher, .articulate
  | .schoolTeacher, .formal     | .schoolTeacher, .polite
  | .schoolTeacher, .clear      | .schoolTeacher, .careful
  | .schoolTeacher, .effortful                                 => true
  -- Nerd Girl: intellectual emphasis (upper right)
  -- nerd girls "distanced themselves from teachers" (p.467) — no
  -- effortful/careful (school-teachery traits). "Builds primarily on
  -- the social significance of clear speech" (p.468).
  | .nerdGirl, .educated    | .nerdGirl, .articulate
  | .nerdGirl, .clear                                  => true
  -- Gay Diva: expressive prissiness (lower right of Figure 4)
  -- "prissiness of the teacher's pet" + exasperation (p.469).
  -- FORMAL/ELEGANT/POLITE are on the left side of Figure 4, far
  -- from the Gay Diva region.
  | .gayDiva, .articulate | .gayDiva, .effortful
  | .gayDiva, .prissy     | .gayDiva, .careful         => true
  | _, _                                               => false

/-- All social types include `articulate` — the most central quality
    in the /t/ release field. This reflects the ideological core of
    hyperarticulation as a semiotic resource. -/
theorem all_types_include_articulate :
    ∀ st : SocialType, socialTypeQualities st .articulate = true := by
  intro st; cases st <;> rfl

/-- British and Nerd Girl share `educated` but differ on formality —
    the field branches from education into refinement (British) vs.
    intellectual emphasis (Nerd Girl). -/
theorem educated_branching :
    socialTypeQualities .british .educated = true ∧
    socialTypeQualities .nerdGirl .educated = true ∧
    socialTypeQualities .british .elegant = true ∧
    socialTypeQualities .nerdGirl .elegant = false := ⟨rfl, rfl, rfl, rfl⟩

/-- Nerd Girl's qualities are a subset of School Teacher's. This
    reflects the text: nerd girls' /t/ release "builds primarily
    on the social significance of clear speech, which in turn is
    associated with a school-teachery standard" (p.468). -/
theorem nerdGirl_subset_schoolTeacher :
    ∀ q : TReleaseQuality,
    socialTypeQualities .nerdGirl q = true →
    socialTypeQualities .schoolTeacher q = true := by
  intro q hq; cases q <;> first | rfl | exact absurd hq (by decide)

/-- Prissy is unique to Gay Diva among the four social types. -/
theorem prissy_unique_to_gayDiva :
    socialTypeQualities .gayDiva .prissy = true ∧
    socialTypeQualities .british .prissy = false ∧
    socialTypeQualities .schoolTeacher .prissy = false ∧
    socialTypeQualities .nerdGirl .prissy = false := ⟨rfl, rfl, rfl, rfl⟩

/-- Every quality is activated by at least one social type — the
    four types collectively cover the full quality space. -/
theorem types_cover_all_qualities :
    ∀ q : TReleaseQuality,
    ∃ st : SocialType, socialTypeQualities st q = true := by
  intro q; cases q
  · exact ⟨.british, rfl⟩         -- educated
  · exact ⟨.british, rfl⟩         -- articulate
  · exact ⟨.british, rfl⟩         -- formal
  · exact ⟨.british, rfl⟩         -- elegant
  · exact ⟨.schoolTeacher, rfl⟩   -- polite
  · exact ⟨.schoolTeacher, rfl⟩   -- effortful
  · exact ⟨.gayDiva, rfl⟩         -- prissy
  · exact ⟨.schoolTeacher, rfl⟩   -- clear
  · exact ⟨.schoolTeacher, rfl⟩   -- careful

-- ============================================================================
-- §6. Belten High adolescents — Figure 1
-- ============================================================================

/-- Social categories at Belten High School, Detroit
    (@cite{eckert-2008} Figure 1, based on Eckert 1989, 2000).

    School-oriented *jocks* and urban-oriented *burnouts* define a
    local opposition that cross-cuts gender, creating four social
    groups with distinct patterns of variation. -/
inductive BeltenGroup where
  | jockBoys
  | jockGirls
  | burnoutBoys
  | burnoutGirls
  deriving DecidableEq, Repr, Inhabited

instance : Fintype BeltenGroup where
  elems := {.jockBoys, .jockGirls, .burnoutBoys, .burnoutGirls}
  complete := by intro x; cases x <;> simp

/-- Variables involved in the Northern Cities Shift at Belten High.

    The NCS splits into chronological layers: *older* changes (vowel
    fronting, stabilized across the suburban area, led by girls) and
    *newer* changes (vowel backing, more advanced in the urban center,
    led by burnouts). Negative concord is a syntactic variable. -/
inductive NCSVariable where
  -- older NCS changes (fronting), led by girls
  | ae_raising        -- æ > eə
  | a_fronting        -- a > æ
  | open_o_lowering   -- ɔ > a
  -- newer NCS changes (backing), led by burnouts
  | wedge_backing     -- ʌ > ɔ
  | ay_backing        -- ay > oy
  | epsilon_backing   -- ε > ʌ
  -- syntactic
  | negation          -- negative concord
  deriving DecidableEq, Repr, Inhabited

instance : Fintype NCSVariable where
  elems := {.ae_raising, .a_fronting, .open_o_lowering,
            .wedge_backing, .ay_backing, .epsilon_backing,
            .negation}
  complete := by intro x; cases x <;> simp

/-- Leadership ranking from Figure 1.
    2 = leader (black in figure), 1 = runner-up (gray), 0 = neither.

    Older NCS changes are led by girls (burnout girls lead, jock girls
    runner-up). Newer NCS changes are led by burnouts (burnout girls
    lead, burnout boys runner-up). Negation: burnout girls lead despite
    the overall male tendency for negative concord.

    The key finding: burnout girls are leaders (= 2) across ALL
    variables — they embed the urban–suburban opposition linguistically,
    demonstrating that the gender effect is mediated through social
    orientation, not a direct gender → language mapping. This is
    @cite{ochs-1992}'s mediation thesis generalized to the ethnographic
    domain. -/
def beltenLeadership : BeltenGroup → NCSVariable → ℚ
  -- older, fronting: girls lead (burnout girls > jock girls)
  | .burnoutGirls, .ae_raising       => 2
  | .jockGirls,    .ae_raising       => 1
  | .burnoutGirls, .a_fronting       => 2
  | .jockGirls,    .a_fronting       => 1
  | .burnoutGirls, .open_o_lowering  => 2
  | .jockGirls,    .open_o_lowering  => 1
  -- newer, backing: burnouts lead (burnout girls > burnout boys)
  | .burnoutGirls, .wedge_backing    => 2
  | .burnoutBoys,  .wedge_backing    => 1
  | .burnoutGirls, .ay_backing       => 2
  | .burnoutBoys,  .ay_backing       => 1
  | .burnoutGirls, .epsilon_backing  => 2
  | .burnoutBoys,  .epsilon_backing  => 1
  -- negation: burnout girls lead
  | .burnoutGirls, .negation         => 2
  | .burnoutBoys,  .negation         => 1
  | _,             _                 => 0

/-- **Universal leadership**: burnout girls lead every NCS variable.

    This is the central empirical finding of the Belten High study.
    The burned-out burnout girls led all other burnouts, male and
    female, in all NCS urban variables AND negative concord — despite
    the general population pattern of male-led negation. -/
theorem burnoutGirls_lead_all :
    ∀ v : NCSVariable, beltenLeadership .burnoutGirls v = 2 := by
  intro v; cases v <;> native_decide

/-- No other group leads all variables — burnout girls' universal
    leadership is unique. -/
theorem jockBoys_not_universal :
    ∃ v : NCSVariable, beltenLeadership .jockBoys v < 2 := ⟨.ae_raising, by native_decide⟩

theorem jockGirls_not_universal :
    ∃ v : NCSVariable, beltenLeadership .jockGirls v < 2 := ⟨.wedge_backing, by native_decide⟩

theorem burnoutBoys_not_universal :
    ∃ v : NCSVariable, beltenLeadership .burnoutBoys v < 2 := ⟨.ae_raising, by native_decide⟩

/-- **Gender × orientation interaction**: older variables split by
    gender (jock girls are runners-up), newer variables split by
    social orientation (burnout boys are runners-up). -/
theorem older_runner_up_is_jockGirls :
    beltenLeadership .jockGirls .ae_raising = 1 ∧
    beltenLeadership .jockGirls .a_fronting = 1 ∧
    beltenLeadership .jockGirls .open_o_lowering = 1 := ⟨rfl, rfl, rfl⟩

theorem newer_runner_up_is_burnoutBoys :
    beltenLeadership .burnoutBoys .wedge_backing = 1 ∧
    beltenLeadership .burnoutBoys .ay_backing = 1 ∧
    beltenLeadership .burnoutBoys .epsilon_backing = 1 := ⟨rfl, rfl, rfl⟩

/-- Jock boys never lead or run up — they are the most linguistically
    conservative group, furthest from both the gender-led and
    orientation-led change fronts. -/
theorem jockBoys_never_lead :
    ∀ v : NCSVariable, beltenLeadership .jockBoys v = 0 := by
  intro v; cases v <;> native_decide

-- ============================================================================
-- §7. The Ochs–Eckert bridge
-- ============================================================================

/-- The /t/ release composed association as an `IndexicalField`.

    Parallel to `Ochs1992.composedField`: both lift composed
    association values to the `IndexicalField` type, connecting
    the study-specific composition back to the core infrastructure. -/
def composedField : IndexicalField TReleaseVariant TReleaseQuality where
  association := composedQuality
  order := .second

/-- The composed field indexes released /t/ toward articulateness. -/
theorem composedField_released_indexes_articulate :
    composedField.indexes .released .articulate := by
  simp only [IndexicalField.indexes, composedField]
  native_decide

/-- Released and unreleased /t/ contrast on every quality —
    the composed field is maximally contrastive. -/
theorem composedField_contrasts_all :
    ∀ q : TReleaseQuality, composedField.contrasts .released .unreleased q := by
  intro q; simp only [IndexicalField.contrasts, composedField]
  cases q <;> native_decide

-- ============================================================================
-- §8. ING → SCM bridge — connecting to the Eckert-Montague lift
-- ============================================================================

/-! The (ING) indexical field (§2) lives over `INGDimension` — a
domain-specific 4-axis space derived from @cite{campbell-kibler-2007}.
To connect it to the Eckert-Montague lift (`EckertMontague.emFieldMI`),
we project it to `SocialDimension` (the 3-axis SCM framework from
@cite{fiske-cuddy-glick-2007}).

**Dimension mapping rationale:**
- `education → competence`: education is a core competence indicator
- `formality → antiSolidarity`: formal register indexes social distance
  (pedantic, uptight — the antiSolidarity pole in SCM/BSB2022)
- `effort → competence`: effortful speech signals diligence/precision
- `articulateness → competence`: articulateness is a competence signal

This maps 3 of 4 ING dimensions to competence and 1 to antiSolidarity,
with warmth = 0. @cite{burnett-2019} makes a different choice: mapping
formality to warmth (aloof ≈ cold) rather than antiSolidarity. Both are
defensible — the present mapping follows BSB2022's PCA loadings where
"pedantic/uptight" loaded on an independent factor from warmth.

The sign structure is preserved: velar indexes the positive pole of
all 4 dimensions, so it indexes competent + antiSolidary in SCM. -/

/-- The (ING) indexical field projected to SCM dimensions.

    All three of education, effort, and articulateness collapse to
    competence (same sign for both variants), while formality projects
    to antiSolidarity. Warmth is zero — (ING) carries no warmth signal
    in this analysis. -/
def ingFieldSCM : IndexicalField INGVariant SocialDimension where
  association
    | .velar,  .competence      => 1
    | .velar,  .antiSolidarity  => 1
    | .velar,  .warmth          => 0
    | .apical, .competence      => -1
    | .apical, .antiSolidarity  => -1
    | .apical, .warmth          => 0
  order := .second

/-- The SCM projection preserves the sign structure of the
    domain-specific field: velar is positive on all mapped dimensions,
    apical is negative. -/
theorem ingFieldSCM_signs_match_ingField :
    (∀ d : SocialDimension, ingFieldSCM.association .velar d ≥ 0) ∧
    (∀ d : SocialDimension, ingFieldSCM.association .apical d ≤ 0) := by
  constructor <;> intro d <;> cases d <;> native_decide

/-- The (ING) field grounded in the SCM property space via
    `fromIndexicalField`. This is the same bridge used by
    @cite{beltrama-schwarz-2024} and @cite{beltrama-solt-burnett-2022}
    for round/precise number variants. -/
def ingGroundedField : GroundedField INGVariant scmSpace :=
  fromIndexicalField ingFieldSCM

/-- The velar variant indexes {competent, antiSolidary} in SCM:
    educated, formal, effortful, articulate → competent + socially
    distant. -/
theorem velar_scm_properties :
    ingGroundedField.indexedProperties .velar = {.competent, .antiSolidary} := by
  native_decide

/-- The apical variant indexes {incompetent, solidary} in SCM:
    uneducated, relaxed, easygoing, inarticulate → incompetent +
    solidary/approachable. -/
theorem apical_scm_properties :
    ingGroundedField.indexedProperties .apical = {.incompetent, .solidary} := by
  native_decide

/-- The Eckert-Montague lift applied to the ING grounded field.
    Returns the set of SCM personae compatible with each variant
    via intersection semantics (a persona is compatible iff it shares
    at least one property with the variant's Eckert field). -/
def ingEM (v : INGVariant) : Finset (Finset scmSpace.Property) :=
  emFieldMI ingGroundedField v

/-- The velar variant is compatible with 6 of 8 SCM personae.
    Excluded: {incompetent, warm, solidary} and {incompetent, cold,
    solidary} — the two personae that have neither competent nor
    antiSolidary. -/
theorem velar_em_count :
    (ingEM .velar).card = 6 := by native_decide

/-- The apical variant is compatible with 6 of 8 SCM personae.
    Excluded: {competent, warm, antiSolidary} and {competent, cold,
    antiSolidary} — the two personae that have neither incompetent
    nor solidary. -/
theorem apical_em_count :
    (ingEM .apical).card = 6 := by native_decide

/-- The two variants exclude different personae, confirming that
    the EM lift distinguishes them despite both being compatible
    with most of the persona space. -/
theorem velar_apical_em_differ :
    ingEM .velar ≠ ingEM .apical := by native_decide

end Phenomena.SocialMeaning.Studies.Eckert2008
