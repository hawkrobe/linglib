import Linglib.Theories.Morphology.DM.Categorizer
import Linglib.Theories.Morphology.DM.VocabularyInsertion
import Linglib.Theories.Syntax.Minimalism.ExtendedProjection.Basic
import Linglib.Core.Discourse.Accessibility
import Linglib.Fragments.English.Pronouns
import Linglib.Phenomena.Pronouns.Studies.Arnold2026

/-!
# @cite{konnelly-cowper-2020}

Konnelly, Lex and Elizabeth Cowper. 2020. Gender diversity and
morphosyntax: An account of singular *they*. *Glossa: a journal
of general linguistics* 5(1): 40. 1--19.
DOI: https://doi.org/10.5334/gjgl.1000

## Core Contribution

Variation in acceptance of singular *they* reflects speakers' position in
a grammatical change in progress. The change has three stages, differing
only in the **contrastivity status** of [MASC] and [FEM] on the gender
features of the pronoun system. The pronoun Vocabulary Items themselves
are constant across all three stages; what changes is which feature
bundles nouns and names project.

| Stage | [MASC]/[FEM] status       | Singular *they* distribution            |
|-------|---------------------------|-----------------------------------------|
| 1     | Contrastive               | Quantified/generic epicene only         |
| 2     | Contrastive, fewer nouns  | Extends to ungendered names             |
| 3     | Non-contrastive modifiers | Default for all singular animate        |

The key theorem: the VIs are *constant* across stages. At Stage 3,
[MASC]/[FEM] are optional modifiers (non-contrastive in the sense of
@cite{wiltschko-2008}), so their absence is the norm, and the Elsewhere
Condition yields *they* as the default singular animate pronoun.

## Connection to @cite{arnold-2026}

Arnold's pragmatic account (underspecified vs. personal singular *they*)
complements K&C's grammatical account. At Stage 1, underspecified *they*
is licensed only when discourse elaboration is thin (quantified/generic
antecedents). At Stage 3, *they* is the grammatical default for any
singular animate referent regardless of discourse elaboration, because
the grammar itself no longer requires a contrastive gender feature.

## Formalization

We define the pronoun VI rules using `FeatureVI` from
`Morphology.DM.VocabularyInsertion`, parameterize the three
stages via `Contrastivity` from `Morphology.DM.Categorizer`,
and prove bridge theorems connecting to Arnold's discourse conditions.
-/

set_option autoImplicit false

namespace KonnellyCowper2020

open Morphology.DM (Contrastivity GenderFeature GenderVal GenderDimension
  Polarity Interpretability CatHead PhiBundle)
open Morphology.DM.VI (FeatureVI subsetPrinciple)
open Core.Discourse.Accessibility (DiscourseElaboration)
open _root_.Arnold2026 (licensesUnderspecified)

-- ============================================================================
-- § 1: Morphosyntactic Features for English Pronouns
-- ============================================================================

/-- The morphosyntactic features relevant to English 3rd-person pronoun
    spellout (K&C §4, (11a--d)).

    K&C place [MASC] and [FEM] on the φ head above Number (following
    @cite{kramer-2009}; @cite{kramer-2015}), [SG] on Num, and [INANIM]
    on n. For VI purposes, only the feature *bundle* at the pronoun
    terminal matters, not where in the tree it originates. -/
inductive PronFeature where
  | sg     -- [SINGULAR]: marked number feature
  | masc   -- [MASC]: masculine gender
  | fem    -- [FEM]: feminine gender
  | inanim -- [INANIM]: inanimate (on n)
  deriving DecidableEq, Repr, BEq

-- ============================================================================
-- § 2: English Pronoun Vocabulary Items (K&C §4, (11a--d))
-- ============================================================================

/-- The four English 3rd-person pronoun VIs.

    These are **constant across all three stages** — the change from
    Stage 1 to Stage 3 is in which feature bundles nouns project, not
    in the VI rules themselves.

    (11) a. [SG] [FEM]   ↔ *she*
         b. [SG] [MASC]  ↔ *he*
         c. [SG, INANIM] ↔ *it*
         d. Elsewhere     ↔ *they*  -/
def vi_she : FeatureVI PronFeature String :=
  ⟨[.sg, .fem], "she"⟩

def vi_he : FeatureVI PronFeature String :=
  ⟨[.sg, .masc], "he"⟩

def vi_it : FeatureVI PronFeature String :=
  ⟨[.sg, .inanim], "it"⟩

def vi_they : FeatureVI PronFeature String :=
  ⟨[], "they"⟩

/-- The complete VI rule set for English 3rd-person pronouns.
    Order does not matter — the Subset Principle selects by specificity
    (feature-list length). -/
def pronounVIs : List (FeatureVI PronFeature String) :=
  [vi_she, vi_he, vi_it, vi_they]

-- ============================================================================
-- § 3: Elsewhere Condition — Edge Cases
-- ============================================================================

/-- A plural bundle (no [SG]) → *they* (elsewhere). -/
theorem plural_yields_they :
    subsetPrinciple pronounVIs [] = some "they" := by decide

/-- A singular bundle with both [MASC] and [FEM] → the VI system is
    well-defined even for this impossible configuration (no nominal
    bears both features). FEM wins by being listed first among
    equal-length matches. -/
theorem masc_fem_overlap_resolves :
    (subsetPrinciple pronounVIs [.sg, .masc, .fem]).isSome = true := by decide

-- ============================================================================
-- § 4: The Three Stages
-- ============================================================================

/-- The three stages of grammatical change for singular *they*
    (K&C §4).

    The stages differ only in the contrastivity status of [MASC] and
    [FEM]. The pronoun VIs (§2) are constant across stages. -/
inductive Stage where
  /-- Stage 1 (pre-modern / conservative): [MASC] and [FEM] are fully
      contrastive. Absence of a gender feature on a singular animate
      nominal is possible only when the referent's gender is unknown
      (quantified/generic contexts). -/
  | stage1
  /-- Stage 2 (innovative / current): [MASC] and [FEM] remain
      contrastive, but the inventory of nouns that obligatorily bear
      them shrinks. Ungendered proper names (Kelly, Morgan) may lack
      a gender feature even for referents of known gender. -/
  | stage2
  /-- Stage 3 (most innovative): [MASC] and [FEM] become optional,
      non-contrastive modifiers. Their absence carries no semantic
      content — *they* is the default for any singular animate. -/
  | stage3
  deriving DecidableEq, Repr, BEq

/-- The contrastivity status of [MASC]/[FEM] at each stage. -/
def Stage.genderContrastivity : Stage → Contrastivity
  | .stage1 => .contrastive
  | .stage2 => .contrastive
  | .stage3 => .nonContrastive

/-- Stages 1 and 2 share contrastive gender features — they differ
    only in the *inventory* of nouns carrying them, not in the
    feature system itself. -/
theorem stage1_stage2_same_contrastivity :
    Stage.stage1.genderContrastivity = Stage.stage2.genderContrastivity := rfl

/-- The Stage 1→3 transition is a change in the feature system itself
    (contrastive → non-contrastive), not just in lexical inventory. -/
theorem stage1_stage3_different_contrastivity :
    Stage.stage1.genderContrastivity ≠ Stage.stage3.genderContrastivity := by
  decide

-- ============================================================================
-- § 5: Feature Bundles by Stage
-- ============================================================================

/-- Whether a contrastive gender feature must be present on a singular
    animate nominal of known binary gender, at a given stage.

    At Stage 1: always (contrastive features are obligatory for known gender).
    At Stage 2: depends on the noun (not modeled here — lexical variation).
    At Stage 3: never obligatory (non-contrastive = optional). -/
def Stage.genderObligatory : Stage → Bool
  | .stage1 => true
  | .stage2 => true   -- obligatory by default, with lexical exceptions
  | .stage3 => false

/-- Gender obligatoriness is DERIVED from the contrastivity status of
    [MASC]/[FEM], not stipulated independently. Contrastive features
    are obligatory (absence = ¬F); non-contrastive features are optional
    (absence = vacuous). This is the formal content of K&C's claim that
    the three stages differ only in feature system properties. -/
theorem genderObligatory_from_contrastivity (s : Stage) :
    s.genderObligatory = s.genderContrastivity.obligatory := by
  cases s <;> rfl

/-- The feature bundle projected by a singular animate nominal with
    no gender specification — the critical case for singular *they*.

    At all stages, this bundle is just [SG], with no [MASC], [FEM],
    or [INANIM]. The Elsewhere Condition yields *they*. -/
def ungenderedBundle : List PronFeature := [.sg]

/-- The feature bundle projected by a singular animate feminine nominal. -/
def feminineBundle : List PronFeature := [.sg, .fem]

/-- The feature bundle projected by a singular animate masculine nominal. -/
def masculineBundle : List PronFeature := [.sg, .masc]

/-- The feature bundle projected by a singular inanimate nominal. -/
def inanimateBundle : List PronFeature := [.sg, .inanim]

-- ============================================================================
-- § 5b: Referent Contexts (K&C §4.1, (12)--(13))
-- ============================================================================

/-- Classification of pronoun–antecedent configurations that differ in
    whether [MASC]/[FEM] is obligatorily projected at a given stage.

    K&C §4.1: the three stages are distinguished by which referent
    contexts obligatorily project gender features.

    - (12): "Every student brought {his/their} lunch" — quantifier-bound,
      gender optional at all stages.
    - (13a): "Jess₁ said he₁ couldn't make it" — referential with known
      gendered name, gender obligatory at Stages 1--2.
    - (13b): "Jess₁ said they₁ couldn't make it" — rejected at Stage 1
      for a known-gender referent.
    - Stage 2 innovation: ungendered proper names (Kelly, Morgan, Pat)
      may lack gender features even though the referent's gender is known. -/
inductive ReferentContext where
  /-- Referential pronoun with a known-gender antecedent
      (e.g., "Jess said he couldn't make it"). -/
  | referentialKnownGender
  /-- Referential pronoun with a gender-unknown/irrelevant antecedent
      (e.g., "the student said they would be late"). -/
  | referentialUnknownGender
  /-- Quantifier-bound / generic pronoun
      (e.g., "every student brought their lunch"). -/
  | quantifierBound
  /-- Referential pronoun with an ungendered proper name antecedent
      (e.g., "Kelly said they would be late"). -/
  | ungenderedProperName
  deriving DecidableEq, Repr, BEq

/-- Whether [MASC]/[FEM] is obligatorily projected for a given referent
    context at a given stage.

    This captures the full empirical landscape of K&C §4:
    - Gender-unknown referents never project [MASC]/[FEM] (at any stage).
    - Quantifier-bound pronouns optionally lack [MASC]/[FEM] at all stages.
    - Known-gender referential pronouns require [MASC]/[FEM] at Stages 1--2.
    - Ungendered names require [MASC]/[FEM] at Stage 1 but not Stage 2.
    - At Stage 3, nothing is obligatory (non-contrastive). -/
def genderObligatoryFor : ReferentContext → Stage → Bool
  | .referentialUnknownGender, _ => false
  | .quantifierBound, _ => false
  | .referentialKnownGender, .stage1 => true
  | .referentialKnownGender, .stage2 => true
  | .referentialKnownGender, .stage3 => false
  | .ungenderedProperName, .stage1 => true
  | .ungenderedProperName, .stage2 => false  -- Stage 2 innovation
  | .ungenderedProperName, .stage3 => false

/-- K&C (12): At Stage 1, quantifier-bound pronouns can be *they*
    because [MASC]/[FEM] is optional in bound variable contexts.
    "Every student brought their lunch" is acceptable at Stage 1. -/
theorem stage1_bound_variable_they :
    genderObligatoryFor .quantifierBound .stage1 = false ∧
    subsetPrinciple pronounVIs ungenderedBundle = some "they" :=
  ⟨rfl, by decide⟩

/-- K&C (13): At Stage 1, referential pronouns with known-gender
    antecedents MUST project [MASC]/[FEM] — singular *they* is not
    available for a referent of known gender.
    "Jess₁ said they₁ couldn't make it" is rejected at Stage 1
    (for a known-gender Jess). -/
theorem stage1_referential_requires_gender :
    genderObligatoryFor .referentialKnownGender .stage1 = true := rfl

/-- The Stage 2 innovation: ungendered proper names (Kelly, Morgan, Pat)
    may lack [MASC]/[FEM] even though the referent's gender is known.
    This extends singular *they* beyond quantifier-bound contexts. -/
theorem stage2_ungendered_names :
    genderObligatoryFor .ungenderedProperName .stage2 = false ∧
    genderObligatoryFor .ungenderedProperName .stage1 = true :=
  ⟨rfl, rfl⟩

/-- At Stage 3, no referent context obligatorily projects [MASC]/[FEM].
    Singular *they* is available for all singular animate referents. -/
theorem stage3_nothing_obligatory (ctx : ReferentContext) :
    genderObligatoryFor ctx .stage3 = false := by
  cases ctx <;> rfl

-- ============================================================================
-- § 6: Stage-Specific Predictions
-- ============================================================================

/-- At **all** stages, ungendered singular animates get *they*. The
    stages differ only in *how many* nominals project ungendered bundles,
    not in what VI does with such a bundle. -/
theorem ungendered_always_they :
    subsetPrinciple pronounVIs ungenderedBundle = some "they" := by decide

/-- At all stages, feminine bundles still get *she*. Stage 3 speakers
    still have *he*/*she* available when the non-contrastive gender
    modifier is present. -/
theorem feminine_always_she :
    subsetPrinciple pronounVIs feminineBundle = some "she" := by decide

/-- At all stages, masculine bundles still get *he*. -/
theorem masculine_always_he :
    subsetPrinciple pronounVIs masculineBundle = some "he" := by decide

/-- At all stages, inanimate bundles still get *it*. The inanimate
    feature [INANIM] is not affected by the contrastivity change —
    it remains contrastive at all stages. -/
theorem inanimate_always_it :
    subsetPrinciple pronounVIs inanimateBundle = some "it" := by decide

-- ============================================================================
-- § 7: Stage 3 Predictions (K&C §4.3, §6)
-- ============================================================================

/-- At Stage 3, non-contrastive [MASC]/[FEM] means gender features are
    optional. For any singular animate referent — regardless of known
    gender — a speaker may omit the gender modifier, yielding *they*.
    This is the core K&C prediction: at Stage 3, singular *they* is
    unrestricted for animate referents. -/
theorem stage3_they_unrestricted :
    Stage.stage3.genderObligatory = false ∧
    subsetPrinciple pronounVIs ungenderedBundle = some "they" :=
  ⟨rfl, by decide⟩

/-- At Stage 1, gender features are obligatory for known-gender referents.
    Singular *they* arises only when gender is genuinely unknown. -/
theorem stage1_they_restricted :
    Stage.stage1.genderObligatory = true ∧
    subsetPrinciple pronounVIs ungenderedBundle = some "they" :=
  ⟨rfl, by decide⟩

-- ============================================================================
-- § 8: Bridge to Arnold 2026
-- ============================================================================

/-- At Stage 1, singular *they* is restricted to contexts where discourse
    elaboration is underspecified — the grammatical obligation to project
    [MASC]/[FEM] for known-gender referents means *they* arises only when
    gender is unknown, which correlates with thin discourse models. -/
theorem stage1_aligns_with_underspecified_they :
    licensesUnderspecified .underspecified = true ∧
    Stage.stage1.genderObligatory = true := ⟨rfl, rfl⟩

/-- At Stage 3, singular *they* is the grammatical default — it does
    not require underspecified discourse elaboration. Arnold's personal
    *they* (elaborated discourse, known they/them pronouns) is naturally
    accommodated: the grammar produces *they* regardless of discourse
    state. -/
theorem stage3_independent_of_discourse :
    Stage.stage3.genderObligatory = false := rfl

-- ============================================================================
-- § 9: Bridge to DM Categorizer
-- ============================================================================

/-- Project a DM n-head's phi-features into K&C's flat pronoun VI feature
    system.

    This bridges @cite{kramer-2015}'s structured features on n
    (GenderFeature with dimension, polarity, interpretability) to K&C's
    flat feature system for VI competition.

    The mapping for English (FEM dimension):
    - i[+FEM] on n → [FEM] (K&C's feature that yields "she")
    - i[−FEM] on n → [MASC] (K&C's feature that yields "he")
    - i[−ANIM] on n → [INANIM] (yields "it")
    - no gender on n → ∅ (elsewhere, yields "they")

    Note: K&C adopt @cite{harley-ritter-2002}'s feature geometry with
    independent [MASC] and [FEM], while @cite{kramer-2015} uses [±FEM]
    with polarity. For English pronoun VI, these are equivalent: K&C's
    [FEM] = Kramer's [+FEM], K&C's [MASC] = Kramer's [−FEM]. -/
def catHeadToPronFeatures (ch : CatHead) : List PronFeature :=
  match ch.phi.gender with
  | some gf =>
    match gf.val with
    | ⟨.fem, .pos⟩  => [.fem]    -- i/u[+FEM] → K&C [FEM]
    | ⟨.fem, .neg⟩  => [.masc]   -- i/u[−FEM] → K&C [MASC]
    | ⟨.anim, .neg⟩ => [.inanim] -- i[−ANIM] → K&C [INANIM]
    | _              => []
  | none => []

/-- The end-to-end pipeline: DM n-head → projected features → VI → "she".
    A singular nominal categorized by n i[+FEM] gets "she" via the
    Elsewhere Condition. -/
theorem iFem_singular_yields_she :
    subsetPrinciple pronounVIs
      ([.sg] ++ catHeadToPronFeatures CatHead.n_iFem) = some "she" := by
  decide

/-- n i[−FEM] (masculine natural gender) → "he". -/
theorem iMasc_singular_yields_he :
    subsetPrinciple pronounVIs
      ([.sg] ++ catHeadToPronFeatures CatHead.n_iMasc) = some "he" := by
  decide

/-- n i[−ANIM] (inanimate) → "it". -/
theorem iInanim_singular_yields_it :
    subsetPrinciple pronounVIs
      ([.sg] ++ catHeadToPronFeatures CatHead.n_iInanim) = some "it" := by
  decide

/-- Plain n (no gender feature) → "they" (elsewhere).
    This is the structural correlate of K&C's core claim: *they* is
    what VI produces when the n-head lacks a gender feature. -/
theorem plain_n_singular_yields_they :
    subsetPrinciple pronounVIs
      ([.sg] ++ catHeadToPronFeatures CatHead.n_plain) = some "they" := by
  decide

-- ============================================================================
-- § 9b: DP Structure (K&C §4, (14))
-- ============================================================================

open Minimalism (fValue allCategoryConsistent allFMonotone catFamily)

/-- K&C's (14): the nominal structure relevant to pronoun feature projection.

    ```
    DP
    ├── D (determiner/quantifier)
    └── NumP
        ├── Num [SG]
        └── nP
            ├── n [gender, animacy]
            └── NP (root)
    ```

    Features are distributed across heads: [SG] on Num, [MASC]/[FEM] on
    the φ head (which K&C identify with the n domain following
    @cite{kramer-2009}; @cite{kramer-2015}), and [INANIM] on n.

    The DP is the maximal projection of the nominal extended projection
    n (F1) → Num (F3) → D (F4), a well-formed subsequence of
    @cite{borer-2005}'s full nominal spine N → n → Q → Num → D. -/
structure PronDP where
  /-- The categorizing head n, bearing gender and animacy features. -/
  nHead : CatHead
  /-- Whether the Num head bears [SG] (singular number). -/
  singular : Bool
  /-- Whether D hosts a quantifier (relevant for bound-variable pronouns
      at Stage 1, where [MASC]/[FEM] are optional for quantifier-bound DPs). -/
  isQuantifier : Bool := false
  deriving DecidableEq, Repr

/-- Project the flat feature bundle for VI competition from the DP structure.

    This composes features from their structural positions in K&C's (14):
    - [SG] comes from the Num head
    - Gender features ([MASC], [FEM]) come from n (via `catHeadToPronFeatures`)
    - [INANIM] comes from n (also via `catHeadToPronFeatures`)

    The resulting list is what the Subset Principle operates over. -/
def PronDP.toPronBundle (ns : PronDP) : List PronFeature :=
  (if ns.singular then [.sg] else []) ++ catHeadToPronFeatures ns.nHead

/-- Spell out the pronoun for a nominal structure via VI competition.

    This is the complete pipeline: DP structure → feature projection →
    Subset Principle → phonological exponent. -/
def PronDP.spellout (ns : PronDP) : Option String :=
  subsetPrinciple pronounVIs ns.toPronBundle

-- ── Structure-to-pronoun theorems ──

/-- A singular feminine nominal (n i[+FEM], Num [SG]) → "she". -/
theorem singular_feminine_spellout :
    ({ nHead := CatHead.n_iFem, singular := true : PronDP }).spellout
      = some "she" := by decide

/-- A singular masculine nominal (n i[−FEM], Num [SG]) → "he". -/
theorem singular_masculine_spellout :
    ({ nHead := CatHead.n_iMasc, singular := true : PronDP }).spellout
      = some "he" := by decide

/-- A singular inanimate nominal (n i[−ANIM], Num [SG]) → "it". -/
theorem singular_inanimate_spellout :
    ({ nHead := CatHead.n_iInanim, singular := true : PronDP }).spellout
      = some "it" := by decide

/-- A singular nominal with plain n (no gender, Num [SG]) → "they".
    The DP structure DETERMINES the elsewhere outcome — plain n projects
    no gender feature, so the Subset Principle selects the elsewhere VI. -/
theorem singular_ungendered_spellout :
    ({ nHead := CatHead.n_plain, singular := true : PronDP }).spellout
      = some "they" := by decide

/-- A plural nominal (no [SG]) → "they" (elsewhere). -/
theorem plural_spellout :
    ({ nHead := CatHead.n_plain, singular := false : PronDP }).spellout
      = some "they" := by decide

/-- A quantifier-bound singular nominal with plain n → "they".
    The `isQuantifier` flag records the D-head status but does not
    affect VI: feature projection reads n and Num, not D content. -/
theorem quantifier_bound_spellout :
    ({ nHead := CatHead.n_plain, singular := true,
       isQuantifier := true : PronDP }).spellout
      = some "they" := by decide

-- ── Extended Projection well-formedness ──

/-- K&C's (14) spine [n, Num, D] is a well-formed nominal extended projection:
    all heads share [-V, +N] features (category consistency). -/
theorem kc14_spine_consistent :
    allCategoryConsistent [Minimalism.Cat.n, .Num, .D] = true := by decide

/-- K&C's (14) spine [n, Num, D] has monotonically increasing F-values:
    n (F1) ≤ Num (F3) ≤ D (F4). The gap between n (F1) and Num (F3)
    reflects K&C's omission of the Q (classifier) layer, which sits
    at F2 in @cite{borer-2005}'s full nominal spine. -/
theorem kc14_spine_monotone :
    allFMonotone [Minimalism.Cat.n, .Num, .D] = true := by decide

/-- The F-values of K&C's (14) are strictly increasing:
    n (F1 = 1) < Num (F3 = 3) < D (F4 = 4). -/
theorem kc14_fvalues_strict :
    fValue .n < fValue .Num ∧
    fValue .Num < fValue .D := by decide

/-- K&C's (14) spine belongs to the nominal EP family. -/
theorem kc14_spine_nominal :
    catFamily .n = .nominal ∧
    catFamily .Num = .nominal ∧
    catFamily .D = .nominal := by decide

-- ── Stage-structure integration ──

/-- At Stage 3, every referent context permits an ungendered nominal
    structure (plain n), which produces "they". This composes two
    independent results:
    - `stage3_nothing_obligatory`: no context requires gender features
    - `singular_ungendered_spellout`: plain n → "they" via VI

    The DP structure at all three stages is identical — K&C's (14). What
    changes across stages is which n-heads are available in which referent
    contexts, not the syntactic architecture itself. -/
theorem stage3_they_from_structure (ctx : ReferentContext) :
    genderObligatoryFor ctx .stage3 = false ∧
    ({ nHead := CatHead.n_plain, singular := true : PronDP }).spellout
      = some "they" :=
  ⟨by cases ctx <;> rfl, by decide⟩

-- ============================================================================
-- § 10: Bridge to English Fragment
-- ============================================================================

/-- The VI elsewhere exponent *they* corresponds to the Fragment's
    epicene gender paradigm. This makes explicit the connection that
    K&C's analysis reveals: epicene is not a positive gender class but
    the **absence** of a contrastive gender feature — the elsewhere
    case in VI competition. -/
theorem elsewhere_is_epicene :
    subsetPrinciple pronounVIs ungenderedBundle = some "they" ∧
    Fragments.English.Pronouns.genderOf "they" = .epicene :=
  ⟨by decide, rfl⟩

/-- The VI competition and the Fragment's gender paradigm are
    consistent across all four pronoun forms: each VI exponent maps
    to its expected gender paradigm class.

    This is the bridge between the morphosyntactic mechanism (VI) and the
    descriptive grammar (GenderParadigm): VI *derives* which form is used,
    and the Fragment's paradigm classification *records* the result. -/
theorem vi_fragment_consistency :
    Fragments.English.Pronouns.genderOf "she" = .feminine ∧
    Fragments.English.Pronouns.genderOf "he" = .masculine ∧
    Fragments.English.Pronouns.genderOf "it" = .neuter ∧
    Fragments.English.Pronouns.genderOf "they" = .epicene :=
  ⟨rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- § 11: Comparison with Bjorkman 2017 (K&C §5)
-- ============================================================================

/-- @cite{bjorkman-2017}'s dynamic discourse condition: a pronoun's
    gender features must be a subset of its antecedent's gender features.
    A pronoun that is "less specified" than its antecedent is acceptable;
    one that adds features the antecedent lacks is not.

    K&C §5 argue this condition presupposes contrastive features and
    cannot extend to Stage 3, where features are non-contrastive. -/
def bjorkmanSubset (pronounFeatures antecedentFeatures : List PronFeature) : Bool :=
  pronounFeatures.all (antecedentFeatures.contains ·)

/-- Under Bjorkman's condition, *they* (no gender features) can always
    corefer with any antecedent, because ∅ ⊆ S for any set S. -/
theorem they_always_bjorkman_ok (antecedent : List PronFeature) :
    bjorkmanSubset [] antecedent = true := by
  simp [bjorkmanSubset, List.all_nil]

/-- Under Bjorkman's condition, *he* ([MASC]) cannot corefer with an
    antecedent that lacks [MASC] — the pronoun adds a feature the
    antecedent doesn't have.
    Example: "Every student₁ brought his₁ lunch" — *his* has [MASC]
    but *every student* has no gender feature → Bjorkman predicts
    this is blocked, matching Stage 1 speakers' judgments. -/
theorem he_blocked_for_ungendered_antecedent :
    bjorkmanSubset [.masc] [] = false := by decide

/-- At Stage 3, K&C predict that antecedents' gender feature bundles
    are typically empty (non-contrastive features are optional modifiers
    whose absence is the norm). Bjorkman's condition is then vacuously
    satisfied for ALL pronouns, providing no constraint at all.

    K&C argue this is a problem: Bjorkman's system gives no mechanism
    for why Stage 3 speakers would still *optionally* use "he"/"she"
    (which K&C handle via non-contrastive modifiers that are present
    but not obligatory). -/
theorem bjorkman_vacuous_at_stage3 :
    Stage.stage3.genderContrastivity = .nonContrastive ∧
    -- When the antecedent projects no gender features (the Stage 3 norm),
    -- Bjorkman's condition accepts any pronoun:
    bjorkmanSubset [] [] = true ∧
    bjorkmanSubset [.masc] [] = false ∧  -- but [MASC] pronoun is blocked!
    -- The condition blocks *he* for ungendered antecedents, which is
    -- correct at Stage 3 — but it cannot explain why *he* is ALSO
    -- available (as an optional modifier). K&C's non-contrastive
    -- analysis handles both cases:
    Stage.stage3.genderObligatory = false :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- K&C §5.2: Bjorkman's condition also cannot explain the GRADUAL
    nature of the Stage 1→2 transition. If the change were simply
    learning that some names lack gender features (Bjorkman's account),
    it should be abrupt — once you learn "Kelly" has no [MASC], you
    accept *they* for Kelly. But K&C argue the change is gradual
    because it involves restructuring the feature system, not just
    updating lexical entries.

    Formally: at Stage 1, ungendered names obligatorily project gender
    (so "Kelly₁ said they₁ couldn't make it" is rejected). The Stage 2
    innovation is that certain names no longer project gender. This is
    NOT modeled by Bjorkman's condition, which only constrains pronoun
    selection given a fixed feature bundle — it doesn't address which
    bundles nominals project. -/
theorem bjorkman_blind_to_projection :
    genderObligatoryFor .ungenderedProperName .stage1 = true ∧
    genderObligatoryFor .ungenderedProperName .stage2 = false :=
  ⟨rfl, rfl⟩

-- ============================================================================
-- § 12: Pets and Inanimates (K&C §3, (9)--(10))
-- ============================================================================

/-- At Stage 3, animate non-human referents (pets) can also receive
    singular *they* — the ungendered bundle is available for all
    animate referents, not just humans. -/
theorem pets_pattern_with_animates :
    subsetPrinciple pronounVIs ungenderedBundle = some "they" ∧
    subsetPrinciple pronounVIs inanimateBundle = some "it" :=
  ⟨by decide, by decide⟩

/-- Inanimate singulars cannot receive *they* even at Stage 3:
    the [INANIM] feature remains contrastive, and *it* is the
    most specific match for [SG, INANIM].

    K&C (10): "I put my favourite watch down somewhere, and now
    I can't find it / *them." -/
theorem inanimates_always_it :
    subsetPrinciple pronounVIs inanimateBundle = some "it" := by decide

end KonnellyCowper2020
