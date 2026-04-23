import Linglib.Core.Lexical.NounCategorization
import Linglib.Features.Prominence
import Linglib.Phenomena.Classifiers.Typology

/-!
# Prasertsom, Smith & Culbertson (2026)
@cite{prasertsom-smith-culbertson-2026}

Domain-general categorisation explains constrained cross-linguistic
variation in noun classification. Cognition 271, 106411.

## Key Claims

@cite{prasertsom-smith-culbertson-2026} ask why animacy — but not colour —
appears in noun classification systems, despite colour being perceptually
salient. They argue the answer lies in a domain-general categorisation
principle: features with higher **predictive power** (the ability to predict
other features of category members) yield more compact, more distinct
categories, which are easier to learn. Animacy is more predictive than
colour, explaining its cross-linguistic prevalence via cultural transmission
amplification (@cite{griffiths-kalish-2007}, @cite{kirby-et-al-2007},
@cite{smith-2011}).

## Argument Chain

1. **Typological observation** (§1): Animacy is universal in noun
   categorization (@cite{aikhenvald-2000}); colour is absent from every
   attested system — despite high perceptual salience.
2. **Learning bias** (Exp 1a–b): Participants learn animacy-based artificial
   noun classes better than colour-based ones.
3. **Domain generality** (Exp 2a–c): Non-linguistic sorting also shows
   animacy preference, ruling out grammar-specific mechanisms.
4. **Mechanism** (§4.1, Table 6): Predictive power — animacy predicts other
   features (shape, horn, appendages) better than colour does, yielding
   more compact categories (Table 2) and higher classifier accuracy (Table 3).
5. **Causal evidence** (Exp 3a–b): Manipulating predictive power modulates
   sorting preferences, though the effect on noun class learning is indirect
   — participants who notice colour's predictive structure and sort by
   colour learn animacy-based noun classes *worse*.

## Formalization

The typological observation (§1) connects to existing `NounCategorization`
infrastructure. Predictive power is formalized via Table 6's conditional
entropy data from the experimental stimuli. The connection to
`Features.Prominence.AnimacyLevel` — the Silverstein hierarchy —
makes explicit that animacy's grammatical privilege spans both case marking
and noun classification.

-/

namespace PrasertsonSmithCulbertson2026

open Core.NounCategorization

-- ============================================================================
-- §1: The Animacy–Colour Asymmetry (derived from typological data)
-- ============================================================================

/-- Whether a semantic parameter is attested in any system in our typology.
    Derived from `allSystems` data rather than stipulated. -/
def isAttestedInTypology (p : SemanticParameter) : Bool :=
  Phenomena.Classifiers.Typology.allSystems.any (λ sys =>
    sys.preferredSemantics.any (· == p))

/-- Animacy is attested in the typological data. -/
theorem animacy_attested : isAttestedInTypology .animacy = true := by native_decide

/-- Humanness is attested in the typological data. -/
theorem humanness_attested : isAttestedInTypology .humanness = true := by native_decide

/-- Shape is attested in the typological data. -/
theorem shape_attested : isAttestedInTypology .shape = true := by native_decide

/-- Colour is NOT attested in any system in our typology. -/
theorem colour_not_attested : isAttestedInTypology .colour = false := by native_decide

/-- The central asymmetry: animacy is attested, colour is not. -/
theorem animacy_colour_asymmetry :
    isAttestedInTypology .animacy = true ∧
    isAttestedInTypology .colour = false := ⟨by native_decide, by native_decide⟩

-- ============================================================================
-- §2: Predictive Power — Conditional Entropy (Table 6)
-- ============================================================================

/-- Features in the experimental stimuli (Fig. 10, Tables 4–5). -/
inductive StimulusFeature where
  | animacy | colour | horn | shape_ | appendages
  deriving DecidableEq, Repr

/-- Conditional entropy H(row|col) from Table 6.
    Lower values mean the column feature is more predictive of the row feature.
    Values are in bits; the maximum for a binary feature is 1.0,
    for a 4-valued feature is 2.0. -/
structure ConditionalEntropy where
  row : StimulusFeature
  col : StimulusFeature
  /-- H(row|col) in bits, scaled ×1000 for exact rational arithmetic -/
  hBits_x1000 : Nat
  deriving Repr

/-- Table 6 data, predictive-animacy stimulus set.
    In this set, animacy is the predictive feature: knowing animacy reduces
    uncertainty about horn/shape/appendages more than knowing colour does.
    H(Horn|Animacy) = 0.406 < H(Horn|Colour) = 0.906. -/
def table6_horn_given_animacy : ConditionalEntropy :=
  ⟨.horn, .animacy, 406⟩   -- H(horn|animacy) = 0.406
def table6_horn_given_colour : ConditionalEntropy :=
  ⟨.horn, .colour, 906⟩    -- H(horn|colour) = 0.906
def table6_shape_given_animacy : ConditionalEntropy :=
  ⟨.shape_, .animacy, 406⟩  -- H(shape|animacy) = 0.406
def table6_shape_given_colour : ConditionalEntropy :=
  ⟨.shape_, .colour, 906⟩   -- H(shape|colour) = 0.906
def table6_appendages_given_animacy : ConditionalEntropy :=
  ⟨.appendages, .animacy, 406⟩ -- H(appendages|animacy) = 0.406
def table6_appendages_given_colour : ConditionalEntropy :=
  ⟨.appendages, .colour, 906⟩  -- H(appendages|colour) = 0.906

/-- Table 6: animacy is more predictive of horn than colour is.
    H(horn|animacy) = 0.406 < H(horn|colour) = 0.906. -/
theorem animacy_predicts_horn_better :
    table6_horn_given_animacy.hBits_x1000 <
    table6_horn_given_colour.hBits_x1000 := by decide

/-- Table 6: animacy is more predictive of shape than colour is. -/
theorem animacy_predicts_shape_better :
    table6_shape_given_animacy.hBits_x1000 <
    table6_shape_given_colour.hBits_x1000 := by decide

/-- Table 6: animacy is more predictive of appendages than colour is. -/
theorem animacy_predicts_appendages_better :
    table6_appendages_given_animacy.hBits_x1000 <
    table6_appendages_given_colour.hBits_x1000 := by decide

/-- Table 6, "Both stimulus sets" column (reverse direction):
    Horn/shape/appendages predict animacy better than they predict colour.
    H(Animacy|Horn) = 1.451 < H(Colour|Horn) = 1.951.
    This is consistent: predictive power is symmetric — if animacy predicts
    horn well, horn also predicts animacy well. -/
def table6_animacy_given_horn : ConditionalEntropy :=
  ⟨.animacy, .horn, 1451⟩   -- H(animacy|horn) = 1.451
def table6_colour_given_horn : ConditionalEntropy :=
  ⟨.colour, .horn, 1951⟩    -- H(colour|horn) = 1.951

theorem horn_predicts_animacy_better_than_colour :
    table6_animacy_given_horn.hBits_x1000 <
    table6_colour_given_horn.hBits_x1000 := by decide

-- ============================================================================
-- §3: Corpus Evidence — Category Compactness (Table 2)
-- ============================================================================

/-- Semantic basis for categorization (both experimental and typological). -/
inductive SemanticBasis where
  | animacy | colour
  deriving DecidableEq, Repr

/-- Intra-category similarity from Word2Vec embeddings of 472 frequent
    physical nouns from CHILDES (§4.1.1). Higher InSim means category members
    are more similar to each other in distributional semantic space. -/
structure CategoryCompactness where
  basis : SemanticBasis
  category : String
  /-- Mean cosine similarity × 1000 (for exact arithmetic) -/
  inSim_x1000 : Nat
  deriving Repr

-- Table 2 data
def compactness_animate   : CategoryCompactness := ⟨.animacy, "animate",   179⟩
def compactness_inanimate : CategoryCompactness := ⟨.animacy, "inanimate", 137⟩
def compactness_warm      : CategoryCompactness := ⟨.colour,  "warm",      151⟩
def compactness_cool      : CategoryCompactness := ⟨.colour,  "cool",      126⟩

/-- InSim(Avg) × 1000: weighted average across categories.
    Animacy: 0.149, Colour: 0.147. -/
def inSimAvg_animacy_x1000 : Nat := 149
def inSimAvg_colour_x1000  : Nat := 147

/-- Animacy-based categories are more compact on average (Table 2).
    InSim(Avg) animacy (0.149) > InSim(Avg) colour (0.147). -/
theorem animacy_categories_more_compact :
    inSimAvg_animacy_x1000 > inSimAvg_colour_x1000 := by decide

/-- The animate category is the most compact single category. -/
theorem animate_most_compact :
    compactness_animate.inSim_x1000 > compactness_inanimate.inSim_x1000 ∧
    compactness_animate.inSim_x1000 > compactness_warm.inSim_x1000 ∧
    compactness_animate.inSim_x1000 > compactness_cool.inSim_x1000 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

-- ============================================================================
-- §4: Corpus Evidence — Classifier Learnability (Table 3)
-- ============================================================================

/-- 5-fold cross-validated logistic classifier accuracy from normalised
    Word2Vec embeddings (§4.1.2, Table 3). -/
structure ClassifierAccuracy where
  basis : SemanticBasis
  /-- Mean accuracy × 1000 -/
  accuracy_x1000 : Nat
  deriving Repr

def logistic_animacy : ClassifierAccuracy := ⟨.animacy, 858⟩  -- 0.858
def logistic_colour  : ClassifierAccuracy := ⟨.colour,  742⟩  -- 0.742

/-- Animacy categories are easier for a classifier to learn (Table 3). -/
theorem animacy_classifier_more_accurate :
    logistic_animacy.accuracy_x1000 > logistic_colour.accuracy_x1000 := by decide

-- ============================================================================
-- §5: Experimental Data — Noun Class Learning (Experiments 1a–b)
-- ============================================================================

/-- Result of a noun class learning experiment. -/
structure LearningResult where
  basis : SemanticBasis
  /-- Mean proportion correct × 1000 -/
  accuracy_x1000 : Nat
  deriving Repr

/-- Experiment 1a: Ease of learning (§2.1).
    Animacy condition: 0.915 mean accuracy.
    Colour condition: 0.841 mean accuracy.
    β_SemanticBasis = 1.859, p = 0.023. -/
def exp1a_animacy : LearningResult := ⟨.animacy, 915⟩
def exp1a_colour  : LearningResult := ⟨.colour,  841⟩

theorem exp1a_animacy_learned_better :
    exp1a_animacy.accuracy_x1000 > exp1a_colour.accuracy_x1000 := by decide

/-- Experiment 1b: Extrapolation from ambiguous data (§2.2).
    When animacy and colour are confounded in training, 77.5% of participants
    (62/80) generalise to animacy-based classification at test. -/
def exp1b_animacy_generalizers : Nat := 62
def exp1b_total_participants   : Nat := 80

theorem exp1b_above_chance :
    exp1b_animacy_generalizers * 2 > exp1b_total_participants := by decide

-- ============================================================================
-- §6: Experimental Data — Non-Linguistic Sorting (Experiments 2a–c)
-- ============================================================================

/-- Result of an image sorting experiment (§3). Participants sort 16 images
    into two groups; sorting strategy is inferred from AMI with reference sorts.
    Proportions are expressed as parts per thousand. -/
structure SortingResult where
  /-- Proportion ×1000 who sorted by animacy -/
  animacy_x1000 : Nat
  /-- Proportion ×1000 who sorted by colour -/
  colour_x1000 : Nat
  /-- Proportion ×1000 who sorted by another strategy -/
  other_x1000 : Nat
  deriving Repr

/-- Exp 2a: original stimuli (same as Exp 1). -/
def exp2a : SortingResult := ⟨875, 25, 100⟩
/-- Exp 2b: increased within-category colour similarity. -/
def exp2b : SortingResult := ⟨683, 150, 167⟩
/-- Exp 2c: further decreased within-category animacy similarity. -/
def exp2c : SortingResult := ⟨617, 183, 200⟩

theorem exp2a_animacy_preferred : exp2a.animacy_x1000 > exp2a.colour_x1000 := by decide
theorem exp2b_animacy_preferred : exp2b.animacy_x1000 > exp2b.colour_x1000 := by decide
theorem exp2c_animacy_preferred : exp2c.animacy_x1000 > exp2c.colour_x1000 := by decide

/-- The animacy bias persists even when visual similarity is manipulated
    to favour colour-based sorting (Exp 2b, 2c). -/
theorem sorting_bias_robust :
    exp2a.animacy_x1000 > exp2a.colour_x1000 ∧
    exp2b.animacy_x1000 > exp2b.colour_x1000 ∧
    exp2c.animacy_x1000 > exp2c.colour_x1000 :=
  ⟨by decide, by decide, by decide⟩

/-- The bias weakens as colour similarity increases — evidence that
    it is not absolute but can be modulated. -/
theorem bias_weakens_with_manipulation :
    exp2a.animacy_x1000 > exp2b.animacy_x1000 ∧
    exp2b.animacy_x1000 > exp2c.animacy_x1000 := by
  constructor <;> decide

-- ============================================================================
-- §7: Predictive Power Manipulation (Experiments 3a–b)
-- ============================================================================

/-- Experiment 3a results (§4.2): predictive power manipulation had a
    main effect of semantic basis (β = 1.251, p = 0.003) but the
    interaction with predictive feature was NOT significant
    (β = 0.276, p = 0.519). The prediction was "not straightforwardly
    confirmed."

    However, the sorting strategy × semantic basis interaction WAS
    significant (β = 1.058, p < 0.001): participants who sorted by
    animacy learned animacy-based noun classes better. -/
structure Exp3Result where
  /-- Accuracy ×1000 for animacy-basis condition -/
  animacyBasis_x1000 : Nat
  /-- Accuracy ×1000 for colour-basis condition -/
  colourBasis_x1000 : Nat
  deriving Repr

/-- Exp 3b (§4.3): among participants who sorted by colour (successful
    manipulation), there was NO significant difference between animacy-based
    and colour-based noun class learning (0.800 vs 0.803).
    β = −0.510, p = 0.314. -/
def exp3b_animacyBasis_x1000 : Nat := 800
def exp3b_colourBasis_x1000  : Nat := 803

/-- Exp 3b: when the animacy bias is neutralised by selecting colour-sorters,
    the learning advantage for animacy disappears. This is consistent with
    the domain-general account — the bias is in categorisation, not in grammar. -/
theorem exp3b_no_animacy_advantage :
    exp3b_colourBasis_x1000 ≥ exp3b_animacyBasis_x1000 := by decide

-- ============================================================================
-- §8: Connection to Silverstein Hierarchy (Features.Prominence)
-- ============================================================================

/-- The animacy hierarchy that governs noun classification
    (@cite{aikhenvald-2000}, @cite{silverstein-1976}) is the same hierarchy
    that governs differential argument marking (`Features.Prominence`).

    @cite{prasertsom-smith-culbertson-2026} provide a domain-general
    explanation for WHY animacy is grammatically privileged in both domains:
    animacy is highly predictive of other referent features, making it a
    good basis for categorization in general.

    This theorem connects the prominence hierarchy to the noun categorization
    typology: the levels of `AnimacyLevel` correspond to the
    `SemanticParameter.animacy` / `.humanness` distinction. -/
theorem prominence_encodes_categorization_parameters :
    -- The prominence hierarchy distinguishes human vs animate vs inanimate
    Features.Prominence.AnimacyLevel.human.rank >
    Features.Prominence.AnimacyLevel.animate.rank ∧
    Features.Prominence.AnimacyLevel.animate.rank >
    Features.Prominence.AnimacyLevel.inanimate.rank ∧
    -- These correspond to the top two semantic parameters in noun categorization
    isAttestedInTypology .animacy = true ∧
    isAttestedInTypology .humanness = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

-- ============================================================================
-- §9: The Full Argument Chain
-- ============================================================================

/-- The paper's core argument, assembled from the evidence above:

    1. Colour is absent from all attested noun categorization systems
    2. Animacy is present in all attested systems
    3. Animacy is more predictive of other features than colour (Table 6)
    4. Animacy-based categories are more compact in distributional space (Table 2)
    5. Animacy-based categories are easier for classifiers to learn (Table 3)
    6. Humans learn animacy-based noun classes better (Exp 1a)
    7. Humans prefer animacy-based sorting even non-linguistically (Exp 2a–c)

    The connection is: predictive power → compactness → learnability →
    typological prevalence (via cultural transmission). -/
theorem argument_chain :
    -- Typological observation
    isAttestedInTypology .colour = false ∧
    isAttestedInTypology .animacy = true ∧
    -- Predictive power (Table 6: animacy predicts other features better)
    table6_horn_given_animacy.hBits_x1000 <
      table6_horn_given_colour.hBits_x1000 ∧
    -- Category compactness (Table 2)
    inSimAvg_animacy_x1000 > inSimAvg_colour_x1000 ∧
    -- Classifier learnability (Table 3)
    logistic_animacy.accuracy_x1000 > logistic_colour.accuracy_x1000 ∧
    -- Human learning (Exp 1a)
    exp1a_animacy.accuracy_x1000 > exp1a_colour.accuracy_x1000 ∧
    -- Non-linguistic sorting (Exp 2a)
    exp2a.animacy_x1000 > exp2a.colour_x1000 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

end PrasertsonSmithCulbertson2026
