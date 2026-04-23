import Linglib.Features.PrivativePair
import Linglib.Features.Prominence

/-!
# Bantu Language Family: Shared Parameters

@cite{carstens-1991} @cite{kramer-2015} @cite{carstens-2026}
@cite{halpert-hammerly-2026} @cite{hammerly-2023}

Shared types for Bantu language fragments, capturing cross-Bantu structural
regularities in the noun class system. Individual Bantu languages (Swahili,
Xhosa, Shona) import these types and specialize them with language-specific
class inventories and morphological forms.

## Key shared structure

- Noun classes come in singular/plural pairs that define **genders**
  (@cite{carstens-1991}, @cite{kramer-2015})
- A small number of genders have **semantic cores** — salient associations
  with entity classes like [human], [animal], [inanimate]
  (@cite{carstens-2026} §4.2)
- The semantic core determines whether a gender is **interpretable**
  (bears an i[entity] flavor) or **uninterpretable** (purely formal)
- All Bantu nouns are underlyingly specified for **core noun class** via
  bivalent features [±Animate] and [±Human], from @cite{hammerly-2023}'s
  containment hierarchy (@cite{halpert-hammerly-2026} (19))

## Design

This file stores pure data — types, inventories, and status classifications.
Resolution logic (percolation, intersection) lives in the Theory layer
(`GenderResolution.lean`); study files connect the two.
-/

namespace Fragments.Bantu

-- ============================================================================
-- § 0: Core Noun Class Features (@cite{halpert-hammerly-2026} (19))
-- ============================================================================

/-- Bivalent animacy features from @cite{hammerly-2023}'s containment
    hierarchy, applied to Bantu core noun class by
    @cite{halpert-hammerly-2026}.

    Two features determine core noun class:
    - [±Animate]: distinguishes animate from inanimate entities
    - [±Human]: distinguishes humans from non-human animates

    These stand in a containment relation: [+Human] entails [+Animate]
    (being human entails being animate). The fourth combination
    [−Animate, +Human] is semantically incoherent and ruled out by
    `wellFormed`. -/
structure AnimacyFeatures where
  isAnimate : Bool
  isHuman : Bool
  deriving DecidableEq, Repr

namespace AnimacyFeatures

/-- Well-formedness: [+Human] → [+Animate].
    Being human entails being animate (@cite{halpert-hammerly-2026} fn. 10). -/
def wellFormed (af : AnimacyFeatures) : Bool :=
  !af.isHuman || af.isAnimate

/-- HUMAN = [+Animate, +Human] ≈ class 1/2 -/
def human : AnimacyFeatures := ⟨true, true⟩
/-- NON-HUMAN ANIMATE = [+Animate, −Human] ≈ class 9/10 -/
def animal : AnimacyFeatures := ⟨true, false⟩
/-- INANIMATE = [−Animate, −Human] ≈ class 7/8 -/
def inanimate : AnimacyFeatures := ⟨false, false⟩

/-- The fourth combination [−Animate, +Human] violates well-formedness. -/
theorem illFormed_only :
    (⟨false, true⟩ : AnimacyFeatures).wellFormed = false := rfl

/-- Exactly three well-formed core noun classes.
    This is an instance of the general `PrivativePair.no_four_way`:
    any `PhiFeatures` type supports at most 3 well-formed cells. -/
theorem exactly_three :
    ([⟨true, true⟩, ⟨true, false⟩, ⟨false, true⟩, ⟨false, false⟩].filter
      AnimacyFeatures.wellFormed).length = 3 := by decide

/-- Animacy features instantiate the `PhiFeatures` privative pair:
    outer = [±Animate], inner = [±Human]. This is the same mathematical
    structure as person features (outer = [±participant], inner = [±author]),
    confirming @cite{hammerly-2023}'s claim that person and animacy features
    share a common containment architecture. -/
instance : Features.PhiFeatures AnimacyFeatures where
  toPair af := ⟨af.isAnimate, af.isHuman⟩
  ofPair p := ⟨p.outer, p.inner⟩
  roundtrip := fun ⟨_, _⟩ => rfl

/-- Bridge to `Features.Prominence.AnimacyLevel`: the three well-formed
    feature bundles map to the three animacy levels used throughout the
    codebase for differential argument marking, agreement hierarchies, etc. -/
def toAnimacyLevel : AnimacyFeatures → Features.Prominence.AnimacyLevel
  | ⟨_, true⟩  => .human
  | ⟨true, false⟩ => .animate
  | ⟨false, false⟩ => .inanimate

theorem human_level : human.toAnimacyLevel = .human := rfl
theorem animal_level : animal.toAnimacyLevel = .animate := rfl
theorem inanimate_level : inanimate.toAnimacyLevel = .inanimate := rfl

end AnimacyFeatures

-- ============================================================================
-- § 0b: Final Vowels (@cite{halpert-hammerly-2026} §4.1)
-- ============================================================================

/-- Bantu nominalizing final vowels encode core noun class on the
    categorizing head n (@cite{halpert-hammerly-2026} (22)).

    - *-i*: n[+Animate, +Human] (human nominalizer)
    - *-o*: n[±Animate, −Human] (non-human nominalizer)
    - *-a*: verbalizing final vowel (not a core noun class marker) -/
inductive FinalVowel where
  | i  -- NFV: human nominalizer ([+Human])
  | o  -- NFV: non-human nominalizer ([−Human])
  | a  -- VFV: verbalizing
  deriving DecidableEq, Repr

namespace AnimacyFeatures

/-- Core noun class features determine the nominalizing final vowel
    (@cite{halpert-hammerly-2026} (22)). -/
def toFinalVowel (af : AnimacyFeatures) : FinalVowel :=
  if af.isHuman then .i else .o

theorem human_fv : human.toFinalVowel = .i := rfl
theorem animal_fv : animal.toFinalVowel = .o := rfl
theorem inanimate_fv : inanimate.toFinalVowel = .o := rfl

end AnimacyFeatures

-- ============================================================================
-- § 1: Semantic Cores
-- ============================================================================

/-- Semantic cores of Bantu gender: salient associations between
    genders and entity classes (@cite{carstens-2026} §4.2, (71)).

    Not all Bantu genders have a semantic core. Those that do have
    an interpretable i[entity] flavor at their innermost nP layer.
    Those that don't are purely formal (uninterpretable).

    Xhosa has three cores — [human], [animal], [inanimate] — reflecting
    a three-way entity split. Shona collapses [animal] and [inanimate]
    into a single [non-human] default, adding a fourth constructor.
    The Xhosa distinction is the parametric maximum. -/
inductive SemanticCore where
  | human     -- [human]: canonically classes 1/2
  | animal    -- [animal]: canonically classes 9/10 (Xhosa)
  | inanimate -- [inanimate]: canonically classes 7/8 (Xhosa)
  | nonhuman  -- [non-human]: Shona's 7/8 default for all non-humans
  deriving DecidableEq, Repr

-- ============================================================================
-- § 1b: AnimacyFeatures ↔ SemanticCore Bridge
-- ============================================================================

namespace AnimacyFeatures

/-- Derive `SemanticCore` from bivalent features
    (@cite{halpert-hammerly-2026} (19)). -/
def toCoreClass : AnimacyFeatures → SemanticCore
  | ⟨true, true⟩   => .human
  | ⟨true, false⟩  => .animal
  | ⟨false, _⟩     => .inanimate

end AnimacyFeatures

namespace SemanticCore

/-- Inverse: recover features from `SemanticCore` (for the three Bantu cores). -/
def toFeatures : SemanticCore → AnimacyFeatures
  | .human     => AnimacyFeatures.human
  | .animal    => AnimacyFeatures.animal
  | .inanimate => AnimacyFeatures.inanimate
  | .nonhuman  => AnimacyFeatures.inanimate  -- Shona conflation of animal + inanimate

end SemanticCore

/-- Round-trip: features → core → features is identity for well-formed features. -/
theorem AnimacyFeatures.roundtrip (af : AnimacyFeatures)
    (h : af.wellFormed = true) :
    af.toCoreClass.toFeatures = af := by
  cases af with | mk a hu =>
  cases a <;> cases hu <;> simp_all [AnimacyFeatures.wellFormed,
    AnimacyFeatures.toCoreClass, SemanticCore.toFeatures,
    AnimacyFeatures.human, AnimacyFeatures.animal, AnimacyFeatures.inanimate]

-- ============================================================================
-- § 1c: Conflation (@cite{halpert-hammerly-2026} §2, (5))
-- ============================================================================

/-- A language's **conflation pattern**: which containment features it is
    sensitive to. Dropping a feature merges the categories it distinguishes
    (@cite{halpert-hammerly-2026} (5), following @cite{mcginnis-2005}). -/
structure ConflationPattern where
  usesAnimate : Bool
  usesHuman : Bool
  deriving DecidableEq, Repr

/-- The number of core noun classes distinguished under a conflation pattern. -/
def ConflationPattern.classCount : ConflationPattern → Nat
  | ⟨true, true⟩   => 3  -- HUMAN, ANIMATE, INANIMATE (full system)
  | ⟨true, false⟩  => 2  -- GENERIC ANIMATE, INANIMATE (no [±Human])
  | ⟨false, true⟩  => 2  -- HUMAN, GENERIC INANIMATE (no [±Animate])
  | ⟨false, false⟩ => 1  -- all conflated (no animacy distinctions)

/-- Xhosa uses both features: three-way distinction. -/
def ConflationPattern.xhosa : ConflationPattern := ⟨true, true⟩
/-- Swahili lacks [±Human]: GENERIC ANIMATE (human + animal) vs INANIMATE. -/
def ConflationPattern.swahili : ConflationPattern := ⟨true, false⟩

theorem xhosa_three_classes : ConflationPattern.xhosa.classCount = 3 := rfl
theorem swahili_two_classes : ConflationPattern.swahili.classCount = 2 := rfl

/-- A feature-definable category: a conjunction of constraints on
    [±Animate] and/or [±Human]. `none` means the feature is unconstrained
    (conflated). This captures exactly the categories that arise from
    the containment hierarchy (@cite{halpert-hammerly-2026} (4)–(5)). -/
structure FeatureConjunction where
  animateReq : Option Bool  -- constraint on [±Animate], or `none` if conflated
  humanReq : Option Bool    -- constraint on [±Human], or `none` if conflated
  deriving DecidableEq, Repr

/-- Whether a feature bundle satisfies a conjunction. -/
def FeatureConjunction.matches (fc : FeatureConjunction) (af : AnimacyFeatures) : Bool :=
  (fc.animateReq.isNone || fc.animateReq == some af.isAnimate) &&
  (fc.humanReq.isNone || fc.humanReq == some af.isHuman)

/-- **Impossible conflation**: no feature-definable category (conjunction
    of [±Animate, ±Human] constraints) can select HUMAN and INANIMATE
    while excluding ANIMAL. This follows from containment: HUMAN shares
    [+Animate] with ANIMAL, and INANIMATE shares [−Human] with ANIMAL,
    so any conjunction selecting both endpoints must also select the
    middle (@cite{halpert-hammerly-2026} §2, p. 5). -/
theorem impossible_human_inanimate_without_animal :
    ¬∃ (fc : FeatureConjunction),
      fc.matches .human = true ∧
      fc.matches .inanimate = true ∧
      fc.matches .animal = false := by
  intro ⟨⟨a, h⟩, mH, mI, mA⟩
  simp only [FeatureConjunction.matches, AnimacyFeatures.human,
    AnimacyFeatures.inanimate, AnimacyFeatures.animal] at mH mI mA
  cases a with
  | none => cases h with
    | none => simp at mA
    | some b => cases b <;> simp_all
  | some b => cases b <;> cases h with
    | none => simp_all
    | some b' => cases b' <;> simp_all

-- ============================================================================
-- § 2: Gender Interpretability
-- ============================================================================

/-- Gender interpretability status (@cite{carstens-2026} §4.2).

    An **interpretable** gender has an i[entity] flavor associated with
    a salient class of countable entities. An **uninterpretable** gender
    has no such association — its members are semantically arbitrary.

    This distinction directly controls agreement with conjoined singulars:
    gender-matching plural agreement succeeds with uniform conjuncts
    only for interpretable genders (@cite{carstens-2026} (52), (54)). -/
inductive GenderStatus where
  | interpretable : SemanticCore → GenderStatus
  | uninterpretable : GenderStatus
  deriving DecidableEq, Repr

def GenderStatus.isInterpretable : GenderStatus → Bool
  | .interpretable _ => true
  | .uninterpretable => false

def GenderStatus.core : GenderStatus → Option SemanticCore
  | .interpretable c => some c
  | .uninterpretable => none

-- ============================================================================
-- § 3: nP Stacking
-- ============================================================================

/-- Stacked nP structure for Bantu nominals (@cite{carstens-2026} §4, (72)–(73)).

    Bantu nouns have an inner semantic nP (bearing the i-core gender)
    wrapped by zero or more outer nPs (determining the visible noun class).
    For nouns in their canonical class, visible = core; for nouns
    appearing in non-canonical classes (e.g. [human] nouns in classes
    3/4 or 5/6), the outer nP differs from the inner core.

    `visibleClass` is the outer noun class number (determines morphological
    agreement with non-conjoined DPs). `coreClass` is the inner class
    determined by the semantic core (or equal to `visibleClass` if no
    stacking). -/
structure NPStack where
  visibleClass : Nat
  coreClass : Nat
  status : GenderStatus
  deriving DecidableEq, Repr

def NPStack.isCanonical (s : NPStack) : Bool :=
  s.visibleClass == s.coreClass

/-- Whether the core noun class is [+Animate] (HUMAN or ANIMAL).
    This is the predicate that [+Animate]-relativized probes and
    object-doubling conditions both target
    (@cite{halpert-hammerly-2026} (29)). -/
def NPStack.hasAnimateCore (s : NPStack) : Bool :=
  match s.status with
  | .interpretable .human  => true
  | .interpretable .animal => true
  | _ => false

-- ============================================================================
-- § 4: Default Agreement Classes
-- ============================================================================

/-- Default agreement class for a semantic core (@cite{carstens-2026} (52c)).
    Class 2 *ba-* for [human], class 8 *zi-* for [inanimate] and [animal]. -/
def SemanticCore.defaultPluralClass : SemanticCore → Nat
  | .human     => 2
  | .animal    => 8
  | .inanimate => 8
  | .nonhuman  => 8

end Fragments.Bantu
