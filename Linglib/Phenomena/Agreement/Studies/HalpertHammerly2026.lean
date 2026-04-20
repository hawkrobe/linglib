import Linglib.Fragments.Bantu.Params
import Linglib.Fragments.Xhosa.Basic
import Linglib.Fragments.Swahili.Basic
import Linglib.Core.Person
import Linglib.Theories.Morphology.DM.Categorizer

/-!
# Halpert & Hammerly 2026: Reconciling Animacy and Noun Class in Bantu

@cite{halpert-hammerly-2026}

Halpert, Claire & Hammerly, Christopher. 2026. Reconciling animacy and noun
class in Bantu. *Glossa: a journal of general linguistics* 11(1). 1--25.

## Core claims

1. **Core Noun Class Hypothesis** (19): All Bantu nouns are underlyingly
   specified for one of three core noun classes based on features
   [±Animate] and [±Human] from @cite{hammerly-2023}'s containment
   hierarchy: HUMAN [+Anim, +Hum] ≈ cl 1/2, NON-HUMAN ANIMATE
   [+Anim, −Hum] ≈ cl 9/10, INANIMATE [−Anim, −Hum] ≈ cl 7/8.

2. **Containment unification**: Person features [±Author, ±Participant]
   and animacy features [±Human, ±Animate] are part of the same
   containment hierarchy (3)–(4): [Auth] ⊂ [Part] ⊂ [Hum] ⊂ [Anim].

3. **Final vowels** (22): Core noun class is morphophonologically encoded
   by the nominalizing final vowel: n[+Anim, +Hum] ↔ *-i*,
   n[_, −Hum] ↔ *-o*.

4. **nP stacking** (26): A secondary n wraps the core nP, creating
   mismatches between the class prefix (secondary) and the core noun
   class (accessible to agreement).

5. **Probe articulation** (29): Cross-Bantu variation in animacy
   effects follows from probe sensitivity — flat φ-probes target
   n_secondary (Zulu), while probes relativized to [+Animate] search
   past n_secondary to n_core (Swahili).

## Empirical phenomena

- Alternative agreement / anti-agreement in Lubukusu (8)–(9)
- Animacy override in Chiyao (11)–(12), Swahili (13)
- Object doubling conditioned by animacy in Nyaturu (14)
- Agreement convergence with conjoined nouns in Xhosa (18)

## Relationship to Carstens 2026

@cite{halpert-hammerly-2026} and @cite{carstens-2026} converge on nP
stacking and the three-way core noun class split, but differ on the
theoretical grounding: H&H derive core classes from @cite{hammerly-2023}'s
containment-type features [±Animate, ±Human] and propose final vowels
as their morphophonological locus. Carstens rejects a grammaticalized
animacy hierarchy (fn. 12). The `AnimacyFeatures` type in `Bantu/Params.lean`
formalizes H&H's feature system; `SemanticCore` (shared with Carstens)
is derived from it via `AnimacyFeatures.toCoreClass`.

## Integration

- `AnimacyFeatures` instantiates `Core.PhiFeatures` (same `PrivativePair`
  as person features), connecting person and animacy containment
- `AnimacyFeatures.toAnimacyLevel` bridges to the `Core.Prominence`
  hierarchy used throughout the codebase
- `impossible_human_inanimate_without_animal` proves the conflation
  impossibility predicted by containment
- `AnimacyFeatures.toGenderFeature` bridges to @cite{kramer-2015}'s
  `GenderFeature` type on the n-head
- Cross-references: `Carstens2026.lean` (convergence data),
  `Kramer2020.lean` (n-head typology)
-/

namespace HalpertHammerly2026

open Fragments.Bantu
open Core.Person (Features)
open Core.Prominence (PersonLevel)

-- ============================================================================
-- § 1: Person–Animacy Containment Bridge
-- ============================================================================

/-- The full prominence hierarchy from @cite{hammerly-2023} (3):
    [Auth] ⊂ [Part] ⊂ [Hum] ⊂ [Anim] ⊂ [Agent] ⊂ [Indiv] ⊂ φ.

    This structure encodes the four innermost features. Person features
    [±Author, ±Participant] are nested inside animacy features
    [±Human, ±Animate]. -/
structure ProminenceFeatures where
  isAnimate : Bool
  isHuman : Bool
  hasParticipant : Bool
  hasAuthor : Bool
  deriving DecidableEq, Repr

/-- Well-formedness enforces the full containment chain:
    [+Author] → [+Participant] → [+Human] → [+Animate]. -/
def ProminenceFeatures.wellFormed (pf : ProminenceFeatures) : Bool :=
  (!pf.hasAuthor || pf.hasParticipant) &&
  (!pf.hasParticipant || pf.isHuman) &&
  (!pf.isHuman || pf.isAnimate)

/-- Extract the person projection. -/
def ProminenceFeatures.personFeatures (pf : ProminenceFeatures) :
    Core.Person.Features :=
  ⟨pf.hasParticipant, pf.hasAuthor⟩

/-- Extract the animacy projection. -/
def ProminenceFeatures.animacyFeatures (pf : ProminenceFeatures) :
    AnimacyFeatures :=
  ⟨pf.isAnimate, pf.isHuman⟩

/-- The containment chain predicts: speech-act participants are human.
    [+Participant] → [+Human] (@cite{halpert-hammerly-2026} (3)–(4)). -/
theorem participant_implies_human (pf : ProminenceFeatures)
    (hw : pf.wellFormed = true) (hp : pf.hasParticipant = true) :
    pf.isHuman = true := by
  cases pf with | mk a h p au =>
  subst hp
  cases h with
  | true => rfl
  | false => simp [ProminenceFeatures.wellFormed] at hw

/-- The containment chain predicts: speech-act participants are animate.
    [+Participant] → [+Human] → [+Animate]. -/
theorem participant_implies_animate (pf : ProminenceFeatures)
    (hw : pf.wellFormed = true) (hp : pf.hasParticipant = true) :
    pf.isAnimate = true := by
  cases pf with | mk a h p au =>
  subst hp
  cases h with
  | true =>
    cases a with
    | true => rfl
    | false => simp [ProminenceFeatures.wellFormed] at hw
  | false => simp [ProminenceFeatures.wellFormed] at hw

/-- First person is necessarily human and animate. -/
theorem first_person_is_human_animate :
    ∀ pf : ProminenceFeatures, pf.wellFormed = true →
    pf.hasAuthor = true →
    pf.isHuman = true ∧ pf.isAnimate = true := by
  intro ⟨a, h, p, au⟩ hw ha
  subst ha
  cases p with
  | true =>
    exact ⟨participant_implies_human ⟨a, h, true, true⟩ hw rfl,
           participant_implies_animate ⟨a, h, true, true⟩ hw rfl⟩
  | false => simp [ProminenceFeatures.wellFormed] at hw

/-- Person and animacy features share the `PrivativePair` structure.
    Both `Core.Person.Features` and `AnimacyFeatures` are `PhiFeatures`
    instances — the same three-cell, no-four-way-distinction architecture.
    This is not a coincidence: they are fragments of the same containment
    hierarchy (@cite{hammerly-2023}). -/
theorem person_animacy_same_structure :
    (Core.PhiFeatures.toPair Core.Person.first).wellFormed = true ∧
    (Core.PhiFeatures.toPair AnimacyFeatures.human).wellFormed = true ∧
    (Core.PhiFeatures.toPair Core.Person.third).wellFormed = true ∧
    (Core.PhiFeatures.toPair AnimacyFeatures.inanimate).wellFormed = true :=
  ⟨rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- § 2: Core Noun Class Hypothesis Verification
-- ============================================================================

/-- The Core Noun Class Hypothesis (19): the three well-formed feature
    combinations map exactly to the three core classes. -/
theorem core_noun_class_hypothesis :
    AnimacyFeatures.toCoreClass AnimacyFeatures.human = SemanticCore.human ∧
    AnimacyFeatures.toCoreClass AnimacyFeatures.animal = SemanticCore.animal ∧
    AnimacyFeatures.toCoreClass AnimacyFeatures.inanimate = SemanticCore.inanimate :=
  ⟨rfl, rfl, rfl⟩

/-- The feature decomposition of Xhosa's three interpretable genders
    matches H&H's core noun class features. -/
theorem xhosa_core_classes :
    (Fragments.Xhosa.Gender.status .genderA).core.map SemanticCore.toFeatures
        = some AnimacyFeatures.human ∧
    (Fragments.Xhosa.Gender.status .genderD).core.map SemanticCore.toFeatures
        = some AnimacyFeatures.inanimate ∧
    (Fragments.Xhosa.Gender.status .genderE).core.map SemanticCore.toFeatures
        = some AnimacyFeatures.animal := ⟨rfl, rfl, rfl⟩

/-- Xhosa's uninterpretable genders have no core feature decomposition. -/
theorem xhosa_no_core :
    (Fragments.Xhosa.Gender.status .genderB).core = none ∧
    (Fragments.Xhosa.Gender.status .genderC).core = none := ⟨rfl, rfl⟩

/-- The three core noun classes match the three animacy levels used
    throughout the codebase (bridging H&H's features to differential
    argument marking, Corbett/Smith-Stark scales, etc.). -/
theorem core_classes_match_prominence :
    AnimacyFeatures.human.toAnimacyLevel = .human ∧
    AnimacyFeatures.animal.toAnimacyLevel = .animate ∧
    AnimacyFeatures.inanimate.toAnimacyLevel = .inanimate := ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- § 3: Anti-Agreement / Alternative Agreement (§3.2)
-- ============================================================================

/-- Lubukusu alternative agreement (8)–(9): local persons and class 1 nouns
    all trigger the same AA morpheme *o-* under A-bar extraction, while
    other classes (e.g. class 7) retain their standard SM.

    This follows from containment: local persons have [+Participant], which
    entails [+Human] via the prominence hierarchy. Class 1 nouns have
    [+Human] directly. A probe targeting [+Human] treats them identically.
    Class 7 lacks [+Human] and so uses a different (unchanged) marker. -/
inductive LubukusuSM where
  | a   -- standard class 1 subject marker
  | o   -- alternative agreement marker (A-bar extraction)
  | sy  -- class 7 subject marker
  deriving DecidableEq, Repr

/-- Subject marker pair: declarative context vs A-bar extraction. -/
structure AAPattern where
  declarative : LubukusuSM
  extraction : LubukusuSM
  deriving DecidableEq, Repr

def lubukusu_class1 : AAPattern := ⟨.a, .o⟩
def lubukusu_local_person : AAPattern := ⟨.a, .o⟩
def lubukusu_class7 : AAPattern := ⟨.sy, .sy⟩

/-- Class 1 and local persons share the AA pattern. -/
theorem aa_class1_eq_local : lubukusu_class1 = lubukusu_local_person := rfl

/-- Class 7 does NOT show alternative agreement (lacks [+Human]). -/
theorem aa_class7_differs : lubukusu_class1 ≠ lubukusu_class7 := by decide

/-- **Derivation**: AA collapses class 1 and local persons BECAUSE both
    project [+Human] via `PhiFeatures`. Local persons have [+Participant],
    which entails [+Human] (person features are a subset of the animacy
    hierarchy). Class 1 has [+Human] directly. Both yield the same
    `PrivativePair` outer value.

    This theorem shows the structural basis: well-formed participants
    must have [+Human], the same outer feature as class 1. -/
theorem aa_structural_basis :
    -- Local persons: [+Participant] → [+Human] (containment)
    (∀ pf : ProminenceFeatures, pf.wellFormed = true →
      pf.hasParticipant = true → pf.animacyFeatures.isHuman = true) ∧
    -- Class 1: [+Human] directly
    AnimacyFeatures.human.isHuman = true :=
  ⟨fun pf hw hp => participant_implies_human pf hw hp, rfl⟩

-- ============================================================================
-- § 4: Probe Articulation (§6, (29))
-- ============================================================================

/-- Probe sensitivity determines whether agreement tracks n_core or
    n_secondary (@cite{halpert-hammerly-2026} (29)).

    - **flat**: the probe targets the closest φ-features (n_secondary).
      Agreement always reflects the visible noun class.
    - **relativized**: the probe bears [+Animate] and searches past
      n_secondary to find [+Animate] on n_core. Agreement reflects
      core noun class for animate nouns.

    This is parameterized per grammatical function: a language may
    have a flat subject probe but a relativized object probe (Nyaturu). -/
inductive ProbeSensitivity where
  | flat          -- targets closest φ (always n_secondary)
  | relativized   -- bears [+Animate], searches to n_core
  deriving DecidableEq, Repr

/-- Which agreement class surfaces for a given probe and nP stack.
    Flat probes always return the visible class; relativized probes
    return the core class when `hasAnimateCore` is true. -/
def agreementClass (probe : ProbeSensitivity) (stack : NPStack) : Nat :=
  match probe with
  | .flat => stack.visibleClass
  | .relativized =>
    if stack.hasAnimateCore then stack.coreClass
    else stack.visibleClass

/-- Zulu (flat probe): a [human] noun in class 3 gets class 3 agreement. -/
theorem zulu_flat_class3_human :
    agreementClass .flat (Fragments.Xhosa.humanInClass3) = 3 := rfl

/-- Swahili (relativized probe): a [human] noun in class 7 gets class 1
    agreement — animacy override. This is NOT separately stipulated;
    it FOLLOWS from `agreementClass .relativized` + `hasAnimateCore`. -/
theorem swahili_relativized_human_override :
    agreementClass .relativized
      ⟨7, 1, .interpretable .human⟩ = 1 := rfl

/-- Swahili (relativized probe): an [animal] noun in class 7 ALSO gets
    core class agreement — animal override (GENERIC ANIMATE). -/
theorem swahili_relativized_animal_override :
    agreementClass .relativized
      ⟨7, 9, .interpretable .animal⟩ = 9 := rfl

/-- Inanimate nouns are unaffected by relativized probes — probe finds
    no [+Animate] and falls back to visible class. -/
theorem inanimate_no_override :
    agreementClass .relativized
      ⟨5, 7, .interpretable .inanimate⟩ = 5 := rfl

/-- Uninterpretable genders are always tracked by visible class
    regardless of probe type. -/
theorem uninterpretable_always_visible (probe : ProbeSensitivity) (v c : Nat) :
    agreementClass probe ⟨v, c, .uninterpretable⟩ = v := by
  cases probe <;> rfl

/-- Animacy override is a consequence of probe articulation, not a
    separate parameter. When the core is [+Animate], a relativized
    probe returns the core class. When it isn't, the probe falls
    back to the visible class. -/
theorem override_from_animate_core (stack : NPStack)
    (h : stack.hasAnimateCore = true) :
    agreementClass .relativized stack = stack.coreClass := by
  simp only [agreementClass, h, ite_true]

theorem no_override_without_animate_core (stack : NPStack)
    (h : stack.hasAnimateCore = false) :
    agreementClass .relativized stack = stack.visibleClass := by
  simp only [agreementClass, h, Bool.false_eq_true, ite_false]

-- ============================================================================
-- § 5: Convergence under Coordination (§3.3, Table 18)
-- ============================================================================

/-- The default plural agreement class for conjoined singulars is
    determined by the core noun class, not the visible class.
    Human conjuncts → SM2, non-human conjuncts → SM8/10.
    This follows from `SemanticCore.defaultPluralClass`. -/
theorem convergence_human_to_sm2 :
    SemanticCore.defaultPluralClass .human = 2 := rfl

theorem convergence_animal_to_sm8 :
    SemanticCore.defaultPluralClass .animal = 8 := rfl

theorem convergence_inanimate_to_sm8 :
    SemanticCore.defaultPluralClass .inanimate = 8 := rfl

/-- Xhosa convergence (Table 18): human nouns in ANY class converge to SM2
    because all human nouns share core noun class [+Animate, +Human]. -/
theorem xhosa_human_convergence :
    SemanticCore.defaultPluralClass
      (AnimacyFeatures.toCoreClass AnimacyFeatures.human) = 2 := rfl

/-- Xhosa convergence (Table 18): inanimate nouns in any class converge
    to SM8 because they share core noun class [−Animate, −Human]. -/
theorem xhosa_inanimate_convergence :
    SemanticCore.defaultPluralClass
      (AnimacyFeatures.toCoreClass AnimacyFeatures.inanimate) = 8 := rfl

/-- **Table 18 key insight**: Classes 1, 7, 9 show EXPECTED agreement
    (their own plural class), not convergence. This is because these
    are the canonical classes for the three core noun classes — their
    visible class IS the core class (`isCanonical = true`).

    Classes 3, 5 are non-canonical for all cores, so nouns in those
    classes show convergence to the core default instead. -/
theorem canonical_classes_show_expected :
    Fragments.Xhosa.humanCanonical.isCanonical = true ∧
    Fragments.Xhosa.animalCanonical.isCanonical = true ∧
    Fragments.Xhosa.humanInClass3.isCanonical = false ∧
    Fragments.Xhosa.humanInClass5.isCanonical = false := by decide

/-- Non-canonical nouns converge to core default, not to their
    visible class's plural. E.g. a [human] noun in class 3 converges
    to SM2 (core default for human), not SM4 (plural of class 3). -/
theorem noncanonical_converges_to_core :
    -- A [human] noun in class 3: core default is SM2, not the
    -- expected plural SM4 (class 4 is plural of class 3)
    SemanticCore.defaultPluralClass
        (AnimacyFeatures.toCoreClass AnimacyFeatures.human) = 2 ∧
    SemanticCore.defaultPluralClass
        (AnimacyFeatures.toCoreClass AnimacyFeatures.human) ≠ 4 :=
  ⟨rfl, by decide⟩

/-- The SM8/SM10 syncretism in Xhosa (both use *zi-*) follows from the
    fact that classes 8 and 10 share [−Human] — they differ only in
    [±Animate], which Xhosa's convergence is insensitive to
    in this context. -/
theorem sm8_sm10_syncretism :
    Fragments.Xhosa.NounClass.subjPrefix .cl8 =
    Fragments.Xhosa.NounClass.subjPrefix .cl10 := rfl

-- ============================================================================
-- § 6: Object Doubling (§3.2, (14))
-- ============================================================================

/-- Object doubling in Nyaturu (14): animate objects allow (or require)
    doubling with an object marker on the verb; inanimate objects
    disallow it. This uses the SAME predicate as animacy override —
    `hasAnimateCore` — applied to the object probe, confirming that
    both phenomena are instances of [+Animate]-relativized probing. -/
def nyaturu_om_allowed (stack : NPStack) : Bool := stack.hasAnimateCore

theorem nyaturu_human_om : nyaturu_om_allowed
    ⟨1, 1, .interpretable .human⟩ = true := rfl

theorem nyaturu_inanimate_no_om : nyaturu_om_allowed
    ⟨7, 7, .interpretable .inanimate⟩ = false := rfl

/-- Object doubling and animacy override share the same structural
    basis: both depend on `hasAnimateCore`, confirming they are
    instances of the same [+Animate]-relativized probing mechanism. -/
theorem om_and_override_share_predicate (stack : NPStack) :
    nyaturu_om_allowed stack = stack.hasAnimateCore ∧
    (stack.hasAnimateCore = true →
      agreementClass .relativized stack = stack.coreClass) := by
  constructor
  · rfl
  · intro h; simp only [agreementClass, h, ite_true]

-- ============================================================================
-- § 7: Bridge to Kramer's n-Head Theory
-- ============================================================================

section KramerBridge
open Morphology.DM

/-- Bridge from H&H's animacy features to @cite{kramer-2015}'s
    `GenderFeature` on the categorizing head n.

    H&H's `AnimacyFeatures` encode core noun class via [±Animate, ±Human].
    Kramer's framework uses `GenderDimension.anim` with interpretability.
    The bridge maps:
    - [+Animate] (human or animal) → i[+ANIM] (interpretable animate)
    - [−Animate] (inanimate) → i[−ANIM] (interpretable inanimate)

    Both systems agree that the n-head bears gender features and that
    interpretability distinguishes natural from arbitrary gender. -/
def toGenderFeature (af : AnimacyFeatures) : GenderFeature :=
  { interp := .i, val := { dim := .anim, pol := if af.isAnimate then .pos else .neg } }

private def iAnimPos : GenderFeature :=
  { interp := .i, val := { dim := .anim, pol := .pos } }
private def iAnimNeg : GenderFeature :=
  { interp := .i, val := { dim := .anim, pol := .neg } }

theorem human_is_iAnimPos :
    toGenderFeature AnimacyFeatures.human = iAnimPos := rfl

theorem inanimate_is_iAnimNeg :
    toGenderFeature AnimacyFeatures.inanimate = iAnimNeg := rfl

/-- All core noun class features yield interpretable gender on n.
    This matches @cite{kramer-2015}'s prediction that natural gender
    is always interpretable, and connects H&H's claim that core noun
    class lives on n to Kramer's n-head architecture. -/
theorem core_features_are_interpretable :
    GenderFeature.IsNatural (toGenderFeature AnimacyFeatures.human) ∧
    GenderFeature.IsNatural (toGenderFeature AnimacyFeatures.animal) ∧
    GenderFeature.IsNatural (toGenderFeature AnimacyFeatures.inanimate) :=
  ⟨rfl, rfl, rfl⟩

/-- H&H's `GenderStatus.uninterpretable` corresponds to Kramer's
    arbitrary (u-feature) gender — both encode nouns whose gender
    is invisible at LF. -/
theorem interpretability_alignment :
    GenderStatus.isInterpretable (.interpretable .human) = true ∧
    GenderStatus.isInterpretable .uninterpretable = false ∧
    GenderFeature.IsNatural iAnimPos ∧
    GenderFeature.IsArbitrary { interp := .u, val := { dim := .anim, pol := .pos } } :=
  ⟨rfl, rfl, rfl, rfl⟩

end KramerBridge

end HalpertHammerly2026
