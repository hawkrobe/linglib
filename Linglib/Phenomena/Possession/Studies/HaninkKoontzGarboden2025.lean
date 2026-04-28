import Linglib.Theories.Morphology.RootTypology
import Linglib.Phenomena.Causation.Studies.KoontzGarboden2009
import Linglib.Theories.Morphology.DM.Categorizer
import Linglib.Theories.Semantics.Noun.Relational.Barker2011

/-!
# Variation in the lexical semantics of property concept roots
@cite{hanink-koontz-garboden-2025}

Hanink, E.A. & Koontz-Garboden, A. (2025). Variation in the lexical
semantics of property concept roots: Evidence from Wá·šiw. *Natural
Language & Linguistic Theory* 43, 2727–2769.

## Core contribution

Property concept (PC) roots in Wá·šiw come in two semantic types:

- **Individual/state relations** (Class 1, Class 3): `λx_e λs_v[P(x)(s)]`
  These relate an individual to a state (e.g., √IHUK' 'dry': λx λs[dry(x)(s)]).
  Type: `⟨e, ⟨v, t⟩⟩` = `RootDenotationType.indivStatePred`.

- **Quality predicates** (Class 2): `λs_v[P(s)]`
  These are predicates of states with no individual argument
  (e.g., √I:YEL 'big': λs[big(s)]). Type: `⟨v, t⟩` = `RootDenotationType.statePred`.

## Three morphological classes

| Class | ATTR ʔil- | Reduplication | v_HAVE -iʔ | Example    |
|-------|-----------|---------------|-------------|------------|
| 1     | *         | *             | *           | yasaŋ 'hot'|
| 2     | *         | *             | ✓           | i:yel 'big'|
| 3     | ✓         | ✓             | ✓           | kaykay 'tall'|

## Key mechanisms

1. **-iʔ as v_have** (possessive light verb / categorizer):
   `⟦-iʔ⟧ = λP_⟨e,t⟩ λx_e ∃y_e[P(y) & π(x, y)]`
   Verbalizes quality-denoting roots (Class 2) by introducing possessive
   semantics. Also functions as v_have in ordinary possession.

2. **ʔil- as ∇** (type-shifter):
   `⟦ʔil-⟧ = λP_⟨e,⟨v,t⟩⟩ λs_v[∇(λx λs'[P(x)(s')])(s)]`
   Converts individual/state relations (Class 3) to quality-type predicates,
   which then feed into -iʔ.

3. **Type mismatch prediction**: v_become requires `⟨e, ⟨v, t⟩⟩` as input.
   Class 2 roots are `⟨v, t⟩` (`hasIndivArg = false`), so they CANNOT
   appear as finals in resultative bipartite verb constructions.
   Class 1 and 3 roots CAN (`hasIndivArg = true`).

## Connections

- Both -iʔ and ʔil- ADD semantic content (possession, ∇) — monotonic
  operations consistent with the MH (@cite{koontz-garboden-2009}).
- π is Barker's relationalizer from possessive NP semantics, reused
  inside the verbal categorizer's denotation.
- Against @cite{menon-pancheva-2014}'s universalist claim: not all PC
  roots have the same meaning.
- All Wá·šiw PC roots are `RootEntailments.propertyConcept` (+S −M −R −C)
  per @cite{beavers-koontz-garboden-2020} — the variation is in *semantic
  type*, not in structural entailments.
-/

namespace HaninkKoontzGarboden2025

open KoontzGarboden2009.Monotonicity
open Morphology.DM (Categorizer)
open Semantics.Noun.Relational.Barker2011 (π Pred1 Pred2)

-- ════════════════════════════════════════════════════
-- § 1. Morphological Classes and Semantic Types
-- ════════════════════════════════════════════════════

/-- Morphological class of PC verbs in Wá·šiw (Table 2). -/
inductive MorphClass where
  | class1  -- bare root predication (yasaŋ 'hot', ihuk' 'dry')
  | class2  -- root + -iʔ (i:yel 'big', kakt 'quiet')
  | class3  -- ʔil- + reduplication + root + -iʔ (kaykay 'tall', ši:šip 'straight')
  deriving DecidableEq, Repr

/-- The `RootDenotationType` of roots in each morphological class.

    Derived from the paper's analysis (§§4–5):
    - Class 1/3: individual/state relations ⟨e, ⟨v, t⟩⟩
    - Class 2: quality predicates ⟨v, t⟩ -/
def MorphClass.denotationType : MorphClass → RootDenotationType
  | .class1 => .indivStatePred
  | .class2 => .statePred
  | .class3 => .indivStatePred

-- ════════════════════════════════════════════════════
-- § 2. Bipartite Verb Composability (derived from RootDenotationType)
-- ════════════════════════════════════════════════════

/-- v_become requires an individual/state relation ⟨e, ⟨v, t⟩⟩.
    A root can serve as a bipartite verb "final" (result component) iff
    its denotation type has an individual argument.

    This is DERIVED from `RootDenotationType.hasIndivArg`, not stipulated
    per morphological class. -/
def MorphClass.canBeResultFinal (mc : MorphClass) : Bool :=
  mc.denotationType.hasIndivArg

/-- Class 1 roots can appear as bipartite verb finals (e.g., √IHUK' 'dry'
    in resultative 'dry by wiping'). -/
theorem class1_can_be_final :
    MorphClass.class1.canBeResultFinal = true := rfl

/-- Class 3 roots can appear as bipartite verb finals (e.g., √ŠI:ŠIP
    'straight' in resultative 'straighten by pulling'). -/
theorem class3_can_be_final :
    MorphClass.class3.canBeResultFinal = true := rfl

/-- Class 2 roots CANNOT appear as bipartite verb finals — type mismatch
    with v_become because `statePred.hasIndivArg = false`.
    (@cite{hanink-koontz-garboden-2025} §5.1) -/
theorem class2_cannot_be_final :
    MorphClass.class2.canBeResultFinal = false := rfl

/-- The bipartite verb gap follows from semantic type: exactly the
    quality-type roots (those lacking an individual argument) are excluded. -/
theorem bipartite_gap_iff_no_indiv_arg (mc : MorphClass) :
    mc.canBeResultFinal = false ↔ mc = .class2 := by
  cases mc <;> simp [MorphClass.canBeResultFinal, MorphClass.denotationType,
    RootDenotationType.hasIndivArg]

-- ════════════════════════════════════════════════════
-- § 3. Possessive Verbalizer -iʔ (v_have)
-- ════════════════════════════════════════════════════

variable {Entity State : Type}

/-- Denotation of -iʔ as v_have (@cite{hanink-koontz-garboden-2025} (34)):
    `⟦-iʔ⟧ = λP λx ∃y[P(y) & π(x, y)]`

    Takes a one-place predicate P (the quality/state) and a possession
    relation R, returning a predicate of individuals who possess
    something satisfying P. Quantification over the possessum y is
    modeled via `List.any` over a finite entity domain. -/
def vHave [BEq Entity] (entities : List Entity)
    (P : Pred1 Entity State) (R : Pred2 Entity State)
    (x : Entity) (s : State) : Bool :=
  entities.any (λ y => P y s && R x y s)

/-- v_have is Barker's π composed with existential closure:
    `vHave entities P R x s = ∃y ∈ entities. (π P R) x y s` -/
theorem vHave_is_ex_pi [BEq Entity] (entities : List Entity)
    (P : Pred1 Entity State) (R : Pred2 Entity State)
    (x : Entity) (s : State) :
    vHave entities P R x s = entities.any (λ y => (π P R) x y s) := by
  simp only [vHave, π]

-- ════════════════════════════════════════════════════
-- § 4. Type-Shifter ∇ (ʔil-)
-- ════════════════════════════════════════════════════

/-- The ∇ operator (ʔil-): type-shifts an individual/state relation to
    a quality predicate (@cite{hanink-koontz-garboden-2025} (57)).

    `⟦ʔil-⟧ = λP_⟨e,⟨v,t⟩⟩ λs_v[∇P(s)]`

    Takes a relation P between individuals and states, and returns the
    set of states that underly P's range — i.e., states s such that
    some individual bears P to s. -/
def nabla [BEq Entity] (entities : List Entity)
    (P : Entity → State → Bool) (s : State) : Bool :=
  entities.any (λ x => P x s)

/-- ∇ produces a quality-type predicate: its output depends only on the
    state, with the individual argument existentially closed.
    This matches `RootDenotationType.statePred` (⟨v,t⟩). -/
theorem nabla_closes_indiv_arg [BEq Entity] (entities : List Entity)
    (P : Entity → State → Bool) (s₁ s₂ : State)
    (h : ∀ x, P x s₁ = P x s₂) :
    nabla entities P s₁ = nabla entities P s₂ := by
  unfold nabla
  congr 1; ext x; exact h x

-- ════════════════════════════════════════════════════
-- § 5. Possessive Morphology ↔ Semantic Type
-- ════════════════════════════════════════════════════

/-- Whether a morphological class requires the possessive verbalizer -iʔ.
    Derived from the root's denotation type: roots without an individual
    argument MUST go through v_have; roots with one MAY (Class 3) or
    may not (Class 1). -/
def MorphClass.requiresVHave : MorphClass → Bool
  | .class1 => false  -- bare root predication (has indiv arg, can predicate directly)
  | .class2 => true   -- root + -iʔ (no indiv arg, needs v_have)
  | .class3 => true   -- ʔil- + reduplication + root + -iʔ

/-- Whether a morphological class requires the ʔil- prefix (∇ type-shift). -/
def MorphClass.requiresNabla : MorphClass → Bool
  | .class1 => false
  | .class2 => false
  | .class3 => true

/-- Class 1 roots are the only class that can be zero-categorized
    as verbs — they predicate directly without v_have
    (@cite{hanink-koontz-garboden-2025} §5.3, Table 2). -/
theorem only_class1_zero_categorizes (mc : MorphClass) :
    mc.requiresVHave = false ↔ mc = .class1 := by
  cases mc <;> simp [MorphClass.requiresVHave]

/-- Quality-type roots (those without an individual argument) always
    require possessive morphology. This is the paper's central claim:
    the type mismatch between ⟨v,t⟩ and predication of individuals
    FORCES v_have. -/
theorem no_indiv_arg_forces_vhave :
    MorphClass.class2.denotationType.hasIndivArg = false ∧
    MorphClass.class2.requiresVHave = true := ⟨rfl, rfl⟩

/-- ʔil- always co-occurs with -iʔ: Class 3 has both. ∇ type-shifts
    the root to quality-type, which then needs v_have. -/
theorem nabla_implies_vhave (mc : MorphClass) :
    mc.requiresNabla = true → mc.requiresVHave = true := by
  cases mc <;> simp [MorphClass.requiresNabla, MorphClass.requiresVHave]

-- ════════════════════════════════════════════════════
-- § 6. Monotonicity Hypothesis Consistency
-- ════════════════════════════════════════════════════

/-- Operators in Wá·šiw PC verb derivation.
    Modeled as abstract labels for MH checking; compositional semantics
    is given by `vHave` and `nabla` above. -/
inductive PCOp where
  | root       -- the root meaning
  | possess    -- possessive semantics (from -iʔ / v_have)
  | nabla      -- ∇ type-shift (from ʔil-)
  | redupMorph -- reduplication morphology (semantically vacuous per §5.2)
  deriving DecidableEq, Repr, BEq

/-- Operators present in each morphological class.
    Class 1: just the root.
    Class 2: root + possession (from -iʔ).
    Class 3: root + ∇ + reduplication + possession. -/
def MorphClass.operators : MorphClass → List PCOp
  | .class1 => [.root]
  | .class2 => [.root, .possess]
  | .class3 => [.root, .nabla, .redupMorph, .possess]

/-- All three derivational relationships are monotonic — none remove
    operators from the LSR. Uses `isMonotonic` from `KoontzGarboden2009.lean`
    (the originating paper for the Monotonicity Hypothesis). -/
theorem all_derivations_monotonic :
    isMonotonic MorphClass.class1.operators MorphClass.class2.operators = true ∧
    isMonotonic MorphClass.class1.operators MorphClass.class3.operators = true ∧
    isMonotonic MorphClass.class2.operators MorphClass.class3.operators = true :=
  ⟨by native_decide, by native_decide, by native_decide⟩

-- ════════════════════════════════════════════════════
-- § 7. Against Universalist Root Meaning
-- ════════════════════════════════════════════════════

/-- @cite{menon-pancheva-2014} claim all PC roots have the same semantic
    type crosslinguistically. @cite{hanink-koontz-garboden-2025} refutes this
    with language-internal evidence: Wá·šiw has PC roots of BOTH denotation
    types, correlated with different morphosyntax. -/
theorem within_language_variation :
    ∃ (c₁ c₂ : MorphClass),
      c₁.denotationType ≠ c₂.denotationType ∧
      c₁.requiresVHave ≠ c₂.requiresVHave ∧
      c₁.canBeResultFinal ≠ c₂.canBeResultFinal :=
  ⟨.class1, .class2, by decide, by decide, by decide⟩

-- ════════════════════════════════════════════════════
-- § 8. Wá·šiw PC Root Data (Table A1, sample)
-- ════════════════════════════════════════════════════

/-- A Wá·šiw property concept root entry.

    Each root carries a `RootClassification` from `RootTypology`, ensuring properties
    are derived from the theory layer. All PC roots share
    `RootEntailments.propertyConcept` (+S −M −R −C) but differ in
    `RootDenotationType` (the H&K-G contribution). -/
structure WasiwPCRoot where
  stem : String
  gloss : String
  morphClass : MorphClass
  dixonCat : PCClass
  /-- The theory-layer root: all PC roots are +S −M −R −C, no theme. -/
  root : RootClassification
  deriving Repr

/-- Construct a Wá·šiw PC root with the correct theory-layer `RootClassification`.
    All PC roots are `propertyConcept` (+S −M −R −C), `noTheme`, and
    their `denotationType` is determined by `MorphClass.denotationType`. -/
def mkWasiwRoot (stem gloss : String) (mc : MorphClass) (cat : PCClass) :
    WasiwPCRoot :=
  { stem, gloss, morphClass := mc, dixonCat := cat,
    root := { arity := .noTheme,
              changeType := .propertyConcept,
              denotationType := some mc.denotationType } }

/-- Sample of Wá·šiw PC roots from Table A1 (representative subset). -/
def sampleRoots : List WasiwPCRoot := [
  -- Class 1: Physical property
  mkWasiwRoot "ihuk'" "dry" .class1 .physicalProperty,
  mkWasiwRoot "yasaŋ" "hot" .class1 .physicalProperty,
  mkWasiwRoot "mosot" "wet" .class1 .physicalProperty,
  mkWasiwRoot "wihl"  "cold" .class1 .physicalProperty,
  mkWasiwRoot "ibik'" "ripe" .class1 .physicalProperty,
  -- Class 1: Dimension
  mkWasiwRoot "beheziŋ" "small" .class1 .dimension,
  mkWasiwRoot "wgohat"  "wide" .class1 .dimension,
  mkWasiwRoot "ʔudaw"   "tall (of object)" .class1 .dimension,
  -- Class 1: Value
  mkWasiwRoot "ʔaŋaw" "good" .class1 .value,
  -- Class 1: Age
  mkWasiwRoot "MiLe"  "old" .class1 .age,
  -- Class 1: Human propensity
  mkWasiwRoot "bišapuʔ" "hungry" .class1 .humanPropensity,
  mkWasiwRoot "Lokaš"   "afraid" .class1 .humanPropensity,
  mkWasiwRoot "yaha"    "sick/hurt" .class1 .humanPropensity,
  -- Class 2: Physical property
  mkWasiwRoot "guc'u"       "torn" .class2 .physicalProperty,
  mkWasiwRoot "kakt"        "quiet" .class2 .physicalProperty,
  mkWasiwRoot "Loyaw"       "dark" .class2 .physicalProperty,
  mkWasiwRoot "nu'uš"       "stinky" .class2 .physicalProperty,
  mkWasiwRoot "gumbeyéc'ik" "closed" .class2 .physicalProperty,
  -- Class 2: Dimension
  mkWasiwRoot "i:yel"  "big" .class2 .dimension,
  -- Class 2: Value
  mkWasiwRoot "mu:ʔaŋ" "tasty" .class2 .value,
  mkWasiwRoot "ʔnu:š"  "poor condition" .class2 .value,
  -- Class 2: Human propensity
  mkWasiwRoot "gumsut'im" "brave" .class2 .humanPropensity,
  mkWasiwRoot "musiw"     "generous" .class2 .humanPropensity,
  -- Class 2: Age
  mkWasiwRoot "ešlut'" "young" .class2 .age,
  -- Class 3: Color (all color roots are Class 3)
  mkWasiwRoot "leleg"    "red" .class3 .color,
  mkWasiwRoot "p'ilp'il" "blue" .class3 .color,
  mkWasiwRoot "popo"     "white" .class3 .color,
  mkWasiwRoot "šošoŋ"    "brown" .class3 .color,
  -- Class 3: Physical property
  mkWasiwRoot "k'awk'aw" "closed" .class3 .physicalProperty,
  mkWasiwRoot "k'unk'un" "bent" .class3 .physicalProperty,
  mkWasiwRoot "kaykay"   "tall" .class3 .physicalProperty,
  mkWasiwRoot "ši:šip"   "straight" .class3 .physicalProperty,
  mkWasiwRoot "lotlot"   "soft" .class3 .physicalProperty,
  -- Class 3: Dimension
  mkWasiwRoot "hamham" "light (in weight)" .class3 .dimension,
  mkWasiwRoot "šiššiš" "heavy" .class3 .dimension
]

-- ════════════════════════════════════════════════════
-- § 9. Per-Root Verification Theorems
-- ════════════════════════════════════════════════════

/-- All roots in the sample are PC roots (+S −M −R −C). -/
theorem all_roots_are_pc :
    sampleRoots.all (·.root.changeType == .propertyConcept) = true := by
  native_decide

/-- All roots have the denotation type matching their morphological class. -/
theorem denotation_types_match_class :
    sampleRoots.all (λ r =>
      r.root.denotationType == some r.morphClass.denotationType) = true := by
  native_decide

/-- No root in the sample entails change. -/
theorem no_root_entails_change :
    sampleRoots.all (λ r => !r.root.entailsChange) = true := by
  native_decide

/-- All color roots are Class 3 — the only fully predictable Dixon
    category (@cite{hanink-koontz-garboden-2025} §7, Appendix). -/
theorem color_roots_are_class3 :
    (sampleRoots.filter (·.dixonCat == .color)).all
      (·.morphClass == .class3) = true := by native_decide

/-- Distribution across the sample. -/
theorem class_distribution :
    (sampleRoots.filter (·.morphClass == .class1)).length = 13 ∧
    (sampleRoots.filter (·.morphClass == .class2)).length = 11 ∧
    (sampleRoots.filter (·.morphClass == .class3)).length = 11 := by native_decide

-- ════════════════════════════════════════════════════
-- § 10. Bridge Theorems
-- ════════════════════════════════════════════════════

/-- `statePred` is the only `RootDenotationType` without an individual
    argument — it is the type that forces possessive morphology. -/
theorem statePred_unique_no_indiv :
    ∀ dt : RootDenotationType, dt.hasIndivArg = false ↔ dt = .statePred := by
  intro dt; cases dt <;> simp [RootDenotationType.hasIndivArg]

/-- Class 1 and Class 3 share denotation type (both `indivStatePred`). -/
theorem class1_class3_same_denotation :
    MorphClass.class1.denotationType = MorphClass.class3.denotationType := rfl

/-- Class 2 is the only class with `statePred` denotation type. -/
theorem class2_unique_statePred (mc : MorphClass) :
    mc.denotationType = .statePred ↔ mc = .class2 := by
  cases mc <;> simp [MorphClass.denotationType]

/-- The three key predictions form a single biconditional over
    morphological class, all derived from `hasIndivArg`:

    mc = Class 2 ↔ statePred ↔ can't be bipartite final ↔ requires v_have

    (The last implication is one-directional: Class 3 also requires v_have
    despite having indivStatePred, because ∇ converts it to quality-type
    before -iʔ applies.) -/
theorem class2_characterization (mc : MorphClass) :
    mc.denotationType = .statePred ↔
    (mc.canBeResultFinal = false ∧ mc = .class2) := by
  cases mc <;> simp [MorphClass.denotationType, MorphClass.canBeResultFinal,
    RootDenotationType.hasIndivArg]

end HaninkKoontzGarboden2025
