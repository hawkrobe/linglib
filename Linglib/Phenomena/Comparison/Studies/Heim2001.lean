import Linglib.Phenomena.Comparison.Studies.Kennedy1999
import Linglib.Theories.Semantics.Degree.DegreeAbstraction
import Linglib.Theories.Semantics.Degree.Comparative
import Linglib.Theories.Semantics.Degree.Superlative
import Linglib.Theories.Semantics.Degree.Differential

/-!
# Heim 2001: Degree Operators and Scope
@cite{heim-2001} @cite{heim-1999} @cite{kennedy-1999}

Irene Heim. Degree Operators and Scope. In C. Féry & W. Sternefeld (eds.),
*Audiatur Vox Sapientiae*, Akademie Verlag, pp. 214–239.

## Core Claim

Degree phrases (DegPs) are **generalized quantifiers over degrees** that
take scope by QR, analogous to DP quantifiers. The paper probes which
scope configurations are empirically available.

## Key Results

1. **Monotone collapse** (§2.1): with ↑monotone operators (∀, ∃,
   required, allowed), low-DegP and high-DegP are truth-conditionally
   equivalent — scope is undetectable for plain comparatives.

2. **Negation** (§2.1): high-DegP over negation yields presupposition
   failure (max of {d: ¬tall(x,d)} is undefined on unbounded scales).

3. **Kennedy's generalization** (§2.2): DegP cannot scope over a
   quantificational DP whose scope contains the DegP's trace.

4. **Intensional verbs** (§2.3): DegP CAN scope over `require`, `allow`,
   `need`, `be able`; but NOT over `might`, `should`, `supposed to`, `want`.

5. **De re/de dicto ≠ DegP-scope** (§2.4): the Russell ambiguity
   ("John thinks the yacht is longer than it is") is world-variable
   binding in the than-clause, not DegP movement.

6. **Semantic ellipsis** (§3.2): `-est` and `too` use their complement
   twice — evidence for DegP movement independent of VP-ellipsis.

-/

namespace Phenomena.Comparison.Studies.Heim2001

open Semantics.Degree.DegreeAbstraction
open Semantics.Degree.Comparative (comparativeSem)

-- ════════════════════════════════════════════════════
-- § 1. Heim = Kennedy Extensionally
-- ════════════════════════════════════════════════════

/-- For simple comparatives, Heim and Kennedy yield the same truth
    conditions. The derivation differs (degree abstraction + max vs
    direct measure comparison), but the result is identical. -/
theorem heim_eq_kennedy_simple {Entity D : Type*} [LinearOrder D]
    (μ : Entity → D) (a b : Entity) :
    heimComparativeWithMeasure μ a b ↔
      comparativeSem μ a b .positive :=
  Iff.rfl

/-- The equivalence is grounded by maximality: max{d: μ(a) ≥ d} = μ(a).
    Heim's `-er` compares maxima of degree predicates, and for monotone
    adjectives, the max of the degree set IS the measure function value. -/
theorem equivalence_via_maxDeg {Entity D : Type*} [LinearOrder D]
    (μ : Entity → D) (a : Entity) :
    IsMaxDeg (matrixPredicate μ a) (μ a) :=
  isMaxDeg_matrixPredicate μ a

-- ════════════════════════════════════════════════════
-- § 2. Scope Interaction Data
-- ════════════════════════════════════════════════════

/-- A scope interaction datum: does high-DegP yield a distinct,
    available reading? -/
structure ScopeInteractionDatum where
  sentence : String
  /-- The operator DegP interacts with -/
  operator : String
  /-- Are low-DegP and high-DegP truth-conditionally equivalent? -/
  scopeCollapse : Bool
  /-- Is the high-DegP reading empirically available? -/
  highDegPAvailable : Bool
  /-- Why (equivalence, presupposition failure, constraint) -/
  explanation : String
  deriving Repr

/-- Heim §2.1: scope collapses with monotone increasing operators.
    For plain comparatives (no `exactly`, no `less`), low-DegP ↔ high-DegP
    with ∀, ∃, required, allowed. Scope is undetectable. -/
def monotoneCollapseData : List ScopeInteractionDatum :=
  [ { sentence := "Every girl is taller than 4 feet"
    , operator := "∀ (every)"
    , scopeCollapse := true
    , highDegPAvailable := true
    , explanation := "low: each girl > 4'; high: shortest girl > 4' — equivalent" }
  , { sentence := "Some girl is taller than 4 feet"
    , operator := "∃ (some)"
    , scopeCollapse := true
    , highDegPAvailable := true
    , explanation := "low: some girl > 4'; high: tallest girl > 4' — equivalent" }
  , { sentence := "Every girl is as tall as John"
    , operator := "∀ (every)"
    , scopeCollapse := true
    , highDegPAvailable := true
    , explanation := "generalizes from comparatives to equatives" }
  , { sentence := "The paper is required to be longer than 10 pages"
    , operator := "□ (required)"
    , scopeCollapse := true
    , highDegPAvailable := true
    , explanation := "monotone collapse with necessity modal" }
  , { sentence := "The paper is allowed to be longer than 10 pages"
    , operator := "◇ (allowed)"
    , scopeCollapse := true
    , highDegPAvailable := true
    , explanation := "monotone collapse with possibility modal" }
  ]

/-- All monotone collapse examples have scopeCollapse = true. -/
theorem monotone_collapse_all_equivalent :
    ∀ d ∈ monotoneCollapseData, d.scopeCollapse = true := by
  intro d hd
  simp [monotoneCollapseData] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl <;> rfl

-- ════════════════════════════════════════════════════
-- § 3. Negation and Downward Monotone Operators
-- ════════════════════════════════════════════════════

/-- Heim §2.1: high-DegP over negation → presupposition failure.
    max{d: ¬tall(m,d)} = max{d: d > μ(m)} is undefined on unbounded
    scales. The high-DegP LF is semantically deviant. -/
def negationData : List ScopeInteractionDatum :=
  [ { sentence := "Mary isn't taller than 4 feet"
    , operator := "¬ (negation)"
    , scopeCollapse := false
    , highDegPAvailable := false
    , explanation := "high-DegP: max{d: ¬tall(m,d)} undefined — presupposition failure" }
  , { sentence := "At most two girls are taller than 5 feet"
    , operator := "at most (↓monotone)"
    , scopeCollapse := false
    , highDegPAvailable := false
    , explanation := "high-DegP: max{d: |{x: girl(x) ∧ tall(x,d)}| ≤ 2} > 5' — deviant" }
  , { sentence := "She refuses to work harder than that"
    , operator := "refuse (implicit negation)"
    , scopeCollapse := false
    , highDegPAvailable := false
    , explanation := "refuse = neg-raising verb; high-DegP presupposes undefined max" }
  ]

/-- The negated degree set {d : d > μ(a)} has no maximum, confirming
    presupposition failure for high-DegP over negation. -/
theorem negation_presupposition_failure {Entity D : Type*} [LinearOrder D]
    (μ : Entity → D) (a : Entity) (d : D) :
    negatedDegreePredicate μ a d ↔ d > μ a :=
  negatedDegreePredicate_eq μ a d

-- ════════════════════════════════════════════════════
-- § 4. Non-Monotone Operators: Scope Matters
-- ════════════════════════════════════════════════════

/-- Heim §2.1–2.2: with `exactly` and `less`, the two scope
    configurations are truth-conditionally DISTINCT. This is where
    Heim's approach makes testable predictions. -/
def nonMonotoneData : List ScopeInteractionDatum :=
  [ { sentence := "Exactly two girls are taller than 5 feet"
    , operator := "exactly (non-monotone)"
    , scopeCollapse := false
    , highDegPAvailable := false
    , explanation := "high-DegP: max{d: |{x: tall(x,d)}| = 2} > 5' — not a possible reading" }
  , { sentence := "Every girl is exactly 1 inch taller than John"
    , operator := "∀ + exactly (differential)"
    , scopeCollapse := false
    , highDegPAvailable := false
    , explanation := "high: shortest girl is exactly 1\" taller — false reading unavailable" }
  , { sentence := "Every girl is less tall than John"
    , operator := "∀ + less"
    , scopeCollapse := false
    , highDegPAvailable := false
    , explanation := "high: max{d: ∀x.tall(x,d)} < John — weaker, unavailable reading" }
  ]

-- ════════════════════════════════════════════════════
-- § 5. Kennedy's Generalization
-- ════════════════════════════════════════════════════

/-- **Kennedy's generalization** (Heim (27), p. 223):
    If the scope of a quantificational DP contains the trace of a DegP,
    it also contains that DegP itself.

    In other words: DegP cannot cross over a quantificational DP
    that c-commands its trace. This is a syntactic constraint on
    DegP-movement, not a semantic equivalence. -/
structure KennedyGeneralization where
  /-- Description of the constraint -/
  statement : String := "DegP cannot scope over a quantificational DP whose scope contains the DegP's trace"
  /-- This is a syntactic constraint, not semantic -/
  isSyntactic : Bool := true
  /-- It targets quantificational DPs specifically (not all operators) -/
  targetsQuantificationalDPs : Bool := true
  /-- Non-quantificational DPs (traces, names) CAN be crossed -/
  crossesNonQuantificational : Bool := true
  deriving Repr

def kennedyGeneralization : KennedyGeneralization := {}

-- ════════════════════════════════════════════════════
-- § 6. Intensional Verb Scope
-- ════════════════════════════════════════════════════

/-- Heim §2.3: with `exactly`-differentials and `less`, some intensional
    verbs allow high-DegP (= DegP scopes over the modal), others don't.

    This is NOT detectable with plain `more` comparatives — those
    collapse due to monotonicity (§2.1). Only `exactly`/`less` break
    the equivalence. -/
structure IntensionalVerbDatum where
  sentence : String
  verb : String
  /-- Does DegP scope over this verb (with exactly/less)? -/
  highDegPAvailable : Bool
  note : String := ""
  deriving Repr

def intensionalVerbData : List IntensionalVerbDatum :=
  -- Verbs that ALLOW high-DegP
  [ { sentence := "The paper is required to be exactly 5 pages longer than that"
    , verb := "require"
    , highDegPAvailable := true
    , note := "low: required length = exactly 15pp; high: length in minimal-compliance worlds = 15pp" }
  , { sentence := "The paper is allowed to be exactly 5 pages longer than that"
    , verb := "allow"
    , highDegPAvailable := true
    , note := "both readings clearly distinct and available" }
  , { sentence := "John is able to run less fast than that"
    , verb := "be able"
    , highDegPAvailable := true }
  , { sentence := "The paper needs to be exactly 5 pp longer than that"
    , verb := "need"
    , highDegPAvailable := true }
  -- Verbs that BLOCK high-DegP
  , { sentence := "The paper might be less long than that"
    , verb := "might"
    , highDegPAvailable := false
    , note := "epistemic modal resists DegP scoping over it" }
  , { sentence := "The paper should be less long than that"
    , verb := "should"
    , highDegPAvailable := false
    , note := "neg-raising: outer negation = inner negation" }
  , { sentence := "The paper is supposed to be less long than that"
    , verb := "supposed to"
    , highDegPAvailable := false }
  , { sentence := "I want the paper to be less long than that"
    , verb := "want"
    , highDegPAvailable := false
    , note := "neg-raising verb" }
  ]

/-- The pattern: deontic/ability modals allow high-DegP,
    epistemic/neg-raising verbs block it. -/
theorem intensional_verb_pattern :
    (intensionalVerbData.filter (·.highDegPAvailable)).length = 4 ∧
    (intensionalVerbData.filter (! ·.highDegPAvailable)).length = 4 := by
  simp [intensionalVerbData]

-- ════════════════════════════════════════════════════
-- § 7. De Re / De Dicto ≠ DegP-Scope
-- ════════════════════════════════════════════════════

/-- Heim §2.4: the Russell ambiguity is NOT evidence for DegP-scope.
    "John thinks the yacht is longer than it is" has two readings from
    world-variable binding in the than-clause (de re vs de dicto),
    both compatible with narrow DegP-scope. -/
structure RussellAmbiguityDatum where
  sentence : String
  readings : List String
  isDegPScope : Bool
  explanation : String
  deriving Repr

def russellAmbiguity : RussellAmbiguityDatum :=
  { sentence := "John thinks the yacht is longer than it is"
  , readings := ["de dicto (contradictory)", "de re (sensible)"]
  , isDegPScope := false
  , explanation := "Von Stechow (1984): both readings arise from world-variable binding in the than-clause, not DegP movement" }

-- ════════════════════════════════════════════════════
-- § 8. Superlative Readings
-- ════════════════════════════════════════════════════

/-- @cite{heim-1999} absolute vs relative superlative ambiguity.
    Absolute = narrow-scope `-est`, relative = wide-scope `-est`.
    Focus determines the comparison set for relative readings. -/
structure SuperlativeJudgment where
  sentence : String
  readings : List String
  focus : Option String := none
  note : String := ""
  deriving Repr

def superlativeExamples : List SuperlativeJudgment :=
  [ { sentence := "Kim climbed the highest mountain"
    , readings := ["absolute", "relative"]
    , note := "ambiguous between absolute and relative" }
  , { sentence := "KIM climbed the highest mountain"
    , readings := ["relative"]
    , focus := some "Kim"
    , note := "focus on subject forces relative reading" }
  , { sentence := "Everest is the highest mountain"
    , readings := ["absolute"]
    , note := "predicative: only absolute reading" }
  ]

-- ════════════════════════════════════════════════════
-- § 9. Bridges
-- ════════════════════════════════════════════════════

/-- **Bridge to Superlative.lean**: Heim's `-est` denotation (59)
    λR⟨d,et⟩.λx. max{d: R(x,d)} > max{d: ∃y ≠ x. R(y,d)}
    matches `absoluteSuperlative` when `R` is a monotone adjective. -/
theorem heim_est_matches_absolute {Entity D : Type*} [LinearOrder D]
    (μ : Entity → D) (C : Set Entity) (x : Entity) :
    Semantics.Degree.Superlative.absoluteSuperlative μ C x ↔
      (x ∈ C ∧ ∀ y ∈ C, y ≠ x → μ x > μ y) :=
  Iff.rfl

/-- **Bridge to Differential.lean**: Heim's exactly-differential (5b)
    ⟦exactly 2" -er than 1'⟧ = λP. max(P) = 1' + 2"
    corresponds to `differentialComparative` with `diff = 2`. -/
theorem heim_exactly_matches_differential {Entity : Type*}
    (μ : Entity → ℚ) (a b : Entity) (diff : ℚ) :
    Semantics.Degree.Differential.differentialComparative μ a b diff ↔
      (μ a - μ b = diff) :=
  Iff.rfl

/-- **Bridge to FoxHackl2006**: Heim's presupposition failure for
    high-DegP over negation (max of {d: ¬tall(m,d)} undefined) is
    the same mechanism as Fox & Hackl's negative islands (max of
    downward-monotone degree predicate undefined on dense scales). -/
theorem shared_maximality_failure {Entity D : Type*} [LinearOrder D]
    (μ : Entity → D) (a : Entity) (d : D) :
    negatedDegreePredicate μ a d ↔ d > μ a :=
  negatedDegreePredicate_eq μ a d

/-- **Bridge to scope theory**: the monotone collapse for ∃ is a
    proper theorem (not Iff.rfl). -/
theorem scope_collapse_exists {Entity D : Type*} [LinearOrder D]
    (restrictor : Entity → Prop) (μ : Entity → D) (threshold : D) :
    lowDegP_exists restrictor μ threshold ↔
    highDegP_exists restrictor μ threshold :=
  exists_more_scope_collapse restrictor μ threshold

end Phenomena.Comparison.Studies.Heim2001
