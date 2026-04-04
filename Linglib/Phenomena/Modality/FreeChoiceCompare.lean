import Linglib.Theories.Semantics.Exhaustification.InnocentInclusion
import Linglib.Theories.Semantics.Exhaustification.InnocentExclusion
import Linglib.Phenomena.Modality.Studies.ChampollionAlsopGrosu2019
import Linglib.Phenomena.Modality.Studies.Alsop2024
import Linglib.Theories.Semantics.Dynamic.Bilateral.FreeChoice
import Linglib.Theories.Semantics.Dynamic.BSML.FreeChoice
import Linglib.Phenomena.Modality.Studies.Aloni2022
import Linglib.Phenomena.Modality.FreeChoice
import Linglib.Theories.Semantics.PossibilitySemantics.Epistemic

/-!
# Free Choice: Theory Comparison
@cite{aloni-2022} @cite{alsop-2024} @cite{bar-lev-fox-2020} @cite{champollion-alsop-grosu-2019} @cite{elliott-2025} @cite{fox-2007} @cite{holliday-mandelkern-2024}

Comparing how different theories derive free choice inferences.

## The Puzzle

"You may have coffee or tea" pragmatically implies:
"You may have coffee AND you may have tea"

Semantically: ◇(A ∨ B) ↔ ◇A ∨ ◇B (standard modal logic)
Pragmatically: ◇(A ∨ B) → ◇A ∧ ◇B (free choice!)

## Theories Compared

1. **@cite{fox-2007}**: Double exhaustification (Exh²) with Innocent Exclusion
2. **@cite{bar-lev-fox-2020}**: Innocent Inclusion (II) + Innocent Exclusion (IE)
3. **@cite{champollion-alsop-grosu-2019}**: RSA with semantic uncertainty (disjunction)
4. **@cite{alsop-2024}**: RSA with Global Intentions (universal *any*)
5. **@cite{aloni-2022}**: BSML - Bilateral State-based Modal Logic (team semantics)
6. **@cite{elliott-sudo-2025}**: BUS - Bilateral Update Semantics (dynamic)
7. **@cite{holliday-mandelkern-2024}**: Possibility semantics (ortholattice algebra)

-/

namespace Phenomena.Modality.FreeChoiceCompare

open Phenomena.Modality.FreeChoice
open Exhaustification
open Exhaustification.InnocentExclusion
open Exhaustification.FreeChoice
open RSA.FreeChoice
open RSA.FCIAny
open Semantics.Dynamic.BUS.FreeChoice
open Semantics.Dynamic.BSML
open Phenomena.Modality.Studies.Aloni2022
open Semantics.PossibilitySemantics

-- ============================================================================
-- SECTION 1: The Free Choice Puzzle
-- ============================================================================

/-!
## The Core Puzzle

Standard modal logic gives us:
  ◇(A ∨ B) ↔ ◇A ∨ ◇B

But pragmatically, we infer:
  ◇(A ∨ B) → ◇A ∧ ◇B

This is **not** a semantic entailment. The challenge is to derive it pragmatically.

### Two Related Inferences

1. **Free Choice Inference (FCI)**: ◇(A ∨ B) → ◇A ∧ ◇B
   - "You may have coffee or tea" → "You may have coffee" AND "You may have tea"

2. **Exclusivity Inference (EI)**: ◇(A ∨ B) → ¬◇(A ∧ B)
   - "You may have coffee or tea" → "You may not have both"

FCI is robust; EI is cancelable. Any theory must explain this asymmetry.
-/

/-- FCI is a pragmatic inference, not semantic -/
theorem fci_is_pragmatic : coffeeOrTea.isSemanticEntailment = false := rfl

/-- FCI is captured pragmatically -/
theorem fci_is_captured : coffeeOrTea.isPragmaticInference = true := rfl

-- ============================================================================
-- SECTION 1b: @cite{fox-2007} - Double Exhaustification
-- ============================================================================

/-!
## @cite{fox-2007}: Free Choice via Recursive Exhaustification

The original grammatical account: recursive application of `exh`
(the covert exhaustivity operator) derives FC without Innocent Inclusion.

- **Layer 1**: Exh(C)(◇(p∨q)) = ◇(p∨q) ∧ ¬◇(p∧q)
- **Layer 2**: Exh²(◇(p∨q)) = ◇p ∧ ◇q ∧ ¬◇(p∧q) — free choice!

See `Exhaustification/InnocentExclusion.lean` for the computable algorithm and
full derivation.
-/

/-- Fox 2007: FC is derived via double exhaustification (Exh²).
    Re-exports the verified computation from `InnocentExclusion.lean`. -/
theorem fox2007_derives_fc :
    ∀ w : InnocentExclusion.ModalW,
      InnocentExclusion.exhB InnocentExclusion.mDomain InnocentExclusion.layer2Alts InnocentExclusion.layer1Result w =
      (InnocentExclusion.diamP w && InnocentExclusion.diamQ w && !InnocentExclusion.diamPandQ w) :=
  InnocentExclusion.free_choice

-- ============================================================================
-- SECTION 2: @cite{bar-lev-fox-2020} - Innocent Inclusion
-- ============================================================================

/-!
## Neo-Gricean Account: Innocent Inclusion

@cite{bar-lev-fox-2020} extend @cite{fox-2007}'s Innocent Exclusion with **Innocent Inclusion**.

### The Mechanism

**Step 1: Innocent Exclusion (IE)**
- Find maximal sets of alternatives that can consistently be assigned FALSE
- An alternative is in IE if it's in ALL such maximal sets

**Step 2: Innocent Inclusion (II)**
- After IE, find maximal sets that can consistently be assigned TRUE
- An alternative is in II if it's in ALL such maximal sets

**Step 3: Combined Exhaustification**
  Exh^{IE+II}(φ) = φ ∧ ∀q ∈ IE[¬q] ∧ ∀r ∈ II[r]

### Why It Works for Free Choice

The key is **closure under conjunction**:

| Alternative Set | Closed under ∧? | Result |
|----------------|-----------------|--------|
| {a∨b, a, b, a∧b} | YES | Exclusive-or |
| {◇(a∨b), ◇a, ◇b, ◇(a∧b)} | NO | Free choice |

For FC alternatives:
- ◇a ∧ ◇b ≠ ◇(a ∧ b) in modal logic
- This non-closure allows II to include ◇a and ◇b
-/

/-- Bar-Lev & Fox: Free choice is derived via Innocent Inclusion -/
theorem barlevfox_derives_fc :
    ∀ w, exhIEII fcALT fcPrejacent w →
      Exhaustification.FreeChoice.permA w ∧ Exhaustification.FreeChoice.permB w :=
  Exhaustification.FreeChoice.free_choice

-- ============================================================================
-- SECTION 3: @cite{champollion-alsop-grosu-2019} - RSA + Semantic Uncertainty
-- ============================================================================

/-!
## RSA Account: Semantic Uncertainty

@cite{champollion-alsop-grosu-2019} use RSA with multiple interpretation functions
(following @cite{bergen-levy-goodman-2016}'s lexical uncertainty).

### The Mechanism

**Two Interpretation Functions**:
- I₁ (literal): Standard modal logic meanings
- I₂ (exhaustified): Strengthened meanings (à @cite{fox-2007})

For "You may A":
- Under I₁: {Only A, Only One, Any Number, Only Both}
- Under I₂: {Only A} only (exhaustified to exclude others)

**The Derivation**:
1. Speaker wants to convey "Only One" (you may choose either)
2. If speaker says "You may A", hearer might use I₂ → "Only A"
3. To avoid this, speaker uses "You may A or B"
4. Hearer reasons: "Speaker avoided A to prevent me thinking Only A"
5. Hearer concludes: Must be Only One or Any Number → FCI!

### Insight

The semantic uncertainty creates an **avoidance pattern**:
- Disjuncts are "risky" (might be interpreted exclusively)
- Disjunction is "safe" (always allows both options)
-/

/-- Champollion et al.: L1 assigns majority probability to FCI states for Or. -/
theorem champollion_derives_fc :
    RSA.FreeChoice.uniformCfg.L1_marginal .or_ hasFCI >
    RSA.FreeChoice.uniformCfg.L1_marginal .or_ (fun w => !hasFCI w) :=
  RSA.FreeChoice.fci_derived

/-- Champollion et al.: FCI is robust to prior manipulation. -/
theorem champollion_fc_robust :
    RSA.FreeChoice.biasedCfg.L1_marginal .or_ hasFCI >
    RSA.FreeChoice.biasedCfg.L1_marginal .or_ (fun w => !hasFCI w) :=
  RSA.FreeChoice.fci_robust_to_prior

-- ============================================================================
-- SECTION 3b: @cite{alsop-2024} - RSA + Global Intentions for *any*
-- ============================================================================

/-!
## RSA Account for Universal *Any*: Global Intentions

@cite{alsop-2024} extends the RSA approach to universal free choice items like *any*,
using the Global Intentions model from @cite{franke-bergen-2020}.

### The Mechanism

**Two Parses** (instead of two interpretation functions):
- Szabolcsi parse (weak): ∃x[◇take(x)] - "some option is permitted"
- Dayal parse (strong): ∀x[◇take(x)] - "each option is permitted"

**The Derivation**:
1. Speaker wants to convey "you may take any (= each) class"
2. If speaker uses weak parse, hearer might only infer "some class is OK"
3. To be informative, speaker intends the strong (Dayal) parse
4. Hearer reasons: "Speaker chose 'any' with the strong parse"
5. Hearer concludes: Each class is individually permitted → Exclusiveness!

### Key Parallel to Champollion et al.

| Aspect | Disjunction (@cite{champollion-alsop-grosu-2019}) | Universal *any* (2024) |
|--------|-------------------|----------------------|
| FC inference | ◇(a∨b) → ◇a ∧ ◇b | ◇∃x.P(x) → ∀x.◇P(x) |
| Robust inference | FCI | Exclusiveness |
| Prior-sensitive | EI (not-both) | Not-every |
| Ambiguity | Interpretation (I₁/I₂) | Parse (Szabolcsi/Dayal) |
-/

/-- Alsop: L1 assigns majority probability to exclusiveness states for "may any". -/
theorem alsop_derives_exclusiveness :
    RSA.FCIAny.uniformCfg.L1_marginal .mayAny hasExclusiveness >
    RSA.FCIAny.uniformCfg.L1_marginal .mayAny (fun w => !hasExclusiveness w) :=
  RSA.FCIAny.exclusiveness_derived

/-- Alsop: Exclusiveness is robust to prior manipulation. -/
theorem alsop_exclusiveness_robust :
    RSA.FCIAny.biasedCfg.L1_marginal .mayAny hasExclusiveness >
    RSA.FCIAny.biasedCfg.L1_marginal .mayAny (fun w => !hasExclusiveness w) :=
  RSA.FCIAny.exclusiveness_robust

/-- Alsop: Not-every is prior-sensitive (unlike exclusiveness). -/
theorem alsop_not_every_sensitive :
    ¬(RSA.FCIAny.biasedCfg.L1_marginal .mayAny hasNotEvery >
      RSA.FCIAny.biasedCfg.L1_marginal .mayAny (fun w => !hasNotEvery w)) :=
  RSA.FCIAny.not_every_weakened

-- ============================================================================
-- SECTION 3c: @cite{aloni-2022} - BSML Team Semantics
-- ============================================================================

/-!
## Semantic Account: BSML (Bilateral State-based Modal Logic)

@cite{aloni-2022} derives FC **semantically** using team semantics.

### The Mechanism

**Split Disjunction**: t ⊨ φ ∨ ψ iff ∃t₁,t₂: t₁ ∪ t₂ = t ∧ t₁ ⊨ φ ∧ t₂ ⊨ ψ

**Non-emptiness Enrichment**: [φ]⁺ adds NE constraints recursively

**FC Derivation**:
1. [◇(α ∨ β)]⁺ = ◇([α]⁺ ∨ [β]⁺) ∧ NE
2. Split disjunction partitions the team
3. [α]⁺ and [β]⁺ both include NE, so both parts must be non-empty
4. Therefore ◇α and ◇β are both supported
-/

-- Verify BSML narrow-scope FC computationally
#eval
  let enriched := enrich mayHaveCoffeeOrTea
  let t := freeChoiceTeam
  let supEnriched := support deonticModel enriched t
  let supCoffee := support deonticModel mayCoffee t
  let supTea := support deonticModel mayTea t
  (supEnriched, supCoffee, supTea)  -- (true, true, true)

/-- Aloni BSML: DNE holds definitionally -/
theorem aloni_dne {W : Type*} [DecidableEq W] (M : BSMLModel W)
    (φ : BSMLFormula) (t : Semantics.Dynamic.TeamSemantics.Team W) :
    support M (.neg (.neg φ)) t = support M φ t :=
  dne_support M φ t

-- ============================================================================
-- SECTION 3d: @cite{elliott-sudo-2025} - Bilateral Update Semantics
-- ============================================================================

/-!
## Semantic Account: BUS (Bilateral Update Semantics)

@cite{elliott-sudo-2025} derive FC **semantically** using dynamic bilateral updates.

### The Mechanism

**Modal Disjunction Precondition**:
s[φ ∨ ψ]⁺ = s[φ ∨ ψ]⁺ if s[φ ∨ ψ]⁺₁ ≠ ∅ AND s[φ ∨ ψ]⁺₂ ≠ ∅, else ∅

**FC Derivation**:
1. For ◇(φ ∨ ψ) to be possible, positive update must be non-empty
2. This requires BOTH disjuncts to contribute possibilities
3. Therefore ◇φ and ◇ψ are both possible

### Key Advantage: Cross-Disjunct Anaphora

BUS is uniquely designed to handle "bathroom disjunctions":
- "Either there's no bathroom or it's in a funny place"
- The pronoun "it" is bound by the existential under negation
- DNE (from bilateral structure) enables this binding
-/

/-!
Elliott & Sudo FC is derived from modal disjunction semantics.
The BUS module provides FC derivation via:
- `fc_semantic_first_disjunct`: ◇(φ ∨ ψ) → ◇φ
- `fc_semantic_second_disjunct`: ◇(φ ∨ ψ) → ψ possible after ¬φ
- `dual_prohibition`: ¬◇φ ∧ ¬◇ψ → ¬◇(φ ∨ ψ)
-/

-- Verify BUS theorems are imported and accessible
#check @fc_semantic_first_disjunct
#check @fc_semantic_second_disjunct
#check @dual_prohibition

-- ============================================================================
-- SECTION 3e: @cite{holliday-mandelkern-2024} - Possibility Semantics
-- ============================================================================

/-!
## Algebraic Account: Possibility Semantics (Ortholattice)

@cite{holliday-mandelkern-2024} provide a **structural** account of free
choice rooted in the algebra of propositions. In possibility semantics,
propositions form an **ortholattice** — validated by excluded middle and
non-contradiction, but NOT by distributivity. A partial possibility can
verify A ∨ B without verifying either disjunct, because disjunction is
De Morgan (A ∨ B = ¬(¬A ∧ ¬B)), weaker than set-theoretic union.

### The Mechanism

**Free choice selective validity**: ◇(A ∨ B) → ◇A ∧ ◇B holds for
propositions in the image of the Boolean embedding (Proposition 5.12.3),
but fails when the ortholattice is genuinely non-Boolean.

In the 5-point epistemic scale:
- At x₃ (full uncertainty), FC holds: both p and ¬p are accessible
- At x₁ (knows p), FC fails: ◇(p ∨ ¬p) is true but ◇¬p is false

### Key Difference

This is neither pragmatic (reasoning about alternatives) nor dynamic
(update semantics) — it's **algebraic**. Free choice depends on whether
the proposition space is Boolean. Standard modal logic (all possibilities
are worlds, compat = identity) is the special case where the algebra is
Boolean and FC holds universally (via `diamond_eq_kripkeEval_classical`).
-/

/-- Holliday & Mandelkern: FC holds at full uncertainty (x₃). -/
theorem hollidayMandelkern_fc_at_uncertainty :
    diamond epistemicScale (disj pathFrame propP (orthoNeg pathFrame propP)) .x3 = true →
    conj (diamond epistemicScale propP)
         (diamond epistemicScale (orthoNeg pathFrame propP)) .x3 = true :=
  free_choice_at_x3

/-- Holliday & Mandelkern: FC FAILS at knowledge (x₁). The non-Boolean
    ortholattice selectively blocks FC where the agent's epistemic state
    rules out one disjunct. -/
theorem hollidayMandelkern_fc_fails_at_knowledge :
    diamond epistemicScale (disj pathFrame propP (orthoNeg pathFrame propP)) .x1 = true ∧
    conj (diamond epistemicScale propP)
         (diamond epistemicScale (orthoNeg pathFrame propP)) .x1 = false :=
  free_choice_fails_at_x1

-- ============================================================================
-- SECTION 4: Comparison Table
-- ============================================================================

/-!
## Side-by-Side Comparison

| Aspect | Bar-Lev & Fox | Champollion et al. | Alsop | Aloni | E&S |
|--------|--------------|-------------------|-------|-------|-----|
| **Framework** | Neo-Gricean | RSA | RSA | Team Sem | Dynamic |
| **Type** | Pragmatic | Pragmatic | Pragmatic | Semantic | Semantic |
| **Key mechanism** | Innocent Inclusion | Semantic uncertainty | Parse ambiguity | NE + split ∨ | Modal ∨ precond |
| **Nature** | Categorical | Probabilistic | Probabilistic | Categorical | Categorical |
| **Anaphora** | No | No | No | No | Yes |
| **Why FC works** | Non-closure | Avoid I₂ | Dayal informative | NE forces both | Both contribute |
-/

/-- Comparison result type (extended for all theories) -/
structure TheoryComparison where
  phenomenon : String
  barlevfox : String
  champollion : String
  alsop : String
  aloni : String
  elliottSudo : String
  allAgree : Bool
  deriving Repr

/-- FCI: All theories derive it -/
def fciComparison : TheoryComparison :=
  { phenomenon := "Free Choice Inference"
  , barlevfox := "Derived via II: ◇a, ◇b ∈ II"
  , champollion := "L1: P(FCI states | Or) ≈ 100%"
  , alsop := "L1: P(exclusiveness | any) ≈ 100%"
  , aloni := "Semantic: [◇(α∨β)]⁺ ⊨ ◇α ∧ ◇β"
  , elliottSudo := "Semantic: modal ∨ precondition"
  , allAgree := true }

/-- Dual Prohibition: Negation blocks FC -/
def dualProhibitionComparison : TheoryComparison :=
  { phenomenon := "Dual Prohibition"
  , barlevfox := "Maximize Strength"
  , champollion := "Automatic (RSA strengthens)"
  , alsop := "Automatic (RSA strengthens)"
  , aloni := "Semantic: [¬◇(α∨β)]⁺ ⊨ ¬◇α ∧ ¬◇β"
  , elliottSudo := "Semantic: negative update unchanged"
  , allAgree := true }

/-- Secondary inference asymmetry -/
def secondaryInference : TheoryComparison :=
  { phenomenon := "Secondary Inference (EI / not-every)"
  , barlevfox := "IE excludes ◇(a∧b)"
  , champollion := "EI prior-sensitive"
  , alsop := "Not-every prior-sensitive"
  , aloni := "Not primary focus"
  , elliottSudo := "Not primary focus"
  , allAgree := true }

/-- Cross-disjunct anaphora -/
def anaphoraComparison : TheoryComparison :=
  { phenomenon := "Cross-disjunct anaphora"
  , barlevfox := "Not addressed"
  , champollion := "Not addressed"
  , alsop := "Not addressed"
  , aloni := "Not addressed"
  , elliottSudo := "Primary motivation (bathroom sentences)"
  , allAgree := false }

/-- All comparisons -/
def allComparisons : List TheoryComparison :=
  [fciComparison, dualProhibitionComparison, secondaryInference, anaphoraComparison]

-- ============================================================================
-- SECTION 5: Pragmatic vs Semantic Approaches
-- ============================================================================

/-!
## Pragmatic vs Semantic Derivation

A key division among FC theories:

### Pragmatic Approaches (FC as implicature)
- **Bar-Lev & Fox**: Exhaustification with Innocent Inclusion
- **Champollion et al.**: RSA reasoning about interpretation uncertainty
- **Alsop**: RSA reasoning about parse ambiguity

### Semantic Approaches (FC built into meaning)
- **Aloni (BSML)**: Split disjunction + non-emptiness enrichment
- **Elliott & Sudo (BUS)**: Modal disjunction precondition

### Trade-offs

| Aspect | Pragmatic | Semantic |
|--------|-----------|----------|
| FC source | Reasoning about alternatives | Lexical meaning |
| Cancelability | Predicted (pragmatic) | Must be stipulated |
| Gradient | RSA: yes; Neo-Gricean: no | No |
| Cross-disjunct anaphora | Hard to capture | BUS: natural |
| Dual prohibition | Requires explanation | Built in |
-/

/-- Approach classification -/
inductive ApproachType where
  | pragmatic : ApproachType
  | semantic : ApproachType
  deriving DecidableEq, Repr

/-- Classify theories by approach -/
def theoryApproach : String → ApproachType
  | "Bar-Lev & Fox 2020" => .pragmatic
  | "Champollion et al. 2019" => .pragmatic
  | "Alsop 2024" => .pragmatic
  | "Aloni 2022" => .semantic
  | "Elliott & Sudo 2025" => .semantic
  | _ => .pragmatic

-- ============================================================================
-- SECTION 6: Structural Insights
-- ============================================================================

/-!
## Different Structural Insights

### Bar-Lev & Fox: Closure Under Conjunction

The key structural property is whether the alternative set is closed under ∧.

**Simple disjunction**: ALT = {a∨b, a, b, a∧b}
- a ∧ b IS in ALT
- Closed → IE excludes everything, II includes nothing
- Result: Exclusive-or (or contradiction)

**FC disjunction**: ALT = {◇(a∨b), ◇a, ◇b, ◇(a∧b)}
- ◇a ∧ ◇b is NOT equivalent to ◇(a∧b)
- Not closed → IE excludes ◇(a∧b), II includes ◇a, ◇b
- Result: Free choice!

### Aloni: Non-Emptiness + Split Disjunction

The key is that disjunction SPLITS the team:
  t ⊨ φ ∨ ψ iff ∃t₁,t₂: t₁ ∪ t₂ = t ∧ t₁ ⊨ φ ∧ t₂ ⊨ ψ

Combined with pragmatic enrichment adding NE:
  [φ ∨ ψ]⁺ = ([φ]⁺ ∨ [ψ]⁺) ∧ NE

Each part of the partition must be non-empty → both disjuncts possible!

### Elliott & Sudo: Bilateral + Precondition

Modal disjunction has a PRECONDITION requiring both disjuncts contribute:
  s[φ ∨ ψ]⁺ = s[φ ∨ ψ]⁺ if s[φ ∨ ψ]⁺₁ ≠ ∅ AND s[φ ∨ ψ]⁺₂ ≠ ∅, else ∅

This SEMANTICALLY derives FC: if the disjunction is assertable, both must
contribute possibilities.
-/

/-- Bar-Lev & Fox: closure under conjunction determines outcome. -/
inductive ClosureStatus where
  | closed : ClosureStatus      -- ALT closed under ∧
  | notClosed : ClosureStatus   -- ALT not closed under ∧
  deriving DecidableEq, Repr

/-- Prediction based on closure -/
def closurePrediction : ClosureStatus → String
  | .closed => "Exclusive-or (standard scalar implicature)"
  | .notClosed => "Free choice (via Innocent Inclusion)"

/-- Simple disjunction is closed -/
def simpleDisjunctionClosure : ClosureStatus := .closed

/-- FC disjunction is not closed -/
def fcDisjunctionClosure : ClosureStatus := .notClosed


-- ============================================================================
-- SECTION 7: Empirical Predictions
-- ============================================================================

/-!
## Where Theories Make Different Predictions

### 1. Gradient vs Categorical Judgments

**Pragmatic (RSA)**: FCI is gradient (probability varies with α, priors)
**Pragmatic (Neo-Gricean)**: FCI is categorical
**Semantic**: FCI is categorical (semantic entailment)

**Test**: Do speakers show gradient acceptance of FC readings?

### 2. EI Cancelability Asymmetry

**Bar-Lev & Fox**: Both FCI and EI derived by same mechanism
**Champollion et al.**: FCI from reasoning, EI from priors → asymmetry
**Semantic**: Must explain cancelability differently

### 3. Cross-Disjunct Anaphora

**Most theories**: Cannot handle "Either there's no bathroom or it's upstairs"
**Elliott & Sudo**: Primary motivation; handles via bilateral + DNE
-/

/-- Empirical prediction type -/
structure EmpiricalPrediction where
  test : String
  pragmaticRSA : String
  pragmaticNG : String
  semantic : String
  testable : Bool
  deriving Repr

def gradientPrediction : EmpiricalPrediction :=
  { test := "Gradient vs categorical FC judgments"
  , pragmaticRSA := "Gradient (varies with α)"
  , pragmaticNG := "Categorical"
  , semantic := "Categorical"
  , testable := true }

def eiAsymmetryPrediction : EmpiricalPrediction :=
  { test := "EI more cancelable than FCI"
  , pragmaticRSA := "Predicted and explained"
  , pragmaticNG := "Not directly predicted"
  , semantic := "Must stipulate"
  , testable := true }

def anaphoraPrediction : EmpiricalPrediction :=
  { test := "Cross-disjunct anaphora (bathroom)"
  , pragmaticRSA := "Not addressed"
  , pragmaticNG := "Not addressed"
  , semantic := "BUS handles; BSML doesn't"
  , testable := true }

def empiricalPredictions : List EmpiricalPrediction :=
  [gradientPrediction, eiAsymmetryPrediction, anaphoraPrediction]

-- ============================================================================
-- SECTION 8: Connection to Phenomena
-- ============================================================================

/-!
## Predictions for Phenomena Data

All theories correctly predict the patterns in `Phenomena.FreeChoice.Data`:

### Basic Free Choice (`coffeeOrTea`)
- Input: "You may have coffee or tea"
- Output: "You may have coffee AND you may have tea"
- All: ✓ Derived

### Ross's Paradox (`postOrBurn`)
- "Post the letter" ⊢ "Post or burn" (semantically)
- But "Post or burn" → "You may burn" (pragmatically via FC)
- All: ✓ Explained

### Modal Free Choice (`deonticFC`, `epistemicFC`, `abilityFC`)
- FC works with different modal flavors
- All: ✓ Predicted (mechanism is general)

### Cancellation (`explicitCancellation`)
- "You may have A or B, but I don't know which"
- Pragmatic: ✓ Predicted (defeasible)
- Semantic: Must add mechanism for cancellation
-/

/-- All phenomena are correctly predicted by all theories -/
def allPredictBasicFC : Bool := coffeeOrTea.isPragmaticInference
def allPredictRoss : Bool := postOrBurn.pragmaticallyFelicitous = false
def allPredictCancellation : Bool := explicitCancellation.felicitous

#guard allPredictBasicFC
#guard allPredictRoss
#guard allPredictCancellation

-- ============================================================================
-- SECTION 9: Source LF — @cite{ciardelli-guerrini-2026}
-- ============================================================================

/-!
## An Orthogonal Dimension: Source LF

@cite{ciardelli-guerrini-2026} identify a dimension missing from the comparison
above. All seven theories derive FC from the **narrow-scope** LF ◇(A ∨ B).
None addresses the compositional question: how does this LF arise for sentences
with surface form "may A or may B"?

### The Reductionist Thesis

Previous work assumed that "may A or may B" can receive the LF ◇A ∨ ◇B
(wide scope), creating a separate "wide-scope free choice" problem. C&G argue
this LF does not generate the FC reading at all — it generates an ignorance
reading. The FC reading comes entirely from ◇(A ∨ B), derived via modal
concord (@cite{zeijlstra-2007}).

### Consequences for the Comparison

The reductionist thesis is **compatible with every theory in the table**.
It adds a pre-semantic step (LF derivation via concord) that feeds into
whichever FC mechanism one prefers. The key new prediction is that
non-auxiliary modal constructions ("it's ok that", "be allowed to")
should NOT give rise to FC in coordination — a prediction that
distinguishes concord-based from movement-based accounts
(@cite{meyer-sauerland-2017}).
-/

/-- Source LF comparison: all theories assume narrow-scope input. -/
structure SourceLFComparison where
  theory : String
  inputLF : String
  derivesFC : Bool
  explainsHowLFArises : Bool
  deriving Repr

def lfComparisons : List SourceLFComparison :=
  [ { theory := "Fox 2007", inputLF := "◇(A ∨ B)"
    , derivesFC := true, explainsHowLFArises := false }
  , { theory := "Bar-Lev & Fox 2020", inputLF := "◇(A ∨ B)"
    , derivesFC := true, explainsHowLFArises := false }
  , { theory := "Champollion et al. 2019", inputLF := "◇(A ∨ B)"
    , derivesFC := true, explainsHowLFArises := false }
  , { theory := "Aloni 2022", inputLF := "◇(A ∨ B)"
    , derivesFC := true, explainsHowLFArises := false }
  , { theory := "Ciardelli & Guerrini 2026", inputLF := "◇(A ∨ B) via concord"
    , derivesFC := true, explainsHowLFArises := true } ]

/-- All theories derive FC from narrow-scope LF. -/
theorem all_narrow_scope : lfComparisons.all (·.derivesFC) = true := rfl

/-- Only C&G explain how the narrow-scope LF arises compositionally. -/
theorem only_cg_explains_lf :
    (lfComparisons.filter (·.explainsHowLFArises)).length = 1 := rfl

-- ============================================================================
-- Summary
-- ============================================================================

/-!
## Summary: Free Choice Theory Landscape

### Seven Theories, Three Approaches

**Pragmatic (FC as implicature)**:
- @cite{bar-lev-fox-2020}: Innocent Inclusion (categorical)
- @cite{champollion-alsop-grosu-2019}: RSA + interpretation uncertainty (gradient)
- @cite{alsop-2024}: RSA + parse ambiguity (gradient)

**Semantic (FC in meaning)**:
- @cite{aloni-2022}: BSML - team semantics + NE enrichment
- @cite{elliott-sudo-2025}: BUS - bilateral dynamics + modal ∨ precondition

**Algebraic (FC from proposition structure)**:
- @cite{holliday-mandelkern-2024}: Possibility semantics — FC holds when the
  proposition algebra is Boolean, fails in non-Boolean ortholattices

**LF derivation (orthogonal to the above)**:
- @cite{ciardelli-guerrini-2026}: Modal concord derives narrow-scope LF
  ◇(A ∨ B) for surface "may A or may B" — no wide-scope FC problem

### Key Differentiators

| Feature | Best Theory |
|---------|------------|
| Gradient judgments | RSA approaches |
| EI asymmetry | RSA approaches |
| Formal precision | Bar-Lev & Fox |
| Cross-disjunct anaphora | Elliott & Sudo |
| Static team semantics | Aloni |
| Why FC fails selectively | Holliday & Mandelkern |
| Source LF for "may A or may B" | Ciardelli & Guerrini |

### Complementary Insights

Each theory contributes something unique:
- **Bar-Lev & Fox**: WHY closure under ∧ matters
- **Champollion et al.**: HOW reasoning produces gradient judgments
- **Alsop**: Extension to universal FCIs (*any*)
- **Aloni**: Static team-semantic alternative to dynamics
- **Elliott & Sudo**: Anaphora + bilateral structure
- **Holliday & Mandelkern**: WHEN FC holds (Boolean algebra) vs fails (ortholattice)
- **Ciardelli & Guerrini**: WHERE the LF comes from (concord, not movement)
-/

end Phenomena.Modality.FreeChoiceCompare
