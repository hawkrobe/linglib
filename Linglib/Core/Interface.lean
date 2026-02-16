import Linglib.Core.Basic
import Linglib.Core.QUD
import Linglib.Core.Proposition

/-!
# Theory Comparison Interfaces

Typeclasses and structures for comparing syntactic, semantic, and pragmatic
theories on a shared vocabulary. Each theory provides an instance; comparison
modules (`Comparisons/`) consume them.

Consolidated from seven files in `Core/Interfaces/`:
- SemanticStructure, CombinationSchema, BindingSemantics, ScopeTheory
- ImplicatureTheory, FelicityCondition, CoreferenceTheory
-/

-- ════════════════════════════════════════════════════════════════════════════
-- §1  Syntax–Semantics Interfaces
-- ════════════════════════════════════════════════════════════════════════════

/-! ### Semantic Structure

Typeclasses defining what compositional semantics needs from syntax.
Parameterized over an arbitrary type system `T` — Semantics.Montague instantiates
with `Ty`, but other theories can supply their own. -/

namespace Core.Interfaces

/-- Access to lexical/terminal content. -/
class HasTerminals (S : Type) where
  /-- Get terminal content if this is a leaf node -/
  getTerminal : S → Option String

/-- Binary decomposition for Functional Application and Predicate Modification. -/
class HasBinaryComposition (S : Type) where
  /-- Decompose into two children if this is a binary node -/
  getBinaryChildren : S → Option (S × S)

/-- Unary decomposition for H&K's Non-Branching Nodes rule. -/
class HasUnaryProjection (S : Type) where
  /-- Get single child if this is a unary node -/
  getUnaryChild : S → Option S

/-- Binding sites for λ-abstraction. -/
class HasBinding (S : Type) where
  /-- Get binding index and body if this is a binder -/
  getBinder : S → Option (Nat × S)

/-- Access to semantic types, parameterized over the type system `T`. -/
class HasSemanticType (S : Type) (T : Type) where
  /-- Get the semantic type of this node -/
  getType : S → Option T

/-- Full semantic structure for H&K-style interpretation. -/
class SemanticStructure (S : Type) (T : Type) extends
    HasTerminals S,
    HasBinaryComposition S,
    HasUnaryProjection S,
    HasBinding S,
    HasSemanticType S T

/-- Check if a node is a terminal. -/
def isTerminal {S : Type} [HasTerminals S] (s : S) : Bool :=
  (HasTerminals.getTerminal s).isSome

/-- Check if a node is binary-branching. -/
def isBinary {S : Type} [HasBinaryComposition S] (s : S) : Bool :=
  (HasBinaryComposition.getBinaryChildren s).isSome

/-- Check if a node is a binder. -/
def isBinder {S : Type} [HasBinding S] (s : S) : Bool :=
  (HasBinding.getBinder s).isSome

end Core.Interfaces

/-! ### Combination Schema

Theory-neutral interface for Müller's (2013) three universal combination schemata.

All syntactic theories (Minimalism, HPSG, CCG, CxG, DG) converge on three
fundamental modes of combination:

| Schema | Minimalism | HPSG | CCG | DG |
|--------|-----------|------|-----|-----|
| Head-Complement | Ext Merge (1st) | Head-Comp | fapp/bapp | obj/det/... dep |
| Head-Specifier | Ext Merge (later) | Head-Subj | T+bapp | subj dep |
| Head-Filler | Int Merge | Head-Filler | fcomp/bcomp | non-proj dep |

## Reference

Müller, S. (2013). Unifying Everything: Some Remarks on Simpler Syntax,
Construction Grammar, Minimalism, and HPSG. Language, 89(4), 920–950. -/

namespace Core.Interfaces

/-- Müller's three universal combination schemata (§2).

Every syntactic theory implements these three modes of combination,
though they use different terminology and formalisms. -/
inductive CombinationKind where
  /-- Head combines with its complement (first-merged argument).
      Minimalism: External Merge (first); HPSG: Head-Complement Schema;
      CCG: forward/backward application; DG: core dependency (obj, det, ...). -/
  | headComplement
  /-- Head combines with its specifier (later-merged argument).
      Minimalism: External Merge (later); HPSG: Head-Subject Schema;
      CCG: type-raise + backward app; DG: subject dependency. -/
  | headSpecifier
  /-- Filler combines with a gapped structure (long-distance dependency).
      Minimalism: Internal Merge; HPSG: Head-Filler Schema;
      CCG: forward/backward composition; DG: non-projective dependency. -/
  | headFiller
  deriving Repr, DecidableEq, BEq

/-- Core convergence: a theory provides three combination schemata.

This is the minimal interface for Müller's convergence claim.
`T` is a theory tag type (e.g., `Minimalism`, `HPSG`).
`Expr` is the theory's expression type (e.g., `SyntacticObject`, `Sign`). -/
class HasCombinationSchemata (T : Type) where
  /-- The expression type for this theory -/
  Expr : Type
  /-- Classify a combination of head + nonHead → result as one of the three schemata -/
  classify : Expr → Expr → Expr → Option CombinationKind
  /-- Get the category of an expression (if available) -/
  catOf : Expr → Option UD.UPOS

/-- Müller's labeling claim (§2.1): the head determines the category of the result.

This is the Head Feature Principle: in any combination, the category
of the resulting phrase equals the category of the head daughter. -/
class HasHeadFeaturePrinciple (T : Type) extends HasCombinationSchemata T where
  /-- The head's category determines the result's category -/
  headDeterminesLabel : ∀ head nonHead result,
    classify head nonHead result ≠ none →
    catOf result = catOf head

/-- Coordination diagnostic (§2.2): same category required.

Coordination is a diagnostic for constituency: only expressions of the
same category can coordinate. This holds across all theories. -/
class HasCoordination (T : Type) extends HasCombinationSchemata T where
  /-- Whether two expressions can coordinate -/
  canCoordinate : Expr → Expr → Bool

end Core.Interfaces

/-! ### Binding Semantics

Abstract interface for H&K-style assignment-based binding semantics. -/

namespace Interfaces.BindingSemantics

/-- A position in a syntactic structure. -/
structure Position where
  /-- Linear index (word position) -/
  index : Nat
  deriving Repr, DecidableEq, BEq, Hashable

/-- A binding relation: which binder binds which bindee. -/
structure BindingRelation where
  /-- Position of the binder (quantifier, λ-operator, etc.) -/
  binder : Position
  /-- Position of the bindee (pronoun, trace, etc.) -/
  bindee : Position
  /-- The variable index used in the assignment function -/
  varIndex : Nat
  deriving Repr, DecidableEq

/-- A complete binding configuration for a structure. -/
structure BindingConfig where
  /-- All binding relations in the structure -/
  bindings : List BindingRelation
  /-- Positions that are free (unbound) variables -/
  freeVariables : List (Position × Nat)  -- position and its index
  deriving Repr

/-- What a syntactic theory must provide for H&K binding semantics. -/
class HasBindingConfig (T : Type) where
  /-- The theory's syntactic structure type -/
  Structure : Type
  /-- Extract binding configuration from a structure -/
  bindingConfig : Structure → BindingConfig

variable {T : Type} [HasBindingConfig T]

/-- Get all binders in a structure -/
def binders (s : HasBindingConfig.Structure T) : List Position :=
  (HasBindingConfig.bindingConfig s).bindings.map (·.binder)

/-- Get all bindees in a structure -/
def bindees (s : HasBindingConfig.Structure T) : List Position :=
  (HasBindingConfig.bindingConfig s).bindings.map (·.bindee)

/-- Is position p bound in structure s? -/
def isBound (s : HasBindingConfig.Structure T) (p : Position) : Bool :=
  (HasBindingConfig.bindingConfig s).bindings.any (·.bindee == p)

/-- Is position p a binder in structure s? -/
def isBinder (s : HasBindingConfig.Structure T) (p : Position) : Bool :=
  (HasBindingConfig.bindingConfig s).bindings.any (·.binder == p)

/-- Get the binder for a bound position (if any) -/
def binderOf (s : HasBindingConfig.Structure T) (p : Position) : Option Position :=
  (HasBindingConfig.bindingConfig s).bindings.find? (·.bindee == p) |>.map (·.binder)

/-- Get the variable index for a bound position -/
def varIndexOf (s : HasBindingConfig.Structure T) (p : Position) : Option Nat :=
  (HasBindingConfig.bindingConfig s).bindings.find? (·.bindee == p) |>.map (·.varIndex)

/-- Get all positions bound by a given binder -/
def boundBy (s : HasBindingConfig.Structure T) (binder : Position) : List Position :=
  (HasBindingConfig.bindingConfig s).bindings.filter (·.binder == binder) |>.map (·.bindee)

/-- A binding configuration is well-formed. -/
def BindingConfig.wellFormed (bc : BindingConfig) : Bool :=
  -- No double binding
  let noDoubleBinding := bc.bindings.all λ r1 =>
    bc.bindings.all λ r2 =>
      r1.bindee != r2.bindee || r1.binder == r2.binder
  -- No self-binding
  let noSelfBinding := bc.bindings.all λ r =>
    r.binder != r.bindee
  -- Consistent indices
  let consistentIndices := bc.bindings.all λ r1 =>
    bc.bindings.all λ r2 =>
      r1.binder != r2.binder || r1.varIndex == r2.varIndex
  noDoubleBinding && noSelfBinding && consistentIndices

/-- A structure has well-formed binding -/
def hasWellFormedBinding (s : HasBindingConfig.Structure T) : Bool :=
  (HasBindingConfig.bindingConfig s).wellFormed

variable {T1 T2 : Type} [HasBindingConfig T1] [HasBindingConfig T2]

/-- Two theories agree on binding if they produce equivalent configurations. -/
def bindingEquivalent
    (s1 : HasBindingConfig.Structure T1)
    (s2 : HasBindingConfig.Structure T2) : Bool :=
  let bc1 := HasBindingConfig.bindingConfig s1
  let bc2 := HasBindingConfig.bindingConfig s2
  -- Check same binder-bindee pairs (ignoring indices)
  let pairs1 := bc1.bindings.map λ r => (r.binder, r.bindee)
  let pairs2 := bc2.bindings.map λ r => (r.binder, r.bindee)
  pairs1.all (pairs2.contains ·) && pairs2.all (pairs1.contains ·)

end Interfaces.BindingSemantics

/-! ### Scope Theory

Abstract interface for theories that determine available scope readings. -/

namespace ScopeTheory

/-- A scope reading: an ordering of scope-taking elements. -/
structure ScopeReading where
  /-- Identifiers for scope-taking elements, in scope order (widest first) -/
  ordering : List String
  deriving DecidableEq, BEq, Repr, Inhabited

/-- The surface scope reading (linear order = scope order) -/
def ScopeReading.surface (elements : List String) : ScopeReading :=
  ⟨elements⟩

/-- Reverse (inverse) scope reading -/
def ScopeReading.inverse (elements : List String) : ScopeReading :=
  ⟨elements.reverse⟩

/-- The set of available scope readings for a form. -/
structure AvailableScopes where
  /-- All available scope readings -/
  readings : List ScopeReading
  /-- At least one reading must be available -/
  nonempty : readings ≠ [] := by simp
  deriving Repr

/-- Singleton: only one reading available -/
def AvailableScopes.singleton (r : ScopeReading) : AvailableScopes :=
  ⟨[r], by simp⟩

/-- Binary: exactly two readings (surface and inverse) -/
def AvailableScopes.binary (surface inverse : ScopeReading) : AvailableScopes :=
  ⟨[surface, inverse], by simp⟩

/-- Check if a specific reading is available -/
def AvailableScopes.hasReading (a : AvailableScopes) (r : ScopeReading) : Bool :=
  a.readings.contains r

/-- Is the scope ambiguous (more than one reading)? -/
def AvailableScopes.isAmbiguous (a : AvailableScopes) : Bool :=
  a.readings.length > 1

/-- Typeclass for theories that determine available scope readings. -/
class HasAvailableScopes (T : Type) (Form : Type) where
  /-- Determine available scope readings for a form -/
  availableScopes : Form → AvailableScopes

/-- Convenience function to get available scopes -/
def getAvailableScopes {T Form : Type} [HasAvailableScopes T Form] (form : Form) : AvailableScopes :=
  HasAvailableScopes.availableScopes (T := T) form

/-- A ranked preference over scope readings. -/
structure ScopePreference where
  /-- Readings ranked by preference (most preferred first) -/
  ranking : List ScopeReading
  /-- Scores for each reading (higher = more preferred) -/
  scores : List Float
  /-- Rankings and scores must align -/
  aligned : ranking.length = scores.length := by simp
  deriving Repr

/-- Typeclass for theories that rank scope readings. -/
class HasScopePreference (T : Type) (Form Context : Type) where
  /-- Rank available scope readings in context -/
  preferScopes : Form → Context → AvailableScopes → ScopePreference

/-- Specialized interface for binary scope ambiguity. -/
structure BinaryScopeForm (α : Type) where
  /-- The form/derivation -/
  form : α
  /-- First scope-taker (surface-wide) -/
  scopeTaker1 : String
  /-- Second scope-taker (surface-narrow) -/
  scopeTaker2 : String
  deriving Repr

/-- Binary scope availability: surface only, inverse only, or both. -/
inductive BinaryScopeAvailability where
  | surfaceOnly   -- Only scopeTaker1 > scopeTaker2
  | inverseOnly   -- Only scopeTaker2 > scopeTaker1
  | ambiguous     -- Both readings available
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Convert to general AvailableScopes -/
def BinaryScopeAvailability.toAvailableScopes
    (b : BinaryScopeAvailability) (s1 s2 : String) : AvailableScopes :=
  match b with
  | .surfaceOnly => AvailableScopes.singleton (ScopeReading.surface [s1, s2])
  | .inverseOnly => AvailableScopes.singleton (ScopeReading.inverse [s1, s2])
  | .ambiguous => AvailableScopes.binary
      (ScopeReading.surface [s1, s2])
      (ScopeReading.inverse [s1, s2])

/-- Typeclass for binary scope theories. -/
class HasBinaryScope (T : Type) (Form : Type) where
  /-- Determine binary scope availability -/
  binaryScope : BinaryScopeForm Form → BinaryScopeAvailability

end ScopeTheory

-- ════════════════════════════════════════════════════════════════════════════
-- §2  Semantics–Pragmatics Interfaces
-- ════════════════════════════════════════════════════════════════════════════

/-! ### Implicature Theory

Abstract interface for scalar implicature predictions. -/

namespace Interfaces

/-- The possible implicature outcomes for a scalar position. -/
inductive ImplicatureStatus where
  /-- Implicature is derived (Bel_S(¬ψ) or P > threshold) -/
  | triggered
  /-- Implicature is available but not required -/
  | possible
  /-- Implicature is blocked (DE context, no competence) -/
  | blocked
  /-- No scalar item / irrelevant position -/
  | absent
  deriving Repr, DecidableEq

/-- A theory that makes predictions about scalar implicatures. -/
class ImplicatureTheory (T : Type) where
  /-- The theory's internal representation of an utterance in context -/
  Structure : Type

  /-- Parse words into the theory's representation.
      Returns `none` if the theory can't parse this input. -/
  parse : List Word → Option Structure

  /-- Predict the implicature status for a scalar position.

      Position indexes into the word list:
      - "some students sleep" → position 0 = some (scalar item)

      Returns the theory's prediction about whether an implicature arises. -/
  implicatureStatus : Structure → Nat → ImplicatureStatus

  /-- Optional: strength/probability (0-100 scale).

      NeoGricean: baseline rate (e.g., 35% for contextualism)
      RSA: L1 probability converted to percentage

      Returns `none` if the theory doesn't provide quantitative predictions. -/
  implicatureStrength : Structure → Nat → Option Nat

  /-- Does the theory predict implicature blocked in downward-entailing contexts? -/
  predictsDEBlocking : Bool

  /-- Does the theory predict a task effect (asking about SI raises rate)? -/
  predictsTaskEffect : Bool

  /-- Predicted baseline implicature rate (%) in neutral contexts -/
  predictedBaselineRate : Nat

variable {T : Type} [ImplicatureTheory T]

/-- Check if implicature is derived at position pos -/
def derivesImplicature (s : ImplicatureTheory.Structure T) (pos : Nat) : Bool :=
  match ImplicatureTheory.implicatureStatus s pos with
  | .triggered => true
  | _ => false

/-- Check if implicature is blocked at position pos -/
def blocksImplicature (s : ImplicatureTheory.Structure T) (pos : Nat) : Bool :=
  match ImplicatureTheory.implicatureStatus s pos with
  | .blocked => true
  | _ => false

/-- Check if implicature is possible (but not required) at position pos -/
def possibleImplicature (s : ImplicatureTheory.Structure T) (pos : Nat) : Bool :=
  match ImplicatureTheory.implicatureStatus s pos with
  | .possible => true
  | _ => false

/-- Check if any implicature arises (triggered or possible) at position pos -/
def anyImplicature (s : ImplicatureTheory.Structure T) (pos : Nat) : Bool :=
  match ImplicatureTheory.implicatureStatus s pos with
  | .triggered => true
  | .possible => true
  | _ => false

variable {T1 T2 : Type} [ImplicatureTheory T1] [ImplicatureTheory T2]

/-- Two theories agree on a sentence at a position if they make the same status prediction -/
def theoriesAgreeOnStatus (ws : List Word) (pos : Nat) : Bool :=
  match ImplicatureTheory.parse (T := T1) ws,
        ImplicatureTheory.parse (T := T2) ws with
  | some s1, some s2 =>
    ImplicatureTheory.implicatureStatus s1 pos ==
    ImplicatureTheory.implicatureStatus s2 pos
  | none, none => true   -- Both can't parse → vacuous agreement
  | _, _ => false        -- One parses, other doesn't → disagreement

/-- Two theories agree on whether an implicature is derived -/
def theoriesAgreeOnDerivation (ws : List Word) (pos : Nat) : Bool :=
  match ImplicatureTheory.parse (T := T1) ws,
        ImplicatureTheory.parse (T := T2) ws with
  | some s1, some s2 =>
    derivesImplicature s1 pos == derivesImplicature s2 pos
  | none, none => true
  | _, _ => false

/-- Two theories agree on DE blocking prediction -/
def theoriesAgreeOnDEPrediction : Bool :=
  ImplicatureTheory.predictsDEBlocking (T := T1) ==
  ImplicatureTheory.predictsDEBlocking (T := T2)

/-- Two theories agree on task effect prediction -/
def theoriesAgreeOnTaskEffect : Bool :=
  ImplicatureTheory.predictsTaskEffect (T := T1) ==
  ImplicatureTheory.predictsTaskEffect (T := T2)

/-- Compare a theory's predicted rate to empirical data. -/
def rateMatchesData (predictedRate observedRate : Nat) (tolerance : Nat := 5) : Bool :=
  let diff := if predictedRate > observedRate
              then predictedRate - observedRate
              else observedRate - predictedRate
  diff <= tolerance

/-- Which theory's baseline is closer to observed data? -/
def closerToData (observed : Nat) : Bool :=
  let diff1 := if ImplicatureTheory.predictedBaselineRate (T := T1) > observed
               then ImplicatureTheory.predictedBaselineRate (T := T1) - observed
               else observed - ImplicatureTheory.predictedBaselineRate (T := T1)
  let diff2 := if ImplicatureTheory.predictedBaselineRate (T := T2) > observed
               then ImplicatureTheory.predictedBaselineRate (T := T2) - observed
               else observed - ImplicatureTheory.predictedBaselineRate (T := T2)
  diff1 < diff2

/-- Coverage status for a phenomenon. -/
inductive CoverageStatus where
  | complete      -- Modeled and verified
  | incomplete    -- Could be modeled, formalization missing
  | outOfScope    -- Theory doesn't address this phenomenon
  | wrong         -- Prediction conflicts with data
  deriving Repr, DecidableEq, BEq

/-- Pragmatic phenomena that theories might cover -/
inductive PragmaticPhenomenon where
  | scalarImplicature      -- Basic SI (some → not all)
  | deBlocking             -- SI blocked in DE contexts
  | taskEffect             -- Asking about SI raises rates
  | referenceGames         -- Ad-hoc implicatures in reference games
  | knowledgeCancellation  -- SI varies with speaker knowledge
  | exhaustivity           -- "Who came? John" → only John
  | freeChoice             -- "You may have cake or ice cream" → both permitted
  deriving Repr, DecidableEq, BEq

/-- Coverage report for a single phenomenon -/
structure PhenomenonCoverage where
  phenomenon : PragmaticPhenomenon
  status : CoverageStatus
  notes : String
  deriving Repr

/-- Full coverage report for a theory -/
structure TheoryCoverage where
  theoryName : String
  phenomena : List PhenomenonCoverage
  deriving Repr

/-- Get status for a phenomenon (helper) -/
def TheoryCoverage.statusFor (tc : TheoryCoverage) (p : PragmaticPhenomenon) : Option CoverageStatus :=
  tc.phenomena.find? (·.phenomenon == p) |>.map (·.status)

/-- Count phenomena by status -/
def TheoryCoverage.countByStatus (tc : TheoryCoverage) (s : CoverageStatus) : Nat :=
  tc.phenomena.filter (·.status == s) |>.length

/-- List incomplete phenomena -/
def TheoryCoverage.incompletePhenomena (tc : TheoryCoverage) : List PragmaticPhenomenon :=
  tc.phenomena.filter (·.status == .incomplete) |>.map (·.phenomenon)

/-- List out-of-scope phenomena -/
def TheoryCoverage.outOfScopePhenomena (tc : TheoryCoverage) : List PragmaticPhenomenon :=
  tc.phenomena.filter (·.status == .outOfScope) |>.map (·.phenomenon)

/-- Summary of what a theory covers vs what's incomplete. -/
structure CoverageSummary where
  /-- Does it derive basic SIs? -/
  derivesBasicSI : Bool
  /-- Does it model DE blocking? -/
  modelsDEBlocking : Bool
  /-- Does it model task effects? -/
  modelsTaskEffect : Bool
  /-- Is baseline rate specified? -/
  hasBaselineRate : Bool
  /-- Notes about incompleteness -/
  incompleteNotes : List String
  deriving Repr

/-- Generate coverage summary for a theory -/
def coverageSummary (T : Type) [ImplicatureTheory T] : CoverageSummary :=
  { derivesBasicSI := ImplicatureTheory.predictedBaselineRate (T := T) > 0
  , modelsDEBlocking := ImplicatureTheory.predictsDEBlocking (T := T)
  , modelsTaskEffect := ImplicatureTheory.predictsTaskEffect (T := T)
  , hasBaselineRate := true  -- All theories must specify this
  , incompleteNotes :=
      (if ImplicatureTheory.predictsDEBlocking (T := T) then []
       else ["DE blocking not modeled"]) ++
      (if ImplicatureTheory.predictsTaskEffect (T := T) then []
       else ["Task effect not modeled"])
  }

/-- A DE blocking test case derived from empirical data. -/
structure DEBlockingTestCase where
  /-- Description of the UE example -/
  ueDescription : String
  /-- Description of the DE example -/
  deDescription : String
  /-- The scalar term -/
  scalarTerm : String
  /-- Expected: implicature arises in UE -/
  expectedUE : Bool
  /-- Expected: implicature blocked in DE -/
  expectedDE : Bool
  deriving Repr

/-- A task effect test case from Geurts & Pouscoulous 2009 -/
structure TaskEffectTestCase where
  /-- Inference task rate (percentage) -/
  inferenceRate : Nat
  /-- Verification task rate (percentage) -/
  verificationRate : Nat
  /-- Is the difference significant? -/
  significant : Bool
  deriving Repr

/-- Result of testing a theory against DE blocking data -/
structure DEBlockingResult where
  /-- Does the theory predict DE blocking? -/
  theoryPredictsDEBlocking : Bool
  /-- Does the data show DE blocking? -/
  datashowsDEBlocking : Bool
  /-- Do they match? -/
  isMatch : Bool
  deriving Repr

/-- Test a theory against a DE blocking test case -/
def testDEBlocking {T : Type} [ImplicatureTheory T] (tc : DEBlockingTestCase) : DEBlockingResult :=
  let theoryPredicts := ImplicatureTheory.predictsDEBlocking (T := T)
  let dataShows := tc.expectedUE && !tc.expectedDE
  { theoryPredictsDEBlocking := theoryPredicts
  , datashowsDEBlocking := dataShows
  , isMatch := theoryPredicts == dataShows
  }

/-- Result of testing a theory against task effect data -/
structure TaskEffectResult where
  /-- Does the theory predict task effect? -/
  theoryPredictsTaskEffect : Bool
  /-- Does the data show task effect? -/
  dataShowsTaskEffect : Bool
  /-- Theory's predicted baseline rate -/
  predictedRate : Nat
  /-- Observed rate (verification task) -/
  observedRate : Nat
  /-- Difference between predicted and observed -/
  rateDifference : Nat
  /-- Does theory match data? -/
  isMatch : Bool
  deriving Repr

/-- Test a theory against task effect data -/
def testTaskEffect {T : Type} [ImplicatureTheory T] (tc : TaskEffectTestCase) (tolerance : Nat := 10) : TaskEffectResult :=
  let theoryPredicts := ImplicatureTheory.predictsTaskEffect (T := T)
  let dataShows := tc.significant && tc.inferenceRate > tc.verificationRate
  let predicted := ImplicatureTheory.predictedBaselineRate (T := T)
  let observed := tc.verificationRate
  let diff := if predicted > observed then predicted - observed else observed - predicted
  { theoryPredictsTaskEffect := theoryPredicts
  , dataShowsTaskEffect := dataShows
  , predictedRate := predicted
  , observedRate := observed
  , rateDifference := diff
  , isMatch := (theoryPredicts == dataShows) && (diff <= tolerance)
  }

/-- A theory captures DE blocking data if its prediction isMatch the pattern. -/
class CapturesDEBlockingPattern (T : Type) [ImplicatureTheory T] where
  /-- The test case from empirical data -/
  testCase : DEBlockingTestCase
  /-- Proof that theory isMatch data -/
  theoryMatchesData : (testDEBlocking (T := T) testCase).isMatch = true

/-- A theory captures task effect data if its predictions match the observations -/
class CapturesTaskEffectData (T : Type) [ImplicatureTheory T] where
  /-- The task effect data -/
  taskEffectData : TaskEffectTestCase
  /-- Tolerance for rate matching -/
  tolerance : Nat := 10
  /-- Proof that theory isMatch task effect pattern -/
  taskEffectMatches : (testTaskEffect (T := T) taskEffectData tolerance).theoryPredictsTaskEffect ==
                      (testTaskEffect (T := T) taskEffectData tolerance).dataShowsTaskEffect
  /-- Proof that predicted rate is close to observed -/
  rateWithinTolerance : (testTaskEffect (T := T) taskEffectData tolerance).rateDifference <= tolerance

/-- Compare a theory's baseline rate to observed data. -/
def compareToObservedRate {T : Type} [ImplicatureTheory T] (observedRate : Nat) : Nat × Nat × Bool :=
  let predicted := ImplicatureTheory.predictedBaselineRate (T := T)
  let diff := if predicted > observedRate then predicted - observedRate else observedRate - predicted
  (predicted, diff, diff <= 10)

/-- Which of two theories is closer to observed rate? -/
def closerToObservedRate {T1 T2 : Type} [ImplicatureTheory T1] [ImplicatureTheory T2]
    (observedRate : Nat) : Bool × Bool :=
  let (_, diff1, _) := compareToObservedRate (T := T1) observedRate
  let (_, diff2, _) := compareToObservedRate (T := T2) observedRate
  (diff1 < diff2, diff1 <= diff2)

end Interfaces

/-! ### Felicity Condition

Abstract interface for felicity/oddness predictions, following the
`ImplicatureTheory` pattern. Provides a unified type for comparing
K&S (2015), Magri (2009), Spector (2014), Fox & Hackl (2006), and
future felicity theories.

## References

- Katzir, R. & Singh, R. (2015). Economy of structure and information.
- Magri, G. (2009). Individual-level predicates and mandatory scalar implicatures.
- Spector, B. (2014). Scalar implicatures, blindness and common knowledge.
- Fox, D. & Hackl, M. (2006). The universal density of measurement. -/

namespace Interfaces

/-- Felicity status for an utterance in context. -/
inductive FelicityStatus where
  /-- The utterance is felicitous (no oddness). -/
  | felicitous
  /-- The utterance is odd (# marks in linguistics). -/
  | odd
  /-- Borderline: some conditions met, others not. -/
  | borderline
  deriving DecidableEq, BEq, Repr

/-- Source of oddness (which condition was violated). -/
inductive OddnessSource where
  /-- Question Condition: QUD trivially settled by CK. -/
  | questionCondition
  /-- Answer Condition: needlessly inferior alternative exists. -/
  | answerCondition
  /-- Both conditions violated. -/
  | both
  /-- Theory doesn't distinguish sources. -/
  | unspecified
  deriving DecidableEq, BEq, Repr

/-- Result of a felicity check: status + optional source information. -/
structure FelicityResult where
  status : FelicityStatus
  source : Option OddnessSource := none
  deriving Repr

/-- A theory that makes predictions about utterance felicity/oddness. -/
class FelicityCondition (T : Type*) where
  /-- Name of the theory. -/
  name : String
  /-- Check whether an input is felicitous, odd, or borderline. -/
  check : T → FelicityResult

variable {T : Type*} [FelicityCondition T]

/-- Is the input felicitous? -/
def isFelicitous (t : T) : Bool :=
  (FelicityCondition.check t).status == .felicitous

/-- Is the input odd? -/
def isOdd (t : T) : Bool :=
  (FelicityCondition.check t).status == .odd

/-- Two felicity theories agree on an input if they give the same status. -/
def felicityAgree {α T₁ T₂ : Type*} [FelicityCondition T₁] [FelicityCondition T₂]
    (f : α → T₁) (g : α → T₂) (a : α) : Bool :=
  (FelicityCondition.check (f a)).status == (FelicityCondition.check (g a)).status

end Interfaces

-- ════════════════════════════════════════════════════════════════════════════
-- §3  Cross-Level Interfaces
-- ════════════════════════════════════════════════════════════════════════════

/-! ### Coreference Theory

Abstract interface for coreference predictions. -/

namespace Interfaces

/-- The possible coreference relationships between two positions. -/
inductive CoreferenceStatus where
  /-- Coreference is obligatory (reflexives with local antecedent) -/
  | obligatory
  /-- Coreference is possible but not required -/
  | possible
  /-- Coreference is blocked (Principle B/C violations) -/
  | blocked
  /-- No prediction (positions not in relevant configuration) -/
  | unspecified
  deriving Repr, DecidableEq

/-- A theory that makes predictions about coreference patterns. -/
class CoreferenceTheory (T : Type) where
  /-- The theory's internal representation of a sentence/structure -/
  Structure : Type

  /-- Parse a list of words into the theory's representation.
      Returns `none` if the theory can't parse this input. -/
  parse : List Word → Option Structure

  /-- Predict the coreference status between positions i and j.

      Positions are indexed from the word list:
      - "John sees himself" → position 0 = John, position 2 = himself

      Returns the theory's prediction about whether these positions
      can/must/cannot corefer. -/
  coreferenceStatus : Structure → Nat → Nat → CoreferenceStatus

  /-- Does the theory predict this sentence is grammatical for coreference?

      A sentence is "grammatical for coreference" if:
      - All obligatory coreferences have valid antecedents
      - No blocked coreferences are forced

      This is the primary prediction we test against empirical data. -/
  grammaticalForCoreference : Structure → Bool

variable {T : Type} [CoreferenceTheory T]

/-- Check if coreference is possible at positions i, j -/
def canCorefer (s : CoreferenceTheory.Structure T) (i j : Nat) : Bool :=
  match CoreferenceTheory.coreferenceStatus s i j with
  | .obligatory => true
  | .possible => true
  | .blocked => false
  | .unspecified => true  -- No constraint means possible

/-- Check if coreference is obligatory at positions i, j -/
def mustCorefer (s : CoreferenceTheory.Structure T) (i j : Nat) : Bool :=
  match CoreferenceTheory.coreferenceStatus s i j with
  | .obligatory => true
  | _ => false

/-- Check if coreference is blocked at positions i, j -/
def cannotCorefer (s : CoreferenceTheory.Structure T) (i j : Nat) : Bool :=
  match CoreferenceTheory.coreferenceStatus s i j with
  | .blocked => true
  | _ => false

/-- Does the theory correctly predict a minimal pair? -/
def capturesMinimalPair (pair : MinimalPair) : Bool :=
  match CoreferenceTheory.parse (T := T) pair.grammatical,
        CoreferenceTheory.parse (T := T) pair.ungrammatical with
  | some sg, some su =>
    CoreferenceTheory.grammaticalForCoreference sg &&
    !CoreferenceTheory.grammaticalForCoreference su
  | _, _ => false  -- Can't parse → doesn't capture

/-- Does the theory capture all pairs in a phenomenon dataset? -/
def capturesPhenomenon (data : PhenomenonData) : Bool :=
  data.pairs.all (capturesMinimalPair (T := T))

variable {T1 T2 : Type} [CoreferenceTheory T1] [CoreferenceTheory T2]

/-- Two theories agree on a sentence if they make the same grammaticality prediction -/
def theoriesAgreeOn (ws : List Word) : Bool :=
  match CoreferenceTheory.parse (T := T1) ws,
        CoreferenceTheory.parse (T := T2) ws with
  | some s1, some s2 =>
    CoreferenceTheory.grammaticalForCoreference s1 ==
    CoreferenceTheory.grammaticalForCoreference s2
  | none, none => true   -- Both can't parse → vacuous agreement
  | _, _ => false        -- One parses, other doesn't → disagreement

/-- Two theories agree on all sentences in a list -/
def theoriesAgreeOnAll (sentences : List (List Word)) : Bool :=
  sentences.all (theoriesAgreeOn (T1 := T1) (T2 := T2))

/-- Two theories agree on a phenomenon dataset -/
def theoriesAgreeOnPhenomenon (data : PhenomenonData) : Bool :=
  data.pairs.all (λ pair =>
    theoriesAgreeOn (T1 := T1) (T2 := T2) pair.grammatical &&
    theoriesAgreeOn (T1 := T1) (T2 := T2) pair.ungrammatical)

/-- Two theories are extensionally equivalent on a class of sentences. -/
def ExtensionallyEquivalentOn (sentences : List (List Word)) : Prop :=
  ∀ ws ∈ sentences, theoriesAgreeOn (T1 := T1) (T2 := T2) ws = true

end Interfaces
