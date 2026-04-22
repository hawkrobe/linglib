/-!
# Implicature Types

Theory-neutral data types for scalar implicature phenomena.
-/

namespace Interfaces

/-- The possible implicature outcomes for a scalar position. -/
inductive ImplicatureStatus where
  /-- Implicature is derived (Bel_S(not psi) or P > threshold) -/
  | triggered
  /-- Implicature is available but not required -/
  | possible
  /-- Implicature is blocked (DE context, no competence) -/
  | blocked
  /-- No scalar item / irrelevant position -/
  | absent
  deriving Repr, DecidableEq

/-- Coverage status for a phenomenon. -/
inductive CoverageStatus where
  | complete      -- Modeled and verified
  | incomplete    -- Could be modeled, formalization missing
  | outOfScope    -- Theory doesn't address this phenomenon
  | wrong         -- Prediction conflicts with data
  deriving Repr, DecidableEq

/-- Pragmatic phenomena that theories might cover -/
inductive PragmaticPhenomenon where
  | scalarImplicature      -- Basic SI (some -> not all)
  | deBlocking             -- SI blocked in DE contexts
  | taskEffect             -- Asking about SI raises rates
  | referenceGames         -- Ad-hoc implicatures in reference games
  | knowledgeCancellation  -- SI varies with speaker knowledge
  | exhaustivity           -- "Who came? John" -> only John
  | freeChoice             -- "You may have cake or ice cream" -> both permitted
  deriving Repr, DecidableEq

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

/-- A task effect test case from @cite{geurts-pouscoulous-2009} -/
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

/-- Compare a theory's predicted rate to empirical data. -/
def rateMatchesData (predictedRate observedRate : Nat) (tolerance : Nat := 5) : Bool :=
  let diff := if predictedRate > observedRate
              then predictedRate - observedRate
              else observedRate - predictedRate
  diff <= tolerance

end Interfaces
