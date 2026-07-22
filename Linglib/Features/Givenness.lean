import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype

/-!
# Givenness — cognitive status of discourse referents

Substrate for the **givenness** axis of information structure (one of
[krifka-2008]'s four IS notions). Two types, for the scalar and the
categorical view of givenness.

* `GivennessStatus` — the [gundel-hedberg-zacharski-1993] (GHZ) six-tier
  Givenness Hierarchy `inFocus > activated > familiar >
  uniquelyIdentifiable > referential > typeIdentifiable`, with a `rank`
  giving GHZ's implicational *status* order (each status entails all
  lower; not a claim about the many-to-many status-to-form mapping).
  Promoted from `Studies/Ariel2001.lean` so it can be shared.
* `BinaryGivenness` — `given | new`, the GHZ coarsening
  (`GivennessStatus.toBinary`) at the identifiable/indefinite boundary
  ([lambrecht-1994] identifiability). Not [prince-1992]'s hearer-old/new
  binary (which cross-cuts identifiability), nor alternatives-based
  givenness (`Alternatives.AltMeaning.Given`; [schwarzschild-1999]
  A-givenness = `isAGiven` in `Studies/KratzerSelkirk2020.lean`);
  a consumer meaning another axis (e.g. discourse-status) should say so.

Sibling GHZ-6 coarsenings/scales: Ariel's 18-tier
`Features.AccessibilityLevel` (`toAccessibility`) and Centering's
[strube-hahn-1999] `StrubeHahnInfoStatus.ofGivenness` (its `mediated`
tier drawn from `uniquelyIdentifiable`/`referential`). [ariel-2001]
argues AccessibilityLevel is better grounded — the lower GHZ tiers lack
independent scalar support — but GHZ-6 is retained as the literature's
canonical scalar scale and is small enough for `decide`. See also
[prince-1981], [chafe-1976], [chafe-1987].
-/

set_option autoImplicit false

namespace Features

/-- [gundel-hedberg-zacharski-1993] six-tier Givenness Hierarchy
    (`inFocus > … > typeIdentifiable`), each status entailing all lower. -/
inductive GivennessStatus where
  /-- In focus: unstressed pronoun — referent currently in attention. -/
  | inFocus
  /-- Activated: that/this/this-N — referent in working memory. -/
  | activated
  /-- Familiar: that-N — referent in long-term memory. -/
  | familiar
  /-- Uniquely identifiable: the-N — hearer can construct the referent
      from the description alone. -/
  | uniquelyIdentifiable
  /-- Referential: indefinite this-N — speaker has a particular
      referent in mind, hearer doesn't yet. -/
  | referential
  /-- Type identifiable: a-N — hearer can construct a representation
      of the *type* of object described. -/
  | typeIdentifiable
  deriving DecidableEq, Repr, Fintype, Inhabited

/-- Numeric rank: `inFocus = 5` (highest), `typeIdentifiable = 0`
    (lowest). Higher rank = more cognitively accessible. -/
def GivennessStatus.rank : GivennessStatus → Nat
  | .inFocus              => 5
  | .activated            => 4
  | .familiar             => 3
  | .uniquelyIdentifiable => 2
  | .referential          => 1
  | .typeIdentifiable     => 0

/-- `given | new`: the GHZ identifiability coarsening
    (`GivennessStatus.toBinary`); see the module docstring for what it is not. -/
inductive BinaryGivenness where
  /-- Given: hearer can identify the referent (GHZ `inFocus`..`uniquelyIdentifiable`). -/
  | given
  /-- New: indefinite, not yet identifiable (GHZ `referential`, `typeIdentifiable`). -/
  | new
  deriving DecidableEq, Repr, Fintype, Inhabited

/-- Numeric rank: `given = 1`, `new = 0`. Higher rank = more given. -/
def BinaryGivenness.rank : BinaryGivenness → Nat
  | .given => 1
  | .new   => 0

/-- GHZ-6 given–new coarsening: identifiable tiers ↦ `given`, indefinite
    tiers ↦ `new`. Makes the module docstring's cut true by construction. -/
def GivennessStatus.toBinary : GivennessStatus → BinaryGivenness
  | .inFocus | .activated | .familiar | .uniquelyIdentifiable => .given
  | .referential | .typeIdentifiable                          => .new

/-- The coarsening is rank-monotone: more accessible GHZ tiers map to `given`. -/
theorem GivennessStatus.toBinary_monotone (a b : GivennessStatus) :
    a.rank ≤ b.rank → a.toBinary.rank ≤ b.toBinary.rank := by
  cases a <;> cases b <;> decide

end Features
