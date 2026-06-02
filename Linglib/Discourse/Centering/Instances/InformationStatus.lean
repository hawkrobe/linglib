import Linglib.Discourse.Centering.Defs
import Linglib.Features.Givenness
import Mathlib.Order.Basic

/-!
# Centering — Information-Status Cf Ranking
[strube-hahn-1999] [prince-1981]
[gundel-hedberg-zacharski-1993]

Strube-Hahn's 3-tier information-status ranker (HEARER-OLD > MEDIATED
> HEARER-NEW) as a `CfRanker` instance. `ofGivenness` projects GHZ's
6-tier `GivennessStatus` onto the Strube-Hahn tiers.
-/

set_option autoImplicit false

namespace Discourse.Centering

open Features (GivennessStatus)

/-- Strube-Hahn's information-status 3-tier taxonomy. -/
inductive StrubeHahnInfoStatus where
  /-- Discourse-old or unused/evoked. Highest salience. -/
  | hearerOld
  /-- Inferable, containing-inferable, or anchored-brand-new. -/
  | mediated
  /-- Brand-new entity. Lowest salience. -/
  | hearerNew
  deriving DecidableEq, Repr, Fintype, Inhabited

/-- Strube-Hahn IS rank on `Nat`: HEARER-OLD = 2 (highest Centering
    rank, matching `≺ = more salient`), MEDIATED = 1, HEARER-NEW = 0. -/
def StrubeHahnInfoStatus.rank : StrubeHahnInfoStatus → Nat
  | .hearerOld  => 2
  | .mediated   => 1
  | .hearerNew  => 0

/-- The Strube-Hahn Cf-ranker instance — sibling of `GrammaticalRole`,
    enabling the parametric Centering story PSDH §4.4 evaluate. -/
instance : CfRanker StrubeHahnInfoStatus where
  rank := StrubeHahnInfoStatus.rank

/-- Total order via the rank pullback, mirroring the `LinearOrder
    GrammaticalRole` instance in the sibling file. -/
instance : LinearOrder StrubeHahnInfoStatus := CfRanker.toLinearOrder _

/-- Project GHZ's 6-tier `GivennessStatus` onto Strube-Hahn's 3-tier
    information status, via the GHZ → Prince → Strube-Hahn chain. -/
def StrubeHahnInfoStatus.ofGivenness :
    GivennessStatus → StrubeHahnInfoStatus
  | .inFocus              => .hearerOld
  | .activated            => .hearerOld
  | .familiar             => .hearerOld
  | .uniquelyIdentifiable => .mediated
  | .referential          => .mediated
  | .typeIdentifiable     => .hearerNew

/-- MEDIATED is reachable via `uniquelyIdentifiable` (and `referential`). -/
theorem mediated_reachable :
    ∃ g : GivennessStatus, StrubeHahnInfoStatus.ofGivenness g = .mediated :=
  ⟨.uniquelyIdentifiable, rfl⟩

/-- The projection is rank-monotone: more activated GHZ tiers map to
    higher Strube-Hahn ranks. -/
theorem ofGivenness_monotone (a b : GivennessStatus) :
    a.rank ≥ b.rank →
    (StrubeHahnInfoStatus.ofGivenness a).rank ≥
      (StrubeHahnInfoStatus.ofGivenness b).rank := by
  cases a <;> cases b <;> decide

end Discourse.Centering
