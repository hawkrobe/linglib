import Linglib.Discourse.CommonGround
import Linglib.Semantics.Questions.Basic

/-!
# Issue extraction
[ciardelli-groenendijk-roelofsen-2018]

The issue-side observable on discourse states: `HasIssue` extracts the
current issue (a `Question W`) the way `CommonGround.HasContextSet`
extracts the context set. In inquisitive pragmatics the context is an
issue and the context set is its informative content
([ciardelli-groenendijk-roelofsen-2018]); frameworks tracking both
projections relate them per instance (e.g. how much of the context set
an issue's informative content retains is a framework fact, not a law —
see the Krifka monopolar/bipolar contrast in
`Discourse/Commitment/Space.lean`).

## Main definitions

* `Discourse.HasIssue` — extraction of the current issue from a
  discourse state.
-/

namespace Discourse

/-- A discourse state from which the current issue can be extracted. -/
class HasIssue (S : Type*) (W : outParam Type*) where
  toIssue : S → Question W

namespace HasIssue

variable {S W : Type*} [HasIssue S W]

/-- An information state settles a discourse state's issue iff it
    resolves the extracted `Question`. -/
abbrev settles (i : Set W) (s : S) : Prop := i ∈ toIssue s

end HasIssue

/-- The canonical instance: an issue is its own extraction. -/
instance {W : Type*} : HasIssue (Question W) W where
  toIssue := id

end Discourse
