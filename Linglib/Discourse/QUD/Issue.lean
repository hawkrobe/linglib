module

public import Linglib.Discourse.CommonGround
public import Linglib.Semantics.Questions.Basic

/-!
# Issue extraction

The issue-side observable on discourse states: `HasIssue` extracts the current issue, a
`Question W`, the way `HasCommonGround` extracts the common ground. In inquisitive pragmatics
the context is an issue and the context set is its informative content; frameworks tracking both
projections relate them per instance. How much of the context set an issue's informative content
retains is a fact about the framework, not a law: on a commitment space a bipolar question
raises an issue and a monopolar question does not (`Studies/Krifka2015.lean`).

## Main definitions

* `Discourse.HasIssue`: extraction of the current issue from a discourse state.

## References

* [I. Ciardelli, J. Groenendijk and F. Roelofsen, *Inquisitive Semantics*
  (2018)][ciardelli-groenendijk-roelofsen-2018]
-/

@[expose] public section

namespace Discourse

/-- A discourse state from which the current issue can be extracted. -/
class HasIssue (S : Type*) (W : outParam Type*) where
  toIssue : S → Question W

namespace HasIssue

variable {S W : Type*} [HasIssue S W]

/-- An information state settles a discourse state's issue iff it resolves the extracted
`Question`. -/
abbrev settles (i : Set W) (s : S) : Prop := i ∈ toIssue s

end HasIssue

/-- An issue is its own extraction. -/
instance {W : Type*} : HasIssue (Question W) W where
  toIssue := id

end Discourse
