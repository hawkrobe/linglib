import Linglib.Syntax.DependencyGrammar.Basic

/-!
# Head determination criteria

Classification of Universal Dependencies relations by how prototypically
"head-dependent" they are, following [hudson-1990]'s six criteria:
category determination, semantic determination, obligatoriness, selection,
morphological determination, and positional determination. The classifier
buckets each UD relation into core argument, modifier, or function-word
class, and `expectedCriteriaCount` records how many of the six criteria
each class typically satisfies — capturing Hudson's prototype-theoretic
observation that "head" admits degrees rather than a sharp boundary.

## Main declarations

* `RelationClass` — three-way bucketing of UD relations.
* `classifyRelation` — `UD.DepRel → RelationClass`.
* `expectedCriteriaCount` — number of Hudson criteria each class satisfies.

## Implementation notes

Earlier drafts shipped a `HeadCriterion` record bundling a `String` name
with a `Bool` `satisfied` predicate, plus stipulated `List String`
"evidence" records for individual UD relations. That material encoded
conclusions as data and used `String` in proof-relevant positions; it has
been dropped. A future revision should derive each criterion structurally
from `Dependency` and the surrounding tree.
-/

namespace DepGrammar.HeadCriteria

open DepGrammar

/-! ### Classification of UD relations -/

/-- Three-way bucketing of UD relations by how prototypically
head-dependent they are. -/
inductive RelationClass where
  /-- Core arguments (`nsubj`, `obj`, …): satisfy all six criteria. -/
  | coreArgument
  /-- Modifiers (`amod`, `advmod`, …): obligatoriness typically fails. -/
  | modifier
  /-- Function-word relations (`det`, `aux`, `case`, …): controversial. -/
  | functionWord
  deriving Repr, DecidableEq

/-- Classify a UD relation by how prototypically "head-dependent" it is.
Core arguments and clausal complements bucket as `coreArgument`; modifiers
and obliques as `modifier`; function-word relations as `functionWord`. -/
def classifyRelation : UD.DepRel → RelationClass
  | .nsubj | .obj | .iobj | .csubj | .ccomp | .xcomp => .coreArgument
  | .amod | .advmod | .nmod | .obl | .advcl | .acl => .modifier
  | .det | .aux | .case_ | .mark | .cop | .cc => .functionWord
  | _ => .modifier

/-- Number of Hudson criteria each relation class typically satisfies:
core arguments satisfy all six; modifiers typically fail obligatoriness
and one positional criterion; function-word relations are controversial. -/
def expectedCriteriaCount : RelationClass → Nat
  | .coreArgument => 6
  | .modifier => 3
  | .functionWord => 4

/-! ### Sanity checks -/

theorem nsubj_isCoreArgument : classifyRelation .nsubj = .coreArgument := rfl

theorem obj_isCoreArgument : classifyRelation .obj = .coreArgument := rfl

theorem det_isFunctionWord : classifyRelation .det = .functionWord := rfl

theorem aux_isFunctionWord : classifyRelation .aux = .functionWord := rfl

/-- Core arguments are expected to satisfy strictly more criteria than
either modifiers or function words — the prototype-theoretic claim. -/
theorem coreArgument_mostCriteria :
    expectedCriteriaCount .coreArgument > expectedCriteriaCount .modifier ∧
    expectedCriteriaCount .coreArgument > expectedCriteriaCount .functionWord := by
  decide

end DepGrammar.HeadCriteria
