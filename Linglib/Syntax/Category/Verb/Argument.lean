import Linglib.Syntax.ArgumentRole
import Linglib.Syntax.Category.Verb.Basic
import Linglib.Semantics.ArgumentStructure.Linking

/-!
# Verb arguments

`Verb.Argument`: an argument slot of a verb entry — core or oblique, with
its proto-role entailment profile — read off the citation frame by
`Verb.arguments`. The slots are the primitive; role labels are derived
classifications of them: `Argument.thetaLabel` gives the Dowty cluster
label, and `Verb.codingRoles` gives the comparative S/A/P/R/T
classification, which is a function of the frame (A is *defined* as the
more agent-like core argument of a two-place frame), never a stored
feature.

## References

* [comrie-1978]
* [dowty-1991]
* [haspelmath-2021]
-/

open ArgumentStructure

namespace Verb

/-- An argument slot of a verb entry: whether the citation frame realizes
    it as a core nominal or an oblique, and its proto-role entailment
    profile (`none` when the entry leaves it unspecified). -/
structure Argument where
  /-- Core nominal (`true`) vs oblique/adpositional realization. -/
  core : Bool
  /-- Proto-role entailment profile. -/
  entailments : Option EntailmentProfile := none
  deriving Repr, BEq

/-- Derived semantic-role label: the cluster label of the slot's
    entailment profile (`EntailmentProfile.toRole`). -/
def Argument.thetaLabel (a : Argument) : Option ThetaRole :=
  a.entailments.bind EntailmentProfile.toRole

/-- The argument slots of the entry's citation frame: the subject, the
    nominal objects, then one oblique slot per adpositional position, with
    entailments read from the entry (object entailments sit on the theme —
    the sole object of a monotransitive, the second object of a
    double-object frame). Clausal complements are not argument slots here;
    they stay in the `frames`/`readings` API. -/
def arguments (v : Verb) : List Argument :=
  let frame := v.frames.head?.getD []
  let nominals := frame.countP (· == Complement.Position.nominal)
  let subj : Argument := ⟨true, v.effectiveSubjectEntailments⟩
  let objects : List Argument :=
    match nominals with
    | 0 => []
    | 1 => [⟨true, v.effectiveObjectEntailments⟩]
    | _ => [⟨true, none⟩, ⟨true, v.effectiveObjectEntailments⟩]
  let obliques : List Argument :=
    (frame.filter (· == Complement.Position.adpositional)).map
      (fun _ => ⟨false, none⟩)
  subj :: objects ++ obliques

/-- The core argument slots of the citation frame. -/
def coreArguments (v : Verb) : List Argument :=
  v.arguments.filter (·.core)

/-- The derived comparative classification of the core slots, positionally
    parallel to `coreArguments` ([comrie-1978]): the sole core argument of
    a one-place frame is S; a two-place frame has A and P; a double-object
    frame has A, R, and T. A function of the frame's arity — coding roles
    are read off argument structure, not assigned to it. -/
def codingRoles (v : Verb) : List ArgumentRole :=
  match v.coreArguments.length with
  | 0 => []
  | 1 => [.S]
  | 2 => [.A, .P]
  | _ => [.A, .R, .T]

end Verb
