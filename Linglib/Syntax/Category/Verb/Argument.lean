import Linglib.Syntax.ArgumentRole
import Linglib.Syntax.Category.Verb.Basic
import Linglib.Semantics.ArgumentStructure.Linking

/-!
# Verb arguments

`Verb.Argument`: an argument slot of a verb entry — the comparative coding
role it occupies in the citation frame, paired with its proto-role
entailment profile. The carrier that voice, extraction, and agreement
machinery selects over: role-label enums elsewhere are derived
classifications of argument slots, not parallel inventories.
`Verb.arguments` reads the slots off the entry's citation frame.

## References

* [comrie-1978]
* [dowty-1991]
* [haspelmath-2021]
-/

open ArgumentStructure

namespace Verb

/-- An argument slot of a verb entry: the comparative coding role it
    occupies in a basic active clause (`none` = oblique, non-core
    realization), and its proto-role entailment profile. -/
structure Argument where
  /-- Coding slot in the citation frame; `none` for oblique realization. -/
  role : Option ArgumentRole
  /-- Proto-role entailment profile; `none` when the entry leaves it
      unspecified. -/
  entailments : Option EntailmentProfile := none
  deriving Repr, BEq

namespace Argument

/-- The slot is a core argument (realized as one of S/A/P/R/T). -/
def IsCore (a : Argument) : Prop := a.role ≠ none

instance (a : Argument) : Decidable a.IsCore :=
  inferInstanceAs (Decidable (_ ≠ _))

/-- Derived semantic-role label: the cluster label of the slot's
    entailment profile (`EntailmentProfile.toRole`). -/
def thetaLabel (a : Argument) : Option ThetaRole :=
  a.entailments.bind EntailmentProfile.toRole

end Argument

/-- The argument slots of the entry's citation frame: the subject — S when
    the frame has no nominal object, A otherwise — then the nominal objects
    (P for a monotransitive; R then T for a double-object frame, with the
    entry's object entailments on the theme), then one oblique slot per
    adpositional position. Clausal complements are not argument slots here;
    they stay in the `frames`/`readings` API. -/
def arguments (v : Verb) : List Argument :=
  let frame := v.frames.head?.getD []
  let nominals := frame.countP (· == Complement.Position.nominal)
  let subj : Argument :=
    ⟨some (if nominals == 0 then .S else .A), v.effectiveSubjectEntailments⟩
  let objects : List Argument :=
    match nominals with
    | 0 => []
    | 1 => [⟨some .P, v.effectiveObjectEntailments⟩]
    | _ => [⟨some .R, none⟩, ⟨some .T, v.effectiveObjectEntailments⟩]
  let obliques : List Argument :=
    (frame.filter (· == Complement.Position.adpositional)).map
      (fun _ => ⟨none, none⟩)
  subj :: objects ++ obliques

/-- The core argument slots of the citation frame. -/
def coreArguments (v : Verb) : List Argument :=
  v.arguments.filter (·.role.isSome)

end Verb
