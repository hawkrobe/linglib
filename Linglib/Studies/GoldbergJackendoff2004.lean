module

public import Linglib.Semantics.ArgumentStructure.ThetaRole
public import Linglib.Semantics.Events.SpatialTrace
public import Linglib.Syntax.Category.Verb.Argument
public import Linglib.Fragments.English.Verbs
public import Linglib.Data.Examples.GoldbergJackendoff2004

/-!
# Goldberg and Jackendoff (2004): The English Resultative as a Family of Constructions

This file formalizes [goldberg-jackendoff-2004]'s resultative family on the paper's own examples.
A resultative sentence has two subevents, a verbal subevent supplied by the verb and a
constructional subevent supplied by the construction: a host comes to have the property the
result phrase names or traverses the path it names, caused by the subject in the transitive
cases. The four subconstructions of the summary (97) are the combinations of these two choices
(`Subconstruction`), and in most of them the verbal subevent is the means of the constructional
one (`SubeventRelation`).

The constructional subevent's aspect controls the sentence's, the generalization (27). The event
measures out the result phrase's path, so an end-bounded result phrase makes a resultative telic
whatever the verb (`qua_resultative`), and one that is not end-bounded leaves an activity atelic
(`cum_resultative`). On a nonrepetitive reading the for-adverbial is accordingly acceptable
exactly when the result phrase is not end-bounded (`rows_for_adverbial`).

The constructional subevent's roles constrain the verb's under the principle of semantic
coherence (44): a verb role unifies with a constructional role only if it can be construed as
an instance of it (`Compatible`). The causer of a causative is an agent and a host a patient,
except that the host of an uncaused GO may be either (`Subconstruction.subjectRoles`). So the
intransitive path resultative admits more verbs than the intransitive property resultative
(`compatible_noncausative_path`), and *The worm wriggled onto the carpet* is acceptable while
**She yelled hoarse* and **The ball wiggled itself loose* are not (`rows_coherence`).

## Implementation notes

The verbal and constructional subevents are identified as one event, the paper's cotemporal
means (§4.2). End-boundedness is rendered by quantization and its absence by cumulativity, the
reading [krifka-1998] gives the event-path homomorphism the paper takes from [jackendoff-1996].
The paper labels result phrases only as AP or PP; a row's subconstruction follows the summary
(97), where a PP naming a state (*into pieces*, *to death*) is a property result phrase, and the
paper presents the examples (49) as transitive spatial resultatives. A row's `subjectRole` and
`objectRole` are the paper's construals of the verb's arguments, per verb and referent: whether
the argument is something that acts, an agent, or something to which something happens, a
patient.

## TODO

- The temporal relations the subevent relation allows (33): a means does not follow the
  subevent it effects, and a result does not precede its cause.
- Full argument realization (37), which excludes (41d) and (43b,c).
- The stative extension readings (25), and the *follow* subconstructions (52), (55) and (56),
  which are transitive but not causative.

## References

* [goldberg-jackendoff-2004]
* [goldberg-1995]
* [jackendoff-1996]
* [krifka-1998]
-/

@[expose] public section

namespace GoldbergJackendoff2004

open ArgumentStructure Data.Examples
open English hiding Verb

/-! ### The family -/

/-- Whether the result phrase names a property the host comes to have or a path it traverses. -/
inductive RPType where
  | property
  | path
  deriving DecidableEq, Repr

/-- A subconstruction of the summary (97): whether the subject causes the host's change, and
what the result phrase names. The causative ones are `X CAUSE [Y BECOME Z]` and
`X CAUSE [Y GO Path]`, the noncausative ones `X BECOME Y` and `X GO Path`. -/
structure Subconstruction where
  /-- Whether the subject causes the change of the host, which is then the object. -/
  causative : Bool
  /-- What the result phrase names. -/
  rp : RPType
  deriving DecidableEq, Repr

/-- How the verbal subevent relates to the constructional one (§3, §7.1). -/
inductive SubeventRelation where
  /-- The verbal subevent is the means of the constructional one, as in all four
  subconstructions: in *Willy watered the plants flat* the watering makes the plants flat. -/
  | means
  /-- The verbal subevent results from the constructional one, as with verbs of sound emission
  (*The trolley rumbled through the tunnel*, (17a)) and disappearance (*The witch vanished into
  the forest*, (21a)). -/
  | result
  /-- The verbal subevent is an instance of the constructional one, as with *follow* (*Bill
  followed the thief into the library*, (50a)) in the analysis (55). -/
  | instance_
  /-- The subevents merely co-occur, for the speakers who accept **The car honked down the
  road*, (18a). -/
  | coOccurrence
  deriving DecidableEq, Repr

/-- How the object of a transitive resultative is selected (§2). By §5 the fake reflexive is not
grammatically special: another object is excluded because it is implausible to make someone
else fall asleep by crying. -/
inductive ObjectSelection where
  /-- The verb selects the object: *The gardener watered the flowers flat*, (7a). -/
  | selected
  /-- Only the construction licenses the object: *They drank the pub dry*, (8a). -/
  | unselected
  /-- An unselected reflexive that alternates with no other object: *We yelled ourselves
  hoarse*, (9a). -/
  | fakeReflexive
  deriving DecidableEq, Repr

/-! ### Semantic coherence -/

/-- The principle of semantic coherence (44): a verb role, given by the roles it can be
construed as, unifies with a constructional role, given by the roles that are instances of it,
only if some construal of the verb role is an instance of the constructional role. -/
def Compatible (rV rC : Finset ThetaRole) : Prop := ∃ ρ ∈ rV, ρ ∈ rC

instance (rV rC : Finset ThetaRole) : Decidable (Compatible rV rC) :=
  inferInstanceAs (Decidable (∃ ρ ∈ rV, ρ ∈ rC))

theorem Compatible.mono {rV rV' rC rC' : Finset ThetaRole} (hV : rV ⊆ rV') (hC : rC ⊆ rC')
    (h : Compatible rV rC) : Compatible rV' rC' :=
  let ⟨ρ, hρV, hρC⟩ := h; ⟨ρ, hV hρV, hC hρC⟩

/-- The roles the host of the constructional subevent admits (§6.2). The host of BECOME and a
caused host are patients, while the host of an uncaused GO is agent or patient, as the subject
of an intransitive motion verb is. -/
def Subconstruction.hostRoles : Subconstruction → Finset ThetaRole
  | ⟨false, .path⟩ => {.agent, .patient}
  | _ => {.patient}

/-- The roles the construction admits for its subject: an agent, the causer, in a causative, and
otherwise the host. -/
def Subconstruction.subjectRoles (s : Subconstruction) : Finset ThetaRole :=
  if s.causative then {.agent} else s.hostRoles

/-- The intransitive path resultative is more liberal than the intransitive property resultative
in the verbs it admits (§6.2): a subject role compatible with BECOME is compatible with GO. -/
theorem compatible_noncausative_path {rV : Finset ThetaRole}
    (h : Compatible rV (Subconstruction.subjectRoles ⟨false, .property⟩)) :
    Compatible rV (Subconstruction.subjectRoles ⟨false, .path⟩) :=
  h.mono subset_rfl (by decide)

/-- An agent subject, as of *yell*, is compatible with GO but not with BECOME. -/
example : Compatible {.agent} (Subconstruction.subjectRoles ⟨false, .path⟩) ∧
    ¬ Compatible {.agent} (Subconstruction.subjectRoles ⟨false, .property⟩) := by
  decide

/-! ### Aspect -/

section Aspect

open Mereology Spatial

variable {Loc T : Type*} [LinearOrder T] [Event.Mereology T] [ClassicalMereology (Event T)]
  [SemilatticeSup (Path Loc)] [Trace Loc T] {V : Event T → Prop} {R : Path Loc → Prop}

/-- A resultative with cotemporal subevents: an event of the verb whose path, the path of the
constructional subevent, is one the result phrase describes. -/
def resultative (V : Event T → Prop) (R : Path Loc → Prop) (e : Event T) : Prop :=
  V e ∧ R (Trace.σ e)

/-- The generalization (27) for an end-bounded result phrase: the resultative is telic whatever
the verb. -/
theorem qua_resultative
    (hσ : ∀ e e' : Event T, (Trace.σ (e ⊔ e') : Path Loc) = Trace.σ e ⊔ Trace.σ e')
    (hinj : Function.Injective (Trace.σ : Event T → Path Loc)) (hR : QUA R) :
    QUA (resultative V R) :=
  IsAntichain.subset (Trace.bounded_path_telic hσ hinj hR) fun _ h ↦ h.2

/-- The generalization (27) for a result phrase that is not end-bounded: the resultative of an
activity is atelic. -/
theorem cum_resultative
    (hσ : ∀ e e' : Event T, (Trace.σ (e ⊔ e') : Path Loc) = Trace.σ e ⊔ Trace.σ e')
    (hV : CUM V) (hR : CUM R) : CUM (resultative V R) :=
  SupClosed.inter hV (Trace.unbounded_path_atelic hσ hR)

end Aspect

/-! ### The examples -/

/-- An example row: the verb, the subconstruction, how the subevents relate, the object
selection of a transitive, whether the result phrase is end-bounded where the paper tests
telicity, the paper's construals of the verb's subject and object where it discusses them, and
the judgment. -/
structure Row where
  verb : English.Verb
  subconstruction : Subconstruction
  relation : SubeventRelation
  selection : Option ObjectSelection
  endBounded : Option Bool
  subjectRole : Option (Finset ThetaRole)
  objectRole : Option (Finset ThetaRole)
  judgment : Judgment

/-- The paper's verbs, by citation form. -/
def verbs : List (String × English.Verb) :=
  [("hammer", hammer), ("laugh", laugh), ("freeze", freeze), ("roll", roll), ("water", water),
   ("break", break_), ("drink", drink), ("talk", talk), ("yell", yell), ("heat", heat),
   ("weave", weave), ("float", float), ("push", push), ("cry", cry), ("bleed", bleed),
   ("cough", cough), ("wriggle", wriggle), ("melt", melt), ("wiggle", wiggle), ("wipe", wipe),
   ("rumble", rumble)]

/-- The construals of a verb role the rows record. -/
def construals : List (String × Finset ThetaRole) :=
  [("agent", {.agent}), ("patient", {.patient}), ("agent or patient", {.agent, .patient})]

/-- The row an example encodes, when its features parse. -/
def Row.ofExample (ex : LinguisticExample) : Option Row := do
  let verb ← ex.parse? "verb" verbs
  let subconstruction ← ex.parse? "subconstruction"
    [("causative property", ⟨true, .property⟩), ("causative path", ⟨true, .path⟩),
     ("noncausative property", ⟨false, .property⟩), ("noncausative path", ⟨false, .path⟩)]
  pure { verb, subconstruction
         relation := (ex.parse? "subeventRelation" [("result", .result)]).getD .means
         selection := ex.parse? "selection"
           [("selected", .selected), ("unselected", .unselected),
            ("fake reflexive", .fakeReflexive)]
         endBounded := ex.parse? "endBounded" [("true", true), ("false", false)]
         subjectRole := ex.parse? "subjectRole" construals
         objectRole := ex.parse? "objectRole" construals
         judgment := ex.judgment }

/-- The paper's examples (5)–(9), (23)–(24), (45)–(49), (97c), and *wipe the table clean*. -/
def rows : List Row := Examples.all.filterMap Row.ofExample

example : rows.length = Examples.all.length := by decide

-- Object selection is a dimension of the transitive, that is causative, subconstructions.
example : ∀ r ∈ rows, r.selection.isSome → r.subconstruction.causative := by decide

/-- Section 4.1: on a nonrepetitive reading the for-adverbial is acceptable exactly when the
result phrase is not end-bounded, that is, when the resultative is atelic. -/
theorem rows_for_adverbial :
    ∀ r ∈ rows, ∀ b ∈ r.endBounded, r.judgment = .acceptable ↔ b = false := by
  decide

/-- The roles of a row cohere: the paper's construal of the verb's subject is compatible with
the construction's subject, and that of a selected object with the host. -/
def Row.Coheres (r : Row) : Prop :=
  (∀ ρ ∈ r.subjectRole, Compatible ρ r.subconstruction.subjectRoles) ∧
    ∀ ρ ∈ r.objectRole, Compatible ρ r.subconstruction.hostRoles

instance (r : Row) : Decidable r.Coheres := inferInstanceAs (Decidable (_ ∧ _))

/-- Section 6.2: outside the telicity tests, an example is acceptable exactly when its roles
cohere. -/
theorem rows_coherence :
    ∀ r ∈ rows, r.endBounded = none → (r.judgment = .acceptable ↔ r.Coheres) := by
  decide +kernel

/-- Where the fragment derives a role label for the object from the verb's citation frame, the
label is among the paper's construals: the object of *wipe* is a patient. The subject's label is
not comparable, since a noncausative may use the verb's anticausative frame, whose subject is the
citation frame's object: the melting chocolate of (48b), not the causer the fragment labels. -/
theorem rows_thetaLabel :
    ∀ r ∈ rows, ∀ ρs ∈ r.objectRole, ∀ s ∈ r.verb.coreSlots[1]?, ∀ ρ ∈ r.verb.thetaLabel s,
      ρ ∈ ρs := by
  decide +kernel

end GoldbergJackendoff2004
