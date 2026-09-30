module

public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Data.Fintype.Sum
public import Linglib.Syntax.ConstructionGrammar.Constructicon

/-!
# Goldberg (1995): Constructions

This file formalizes [goldberg-1995]'s account of argument structure. Clausal argument
realization is not projected from verb entries alone: independent form–meaning pairings, the
argument structure constructions, contribute meaning of their own, and a verb in a construction
fuses its meaning with the construction's. The constructions of the book's first chapter are the
ditransitive (*X CAUSES Y to RECEIVE Z*), the caused-motion (*X CAUSES Y to MOVE Z*), the
resultative (*X CAUSES Y to BECOME Z*), the intransitive motion (*X MOVES Y*) and the conative
(*X DIRECTS ACTION at Y*).

The constructions form a network of normal-mode inheritance links (§3.3, `network`). The
extensions of the polysemous ditransitive state no syntax of their own and inherit the central
sense's (`inherited_statedForm`), and the network checks each link against the forms its type
requires (`network_wellTyped`): a polysemy extension has the form of its central sense, and
intransitive motion is a proper subpart of caused motion. The resultative is a metaphorical
extension of caused motion.

## Implementation notes

The forms are sequences of single-word slots, where the book states argument frames over
grammatical functions of phrases.

## TODO

The meaning poles are `Unit`: the constructions' semantics, *X CAUSES Y to RECEIVE Z* and the
rest, and the fusion of a verb's participant roles with a construction's argument roles are not
modelled.

## References

* [goldberg-1995]
-/

@[expose] public section

namespace Goldberg1995

open ConstructionGrammar

/-! ### The argument structure constructions -/

/-- The ditransitive, [Subj V Obj Obj₂]: *X CAUSES Y to RECEIVE Z* (*Pat faxed Bill the
letter*). -/
def ditransitive : Construction Unit :=
  { form :=
      [ { filler := .open_ .NOUN }
      , { filler := .open_ .VERB, isHead := true }
      , { filler := .open_ .NOUN }
      , { filler := .open_ .NOUN } ]
  , meaning := () }

/-- The caused-motion construction, [Subj V Obj Obl]: *X CAUSES Y to MOVE Z*, *Z* a directional
(*Pat sneezed the napkin off the table*). A verb such as *sneeze*, lexicalizing neither motion nor
causation, acquires both from the construction. -/
def causedMotion : Construction Unit :=
  { form :=
      [ { filler := .open_ .NOUN }
      , { filler := .open_ .VERB, isHead := true }
      , { filler := .open_ .NOUN }
      , { filler := .open_ .ADP } ]
  , meaning := () }

/-- The resultative, [Subj V Obj Xcomp]: *X CAUSES Y to BECOME Z* (*She hammered the metal
flat*). -/
def resultative : Construction Unit :=
  { form :=
      [ { filler := .open_ .NOUN }
      , { filler := .open_ .VERB, isHead := true }
      , { filler := .open_ .NOUN }
      , { filler := .open_ .ADJ } ]
  , meaning := () }

/-- The intransitive motion construction, [Subj V Obl]: *X MOVES Y* (*The fly buzzed into the
room*). -/
def intransitiveMotion : Construction Unit :=
  { form :=
      [ { filler := .open_ .NOUN }
      , { filler := .open_ .VERB, isHead := true }
      , { filler := .open_ .ADP } ]
  , meaning := () }

/-- The conative, [Subj V Obl_at]: *X DIRECTS ACTION at Y* (*Sam kicked at Bill*). The at-phrase
marks the target without entailing contact. -/
def conative : Construction Unit :=
  { form :=
      [ { filler := .open_ .NOUN }
      , { filler := .open_ .VERB, isHead := true }
      , { filler := .open_ .ADP } ]
  , meaning := () }

/-! ### The network (§3.3) -/

/-- The modality of the CAUSE-RECEIVE relation that distinguishes the ditransitive's senses
(pp. 75–77). -/
inductive TransferModality where
  /-- Actual transfer, the central sense: X CAUSES Y TO RECEIVE Z. -/
  | actual
  /-- Conditions of satisfaction imply X CAUSES Y TO RECEIVE Z. -/
  | satisfaction
  /-- X ENABLES Y TO RECEIVE Z. -/
  | enablement
  /-- X CAUSES Y NOT TO RECEIVE Z. -/
  | negated
  /-- X INTENDS TO CAUSE Y TO RECEIVE Z. -/
  | intended
  /-- X ACTS TO CAUSE Y TO RECEIVE Z at some future point in time. -/
  | future
  deriving DecidableEq, Fintype, Repr

/-- The constructions of the book's network: the ditransitive in each of its senses and the other
argument structure constructions. -/
inductive Node where
  | ditransitive (m : TransferModality)
  | causedMotion
  | intransitiveMotion
  | resultative
  | conative
  deriving DecidableEq, Fintype

/-- The construction at each node; the senses of the ditransitive share its form. -/
def construction : Node → Construction Unit
  | .ditransitive _ => ditransitive
  | .causedMotion => causedMotion
  | .intransitiveMotion => intransitiveMotion
  | .resultative => resultative
  | .conative => conative

/-- The network of chapters 2 and 3, "the entire collection of constructions as forming a lattice,
with individual constructions related by specific types of asymmetric normal mode inheritance
links" (§3.7, p. 99). Each extension of the ditransitive inherits from the central sense by a
polysemy link (pp. 75–77), intransitive motion from caused motion by a subpart link (p. 78), and
the resultative from caused motion by a metaphorical link, change of state as change of location
(pp. 81–84). The conative is in the book's inventory (p. 4) but in no link. -/
def network : Constructicon Node Unit where
  cxn := construction
  mothers
    | .ditransitive .actual => []
    | .ditransitive _ => [(.ditransitive .actual, some .polysemy)]
    | .intransitiveMotion => [(.causedMotion, some .subpart)]
    | .resultative => [(.causedMotion, some .metaphorical)]
    | _ => []

/-- The depth of a node below the constructions it inherits from. -/
def Node.rank : Node → ℕ
  | .ditransitive .actual | .causedMotion | .conative => 0
  | _ => 1

instance : PartialOrder Node := network.partialOrder Node.rank (by decide)

instance : DecidableLE Node :=
  network.decidableLE [.ditransitive .actual, .causedMotion] (by decide)

/-- Every link respects its type: the extensions of the ditransitive have its form, and
intransitive motion is a proper subpart of caused motion. -/
theorem network_wellTyped : network.WellTyped := by decide

/-- The links determine the resultative's mother: caused motion. -/
theorem isMother_resultative_iff (n : Node) :
    network.IsMother .resultative n ↔ n = .causedMotion := by
  revert n; decide

/-- The form a construction states itself. The extensions of the ditransitive state none: "the
syntactic specifications of the central sense are inherited by the extensions; therefore we do
not need to state the syntactic realization for each extension" (p. 75). -/
def statedForm : Node → Option (TypedForm String)
  | .ditransitive .actual => some ditransitive.form
  | .ditransitive _ => none
  | n => some (construction n).form

/-- Each sense of the ditransitive inherits the central sense's form. -/
theorem inherited_statedForm (m : TransferModality) :
    DefaultInheritance.inherited statedForm (.ditransitive m) = {ditransitive.form} := by
  cases m <;> exact DefaultInheritance.inherited_eq_singleton_of_isLeast
    (m := .ditransitive .actual) (by decide) rfl

end Goldberg1995
