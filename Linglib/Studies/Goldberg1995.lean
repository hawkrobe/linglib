module

public import Linglib.Syntax.ConstructionGrammar.Inheritance
public import Linglib.Semantics.ArgumentStructure.DiathesisAlternation

/-!
# Goldberg (1995): Constructions

This file formalizes [goldberg-1995]'s account of argument structure. Clausal argument
realization is not projected from verb entries alone: independent form–meaning pairings, the
argument structure constructions, contribute meaning of their own, and a verb in a construction
fuses its meaning with the construction's. The constructions of the book's first chapter are the
ditransitive (*X CAUSES Y to RECEIVE Z*), the caused-motion (*X CAUSES Y to MOVE Z*), the
resultative (*X CAUSES Y to BECOME Z*), the intransitive motion (*X MOVES Y*) and the conative
(*X DIRECTS ACTION at Y*). A manner verb such as *push* lacks change of state and causation, but in
the resultative it acquires both, so the causative alternation is predicted for it there and not
alone (`manner_verb_alternates_in_resultative`, `manner_verb_no_alternation`).

The constructions form a network of inheritance links (§3.3). The ditransitive is a polysemy
family whose senses share one argument frame, which `PolysemyFamily` enforces by construction
(`PolysemyFamily.extension_form`); intransitive motion is a subpart of caused motion, and the
resultative a metaphorical extension of it (`goldberg1995Network`).

## Implementation notes

A meaning pole records the meaning components of [levin-1993] that the construction adds beyond
the verb, fused with the verb's by componentwise disjunction (`MeaningComponents.fuse`), an
approximation of the book's fusion of roles. The ditransitive's reception and the conative's
directed action are not among those components, so the ditransitive records only its causation
and the conative nothing. The forms are sequences of single-word slots, where the book states
argument frames over grammatical functions of phrases.

## References

* [goldberg-1995]
* [levin-1993]
-/

@[expose] public section

namespace Goldberg1995

open ConstructionGrammar ArgumentStructure

/-! ### The argument structure constructions -/

/-- The ditransitive, [Subj V Obj Obj₂]: *X CAUSES Y to RECEIVE Z* (*Pat faxed Bill the
letter*). -/
def ditransitive : Construction MeaningComponents :=
  { name := "Ditransitive"
  , form :=
      [ { filler := .open_ .NOUN }
      , { filler := .open_ .VERB, isHead := true }
      , { filler := .open_ .NOUN }
      , { filler := .open_ .NOUN } ]
  , meaning := { changeOfState := false, contact := false, motion := false, causation := true } }

/-- The caused-motion construction, [Subj V Obj Obl]: *X CAUSES Y to MOVE Z*, *Z* a directional
(*Pat sneezed the napkin off the table*). A verb such as *sneeze*, lexicalizing neither motion nor
causation, acquires both from the construction. -/
def causedMotion : Construction MeaningComponents :=
  { name := "Caused-motion"
  , form :=
      [ { filler := .open_ .NOUN }
      , { filler := .open_ .VERB, isHead := true }
      , { filler := .open_ .NOUN }
      , { filler := .open_ .ADP } ]
  , meaning := { changeOfState := false, contact := false, motion := true, causation := true } }

/-- The resultative, [Subj V Obj Xcomp]: *X CAUSES Y to BECOME Z* (*She hammered the metal
flat*). A manner verb such as *push*, lexicalizing neither change of state nor causation,
acquires both from the construction. -/
def resultative : Construction MeaningComponents :=
  { name := "Resultative"
  , form :=
      [ { filler := .open_ .NOUN }
      , { filler := .open_ .VERB, isHead := true }
      , { filler := .open_ .NOUN }
      , { filler := .open_ .ADJ } ]
  , meaning := { changeOfState := true, contact := false, motion := false, causation := true } }

/-- The intransitive motion construction, [Subj V Obl]: *X MOVES Y* (*The fly buzzed into the
room*). -/
def intransitiveMotion : Construction MeaningComponents :=
  { name := "Intransitive-motion"
  , form :=
      [ { filler := .open_ .NOUN }
      , { filler := .open_ .VERB, isHead := true }
      , { filler := .open_ .ADP } ]
  , meaning := { changeOfState := false, contact := false, motion := true, causation := false } }

/-- The conative, [Subj V Obl_at]: *X DIRECTS ACTION at Y* (*Sam kicked at Bill*). The at-phrase
marks the target without entailing contact. -/
def conative : Construction MeaningComponents :=
  { name := "Conative"
  , form :=
      [ { filler := .open_ .NOUN }
      , { filler := .open_ .VERB, isHead := true }
      , { filler := .open_ .ADP } ]
  , meaning := .none }

/-! ### Fusion -/

/-- The meaning of a verb in a construction: the verb's meaning components fused with the
construction's meaning pole. -/
def composedMeaning (verbMC : MeaningComponents) (cxn : Construction MeaningComponents) :
    MeaningComponents :=
  verbMC.fuse cxn.meaning

/-- Whether an alternation is predicted for a verb in a construction. -/
def predictedAlternationInConstruction (verbMC : MeaningComponents)
    (cxn : Construction MeaningComponents) (alt : DiathesisAlternation) : Bool :=
  (composedMeaning verbMC cxn).predictedAlternation alt

/-- A construction that adds nothing leaves the verb's meaning as it is. -/
theorem composedMeaning_of_meaning_eq_none (mc : MeaningComponents)
    {cxn : Construction MeaningComponents} (h : cxn.meaning = .none) :
    composedMeaning mc cxn = mc := by
  rw [composedMeaning, h, MeaningComponents.fuse_none_right]

/-- A manner verb, with neither change of state nor causation, does not alternate alone. -/
theorem manner_verb_no_alternation (mc : MeaningComponents) (hCoS : mc.changeOfState = false) :
    mc.predictedAlternation .causativeInchoative = false := by
  simp [MeaningComponents.predictedAlternation, hCoS]

/-- In the resultative, any verb that specifies no instrument alternates: the construction adds
the change of state and causation the verb lacks. -/
theorem manner_verb_alternates_in_resultative (mc : MeaningComponents)
    (hInstr : mc.instrumentSpec = false) :
    predictedAlternationInConstruction mc resultative .causativeInchoative = true :=
  (fuse_cos_caus_enables mc resultative.meaning rfl rfl hInstr rfl).1

/-! ### The ditransitive as a polysemy family (§3.3.2, pp. 75–77) -/

/-- A polysemy family: one argument frame shared by a central sense and its extensions. -/
structure PolysemyFamily (Sem : Type*) where
  /-- The name of the family. -/
  name : String
  /-- The shared argument frame. -/
  form : TypedForm String
  /-- The central sense. -/
  centralMeaning : Sem
  /-- The extended senses, each with its name and the properties it overrides. -/
  extensions : List (String × Sem × List String)

variable {Sem : Type*}

/-- The central sense as a construction. -/
def PolysemyFamily.centralConstruction (f : PolysemyFamily Sem) : Construction Sem :=
  { name := f.name, form := f.form, meaning := f.centralMeaning }

/-- An extension as a construction, sharing the family's form by definition. -/
def PolysemyFamily.extensionConstruction (f : PolysemyFamily Sem)
    (ext : String × Sem × List String) : Construction Sem :=
  { name := f.name ++ "-" ++ ext.1, form := f.form, meaning := ext.2.1 }

/-- Every sense of the family, the central one first. -/
def PolysemyFamily.allConstructions (f : PolysemyFamily Sem) : List (Construction Sem) :=
  f.centralConstruction :: f.extensions.map f.extensionConstruction

/-- The polysemy links a family determines, one per extension. -/
def PolysemyFamily.polysemyLinks (f : PolysemyFamily Sem) : List InheritanceLink :=
  f.extensions.map fun ⟨extName, _, overrides⟩ ↦
    { parent := f.name
    , child := f.name ++ "-" ++ extName
    , mode := .normal
    , linkType := some .polysemy
    , sharedProperties := ["shared argument frame"]
    , overriddenProperties := overrides }

/-- Every extension has the family's form: "the syntactic specifications of the central sense
are inherited by the extensions" (p. 75). -/
theorem PolysemyFamily.extension_form (f : PolysemyFamily Sem)
    (ext : String × Sem × List String) : (f.extensionConstruction ext).form = f.form := rfl

/-- Every link a polysemy family derives is a polysemy link. -/
theorem PolysemyFamily.polysemyLinks_typed (f : PolysemyFamily Sem) :
    ∀ l ∈ f.polysemyLinks, l.linkType = some .polysemy := by
  intro l hl
  obtain ⟨_, _, rfl⟩ := List.mem_map.1 hl
  rfl

/-- The modality of the CAUSE-RECEIVE relation that distinguishes the ditransitive's senses
(pp. 75–77). -/
inductive TransferModality where
  /-- Actual transfer: X CAUSES Y TO RECEIVE Z. -/
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
  deriving DecidableEq, Repr

/-- The ditransitive's six senses sharing one argument frame (pp. 75–77; verb classes per
Figure 2.2, p. 38). The extension labels are the formalizer's; the book numbers the senses. -/
def ditransitiveFamily : PolysemyFamily TransferModality :=
  { name := "Ditransitive"
  , form := ditransitive.form
  , centralMeaning := .actual
  , extensions :=
      [ ("Satisfaction", .satisfaction, ["transfer is implied, not entailed"])
      , ("Enablement", .enablement, ["enablement replaces direct causation"])
      , ("Negated", .negated, ["transfer is negated"])
      , ("Intended", .intended, ["transfer is intended, not actual"])
      , ("Future", .future, ["transfer deferred to future"]) ] }

/-! ### The network (§3.3–3.7) -/

/-- The subpart link from caused motion to intransitive motion (p. 78, "I_S: cause"): the
intransitive motion construction is a proper subpart of the caused-motion construction, the
cause role absent. -/
def causedMotionSubpart : InheritanceLink :=
  { parent := "Caused-motion"
  , child := "Intransitive-motion"
  , mode := .normal
  , linkType := some .subpart
  , sharedProperties := ["MOVE predicate", "theme role", "path/goal role"] }

/-- The metaphorical link from caused motion to the resultative (pp. 81–84): the resultative
extends caused motion by the metaphor of change of state as change of location. -/
def causedMotionToResultative : InheritanceLink :=
  { parent := "Caused-motion"
  , child := "Resultative"
  , mode := .normal
  , linkType := some .metaphorical
  , sharedProperties := ["X CAUSES Y to undergo change", "causal structure"]
  , overriddenProperties := ["motion → change of state", "location → state"] }

/-- The constructional network of chapters 2 and 3, with the meaning poles erased: "the entire
collection of constructions as forming a lattice, with individual constructions related by
specific types of asymmetric normal mode inheritance links" (§3.7, p. 99). The conative is in
the book's inventory (p. 4) but in no inheritance link. -/
def goldberg1995Network : Constructicon Unit :=
  { constructions :=
      ditransitiveFamily.allConstructions.map (.map fun _ ↦ ()) ++
        [causedMotion, intransitiveMotion, resultative, conative].map (.map fun _ ↦ ())
  , links := ditransitiveFamily.polysemyLinks ++ [causedMotionSubpart, causedMotionToResultative] }

/-- Every link of the network resolves to a member construction. -/
theorem goldberg1995Network_wellFormed : goldberg1995Network.WellFormed := by
  decide

/-- The links determine the resultative's mother: caused motion, by the metaphorical link. -/
theorem resultative_parent :
    goldberg1995Network.parentsOf "Resultative" = [causedMotion.map fun _ ↦ ()] := by
  decide

end Goldberg1995
