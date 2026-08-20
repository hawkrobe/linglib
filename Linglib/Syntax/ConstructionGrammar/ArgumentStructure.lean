/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.ConstructionGrammar.Basic
import Linglib.Syntax.ConstructionGrammar.Inheritance
import Linglib.Semantics.ArgumentStructure.DiathesisAlternation
import Linglib.Data.UD.Basic

/-!
# Argument structure in Construction Grammar

[goldberg-1995]'s account of argument structure: clausal argument
realization is not projected from verb entries alone but contributed by
independent form–meaning pairings — argument structure constructions —
whose meaning pole records the components they add beyond the verb. A
verb appearing in a construction fuses its components with the
construction's, deriving alternation behavior the verb lacks in
isolation, and the constructions themselves form a network of polysemy
and inheritance links.

## Main definitions

* `ditransitive`, `causedMotion`, `resultative`, `intransitiveMotion`,
  `conative`: [goldberg-1995]'s constructions
* `isFullyCompositional`: analyzable by the universal combination
  schemata alone
* `PolysemyFamily`, `goldberg1995Network`: one argument frame with many
  senses, and the ch. 2–3 network
* `composedMeaning`, `predictedAlternationInConstruction`:
  verb–construction fusion
-/

namespace ConstructionGrammar

open ArgumentStructure

/-! ## Concrete argument structure constructions

An argument structure construction is a `Construction MeaningComponents`:
its typed form is the argument frame, and its meaning pole records which
meaning components ([levin-1993]) the construction adds independently of
the verb ([goldberg-1995]) — `.none` for constructions that do not
augment. -/

/-- Ditransitive construction: [Subj V Obj1 Obj2].
"X CAUSES Y to RECEIVE Z" (e.g., "She gave him a book"). -/
def ditransitive : Construction MeaningComponents :=
  { name := "Ditransitive"
  , form :=
      [ { filler := .open_ .NOUN }                 -- agent
      , { filler := .open_ .VERB, isHead := true }
      , { filler := .open_ .NOUN }                 -- recipient
      , { filler := .open_ .NOUN } ]               -- theme
  , meaning := .none }

/-- Caused-motion construction: [Subj V Obj Obl].
"X CAUSES Y to MOVE Z", Z a directional ("Pat sneezed the napkin off the
table", p. 3). Contributes motion + causation: verbs that lexicalize
neither (like *sneeze*) acquire both from the construction
([goldberg-1995] p. 152–179). -/
def causedMotion : Construction MeaningComponents :=
  { name := "Caused-motion"
  , form :=
      [ { filler := .open_ .NOUN }                 -- agent
      , { filler := .open_ .VERB, isHead := true }
      , { filler := .open_ .NOUN }                 -- theme
      , { filler := .open_ .ADP } ]                -- goal
  , meaning :=
      { changeOfState := false, contact := false, motion := true, causation := true } }

/-- Resultative construction: [Subj V Obj Pred].
"X CAUSES Y to BECOME Z" (e.g., "She hammered the metal flat").
Contributes CoS + causation: manner verbs that lexicalize neither
acquire both — [rappaport-hovav-levin-1998]'s Template Augmentation,
cast lexically there (their appendix maps it onto the constructional
approach); [levin-2026] §3. This is what enables the causative
alternation for verbs like *push* that lack it in isolation. -/
def resultative : Construction MeaningComponents :=
  { name := "Resultative"
  , form :=
      [ { filler := .open_ .NOUN }                 -- agent
      , { filler := .open_ .VERB, isHead := true }
      , { filler := .open_ .NOUN }                 -- patient
      , { filler := .open_ .ADJ } ]                -- result
  , meaning :=
      { changeOfState := true, contact := false, motion := false, causation := true } }

/-- Intransitive motion construction: [Subj V Obl].
"X MOVES to Y" (e.g., "The ball rolled down the hill"). -/
def intransitiveMotion : Construction MeaningComponents :=
  { name := "Intransitive-motion"
  , form :=
      [ { filler := .open_ .NOUN }                 -- theme
      , { filler := .open_ .VERB, isHead := true }
      , { filler := .open_ .ADP } ]                -- path
  , meaning := .none }

/-- Conative construction: [Subj V Obl_at].
"X DIRECTS ACTION at Y" (e.g., "Sam kicked at Bill").
The verb designates the intended result of the directed action;
the at-PP marks the target without entailing contact
([goldberg-1995] p. 3–4, 63–64). -/
def conative : Construction MeaningComponents :=
  { name := "Conative"
  , form :=
      [ { filler := .open_ .NOUN }                 -- agent
      , { filler := .open_ .VERB, isHead := true }
      , { filler := .open_ .ADP } ]                -- target
  , meaning := .none }

/-! ## Full compositionality -/

/-- Whether a construction is analyzable by universal combination
schemata alone: fully abstract form and no pragmatic point — a Boolean
proxy for [mueller-2013]'s structural criterion, approximating what
[kay-michaelis-2019] survey as a continuum. -/
def isFullyCompositional {Sem : Type*} (c : Construction Sem) : Bool :=
  c.specificity == .fullyAbstract && !c.pragmaticPoint

/-! ## Core theorems -/

/-- Fully abstract constructions without pragmatic point are fully compositional. -/
theorem fullyAbstract_isFullyCompositional {Sem : Type*} (c : Construction Sem)
    (h₁ : c.specificity = .fullyAbstract)
    (h₂ : c.pragmaticPoint = false) :
    isFullyCompositional c = true := by
  unfold isFullyCompositional
  rw [h₁, h₂]
  rfl

/-! ## Polysemy families ([goldberg-1995] §3.3.2, I_P links)

A polysemy family groups constructions that share one syntactic frame
but differ in meaning. The shared form is enforced by construction —
all senses are generated from the same `form`, making it impossible
for a polysemy extension to silently diverge in syntax. -/

/-- A polysemy family: one argument frame, multiple meanings.

All constructions in a family share the same `form` definitionally —
there is no way to create an extension with different syntax. The
polysemy links (I_P) are derived, not manually assembled. -/
structure PolysemyFamily (Sem : Type*) where
  /-- Name of the construction family -/
  name : String
  /-- The shared argument frame -/
  form : TypedForm String
  /-- Central sense meaning -/
  centralMeaning : Sem
  /-- Extended senses: (extension name, meaning, overridden properties) -/
  extensions : List (String × Sem × List String)

variable {Sem : Type*}

/-- The central sense as a construction. -/
def PolysemyFamily.centralConstruction (f : PolysemyFamily Sem) :
    Construction Sem :=
  { name := f.name, form := f.form, meaning := f.centralMeaning }

/-- An extension construction, sharing the family's `form`
definitionally rather than by assertion. -/
def PolysemyFamily.extensionConstruction (f : PolysemyFamily Sem)
    (ext : String × Sem × List String) : Construction Sem :=
  { name := f.name ++ "-" ++ ext.1, form := f.form, meaning := ext.2.1 }

/-- All extension constructions. -/
def PolysemyFamily.extensionConstructions (f : PolysemyFamily Sem) :
    List (Construction Sem) :=
  f.extensions.map f.extensionConstruction

/-- All constructions (central + extensions). -/
def PolysemyFamily.allConstructions (f : PolysemyFamily Sem) :
    List (Construction Sem) :=
  f.centralConstruction :: f.extensionConstructions

/-- The polysemy links a family determines, one per extension. -/
def PolysemyFamily.polysemyLinks (f : PolysemyFamily Sem) : List InheritanceLink :=
  f.extensions.map fun ⟨extName, _, overrides⟩ =>
    { parent := f.name
    , child := f.name ++ "-" ++ extName
    , mode := .normal
    , linkType := some .polysemy
    , sharedProperties := ["shared argument frame"]
    , overriddenProperties := overrides }

/-- Central construction uses the family's form (definitionally true). -/
theorem PolysemyFamily.central_form (f : PolysemyFamily Sem) :
    f.centralConstruction.form = f.form := rfl

/-- Every extension uses the family's form (definitionally true).
This is the structural enforcement: shared syntax is impossible
to violate because it follows from the definition, not from a proof. -/
theorem PolysemyFamily.extension_form (f : PolysemyFamily Sem)
    (ext : String × Sem × List String) :
    (f.extensionConstruction ext).form = f.form := rfl

/-! ## Ditransitive polysemy network ([goldberg-1995] pp. 75–77)

The ditransitive is not a single construction but a family of six related
senses connected by polysemy links (I_P). Each sense inherits the
ditransitive's syntactic form [Subj V Obj Obj₂] but differs in the
semantic relation between the event participants. -/

/-- The modality of the CAUSE-RECEIVE relation distinguishing the
ditransitive's senses ([goldberg-1995] pp. 75–77). -/
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

/-- The ditransitive polysemy family: six senses sharing one argument
frame ([goldberg-1995] pp. 75–77; verb classes per Figure 2.2, p. 38).
The extension labels are the formalizer's — Goldberg numbers the senses
and calls the Intended extension "the benefactive construction" (Figure
3.2). Her warrant for the shared frame is exactly what `PolysemyFamily`
enforces definitionally: "The syntactic specifications of the central
sense are inherited by the extensions" (p. 75). -/
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

/-- Derived polysemy links. -/
def ditransitivePolysemy : List InheritanceLink :=
  ditransitiveFamily.polysemyLinks

/-- Subpart link (I_S) from caused-motion to intransitive motion
([goldberg-1995] p. 78, link annotated "I_S: cause"): the intransitive
motion construction is a proper subpart of the caused-motion construction.
The cause role is *absent* in the subpart, not overridden — I_S relates a
proper subpart, so the override slot stays empty. -/
def causedMotionSubpart : InheritanceLink :=
  { parent := "Caused-motion"
  , child := "Intransitive-motion"
  , mode := .normal
  , linkType := some .subpart
  , sharedProperties := ["MOVE predicate", "theme role", "path/goal role"] }

/-- Metaphorical extension link (I_M) from caused-motion to resultative
([goldberg-1995] pp. 81–84): the resultative is a metaphorical
extension of caused-motion via the systematic metaphor
motion → change, location → state. -/
def causedMotionToResultative : InheritanceLink :=
  { parent := "Caused-motion"
  , child := "Resultative"
  , mode := .normal
  , linkType := some .metaphorical
  , sharedProperties := ["X CAUSES Y to undergo change", "causal structure"]
  , overriddenProperties := ["motion → change of state", "location → state"] }

/-! ## The book's network as a constructicon

[goldberg-1995] draws no single master figure; the network below assembles
the per-link analyses under the book's own framing of "the entire
collection of constructions as forming a lattice, with individual
constructions related by specific types of asymmetric normal mode
inheritance links" (§3.7, p. 99): the ditransitive polysemy family
(pp. 75–77), the caused-motion → intransitive-motion subpart link (p. 78),
and the caused-motion → resultative metaphorical link (§3.4.1, the
"Change of State as Change of Location" metaphor, p. 99). The conative
appears in
the book's construction inventory (p. 4) but participates in no
inheritance link — it is a node without edges, and linking it would be
invention. -/

/-- The ch. 2–3 constructional network, with meaning poles erased: the
network theorems concern the links and forms only, and the family's
`TransferModality` meanings and the argument-structure constructions'
`MeaningComponents` meanings live in different types. -/
def goldberg1995Network : Constructicon Unit :=
  { constructions :=
      ditransitiveFamily.allConstructions.map (.map fun _ => ()) ++
        ([causedMotion, intransitiveMotion, resultative, conative].map
          (.map fun _ => ()))
  , links :=
      ditransitivePolysemy ++ [causedMotionSubpart, causedMotionToResultative] }

/-- Every link of the network resolves to a member construction. -/
theorem goldberg1995Network_wellFormed : goldberg1995Network.WellFormed := by
  decide

/-- The links, not hand-listed parents, determine the resultative's mother:
the caused-motion construction, via the metaphorical link. -/
theorem resultative_parent :
    goldberg1995Network.parentsOf "Resultative"
      = [causedMotion.map fun _ => ()] := by
  decide

/-- Every link a polysemy family derives is an I_P link — a fact about the
construction, not about one table. -/
theorem PolysemyFamily.polysemyLinks_typed (f : PolysemyFamily Sem) :
    ∀ l ∈ f.polysemyLinks, l.linkType = some .polysemy := by
  intro l hl
  simp only [PolysemyFamily.polysemyLinks, List.mem_map] at hl
  obtain ⟨ext, _, rfl⟩ := hl
  rfl

/-! ## Verb–construction fusion

A verb appearing in a construction fuses its meaning components with the
construction's — componentwise, so the composed meaning can have
properties neither has alone ([goldberg-1995]; [levin-2026]): *push*
lacks change of state and causation, but *push* in the resultative
acquires both, and the causative alternation is predicted. -/

/-- The composed meaning of a verb in an argument structure construction:
the verb's meaning components fused with the construction's meaning
pole. -/
def composedMeaning (verbMC : MeaningComponents) (cxn : Construction MeaningComponents) :
    MeaningComponents :=
  verbMC.fuse cxn.meaning

/-- Whether an alternation is predicted for a verb *in a construction*.
    Generalizes `MeaningComponents.predictedAlternation` to construction contexts. -/
def predictedAlternationInConstruction (verbMC : MeaningComponents)
    (cxn : Construction MeaningComponents) (alt : DiathesisAlternation) : Bool :=
  (composedMeaning verbMC cxn).predictedAlternation alt

/-! ### Core theorems: constructions that don't augment -/

/-- Ditransitive contributes nothing beyond the verb (`.none`). -/
theorem ditransitive_no_augmentation :
    ditransitive.meaning = .none := rfl

/-- With no augmentation, the composed meaning equals the verb's own. -/
theorem no_augmentation_identity (mc : MeaningComponents) :
    composedMeaning mc ditransitive = mc := by
  simp [composedMeaning, ditransitive, MeaningComponents.fuse_none_right]

/-! ### Core theorems: constructions that augment -/

/-- The resultative adds CoS + causation. -/
theorem resultative_adds_cos_causation :
    resultative.meaning.changeOfState = true ∧
    resultative.meaning.causation = true := ⟨rfl, rfl⟩

/-- The caused-motion construction adds motion + causation. -/
theorem causedMotion_adds_motion_causation :
    causedMotion.meaning.motion = true ∧
    causedMotion.meaning.causation = true := ⟨rfl, rfl⟩

/-! ### Construction-dependent alternation

Manner verbs participate in the causative alternation inside the
resultative but not outside it: the component-based prediction fires on
the fused result, with no alternation logic specific to constructions. -/

/-- A pure manner verb (no CoS, no causation) cannot alternate alone. -/
theorem manner_verb_no_alternation (mc : MeaningComponents)
    (hCoS : mc.changeOfState = false) (_hCaus : mc.causation = false) :
    mc.predictedAlternation .causativeInchoative = false := by
  simp [MeaningComponents.predictedAlternation, hCoS]

/-- A pure manner verb in the resultative CAN alternate: the construction
    adds the CoS and causation the verb lacks. -/
theorem manner_verb_alternates_in_resultative (mc : MeaningComponents)
    (hInstr : mc.instrumentSpec = false) :
    predictedAlternationInConstruction mc resultative .causativeInchoative = true := by
  simp [predictedAlternationInConstruction, composedMeaning,
    MeaningComponents.fuse, resultative, MeaningComponents.predictedAlternation, hInstr]

/-- Concrete instance: hit-class components + resultative → causative alternation. -/
theorem hit_alternates_in_resultative :
    predictedAlternationInConstruction .hit resultative .causativeInchoative = true := rfl

/-- Concrete instance: hit-class components alone → no causative alternation. -/
theorem hit_no_alternation_alone :
    MeaningComponents.hit.predictedAlternation .causativeInchoative = false := rfl

/-! ### Multiple alternation flips from a single construction

Fusion can flip several alternation predictions at once: every
alternation whose required components the augmented profile satisfies
becomes available ([goldberg-1995]). -/

/-- Hit-class verbs alone permit neither the middle, the
instrument-subject, nor the resultative alternation. -/
theorem hit_blocked_alone :
    MeaningComponents.hit.predictedAlternation .middle = false
    ∧ MeaningComponents.hit.predictedAlternation .instrumentSubject = false
    ∧ MeaningComponents.hit.predictedAlternation .resultative = false := by
  exact ⟨rfl, rfl, rfl⟩

/-- Hit-class verbs in the resultative permit all four component-derived
alternations: the construction's change of state and causation complete
the profile. -/
theorem hit_resultative_full_profile :
    predictedAlternationInConstruction .hit resultative .causativeInchoative = true
    ∧ predictedAlternationInConstruction .hit resultative .middle = true
    ∧ predictedAlternationInConstruction .hit resultative .instrumentSubject = true
    ∧ predictedAlternationInConstruction .hit resultative .resultative = true := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Conative stays true: hit already has contact + motion, and fusing preserves them. -/
theorem hit_resultative_conative_preserved :
    MeaningComponents.hit.predictedAlternation .conative = true
    ∧ predictedAlternationInConstruction .hit resultative .conative = true := ⟨rfl, rfl⟩

/-! ### Caused-motion fusion

The caused-motion construction adds motion + causation. For touch-class verbs
(pure contact, no motion), this unlocks the conative alternation (requires
contact + motion) and the instrument subject alternation (requires causation).

Touch alone: `⟨false, true, false, false, false, false⟩` — only BPPA (contact)
Touch + caused-motion: `⟨false, true, true, true, false, false⟩` — conative + instrumentSubject too -/

/-- Touch verbs alone: no conative, no instrumentSubject. -/
theorem touch_blocked_alone :
    MeaningComponents.touch.predictedAlternation .conative = false
    ∧ MeaningComponents.touch.predictedAlternation .instrumentSubject = false := ⟨rfl, rfl⟩

/-- Touch + caused-motion: conative AND instrumentSubject flip to true.
    Motion + causation from the construction fill exactly what touch lacks. -/
theorem touch_causedMotion_flips :
    predictedAlternationInConstruction .touch causedMotion .conative = true
    ∧ predictedAlternationInConstruction .touch causedMotion .instrumentSubject = true := ⟨rfl, rfl⟩

/-- Touch + caused-motion: BPPA stays true (contact preserved by fusion). -/
theorem touch_causedMotion_bppa_preserved :
    MeaningComponents.touch.predictedAlternation .bodyPartPossessorAscension = true
    ∧ predictedAlternationInConstruction .touch causedMotion .bodyPartPossessorAscension = true := ⟨rfl, rfl⟩

/-! ### Manner-of-motion verbs in the resultative

Manner-of-motion verbs (`⟨false, false, true, false, false, true⟩`) have motion
but no CoS or causation. In the resultative, they acquire both — unlocking
causativeInchoative, middle, instrumentSubject, and resultative. -/

/-- Manner-of-motion verbs alone: no CI, no middle, no instrumentSubject. -/
theorem mannerOfMotion_blocked_alone :
    (LevinClass.mannerOfMotion.meaningComponents).predictedAlternation .causativeInchoative = false
    ∧ (LevinClass.mannerOfMotion.meaningComponents).predictedAlternation .middle = false
    ∧ (LevinClass.mannerOfMotion.meaningComponents).predictedAlternation .instrumentSubject = false := by
  exact ⟨rfl, rfl, rfl⟩

/-- Manner-of-motion + resultative: CI, middle, and instrumentSubject all flip. -/
theorem mannerOfMotion_resultative_flips :
    predictedAlternationInConstruction (LevinClass.mannerOfMotion.meaningComponents) resultative .causativeInchoative = true
    ∧ predictedAlternationInConstruction (LevinClass.mannerOfMotion.meaningComponents) resultative .middle = true
    ∧ predictedAlternationInConstruction (LevinClass.mannerOfMotion.meaningComponents) resultative .instrumentSubject = true := by
  exact ⟨rfl, rfl, rfl⟩

/-! ### Constructional augmentation summary

Each construction unlocks a characteristic set of alternations by augmenting
the verb's meaning components. The table below summarizes what each construction
contributes and which alternations it enables for verbs that lack the relevant
components:

| Construction | Adds | Unlocks |
|---|---|---|
| Resultative | CoS + causation | CI, middle, instrumentSubject, resultative |
| Caused-motion | motion + causation | conative (if +contact), instrumentSubject |
| Ditransitive | (nothing) | (nothing) |

These predictions are all derived from the *same* `predictedAlternation` function —
no construction-specific alternation logic exists. The construction simply changes
the input to the general prediction function. -/

/-- Ditransitive adds nothing: hit verbs stay blocked in all alternations
    that are blocked in isolation. -/
theorem hit_ditransitive_no_change :
    predictedAlternationInConstruction .hit ditransitive .causativeInchoative = false
    ∧ predictedAlternationInConstruction .hit ditransitive .middle = false
    ∧ predictedAlternationInConstruction .hit ditransitive .instrumentSubject = false := by
  simp [predictedAlternationInConstruction, composedMeaning, ditransitive,
    MeaningComponents.fuse_none_right, MeaningComponents.hit,
    MeaningComponents.predictedAlternation]

/-- Instrument specification survives fusion: cut-class verbs remain blocked
    from causativeInchoative and resultative even inside the resultative
    construction, because instrumentSpec = true persists through componentwise OR. -/
theorem cut_blocked_even_in_resultative :
    predictedAlternationInConstruction .cut resultative .causativeInchoative = false
    ∧ predictedAlternationInConstruction .cut resultative .resultative = false := by
  exact ⟨rfl, rfl⟩

end ConstructionGrammar
