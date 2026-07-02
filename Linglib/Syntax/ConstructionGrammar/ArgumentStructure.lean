import Linglib.Syntax.ConstructionGrammar.Basic
import Linglib.Syntax.ConstructionGrammar.Inheritance
import Linglib.Semantics.Lexical.DiathesisAlternation
import Linglib.Data.UD.Basic

/-!
# Argument Structure Constructions
[goldberg-1995]

CxG's argument structure constructions: explicit slot structure, full
compositionality, polysemy families, and verb–construction fusion.

Fully abstract constructions without pragmatic functions are fully
compositional (`isFullyCompositional`); constructions with idiosyncratic
form–meaning pairings (*let alone*, WXDY, PAL) are irreducible phrasal
patterns that only CxG can capture. The decomposition of fully abstract constructions into
[mueller-2013]'s three universal combination schemata lives in
`Studies/Mueller2013.lean` (`Mueller2013.decompose`).

-/

namespace ConstructionGrammar

open Semantics.Lexical

/-! ## Construction slots and argument frames -/

/-- An argument structure construction: a `Construction` whose typed form
serves as the argument frame, enabling formal analysis of how the
construction relates to the three universal combination schemata.

The `semanticContribution` field captures which meaning components
([levin-1993]) the construction adds independently of the verb
([goldberg-1995]). When a verb fuses with a construction, the
composed meaning = `verb.meaningComponents.fuse cxn.semanticContribution`.
This is how constructions can license alternation behavior that verbs
lack in isolation — e.g., the resultative adds CoS + causation, enabling
the causative alternation for manner verbs ([levin-2026]). -/
structure ArgStructureConstruction where
  /-- The underlying construction -/
  construction : Construction
  /-- At least one slot of the form should be the head -/
  hasHead : construction.form.any (·.isHead) = true
  /-- What meaning components this construction contributes independently
      of the verb. Defaults to `.none` (no augmentation). -/
  semanticContribution : MeaningComponents := .none
  deriving Repr

/-- The argument frame: the underlying construction's typed form. -/
def ArgStructureConstruction.slots (asc : ArgStructureConstruction) :
    TypedForm String :=
  asc.construction.form

/-! ## Concrete argument structure constructions -/

/-- Ditransitive construction: [Subj V Obj1 Obj2].
"X CAUSES Y to RECEIVE Z" (e.g., "She gave him a book"). -/
def ditransitive : ArgStructureConstruction :=
  { construction :=
      { name := "Ditransitive"
      , form :=
          [ { filler := .open_ .NOUN, role := some "agent" }
          , { filler := .open_ .VERB, role := some "predicate", isHead := true }
          , { filler := .open_ .NOUN, role := some "recipient" }
          , { filler := .open_ .NOUN, role := some "theme" } ]
      , meaning := "X CAUSES Y to RECEIVE Z" }
  , hasHead := by decide }

/-- Caused-motion construction: [Subj V Obj Obl].
"X CAUSES Y to MOVE Z", Z a directional ("Pat sneezed the napkin off the
table", p. 3). Contributes motion + causation: verbs that lexicalize
neither (like *sneeze*) acquire both from the construction
([goldberg-1995] p. 152–179). -/
def causedMotion : ArgStructureConstruction :=
  { construction :=
      { name := "Caused-motion"
      , form :=
          [ { filler := .open_ .NOUN, role := some "agent" }
          , { filler := .open_ .VERB, role := some "predicate", isHead := true }
          , { filler := .open_ .NOUN, role := some "theme" }
          , { filler := .open_ .ADP, role := some "goal" } ]
      , meaning := "X CAUSES Y to MOVE Z" }
  , hasHead := by decide
  , semanticContribution :=
      { changeOfState := false, contact := false, motion := true, causation := true } }

/-- Resultative construction: [Subj V Obj Pred].
"X CAUSES Y to BECOME Z" (e.g., "She hammered the metal flat").
Contributes CoS + causation: manner verbs that lexicalize neither
acquire both from the construction ([rappaport-hovav-levin-1998];
[levin-2026] §3). This is what enables the causative alternation
for verbs like *push* that lack it in isolation. -/
def resultative : ArgStructureConstruction :=
  { construction :=
      { name := "Resultative"
      , form :=
          [ { filler := .open_ .NOUN, role := some "agent" }
          , { filler := .open_ .VERB, role := some "predicate", isHead := true }
          , { filler := .open_ .NOUN, role := some "patient" }
          , { filler := .open_ .ADJ, role := some "result" } ]
      , meaning := "X CAUSES Y to BECOME Z" }
  , hasHead := by decide
  , semanticContribution :=
      { changeOfState := true, contact := false, motion := false, causation := true } }

/-- Intransitive motion construction: [Subj V Obl].
"X MOVES to Y" (e.g., "The ball rolled down the hill"). -/
def intransitiveMotion : ArgStructureConstruction :=
  { construction :=
      { name := "Intransitive-motion"
      , form :=
          [ { filler := .open_ .NOUN, role := some "theme" }
          , { filler := .open_ .VERB, role := some "predicate", isHead := true }
          , { filler := .open_ .ADP, role := some "path" } ]
      , meaning := "X MOVES to Y" }
  , hasHead := by decide }

/-- Conative construction: [Subj V Obl_at].
"X DIRECTS ACTION at Y" (e.g., "Sam kicked at Bill").
The verb designates the intended result of the directed action;
the at-PP marks the target without entailing contact
([goldberg-1995] p. 3–4, 63–64). -/
def conative : ArgStructureConstruction :=
  { construction :=
      { name := "Conative"
      , form :=
          [ { filler := .open_ .NOUN, role := some "agent" }
          , { filler := .open_ .VERB, role := some "predicate", isHead := true }
          , { filler := .open_ .ADP, role := some "target" } ]
      , meaning := "X DIRECTS ACTION at Y" }
  , hasHead := by decide }

/-! ## Full compositionality -/

/-- A construction is fully compositional if it has specificity `fullyAbstract`
and no construction-specific pragmatic function.

This is a proxy for [mueller-2013]'s structural criterion (whether the
construction can be analyzed as a sequence of headed binary combinations).
The proxy works because fully abstract constructions without pragmatic
functions have no idiosyncratic form–meaning pairings that would resist
decomposition into the three universal schemata. The Boolean approximates
what [kay-michaelis-2019] survey as a continuum of constructional meaning
contributions. -/
def isFullyCompositional (c : Construction) : Bool :=
  c.specificity == .fullyAbstract && c.pragmaticFunction.isNone

/-! ## Core theorems -/

/-- Fully abstract constructions without pragmatic functions are fully compositional. -/
theorem fullyAbstract_isFullyCompositional (c : Construction)
    (h₁ : c.specificity = .fullyAbstract)
    (h₂ : c.pragmaticFunction = none) :
    isFullyCompositional c = true := by
  unfold isFullyCompositional
  rw [h₁, h₂]
  rfl

/-! ## Polysemy families ([goldberg-1995] §3.3.2, I_P links)

A polysemy family groups constructions that share one syntactic frame
but differ in meaning. The shared form is enforced by construction —
all senses are generated from the same `slots`, making it impossible
for a polysemy extension to silently diverge in syntax. -/

/-- A polysemy family: one argument frame, multiple meanings.

All constructions in a family share the same `slots` definitionally —
there is no way to create an extension with different syntax. The
polysemy links (I_P) are derived, not manually assembled. -/
structure PolysemyFamily where
  /-- Name of the construction family -/
  name : String
  /-- The shared argument frame -/
  slots : TypedForm String
  /-- At least one slot is the head -/
  hasHead : slots.any (·.isHead) = true
  /-- Central sense meaning -/
  centralMeaning : String
  /-- Extended senses: (extension name, meaning, overridden properties) -/
  extensions : List (String × String × List String)

/-- The central sense as an `ArgStructureConstruction`. -/
def PolysemyFamily.centralConstruction (f : PolysemyFamily) :
    ArgStructureConstruction :=
  { construction :=
      { name := f.name
      , form := f.slots
      , meaning := f.centralMeaning }
  , hasHead := f.hasHead }

/-- Build an extension construction. Uses the family's `slots` — shared
by construction, not by assertion. -/
def PolysemyFamily.extensionConstruction (f : PolysemyFamily)
    (ext : String × String × List String) : ArgStructureConstruction :=
  { construction :=
      { name := f.name ++ "-" ++ ext.1
      , form := f.slots
      , meaning := ext.2.1 }
  , hasHead := f.hasHead }

/-- All extension constructions. -/
def PolysemyFamily.extensionConstructions (f : PolysemyFamily) :
    List ArgStructureConstruction :=
  f.extensions.map f.extensionConstruction

/-- All constructions (central + extensions). -/
def PolysemyFamily.allConstructions (f : PolysemyFamily) :
    List ArgStructureConstruction :=
  f.centralConstruction :: f.extensionConstructions

/-- Derive polysemy links from the family structure. -/
def PolysemyFamily.polysemyLinks (f : PolysemyFamily) : List InheritanceLink :=
  f.extensions.map fun ⟨extName, _, overrides⟩ =>
    { parent := f.name
    , child := f.name ++ "-" ++ extName
    , mode := .normal
    , linkType := some .polysemy
    , sharedProperties := ["shared argument frame"]
    , overriddenProperties := overrides }

/-- Central construction uses the family's slots (definitionally true). -/
theorem PolysemyFamily.central_slots (f : PolysemyFamily) :
    f.centralConstruction.slots = f.slots := rfl

/-- Every extension uses the family's slots (definitionally true).
This is the structural enforcement: shared syntax is impossible
to violate because it follows from the definition, not from a proof. -/
theorem PolysemyFamily.extension_slots (f : PolysemyFamily)
    (ext : String × String × List String) :
    (f.extensionConstruction ext).slots = f.slots := rfl

/-! ## Ditransitive polysemy network ([goldberg-1995] pp. 75–77)

The ditransitive is not a single construction but a family of six related
senses connected by polysemy links (I_P). Each sense inherits the
ditransitive's syntactic form [Subj V Obj Obj₂] but differs in the
semantic relation between the event participants. -/

/-- The ditransitive polysemy family: six senses sharing one argument
frame ([goldberg-1995] pp. 75–77; verb classes per Figure 2.2, p. 38).
The extension labels are the formalizer's — Goldberg numbers the senses
and calls the Intended extension "the benefactive construction" (Figure
3.2). Her warrant for the shared frame is exactly what `PolysemyFamily`
enforces definitionally: "The syntactic specifications of the central
sense are inherited by the extensions" (p. 75). -/
def ditransitiveFamily : PolysemyFamily :=
  { name := "Ditransitive"
  , slots := ditransitive.slots
  , hasHead := by decide
  , centralMeaning := "X CAUSES Y TO RECEIVE Z"
  , extensions :=
      [ ("Satisfaction",
         "Conditions of satisfaction imply X CAUSES Y TO RECEIVE Z",
         ["transfer is implied, not entailed"])
      , ("Enablement",
         "X ENABLES Y TO RECEIVE Z",
         ["enablement replaces direct causation"])
      , ("Negated",
         "X CAUSES Y NOT TO RECEIVE Z",
         ["transfer is negated"])
      , ("Intended",
         "X INTENDS TO CAUSE Y TO RECEIVE Z",
         ["transfer is intended, not actual"])
      , ("Future",
         "X ACTS TO CAUSE Y TO RECEIVE Z at some future point in time",
         ["transfer deferred to future"]) ] }

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
inheritance links" (pp. 99–100): the ditransitive polysemy family
(pp. 75–77), the caused-motion → intransitive-motion subpart link (p. 78),
and the caused-motion → resultative metaphorical link (§3.4.1, the
"Change of State as Change of Location" metaphor). The conative appears in
the book's construction inventory (p. 4) but participates in no
inheritance link — it is a node without edges, and linking it would be
invention. -/

/-- The ch. 2–3 constructional network. -/
def goldberg1995Network : Constructicon :=
  { constructions :=
      ditransitiveFamily.allConstructions.map (·.construction) ++
        [ causedMotion.construction, intransitiveMotion.construction
        , resultative.construction, conative.construction ]
  , links :=
      ditransitivePolysemy ++ [causedMotionSubpart, causedMotionToResultative] }

/-- Every link of the network resolves to a member construction. -/
theorem goldberg1995Network_wellFormed : goldberg1995Network.WellFormed := by
  decide

/-- The links, not hand-listed parents, determine the resultative's mother:
the caused-motion construction, via the metaphorical link. -/
theorem resultative_parent :
    goldberg1995Network.parentsOf "Resultative" = [causedMotion.construction] := by
  decide

/-- Every link a polysemy family derives is an I_P link — a fact about the
construction, not about one table. -/
theorem PolysemyFamily.polysemyLinks_typed (f : PolysemyFamily) :
    ∀ l ∈ f.polysemyLinks, l.linkType = some .polysemy := by
  intro l hl
  simp only [PolysemyFamily.polysemyLinks, List.mem_map] at hl
  obtain ⟨ext, _, rfl⟩ := hl
  rfl

/-! ## Verb–construction fusion

[goldberg-1995]'s central claim: argument structure constructions are
independent form–meaning pairings. When a verb appears in a construction,
its meaning **fuses** with the construction's meaning. The composed meaning
can have properties neither has alone.

At the level of [levin-1993] meaning components, fusion is componentwise
OR: if either the verb or the construction contributes a component, the
composed meaning has it. This simple mechanism derives construction-dependent
alternation behavior ([levin-2026]):

- *push* alone: `{−CoS, +contact, +motion, −causation}` → no causative alternation
- *push* + resultative: `{+CoS, +contact, +motion, +causation}` → causative alternation predicted

The construction adds what the verb lacks; `predictedAlternation` on the
fused result gives the correct prediction without any new alternation logic. -/

/-- The composed meaning of a verb in an argument structure construction.
    Verb root semantics fused with the construction's semantic contribution. -/
def composedMeaning (verbMC : MeaningComponents) (cxn : ArgStructureConstruction) :
    MeaningComponents :=
  verbMC.fuse cxn.semanticContribution

/-- Whether an alternation is predicted for a verb *in a construction*.
    Generalizes `MeaningComponents.predictedAlternation` to construction contexts. -/
def predictedAlternationInConstruction (verbMC : MeaningComponents)
    (cxn : ArgStructureConstruction) (alt : DiathesisAlternation) : Bool :=
  (composedMeaning verbMC cxn).predictedAlternation alt

/-! ### Core theorems: constructions that don't augment -/

/-- Ditransitive contributes nothing beyond the verb (`.none`). -/
theorem ditransitive_no_augmentation :
    ditransitive.semanticContribution = .none := rfl

/-- With no augmentation, the composed meaning equals the verb's own. -/
theorem no_augmentation_identity (mc : MeaningComponents) :
    composedMeaning mc ditransitive = mc := by
  simp [composedMeaning, ditransitive, MeaningComponents.fuse_none_right]

/-! ### Core theorems: constructions that augment -/

/-- The resultative adds CoS + causation. -/
theorem resultative_adds_cos_causation :
    resultative.semanticContribution.changeOfState = true ∧
    resultative.semanticContribution.causation = true := ⟨rfl, rfl⟩

/-- The caused-motion construction adds motion + causation. -/
theorem causedMotion_adds_motion_causation :
    causedMotion.semanticContribution.motion = true ∧
    causedMotion.semanticContribution.causation = true := ⟨rfl, rfl⟩

/-! ### Key derivation: construction-dependent alternation

The payoff: `predictedAlternation` on fused components derives that manner
verbs participate in the causative alternation inside the resultative, even
though they cannot outside it. No new alternation logic is needed — the
existing component-based prediction (`mc.changeOfState && mc.causation`)
fires on the fused result. -/

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

The key architectural insight: fusing a construction's components with a verb's
components can flip *multiple* alternation predictions simultaneously. The
resultative adds CoS + causation, which unlocks not just causativeInchoative but
also middle, instrumentSubject, and the resultative alternation itself — all
from the same mechanism, with no new alternation logic.

This is the formal payoff of Goldbergian fusion ([goldberg-1995]):
constructions don't just license one new alternation — they systematically
augment the verb's meaning component profile, and every alternation whose
required components are now satisfied becomes available. -/

/-- Hit-class verbs alone: no middle, no instrumentSubject, no resultative alternation. -/
theorem hit_blocked_alone :
    MeaningComponents.hit.predictedAlternation .middle = false
    ∧ MeaningComponents.hit.predictedAlternation .instrumentSubject = false
    ∧ MeaningComponents.hit.predictedAlternation .resultative = false := by
  exact ⟨rfl, rfl, rfl⟩

/-- Hit-class in resultative: ALL FOUR component-derived alternations flip.
    The resultative adds CoS + causation → fused = ⟨true, true, true, true, false, false⟩.
    This unlocks causativeInchoative, middle, instrumentSubject, AND resultative. -/
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
