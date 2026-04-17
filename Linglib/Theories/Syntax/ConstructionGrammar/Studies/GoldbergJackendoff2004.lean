import Linglib.Theories.Syntax.ConstructionGrammar.ArgumentStructure
import Linglib.Theories.Semantics.Tense.Aspect.LexicalAspect
import Linglib.Theories.Semantics.Verb.EventStructure
import Linglib.Theories.Interfaces.SyntaxSemantics.Linking
import Linglib.Core.Empirical

/-!
# @cite{goldberg-jackendoff-2004}: The English Resultative as a Family of Constructions
@cite{goldberg-jackendoff-2004}

Formalization of the core claims from @cite{goldberg-jackendoff-2004}.

## Key claims

1. The English resultative is not one construction but a **family of four subconstructions**
   organized along two dimensions: causative/noncausative × property/path RP
2. Every resultative has a **dual subevent structure**: a verbal subevent (from the verb)
   and a constructional subevent (CAUSE + BECOME/GO from the construction)
3. The verbal and constructional subevents are linked by typed semantic relations:
   MEANS, RESULT, INSTANCE, or CO-OCCURRENCE
4. **Full Argument Realization (FAR)**: all obligatory arguments of both verb and
   construction must be syntactically realized; shared arguments fuse
5. **Semantic Coherence**: verb role rV and construction role rC may fuse only if
   rV is construable as an instance of rC
6. **Aspectual constraint**: resultatives are telic iff the RP denotes a bounded path/property
7. **Temporal constraint**: the constructional subevent cannot temporally precede
   the verbal subevent

-/

namespace ConstructionGrammar.Studies.GoldbergJackendoff2004

open ConstructionGrammar
open Core.Verbs
open Semantics.Tense.Aspect.LexicalAspect

/-! ## Core types -/

/-- The kind of subevent in a resultative. -/
inductive SubeventKind where
  /-- From the verb's lexical meaning (e.g., hammering, kicking) -/
  | verbal
  /-- From the construction (CAUSE + BECOME/GO) -/
  | constructional
  deriving Repr, DecidableEq

/-- How the verbal and constructional subevents are related (§3).

- **means**: The verbal subevent is the means by which the constructional subevent
  is brought about. This is the default relation for all four core subconstructions
  (97a–d). E.g., "hammer metal flat" — hammering is the means of causing flatness.
  Also holds for noncausative cases: "the river froze solid" — freezing is the
  means of becoming solid; "the ball rolled into the field" — rolling is the
  means of motion along the path.
- **result**: The verbal subevent is a result of the constructional subevent
  (reversed directionality from means). Reserved for sound-emission resultatives
  (ex. 20: "The trolley rumbled through the tunnel" — rumbling results from
  motion) and disappearance resultatives (ex. 21: "The witch vanished into the
  forest" — vanishing results from motion).
- **instance_**: The verbal subevent is an instance of the constructional subevent.
  For the follow-type cases (§7.1, ex. 55: "Bill followed the thief into the
  library" — following IS going-after) and ride/drive-type cases (ex. 56: "Bill
  rode a train to New York" — riding IS going-by-way-of).
- **coOccurrence**: The two subevents merely co-occur without causal connection.
  The *way* construction ("She sang her way down the road") uses this relation.
  Some speakers accept CO-OCCURRENCE for sound-emission resultatives as well. -/
inductive SubeventRelation where
  | means
  | result
  | instance_
  | coOccurrence
  deriving Repr, DecidableEq

/-- Type of result phrase. -/
inductive RPType where
  /-- Adjectival/property result: "flat", "clean", "solid" -/
  | property
  /-- Directional/path result: "into the field", "off the table" -/
  | path
  deriving Repr, DecidableEq

/-- The four subconstructions in the resultative family (§2, Table 1).

|               | Property RP      | Path RP          |
|---------------|------------------|------------------|
| **Causative** | causativeProperty | causativePath   |
| **Noncausative** | noncausativeProperty | noncausativePath | -/
inductive ResultativeSubconstruction where
  | causativeProperty
  | causativePath
  | noncausativeProperty
  | noncausativePath
  deriving Repr, DecidableEq

/-- Whether a subconstruction is causative. -/
def ResultativeSubconstruction.isCausative : ResultativeSubconstruction → Bool
  | .causativeProperty => true
  | .causativePath => true
  | .noncausativeProperty => false
  | .noncausativePath => false

/-- Whether a subconstruction has a property (vs path) RP. -/
def ResultativeSubconstruction.isPropertyRP : ResultativeSubconstruction → Bool
  | .causativeProperty => true
  | .causativePath => false
  | .noncausativeProperty => true
  | .noncausativePath => false

/-- Get the RP type of a subconstruction. -/
def ResultativeSubconstruction.rpType : ResultativeSubconstruction → RPType
  | .causativeProperty => .property
  | .causativePath => .path
  | .noncausativeProperty => .property
  | .noncausativePath => .path

/-! ## Dual subevent structure (§3) -/

/-- Description of a subevent via event-structural features.

The two booleans encode the presence of CAUSE and BECOME/GO operators
in the subevent's event template (cf. `Template` in EventStructure.lean).
Verbal subevents are typically ⟨false, false⟩ (bare manner/activity);
constructional subevents are ⟨true, true⟩ (causative) or ⟨false, true⟩
(noncausative change-of-state/motion). -/
structure SubeventDesc where
  /-- Whether CAUSE is part of this subevent -/
  hasCause : Bool := false
  /-- Whether BECOME/GO is part of this subevent -/
  hasBecome : Bool := false
  deriving Repr, BEq, DecidableEq

/-- The dual subevent structure of a resultative (§3, Principle 25).

Every resultative has exactly two subevents linked by a semantic relation. -/
structure DualSubevent where
  /-- The verbal subevent (from the verb's lexical semantics) -/
  verbal : SubeventDesc
  /-- The constructional subevent (from the construction) -/
  constructional : SubeventDesc
  /-- How the subevents are related -/
  relation : SubeventRelation
  deriving Repr, BEq

/-! ## Derived constructional subevent

The constructional subevent's event-structural features are fully determined
by the subconstruction type: causative subconstructions have CAUSE + BECOME;
noncausative subconstructions have BECOME only. Verbal subevents are always
bare (no CAUSE, no BECOME) — the manner comes from the verb's lexical
semantics, not from event-structural operators. -/

/-- Derive the constructional subevent description from the subconstruction.
    This replaces per-entry stipulation: causative ↔ hasCause, all have hasBecome. -/
def ResultativeSubconstruction.constructionalDesc : ResultativeSubconstruction → SubeventDesc
  | .causativeProperty    => { hasCause := true,  hasBecome := true }
  | .causativePath        => { hasCause := true,  hasBecome := true }
  | .noncausativeProperty => { hasCause := false, hasBecome := true }
  | .noncausativePath     => { hasCause := false, hasBecome := true }

/-- The verbal subevent is always a bare manner/activity (no CAUSE, no BECOME). -/
def verbalSubeventDesc : SubeventDesc := {}

/-- Causative subconstructions have CAUSE in their constructional subevent. -/
theorem causative_constructional_has_cause (sc : ResultativeSubconstruction)
    (h : sc.isCausative = true) :
    sc.constructionalDesc.hasCause = true := by
  cases sc <;> simp [ResultativeSubconstruction.isCausative] at h <;>
    simp [ResultativeSubconstruction.constructionalDesc]

/-- Noncausative subconstructions lack CAUSE. -/
theorem noncausative_constructional_no_cause (sc : ResultativeSubconstruction)
    (h : sc.isCausative = false) :
    sc.constructionalDesc.hasCause = false := by
  cases sc <;> simp [ResultativeSubconstruction.isCausative] at h <;>
    simp [ResultativeSubconstruction.constructionalDesc]

/-- All subconstructions have BECOME in the constructional subevent. -/
theorem all_constructional_have_become_derived (sc : ResultativeSubconstruction) :
    sc.constructionalDesc.hasBecome = true := by
  cases sc <;> rfl

/-! ## Bridge to event structure templates

G&J's constructional subevent maps to Rappaport Hovav & Levin's event
structure templates: causative → accomplishment template, noncausative →
achievement template. The hasCause/hasBecome features of SubeventDesc
are exactly Template.hasCause/Template.hasResultState. -/

open Semantics.Verb.EventStructure (Template)

/-- Map subconstruction to the constructional subevent's event template. -/
def ResultativeSubconstruction.constructionalTemplate :
    ResultativeSubconstruction → Template
  | .causativeProperty    => .accomplishment
  | .causativePath        => .accomplishment
  | .noncausativeProperty => .achievement
  | .noncausativePath     => .achievement

/-- The derived hasCause agrees with Template.hasCause. -/
theorem constructional_cause_matches_template (sc : ResultativeSubconstruction) :
    sc.constructionalDesc.hasCause = sc.constructionalTemplate.hasCause := by
  cases sc <;> rfl

/-- The derived hasBecome agrees with Template.hasResultState. -/
theorem constructional_become_matches_template (sc : ResultativeSubconstruction) :
    sc.constructionalDesc.hasBecome = sc.constructionalTemplate.hasResultState := by
  cases sc <;> rfl

/-! ## Boundedness and aspect -/

/-- Whether an RP denotes a bounded endpoint.

Property RPs are typically bounded (reaching an endstate), but comparative/gradual
APs ("hotter and hotter", "ever flatter") create unbounded property RPs (§4.1).
Path RPs are bounded iff the goal is specific ("into the field" = bounded;
"along the road" = unbounded). -/
inductive Boundedness where
  | bounded
  | unbounded
  deriving Repr, DecidableEq

/-! ## Object selection (§2, ex. 7–9)

Within transitive resultatives, the object may be independently selected
by the verb (selected) or licensed only by the construction (unselected).
A special case of unselected: fake reflexives, where the object is a
reflexive pronoun that cannot alternate with other NPs. -/

/-- How the postverbal NP is selected (§2). -/
inductive ObjectSelection where
  /-- Verb independently selects the object: "She watered the plants flat" -/
  | selected
  /-- Construction licenses the object (verb doesn't take it independently):
      "They drank the pub dry" (cf. *They drank the pub) -/
  | unselected
  /-- Special unselected: reflexive object that cannot alternate with other NPs:
      "She laughed herself silly" (cf. *She laughed him silly) -/
  | fakeReflexive
  deriving Repr, DecidableEq, BEq

/-- Intransitive resultatives have no object selection. -/
def ResultativeSubconstruction.defaultObjectSelection :
    ResultativeSubconstruction → Option ObjectSelection
  | .causativeProperty    => some .selected
  | .causativePath        => some .selected
  | .noncausativeProperty => none
  | .noncausativePath     => none

/-! ## Resultative entry -/

/-- A resultative entry: verb + subconstruction + aspect.

The dual subevent structure is derived from the subconstruction:
- verbal desc: always `verbalSubeventDesc` (bare manner/activity)
- constructional desc: `subconstruction.constructionalDesc`
The subevent relation defaults to MEANS for all four core subconstructions;
RESULT is used only for sound-emission and disappearance subtypes.

The Levin class enables compositional fusion: `verbMC.fuse cxn.semanticContribution`
derives predictions about alternation participation. -/
structure ResultativeEntry where
  /-- The verb form -/
  verb : String
  /-- Which subconstruction -/
  subconstruction : ResultativeSubconstruction
  /-- How the subevents are related (default: MEANS for core subconstructions) -/
  subeventRelation : SubeventRelation := .means
  /-- Boundedness of the result phrase -/
  rpBoundedness : Boundedness
  /-- Vendler class of the bare verb (without resultative) -/
  bareVerbClass : VendlerClass
  /-- How the postverbal NP is selected (transitive only) -/
  objectSelection : Option ObjectSelection := none
  /-- Levin class of the verb, for MeaningComponents derivation -/
  levinClass : LevinClass
  deriving Repr, BEq

/-- Derive the full dual subevent structure from the entry. -/
def ResultativeEntry.dualSubevent (e : ResultativeEntry) : DualSubevent :=
  { verbal := verbalSubeventDesc
  , constructional := e.subconstruction.constructionalDesc
  , relation := e.subeventRelation }

/-- The verb's inherent meaning components, from its Levin class. -/
def ResultativeEntry.verbMC (e : ResultativeEntry) : MeaningComponents :=
  e.levinClass.meaningComponents

/-! ## Aspectual profile (§4, Principle 27)

The resultative's aspect is derived compositionally:
- Always dynamic (involves change)
- Always durative (extends over time)
- Telic iff the RP denotes a bounded path/property -/

/-- Derive the aspectual profile of a resultative from RP boundedness. -/
def resultativeAspect (b : Boundedness) : AspectualProfile :=
  { telicity := match b with
      | .bounded => .telic
      | .unbounded => .atelic
  , duration := .durative
  , dynamicity := .dynamic }

/-- Derive the Vendler class of a resultative. -/
def resultativeVendlerClass (b : Boundedness) : VendlerClass :=
  (resultativeAspect b).toVendlerClass

/-! ## Semantic roles and argument licensing

Uses the canonical `ThetaRole` from the linking interface rather than
a paper-specific enum. G&J's four resultative-relevant roles map to:
agent, patient, theme, goal (= "resultGoal" in G&J's terminology). -/

/-- An argument with its source (verb or construction). -/
structure ArgSource where
  /-- The semantic role -/
  role : ThetaRole
  /-- Whether this argument comes from the verb -/
  fromVerb : Bool
  /-- Whether this argument comes from the construction -/
  fromConstruction : Bool
  deriving Repr, BEq

/-- Whether an argument is fused (shared between verb and construction). -/
def ArgSource.isFused (a : ArgSource) : Bool :=
  a.fromVerb && a.fromConstruction

/-! ## Full Argument Realization (FAR) — Principle 37, §6.1

All obligatory arguments of both the verb and the construction must be
syntactically realized. Arguments shared between verb and construction fuse
into a single syntactic position. -/

/-- Check FAR: every role's source is accounted for. -/
def farSatisfied (args : List ArgSource) : Bool :=
  args.all (λ a => a.fromVerb || a.fromConstruction)

/-! ## Semantic Coherence Principle — Principle 44, §6.2

A verb role rV and a construction role rC may fuse only if rV is
construable as an instance of rC. -/

/-- Which role pairs are coherent for fusion (Principle 44).

Agent can fuse with agent; patient with patient or theme;
theme with patient or theme; goal with goal. All other combinations
(experiencer, instrument, stimulus, source) are incoherent in the
resultative construction. -/
def rolesCoherent (rV rC : ThetaRole) : Bool :=
  match rV, rC with
  | .agent, .agent => true
  | .patient, .patient => true
  | .patient, .theme => true
  | .theme, .patient => true
  | .theme, .theme => true
  | .goal, .goal => true
  | _, _ => false

/-- Check semantic coherence: all fused arguments have coherent roles. -/
def semanticCoherenceSatisfied (args : List (ThetaRole × ThetaRole)) : Bool :=
  args.all (λ ⟨rV, rC⟩ => rolesCoherent rV rC)

/-! ## Temporal constraint (§4.2)

Temporal ordering between subevents is constrained by the subevent relation:
- **MEANS**: The verbal subevent must temporally overlap with or precede the
  constructional subevent. Constructional-first is ruled out because you
  cannot achieve a result before performing the means to it.
- **RESULT**: The constructional subevent CAN precede the verbal subevent.
  E.g., "The door banged open" — the opening (constructional) precedes
  the banging (verbal result of the motion).
- **INSTANCE/CO-OCCURRENCE**: Simultaneity expected (the verbal IS the
  constructional, or they merely co-occur). -/

/-- Temporal ordering between subevents. -/
inductive TemporalOrder where
  | verbalFirst
  | simultaneous
  | constructionalFirst
  deriving Repr, DecidableEq

/-- Check the temporal constraint given the subevent relation.

For MEANS, the constructional subevent cannot precede the verbal subevent.
For RESULT, all orderings are acceptable (reversed directionality).
For INSTANCE/CO-OCCURRENCE, simultaneity is expected but not enforced. -/
def temporalConstraintSatisfied (rel : SubeventRelation) (order : TemporalOrder) : Bool :=
  match rel, order with
  | .means, .constructionalFirst => false
  | _, _ => true

/-! ## Empirical data: resultative entries -/

def hammerFlat : ResultativeEntry :=
  { verb := "hammer", subconstruction := .causativeProperty
  , rpBoundedness := .bounded, bareVerbClass := .activity
  , objectSelection := some .selected  -- cf. "She hammered the metal"
  , levinClass := .hit }               -- Levin §18.1

def kickIntoField : ResultativeEntry :=
  { verb := "kick", subconstruction := .causativePath
  , rpBoundedness := .bounded, bareVerbClass := .activity
  , objectSelection := some .selected  -- cf. "She kicked the ball"
  , levinClass := .hit }               -- Levin §18.1

def freezeSolid : ResultativeEntry :=
  { verb := "freeze", subconstruction := .noncausativeProperty
  , rpBoundedness := .bounded, bareVerbClass := .achievement
  , levinClass := .otherCoS }          -- Levin §45.4

def rollIntoField : ResultativeEntry :=
  { verb := "roll", subconstruction := .noncausativePath
  , rpBoundedness := .bounded, bareVerbClass := .activity
  , levinClass := .mannerOfMotion }    -- Levin §51.3

def drinkSick : ResultativeEntry :=
  { verb := "drink", subconstruction := .causativeProperty
  , rpBoundedness := .bounded, bareVerbClass := .activity
  , objectSelection := some .unselected  -- cf. *"They drank the pub"
  , levinClass := .eat }                 -- Levin §39.1

def laughSilly : ResultativeEntry :=
  { verb := "laugh", subconstruction := .causativeProperty
  , rpBoundedness := .bounded, bareVerbClass := .activity
  , objectSelection := some .fakeReflexive  -- cf. *"She laughed him silly"
  , levinClass := .performance }             -- Levin §26.7

def swingShut : ResultativeEntry :=
  { verb := "swing", subconstruction := .noncausativeProperty
  , rpBoundedness := .bounded, bareVerbClass := .activity
  , levinClass := .mannerOfMotion }    -- Levin §51.3

def wipeClean : ResultativeEntry :=
  { verb := "wipe", subconstruction := .causativeProperty
  , rpBoundedness := .bounded, bareVerbClass := .activity
  , objectSelection := some .selected  -- cf. "He wiped the table"
  , levinClass := .wipe }              -- Levin §10.4

/-- All resultative entries. -/
def allEntries : List ResultativeEntry :=
  [ hammerFlat, kickIntoField, freezeSolid, rollIntoField
  , drinkSick, laughSilly, swingShut, wipeClean ]

/-! ## Per-datum verification theorems -/

-- Subconstruction classification
theorem hammerFlat_is_causativeProperty :
    hammerFlat.subconstruction = .causativeProperty := rfl

theorem kickIntoField_is_causativePath :
    kickIntoField.subconstruction = .causativePath := rfl

theorem freezeSolid_is_noncausativeProperty :
    freezeSolid.subconstruction = .noncausativeProperty := rfl

theorem rollIntoField_is_noncausativePath :
    rollIntoField.subconstruction = .noncausativePath := rfl

-- Subevent relations: all core entries default to MEANS
theorem hammerFlat_means : hammerFlat.subeventRelation = .means := rfl
theorem freezeSolid_means : freezeSolid.subeventRelation = .means := rfl
theorem drinkSick_means : drinkSick.subeventRelation = .means := rfl

/-- All four core subconstructions use MEANS (§3, summary 97a–d).
    RESULT is reserved for sound-emission and disappearance subconstructions. -/
theorem all_core_entries_use_means :
    allEntries.all (·.subeventRelation == .means) = true := by
  native_decide

-- Derived subevent structure: CAUSE follows from subconstruction

/-- Causative entries have CAUSE in their derived constructional subevent. -/
theorem causative_entries_have_cause :
    (allEntries.filter (·.subconstruction.isCausative)).all
      (·.dualSubevent.constructional.hasCause) = true := by
  native_decide

/-- Noncausative entries lack CAUSE in their derived constructional subevent. -/
theorem noncausative_entries_no_cause :
    (allEntries.filter (λ e => !e.subconstruction.isCausative)).all
      (λ e => !e.dualSubevent.constructional.hasCause) = true := by
  native_decide

/-- All derived constructional subevents have BECOME. -/
theorem all_constructional_have_become :
    allEntries.all (·.dualSubevent.constructional.hasBecome) = true := by
  native_decide

-- Object selection: intransitive entries have no object selection

/-- Noncausative (intransitive) entries have no object selection. -/
theorem noncausative_no_object_selection :
    (allEntries.filter (λ e => !e.subconstruction.isCausative)).all
      (λ e => e.objectSelection == none) = true := by
  native_decide

/-- All causative entries specify an object selection mode. -/
theorem causative_have_object_selection :
    (allEntries.filter (·.subconstruction.isCausative)).all
      (λ e => e.objectSelection.isSome) = true := by
  native_decide

-- Aspectual predictions

/-- Bounded RP yields telic resultative (= accomplishment). -/
theorem bounded_rp_telic :
    resultativeVendlerClass .bounded = .accomplishment := rfl

/-- Unbounded RP yields atelic resultative (= activity). -/
theorem unbounded_rp_atelic :
    resultativeVendlerClass .unbounded = .activity := rfl

/-- All entries with bounded RP are telic. -/
theorem bounded_entries_telic :
    (allEntries.filter (·.rpBoundedness == .bounded)).all
      (λ e => (resultativeAspect e.rpBoundedness).telicity == .telic) = true := by
  native_decide

/-- Resultative telicizes an activity verb: adding bounded RP to an activity
    yields an accomplishment (§4, Principle 27). -/
theorem resultative_telicizes_activity :
    activityProfile.telicize.toVendlerClass = .accomplishment := rfl

/-- The resultative's derived aspect matches telicization of the bare verb
    when the bare verb is an activity and the RP is bounded. -/
theorem resultative_aspect_matches_telicize (e : ResultativeEntry)
    (hVerb : e.bareVerbClass = .activity) (hBounded : e.rpBoundedness = .bounded) :
    resultativeVendlerClass e.rpBoundedness =
    (e.bareVerbClass.toProfile.telicize).toVendlerClass := by
  rw [hVerb, hBounded]
  rfl

/-! ## Closed-scale → bounded RP bridge (§8, Principle 27)

@cite{goldberg-jackendoff-2004} §8: productive property RPs "tend to be
nongradable" and "encode a clearly delimited state." The formal correlate
(@cite{kennedy-2007}): productive RPs have a **maximum endpoint** on
their scale. `dry` (upper-bounded, has max) is productive; `wet`
(lower-bounded, no max) is not. `flat`, `clean`, `shut`, `dead`, `open`,
`full`, `empty` are all closed-scale (has max).

The aspectual chain: `hasMax → bounded RP → telic resultative`. -/

/-- Map Kennedy's scale boundedness to G&J's RP boundedness.
    Scales with a maximum endpoint yield bounded RPs (the RP denotes a
    delimited endstate). Scales without a maximum yield unbounded RPs. -/
def adjScaleToRPBoundedness (b : Core.Scale.Boundedness) : Boundedness :=
  if b.hasMax then .bounded else .unbounded

/-- Closed scales yield bounded RPs. -/
theorem closed_scale_bounded :
    adjScaleToRPBoundedness .closed = .bounded := rfl

/-- Upper-bounded scales yield bounded RPs (e.g., "dry"). -/
theorem upper_bounded_scale_bounded :
    adjScaleToRPBoundedness .upperBounded = .bounded := rfl

/-- Open scales yield unbounded RPs (e.g., "tall"). -/
theorem open_scale_unbounded :
    adjScaleToRPBoundedness .open_ = .unbounded := rfl

/-- Lower-bounded scales yield unbounded RPs (e.g., "wet"). -/
theorem lower_bounded_scale_unbounded :
    adjScaleToRPBoundedness .lowerBounded = .unbounded := rfl

/-- The full aspectual chain: a closed-scale adjective as RP yields a telic
    resultative. `hasMax → bounded → telic → accomplishment`. -/
theorem closed_scale_telic_resultative (b : Core.Scale.Boundedness) (hMax : b.hasMax = true) :
    resultativeVendlerClass (adjScaleToRPBoundedness b) = .accomplishment := by
  cases b <;> simp [Core.Scale.Boundedness.hasMax] at hMax <;>
    simp [adjScaleToRPBoundedness, Core.Scale.Boundedness.hasMax,
      resultativeVendlerClass, resultativeAspect, AspectualProfile.toVendlerClass]

/-- The dry/wet contrast: dry is productive (bounded → telic),
    wet is not (unbounded → atelic). Derives from scale structure alone. -/
theorem dry_wet_contrast :
    adjScaleToRPBoundedness .upperBounded = .bounded ∧
    adjScaleToRPBoundedness .lowerBounded = .unbounded :=
  ⟨rfl, rfl⟩

/-! ## Semantic contribution (meaning components)

Each subconstruction's semantic contribution is derived from the causativity
dimension: causative subconstructions contribute CoS + causation (matching
the parent `resultative` in ArgumentStructure.lean); noncausative ones
contribute only CoS (BECOME without CAUSE). This is consistent with the
`constructionalDesc`: `hasCause ↔ causation`, `hasBecome ↔ changeOfState`. -/

/-- Derive the meaning components contributed by a subconstruction.
    Causative: CoS + causation (same as parent `resultative`).
    Noncausative: CoS only (BECOME without CAUSE). -/
def ResultativeSubconstruction.semanticContribution :
    ResultativeSubconstruction → MeaningComponents
  | .causativeProperty    => ⟨true, false, false, true, false, false⟩
  | .causativePath        => ⟨true, false, false, true, false, false⟩
  | .noncausativeProperty => ⟨true, false, false, false, false, false⟩
  | .noncausativePath     => ⟨true, false, false, false, false, false⟩

/-- All subconstructions contribute change-of-state (all have BECOME). -/
theorem all_subconstructions_contribute_cos (sc : ResultativeSubconstruction) :
    sc.semanticContribution.changeOfState = true := by
  cases sc <;> rfl

/-- Causative subconstructions contribute causation. -/
theorem causative_contributes_causation (sc : ResultativeSubconstruction)
    (h : sc.isCausative = true) :
    sc.semanticContribution.causation = true := by
  cases sc <;> simp_all [ResultativeSubconstruction.isCausative,
    ResultativeSubconstruction.semanticContribution]

/-- Noncausative subconstructions do not contribute causation. -/
theorem noncausative_no_causation (sc : ResultativeSubconstruction)
    (h : sc.isCausative = false) :
    sc.semanticContribution.causation = false := by
  cases sc <;> simp_all [ResultativeSubconstruction.isCausative,
    ResultativeSubconstruction.semanticContribution]

/-- The semantic contribution is consistent with the constructional subevent:
    `hasCause ↔ causation` and `hasBecome ↔ changeOfState`. -/
theorem semanticContribution_matches_constructionalDesc (sc : ResultativeSubconstruction) :
    sc.semanticContribution.causation = sc.constructionalDesc.hasCause ∧
    sc.semanticContribution.changeOfState = sc.constructionalDesc.hasBecome := by
  cases sc <;> exact ⟨rfl, rfl⟩

/-- No subconstruction contributes instrument specificity. -/
theorem no_subconstruction_instrumentSpec (sc : ResultativeSubconstruction) :
    sc.semanticContribution.instrumentSpec = false := by
  cases sc <;> rfl

/-- Bundled: causative subconstruction contributes CoS + causation + ¬instrumentSpec.
    Satisfies the hypotheses of `fuse_cos_caus_enables`. -/
theorem causative_sc_contribution (sc : ResultativeSubconstruction)
    (h : sc.isCausative = true) :
    sc.semanticContribution.changeOfState = true ∧
    sc.semanticContribution.causation = true ∧
    sc.semanticContribution.instrumentSpec = false := by
  cases sc <;> simp_all [ResultativeSubconstruction.isCausative,
    ResultativeSubconstruction.semanticContribution]

/-- Bundled: noncausative subconstruction contributes CoS + ¬causation + ¬instrumentSpec.
    Satisfies the hypotheses of `fuse_cos_only_partial`. -/
theorem noncausative_sc_contribution (sc : ResultativeSubconstruction)
    (h : sc.isCausative = false) :
    sc.semanticContribution.changeOfState = true ∧
    sc.semanticContribution.causation = false ∧
    sc.semanticContribution.instrumentSpec = false := by
  cases sc <;> simp_all [ResultativeSubconstruction.isCausative,
    ResultativeSubconstruction.semanticContribution]

/-- Causative subconstructions match the parent `resultative`'s semantic contribution. -/
theorem causative_semantics_match_parent (sc : ResultativeSubconstruction)
    (h : sc.isCausative = true) :
    sc.semanticContribution = resultative.semanticContribution := by
  cases sc <;> simp_all [ResultativeSubconstruction.isCausative,
    ResultativeSubconstruction.semanticContribution, resultative]

/-! ## Derived construction network

The four subconstructions are derived from `ResultativeSubconstruction`
rather than hard-coded. Each subconstruction inherits from the existing
`resultative` parent in `ArgumentStructure.lean`.

The slot structure follows from two dimensions:
- **Causative** adds an agent subject + patient/theme object (4 slots)
- **Noncausative** has only a theme subject (3 slots)
- **Property** RP uses ADJ; **Path** RP uses ADP -/

/-- The UPOS category of the result phrase slot. -/
def RPType.toUPOS : RPType → UD.UPOS
  | .property => .ADJ
  | .path     => .ADP

/-- The role label for the result phrase slot. -/
def RPType.roleLabel : RPType → String
  | .property => "result"
  | .path     => "goal"

/-- The name suffix for a subconstruction. -/
def ResultativeSubconstruction.nameSuffix : ResultativeSubconstruction → String
  | .causativeProperty    => "CausativeProperty"
  | .causativePath        => "CausativePath"
  | .noncausativeProperty => "NoncausativeProperty"
  | .noncausativePath     => "NoncausativePath"

/-- Derive the ArgStructureConstruction from a subconstruction.

Slots are determined by the two dimensions:
- Causative: [NOUN subj, VERB head, NOUN obj, RP-UPOS rp]
- Noncausative: [NOUN subj, VERB head, RP-UPOS rp] -/
def ResultativeSubconstruction.toConstruction (sc : ResultativeSubconstruction) :
    ArgStructureConstruction :=
  let rpCat := sc.rpType.toUPOS
  let rpRole := sc.rpType.roleLabel
  let subjRole := if sc.isCausative then "agent" else "theme"
  { construction :=
      { name := s!"Resultative-{sc.nameSuffix}"
      , form := if sc.isCausative then
          s!"[Subj V Obj {if sc.rpType == .property then "AdjP" else "PP"}]"
        else
          s!"[Subj V {if sc.rpType == .property then "AdjP" else "PP"}]"
      , meaning := match sc with
          | .causativeProperty    => "X CAUSES Y to BECOME Z-state (via V-ing)"
          | .causativePath        => "X CAUSES Y to GO to Z-location (via V-ing)"
          | .noncausativeProperty => "X BECOMES Z-state (via V-ing)"
          | .noncausativePath     => "X GOES to Z-location (via V-ing)"
      , specificity := .fullyAbstract }
  , slots := if sc.isCausative then
      [ ⟨.NOUN, subjRole, false⟩, ⟨.VERB, "predicate", true⟩
      , ⟨.NOUN, (if sc.rpType == .property then "patient" else "theme"), false⟩
      , ⟨rpCat, rpRole, false⟩ ]
    else
      [ ⟨.NOUN, subjRole, false⟩, ⟨.VERB, "predicate", true⟩
      , ⟨rpCat, rpRole, false⟩ ]
  , hasHead := by cases sc <;> native_decide
  , semanticContribution := sc.semanticContribution }

/-- The composed meaning: verb MC fused with the subconstruction's contribution. -/
def ResultativeEntry.fusedMC (e : ResultativeEntry) : MeaningComponents :=
  composedMeaning e.verbMC e.subconstruction.toConstruction

/-- Convenience aliases for downstream compatibility. -/
def causativePropertyConstruction := ResultativeSubconstruction.causativeProperty.toConstruction
def causativePathConstruction := ResultativeSubconstruction.causativePath.toConstruction
def noncausativePropertyConstruction := ResultativeSubconstruction.noncausativeProperty.toConstruction
def noncausativePathConstruction := ResultativeSubconstruction.noncausativePath.toConstruction

/-- The full resultative family, derived from all four subconstructions. -/
def resultativeFamily : List ArgStructureConstruction :=
  [ResultativeSubconstruction.causativeProperty,
   .causativePath, .noncausativeProperty, .noncausativePath].map (·.toConstruction)

/-- Derive an inheritance link from a subconstruction to the parent. -/
def ResultativeSubconstruction.inheritanceLink (sc : ResultativeSubconstruction) :
    InheritanceLink :=
  let transStr := if sc.isCausative then "transitive" else "intransitive"
  let rpStr := if sc.rpType == .property then "AdjP" else "PP"
  { parent := "Resultative"
  , child := s!"Resultative-{sc.nameSuffix}"
  , mode := .normal
  , linkType := some .instance
  , sharedProperties := ["dual-subevent", "FAR", "semantic-coherence"]
  , overriddenProperties :=
      [s!"transitivity: {transStr}", s!"RP: {rpStr}"] ++
      (if sc.isCausative then [] else ["no CAUSE"]) }

/-- All four inheritance links, derived. -/
def resultativeInheritance : List InheritanceLink :=
  [ResultativeSubconstruction.causativeProperty,
   .causativePath, .noncausativeProperty, .noncausativePath].map (·.inheritanceLink)

/-- All inheritance links point to the same parent. -/
theorem all_inherit_from_resultative :
    resultativeInheritance.all (·.parent == "Resultative") = true := by
  native_decide

/-- All four subconstructions are fully abstract (decomposable). -/
theorem all_subconstructions_abstract :
    resultativeFamily.all (λ c => c.construction.specificity == .fullyAbstract) = true := by
  native_decide

/-- Causative subconstructions are transitive (4 slots);
    noncausative are intransitive (3 slots). -/
theorem causative_are_transitive :
    causativePropertyConstruction.slots.length = 4 ∧
    causativePathConstruction.slots.length = 4 := by
  constructor <;> native_decide

theorem noncausative_are_intransitive :
    noncausativePropertyConstruction.slots.length = 3 ∧
    noncausativePathConstruction.slots.length = 3 := by
  constructor <;> native_decide

/-- Causative subconstructions decompose like the parent resultative. -/
theorem causative_match_parent :
    decompose causativePropertyConstruction = decompose resultative ∧
    decompose causativePathConstruction = decompose resultative := by
  constructor <;> native_decide

/-- Noncausative subconstructions have one fewer decomposition step. -/
theorem noncausative_fewer_steps :
    (decompose noncausativePropertyConstruction).length <
    (decompose causativePropertyConstruction).length := by
  native_decide

/-! ## Verb–construction fusion (integration with ArgumentStructure.lean)

The `toConstruction` now carries `semanticContribution`, so the
`composedMeaning` / `predictedAlternationInConstruction` machinery from
ArgumentStructure.lean works directly with derived subconstructions. -/

/-- A manner verb (no CoS, no causation, no instrumentSpec) in a causative
    subconstruction acquires causative alternation: the subconstruction's
    semantic contribution adds CoS + causation via `fuse`. -/
theorem manner_verb_alternates_in_causative_sub (mc : MeaningComponents)
    (hInstr : mc.instrumentSpec = false)
    (sc : ResultativeSubconstruction) (hCaus : sc.isCausative = true) :
    predictedAlternationInConstruction mc sc.toConstruction
      .causativeInchoative = true := by
  cases sc <;> simp_all [ResultativeSubconstruction.isCausative,
    predictedAlternationInConstruction, composedMeaning,
    ResultativeSubconstruction.toConstruction,
    ResultativeSubconstruction.semanticContribution,
    MeaningComponents.fuse, MeaningComponents.predictedAlternation]

/-- A manner verb in a noncausative subconstruction does NOT acquire the
    causative alternation: noncausative subconstructions lack causation. -/
theorem manner_verb_no_alternation_in_noncausative (mc : MeaningComponents)
    (hCoS : mc.changeOfState = false) (hCaus : mc.causation = false)
    (sc : ResultativeSubconstruction) (hNonCaus : sc.isCausative = false) :
    predictedAlternationInConstruction mc sc.toConstruction
      .causativeInchoative = false := by
  cases sc <;> simp_all [ResultativeSubconstruction.isCausative,
    predictedAlternationInConstruction, composedMeaning,
    ResultativeSubconstruction.toConstruction,
    ResultativeSubconstruction.semanticContribution,
    MeaningComponents.fuse, MeaningComponents.predictedAlternation]

/-- Concrete: hit-class verb in causativeProperty → causative alternation. -/
theorem hit_alternates_in_causativeProperty :
    predictedAlternationInConstruction .hit
      causativePropertyConstruction .causativeInchoative = true := by
  native_decide

/-- Concrete: hit-class verb in noncausativeProperty → no alternation. -/
theorem hit_no_alternation_in_noncausativeProperty :
    predictedAlternationInConstruction .hit
      noncausativePropertyConstruction .causativeInchoative = false := by
  native_decide

/-- The composed meaning in a causative subconstruction matches the
    composed meaning in the parent `resultative` construction. -/
theorem causative_sub_fuse_matches_parent (mc : MeaningComponents)
    (sc : ResultativeSubconstruction) (h : sc.isCausative = true) :
    composedMeaning mc sc.toConstruction = composedMeaning mc resultative := by
  cases sc <;> simp_all [ResultativeSubconstruction.isCausative,
    composedMeaning, ResultativeSubconstruction.toConstruction,
    ResultativeSubconstruction.semanticContribution, resultative]

/-- All subconstructions contribute CoS via `toConstruction`, so the composed
    meaning always has `changeOfState = true` regardless of the verb. -/
theorem fused_always_has_cos (mc : MeaningComponents)
    (sc : ResultativeSubconstruction) :
    (composedMeaning mc sc.toConstruction).changeOfState = true := by
  cases sc <;> simp [composedMeaning, ResultativeSubconstruction.toConstruction,
    ResultativeSubconstruction.semanticContribution, MeaningComponents.fuse]

/-- The resultative alternation itself is predicted for any non-instrument verb
    in any subconstruction (since all contribute CoS). -/
theorem resultative_alternation_predicted (mc : MeaningComponents)
    (hInstr : mc.instrumentSpec = false)
    (sc : ResultativeSubconstruction) :
    predictedAlternationInConstruction mc sc.toConstruction .resultative = true := by
  cases sc <;> simp_all [predictedAlternationInConstruction, composedMeaning,
    ResultativeSubconstruction.toConstruction,
    ResultativeSubconstruction.semanticContribution,
    MeaningComponents.fuse, MeaningComponents.predictedAlternation]

/-! ## Per-entry verb class participation

Each `ResultativeEntry` carries its Levin class. The fused meaning
(`verbMC.fuse cxn.semanticContribution`) determines which alternations
are predicted for the verb *in the construction*.

The key G&J insight: manner verbs (hit, performance, manner-of-motion)
that lack CoS or causation in isolation acquire them from the
construction. The `fusedMC` captures this compositionally. -/

/-- All entries acquire CoS from the construction, regardless of verb class. -/
theorem all_entries_fused_cos :
    allEntries.all (λ e => e.fusedMC.changeOfState) = true := by
  native_decide

/-- All entries participate in the resultative alternation (none are instrument-spec). -/
theorem all_entries_resultative_alternation :
    allEntries.all (λ e =>
      predictedAlternationInConstruction e.verbMC
        e.subconstruction.toConstruction .resultative) = true := by
  native_decide

/-- Causative entries all acquire the causative alternation. -/
theorem causative_entries_causative_alternation :
    (allEntries.filter (·.subconstruction.isCausative)).all (λ e =>
      predictedAlternationInConstruction e.verbMC
        e.subconstruction.toConstruction .causativeInchoative) = true := by
  native_decide

/-- Noncausative entries do NOT acquire the causative alternation
    (unless the verb already has causation — freeze/otherCoS does). -/
theorem noncausative_entries_no_new_causation :
    (allEntries.filter (λ e => !e.subconstruction.isCausative)).all (λ e =>
      predictedAlternationInConstruction e.verbMC
        e.subconstruction.toConstruction .causativeInchoative
      = e.verbMC.predictedAlternation .causativeInchoative) = true := by
  native_decide

/-! ### Verb-specific participation

The construction-verb interaction across the four canonical Levin classes
that G&J discuss: manner verbs (hit = hammer/kick), change-of-state
verbs (otherCoS = freeze), motion verbs (mannerOfMotion = roll/swing),
and removing verbs (wipe). -/

/-- Hammer (hit-class): no CoS or causation alone → both added by causative construction. -/
theorem hammer_gains_cos_causation :
    hammerFlat.verbMC.changeOfState = false ∧
    hammerFlat.verbMC.causation = false ∧
    hammerFlat.fusedMC.changeOfState = true ∧
    hammerFlat.fusedMC.causation = true := by
  constructor; native_decide
  constructor; native_decide
  constructor <;> native_decide

/-- Freeze (otherCoS): already has CoS + causation → construction doesn't change profile. -/
theorem freeze_already_has_cos :
    freezeSolid.verbMC.changeOfState = true ∧
    freezeSolid.verbMC.causation = true ∧
    freezeSolid.fusedMC = freezeSolid.verbMC := by
  constructor; native_decide
  constructor <;> native_decide

/-- Roll (manner-of-motion): gains CoS from construction; no causation (noncausative). -/
theorem roll_gains_cos_only :
    rollIntoField.verbMC.changeOfState = false ∧
    rollIntoField.fusedMC.changeOfState = true ∧
    rollIntoField.fusedMC.causation = false := by
  constructor; native_decide
  constructor <;> native_decide

/-- Laugh (performance): pure manner verb — construction adds CoS + causation. -/
theorem laugh_gains_cos_causation :
    laughSilly.verbMC.changeOfState = false ∧
    laughSilly.verbMC.causation = false ∧
    laughSilly.fusedMC.changeOfState = true ∧
    laughSilly.fusedMC.causation = true := by
  constructor; native_decide
  constructor; native_decide
  constructor <;> native_decide

/-- Wipe (wipe-class): already has full profile — construction is redundant. -/
theorem wipe_already_has_everything :
    wipeClean.verbMC.changeOfState = true ∧
    wipeClean.verbMC.causation = true ∧
    wipeClean.fusedMC = wipeClean.verbMC := by
  constructor; native_decide
  constructor <;> native_decide

/-! ## General chain theorems

The full derivation pipeline connecting adjective scale structure,
RP boundedness, aspect, and alternation participation. These are
universally quantified — they hold for ANY verb class and ANY
subconstruction satisfying the hypotheses, not just the attested entries.

The two chains are logically independent (aspect and alternation don't
interact at the MeaningComponents level), but they share a common input:
the subconstruction type determines both the constructional semantics
(CoS, causation) and the default subevent relation (MEANS). -/

/-- **Aspect chain**: any adjective with a scale maximum, used as an RP
    in a resultative, produces a telic accomplishment.

    The derivation composes two independently-defined functions:
    `adjScaleToRPBoundedness` (Kennedy 2007 → G&J) and
    `resultativeVendlerClass` (G&J → Vendler). Neither function knows
    about the other; the chain theorem proves they compose correctly. -/
theorem aspect_chain (b : Core.Scale.Boundedness) (hMax : b.hasMax = true) :
    let rpB := adjScaleToRPBoundedness b
    rpB = .bounded ∧
    resultativeVendlerClass rpB = .accomplishment ∧
    (resultativeVendlerClass rpB).telicity = .telic := by
  constructor
  · simp [adjScaleToRPBoundedness, hMax]
  constructor
  · exact closed_scale_telic_resultative b hMax
  · rw [closed_scale_telic_resultative b hMax]; rfl

/-- **Alternation chain**: corollary of `fuse_cos_caus_enables` for
    causative resultative subconstructions. The subconstruction contributes
    CoS + causation + ¬instrumentSpec, satisfying the general enabling
    theorem's hypotheses. -/
theorem alternation_chain (mc : MeaningComponents) (sc : ResultativeSubconstruction)
    (hInstr : mc.instrumentSpec = false) (hCausative : sc.isCausative = true) :
    let fused := composedMeaning mc sc.toConstruction
    fused.predictedAlternation .causativeInchoative = true ∧
    fused.predictedAlternation .middle = true ∧
    fused.predictedAlternation .instrumentSubject = true ∧
    fused.predictedAlternation .resultative = true := by
  have ⟨hCoS, hCaus, hNoInst⟩ := causative_sc_contribution sc hCausative
  simp only [composedMeaning, ResultativeSubconstruction.toConstruction]
  exact fuse_cos_caus_enables mc _ hCoS hCaus hInstr hNoInst

/-- **Noncausative contrast**: corollary of `fuse_cos_only_partial`.
    Noncausative subconstructions contribute CoS but not causation,
    so only CoS-dependent alternations fire. -/
theorem noncausative_partial_chain (mc : MeaningComponents)
    (sc : ResultativeSubconstruction)
    (hInstr : mc.instrumentSpec = false) (hNonCaus : sc.isCausative = false)
    (hNoCaus : mc.causation = false) :
    let fused := composedMeaning mc sc.toConstruction
    fused.predictedAlternation .middle = true ∧
    fused.predictedAlternation .resultative = true ∧
    fused.predictedAlternation .causativeInchoative = false ∧
    fused.predictedAlternation .instrumentSubject = false := by
  have ⟨hCoS, hNoCausC, hNoInst⟩ := noncausative_sc_contribution sc hNonCaus
  simp only [composedMeaning, ResultativeSubconstruction.toConstruction]
  exact fuse_cos_only_partial mc _ hCoS hNoCausC hNoCaus hInstr hNoInst

/-- **instrumentSpec blocking**: corollary of `instrumentSpec_blocks_after_fuse`.
    Cut-class verbs remain blocked in all subconstructions. -/
theorem instrumentSpec_blocks_across_subconstructions (mc : MeaningComponents)
    (sc : ResultativeSubconstruction)
    (hInstr : mc.instrumentSpec = true) :
    let fused := composedMeaning mc sc.toConstruction
    fused.predictedAlternation .causativeInchoative = false ∧
    fused.predictedAlternation .instrumentSubject = false ∧
    fused.predictedAlternation .resultative = false := by
  simp only [composedMeaning, ResultativeSubconstruction.toConstruction]
  exact instrumentSpec_blocks_after_fuse mc _ hInstr

/-! ## Empirical data: grammaticality judgments

Theory-neutral grammaticality judgments and aspectual contrasts drawn
from §§2–8 of the paper. These provide the shared data layer that
other studies (Dendikken, Tay, Levin) connect to their own analyses. -/

open Core.Empirical

/-- What type of resultative is exemplified.

Extends the paper's 2×2 matrix (§2) with fake reflexives (§5) and
anticausative property resultatives (@cite{levin-2026}). -/
inductive ResultativeType where
  | causativeProperty
  | causativePath
  | noncausativeProperty
  | noncausativePath
  | fakeReflexive
  /-- Anticausative: verb doesn't alternate alone; construction licenses it
      (@cite{levin-2026}). Distinct from `noncausativeProperty` (e.g., *freeze
      solid*) where the verb independently shows the causative alternation. -/
  | anticausativeProperty
  deriving Repr, DecidableEq

/-- A single resultative example with judgment data. -/
structure ResultativeDatum where
  /-- Example identifier -/
  exId : String
  /-- The sentence -/
  sentence : String
  /-- Acceptability judgment -/
  judgment : Acceptability
  /-- Which resultative subtype -/
  resType : ResultativeType
  /-- What phenomenon this illustrates -/
  phenomenon : String
  deriving Repr, BEq

/-! ### Causative property resultatives (§2, ex. 5a, 7a) -/

def hammer_flat : ResultativeDatum :=
  { exId := "1a"
  , sentence := "She hammered the metal flat"
  , judgment := .ok
  , resType := .causativeProperty
  , phenomenon := "causative + property RP: agent causes patient to become flat" }

def wipe_clean : ResultativeDatum :=
  { exId := "1b"
  , sentence := "He wiped the table clean"
  , judgment := .ok
  , resType := .causativeProperty
  , phenomenon := "causative + property RP: agent causes patient to become clean" }

def paint_red : ResultativeDatum :=
  { exId := "1c"
  , sentence := "They painted the house red"
  , judgment := .ok
  , resType := .causativeProperty
  , phenomenon := "causative + property RP: agent causes patient to become red" }

/-! ### Causative path resultatives (§2, ex. 5b) -/

def kick_into_field : ResultativeDatum :=
  { exId := "2a"
  , sentence := "She kicked the ball into the field"
  , judgment := .ok
  , resType := .causativePath
  , phenomenon := "causative + path RP: agent causes theme to go to goal" }

def push_off_table : ResultativeDatum :=
  { exId := "2b"
  , sentence := "He pushed the glass off the table"
  , judgment := .ok
  , resType := .causativePath
  , phenomenon := "causative + path RP: agent causes theme to move from source" }

/-! ### Noncausative property resultatives (§2, ex. 6a) -/

def freeze_solid : ResultativeDatum :=
  { exId := "3a"
  , sentence := "The river froze solid"
  , judgment := .ok
  , resType := .noncausativeProperty
  , phenomenon := "noncausative + property RP: theme becomes result state" }

def swing_shut : ResultativeDatum :=
  { exId := "3b"
  , sentence := "The gate swung shut"
  , judgment := .ok
  , resType := .noncausativeProperty
  , phenomenon := "noncausative + property RP: unaccusative verb + result state" }

/-! ### Noncausative path resultatives (§2, ex. 6b) -/

def roll_into_field : ResultativeDatum :=
  { exId := "4a"
  , sentence := "The ball rolled into the field"
  , judgment := .ok
  , resType := .noncausativePath
  , phenomenon := "noncausative + path RP: theme moves along path" }

def slide_off_table : ResultativeDatum :=
  { exId := "4b"
  , sentence := "The book slid off the table"
  , judgment := .ok
  , resType := .noncausativePath
  , phenomenon := "noncausative + path RP: theme moves from source" }

/-! ### Fake reflexive resultatives (§5, ex. 9) -/

def laugh_silly : ResultativeDatum :=
  { exId := "5a"
  , sentence := "She laughed herself silly"
  , judgment := .ok
  , resType := .fakeReflexive
  , phenomenon := "fake reflexive: intransitive verb + reflexive + result" }

def drink_sick : ResultativeDatum :=
  { exId := "5b"
  , sentence := "He drank himself sick"
  , judgment := .ok
  , resType := .fakeReflexive
  , phenomenon := "fake reflexive: verb lacks patient; construction adds it" }

def run_ragged : ResultativeDatum :=
  { exId := "5c"
  , sentence := "She ran herself ragged"
  , judgment := .ok
  , resType := .fakeReflexive
  , phenomenon := "fake reflexive: unergative verb + reflexive + result" }

/-! ### Aspectual contrasts (§4, Principle 27) -/

/-- An aspectual contrast pair. -/
structure AspectualContrast where
  /-- Sentence with temporal adverbial -/
  sentence : String
  /-- Acceptability -/
  judgment : Acceptability
  /-- Which adverbial type -/
  adverbialType : String
  /-- Description -/
  description : String
  deriving Repr, BEq

def hammer_flat_in : AspectualContrast :=
  { sentence := "She hammered the metal flat in an hour"
  , judgment := .ok
  , adverbialType := "in-adverbial"
  , description := "resultative is telic: in-adverbial OK" }

def hammer_flat_for : AspectualContrast :=
  { sentence := "*She hammered the metal flat for an hour"
  , judgment := .unacceptable
  , adverbialType := "for-adverbial"
  , description := "resultative is telic: for-adverbial bad" }

def hammer_bare_for : AspectualContrast :=
  { sentence := "She hammered the metal for an hour"
  , judgment := .ok
  , adverbialType := "for-adverbial"
  , description := "bare activity is atelic: for-adverbial OK" }

def hammer_bare_in : AspectualContrast :=
  { sentence := "??She hammered the metal in an hour"
  , judgment := .marginal
  , adverbialType := "in-adverbial"
  , description := "bare activity is atelic: in-adverbial degraded" }

/-! ### Unacceptable resultatives (§6, semantic coherence violations) -/

def eat_full : ResultativeDatum :=
  { exId := "7a"
  , sentence := "*She ate the food full"
  , judgment := .unacceptable
  , resType := .causativeProperty
  , phenomenon := "semantic incoherence: patient of eat ≠ entity that becomes full" }

def sleep_flat : ResultativeDatum :=
  { exId := "7b"
  , sentence := "*She slept the bed flat"
  , judgment := .unacceptable
  , resType := .causativeProperty
  , phenomenon := "semantic incoherence: sleep cannot cause flatness" }

/-! ### Aggregate data -/

def allExamples : List ResultativeDatum :=
  [ hammer_flat, wipe_clean, paint_red
  , kick_into_field, push_off_table
  , freeze_solid, swing_shut
  , roll_into_field, slide_off_table
  , laugh_silly, drink_sick, run_ragged
  , eat_full, sleep_flat ]

def aspectualContrasts : List AspectualContrast :=
  [ hammer_flat_in, hammer_flat_for, hammer_bare_for, hammer_bare_in ]

/-! ### Empirical verification -/

/-- All four resultative types are attested in the data. -/
theorem has_all_resultative_types :
    (allExamples.any (·.resType == .causativeProperty)) = true ∧
    (allExamples.any (·.resType == .causativePath)) = true ∧
    (allExamples.any (·.resType == .noncausativeProperty)) = true ∧
    (allExamples.any (·.resType == .noncausativePath)) = true ∧
    (allExamples.any (·.resType == .fakeReflexive)) = true := by
  constructor; native_decide
  constructor; native_decide
  constructor; native_decide
  constructor; native_decide
  native_decide

/-- Both grammatical and ungrammatical examples are represented. -/
theorem has_both_judgments :
    (allExamples.any (·.judgment == .ok)) = true ∧
    (allExamples.any (·.judgment == .unacceptable)) = true := by
  constructor; native_decide
  native_decide

/-- The aspectual contrast data includes both in- and for-adverbials. -/
theorem aspectual_both_adverbials :
    (aspectualContrasts.any (·.adverbialType == "in-adverbial")) = true ∧
    (aspectualContrasts.any (·.adverbialType == "for-adverbial")) = true := by
  constructor; native_decide
  native_decide

/-- Telic resultatives accept in-adverbials and reject for-adverbials. -/
theorem telic_adverbial_pattern :
    hammer_flat_in.judgment == .ok ∧
    hammer_flat_for.judgment == .unacceptable := by
  constructor <;> native_decide

/-- Atelic bare activities accept for-adverbials. -/
theorem atelic_adverbial_pattern :
    hammer_bare_for.judgment == .ok := by
  native_decide

end ConstructionGrammar.Studies.GoldbergJackendoff2004
