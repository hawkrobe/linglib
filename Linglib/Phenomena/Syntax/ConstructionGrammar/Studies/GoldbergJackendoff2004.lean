import Linglib.Phenomena.Syntax.ConstructionGrammar.ArgumentStructure
import Linglib.Theories.Semantics.Lexical.Verb.Aspect

/-!
# Goldberg & Jackendoff (2004): The English Resultative as a Family of Constructions

Formalization of the core claims from Goldberg & Jackendoff (2004, Language 80(3):532–568).

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

## Reference

Goldberg, A. E. & Jackendoff, R. (2004). The English Resultative as a
Family of Constructions. Language, 80(3), 532–568.
-/

namespace ConstructionGrammar.Studies.GoldbergJackendoff2004

open ConstructionGrammar
open Semantics.Lexical.Verb.Aspect

/-! ## Core types -/

/-- The kind of subevent in a resultative. -/
inductive SubeventKind where
  /-- From the verb's lexical meaning (e.g., hammering, kicking) -/
  | verbal
  /-- From the construction (CAUSE + BECOME/GO) -/
  | constructional
  deriving Repr, DecidableEq, BEq

/-- How the verbal and constructional subevents are related (§3).

- **means**: The verbal subevent is the means by which the constructional subevent
  is brought about. E.g., "hammer metal flat" — hammering is the means of causing flatness.
- **result**: The constructional subevent is an independent result of the verbal subevent.
  E.g., "the river froze solid" — becoming solid results from freezing.
- **instance_**: The verbal subevent is an instance of the constructional subevent.
  E.g., "kick the ball into the field" — kicking IS a way of causing motion.
- **coOccurrence**: The two subevents merely co-occur without causal connection.
  E.g., "She sang her way down the road" — singing accompanies motion. -/
inductive SubeventRelation where
  | means
  | result
  | instance_
  | coOccurrence
  deriving Repr, DecidableEq, BEq

/-- Type of result phrase. -/
inductive RPType where
  /-- Adjectival/property result: "flat", "clean", "solid" -/
  | property
  /-- Directional/path result: "into the field", "off the table" -/
  | path
  deriving Repr, DecidableEq, BEq

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
  deriving Repr, DecidableEq, BEq

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

/-- Description of a subevent. -/
structure SubeventDesc where
  /-- What the subevent describes -/
  description : String
  /-- Whether CAUSE is part of this subevent -/
  hasCause : Bool := false
  /-- Whether BECOME/GO is part of this subevent -/
  hasBecome : Bool := false
  deriving Repr, BEq

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

/-! ## Boundedness and aspect -/

/-- Whether an RP denotes a bounded endpoint.

Property RPs are always bounded (reaching a property state).
Path RPs are bounded iff the goal is specific ("into the field" = bounded;
"along the road" = unbounded). -/
inductive Boundedness where
  | bounded
  | unbounded
  deriving Repr, DecidableEq, BEq

/-! ## Resultative entry -/

/-- A resultative entry: verb + subconstruction + subevent structure + aspect. -/
structure ResultativeEntry where
  /-- The verb form -/
  verb : String
  /-- Which subconstruction -/
  subconstruction : ResultativeSubconstruction
  /-- The dual subevent structure -/
  subevents : DualSubevent
  /-- Boundedness of the result phrase -/
  rpBoundedness : Boundedness
  /-- Vendler class of the bare verb (without resultative) -/
  bareVerbClass : VendlerClass
  deriving Repr, BEq

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

/-! ## Semantic roles and argument licensing -/

/-- Semantic roles relevant to resultatives (§6). -/
inductive SemRole where
  | agent
  | patient
  | theme
  | resultGoal
  deriving Repr, DecidableEq, BEq

/-- An argument with its source (verb or construction). -/
structure ArgSource where
  /-- The semantic role -/
  role : SemRole
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
  -- Every argument must come from verb, construction, or both
  args.all (λ a => a.fromVerb || a.fromConstruction)

/-! ## Semantic Coherence Principle — Principle 44, §6.2

A verb role rV and a construction role rC may fuse only if rV is
construable as an instance of rC. -/

/-- Which role pairs are coherent for fusion.

Agent can fuse with agent; patient with patient or theme;
theme with patient or theme. -/
def rolesCoherent (rV rC : SemRole) : Bool :=
  match rV, rC with
  | .agent, .agent => true
  | .patient, .patient => true
  | .patient, .theme => true
  | .theme, .patient => true
  | .theme, .theme => true
  | _, _ => false

/-- Check semantic coherence: all fused arguments have coherent roles. -/
def semanticCoherenceSatisfied (args : List (SemRole × SemRole)) : Bool :=
  args.all (λ ⟨rV, rC⟩ => rolesCoherent rV rC)

/-! ## Temporal constraint (§4.2, Principle 33)

The constructional subevent cannot temporally precede the verbal subevent. -/

/-- Temporal ordering between subevents. -/
inductive TemporalOrder where
  | verbalFirst
  | simultaneous
  | constructionalFirst
  deriving Repr, DecidableEq, BEq

/-- Check the temporal constraint: constructional subevent does not precede verbal. -/
def temporalConstraintSatisfied (order : TemporalOrder) : Bool :=
  match order with
  | .verbalFirst => true
  | .simultaneous => true
  | .constructionalFirst => false

/-! ## Empirical data: resultative entries -/

def hammerFlat : ResultativeEntry :=
  { verb := "hammer"
  , subconstruction := .causativeProperty
  , subevents :=
      { verbal := { description := "agent hammers patient" }
      , constructional := { description := "agent CAUSES patient to BECOME flat"
                          , hasCause := true, hasBecome := true }
      , relation := .means }
  , rpBoundedness := .bounded
  , bareVerbClass := .activity }

def kickIntoField : ResultativeEntry :=
  { verb := "kick"
  , subconstruction := .causativePath
  , subevents :=
      { verbal := { description := "agent kicks theme" }
      , constructional := { description := "agent CAUSES theme to GO into field"
                          , hasCause := true, hasBecome := true }
      , relation := .means }
  , rpBoundedness := .bounded
  , bareVerbClass := .activity }

def freezeSolid : ResultativeEntry :=
  { verb := "freeze"
  , subconstruction := .noncausativeProperty
  , subevents :=
      { verbal := { description := "theme freezes" }
      , constructional := { description := "theme BECOMES solid"
                          , hasBecome := true }
      , relation := .result }
  , rpBoundedness := .bounded
  , bareVerbClass := .achievement }

def rollIntoField : ResultativeEntry :=
  { verb := "roll"
  , subconstruction := .noncausativePath
  , subevents :=
      { verbal := { description := "theme rolls" }
      , constructional := { description := "theme GOES into field"
                          , hasBecome := true }
      , relation := .result }
  , rpBoundedness := .bounded
  , bareVerbClass := .activity }

def drinkSick : ResultativeEntry :=
  { verb := "drink"
  , subconstruction := .causativeProperty
  , subevents :=
      { verbal := { description := "agent drinks" }
      , constructional := { description := "agent CAUSES self to BECOME sick"
                          , hasCause := true, hasBecome := true }
      , relation := .means }
  , rpBoundedness := .bounded
  , bareVerbClass := .activity }

def laughSilly : ResultativeEntry :=
  { verb := "laugh"
  , subconstruction := .causativeProperty
  , subevents :=
      { verbal := { description := "agent laughs" }
      , constructional := { description := "agent CAUSES self to BECOME silly"
                          , hasCause := true, hasBecome := true }
      , relation := .means }
  , rpBoundedness := .bounded
  , bareVerbClass := .activity }

def swingShut : ResultativeEntry :=
  { verb := "swing"
  , subconstruction := .noncausativeProperty
  , subevents :=
      { verbal := { description := "theme swings" }
      , constructional := { description := "theme BECOMES shut"
                          , hasBecome := true }
      , relation := .result }
  , rpBoundedness := .bounded
  , bareVerbClass := .activity }

def wipeClea : ResultativeEntry :=
  { verb := "wipe"
  , subconstruction := .causativeProperty
  , subevents :=
      { verbal := { description := "agent wipes patient" }
      , constructional := { description := "agent CAUSES patient to BECOME clean"
                          , hasCause := true, hasBecome := true }
      , relation := .means }
  , rpBoundedness := .bounded
  , bareVerbClass := .activity }

/-- All resultative entries. -/
def allEntries : List ResultativeEntry :=
  [ hammerFlat, kickIntoField, freezeSolid, rollIntoField
  , drinkSick, laughSilly, swingShut, wipeClea ]

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

-- Subevent relation classification
theorem hammerFlat_means :
    hammerFlat.subevents.relation = .means := rfl

theorem freezeSolid_result :
    freezeSolid.subevents.relation = .result := rfl

theorem drinkSick_means :
    drinkSick.subevents.relation = .means := rfl

-- Causative entries have CAUSE in constructional subevent
theorem hammerFlat_has_cause :
    hammerFlat.subevents.constructional.hasCause = true := rfl

theorem kickIntoField_has_cause :
    kickIntoField.subevents.constructional.hasCause = true := rfl

theorem drinkSick_has_cause :
    drinkSick.subevents.constructional.hasCause = true := rfl

-- Noncausative entries lack CAUSE in constructional subevent
theorem freezeSolid_no_cause :
    freezeSolid.subevents.constructional.hasCause = false := rfl

theorem rollIntoField_no_cause :
    rollIntoField.subevents.constructional.hasCause = false := rfl

theorem swingShut_no_cause :
    swingShut.subevents.constructional.hasCause = false := rfl

/-- All causative entries have CAUSE in their constructional subevent. -/
theorem causative_entries_have_cause :
    (allEntries.filter (·.subconstruction.isCausative)).all
      (·.subevents.constructional.hasCause) = true := by
  native_decide

/-- All noncausative entries lack CAUSE in their constructional subevent. -/
theorem noncausative_entries_no_cause :
    (allEntries.filter (λ e => !e.subconstruction.isCausative)).all
      (λ e => !e.subevents.constructional.hasCause) = true := by
  native_decide

/-- All constructional subevents have BECOME. -/
theorem all_constructional_have_become :
    allEntries.all (·.subevents.constructional.hasBecome) = true := by
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

/-! ## Inheritance network

The four subconstructions inherit from the existing `resultative`
construction in `ArgumentStructure.lean`. -/

/-- ArgStructureConstruction for each subconstruction. -/
def causativePropertyConstruction : ArgStructureConstruction :=
  { construction :=
      { name := "Resultative-CausativeProperty"
      , form := "[Subj V Obj AdjP]"
      , meaning := "X CAUSES Y to BECOME Z-state (via V-ing)"
      , specificity := .fullyAbstract }
  , slots :=
      [ ⟨.NOUN, "agent", false⟩
      , ⟨.VERB, "predicate", true⟩
      , ⟨.NOUN, "patient", false⟩
      , ⟨.ADJ, "result", false⟩ ]
  , hasHead := by native_decide }

def causativePathConstruction : ArgStructureConstruction :=
  { construction :=
      { name := "Resultative-CausativePath"
      , form := "[Subj V Obj PP]"
      , meaning := "X CAUSES Y to GO to Z-location (via V-ing)"
      , specificity := .fullyAbstract }
  , slots :=
      [ ⟨.NOUN, "agent", false⟩
      , ⟨.VERB, "predicate", true⟩
      , ⟨.NOUN, "theme", false⟩
      , ⟨.ADP, "goal", false⟩ ]
  , hasHead := by native_decide }

def noncausativePropertyConstruction : ArgStructureConstruction :=
  { construction :=
      { name := "Resultative-NoncausativeProperty"
      , form := "[Subj V AdjP]"
      , meaning := "X BECOMES Z-state (via V-ing)"
      , specificity := .fullyAbstract }
  , slots :=
      [ ⟨.NOUN, "theme", false⟩
      , ⟨.VERB, "predicate", true⟩
      , ⟨.ADJ, "result", false⟩ ]
  , hasHead := by native_decide }

def noncausativePathConstruction : ArgStructureConstruction :=
  { construction :=
      { name := "Resultative-NoncausativePath"
      , form := "[Subj V PP]"
      , meaning := "X GOES to Z-location (via V-ing)"
      , specificity := .fullyAbstract }
  , slots :=
      [ ⟨.NOUN, "theme", false⟩
      , ⟨.VERB, "predicate", true⟩
      , ⟨.ADP, "goal", false⟩ ]
  , hasHead := by native_decide }

/-- The full resultative family: all four subconstructions. -/
def resultativeFamily : List ArgStructureConstruction :=
  [ causativePropertyConstruction
  , causativePathConstruction
  , noncausativePropertyConstruction
  , noncausativePathConstruction ]

/-- Inheritance links from the four subconstructions to the parent resultative. -/
def resultativeInheritance : List InheritanceLink :=
  [ { parent := "Resultative"
    , child := "Resultative-CausativeProperty"
    , mode := .normal
    , sharedProperties := ["dual-subevent", "FAR", "semantic-coherence"]
    , overriddenProperties := ["transitivity: transitive", "RP: AdjP"] }
  , { parent := "Resultative"
    , child := "Resultative-CausativePath"
    , mode := .normal
    , sharedProperties := ["dual-subevent", "FAR", "semantic-coherence"]
    , overriddenProperties := ["transitivity: transitive", "RP: PP"] }
  , { parent := "Resultative"
    , child := "Resultative-NoncausativeProperty"
    , mode := .normal
    , sharedProperties := ["dual-subevent", "FAR", "semantic-coherence"]
    , overriddenProperties := ["transitivity: intransitive", "RP: AdjP", "no CAUSE"] }
  , { parent := "Resultative"
    , child := "Resultative-NoncausativePath"
    , mode := .normal
    , sharedProperties := ["dual-subevent", "FAR", "semantic-coherence"]
    , overriddenProperties := ["transitivity: intransitive", "RP: PP", "no CAUSE"] } ]

/-- All inheritance links point to the same parent. -/
theorem all_inherit_from_resultative :
    resultativeInheritance.all (·.parent == "Resultative") = true := by
  native_decide

/-- All four subconstructions are fully abstract (decomposable). -/
theorem all_subconstructions_abstract :
    resultativeFamily.all (λ c => c.construction.specificity == .fullyAbstract) = true := by
  native_decide

/-- Causative subconstructions are transitive (4 slots). -/
theorem causative_are_transitive :
    causativePropertyConstruction.slots.length = 4 ∧
    causativePathConstruction.slots.length = 4 := by
  constructor <;> rfl

/-- Noncausative subconstructions are intransitive (3 slots). -/
theorem noncausative_are_intransitive :
    noncausativePropertyConstruction.slots.length = 3 ∧
    noncausativePathConstruction.slots.length = 3 := by
  constructor <;> rfl

/-- All four subconstructions decompose via the existing `decompose` function.

Causative subconstructions decompose to [HS, HC, HC].
Noncausative subconstructions decompose to [HS, HC]. -/
theorem causativeProperty_decomposes :
    decompose causativePropertyConstruction =
    [.headSpecifier, .headComplement, .headComplement] := by
  native_decide

theorem causativePath_decomposes :
    decompose causativePathConstruction =
    [.headSpecifier, .headComplement, .headComplement] := by
  native_decide

theorem noncausativeProperty_decomposes :
    decompose noncausativePropertyConstruction =
    [.headSpecifier, .headComplement] := by
  native_decide

theorem noncausativePath_decomposes :
    decompose noncausativePathConstruction =
    [.headSpecifier, .headComplement] := by
  native_decide

/-- The causative subconstructions have the same decomposition as
    the parent resultative construction. -/
theorem causative_match_parent :
    decompose causativePropertyConstruction = decompose resultative ∧
    decompose causativePathConstruction = decompose resultative := by
  constructor <;> native_decide

end ConstructionGrammar.Studies.GoldbergJackendoff2004
