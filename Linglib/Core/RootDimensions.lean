/-!
# Quality Dimensions for Verb Root Content
@cite{dowty-1991} @cite{fillmore-atkins-2000} @cite{hale-keyser-1987} @cite{levin-1993} @cite{talmy-1988} @cite{talmy-2000}

Empirically attested feature dimensions for characterizing the idiosyncratic
("root") content of verb meanings. Verbs within a single class (e.g., Levin's
45.1 Break Verbs) share event structure but may differ along these dimensions
in ways that affect selectional restrictions, figurative extensions, and
cross-linguistic translation equivalence (Spalek & McNally, forthcoming).

## Three-level architecture

**Level 1 — Levin meaning components** (§ 1). Binary features that define verb
classes, diagnosed by diathesis alternation behavior. From Levin (1993:5–10):
the four verbs *break*, *cut*, *hit*, and *touch* are distinguished by the
presence or absence of change of state, contact, motion, and causation.

**Level 2 — Root structural entailments** (§ 3b). Binary features capturing
what the verb root itself entails about event structure: state, manner, result,
and cause. From Beavers & Koontz-Garboden (2020, Table 12). These sit between
template-level event structure and surface meaning components, explaining
*why* surface verbs have the components they do.

**Level 3 — Root-specific features** (§ 3). Range-valued dimensions capturing
within-class variation in root content. A root's "position" along each
dimension is not a point but a **range** of acceptable values (§ 2), reflecting
the fact that verbs are compatible with a range of event types.

## Levin class taxonomy

The full verb class taxonomy from @cite{levin-1993} Part II is encoded in § 4.
This provides a standardized reference for verb classification; individual
verb entries in `Fragments/` are tagged with their Levin class.

## Extensibility

Adding a new dimension: define a value type, add a `Range` field to
`RootProfile` (defaulting to `none`). All existing entries compile unchanged.
Adding a value to an existing dimension: breaking change — forces reviewing
all entries that constrain that dimension. This is by design.

-/

-- ════════════════════════════════════════════════════
-- § 1. Levin (1993) Meaning Components
-- ════════════════════════════════════════════════════

/-- Binary meaning components that define @cite{levin-1993} verb classes.

    These describe **surface** verb behavior, not root-level entailments.
    @cite{beavers-koontz-garboden-2020} argue that surface CoS and causation
    can come from either the template or the root; see `RootEntailments`
    (§ 3b) for the root-level decomposition.

    Diagnosed by participation in diathesis alternations (pp. 5–10):
    - `changeOfState`: middle alternation, causative/inchoative alternation
    - `contact`: body-part possessor ascension alternation
    - `motion`: conative alternation (with contact)
    - `causation`: causative/inchoative alternation (with changeOfState)

    The four canonical classes from Levin's Introduction:
    - *break* = [+CoS, −contact, −motion, +causation]
    - *cut* = [+CoS, +contact, +motion, +causation]
    - *hit* = [−CoS, +contact, +motion, −causation]
    - *touch* = [−CoS, +contact, −motion, −causation]

    Additional binary features (from class descriptions in Part II):
    - `instrumentSpec`: verb specifies instrument/means (cut vs. break; p. 157)
    - `mannerSpec`: verb specifies manner of action (cooking subclasses; p. 244) -/
structure MeaningComponents where
  /-- Does the verb denote causing a change of state?
      Diagnostic: participation in the middle alternation (p. 5). -/
  changeOfState : Bool
  /-- Does the verb's meaning inherently involve contact?
      Diagnostic: body-part possessor ascension (p. 7). -/
  contact : Bool
  /-- Does the verb's meaning inherently involve motion?
      Diagnostic: conative alternation requires both motion and contact (p. 8). -/
  motion : Bool
  /-- Does the verb's meaning include a notion of causation?
      Diagnostic: participation in causative/inchoative alternation (p. 9). -/
  causation : Bool
  /-- Does the verb specify the instrument or means?
      *Cut* includes instrument specification; *break* does not (p. 157). -/
  instrumentSpec : Bool := false
  /-- Does the verb specify the manner of action?
      Cooking verbs "describe different ways of cooking food" (p. 244). -/
  mannerSpec : Bool := false
  deriving DecidableEq, BEq, Repr

namespace MeaningComponents

/-- *break* verbs (45.1): pure change of state, no manner/instrument. -/
def break_ : MeaningComponents :=
  ⟨true, false, false, true, false, false⟩

/-- *cut* verbs (21.1): change of state via contact through motion. -/
def cut : MeaningComponents :=
  ⟨true, true, true, true, true, false⟩

/-- *hit* verbs (18.1): contact by impact, no change of state. -/
def hit : MeaningComponents :=
  ⟨false, true, true, false, false, false⟩

/-- *touch* verbs (20): pure contact, no motion or change of state. -/
def touch : MeaningComponents :=
  ⟨false, true, false, false, false, false⟩

/-- *destroy* verbs (44): total destruction, no specific physical result. -/
def destroy : MeaningComponents :=
  ⟨true, false, false, true, false, false⟩

/-- *bend* verbs (45.2): shape change without disruption of integrity. -/
def bend : MeaningComponents :=
  ⟨true, false, false, true, false, false⟩

end MeaningComponents

-- ════════════════════════════════════════════════════
-- § 2. Range Mechanism
-- ════════════════════════════════════════════════════

/-- Acceptable values along a quality dimension.

    - `none`: the root is unconstrained on this dimension (says nothing)
    - `some [v₁, v₂, …]`: the root is compatible with exactly these values

    Roots are **regions**, not points: a verb like *tear* is compatible with
    a range of force levels, not a single one. -/
abbrev Range (α : Type) := Option (List α)

namespace Range

variable {α : Type}

def unconstrained : Range α := none

def only (vs : List α) : Range α := some vs

def isCompatible [BEq α] : Range α → α → Bool
  | none, _ => true
  | some vs, v => vs.contains v

def isConstrained : Range α → Bool
  | none => false
  | some _ => true

/-- Two ranges overlap if they share at least one value. -/
def overlaps [BEq α] : Range α → Range α → Bool
  | none, _ => true
  | _, none => true
  | some vs₁, some vs₂ => vs₁.any (vs₂.contains ·)

end Range

-- ════════════════════════════════════════════════════
-- § 3. Quality Dimensions (Root-Specific Features)
-- ════════════════════════════════════════════════════

/-- Magnitude of force involved in the event.

    Talmy (1988:52–54) identifies force magnitude as a core parameter of
    force-dynamic schemas. Spalek & McNally: *tear* implies considerable
    force; *rasgar* implies less (enough to damage something flimsy). -/
inductive ForceLevel where
  | none      -- no force component (states)
  | low       -- gentle / minimal force
  | moderate  -- typical force
  | high      -- considerable / violent force
  deriving DecidableEq, BEq, Repr

/-- Spatial pattern of force application.

    @cite{talmy-2000}: force vectors have directional parameters.
    Spalek & McNally: *tear* implies contrary-direction force (pulling
    apart); *rasgar* implies unidirectional force (gash-like). -/
inductive ForceDirection where
  | none             -- no directional force component
  | unidirectional   -- linear / single-direction force (rasgar: gash)
  | bidirectional    -- contrary directions (tear: pulling apart)
  | omnidirectional  -- multi-directional (shatter: radiating fracture)
  deriving DecidableEq, BEq, Repr

/-- Material substantiality of the affected entity (patient).

    Spalek & McNally (forthcoming): the primary dimension distinguishing
    *tear* (unrestricted) from *rasgar* (flimsy patients only). -/
inductive Robustness where
  | insubstantial  -- states, abstractions (silence, darkness)
  | flimsy         -- thin solids: fabric, paper, thin plastic
  | moderate       -- standard solids: rope, muscle, tendons
  | robust         -- thick solids: bread, cement, bone
  deriving DecidableEq, BEq, Repr

/-- Nature of the physical change produced by the event.

    Grounded in @cite{levin-1993}'s class descriptions and @cite{hale-keyser-1987} notion of "separation in material integrity":
    - 45.1 Break: loss of material integrity (break, crack, shatter, tear)
    - 45.2 Bend: change in shape without loss of integrity
    - 44 Destroy: total destruction (no specific resulting state)
    - 21 Cut: separation via instrument contact
    Refined by @cite{beavers-koontz-garboden-2020} on CoS root types. -/
inductive ResultType where
  | separation      -- loss of integrity via pulling apart (tear)
  | surfaceBreach   -- gash-like damage to surface (rasgar)
  | fracture        -- breakage along stress lines (crack, break)
  | fragmentation   -- complete structural failure (shatter, smash)
  | deformation     -- shape change, integrity preserved (bend, fold)
  | totalDestruction -- entity ceases to exist as such (destroy, ruin)
  deriving DecidableEq, BEq, Repr

/-- Whether the agent acts with volitional intent.

    Dowty (1991:572): Proto-Agent entailment P1 = "volitional involvement
    in the event or state." Ausensi (2021, 2024): killing verb roots impose
    specific intentionality requirements on the agent (*murder* requires
    intentional agent; *kill* does not).
    Levin (1993:242): some *break* verbs "allow unintentional, action
    interpretations with body-part objects." -/
inductive Volitionality where
  | nonvolitional  -- unintentional / accidental
  | neutral        -- underspecified for volition
  | volitional     -- intentional / deliberate
  deriving DecidableEq, BEq, Repr

/-- Whether the action can be performed with care and control.

    Dowty (1991:572): Proto-Agent entailment P2 = "sentience
    (and/or perception)," enabling controlled action.
    Spalek & McNally: *tear* is compatible with careful action
    ("carefully tore the tin foil"); *rasgar* is not
    ("??rasgaron con cuidado el papel"). -/
inductive AgentControl where
  | incompatible  -- incompatible with careful/controlled action
  | neutral       -- underspecified for control
  | compatible    -- compatible with careful/controlled action
  deriving DecidableEq, BEq, Repr

/-- Within-class root content profile.

    Captures **quality** dimensions of root content — force, robustness,
    agent properties — as opposed to `RootEntailments` (§ 3b), which
    captures **structural** entailments (state, manner, result, cause).

    Each dimension is a `Range` of acceptable values; `none` means the
    root says nothing about that dimension (unconstrained).

    Together with `MeaningComponents` (which defines the class),
    `LevinClass` (which identifies the class), and `RootEntailments`
    (which captures structural entailments), this gives a four-level
    characterization of a verb's semantic content:
    1. Class-defining meaning components (binary, from alternations)
    2. Class membership (Levin taxonomy)
    3. Root structural entailments (B&KG 2020)
    4. Root-specific quality features (ranges, from detailed lexical analysis) -/
structure RootProfile where
  /-- Force magnitude: @cite{talmy-1988}. -/
  forceMag : Range ForceLevel := none
  /-- Force directionality: @cite{talmy-2000}, Spalek & McNally. -/
  forceDir : Range ForceDirection := none
  /-- Patient material robustness: Spalek & McNally. -/
  patientRob : Range Robustness := none
  /-- Type of physical change: @cite{levin-1993}, @cite{beavers-koontz-garboden-2020}. -/
  resultType : Range ResultType := none
  /-- Agent volitionality: @cite{dowty-1991} P1, @cite{ausensi-yu-smith-2021}. -/
  agentVolition : Range Volitionality := none
  /-- Agent control: @cite{dowty-1991} P2, Spalek & McNally. -/
  agentControl : Range AgentControl := none
  deriving BEq, Repr, Inhabited

-- ════════════════════════════════════════════════════
-- § 3b. Root Structural Entailments (B&KG 2020)
-- ════════════════════════════════════════════════════

/-- Root-level structural entailments from @cite{beavers-koontz-garboden-2020}.

    B&KG argue against Bifurcation (roots only contribute idiosyncratic
    content) and Manner/Result Complementarity (no root encodes both).
    Roots CAN entail states, change, and causation — notions traditionally
    reserved for templates (CAUSE, BECOME).

    The four features define a root typology (Table 12, p. 228):
    - `state`: root describes a state (√FLAT, √CRACK, √DRY)
    - `manner`: root describes an action/manner (√JOG, √RUN, √HIT)
    - `result`: root entails change — passes restitutive *again* test
    - `cause`: root entails causation

    Constraints: `result → state` and `cause → result` (see `wellFormed`).

    @cite{beavers-koontz-garboden-2020} -/
structure RootEntailments where
  state  : Bool
  manner : Bool
  result : Bool
  cause  : Bool
  deriving DecidableEq, BEq, Repr

namespace RootEntailments

/-- If a root entails change (result), it entails a state that changes.
    B&@cite{beavers-koontz-garboden-2020}: result entailments presuppose state entailments. -/
def resultImpliesState (r : RootEntailments) : Bool :=
  !r.result || r.state

/-- If a root entails causation, it entails what is caused (a result).
    B&@cite{beavers-koontz-garboden-2020}: cause entailments presuppose result entailments. -/
def causeImpliesResult (r : RootEntailments) : Bool :=
  !r.cause || r.result

/-- Well-formedness: both collocational constraints hold. -/
def wellFormed (r : RootEntailments) : Bool :=
  r.resultImpliesState && r.causeImpliesResult

/-! ### Canonical root types (B&KG Table 12) -/

/-- +S −M −R −C: property concept roots (√FLAT, √DRY).
    Deadjectival COS verbs — the root names the result state.
    Table 12, row 1, complement position. -/
def propertyConcept : RootEntailments := ⟨true, false, false, false⟩

/-- +S −M +R −C: internally caused result roots (√BLOSSOM, √RUST).
    Root entails both a state and a change to that state, but not
    external causation. Table 12, row 2, complement position. -/
def pureResult : RootEntailments := ⟨true, false, true, false⟩

/-- +S −M +R +C: externally caused result roots (√CRACK, √BREAK).
    Root entails a state, change, AND causation — the root inherently
    implies an external cause. Table 12, row 3, complement position.
    B&KG (p. 228): these "lexicalize crosslinguistically as basic
    causatives" unlike √BLOSSOM-type roots. -/
def causativeResult : RootEntailments := ⟨true, false, true, true⟩

/-- −S +M −R −C: pure manner roots (√JOG, √RUN, √SWIM).
    Root specifies action manner without entailing any state.
    Table 12, row 4, adjoined position. -/
def pureManner : RootEntailments := ⟨false, true, false, false⟩

/-- +S +M +R −C: manner + result without cause.
    Well-formed per the constraints but UNATTESTED in B&KG's Table 12
    (row 6 is empty in both positions). B&KG (p. 229): such roots
    "would essentially derive syntactically unergative verbs with pure
    change-of-state meanings." Defined for completeness. -/
def mannerResult : RootEntailments := ⟨true, true, true, false⟩

/-- +S +M +R +C: fully specified roots (√HAND, √DROWN, √CUT).
    B&KG Ch. 3–4: manner + caused change. These are the attested MRC
    violators. Table 12, row 7.
    √HAND sits in adjoined position, √DROWN in complement position;
    this structural difference is not captured here. -/
def fullSpec : RootEntailments := ⟨true, true, true, true⟩

/-- −S −M −R −C: minimal roots — no structural entailments.
    Conservative default for classes not yet studied under B&KG's
    framework. Not a row in Table 12 (which only lists roots with
    at least one positive feature). -/
def minimal : RootEntailments := ⟨false, false, false, false⟩

/-! ### Canonical type well-formedness -/

theorem propertyConcept_wf : propertyConcept.wellFormed = true := rfl
theorem pureResult_wf : pureResult.wellFormed = true := rfl
theorem causativeResult_wf : causativeResult.wellFormed = true := rfl
theorem pureManner_wf : pureManner.wellFormed = true := rfl
theorem mannerResult_wf : mannerResult.wellFormed = true := rfl
theorem fullSpec_wf : fullSpec.wellFormed = true := rfl
theorem minimal_wf : minimal.wellFormed = true := rfl

/-! ### MRC violation detection -/

/-- Does this root violate Manner/Result Complementarity?
    B&KG Ch. 4: some roots encode both manner and result. -/
def violatesMRC (r : RootEntailments) : Bool := r.manner && r.result

theorem fullSpec_violates_MRC : fullSpec.violatesMRC = true := rfl
theorem mannerResult_violates_MRC : mannerResult.violatesMRC = true := rfl
theorem pureResult_respects_MRC : pureResult.violatesMRC = false := rfl
theorem pureManner_respects_MRC : pureManner.violatesMRC = false := rfl
theorem causativeResult_respects_MRC : causativeResult.violatesMRC = false := rfl

end RootEntailments

-- ════════════════════════════════════════════════════
-- § 4. Levin (1993) Verb Class Taxonomy
-- ════════════════════════════════════════════════════

/-- Verb class taxonomy from @cite{levin-1993} Part II.

    Section numbers follow the book. Class names are Levin's labels.
    This provides a standardized, widely-cited reference for verb
    classification; 49 top-level classes covering the English verb lexicon.

    Not all subclasses are listed here — the taxonomy is intentionally
    at the top-level class grain, with subclass distinctions handled by
    `MeaningComponents` and `RootProfile`. -/
inductive LevinClass where
  -- Verbs of Putting (§ 9)
  | put                -- 9.1: put, place, set, lay, ...
  | funnel             -- 9.3: funnel, channel, siphon, ...
  | pour               -- 9.5: pour, drip, dribble, ...
  | coil               -- 9.6: coil, spin, twist, ...
  | sprayLoad          -- 9.7: spray, load, pack, ...
  -- Verbs of Removing (§ 10)
  | remove             -- 10.1: remove, withdraw, extract, ...
  | clear              -- 10.3: clear, clean, drain, ...
  | wipe               -- 10.4: wipe, scrub, sweep, ...
  | steal              -- 10.5: steal, rob, pilfer, ...
  -- Verbs of Sending and Carrying (§ 11)
  | send               -- 11.1: send, ship, mail, ...
  | carry              -- 11.4: carry, haul, lug, ...
  | drive              -- 11.5: drive, fly, sail, ...
  -- Verbs of Exerting Force (§ 12)
  | pushPull           -- 12: push, pull, press, tug, ...
  -- Verbs of Change of Possession (§ 13)
  | give               -- 13.1: give, hand, pass, ...
  | contribute         -- 13.2: contribute, donate, ...
  | getObtain          -- 13.5: get, obtain, acquire, ...
  | exchange           -- 13.6: exchange, swap, trade, ...
  -- Learn Verbs (§ 14)
  | learn              -- 14: learn, study, memorize, ...
  -- Hold and Keep Verbs (§ 15)
  | hold               -- 15.1: hold, grasp, clutch, ...
  -- Verbs of Concealment (§ 16)
  | conceal            -- 16: conceal, hide, cover, ...
  -- Verbs of Throwing (§ 17)
  | throw              -- 17.1: throw, toss, fling, ...
  -- Verbs of Contact by Impact (§ 18)
  | hit                -- 18.1: hit, bash, kick, ...
  | swat               -- 18.2: swat, slap, whack, ...
  -- Poke Verbs (§ 19)
  | poke               -- 19: poke, jab, pierce, ...
  -- Verbs of Contact: Touch (§ 20)
  | touch              -- 20: touch, pat, stroke, ...
  -- Verbs of Cutting (§ 21)
  | cut                -- 21.1: cut, hack, saw, slash, ...
  | carve              -- 21.2: carve, chop, dice, ...
  -- Verbs of Combining and Attaching (§ 22)
  | mix                -- 22.1: mix, blend, combine, ...
  | amalgamate         -- 22.2: amalgamate, integrate, ...
  -- Verbs of Separating and Disassembling (§ 23)
  | separate           -- 23.1: separate, disconnect, ...
  | split              -- 23.2: split, divide, ...
  -- Verbs of Coloring (§ 24)
  | color              -- 24: color, dye, paint, ...
  -- Image Creation (§ 25)
  | imageCreation      -- 25: draw, etch, engrave, ...
  -- Verbs of Creation and Transformation (§ 26)
  | build              -- 26.1: build, assemble, construct, ...
  | grow               -- 26.2: grow, cultivate, ...
  | create             -- 26.4: create, design, invent, ...
  | knead              -- 26.5: knead, mold, shape, ...
  | turn               -- 26.6: turn, convert, transform, ...
  | performance        -- 26.7: perform, play, sing, ...
  -- Engender Verbs (§ 27)
  | engender           -- 27: engender, cause, generate, ...
  -- Calve Verbs (§ 28)
  | calve              -- 28: calve, foal, lamb, ...
  -- Verbs with Predicative Complements (§ 29)
  | appoint            -- 29.1: appoint, name, elect, ...
  | characterize       -- 29.2: characterize, classify, ...
  | declare            -- 29.4: declare, certify, ...
  -- Verbs of Perception (§ 30)
  | see                -- 30.1: see, hear, feel, ...
  | sight              -- 30.2: sight, spot, glimpse, ...
  -- Psych-Verbs (§ 31)
  | amuse              -- 31.1: amuse, delight, frighten, ...
  | admire             -- 31.2: admire, envy, respect, ...
  | marvel             -- 31.3: marvel, grieve, ...
  -- Verbs of Desire (§ 32)
  | want               -- 32.1: want, need, desire, ...
  -- Judgment Verbs (§ 33)
  | judgment           -- 33: judge, blame, praise, ...
  -- Verbs of Assessment (§ 34)
  | assessment         -- 34: assess, evaluate, ...
  -- Verbs of Searching (§ 35)
  | search             -- 35: hunt, search, stalk, ...
  -- Verbs of Social Interaction (§ 36)
  | socialInteraction  -- 36: correspond, marry, meet, ...
  -- Verbs of Communication (§ 37)
  | say                -- 37.7: say, report, announce, ...
  | tell               -- 37.2: tell, inform, notify, ...
  | mannerOfSpeaking   -- 37.3: whisper, shout, mumble, ...
  -- Verbs of Sounds Made by Animals (§ 38)
  | animalSound        -- 38: bark, moo, roar, ...
  -- Verbs of Ingesting (§ 39)
  | eat                -- 39.1: eat, consume, ...
  | devour             -- 39.4: devour, gobble, ...
  | dine               -- 39.5: dine, feast, ...
  -- Verbs Involving the Body (§ 40)
  | bodyProcess        -- 40.1: hiccup, breathe, cough, ...
  | flinch             -- 40.5: flinch, cringe, wince, ...
  -- Verbs of Grooming and Bodily Care (§ 41)
  | dress              -- 41.1: dress, clothe, ...
  -- Verbs of Killing (§ 42)
  | murder             -- 42.1: murder, assassinate, ...
  | poison             -- 42.2: poison, drown, ...
  -- Verbs of Emission (§ 43)
  | lightEmission      -- 43.1: glow, shine, sparkle, ...
  | soundEmission      -- 43.2: ring, buzz, creak, ...
  | substanceEmission  -- 43.4: gush, ooze, bleed, ...
  -- Destroy Verbs (§ 44)
  | destroy            -- 44: destroy, demolish, raze, ...
  -- Verbs of Change of State (§ 45)
  | break_             -- 45.1: break, crack, rip, shatter, tear, ...
  | bend               -- 45.2: bend, crease, fold, ...
  | cooking            -- 45.3: bake, boil, fry, ...
  | otherCoS           -- 45.4: burn, melt, freeze, ...
  | entitySpecificCoS  -- 45.5: bloom, rust, ...
  | calibratableCoS    -- 45.6: increase, decrease, ...
  -- Lodge Verbs (§ 46)
  | lodge              -- 46: lodge, shelter, ...
  -- Verbs of Existence (§ 47)
  | exist              -- 47.1: exist, remain, ...
  -- Verbs of Appearance (§ 48)
  | appear             -- 48.1: appear, emerge, ...
  -- Verbs of Body-Internal Motion (§ 49)
  | bodyInternalMotion -- 49: fidget, squirm, ...
  -- Verbs of Assuming a Position (§ 50)
  | assumePosition     -- 50: sit, stand, lie, ...
  -- Verbs of Motion (§ 51)
  | inherentlyDirectedMotion -- 51.1: arrive, come, go, ...
  | leave              -- 51.2: leave, depart, ...
  | mannerOfMotion     -- 51.3: run, walk, swim, ...
  | vehicleMotion      -- 51.4: drive, fly, sail, ...
  | chase              -- 51.6: chase, pursue, ...
  -- Avoid Verbs (§ 52)
  | avoid              -- 52: avoid, escape, ...
  -- Verbs of Lingering and Rushing (§ 53)
  | linger             -- 53.1: linger, loiter, ...
  | rush               -- 53.2: rush, hurry, ...
  -- Measure Verbs (§ 54)
  | measure            -- 54: cost, weigh, ...
  -- Aspectual Verbs (§ 55)
  | aspectual          -- 55: begin, start, finish, ...
  -- Weather Verbs (§ 57)
  | weather            -- 57: rain, snow, ...
  deriving DecidableEq, BEq, Repr

/-- Section number in @cite{levin-1993} for each class. -/
def LevinClass.section : LevinClass → String
  | .put => "9.1" | .funnel => "9.3" | .pour => "9.5"
  | .coil => "9.6" | .sprayLoad => "9.7"
  | .remove => "10.1" | .clear => "10.3" | .wipe => "10.4"
  | .steal => "10.5"
  | .send => "11.1" | .carry => "11.4" | .drive => "11.5"
  | .pushPull => "12"
  | .give => "13.1" | .contribute => "13.2"
  | .getObtain => "13.5" | .exchange => "13.6"
  | .learn => "14" | .hold => "15.1" | .conceal => "16"
  | .throw => "17.1" | .hit => "18.1" | .swat => "18.2"
  | .poke => "19" | .touch => "20"
  | .cut => "21.1" | .carve => "21.2"
  | .mix => "22.1" | .amalgamate => "22.2"
  | .separate => "23.1" | .split => "23.2"
  | .color => "24" | .imageCreation => "25"
  | .build => "26.1" | .grow => "26.2" | .create => "26.4"
  | .knead => "26.5" | .turn => "26.6" | .performance => "26.7"
  | .engender => "27" | .calve => "28"
  | .appoint => "29.1" | .characterize => "29.2" | .declare => "29.4"
  | .see => "30.1" | .sight => "30.2"
  | .amuse => "31.1" | .admire => "31.2" | .marvel => "31.3"
  | .want => "32.1" | .judgment => "33" | .assessment => "34"
  | .search => "35" | .socialInteraction => "36"
  | .say => "37.7" | .tell => "37.2" | .mannerOfSpeaking => "37.3"
  | .animalSound => "38"
  | .eat => "39.1" | .devour => "39.4" | .dine => "39.5"
  | .bodyProcess => "40.1" | .flinch => "40.5" | .dress => "41.1"
  | .murder => "42.1" | .poison => "42.2"
  | .lightEmission => "43.1" | .soundEmission => "43.2"
  | .substanceEmission => "43.4"
  | .destroy => "44"
  | .break_ => "45.1" | .bend => "45.2" | .cooking => "45.3"
  | .otherCoS => "45.4" | .entitySpecificCoS => "45.5"
  | .calibratableCoS => "45.6"
  | .lodge => "46" | .exist => "47.1" | .appear => "48.1"
  | .bodyInternalMotion => "49" | .assumePosition => "50"
  | .inherentlyDirectedMotion => "51.1" | .leave => "51.2"
  | .mannerOfMotion => "51.3" | .vehicleMotion => "51.4"
  | .chase => "51.6"
  | .avoid => "52" | .linger => "53.1" | .rush => "53.2"
  | .measure => "54" | .aspectual => "55" | .weather => "57"

/-- Meaning components associated with each Levin class.

    Profiles are assigned using the diagnostic criteria from Levin (1993:5–10):
    - `changeOfState`: middle alternation (*the glass broke* / *this bread cuts easily*)
    - `contact`: body-part possessor ascension (*I hit him on the arm* / *I hit his arm*)
    - `motion`: conative alternation requires motion + contact (*I cut at the bread*)
    - `causation`: causative/inchoative alternation (*she broke the vase* / *the vase broke*)
    - `instrumentSpec`: verb specifies instrument/means (cut vs. break; p. 157)
    - `mannerSpec`: verb specifies manner of action (cooking, manner of motion; p. 244)

    For classes not discussed in the canonical quadruple analysis, profiles are inferred
    from Part II class descriptions and alternation participation patterns. -/
def LevinClass.meaningComponents : LevinClass → MeaningComponents
  -- §9 Putting: caused change of location (motion + causation)
  | .put => ⟨false, false, true, true, false, false⟩
  | .funnel => ⟨false, false, true, true, false, true⟩        -- manner of putting
  | .pour => ⟨false, false, true, true, false, true⟩          -- manner of putting
  | .coil => ⟨false, false, true, true, false, true⟩          -- resulting configuration
  | .sprayLoad => ⟨false, false, true, true, false, false⟩
  -- §10 Removing: caused change of location away from source
  | .remove => ⟨false, false, true, true, false, false⟩
  | .clear => ⟨true, false, true, true, false, false⟩         -- location undergoes CoS
  | .wipe => ⟨true, true, true, true, false, true⟩            -- contact + manner of removing
  | .steal => ⟨false, false, false, true, false, false⟩       -- change of possession, not physical motion
  -- §11 Sending and Carrying: caused motion
  | .send => ⟨false, false, true, true, false, false⟩
  | .carry => ⟨false, true, true, true, false, true⟩          -- contact + manner (holding while moving)
  | .drive => ⟨false, false, true, true, false, true⟩         -- manner via vehicle
  -- §12 Exerting Force: directed force with contact
  | .pushPull => ⟨false, true, true, false, false, false⟩     -- no causative alternation
  -- §13 Change of Possession
  | .give => ⟨false, false, false, true, false, false⟩        -- caused transfer
  | .contribute => ⟨false, false, false, true, false, false⟩
  | .getObtain => ⟨false, false, false, false, false, false⟩  -- no causation (receiver perspective)
  | .exchange => ⟨false, false, false, false, false, false⟩
  -- §14–16
  | .learn => ⟨false, false, false, false, false, false⟩
  | .hold => ⟨false, true, false, false, false, false⟩        -- inherent contact
  | .conceal => ⟨true, false, false, true, false, false⟩      -- causes hidden state
  -- §17 Throwing: ballistic caused motion with initial contact
  | .throw => ⟨false, true, true, true, false, false⟩
  -- §18 Contact by Impact
  | .hit => .hit
  | .swat => ⟨false, true, true, false, false, false⟩         -- like hit
  -- §19 Poking: contact through motion with instrument
  | .poke => ⟨false, true, true, false, true, false⟩
  -- §20 Contact: Touch
  | .touch => .touch
  -- §21 Cutting
  | .cut => .cut
  | .carve => ⟨true, true, true, true, true, false⟩
  -- §22 Combining and Attaching
  | .mix => ⟨true, false, false, true, false, false⟩          -- CoS (combined state)
  | .amalgamate => ⟨true, false, false, true, false, false⟩
  -- §23 Separating and Disassembling
  | .separate => ⟨true, false, false, true, false, false⟩
  | .split => ⟨true, true, false, true, true, false⟩          -- contact + instrument
  -- §24 Coloring: surface CoS via contact
  | .color => ⟨true, true, false, true, false, false⟩
  -- §25 Image Creation: surface CoS with instrument
  | .imageCreation => ⟨true, true, false, true, true, false⟩
  -- §26 Creation and Transformation
  | .build => ⟨true, false, false, true, false, false⟩        -- CoS (creation)
  | .grow => ⟨true, false, false, true, false, false⟩
  | .create => ⟨true, false, false, true, false, false⟩
  | .knead => ⟨true, true, false, true, false, true⟩          -- contact + manner
  | .turn => ⟨true, false, false, true, false, false⟩         -- transformation
  | .performance => ⟨false, false, false, false, false, true⟩  -- manner only
  -- §27–28
  | .engender => ⟨true, false, false, true, false, false⟩     -- bringing into being
  | .calve => ⟨true, false, false, false, false, false⟩       -- inherent process, not caused
  -- §29 Predicative Complements
  | .appoint => ⟨true, false, false, true, false, false⟩      -- status change
  | .characterize => ⟨false, false, false, false, false, false⟩
  | .declare => ⟨true, false, false, true, false, false⟩
  -- §30 Perception
  | .see => ⟨false, false, false, false, false, false⟩
  | .sight => ⟨false, false, false, false, false, false⟩
  -- §31 Psych-Verbs
  | .amuse => ⟨true, false, false, true, false, false⟩        -- stimulus causes psychological CoS
  | .admire => ⟨false, false, false, false, false, false⟩     -- stative
  | .marvel => ⟨false, false, false, false, false, false⟩     -- stative
  -- §32–34
  | .want => ⟨false, false, false, false, false, false⟩
  | .judgment => ⟨false, false, false, false, false, false⟩
  | .assessment => ⟨false, false, false, false, false, false⟩
  -- §35 Searching
  | .search => ⟨false, false, true, false, false, false⟩      -- directed motion through space
  -- §36 Social Interaction
  | .socialInteraction => ⟨false, false, false, false, false, false⟩
  -- §37 Communication
  | .say => ⟨false, false, false, false, false, false⟩
  | .tell => ⟨false, false, false, false, false, false⟩
  | .mannerOfSpeaking => ⟨false, false, false, false, false, true⟩  -- manner specified
  -- §38 Animal Sounds
  | .animalSound => ⟨false, false, false, false, false, true⟩
  -- §39 Ingesting
  | .eat => ⟨true, true, false, false, false, false⟩          -- CoS (consumption) + contact
  | .devour => ⟨true, true, false, false, false, true⟩        -- + manner
  | .dine => ⟨false, false, false, false, false, true⟩        -- manner only (social activity)
  -- §40 Body
  | .bodyProcess => ⟨false, false, false, false, false, false⟩
  | .flinch => ⟨false, false, true, false, false, false⟩      -- involuntary motion
  -- §41 Grooming
  | .dress => ⟨true, true, false, true, false, false⟩         -- CoS (dressed state) + contact
  -- §42 Killing
  | .murder => ⟨true, false, false, true, false, false⟩
  | .poison => ⟨true, false, false, true, true, false⟩        -- instrument specified
  -- §43 Emission
  | .lightEmission => ⟨false, false, false, false, false, false⟩
  | .soundEmission => ⟨false, false, false, false, false, false⟩
  | .substanceEmission => ⟨false, false, false, false, false, false⟩
  -- §44 Destroy
  | .destroy => .destroy
  -- §45 Change of State
  | .break_ => .break_
  | .bend => .bend
  | .cooking => ⟨true, false, false, true, false, true⟩       -- CoS + manner (bake/boil/fry)
  | .otherCoS => ⟨true, false, false, true, false, false⟩     -- burn, melt, freeze
  | .entitySpecificCoS => ⟨true, false, false, true, false, false⟩  -- bloom, rust
  | .calibratableCoS => ⟨true, false, false, true, false, false⟩    -- increase, decrease
  -- §46 Lodge
  | .lodge => ⟨false, false, true, false, false, false⟩       -- locating
  -- §47 Existence
  | .exist => ⟨false, false, false, false, false, false⟩      -- pure stative
  -- §48 Appearance
  | .appear => ⟨true, false, false, false, false, false⟩      -- coming into view = CoS
  -- §49 Body-Internal Motion
  | .bodyInternalMotion => ⟨false, false, true, false, false, false⟩
  -- §50 Assuming a Position
  | .assumePosition => ⟨true, false, true, false, false, false⟩  -- CoS (new position) + motion
  -- §51 Motion
  | .inherentlyDirectedMotion => ⟨false, false, true, false, false, false⟩
  | .leave => ⟨false, false, true, false, false, false⟩
  | .mannerOfMotion => ⟨false, false, true, false, false, true⟩   -- manner specified
  | .vehicleMotion => ⟨false, false, true, false, false, true⟩    -- vehicle = manner
  | .chase => ⟨false, false, true, false, false, false⟩
  -- §52 Avoid
  | .avoid => ⟨false, false, false, false, false, false⟩      -- no inherent motion
  -- §53 Lingering and Rushing
  | .linger => ⟨false, false, false, false, false, true⟩      -- temporal manner
  | .rush => ⟨false, false, true, false, false, true⟩         -- motion + manner
  -- §54 Measure
  | .measure => ⟨false, false, false, false, false, false⟩    -- stative
  -- §55 Aspectual
  | .aspectual => ⟨true, false, false, true, false, false⟩    -- causative alternation (start/stop)
  -- §57 Weather
  | .weather => ⟨false, false, false, false, false, false⟩

-- ════════════════════════════════════════════════════
-- § 5. Diathesis Alternation Diagnostics
-- ════════════════════════════════════════════════════

/-- Diathesis alternations from @cite{levin-1993} Part One that serve as diagnostics
    for verb class membership. The first four are the canonical diagnostics
    from the Introduction (pp. 5–10); others are class-specific. -/
inductive DiathesisAlternation where
  /-- §1.1.2: *she broke the vase* / *the vase broke*. Diagnoses causation + CoS. -/
  | causativeInchoative
  /-- §1.2: *the bread cuts easily*. Diagnoses change of state. -/
  | middle
  /-- §1.3: *I cut at the bread*. Diagnoses contact + motion. -/
  | conative
  /-- §1.4.1: *I hit him on the arm* / *I hit his arm*. Diagnoses contact. -/
  | bodyPartPossessorAscension
  /-- §2.1: *give NP NP* / *give NP to NP*. Give/send class. -/
  | dative
  /-- §2.3: *spray paint on wall* / *spray wall with paint*. Spray/load class. -/
  | locative
  /-- §8.1: *hammer the metal flat*. Available to manner verbs. -/
  | resultative
  deriving DecidableEq, BEq, Repr

/-- Predicted alternation participation derived from meaning components.

    The core claim of Levin (1993:5–10): meaning components — diagnosed by
    alternation participation — form the bridge between verb semantics and
    verb syntax. Each diagnostic alternation corresponds to a specific
    configuration of meaning components:

    | Alternation | Required components |
    |---|---|
    | Causative/inchoative | changeOfState ∧ causation ∧ ¬instrumentSpec |
    | Middle | changeOfState |
    | Conative | contact ∧ motion |
    | Body-part possessor ascension | contact |
    | Resultative | changeOfState ∧ ¬instrumentSpec (manner verbs) |

    Dative and locative alternations are class-specific rather than
    component-derived, so they must be checked per class. -/
def MeaningComponents.predictedAlternation : MeaningComponents → DiathesisAlternation → Bool
  | mc, .causativeInchoative => mc.changeOfState && mc.causation && !mc.instrumentSpec
  | mc, .middle => mc.changeOfState
  | mc, .conative => mc.contact && mc.motion
  | mc, .bodyPartPossessorAscension => mc.contact
  | _, .dative => false         -- class-specific, not component-derived
  | _, .locative => false       -- class-specific, not component-derived
  | mc, .resultative => mc.changeOfState && !mc.instrumentSpec

/-- Full alternation profile for a Levin class, combining component-derived
    predictions with class-specific overrides for dative and locative. -/
def LevinClass.participatesIn (c : LevinClass) (alt : DiathesisAlternation) : Bool :=
  c.meaningComponents.predictedAlternation alt ||
  match c, alt with
  | .give, .dative | .send, .dative | .tell, .dative => true
  | .sprayLoad, .locative => true
  | _, _ => false

/-! ### Canonical diagnostic theorems

The four verbs *break*, *cut*, *hit*, *touch* are distinguished by exactly
their pattern of alternation participation (Levin 1993:5–10). -/

/-- Break participates in causative/inchoative and middle (CoS + causation). -/
theorem break_alternations :
    LevinClass.break_.participatesIn .causativeInchoative = true
    ∧ LevinClass.break_.participatesIn .middle = true
    ∧ LevinClass.break_.participatesIn .conative = false
    ∧ LevinClass.break_.participatesIn .bodyPartPossessorAscension = false := ⟨rfl, rfl, rfl, rfl⟩

/-- Cut participates in middle, conative, and BPPA but NOT causative/inchoative.
    Instrument specification blocks the inchoative: "*The string cut." (Levin p. 9, ex. 23b).
    Because *cut* inherently specifies an instrument, it requires an agent (p. 10). -/
theorem cut_alternations :
    LevinClass.cut.participatesIn .causativeInchoative = false
    ∧ LevinClass.cut.participatesIn .middle = true
    ∧ LevinClass.cut.participatesIn .conative = true
    ∧ LevinClass.cut.participatesIn .bodyPartPossessorAscension = true := ⟨rfl, rfl, rfl, rfl⟩

/-- Hit participates in conative and body-part ascension (contact + motion, no CoS). -/
theorem hit_alternations :
    LevinClass.hit.participatesIn .causativeInchoative = false
    ∧ LevinClass.hit.participatesIn .middle = false
    ∧ LevinClass.hit.participatesIn .conative = true
    ∧ LevinClass.hit.participatesIn .bodyPartPossessorAscension = true := ⟨rfl, rfl, rfl, rfl⟩

/-- Touch participates only in body-part ascension (contact only). -/
theorem touch_alternations :
    LevinClass.touch.participatesIn .causativeInchoative = false
    ∧ LevinClass.touch.participatesIn .middle = false
    ∧ LevinClass.touch.participatesIn .conative = false
    ∧ LevinClass.touch.participatesIn .bodyPartPossessorAscension = true := ⟨rfl, rfl, rfl, rfl⟩

/-- Instrument specification blocks the causative/inchoative alternation
    for any verb, regardless of other meaning components.
    Because the instrument must be wielded by an agent, the agentless
    inchoative variant is unavailable. -/
theorem MeaningComponents.instrumentSpec_blocks_ci (mc : MeaningComponents)
    (h : mc.instrumentSpec = true) :
    mc.predictedAlternation .causativeInchoative = false := by
  simp only [predictedAlternation, h, Bool.not_true, Bool.and_false]

/-- Corollary: instrument specification also blocks the resultative
    (same reasoning — manner verbs that specify an instrument cannot
    appear in the resultative construction). -/
theorem MeaningComponents.instrumentSpec_blocks_resultative (mc : MeaningComponents)
    (h : mc.instrumentSpec = true) :
    mc.predictedAlternation .resultative = false := by
  simp only [predictedAlternation, h, Bool.not_true, Bool.and_false]

/-! ### Cross-class predictions -/

/-- All CoS classes (§45) participate in the causative/inchoative alternation. -/
theorem cos_classes_causative :
    LevinClass.break_.participatesIn .causativeInchoative = true
    ∧ LevinClass.bend.participatesIn .causativeInchoative = true
    ∧ LevinClass.cooking.participatesIn .causativeInchoative = true
    ∧ LevinClass.otherCoS.participatesIn .causativeInchoative = true := ⟨rfl, rfl, rfl, rfl⟩

/-- Spray/load participates in the locative alternation. -/
theorem sprayLoad_locative :
    LevinClass.sprayLoad.participatesIn .locative = true := rfl

/-- Give class participates in the dative alternation. -/
theorem give_dative :
    LevinClass.give.participatesIn .dative = true := rfl

/-- Motion verbs (§51) don't participate in causative alternation (no causation component). -/
theorem motion_no_causative :
    LevinClass.mannerOfMotion.participatesIn .causativeInchoative = false
    ∧ LevinClass.inherentlyDirectedMotion.participatesIn .causativeInchoative = false := ⟨rfl, rfl⟩

/-- Contact verbs predict conative alternation participation. -/
theorem contact_motion_conative :
    LevinClass.hit.participatesIn .conative = true
    ∧ LevinClass.swat.participatesIn .conative = true
    ∧ LevinClass.poke.participatesIn .conative = true
    ∧ LevinClass.cut.participatesIn .conative = true := ⟨rfl, rfl, rfl, rfl⟩

/-- Touch verbs lack motion → no conative despite having contact. -/
theorem touch_no_conative :
    LevinClass.touch.participatesIn .conative = false := rfl

/-- Cut participates in resultative; break does too (no instrumentSpec). -/
theorem cut_no_resultative_break_resultative :
    LevinClass.cut.participatesIn .resultative = false
    ∧ LevinClass.break_.participatesIn .resultative = true := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 6. Predicted Unaccusativity
-- ════════════════════════════════════════════════════

/-- Predicted unaccusativity from Levin class membership.

    Based on Levin & Rappaport @cite{levin-hovav-1995}: unaccusativity correlates with
    internally caused change of state or directed change, while unergativity
    correlates with agentive activity.

    For classes that participate in the causative/inchoative alternation
    (CoS + causation), this predicts unaccusativity for the intransitive
    (inchoative) alternant. For inherently intransitive classes (emission,
    existence, appearance), this predicts unaccusativity outright.

    **Key omission**: manner-of-speaking verbs (§37.3) are predicted
    unergative here (agentive manner), but @cite{storment-2026} shows they
    are empirically unaccusative. This is a documented divergence. -/
def LevinClass.predictsUnaccusative : LevinClass → Bool
  -- §45 Change of State: inchoative alternant is unaccusative
  | .break_ | .bend | .cooking | .otherCoS
  | .entitySpecificCoS | .calibratableCoS => true
  -- §44 Destroy: CoS (total destruction)
  | .destroy => true
  -- §22 Combining: CoS (combined state)
  | .mix | .amalgamate => true
  -- §23 Separating: CoS
  | .separate | .split => true
  -- §48 Appearance: coming into view
  | .appear => true
  -- §47 Existence: stative (there-insertion diagnostic)
  | .exist => true
  -- §28 Calve: internally caused CoS
  | .calve => true
  -- §51.1 Inherently directed motion: goal-oriented
  | .inherentlyDirectedMotion => true
  -- §51.2 Leave: source-oriented directed motion
  | .leave => true
  -- §43 Emission: source argument is internal
  | .lightEmission | .soundEmission | .substanceEmission => true
  -- §57 Weather: expletive subject
  | .weather => true
  -- Default: not predicted unaccusative (includes agentive activities,
  -- manner of motion §51.3, manner of speaking §37.3, body process §40.1)
  | _ => false

/-! ### Unaccusativity prediction theorems -/

/-- CoS classes (§45) predict unaccusative. -/
theorem cos_predicts_unaccusative :
    LevinClass.predictsUnaccusative .break_ = true
    ∧ LevinClass.predictsUnaccusative .bend = true
    ∧ LevinClass.predictsUnaccusative .cooking = true
    ∧ LevinClass.predictsUnaccusative .otherCoS = true := ⟨rfl, rfl, rfl, rfl⟩

/-- Manner-of-motion (§51.3) predicts unergative. -/
theorem mom_predicts_unergative :
    LevinClass.predictsUnaccusative .mannerOfMotion = false := rfl

/-- Inherently directed motion (§51.1) predicts unaccusative. -/
theorem idm_predicts_unaccusative :
    LevinClass.predictsUnaccusative .inherentlyDirectedMotion = true := rfl

/-- Emission classes (§43) predict unaccusative. -/
theorem emission_predicts_unaccusative :
    LevinClass.predictsUnaccusative .lightEmission = true
    ∧ LevinClass.predictsUnaccusative .soundEmission = true
    ∧ LevinClass.predictsUnaccusative .substanceEmission = true := ⟨rfl, rfl, rfl⟩

/-- MoS (§37.3) does NOT predict unaccusative — this is the Storment divergence. -/
theorem mos_predicts_unergative :
    LevinClass.predictsUnaccusative .mannerOfSpeaking = false := rfl

/-- The causative/inchoative alternation implies the existence of an
    unaccusative variant: if a class participates in causative/inchoative,
    it predicts unaccusativity for the inchoative alternant. -/
theorem causativeInchoative_implies_unaccusative :
    LevinClass.break_.participatesIn .causativeInchoative = true
    ∧ LevinClass.predictsUnaccusative .break_ = true
    ∧ LevinClass.otherCoS.participatesIn .causativeInchoative = true
    ∧ LevinClass.predictsUnaccusative .otherCoS = true := ⟨rfl, rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 7. Derived Properties
-- ════════════════════════════════════════════════════

/-- Does a root profile constrain patient properties? -/
def RootProfile.constrainsPatient (rp : RootProfile) : Bool :=
  rp.patientRob.isConstrained

/-- Do two root profiles overlap (share at least one compatible event)? -/
def RootProfile.overlaps (rp₁ rp₂ : RootProfile) : Bool :=
  rp₁.forceMag.overlaps rp₂.forceMag &&
  rp₁.forceDir.overlaps rp₂.forceDir &&
  rp₁.patientRob.overlaps rp₂.patientRob &&
  rp₁.resultType.overlaps rp₂.resultType &&
  rp₁.agentVolition.overlaps rp₂.agentVolition &&
  rp₁.agentControl.overlaps rp₂.agentControl

-- ════════════════════════════════════════════════════
-- § 8. Root Entailment Mapping (B&KG 2020)
-- ════════════════════════════════════════════════════

/-- Root structural entailments for each Levin class.

    Assignments marked (B&KG) are directly from @cite{beavers-koontz-garboden-2020} Table 12 and Chapters 2–5. Others are inferred from class
    semantics following B&KG's framework:
    - Externally caused CoS → `causativeResult` (√CRACK pattern)
    - Internally caused CoS → `pureResult` (√BLOSSOM pattern)
    - Action/manner verbs → `pureManner` (√JOG pattern)
    - MRC violators → `fullSpec` (√HAND/√DROWN pattern)
    - Stative/psychological → `propertyConcept` (√FLAT pattern)

    Classes marked (default) use `minimal` as a conservative placeholder
    pending detailed study under B&KG's framework. -/
def LevinClass.rootEntailments : LevinClass → RootEntailments
  -- §9 Putting: template provides CAUSE+BECOME; root content varies
  | .put => .minimal                -- (default)
  | .funnel => .pureManner          -- manner of channeling
  | .pour => .pureManner            -- manner of pouring
  | .coil => .pureManner            -- manner of arranging
  | .sprayLoad => .minimal          -- (default)
  -- §10 Removing
  | .remove => .minimal             -- (default)
  | .clear => .causativeResult      -- externally caused cleared state
  | .wipe => .pureManner            -- manner of surface action
  | .steal => .minimal              -- (default)
  -- §11 Sending and Carrying
  | .send => .minimal               -- (default)
  | .carry => .pureManner           -- manner of transport
  | .drive => .pureManner           -- manner via vehicle
  -- §12 Exerting Force
  | .pushPull => .pureManner        -- manner of force application
  -- §13 Change of Possession
  | .give => .fullSpec              -- (B&KG Ch.3) √HAND: manner + caused possession change
  | .contribute => .minimal         -- (default) less specified than give
  | .getObtain => .minimal          -- (default)
  | .exchange => .minimal           -- (default)
  -- §14–16
  | .learn => .minimal              -- (default)
  | .hold => .propertyConcept       -- state of holding
  | .conceal => .causativeResult    -- externally caused hidden state
  -- §17 Throwing
  | .throw => .fullSpec             -- manner of propulsion + caused arrival
  -- §18 Contact by Impact
  | .hit => .pureManner             -- (B&KG Ch.4) impact manner, no state entailed
  | .swat => .pureManner            -- like hit
  -- §19 Poking
  | .poke => .pureManner            -- manner of contact
  -- §20 Contact: Touch
  | .touch => .minimal              -- (B&KG) no structural entailments
  -- §21 Cutting
  | .cut => .fullSpec               -- (B&KG Ch.4) cutting manner + caused separation
  | .carve => .fullSpec             -- like cut
  -- §22 Combining and Attaching
  | .mix => .causativeResult        -- externally caused combined state
  | .amalgamate => .causativeResult
  -- §23 Separating
  | .separate => .causativeResult   -- externally caused separated state
  | .split => .fullSpec             -- instrument manner + caused separation
  -- §24 Coloring
  | .color => .causativeResult      -- externally caused colored state
  -- §25 Image Creation
  | .imageCreation => .fullSpec     -- etching manner + caused image
  -- §26 Creation and Transformation
  | .build => .causativeResult      -- externally caused creation
  | .grow => .pureResult            -- internally caused growth
  | .create => .causativeResult     -- externally caused creation
  | .knead => .fullSpec             -- kneading manner + caused shape change
  | .turn => .causativeResult       -- externally caused transformation
  | .performance => .pureManner     -- performance manner
  -- §27–28
  | .engender => .causativeResult   -- root entails causation
  | .calve => .pureResult           -- internally caused biological process
  -- §29 Predicative Complements
  | .appoint => .causativeResult    -- externally caused status change
  | .characterize => .minimal       -- (default)
  | .declare => .causativeResult    -- externally caused status change
  -- §30 Perception
  | .see => .minimal                -- (default)
  | .sight => .minimal              -- (default)
  -- §31 Psych-Verbs
  | .amuse => .causativeResult      -- stimulus causes psychological CoS
  | .admire => .propertyConcept     -- psychological state
  | .marvel => .propertyConcept     -- psychological state
  -- §32–34
  | .want => .propertyConcept       -- desiderative state
  | .judgment => .minimal           -- (default)
  | .assessment => .minimal         -- (default)
  -- §35 Searching
  | .search => .pureManner          -- searching manner
  -- §36 Social Interaction
  | .socialInteraction => .minimal  -- (default)
  -- §37 Communication
  | .say => .minimal                -- (default)
  | .tell => .minimal               -- (default)
  | .mannerOfSpeaking => .pureManner -- manner of speaking
  -- §38 Animal Sounds
  | .animalSound => .pureManner     -- specific sound manner
  -- §39 Ingesting
  | .eat => .causativeResult        -- caused consumption, no specific manner
  | .devour => .fullSpec            -- vigorous manner + caused consumption
  | .dine => .pureManner            -- social activity manner
  -- §40 Body
  | .bodyProcess => .minimal        -- (default)
  | .flinch => .minimal             -- (default)
  -- §41 Grooming
  | .dress => .causativeResult      -- externally caused dressed state
  -- §42 Killing
  | .murder => .causativeResult     -- (B&KG) root entails caused death
  | .poison => .fullSpec            -- (B&KG) poisoning manner + caused death (√DROWN-type)
  -- §43 Emission
  | .lightEmission => .propertyConcept  -- emitting state
  | .soundEmission => .propertyConcept
  | .substanceEmission => .propertyConcept
  -- §44 Destroy
  | .destroy => .causativeResult    -- (B&KG) root entails caused total destruction
  -- §45 Change of State
  | .break_ => .causativeResult     -- (B&KG Ch.2,5) √CRACK: externally caused CoS
  | .bend => .causativeResult       -- externally caused shape change
  | .cooking => .fullSpec           -- (B&KG) cooking manner + caused CoS
  | .otherCoS => .causativeResult   -- √MELT/√FREEZE: externally caused CoS
  | .entitySpecificCoS => .pureResult -- √BLOSSOM/√RUST: internally caused
  | .calibratableCoS => .pureResult -- internally driven scalar change
  -- §46 Lodge
  | .lodge => .minimal              -- (default)
  -- §47 Existence
  | .exist => .minimal              -- (B&KG) pure stative, no root content
  -- §48 Appearance
  | .appear => .pureResult          -- internally caused appearance
  -- §49 Body-Internal Motion
  | .bodyInternalMotion => .pureManner -- fidgeting manner
  -- §50 Assuming a Position
  | .assumePosition => .pureResult  -- internally caused position change
  -- §51 Motion
  | .inherentlyDirectedMotion => .pureResult -- internally caused directed motion
  | .leave => .pureResult           -- internally caused departure
  | .mannerOfMotion => .pureManner  -- (B&KG) √JOG: motion manner
  | .vehicleMotion => .pureManner   -- vehicle manner
  | .chase => .pureManner           -- chasing manner
  -- §52 Avoid
  | .avoid => .minimal              -- (default)
  -- §53 Lingering and Rushing
  | .linger => .pureManner          -- temporal manner
  | .rush => .pureManner            -- temporal manner
  -- §54 Measure
  | .measure => .propertyConcept    -- measurement state
  -- §55 Aspectual
  | .aspectual => .minimal          -- (default) template-level
  -- §57 Weather
  | .weather => .minimal            -- (default)

/-! ### Well-formedness verification

All canonical types satisfy the constraints, so every branch of
`rootEntailments` is well-formed (each branch returns a canonical type). -/

/-- Break roots (√CRACK) are well-formed. -/
theorem break_root_wf : (LevinClass.rootEntailments .break_).wellFormed = true := rfl

/-- Cut roots (MRC violator, fullSpec) are well-formed. -/
theorem cut_root_wf : (LevinClass.rootEntailments .cut).wellFormed = true := rfl

/-- Hit roots (pureManner) are well-formed. -/
theorem hit_root_wf : (LevinClass.rootEntailments .hit).wellFormed = true := rfl

/-- Touch roots (minimal) are well-formed. -/
theorem touch_root_wf : (LevinClass.rootEntailments .touch).wellFormed = true := rfl

/-- Give roots (√HAND, fullSpec) are well-formed. -/
theorem give_root_wf : (LevinClass.rootEntailments .give).wellFormed = true := rfl

/-- Destroy roots (causativeResult) are well-formed. -/
theorem destroy_root_wf : (LevinClass.rootEntailments .destroy).wellFormed = true := rfl

/-- Murder roots (causativeResult) are well-formed. -/
theorem murder_root_wf : (LevinClass.rootEntailments .murder).wellFormed = true := rfl

/-- Poison roots (√DROWN-type fullSpec) are well-formed. -/
theorem poison_root_wf : (LevinClass.rootEntailments .poison).wellFormed = true := rfl

/-! ### MRC violation verification -/

/-- Cut is an MRC violator (B&KG Ch. 4): manner of cutting + caused separation. -/
theorem cut_violates_MRC :
    (LevinClass.rootEntailments .cut).violatesMRC = true := rfl

/-- Cooking is an MRC violator: cooking manner + caused CoS. -/
theorem cooking_violates_MRC :
    (LevinClass.rootEntailments .cooking).violatesMRC = true := rfl

/-- Poison (√DROWN-type) is an MRC violator: poisoning manner + caused death. -/
theorem poison_violates_MRC :
    (LevinClass.rootEntailments .poison).violatesMRC = true := rfl

/-- Break respects MRC — pure result (√CRACK), no manner. -/
theorem break_respects_MRC :
    (LevinClass.rootEntailments .break_).violatesMRC = false := rfl

/-- Hit respects MRC — pure manner (√JOG-type), no result. -/
theorem hit_respects_MRC :
    (LevinClass.rootEntailments .hit).violatesMRC = false := rfl

/-! ### Cross-layer consistency

Template + root entailments predict the event-structural subset of surface
meaning components (changeOfState, causation, mannerSpec). Uses
`mc.changeOfState && mc.causation` as a proxy for `Template.hasCause`
(the accomplishment template is selected when both hold; the actual
`Template` type lives in `Theories/Semantics/Events/EventStructure.lean`
and cannot be imported here without creating a circular dependency).

B&KG's "manner" is broader than Levin's `mannerSpec`: B&KG code hit/cut
as +manner (impact/cutting action), but Levin codes this as contact+motion
(±instrument), not `mannerSpec`. The prediction holds for classes where
root manner aligns with Levin's `mannerSpec` (cooking, motion) but
diverges for contact-manner classes (hit, cut). -/

/-- Predict event-structural meaning components from template causation
    and root entailments. -/
def predictEventStructural (templateHasCause : Bool) (r : RootEntailments) :
    Bool × Bool × Bool :=
  (templateHasCause || r.result,   -- changeOfState
   templateHasCause || r.cause,    -- causation
   r.manner)                       -- mannerSpec (B&KG sense)

/-- Event-structural subset of surface meaning components. -/
def MeaningComponents.eventStructural (mc : MeaningComponents) : Bool × Bool × Bool :=
  (mc.changeOfState, mc.causation, mc.mannerSpec)

/-- Predicted event structure for a Levin class.
    Uses `mc.changeOfState && mc.causation` as a proxy for `Template.hasCause`. -/
def LevinClass.predictedEventStructural (c : LevinClass) : Bool × Bool × Bool :=
  let mc := c.meaningComponents
  predictEventStructural (mc.changeOfState && mc.causation) c.rootEntailments

/-- Break: prediction matches observation (accomplishment + √CRACK). -/
theorem break_eventStructural_consistent :
    LevinClass.predictedEventStructural .break_ =
    (LevinClass.meaningComponents .break_).eventStructural := rfl

/-- Cooking: prediction matches (accomplishment + fullSpec root). -/
theorem cooking_eventStructural_consistent :
    LevinClass.predictedEventStructural .cooking =
    (LevinClass.meaningComponents .cooking).eventStructural := rfl

/-- Manner of motion: prediction matches (activity + √JOG). -/
theorem mannerOfMotion_eventStructural_consistent :
    LevinClass.predictedEventStructural .mannerOfMotion =
    (LevinClass.meaningComponents .mannerOfMotion).eventStructural := rfl

/-- Existence: prediction matches (stative + minimal root). -/
theorem exist_eventStructural_consistent :
    LevinClass.predictedEventStructural .exist =
    (LevinClass.meaningComponents .exist).eventStructural := rfl

/-- Destroy: prediction matches (accomplishment + causativeResult). -/
theorem destroy_eventStructural_consistent :
    LevinClass.predictedEventStructural .destroy =
    (LevinClass.meaningComponents .destroy).eventStructural := rfl

/-- Touch: prediction matches (activity + minimal root). -/
theorem touch_eventStructural_consistent :
    LevinClass.predictedEventStructural .touch =
    (LevinClass.meaningComponents .touch).eventStructural := rfl

/-- Murder: prediction matches (accomplishment + causativeResult). -/
theorem murder_eventStructural_consistent :
    LevinClass.predictedEventStructural .murder =
    (LevinClass.meaningComponents .murder).eventStructural := rfl

/-- Manner of speaking: prediction matches (activity + pureManner root). -/
theorem mannerOfSpeaking_eventStructural_consistent :
    LevinClass.predictedEventStructural .mannerOfSpeaking =
    (LevinClass.meaningComponents .mannerOfSpeaking).eventStructural := rfl
