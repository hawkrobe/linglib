/-!
# Quality Dimensions for Verb Root Content

Empirically attested feature dimensions for characterizing the idiosyncratic
("root") content of verb meanings. Verbs within a single class (e.g., Levin's
45.1 Break Verbs) share event structure but may differ along these dimensions
in ways that affect selectional restrictions, figurative extensions, and
cross-linguistic translation equivalence (Spalek & McNally, forthcoming).

## Two-level architecture

**Level 1 — Levin meaning components** (§ 1). Binary features that define verb
classes, diagnosed by diathesis alternation behavior. From Levin (1993:5–10):
the four verbs *break*, *cut*, *hit*, and *touch* are distinguished by the
presence or absence of change of state, contact, motion, and causation.

**Level 2 — Root-specific features** (§ 3). Range-valued dimensions capturing
within-class variation in root content. A root's "position" along each
dimension is not a point but a **range** of acceptable values (§ 2), reflecting
the fact that verbs are compatible with a range of event types.

## Levin class taxonomy

The full verb class taxonomy from Levin (1993) Part II is encoded in § 4.
This provides a standardized reference for verb classification; individual
verb entries in `Fragments/` are tagged with their Levin class.

## Extensibility

Adding a new dimension: define a value type, add a `Range` field to
`RootProfile` (defaulting to `none`). All existing entries compile unchanged.
Adding a value to an existing dimension: breaking change — forces reviewing
all entries that constrain that dimension. This is by design.

## References

- Levin, B. (1993). *English Verb Classes and Alternations*. Chicago.
  — Meaning components: pp. 5–10 (break/cut/hit/touch analysis).
  — Class taxonomy: Part II, §§ 9–57.
- Hale, K. & Keyser, S.J. (1987). A view from the middle. Lexicon Project
  Working Papers 10, MIT.
  — "separation in material integrity" as the core of cut/break meaning.
- Talmy, L. (1988). Force dynamics in language and cognition.
  *Cognitive Science* 12, 49–100.
  — Force magnitude and direction as primitives of event structure.
- Talmy, L. (2000). *Toward a Cognitive Semantics*, Vol. I. MIT Press.
  — Force vectors with directional parameters.
- Dowty, D. (1991). Thematic proto-roles and argument selection.
  *Language* 67(3), 547–619.
  — Proto-Agent P1 (volitional involvement), P2 (sentience/perception).
- Fillmore, C. & Atkins, B.T.S. (2000). Describing polysemy: The case of
  'crawl'. In *Polysemy*, ed. Y. Ravin & C. Leacock, 91–110. OUP.
  — Participant physical properties constrain verb applicability.
- Spalek, A.A. & McNally, L. (forthcoming). The anatomy of a verb: *Tear*,
  *rasgar*, and lexical equivalence. *Linguistics in Contrast*.
  — Patient robustness, force direction, agent control as root dimensions.
- Beavers, J. & Koontz-Garboden, A. (2020). *The Roots of Verbal Meaning*.
  OUP.
  — Change-of-state roots vs. property concept roots.
-/

-- ════════════════════════════════════════════════════
-- § 1. Levin (1993) Meaning Components
-- ════════════════════════════════════════════════════

/-- Binary meaning components that define Levin (1993) verb classes.

    Diagnosed by participation in diathesis alternations (pp. 5–10):
    - `changeOfState`: middle alternation, causative/inchoative alternation
    - `contact`: body-part possessor ascension alternation
    - `motion`: conative alternation (with contact)
    - `causation`: causative/inchoative alternation (with changeOfState)

    The four canonical classes from Levin's Introduction:
    - *break* = [+CoS, −contact, −motion, +causation]
    - *cut*   = [+CoS, +contact, +motion, +causation]
    - *hit*   = [−CoS, +contact, +motion, −causation]
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

    Talmy (2000, Ch. 7): force vectors have directional parameters.
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

    Grounded in Levin's (1993) class descriptions and Hale & Keyser's
    (1987) notion of "separation in material integrity":
    - 45.1 Break: loss of material integrity (break, crack, shatter, tear)
    - 45.2 Bend: change in shape without loss of integrity
    - 44 Destroy: total destruction (no specific resulting state)
    - 21 Cut: separation via instrument contact
    Refined by Beavers & Koontz-Garboden (2020) on CoS root types. -/
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

    Captures the idiosyncratic conceptual content that distinguishes
    verbs within a single Levin class. Each dimension is a `Range`
    of acceptable values; `none` means the root says nothing about
    that dimension (unconstrained).

    Together with `MeaningComponents` (which defines the class) and
    `LevinClass` (which identifies the class), this gives a three-level
    characterization of a verb's semantic content:
    1. Class-defining meaning components (binary, from alternations)
    2. Class membership (Levin taxonomy)
    3. Root-specific features (ranges, from detailed lexical analysis) -/
structure RootProfile where
  /-- Force magnitude: Talmy (1988). -/
  forceMag : Range ForceLevel := none
  /-- Force directionality: Talmy (2000), Spalek & McNally. -/
  forceDir : Range ForceDirection := none
  /-- Patient material robustness: Spalek & McNally. -/
  patientRob : Range Robustness := none
  /-- Type of physical change: Levin (1993), Beavers & Koontz-Garboden (2020). -/
  resultType : Range ResultType := none
  /-- Agent volitionality: Dowty (1991) P1, Ausensi (2021). -/
  agentVolition : Range Volitionality := none
  /-- Agent control: Dowty (1991) P2, Spalek & McNally. -/
  agentControl : Range AgentControl := none
  deriving BEq, Repr, Inhabited

-- ════════════════════════════════════════════════════
-- § 4. Levin (1993) Verb Class Taxonomy
-- ════════════════════════════════════════════════════

/-- Verb class taxonomy from Levin (1993) Part II.

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

/-- Section number in Levin (1993) for each class. -/
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
    Populated for classes with well-known component profiles. -/
def LevinClass.meaningComponents : LevinClass → Option MeaningComponents
  | .break_ => some .break_
  | .cut => some .cut
  | .hit => some .hit
  | .touch => some .touch
  | .destroy => some .destroy
  | .bend => some .bend
  | .carve => some { changeOfState := true, contact := true, motion := true,
                     causation := true, instrumentSpec := true }
  | _ => none

-- ════════════════════════════════════════════════════
-- § 5. Derived Properties
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
