import Linglib.Core.Lexical.RootFeatures

/-!
# Levin Verb Classes and Meaning Components
@cite{levin-1993} @cite{dowty-1991} @cite{beavers-koontz-garboden-2020}

## § 1. Meaning components

Binary features that define @cite{levin-1993} verb classes, diagnosed by
diathesis alternation behavior: change of state, contact, motion, causation,
instrument specification, manner specification.

## § 2. Verb class taxonomy

The full verb class taxonomy from @cite{levin-1993} Part II: 49 top-level
classes covering the English verb lexicon. Individual verb entries in
`Fragments/` are tagged with their Levin class.

## § 3. Per-class meaning component profiles

## § 4. Predicted unaccusativity

Based on @cite{levin-hovav-1995}: unaccusativity correlates with internally
caused change of state or directed change.

## § 5. Root entailment mapping (@cite{beavers-koontz-garboden-2020})

Root structural entailments, well-formedness verification, and MRC tests.

## § 6. Root–MC bridge

Classification enums (CausationSource, ResultKind, MannerKind) naming the
systematic divergences between B&KG root features and Levin meaning
components, plus universal consistency theorems.
-/

-- ════════════════════════════════════════════════════
-- § 1. Meaning Components
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
  deriving DecidableEq, Repr

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

/-- No meaning components contributed. Identity for `fuse`. -/
def none : MeaningComponents := ⟨false, false, false, false, false, false⟩

/-- Componentwise OR. Models how a construction augments a verb's
    inherent semantics (@cite{goldberg-1995}): if either the verb or
    the construction contributes a component, the composed meaning has it.
    This is the semantic side of @cite{goldberg-1995}'s "fusion". -/
def fuse (a b : MeaningComponents) : MeaningComponents :=
  { changeOfState := a.changeOfState || b.changeOfState
  , contact := a.contact || b.contact
  , motion := a.motion || b.motion
  , causation := a.causation || b.causation
  , instrumentSpec := a.instrumentSpec || b.instrumentSpec
  , mannerSpec := a.mannerSpec || b.mannerSpec }

instance : Append MeaningComponents where
  append := fuse

theorem fuse_none_left (mc : MeaningComponents) : none.fuse mc = mc := by
  cases mc; simp [fuse, none]

theorem fuse_none_right (mc : MeaningComponents) : mc.fuse none = mc := by
  cases mc; simp [fuse, none, Bool.or_false]

theorem fuse_comm (a b : MeaningComponents) : a.fuse b = b.fuse a := by
  cases a; cases b; simp [fuse, Bool.or_comm]

end MeaningComponents

-- ════════════════════════════════════════════════════
-- § 2. Verb Class Taxonomy
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
  deriving DecidableEq, Repr

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

-- ════════════════════════════════════════════════════
-- § 3. Per-Class Meaning Component Profiles
-- ════════════════════════════════════════════════════

/-- Meaning components associated with each Levin class.

    Profiles are assigned using the diagnostic criteria from @cite{levin-1993}:
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
-- § 4. Predicted Unaccusativity
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

/-! ### Communication verb manner contrast (@cite{lu-pan-degen-2025})

The `mannerSpec` meaning component is what distinguishes MoS verbs from bridge
verbs within the Communication verb superclass (§37). This distinction drives
the manner-of-speaking island effect: verbs with `mannerSpec = true` activate
manner alternatives, foregrounding the manner QUD and backgrounding the
complement content.

See `Theories/Semantics/Focus/BackgroundedIslands.lean` for the full
derivation chain. -/

/-- MoS verbs (§37.3) specify manner; bridge verbs (§37.7) do not.
This is the lexical basis of the MoS island effect. -/
theorem communication_verb_manner_contrast :
    (LevinClass.mannerOfSpeaking).meaningComponents.mannerSpec = true ∧
    (LevinClass.say).meaningComponents.mannerSpec = false ∧
    (LevinClass.tell).meaningComponents.mannerSpec = false := ⟨rfl, rfl, rfl⟩

/-- The MoS/bridge distinction is EXCLUSIVELY about manner specification.
All three communication verb classes (say, tell, MoS) agree on all other
meaning components — they differ ONLY in `mannerSpec`. -/
theorem communication_verb_only_differ_in_manner :
    (LevinClass.mannerOfSpeaking).meaningComponents.changeOfState =
      (LevinClass.say).meaningComponents.changeOfState ∧
    (LevinClass.mannerOfSpeaking).meaningComponents.contact =
      (LevinClass.say).meaningComponents.contact ∧
    (LevinClass.mannerOfSpeaking).meaningComponents.motion =
      (LevinClass.say).meaningComponents.motion ∧
    (LevinClass.mannerOfSpeaking).meaningComponents.causation =
      (LevinClass.say).meaningComponents.causation ∧
    (LevinClass.mannerOfSpeaking).meaningComponents.instrumentSpec =
      (LevinClass.say).meaningComponents.instrumentSpec :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 5. Root Entailment Mapping (@cite{beavers-koontz-garboden-2020})
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

-- ════════════════════════════════════════════════════
-- § 6. Root–MC Bridge (@cite{beavers-koontz-garboden-2020})
-- ════════════════════════════════════════════════════

/-! ### Root–MC correspondence (2026 consensus)

The 2026 consensus in lexical semantics (@cite{beavers-koontz-garboden-2020},
@cite{rappaport-hovav-levin-2024}) treats root entailments as primary:
verb behavior at the Levin diagnostic level is determined by root content
plus semantic field membership plus template structure.

But the B&KG root features and the Levin meaning components are NOT
isomorphic — they conceptualize different levels of granularity:

| B&KG concept | Levin concept | Relationship |
|---|---|---|
| `result` | `changeOfState` | B&KG broader: includes location/possession change |
| `manner` | `mannerSpec` ∨ `instrumentSpec` | B&KG broader: includes contact-manner (hit) |
| `cause` | `causation` | Distinct: root-level vs event-level causation |

The three `*Kind` enums below name the specific cases where the two
frameworks diverge, making the divergences grep-able and testable. -/

/-- Where a verb class's event-level causation originates.

    B&KG's root-level `cause` and Levin's event-level `causation` are
    distinct concepts (@cite{beavers-koontz-garboden-2020} Ch. 5;
    @cite{levin-1993} pp. 9–10):

    - **rootExternal**: root entails detachable external causation.
      *break*: √CRACK entails cause, and the inchoative *the vase broke*
      is available. `re.cause = true, mc.causation = true`.

    - **rootNonDetachable**: root entails causation but it can't be
      syntactically removed — no inchoative variant. *eat*: √EAT entails
      the eater causes consumption, but **the cake ate* is bad.
      `re.cause = true, mc.causation = false`.

    - **template**: the event structure template provides vCAUSE but the
      root itself doesn't entail it. *put*: √PUT is minimal (no structural
      entailments), but the putting frame is causative.
      `re.cause = false, mc.causation = true`.

    - **none**: no causation component. *hit*: neither root nor template
      contributes causation. `re.cause = false, mc.causation = false`. -/
inductive CausationSource where
  | rootExternal
  | rootNonDetachable
  | template
  | none
  deriving DecidableEq, Repr

/-- Derive the causation source from root entailments and meaning components.
    This is a derived classification: it follows from the relationship between
    B&KG's root `cause` and Levin's `causation`. -/
def LevinClass.causationSource (c : LevinClass) : CausationSource :=
  let re := c.rootEntailments
  let mc := c.meaningComponents
  if re.cause then
    if mc.causation then .rootExternal else .rootNonDetachable
  else
    if mc.causation then .template else .none

/-- What kind of result the root entails (refines B&KG `result`).

    Levin's `changeOfState` corresponds to `stateChange` only —
    change of location (throw, arrive) and change of possession (give)
    have `result = true` in B&KG but `changeOfState = false` in Levin. -/
inductive ResultKind where
  | stateChange        -- internal property change (break, destroy, melt)
  | locationChange     -- spatial change (throw, arrive, leave)
  | possessionChange   -- ownership change (give)
  | none               -- no result entailed (hit, run, exist)
  deriving DecidableEq, Repr

/-- Derive result kind from root entailments and meaning components. -/
def LevinClass.resultKind (c : LevinClass) : ResultKind :=
  let re := c.rootEntailments
  let mc := c.meaningComponents
  if !re.result then .none
  else if mc.changeOfState then .stateChange
  else if mc.motion then .locationChange
  else .possessionChange

/-- How root manner maps to Levin's MC spec features.

    B&KG's `manner` subsumes three Levin-level distinctions:
    - **mannerSpec**: how the action proceeds (cooking, running)
    - **instrumentSpec**: what tool is used (cutting, poking)
    - **unspecified**: manner verb without a Levin spec flag (hit, push)

    The last case reflects a genuine conceptual gap: B&KG codes any
    action-specifying root as +manner, while Levin reserves `mannerSpec`
    and `instrumentSpec` for manner specifications with specific
    diagnostic consequences (blocking alternations, etc.). -/
inductive MannerKind where
  | mannerSpec       -- manner of action (cooking, motion verbs)
  | instrumentSpec   -- instrument specification (cut, poke verbs)
  | unspecified      -- B&KG +manner but no Levin spec flag (hit, push)
  | none             -- no manner in root (break, exist)
  deriving DecidableEq, Repr

/-- Derive manner kind from root entailments and meaning components. -/
def LevinClass.mannerKind (c : LevinClass) : MannerKind :=
  let re := c.rootEntailments
  let mc := c.meaningComponents
  if !re.manner then .none
  else if mc.instrumentSpec then .instrumentSpec
  else if mc.mannerSpec then .mannerSpec
  else .unspecified

/-! #### Causation source verification -/

theorem break_causation_rootExternal :
    LevinClass.causationSource .break_ = .rootExternal := rfl
theorem destroy_causation_rootExternal :
    LevinClass.causationSource .destroy = .rootExternal := rfl
theorem murder_causation_rootExternal :
    LevinClass.causationSource .murder = .rootExternal := rfl

/-- Eat: root cause is non-detachable — no inchoative **the cake ate*. -/
theorem eat_causation_rootNonDetachable :
    LevinClass.causationSource .eat = .rootNonDetachable := rfl
theorem devour_causation_rootNonDetachable :
    LevinClass.causationSource .devour = .rootNonDetachable := rfl

/-- Put: template provides causation; root is minimal. -/
theorem put_causation_template :
    LevinClass.causationSource .put = .template := rfl
theorem send_causation_template :
    LevinClass.causationSource .send = .template := rfl
/-- Grow: root is pureResult (internally caused); template adds vCAUSE
    for the transitive *the farmer grew tomatoes*. -/
theorem grow_causation_template :
    LevinClass.causationSource .grow = .template := rfl

theorem hit_causation_none :
    LevinClass.causationSource .hit = .none := rfl
theorem mannerOfMotion_causation_none :
    LevinClass.causationSource .mannerOfMotion = .none := rfl

/-! #### Result kind verification -/

theorem break_result_stateChange :
    LevinClass.resultKind .break_ = .stateChange := rfl
theorem destroy_result_stateChange :
    LevinClass.resultKind .destroy = .stateChange := rfl

/-- Throw: root entails result (ball arrives), but it's a location
    change, not an internal state change → `changeOfState = false`. -/
theorem throw_result_locationChange :
    LevinClass.resultKind .throw = .locationChange := rfl
theorem inherentlyDirectedMotion_result_locationChange :
    LevinClass.resultKind .inherentlyDirectedMotion = .locationChange := rfl
theorem leave_result_locationChange :
    LevinClass.resultKind .leave = .locationChange := rfl

/-- Give: root entails result (possession transfers), but it's a
    possession change, not an internal state change. -/
theorem give_result_possessionChange :
    LevinClass.resultKind .give = .possessionChange := rfl

theorem hit_result_none :
    LevinClass.resultKind .hit = .none := rfl

/-! #### Manner kind verification -/

theorem cooking_manner_mannerSpec :
    LevinClass.mannerKind .cooking = .mannerSpec := rfl
theorem mannerOfMotion_manner_mannerSpec :
    LevinClass.mannerKind .mannerOfMotion = .mannerSpec := rfl

/-- Cut: B&KG +manner (cutting action), Levin codes as instrumentSpec. -/
theorem cut_manner_instrumentSpec :
    LevinClass.mannerKind .cut = .instrumentSpec := rfl
theorem poke_manner_instrumentSpec :
    LevinClass.mannerKind .poke = .instrumentSpec := rfl

/-- Hit: B&KG +manner (impact action), but Levin codes the manner as
    contact + motion in the semantic field, not as a spec flag. -/
theorem hit_manner_unspecified :
    LevinClass.mannerKind .hit = .unspecified := rfl
/-- PushPull: B&KG +manner, but Levin gives no spec flag. -/
theorem pushPull_manner_unspecified :
    LevinClass.mannerKind .pushPull = .unspecified := rfl

theorem break_manner_none :
    LevinClass.mannerKind .break_ = .none := rfl

-- ============================================================================
-- Verb of Creation (VOC) classification
-- ============================================================================

/-- Whether a Levin class denotes creation of the object referent.

@cite{davies-dubinsky-2003}: verbs of creation (VOCs) produce their
direct object as a result of the event — the object comes into existence
through the action. In English, VOCs can ameliorate definite island
effects via N/D-incorporation, neutralizing the phasehood of the object
DP (@cite{shen-huang-2026}).

Levin classes 25 (image creation), 26.1 (build), 26.2 (grow), 26.4
(create), 26.7 (performance), and related classes are VOCs. Perception
verbs (30), communication verbs (37), and consumption verbs (eat) are
non-VOCs — the object exists independently of the event. -/
def LevinClass.isVerbOfCreation : LevinClass → Bool
  | .imageCreation => true   -- 25: draw, etch, engrave
  | .build         => true   -- 26.1: build, assemble, construct
  | .grow          => true   -- 26.2: grow, cultivate
  | .create        => true   -- 26.4: create, design, invent
  | .knead         => true   -- 26.5: knead, mold, shape
  | .performance   => true   -- 26.7: perform, play, sing
  | .cooking       => true   -- 45.3: cook, bake, fry (object created)
  | _              => false

/-- Build verbs are VOCs. -/
theorem build_is_voc : LevinClass.isVerbOfCreation .build = true := rfl

/-- Perception verbs are not VOCs. -/
theorem see_is_not_voc : LevinClass.isVerbOfCreation .see = false := rfl

/-- Core creation classes (build, create, grow, knead, imageCreation)
    all have causativeResult root entailments: the object comes into
    existence as a causal result of the agent's action. -/
theorem build_class_causative :
    LevinClass.build.rootEntailments = .causativeResult := rfl
theorem create_class_causative :
    LevinClass.create.rootEntailments = .causativeResult := rfl

/-! ### Root-structural MC contribution

The conservative structural derivation from root entailments to meaning
components. Only sets features that the root structure UNAMBIGUOUSLY
contributes — other features require class-level information. -/

/-- Root structural contribution to meaning components.
    Maps result → changeOfState and manner → mannerSpec. These are the
    two correspondences where the MAJORITY of classes agree (modulo the
    documented divergences above). Causation and semantic-field features
    (contact, motion, instrumentSpec) are omitted — they require
    class-level information. -/
def RootEntailments.structuralMC (re : RootEntailments) : MeaningComponents :=
  { changeOfState := re.result
  , contact := false
  , motion := false
  , causation := false
  , instrumentSpec := false
  , mannerSpec := re.manner }

/-! ### Universal consistency theorems

These hold for ALL 78 LevinClass constructors and are proved by
exhaustive case analysis. They capture the reliable structural
correspondences between B&KG and Levin. -/

/-- Levin spec implies B&KG manner: if Levin marks a class as
    manner-specified or instrument-specified, B&KG codes the root as
    +manner. The reverse does NOT hold (hit, pushPull are +manner
    in B&KG but lack MC spec flags). -/
def LevinClass.specImpliesManner (c : LevinClass) : Bool :=
  !(c.meaningComponents.mannerSpec || c.meaningComponents.instrumentSpec) ||
  c.rootEntailments.manner

theorem levin_spec_implies_bkg_manner :
    ∀ c : LevinClass, c.specImpliesManner = true := by
  intro c; cases c <;> decide

/-- CausativeResult roots always have changeOfState: every class whose
    root entails externally caused result (causativeResult) has CoS in
    its meaning components. This is the strongest result↔CoS
    correspondence — it holds without exception. -/
def LevinClass.causativeResultImpliesCos (c : LevinClass) : Bool :=
  !(c.rootEntailments == .causativeResult) || c.meaningComponents.changeOfState

theorem causativeResult_always_cos :
    ∀ c : LevinClass, c.causativeResultImpliesCos = true := by
  intro c; cases c <;> decide

/-- Root cause implies either event causation or non-detachable causation:
    if B&KG says the root entails cause, then Levin's MC has causation = true
    OR the class is eat/devour-type (non-detachable). Put differently:
    root cause = false whenever MC causation = false AND the root is not
    a non-detachable causer. -/
def LevinClass.causeImpliesCausationOrNonDetach (c : LevinClass) : Bool :=
  !c.rootEntailments.cause || c.meaningComponents.causation ||
  c.causationSource == .rootNonDetachable

theorem root_cause_accounted_for :
    ∀ c : LevinClass, c.causeImpliesCausationOrNonDetach = true := by
  intro c; cases c <;> decide
