/-!
# Verb Classification Enums

All verb classification types in one place, with pure classification data
(meaning components, unaccusativity prediction, VOC status). Semantic
interpretations (`.toSemantics`, `.rootEntailments`, etc.) that depend on
theory infrastructure are in the corresponding theory files.

| Type | Theory file | Domain |
|------|-------------|--------|
| `LevinClass` | `Theories/Semantics/Lexical/Verb/LevinTheory.lean` | Diathesis-based class |
| `VendlerClass` | `Theories/Semantics/Tense/Aspect/LexicalAspect.lean` | Situation type (aspect) |
| `Causative` | `Theories/Semantics/Causation/Interpretation.lean` | Force-dynamic mechanism |
| `Implicative` | `Theories/Semantics/Causation/Implicative.lean` | Complement entailment polarity |
| `Preferential` | `Theories/Semantics/Attitudes/BuilderProperties.lean` | Preferential predicate strategy |
| `Attitude` | (composed from Doxastic + Preferential) | Attitude verb type |

Supporting types: `Veridicality`, `AttitudeValence`, `Telicity`, `Duration`,
`Dynamicity`, `AspectualProfile`. All zero-import.
-/

set_option autoImplicit false

namespace Core.Verbs

-- ════════════════════════════════════════════════════
-- § LevinClass: diathesis-based verb taxonomy
-- ════════════════════════════════════════════════════

/-- Verb class taxonomy from @cite{levin-1993} Part II.

    Section numbers follow the book. Class names are Levin's labels.
    This provides a standardized, widely-cited reference for verb
    classification; 49 top-level classes covering the English verb lexicon.

    Not all subclasses are listed here — the taxonomy is intentionally
    at the top-level class grain, with subclass distinctions handled by
    `MeaningComponents` and `RootProfile` (in Theory layer). -/
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
-- § MeaningComponents: Levin class feature profiles
-- ════════════════════════════════════════════════════

/-- Binary meaning components that define @cite{levin-1993} verb classes.

    These describe **surface** verb behavior, not root-level entailments.
    @cite{beavers-koontz-garboden-2020} argue that surface CoS and causation
    can come from either the template or the root; see `RootEntailments`
    (in Theory layer) for the root-level decomposition.

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
  changeOfState : Bool
  contact : Bool
  motion : Bool
  causation : Bool
  instrumentSpec : Bool := false
  mannerSpec : Bool := false
  deriving DecidableEq, Repr

namespace MeaningComponents

def break_ : MeaningComponents := ⟨true, false, false, true, false, false⟩
def cut : MeaningComponents := ⟨true, true, true, true, true, false⟩
def hit : MeaningComponents := ⟨false, true, true, false, false, false⟩
def touch : MeaningComponents := ⟨false, true, false, false, false, false⟩
def destroy : MeaningComponents := ⟨true, false, false, true, false, false⟩
def bend : MeaningComponents := ⟨true, false, false, true, false, false⟩
def none : MeaningComponents := ⟨false, false, false, false, false, false⟩

/-- Componentwise OR. Models how a construction augments a verb's
    inherent semantics (@cite{goldberg-1995}). -/
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

/-- Meaning components associated with each Levin class.

    Profiles are assigned using the diagnostic criteria from @cite{levin-1993}:
    - `changeOfState`: middle alternation (*the glass broke* / *this bread cuts easily*)
    - `contact`: body-part possessor ascension (*I hit him on the arm* / *I hit his arm*)
    - `motion`: conative alternation requires motion + contact (*I cut at the bread*)
    - `causation`: causative/inchoative alternation (*she broke the vase* / *the vase broke*)
    - `instrumentSpec`: verb specifies instrument/means (cut vs. break; p. 157)
    - `mannerSpec`: verb specifies manner of action (cooking, manner of motion; p. 244) -/
def LevinClass.meaningComponents : LevinClass → MeaningComponents
  | .put => ⟨false, false, true, true, false, false⟩
  | .funnel => ⟨false, false, true, true, false, true⟩
  | .pour => ⟨false, false, true, true, false, true⟩
  | .coil => ⟨false, false, true, true, false, true⟩
  | .sprayLoad => ⟨false, false, true, true, false, false⟩
  | .remove => ⟨false, false, true, true, false, false⟩
  | .clear => ⟨true, false, true, true, false, false⟩
  | .wipe => ⟨true, true, true, true, false, true⟩
  | .steal => ⟨false, false, false, true, false, false⟩
  | .send => ⟨false, false, true, true, false, false⟩
  | .carry => ⟨false, true, true, true, false, true⟩
  | .drive => ⟨false, false, true, true, false, true⟩
  | .pushPull => ⟨false, true, true, false, false, false⟩
  | .give => ⟨false, false, false, true, false, false⟩
  | .contribute => ⟨false, false, false, true, false, false⟩
  | .getObtain => ⟨false, false, false, false, false, false⟩
  | .exchange => ⟨false, false, false, false, false, false⟩
  | .learn => ⟨false, false, false, false, false, false⟩
  | .hold => ⟨false, true, false, false, false, false⟩
  | .conceal => ⟨true, false, false, true, false, false⟩
  | .throw => ⟨false, true, true, true, false, false⟩
  | .hit => .hit
  | .swat => ⟨false, true, true, false, false, false⟩
  | .poke => ⟨false, true, true, false, true, false⟩
  | .touch => .touch
  | .cut => .cut
  | .carve => ⟨true, true, true, true, true, false⟩
  | .mix => ⟨true, false, false, true, false, false⟩
  | .amalgamate => ⟨true, false, false, true, false, false⟩
  | .separate => ⟨true, false, false, true, false, false⟩
  | .split => ⟨true, true, false, true, true, false⟩
  | .color => ⟨true, true, false, true, false, false⟩
  | .imageCreation => ⟨true, true, false, true, true, false⟩
  | .build => ⟨true, false, false, true, false, false⟩
  | .grow => ⟨true, false, false, true, false, false⟩
  | .create => ⟨true, false, false, true, false, false⟩
  | .knead => ⟨true, true, false, true, false, true⟩
  | .turn => ⟨true, false, false, true, false, false⟩
  | .performance => ⟨false, false, false, false, false, true⟩
  | .engender => ⟨true, false, false, true, false, false⟩
  | .calve => ⟨true, false, false, false, false, false⟩
  | .appoint => ⟨true, false, false, true, false, false⟩
  | .characterize => ⟨false, false, false, false, false, false⟩
  | .declare => ⟨true, false, false, true, false, false⟩
  | .see => ⟨false, false, false, false, false, false⟩
  | .sight => ⟨false, false, false, false, false, false⟩
  | .amuse => ⟨true, false, false, true, false, false⟩
  | .admire => ⟨false, false, false, false, false, false⟩
  | .marvel => ⟨false, false, false, false, false, false⟩
  | .want => ⟨false, false, false, false, false, false⟩
  | .judgment => ⟨false, false, false, false, false, false⟩
  | .assessment => ⟨false, false, false, false, false, false⟩
  | .search => ⟨false, false, true, false, false, false⟩
  | .socialInteraction => ⟨false, false, false, false, false, false⟩
  | .say => ⟨false, false, false, false, false, false⟩
  | .tell => ⟨false, false, false, false, false, false⟩
  | .mannerOfSpeaking => ⟨false, false, false, false, false, true⟩
  | .animalSound => ⟨false, false, false, false, false, true⟩
  | .eat => ⟨true, true, false, false, false, false⟩
  | .devour => ⟨true, true, false, false, false, true⟩
  | .dine => ⟨false, false, false, false, false, true⟩
  | .bodyProcess => ⟨false, false, false, false, false, false⟩
  | .flinch => ⟨false, false, true, false, false, false⟩
  | .dress => ⟨true, true, false, true, false, false⟩
  | .murder => ⟨true, false, false, true, false, false⟩
  | .poison => ⟨true, false, false, true, true, false⟩
  | .lightEmission => ⟨false, false, false, false, false, false⟩
  | .soundEmission => ⟨false, false, false, false, false, false⟩
  | .substanceEmission => ⟨false, false, false, false, false, false⟩
  | .destroy => .destroy
  | .break_ => .break_
  | .bend => .bend
  | .cooking => ⟨true, false, false, true, false, true⟩
  | .otherCoS => ⟨true, false, false, true, false, false⟩
  | .entitySpecificCoS => ⟨true, false, false, true, false, false⟩
  | .calibratableCoS => ⟨true, false, false, true, false, false⟩
  | .lodge => ⟨false, false, true, false, false, false⟩
  | .exist => ⟨false, false, false, false, false, false⟩
  | .appear => ⟨true, false, false, false, false, false⟩
  | .bodyInternalMotion => ⟨false, false, true, false, false, false⟩
  | .assumePosition => ⟨true, false, true, false, false, false⟩
  | .inherentlyDirectedMotion => ⟨false, false, true, false, false, false⟩
  | .leave => ⟨false, false, true, false, false, false⟩
  | .mannerOfMotion => ⟨false, false, true, false, false, true⟩
  | .vehicleMotion => ⟨false, false, true, false, false, true⟩
  | .chase => ⟨false, false, true, false, false, false⟩
  | .avoid => ⟨false, false, false, false, false, false⟩
  | .linger => ⟨false, false, false, false, false, true⟩
  | .rush => ⟨false, false, true, false, false, true⟩
  | .measure => ⟨false, false, false, false, false, false⟩
  | .aspectual => ⟨true, false, false, true, false, false⟩
  | .weather => ⟨false, false, false, false, false, false⟩

/-- Predicted unaccusativity from Levin class membership.

    Based on @cite{levin-hovav-1995}: unaccusativity correlates with internally
    caused change of state or directed change, while unergativity correlates
    with agentive activity. -/
def LevinClass.PredictsUnaccusative : LevinClass → Prop
  | .break_ | .bend | .cooking | .otherCoS
  | .entitySpecificCoS | .calibratableCoS => True
  | .destroy => True
  | .mix | .amalgamate => True
  | .separate | .split => True
  | .appear => True
  | .exist => True
  | .calve => True
  | .inherentlyDirectedMotion => True
  | .leave => True
  | .lightEmission | .soundEmission | .substanceEmission => True
  | .weather => True
  | _ => False

instance : DecidablePred LevinClass.PredictsUnaccusative := fun c => by
  cases c <;> unfold LevinClass.PredictsUnaccusative <;> infer_instance

/-- Whether a Levin class denotes creation of the object referent.
    @cite{davies-dubinsky-2003}: VOCs produce their direct object
    as a result of the event. -/
def LevinClass.isVerbOfCreation : LevinClass → Bool
  | .imageCreation => true
  | .build         => true
  | .grow          => true
  | .create        => true
  | .knead         => true
  | .performance   => true
  | .cooking       => true
  | _              => false

-- ════════════════════════════════════════════════════
-- § Supporting enums
-- ════════════════════════════════════════════════════

/-- A doxastic predicate is veridical if believing/knowing p entails p is true.

    Veridical: know, realize, discover
    Non-veridical: believe, think, suspect -/
inductive Veridicality where
  | veridical      -- x V p ⊢ p (knowledge, factives)
  | nonVeridical   -- x V p ⊬ p (belief, opinion)
  deriving DecidableEq, Repr

/-- Evaluative valence of a preferential predicate.

    - **Positive**: Expresses desire for the proposition (hope, wish, expect)
    - **Negative**: Expresses aversion to the proposition (fear, worry, dread)

    This distinction is crucial for:
    1. TSP distribution (positive have TSP, negative don't)
    2. Interpretive asymmetry in "V whether" constructions -/
inductive AttitudeValence where
  | positive   -- hope, wish, expect, look_forward_to
  | negative   -- fear, worry, dread
  deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════
-- § Causative: force-dynamic mechanism
-- ════════════════════════════════════════════════════

/-- How a causative verb's semantics is built from causal model infrastructure.

    Names a **force-dynamic mechanism**, not a causal-model property.
    `toSemantics` (in `Causation/Interpretation.lean`) maps each variant to
    its truth-condition function; properties like sufficiency/necessity are
    derived via theorems.

    - `cause`: Counterfactual dependence — removing cause blocks effect.
    - `make`: Direct sufficient guarantee — adding cause ensures effect.
    - `force`: Coercive sufficiency — overcome resistance, no alternatives.
    - `enable`: Permissive — remove barrier so effect can occur.
    - `prevent`: Blocking — add barrier so effect cannot occur. -/
inductive Causative where
  /-- Counterfactual dependence: removing cause → no effect.
      Semantic function: `causeSem`. -/
  | cause
  /-- Direct sufficient guarantee: adding cause → effect.
      Semantic function: `causallySufficient`. -/
  | make
  /-- Coercive sufficiency: overcome resistance, no alternatives.
      Same truth conditions as `make`; distinguished by `isCoercive`. -/
  | force
  /-- Permissive: remove barrier so effect can occur.
      Same truth conditions as `make`; distinguished by `isPermissive`. -/
  | enable
  /-- Blocking: add barrier so effect cannot occur.
      Semantic function: `preventSem` (dual of `causeSem`). -/
  | prevent
  deriving DecidableEq, Repr

/-- Does this variant assert causal sufficiency (N&L Def 23)?

    DERIVED: true for variants whose `toSemantics` maps to `causallySufficient`. -/
def Causative.assertsSufficiency : Causative → Bool
  | .make | .force | .enable => true
  | .cause | .prevent => false

/-- Does this variant assert causal necessity (N&L Def 24)?

    DERIVED: true only for `.cause`, whose `toSemantics` maps to `causeSem`. -/
def Causative.assertsNecessity : Causative → Bool
  | .cause => true
  | _ => false

/-- Does this variant encode coercion (overcoming resistance)?

    Force-dynamic property: `.force` encodes that the causer overcame
    the causee's resistance. -/
def Causative.isCoercive : Causative → Bool
  | .force => true
  | _ => false

/-- Does this variant encode permissivity (barrier removal)?

    Force-dynamic property: `.enable` encodes that the causer removed
    a barrier, allowing the effect to occur naturally. -/
def Causative.isPermissive : Causative → Bool
  | .enable => true
  | _ => false

-- ════════════════════════════════════════════════════
-- § Implicative: complement entailment polarity
-- ════════════════════════════════════════════════════

/-- Polarity for implicative verbs.

    Positive implicatives (*manage*, *remember*) entail the complement on success.
    Negative implicatives (*fail*, *forget*) entail the complement does NOT hold
    on success.

    Note: `Implicative` and `Causative` are structurally different
    (@cite{nadathur-2024}): causatives directly predicate causation (make/cause →
    sufficiency/necessity), while implicatives predicate a prerequisite whose
    causal relationship to the complement is only presupposed. -/
inductive Implicative where
  | positive   -- manage, remember: success → complement true
  | negative   -- fail, forget: success → complement NOT true
  deriving DecidableEq, Repr

/-- Whether the verb entails the complement (positive) or its negation (negative). -/
def Implicative.entailsComplement : Implicative → Bool
  | .positive => true
  | .negative => false

-- ════════════════════════════════════════════════════
-- § Preferential: attitude predicate strategy
-- ════════════════════════════════════════════════════

/-- Which Montague predicate strategy this preferential verb uses.

    Links the Fragment entry to the compositional semantics in
    `Semantics.Attitudes.Preferential`. Properties like C-distributivity
    are DERIVED from this tag via theorems, not stipulated.

    - `degreeComparison`: Uses `mkDegreeComparisonPredicate` → C-distributive
    - `uncertaintyBased`: Uses `worry` constructor → NOT C-distributive
    - `relevanceBased`: Uses `qidai` constructor → NOT C-distributive -/
inductive Preferential where
  /-- Degree comparison semantics: ⟦x V Q⟧ = ∃p ∈ Q. μ(x,p) > θ. C-distributive. -/
  | degreeComparison (valence : AttitudeValence)
  /-- Uncertainty-based semantics (worry): involves global uncertainty. NOT C-distributive. -/
  | uncertaintyBased
  /-- Relevance-based semantics (qidai, care): involves resolution. NOT C-distributive. -/
  | relevanceBased (valence : AttitudeValence)
  deriving DecidableEq, Repr

/-- Get the valence from the preferential classification. -/
def Preferential.valence : Preferential → AttitudeValence
  | .degreeComparison v => v
  | .uncertaintyBased => .negative  -- worry is negative
  | .relevanceBased v => v

-- ════════════════════════════════════════════════════
-- § Attitude: unified attitude verb type
-- ════════════════════════════════════════════════════

/-- Unified classification for all attitude verbs, covering both doxastic
    (believe, know) and preferential (hope, fear) attitudes.

    This is the **minimal basis** from which theoretical properties are derived:
    1. **Doxastic attitudes**: Use accessibility relations (Hintikka semantics)
    2. **Preferential attitudes**: Use degree/uncertainty semantics (Villalta)

    Derived properties (in Theory layer):
    - C-distributivity: from Preferential structure
    - NVP class: from C-distributivity + valence
    - Parasitic on belief: from being preferential
    - Presupposition projection: from veridicality + attitude type -/
inductive Attitude where
  /-- Doxastic attitude (believe, know, think) with accessibility semantics -/
  | doxastic (veridicality : Veridicality)
  /-- Preferential attitude (hope, fear, worry) with degree/uncertainty semantics -/
  | preferential (kind : Preferential)
  deriving DecidableEq, Repr

/-- Get veridicality from an attitude classification. -/
def Attitude.veridicality : Attitude → Veridicality
  | .doxastic v => v
  | .preferential _ => .nonVeridical  -- Preferential attitudes are non-veridical

/-- Is this a doxastic attitude? -/
def Attitude.isDoxastic : Attitude → Bool
  | .doxastic _ => true
  | .preferential _ => false

/-- Is this a preferential attitude? -/
def Attitude.isPreferential : Attitude → Bool
  | .doxastic _ => false
  | .preferential _ => true

/-- Get the preferential classification if this is a preferential attitude. -/
def Attitude.getPreferential : Attitude → Option Preferential
  | .doxastic _ => none
  | .preferential b => some b

/-- Get valence for preferential attitudes. -/
def Attitude.valence : Attitude → Option AttitudeValence
  | .doxastic _ => none
  | .preferential b => some b.valence

/-- Can this attitude verb take a circumstantial modal base?
    @cite{klecha-2016}: doxastic attitudes (think, believe) take only DOX;
    preferential attitudes (hope, want, pray) can also take CIR, which
    permits future temporal orientation. This is the source of the
    Upper Limit Constraint: DOX-only verbs block future readings. -/
def Attitude.PermitsCircumstantial : Attitude → Prop
  | .doxastic _ => False
  | .preferential _ => True

instance : DecidablePred Attitude.PermitsCircumstantial := fun a => by
  cases a <;> unfold Attitude.PermitsCircumstantial <;> infer_instance

-- ════════════════════════════════════════════════════
-- § Vendler classification: situation types
-- ════════════════════════════════════════════════════

/-- Telicity: whether an event has a natural endpoint. -/
inductive Telicity where
  | telic   -- has natural endpoint (stop, build, arrive)
  | atelic  -- no natural endpoint (run, swim, love)
  deriving DecidableEq, Repr, Inhabited

/-- Duration: whether an event takes time or is instantaneous. -/
inductive Duration where
  | durative  -- takes time (run, build, love)
  | punctual  -- instantaneous (recognize, arrive, die)
  deriving DecidableEq, Repr, Inhabited

/-- Dynamicity: whether the event involves change. -/
inductive Dynamicity where
  | dynamic  -- involves change (run, build, die)
  | stative  -- no change (know, love, own)
  deriving DecidableEq, Repr, Inhabited

/-- Five-way situation type classification (@cite{smith-1997}).
    Three binary features [±dynamic, ±durative, ±telic] yield five classes.
    The name `VendlerClass` is retained for compatibility; @cite{vendler-1957}
    identified the first four, @cite{smith-1997} added semelfactives. -/
inductive VendlerClass where
  | state         -- [-dynamic, +durative]  know, love
  | activity      -- [+dynamic, +durative, -telic]  run, swim
  | achievement   -- [+dynamic, -durative, +telic]  recognize, die
  | accomplishment -- [+dynamic, +durative, +telic]  build, write
  | semelfactive  -- [+dynamic, -durative, -telic]  cough, tap, flash
  deriving DecidableEq, Repr, Inhabited

/-- Get the telicity of a Vendler class (states treated as atelic). -/
def VendlerClass.telicity : VendlerClass → Telicity
  | .state => .atelic
  | .activity => .atelic
  | .achievement => .telic
  | .accomplishment => .telic
  | .semelfactive => .atelic

/-- Get the duration of a Vendler class. -/
def VendlerClass.duration : VendlerClass → Duration
  | .state => .durative
  | .activity => .durative
  | .achievement => .punctual
  | .accomplishment => .durative
  | .semelfactive => .punctual

/-- Get the dynamicity of a Vendler class. -/
def VendlerClass.dynamicity : VendlerClass → Dynamicity
  | .state => .stative
  | .activity => .dynamic
  | .achievement => .dynamic
  | .accomplishment => .dynamic
  | .semelfactive => .dynamic

/-- States are stative. -/
theorem state_is_stative : VendlerClass.state.dynamicity = .stative := rfl

/-- Activities are atelic. -/
theorem activity_is_atelic : VendlerClass.activity.telicity = .atelic := rfl

/-- Activities are durative. -/
theorem activity_is_durative : VendlerClass.activity.duration = .durative := rfl

/-- Achievements are punctual. -/
theorem achievement_is_punctual : VendlerClass.achievement.duration = .punctual := rfl

/-- Achievements are telic. -/
theorem achievement_is_telic : VendlerClass.achievement.telicity = .telic := rfl

/-- Accomplishments are telic. -/
theorem accomplishment_is_telic : VendlerClass.accomplishment.telicity = .telic := rfl

/-- Accomplishments are durative. -/
theorem accomplishment_is_durative : VendlerClass.accomplishment.duration = .durative := rfl

/-- Semelfactives are atelic. -/
theorem semelfactive_is_atelic : VendlerClass.semelfactive.telicity = .atelic := rfl

/-- Semelfactives are punctual. -/
theorem semelfactive_is_punctual : VendlerClass.semelfactive.duration = .punctual := rfl

/-- Semelfactives are dynamic. -/
theorem semelfactive_is_dynamic : VendlerClass.semelfactive.dynamicity = .dynamic := rfl

/-- All dynamic classes involve change. -/
theorem dynamic_classes_are_dynamic (c : VendlerClass) :
    c ≠ .state → c.dynamicity = .dynamic := by
  intro h
  cases c with
  | state => contradiction
  | activity => rfl
  | achievement => rfl
  | accomplishment => rfl
  | semelfactive => rfl

/-- All telic classes have endpoints. -/
theorem telic_classes (c : VendlerClass) :
    c.telicity = .telic ↔ (c = .achievement ∨ c = .accomplishment) := by
  cases c <;> simp [VendlerClass.telicity]

-- ────────────────────────────────────────────────────
-- AspectualProfile
-- ────────────────────────────────────────────────────

/-- An aspectual profile bundles telicity, duration, and dynamicity. -/
structure AspectualProfile where
  /-- Whether the eventuality has a natural endpoint -/
  telicity : Telicity
  /-- Whether the eventuality takes time -/
  duration : Duration
  /-- Whether the eventuality involves change -/
  dynamicity : Dynamicity
  deriving DecidableEq, Repr

/-- Convert an aspectual profile to a situation type.
    All five [±dynamic, ±durative, ±telic] combinations are distinguished. -/
def AspectualProfile.toVendlerClass (p : AspectualProfile) : VendlerClass :=
  match p.dynamicity, p.duration, p.telicity with
  | .stative, _, _ => .state
  | .dynamic, .durative, .atelic => .activity
  | .dynamic, .punctual, .telic => .achievement
  | .dynamic, .durative, .telic => .accomplishment
  | .dynamic, .punctual, .atelic => .semelfactive

/-- Convert a Vendler class to its canonical aspectual profile. -/
def VendlerClass.toProfile (c : VendlerClass) : AspectualProfile :=
  { telicity := c.telicity
  , duration := c.duration
  , dynamicity := c.dynamicity }

/-- Canonical profile for states. -/
def stateProfile : AspectualProfile :=
  { telicity := .atelic, duration := .durative, dynamicity := .stative }

/-- Canonical profile for activities. -/
def activityProfile : AspectualProfile :=
  { telicity := .atelic, duration := .durative, dynamicity := .dynamic }

/-- Canonical profile for achievements. -/
def achievementProfile : AspectualProfile :=
  { telicity := .telic, duration := .punctual, dynamicity := .dynamic }

/-- Canonical profile for accomplishments. -/
def accomplishmentProfile : AspectualProfile :=
  { telicity := .telic, duration := .durative, dynamicity := .dynamic }

/-- Canonical profile for semelfactives. -/
def semelfactiveProfile : AspectualProfile :=
  { telicity := .atelic, duration := .punctual, dynamicity := .dynamic }

/-- Converting a situation type to a profile and back is identity. -/
theorem vendler_profile_roundtrip (c : VendlerClass) :
    c.toProfile.toVendlerClass = c := by
  cases c <;> rfl

/-- The canonical state profile maps to the state class. -/
theorem stateProfile_toClass : stateProfile.toVendlerClass = .state := rfl

/-- The canonical activity profile maps to the activity class. -/
theorem activityProfile_toClass : activityProfile.toVendlerClass = .activity := rfl

/-- The canonical achievement profile maps to the achievement class. -/
theorem achievementProfile_toClass : achievementProfile.toVendlerClass = .achievement := rfl

/-- The canonical accomplishment profile maps to the accomplishment class. -/
theorem accomplishmentProfile_toClass : accomplishmentProfile.toVendlerClass = .accomplishment := rfl

/-- The canonical semelfactive profile maps to the semelfactive class. -/
theorem semelfactiveProfile_toClass : semelfactiveProfile.toVendlerClass = .semelfactive := rfl

-- ────────────────────────────────────────────────────
-- Homogeneity and subinterval properties
-- ────────────────────────────────────────────────────

/-- Whether a predicate has the subinterval property (qualified).
    States and activities both have it, but with different strength:
    - **States** have the *full* SIP: every subinterval of a knowing event
      is a knowing event (@cite{smith-1997} p. 23).
    - **Activities** have a *qualified* SIP: subintervals down to a
      minimum size are activity events, but below that minimum they
      are not (you can't be "walking" in an interval smaller than a
      single stride). See `hasFullSubintervalProp` for the distinction. -/
def AspectualProfile.isHomogeneous (p : AspectualProfile) : Bool :=
  match p.toVendlerClass with
  | .state | .activity => true
  | .achievement | .accomplishment | .semelfactive => false

/-- Whether the situation type has the *full* (unqualified) subinterval
    property. Only states satisfy this: every subinterval of a state event
    is itself a state event, with no minimum-size qualification.
    Activities have a qualified SIP (above a minimum interval); all other
    types lack it entirely.

    This distinction is the semantic content behind @cite{zhao-2025}'s
    ATOM-DIST_t: states distribute over temporal atoms, activities do not.
    See `predictsAtomDist_iff_stative`. -/
def VendlerClass.hasFullSubintervalProp : VendlerClass → Bool
  | .state => true
  | .activity | .achievement | .accomplishment | .semelfactive => false

/-- States are homogeneous (full SIP). -/
theorem state_is_homogeneous : stateProfile.isHomogeneous = true := rfl

/-- Activities are homogeneous (qualified SIP — above minimum intervals). -/
theorem activity_is_homogeneous : activityProfile.isHomogeneous = true := rfl

/-- Achievements are not homogeneous. -/
theorem achievement_not_homogeneous : achievementProfile.isHomogeneous = false := rfl

/-- Accomplishments are not homogeneous. -/
theorem accomplishment_not_homogeneous : accomplishmentProfile.isHomogeneous = false := rfl

/-- Semelfactives are not homogeneous (punctual — no proper subintervals). -/
theorem semelfactive_not_homogeneous : semelfactiveProfile.isHomogeneous = false := rfl

/-- States have the full (unqualified) SIP. -/
theorem state_has_full_sip : VendlerClass.state.hasFullSubintervalProp = true := rfl

/-- Activities do NOT have the full SIP — only a qualified version. -/
theorem activity_lacks_full_sip : VendlerClass.activity.hasFullSubintervalProp = false := rfl

/-- Full SIP implies qualified SIP (homogeneity), but not vice versa. -/
theorem fullSIP_implies_homogeneous (c : VendlerClass)
    (h : c.hasFullSubintervalProp = true) :
    c.toProfile.isHomogeneous = true := by
  cases c <;> simp_all [VendlerClass.hasFullSubintervalProp]; rfl

/-- VendlerClass predicts the (qualified) subinterval property:
    states and activities have it, others don't.
    This matches `isHomogeneous` — see `sub_agrees_with_homogeneous`.

    Note: states have the *full* SIP (every subinterval, no minimum),
    while activities have a *qualified* SIP (subintervals above a
    minimum size). This predicate returns `true` for both — use
    `VendlerClass.hasFullSubintervalProp` to distinguish them. -/
def predictsSubintervalProp : VendlerClass → Bool
  | .state | .activity => true
  | .achievement | .accomplishment | .semelfactive => false

/-- SUB prediction agrees with homogeneity. -/
theorem sub_agrees_with_homogeneous (c : VendlerClass) :
    predictsSubintervalProp c = c.toProfile.isHomogeneous := by
  cases c <;> rfl

/-- Full SIP is strictly stronger than qualified SIP:
    states have full SIP, activities have only qualified SIP. -/
theorem fullSIP_strictly_stronger :
    VendlerClass.state.hasFullSubintervalProp = true ∧
    predictsSubintervalProp .state = true ∧
    VendlerClass.activity.hasFullSubintervalProp = false ∧
    predictsSubintervalProp .activity = true := ⟨rfl, rfl, rfl, rfl⟩

/-- Homogeneous iff durative and atelic.
    Semelfactives are atelic but not homogeneous (punctual), so
    homogeneity requires both atelicity and duration. -/
theorem homogeneous_iff_durative_atelic (p : AspectualProfile) :
    p.isHomogeneous = true ↔
    (p.toVendlerClass = .state ∨ p.toVendlerClass = .activity) := by
  simp only [AspectualProfile.isHomogeneous]
  cases h : p.toVendlerClass <;> simp

-- ────────────────────────────────────────────────────
-- Atomic distributivity
-- ────────────────────────────────────────────────────

/-- Whether a VendlerClass predicts ATOM-DIST_t (@cite{zhao-2025}, Def. 5.3).
    States satisfy ATOM-DIST_t (distribute over temporal subintervals);
    dynamic classes do not. Stricter than `isHomogeneous`: activities are
    homogeneous but fail ATOM-DIST_t. -/
def VendlerClass.predictsAtomDist : VendlerClass → Bool
  | .state => true
  | .activity | .achievement | .accomplishment | .semelfactive => false

/-- ATOM-DIST_t prediction coincides with stative dynamicity. -/
theorem predictsAtomDist_iff_stative (c : VendlerClass) :
    c.predictsAtomDist = true ↔ c.dynamicity = .stative := by
  cases c <;> simp [VendlerClass.predictsAtomDist, VendlerClass.dynamicity]

/-- States predict ATOM-DIST_t holds. -/
theorem state_predictsAtomDist :
    VendlerClass.state.predictsAtomDist = true := rfl

/-- All dynamic classes predict ATOM-DIST_t failure. -/
theorem dynamic_predictsAtomDist_false (c : VendlerClass)
    (h : c.dynamicity = .dynamic) :
    c.predictsAtomDist = false := by
  cases c <;> simp_all [VendlerClass.dynamicity, VendlerClass.predictsAtomDist]

/-- ATOM-DIST_t implies homogeneity (but not vice versa).
    Activities are homogeneous but do NOT satisfy ATOM-DIST_t — this is
    Zhao's point: ATOM-DIST_t discriminates states from activities, while
    the classical subinterval property does not. -/
theorem atomDist_implies_homogeneous (c : VendlerClass)
    (h : c.predictsAtomDist = true) :
    c.toProfile.isHomogeneous = true := by
  cases c <;> simp_all [VendlerClass.predictsAtomDist]; rfl

/-- ATOM-DIST_t prediction is the negation of dynamicity =.dynamic. -/
theorem predictsAtomDist_iff_not_dynamic (c : VendlerClass) :
    (c.predictsAtomDist = false) ↔ (c.dynamicity = .dynamic) := by
  cases c <;> simp [VendlerClass.predictsAtomDist, VendlerClass.dynamicity]

/-- Full SIP coincides with ATOM-DIST_t — both pick out exactly states. -/
theorem fullSIP_iff_atomDist (c : VendlerClass) :
    c.hasFullSubintervalProp = c.predictsAtomDist := by
  cases c <;> rfl

end Core.Verbs
