import Linglib.Semantics.ArgumentStructure.MeaningComponents
import Linglib.Semantics.Spatial.Path

/-!
# ArgumentStructure.LevinClass
[levin-1993]

The 49-class verb taxonomy from [levin-1993] Part II, with
per-class meaning-component profiles, unaccusativity prediction, and
verb-of-creation flag.

## Provenance

Moved from `Core/Lexical/VerbClass.lean` in the cleanup that dissolved
`Core/Lexical/`. Lives at `Semantics/Lexical/` (sibling of
`LevinTheory.lean` for root-entailment derivation, `LevinClassProfiles.lean`
for argument templates, `MeaningComponents.lean` for the diagnostic
features) — Levin's framework, not consensus substrate.

## Framework commitment

[levin-1993]'s 49 classes are the most widely-cited reference for
English verb classification, but they are **not** the only such taxonomy.
Sibling theory-named slots are intentionally unfilled in this restructure:

- `Semantics/Lexical/VerbNet.lean` — Kipper-Schuler 2005
  formally extends Levin to ~270 classes with thematic role hierarchies
- `Semantics/Lexical/FrameNet.lean` — Fillmore/Baker/Sato semantic
  frames as an alternative to alternation-based classification
- `Semantics/Lexical/PropBank.lean` — Palmer/Gildea/Kingsbury 2005
  verb-specific argument frames
- `Semantics/Lexical/Faulhaber2011.lean` — *Verb Valency Patterns*
  empirical critique of meaning-based predictions about alternation
  participation; the principal disconfirming reference

Future formalisations of these alternatives should land as siblings
here, with refutation theorems showing where they diverge from Levin
on attested verbs.

## Citation hygiene notes

- The 49 per-class section numbers (`§ 9.1`, `§ 9.3`, etc.) cited in
  `LevinClass.levinSection` are flagged `UNVERIFIED:` per CLAUDE.md ("Never
  cite specific equation, table, or section numbers from memory").
  They are preserved as comments since they're useful for navigation
  but should be cross-checked against the published [levin-1993].
- The `meaningComponents` per-class assignments in [levin-1993]'s
  Part II text are similarly UNVERIFIED in detail; the canonical
  *break*/*cut*/*hit*/*touch* assignments from the Introduction are
  the most reliably-cited.
- `isVerbOfCreation .cooking := true` is debatable per [dowty-1979]
  *bake*-polysemy: *bake a cake* (creation) vs *bake the potato* (CoS).
  Levin §45.3 cooking verbs exhibit causative-inchoative alternation
  grouping them with CoS verbs; the substrate's classification reflects
  the creation reading, but downstream consumers should be aware of the
  polysemy.

## Alternative frameworks not formalized in linglib

The Levin-style alternation-diagnosed classification competes with
other lexical-semantic frameworks that may be worth formalizing as
sibling theories:
- **Generative Lexicon** ([pustejovsky-1995]): qualia structure
  (formal/constitutive/telic/agentive) as the primitive decomposition,
  with verbs deriving meaning from interaction with NP qualia.
- **Frame semantics** ([fillmore-1982], [fillmore-kay-oconnor-1988]):
  semantic frames as the primitive, alternations as surface reflexes.
- **Configurational lexical semantics** ([hale-keyser-1987]):
  verb meaning derives from syntactic configuration, not feature decomposition.
- **Lexical Conceptual Structure** ([jackendoff-1996]): primitive
  predicates GO/STAY/CAUSE compose into LCS templates.
-/

namespace ArgumentStructure

/-- Verb class taxonomy from [levin-1993] Part II.

    Section numbers follow the book. Class names are Levin's labels.
    49 top-level classes covering the English verb lexicon.

    Not all subclasses are listed here — the taxonomy is intentionally
    at the top-level class grain, with subclass distinctions handled by
    `MeaningComponents` and `RootProfile`.

    UNVERIFIED: Per-class section numbers (e.g., `§ 9.1` for `.put`)
    cited from memory — verify against the published monograph. -/
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
  | give               -- 13.1: give, lend, pass, sell, ...
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
  | build              -- 26.1: build, assemble, bake, carve, ...
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
  | eat                -- 39.1: eat, drink (the class's only members)
  | devour             -- 39.4: devour, consume, ingest, ...
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
  -- Verbs of Appearance, Disappearance, and Occurrence (§ 48)
  | appear             -- 48.1: appear, emerge, ...
  | disappearance      -- 48.2: die, disappear, expire, perish, vanish
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

namespace LevinClass

/-- Section number in [levin-1993] for each class. The bare name
    `section` would clash with Lean's reserved keyword; we use
    `levinSection` as the canonical accessor.

    UNVERIFIED: Per-class section numbers cited from memory; verify
    against the published monograph. -/
def levinSection : LevinClass → String
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
  | .disappearance => "48.2"
  | .bodyInternalMotion => "49" | .assumePosition => "50"
  | .inherentlyDirectedMotion => "51.1" | .leave => "51.2"
  | .mannerOfMotion => "51.3" | .vehicleMotion => "51.4"
  | .chase => "51.6"
  | .avoid => "52" | .linger => "53.1" | .rush => "53.2"
  | .measure => "54" | .aspectual => "55" | .weather => "57"

/-- Meaning components associated with each Levin class.

    Profiles are assigned using the diagnostic criteria from [levin-1993]:
    - `changeOfState`: middle alternation
    - `contact`: body-part possessor ascension
    - `motion`: conative alternation requires motion + contact
    - `causation`: causative/inchoative alternation
    - `instrumentSpec`: verb specifies instrument/means
    - `mannerSpec`: verb specifies manner of action

    UNVERIFIED: Per-class meaning-component assignments are summary
    judgments; the canonical *break*/*cut*/*hit*/*touch* from Levin's
    Introduction are the most reliably cited; per-class assignments
    for the other 45 classes are the formaliser's interpretation of
    Part II text and should be cross-checked. -/
def meaningComponents : LevinClass → MeaningComponents
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
  | .hit => MeaningComponents.hit
  | .swat => ⟨false, true, true, false, false, false⟩
  | .poke => ⟨false, true, true, false, true, false⟩
  | .touch => MeaningComponents.touch
  | .cut => MeaningComponents.cut
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
  | .destroy => MeaningComponents.destroy
  | .break_ => MeaningComponents.break_
  | .bend => MeaningComponents.bend
  | .cooking => ⟨true, false, false, true, false, true⟩
  | .otherCoS => ⟨true, false, false, true, false, false⟩
  | .entitySpecificCoS => ⟨true, false, false, true, false, false⟩
  | .calibratableCoS => ⟨true, false, false, true, false, false⟩
  | .lodge => ⟨false, false, true, false, false, false⟩
  | .exist => ⟨false, false, false, false, false, false⟩
  | .appear => ⟨true, false, false, false, false, false⟩
  | .disappearance => ⟨true, false, false, false, false, false⟩
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

    Based on [levin-hovav-1995]: unaccusativity correlates with internally
    caused change of state or directed change, while unergativity correlates
    with agentive activity. -/
def PredictsUnaccusative : LevinClass → Prop
  | .break_ | .bend | .cooking | .otherCoS
  | .entitySpecificCoS | .calibratableCoS => True
  | .destroy => True
  | .mix | .amalgamate => True
  | .separate | .split => True
  | .appear => True
  | .disappearance => True
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
    [davies-dubinsky-2003]: VOCs produce their direct object
    as a result of the event. -/
def isVerbOfCreation : LevinClass → Bool
  | .imageCreation => true
  | .build         => true
  | .grow          => true
  | .create        => true
  | .knead         => true
  | .performance   => true
  | .cooking       => true
  | _              => false

/-- Whether a verb class inherently specifies a path shape.
    Inherently directed motion verbs (Levin 51.1: arrive, come, go)
    lexicalize a bounded path. Manner-of-motion verbs (51.3: run, walk)
    are path-neutral — the path comes from a PP complement.
    [talmy-2000]: verb-framed vs. satellite-framed distinction. -/
def pathSpec : LevinClass → Option Semantics.Spatial.Path.PathShape
  | .inherentlyDirectedMotion => some .bounded
  | .leave => some .source
  | .mannerOfMotion => none    -- path from PP
  | .vehicleMotion => none     -- path from PP/context
  | .chase => none             -- path from complement
  | _ => none                  -- non-motion verbs

end LevinClass

end ArgumentStructure
