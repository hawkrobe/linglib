import Linglib.Semantics.ArgumentStructure.MeaningComponents
import Linglib.Semantics.ArgumentStructure.RoleList
import Linglib.Semantics.Events.Path
import Linglib.Semantics.Aspect.Basic

/-!
# The verb classes of Levin 1993

The verb classes of [levin-1993] Part II as an enumeration, each with its meaning components,
the unaccusativity [levin-hovav-1995] predict for it, and whether it is a class of
creation verbs. The classes' alternation profiles are in `DiathesisAlternation.lean`, their
root entailments in `LevinTheory.lean`, and the `levinClass` field of a `Verb` entry carries
its class.

## Implementation notes

The taxonomy is at the grain of Levin's top-level classes, so a constructor such as `search`
covers §35.1–35.6. Section numbers and example members were checked against the monograph.
The meaning components are Levin's semantic characterizations; the alternations diagnose
them only on the Introduction's quadruple, which `DiathesisAlternation.lean` records.

## References

* [levin-1993]
* [levin-hovav-1995]
* [davies-dubinsky-2003]
-/

namespace ArgumentStructure

/-- The verb classes of [levin-1993] Part II, named by Levin's labels, with the section
    number and example members from each class's member list. Some constructors sit at a
    parent grain (`search` for §35.1–35.6, `mannerOfMotion` for §51.3.1–51.3.2). -/
inductive LevinClass where
  -- Verbs of Putting (§ 9)
  | put                -- 9.1: put, place, set, position, ...
  | funnel             -- 9.3: funnel, channel, siphon, ...
  | putDirection       -- 9.4: drop, hoist, lift, lower, raise
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
  | drive              -- 11.5: drive, fly, ferry, ...
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
  | conceal            -- 16: conceal, hide, shelter, ...
  -- Verbs of Throwing (§ 17)
  | throw              -- 17.1: throw, toss, fling, ...
  -- Verbs of Contact by Impact (§ 18)
  | hit                -- 18.1: hit, bash, kick, ...
  | swat               -- 18.2: swat, punch, stab, bite, ...
  | spank              -- 18.3: spank, thrash, whip, flog, ...
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
  | grow               -- 26.2: grow, develop, hatch, ...
  | create             -- 26.4: create, design, invent, ...
  | knead              -- 26.5: knead, squeeze, twist, ...
  | turn               -- 26.6: turn, convert, transform, ...
  | performance        -- 26.7: perform, play, sing, ...
  -- Engender Verbs (§ 27)
  | engender           -- 27: engender, cause, generate, ...
  -- Calve Verbs (§ 28)
  | calve              -- 28: calve, foal, lamb, ...
  -- Verbs with Predicative Complements (§ 29)
  | appoint            -- 29.1: appoint, elect, nominate, ...
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
  | long               -- 32.2: long, wish, yearn, hope, ...
  -- Judgment Verbs (§ 33)
  | judgment           -- 33: praise, thank, criticize, ...
  -- Verbs of Assessment (§ 34)
  | assessment         -- 34: assess, evaluate, ...
  -- Verbs of Searching (§ 35)
  | search             -- 35: hunt, search, stalk, ...
  -- Verbs of Social Interaction (§ 36)
  | socialInteraction  -- 36: correspond, marry, meet, ...
  -- Verbs of Communication (§ 37)
  | say                -- 37.7: say, report, announce, ...
  | tell               -- 37.2: tell (the only member)
  | mannerOfSpeaking   -- 37.3: whisper, shout, mumble, ...
  | talk               -- 37.5: speak, talk
  -- Verbs of Sounds Made by Animals (§ 38)
  | animalSound        -- 38: bark, moo, roar, ...
  -- Verbs of Ingesting (§ 39)
  | eat                -- 39.1: eat, drink (the class's only members)
  | devour             -- 39.4: devour, consume, ingest, ...
  | dine               -- 39.5: dine, feast, ...
  -- Verbs Involving the Body (§ 40)
  | bodyProcess        -- 40.1: hiccup, breathe, cough, ...
  | nonverbalExpression -- 40.2: sigh, laugh, cry, smile, ...
  | flinch             -- 40.5: flinch, cringe, wince, ...
  | hurt               -- 40.8.3: hurt, injure, bruise, sprain, ...
  -- Verbs of Grooming and Bodily Care (§ 41)
  | dress              -- 41.1.1: dress, bathe, shave, ...
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
  | leave              -- 51.2: leave, abandon, desert
  | mannerOfMotion     -- 51.3: run, walk, swim, ...
  | vehicleMotion      -- 51.4: bicycle, fly, sail, ...
  | chase              -- 51.6: chase, pursue, ...
  -- Avoid Verbs (§ 52)
  | avoid              -- 52: avoid, evade, shun, ...
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

/-- The meaning components of each class: the Introduction's characterization for *break*,
    *cut*, *hit* and *touch*, and a reading of the Part II class descriptions for the rest.
    How the components predict alternations, and where the prediction fails against the
    class profiles, is `MeaningComponents.predictedAlternation` in
    `DiathesisAlternation.lean`. -/
def meaningComponents : LevinClass → MeaningComponents
  | .put => ⟨false, false, true, true, false, false⟩
  | .putDirection => ⟨false, false, true, true, false, false⟩
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
  | .spank => ⟨false, true, true, false, false, false⟩
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
  | .long => ⟨false, false, false, false, false, false⟩
  | .judgment => ⟨false, false, false, false, false, false⟩
  | .assessment => ⟨false, false, false, false, false, false⟩
  | .search => ⟨false, false, true, false, false, false⟩
  | .socialInteraction => ⟨false, false, false, false, false, false⟩
  | .say => ⟨false, false, false, false, false, false⟩
  | .tell => ⟨false, false, false, false, false, false⟩
  | .mannerOfSpeaking => ⟨false, false, false, false, false, true⟩
  | .talk => ⟨false, false, false, false, false, false⟩
  | .animalSound => ⟨false, false, false, false, false, true⟩
  | .eat => ⟨true, true, false, false, false, false⟩
  | .devour => ⟨true, true, false, false, false, true⟩
  | .dine => ⟨false, false, false, false, false, true⟩
  | .bodyProcess => ⟨false, false, false, false, false, false⟩
  | .nonverbalExpression => ⟨false, false, false, false, false, false⟩
  | .flinch => ⟨false, false, true, false, false, false⟩
  | .hurt => ⟨true, true, false, true, false, false⟩
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
  | .entitySpecificCoS => ⟨true, false, false, false, false, false⟩
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
  | .putDirection | .spank | .long | .hurt | .talk | .nonverbalExpression => False
  | _ => False

instance : DecidablePred LevinClass.PredictsUnaccusative := fun c => by
  cases c <;> unfold LevinClass.PredictsUnaccusative <;> infer_instance

/-- The class denotes the creation of its object ([davies-dubinsky-2003]). -/
def IsVerbOfCreation : LevinClass → Prop
  | .imageCreation | .build | .grow | .create | .knead | .performance | .cooking => True
  | _ => False

instance : DecidablePred LevinClass.IsVerbOfCreation := fun c => by
  cases c <;> unfold LevinClass.IsVerbOfCreation <;> infer_instance

end LevinClass

/-! ### Class → template map

The argument-structure template each class realizes
(`ArgumentStructure.Template`); `none` for classes whose profiles haven't
been determined yet. Consumed by `Verb.Basic` to derive a verb entry's
default argument profiles from its `levinClass` field. -/

/-- Map a Levin class to its argument structure template.
    Returns `none` for classes whose profiles haven't been determined yet. -/
def LevinClass.roleList : LevinClass → Option RoleList
  -- § 18: Contact by Impact — manner verbs, no CoS entailment
  | .hit | .swat | .spank      => some mannerContact
  -- § 20: Contact: Touch — like hit but lighter force
  | .touch                    => some mannerContact
  -- § 21: Cutting — manner + result (CoS entailed)
  | .cut | .carve             => some resultChange
  -- § 44: Destroy
  | .destroy                  => some resultChange
  -- § 42: Killing
  | .murder | .poison         => some resultChange
  -- § 45: Change of State (causative/inchoative alternation)
  | .break_ | .bend | .cooking
  | .otherCoS | .entitySpecificCoS
  | .calibratableCoS          => some resultChange
  -- § 26: Creation and Transformation
  | .build | .create | .knead => some creation
  | .grow                     => some creation
  -- § 25: Image Creation
  | .imageCreation            => some creation
  -- § 39: Ingesting
  | .eat | .devour            => some consumption
  -- § 51.3: Manner of Motion
  | .mannerOfMotion           => some selfMotion
  -- § 51.6: Chase
  | .chase                    => some selfMotion
  -- § 51.1: Inherently Directed Motion
  | .inherentlyDirectedMotion => some directedMotion
  -- § 30: Perception
  | .see | .sight             => some perception
  -- § 31.1: Amuse-class psych verbs (stimulus subject)
  | .amuse                    => some psychCausal
  -- § 31.2: Admire-class psych verbs (experiencer subject)
  | .admire                   => some psychState
  -- § 32.1: Want verbs (desire states)
  | .want | .long              => some desire
  -- § 13.1 / § 13.5: Change of possession (give / obtain)
  | .give | .getObtain        => some possessionTransfer
  -- § 10.4: Wipe verbs (manner-subclass default; instrument-sense
  -- entries override with `wipeInstrument` per verb)
  | .wipe                     => some wipeManner
  -- § 48.2: Disappearance
  | .disappearance            => some ArgumentStructure.disappearance
  -- Not yet classified
  | _                         => none

-- ════════════════════════════════════════════════════
-- § 4. Convenience accessors
-- ════════════════════════════════════════════════════

/-- Subject entailment profile for a Levin class. -/
def LevinClass.subjectProfile (c : LevinClass) : Option EntailmentProfile :=
  c.roleList.map (·.subjectProfile)

/-- Object entailment profile for a Levin class. -/
def LevinClass.objectProfile (c : LevinClass) : Option EntailmentProfile :=
  c.roleList.bind (·.objectProfile)

/-- **The stored linking is never ASP-reversed** ([dowty-1991] via
    [levin-rappaport-hovav-2005] ch. 2): in no class does the object
    outrank the subject under the Argument Selection Principle. Where
    dominance is strict the ASP derives the stored linking; at the psych
    doublets (*like*/*please*: `Dowty1991.psychStative_alternation`)
    neither argument outranks, and the class's linking is a lexical
    choice the role list underdetermines. -/
theorem roleList_not_asp_reversed {c : LevinClass} {r : RoleList}
    {o : EntailmentProfile} (hr : c.roleList = some r)
    (ho : r.objectProfile = some o) :
    ¬ OutranksForSubject o r.subjectProfile := by
  cases c <;> cases hr <;> cases ho <;> decide

end ArgumentStructure
