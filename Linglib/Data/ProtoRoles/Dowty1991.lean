import Linglib.Data.ProtoRoles.Schema

/-!
# Dowty1991 — proto-role attribution data (generated)
[dowty-1991]

Auto-generated from `Linglib/Data/ProtoRoles/Dowty1991.json` by
`scripts/gen_protoroles.py`. **Do not edit by hand** — edit the JSON and
re-run the generator. The 48 per-argument entailment attributions
the paper states explicitly, with locators; fields the paper is silent or
hedged about are `none`.
-/

namespace Dowty1991

namespace Rows

def buildSubject : ProtoRoleDatum :=
  { verb := "build", arg := .subject,
    argDesc := "the builder",
    volition := some true,
    sentience := some true,
    causation := some true,
    movement := some true,
    independentExistence := some true,
    locator := "pp. 572-573: 'build, for example has all of 27 for subject'; also (35) p. 577" }

def buildObject : ProtoRoleDatum :=
  { verb := "build", arg := .object,
    argDesc := "the thing built (a house)",
    changeOfState := some true,
    incrementalTheme := some true,
    causallyAffected := some true,
    stationary := some true,
    dependentExistence := some true,
    locator := "pp. 572-573: 'all of 28 for object'; (30e) 'John built a house'; also (35) p. 577" }

def bePoliteSubject : ProtoRoleDatum :=
  { verb := "be polite to", arg := .subject,
    argDesc := "the polite party",
    volition := some true,
    locator := "(29a) p. 572, 'VOLITION ALONE: John is being polite to Bill'" }

def ignoreSubject : ProtoRoleDatum :=
  { verb := "ignore", arg := .subject,
    argDesc := "the ignorer",
    volition := some true,
    locator := "(29a) p. 572, 'is ignoring Mary'" }

def knowSubject : ProtoRoleDatum :=
  { verb := "know", arg := .subject,
    argDesc := "the knower",
    sentience := some true,
    locator := "(29b) p. 573, 'SENTIENCE/PERCEPTION ALONE: John knows ... the statement'" }

def believeSubject : ProtoRoleDatum :=
  { verb := "believe", arg := .subject,
    argDesc := "the believer",
    sentience := some true,
    locator := "(29b) p. 573" }

def seeSubject : ProtoRoleDatum :=
  { verb := "see", arg := .subject,
    argDesc := "the perceiver",
    sentience := some true,
    locator := "(29b) p. 573, 'John sees ... Mary'; p. 573 'the stative perception verbs'" }

def fearSubject : ProtoRoleDatum :=
  { verb := "fear", arg := .subject,
    argDesc := "the fearer",
    sentience := some true,
    locator := "(29b) p. 573, 'John ... fears Mary'" }

def causeSubject : ProtoRoleDatum :=
  { verb := "cause", arg := .subject,
    argDesc := "the causing state (his loneliness)",
    causation := some true,
    movement := some false,
    locator := "(29c) p. 573, 'CAUSATION ALONE'; p. 573 'stative causatives ... would fill this slot'" }

def passSubject : ProtoRoleDatum :=
  { verb := "pass", arg := .subject,
    argDesc := "the mover (the rolling tumbleweed)",
    volition := some false,
    causation := some false,
    movement := some true,
    locator := "(29d) p. 573; p. 573 'movement is found without causation or volition (29d)'" }

def overtakeSubject : ProtoRoleDatum :=
  { verb := "overtake", arg := .subject,
    argDesc := "the faster mover (the bullet)",
    volition := some false,
    causation := some false,
    movement := some true,
    locator := "(29d) p. 573, 'The bullet overtook the arrow'" }

def fillSubject : ProtoRoleDatum :=
  { verb := "fill", arg := .subject,
    argDesc := "the filling substance (water)",
    volition := some false,
    causation := some false,
    movement := some true,
    locator := "(29d) p. 573, 'Water filled the boat'" }

def fallSubject : ProtoRoleDatum :=
  { verb := "fall", arg := .subject,
    argDesc := "the faller",
    volition := some false,
    causation := some false,
    movement := some true,
    locator := "(29d) p. 573, 'He accidentally fell'" }

def needSubject : ProtoRoleDatum :=
  { verb := "need", arg := .subject,
    argDesc := "the needer",
    volition := some false,
    sentience := some false,
    causation := some false,
    movement := some false,
    independentExistence := some true,
    locator := "(29e) p. 573, 'John needs a new car'; p. 573 'verbs that entail subject existence but have none of (a)-(d)'" }

def makeObject : ProtoRoleDatum :=
  { verb := "make", arg := .object,
    argDesc := "the thing made (a mistake)",
    changeOfState := some true,
    dependentExistence := some true,
    locator := "(30a) p. 573, 'John made a mistake (coming into being, therefore also 30e below)'" }

def moveObject : ProtoRoleDatum :=
  { verb := "move", arg := .object,
    argDesc := "the thing moved (the rock)",
    changeOfState := some true,
    locator := "(30a) p. 573, 'John moved the rock (indefinite change of position)'" }

def eraseObject : ProtoRoleDatum :=
  { verb := "erase", arg := .object,
    argDesc := "the thing erased (the error)",
    changeOfState := some true,
    dependentExistence := some true,
    locator := "(30a) p. 573 'erased the error (ceasing to exist)'; (30e) pp. 573-574" }

def crossObject : ProtoRoleDatum :=
  { verb := "cross", arg := .object,
    argDesc := "the path crossed (the driveway)",
    incrementalTheme := some true,
    stationary := some true,
    locator := "(30b) p. 573, 'John crossed the driveway ... (also stationary relative to other arguments)'" }

def fillObject : ProtoRoleDatum :=
  { verb := "fill", arg := .object,
    argDesc := "the container filled (the glass)",
    incrementalTheme := some true,
    stationary := some true,
    locator := "(30b) p. 573, 'filled the glass with water'" }

def causeObject : ProtoRoleDatum :=
  { verb := "cause", arg := .object,
    argDesc := "the caused condition (cancer)",
    causallyAffected := some true,
    locator := "(30c) p. 573, 'CAUSALLY AFFECTED: Smoking causes cancer'" }

def enterObject : ProtoRoleDatum :=
  { verb := "enter", arg := .object,
    argDesc := "the target entered",
    stationary := some true,
    locator := "(30d) p. 573, 'The bullet entered the target'" }

def overtakeObject : ProtoRoleDatum :=
  { verb := "overtake", arg := .object,
    argDesc := "the slower mover (the arrow)",
    stationary := some true,
    locator := "(30d) p. 573; cf. p. 573 'only be stationary from the faster first object's perspective'" }

def constituteObject : ProtoRoleDatum :=
  { verb := "constitute", arg := .object,
    argDesc := "the constituted state (a major dilemma)",
    dependentExistence := some true,
    locator := "(30e) pp. 573-574, 'This situation constitutes a major dilemma for us'" }

def needObject : ProtoRoleDatum :=
  { verb := "need", arg := .object,
    argDesc := "the thing needed (a car, de dicto)",
    dependentExistence := some true,
    locator := "(30e) p. 574, 'John needs a car ... (de dicto objects: no existence)'" }

def seekObject : ProtoRoleDatum :=
  { verb := "seek", arg := .object,
    argDesc := "the thing sought (a unicorn, de dicto)",
    dependentExistence := some true,
    locator := "(30e) p. 574, 'seeks a unicorn'" }

def lackObject : ProtoRoleDatum :=
  { verb := "lack", arg := .object,
    argDesc := "the thing lacked (de dicto)",
    dependentExistence := some true,
    locator := "(30e) p. 574, 'lacks enough money to buy it'" }

def writeSubject : ProtoRoleDatum :=
  { verb := "write", arg := .subject,
    argDesc := "the writer",
    volition := some true,
    sentience := some true,
    causation := some true,
    movement := some true,
    changeOfState := some false,
    incrementalTheme := some false,
    causallyAffected := some false,
    stationary := some false,
    dependentExistence := some false,
    locator := "(35) p. 577: subjects have 'volition, sentience, causation, and movement ... and no P-Patient entailments'" }

def murderSubject : ProtoRoleDatum :=
  { verb := "murder", arg := .subject,
    argDesc := "the murderer",
    volition := some true,
    sentience := some true,
    causation := some true,
    movement := some true,
    changeOfState := some false,
    incrementalTheme := some false,
    causallyAffected := some false,
    stationary := some false,
    dependentExistence := some false,
    locator := "(35) p. 577" }

def eatSubject : ProtoRoleDatum :=
  { verb := "eat", arg := .subject,
    argDesc := "the eater",
    volition := some true,
    sentience := some true,
    causation := some true,
    movement := some true,
    changeOfState := some false,
    incrementalTheme := some false,
    causallyAffected := some false,
    stationary := some false,
    dependentExistence := some false,
    locator := "(35) p. 577" }

def washSubject : ProtoRoleDatum :=
  { verb := "wash", arg := .subject,
    argDesc := "the washer",
    volition := some true,
    sentience := some true,
    causation := some true,
    movement := some true,
    changeOfState := some false,
    incrementalTheme := some false,
    causallyAffected := some false,
    stationary := some false,
    dependentExistence := some false,
    locator := "(35) p. 577" }

def writeObject : ProtoRoleDatum :=
  { verb := "write", arg := .object,
    argDesc := "the thing written (a letter)",
    changeOfState := some true,
    causallyAffected := some true,
    locator := "(35) p. 577: objects have 'change, causally affected, and (mostly) incremental theme, stationary, dependent existence'" }

def murderObject : ProtoRoleDatum :=
  { verb := "murder", arg := .object,
    argDesc := "the victim",
    changeOfState := some true,
    causallyAffected := some true,
    locator := "(35) p. 577" }

def eatObject : ProtoRoleDatum :=
  { verb := "eat", arg := .object,
    argDesc := "the thing eaten",
    changeOfState := some true,
    causallyAffected := some true,
    locator := "(35) p. 577" }

def washObject : ProtoRoleDatum :=
  { verb := "wash", arg := .object,
    argDesc := "the thing washed (a plate)",
    changeOfState := some true,
    causallyAffected := some true,
    locator := "(35) p. 577" }

def buySubject : ProtoRoleDatum :=
  { verb := "buy", arg := .subject,
    argDesc := "the buyer",
    volition := some true,
    locator := "sec. 3.2 p. 556: 'both buyer and seller must act agentively (voluntarily)'" }

def buySeller : ProtoRoleDatum :=
  { verb := "buy", arg := .oblique,
    argDesc := "the seller (from-phrase)",
    volition := some true,
    locator := "sec. 3.2 p. 556; (4b) 'Mary bought the piano from John'" }

def sellSubject : ProtoRoleDatum :=
  { verb := "sell", arg := .subject,
    argDesc := "the seller",
    volition := some true,
    locator := "sec. 3.2 p. 556; (4a) 'John sold the piano to Mary'" }

def sellBuyer : ProtoRoleDatum :=
  { verb := "sell", arg := .oblique,
    argDesc := "the buyer (to-phrase)",
    volition := some true,
    locator := "sec. 3.2 p. 556" }

def likeSubject : ProtoRoleDatum :=
  { verb := "like", arg := .subject,
    argDesc := "the experiencer",
    sentience := some true,
    locator := "(38) p. 579: 'the Experiencer is entailed to be sentient/perceiving'" }

def likeObject : ProtoRoleDatum :=
  { verb := "like", arg := .object,
    argDesc := "the stimulus",
    sentience := some false,
    causation := some true,
    locator := "(38) p. 579: 'the Stimulus causes some emotional reaction or cognitive judgment in the Experiencer', 'though the Stimulus is not [sentient/perceiving]'" }

def pleaseSubject : ProtoRoleDatum :=
  { verb := "please", arg := .subject,
    argDesc := "the stimulus",
    sentience := some false,
    causation := some true,
    locator := "(38) p. 579 (stimulus-subject column)" }

def pleaseObject : ProtoRoleDatum :=
  { verb := "please", arg := .object,
    argDesc := "the experiencer",
    sentience := some true,
    locator := "(38) p. 579" }

def surpriseObjectInchoative : ProtoRoleDatum :=
  { verb := "surprise (inchoative)", arg := .object,
    argDesc := "the experiencer (coming to be surprised)",
    sentience := some true,
    changeOfState := some true,
    locator := "p. 580: 'the inchoative interpretation entails a Proto-Patient property in the Experiencer ... undergoing a (definite) change of state'" }

def hitObject : ProtoRoleDatum :=
  { verb := "hit", arg := .object,
    argDesc := "the location (the fence)",
    movement := some false,
    changeOfState := some false,
    incrementalTheme := some false,
    locator := "sec. 9.3.3 p. 595: 'neither object can be a (nontrivial) Incremental Theme'; pp. 595-596: movement entailed for the prepositional argument 'but not its direct-object argument'; p. 596: 'no entailments of change of state'" }

def hitInstrument : ProtoRoleDatum :=
  { verb := "hit", arg := .oblique,
    argDesc := "the instrument (the stick)",
    movement := some true,
    changeOfState := some false,
    incrementalTheme := some false,
    locator := "sec. 9.3.3 pp. 595-596: 'hit the fence with the stick entails movement for its prepositional argument'" }

def breakObject : ProtoRoleDatum :=
  { verb := "break", arg := .object,
    argDesc := "the thing broken",
    changeOfState := some true,
    incrementalTheme := some true,
    locator := "(64 II) p. 595: 'entails change of state (and Incremental Themehood) in only one argument'" }

def loadTheme : ProtoRoleDatum :=
  { verb := "load", arg := .nonsubject,
    argDesc := "the locatum (the hay)",
    changeOfState := some true,
    locator := "p. 594: 'in loading a truck with hay, the hay changes location'; (64 I) p. 595: 'entail change of state in both arguments'" }

def loadLocation : ProtoRoleDatum :=
  { verb := "load", arg := .nonsubject,
    argDesc := "the location (the truck)",
    changeOfState := some true,
    locator := "p. 594: 'the truck also changes from an unloaded to a loaded state'; (64 I) p. 595" }

end Rows

/-- All 48 explicit per-argument attributions. -/
def allRows : List ProtoRoleDatum :=
  [Rows.buildSubject,
   Rows.buildObject,
   Rows.bePoliteSubject,
   Rows.ignoreSubject,
   Rows.knowSubject,
   Rows.believeSubject,
   Rows.seeSubject,
   Rows.fearSubject,
   Rows.causeSubject,
   Rows.passSubject,
   Rows.overtakeSubject,
   Rows.fillSubject,
   Rows.fallSubject,
   Rows.needSubject,
   Rows.makeObject,
   Rows.moveObject,
   Rows.eraseObject,
   Rows.crossObject,
   Rows.fillObject,
   Rows.causeObject,
   Rows.enterObject,
   Rows.overtakeObject,
   Rows.constituteObject,
   Rows.needObject,
   Rows.seekObject,
   Rows.lackObject,
   Rows.writeSubject,
   Rows.murderSubject,
   Rows.eatSubject,
   Rows.washSubject,
   Rows.writeObject,
   Rows.murderObject,
   Rows.eatObject,
   Rows.washObject,
   Rows.buySubject,
   Rows.buySeller,
   Rows.sellSubject,
   Rows.sellBuyer,
   Rows.likeSubject,
   Rows.likeObject,
   Rows.pleaseSubject,
   Rows.pleaseObject,
   Rows.surpriseObjectInchoative,
   Rows.hitObject,
   Rows.hitInstrument,
   Rows.breakObject,
   Rows.loadTheme,
   Rows.loadLocation]

end Dowty1991
