import Linglib.Semantics.Causation.Morphological
import Linglib.Semantics.ArgumentStructure.EventStructure
import Linglib.Semantics.ArgumentStructure.ArgDerivation

/-!
# [krejci-2012] — Causativization as Antireflexivization

Krejci, Bonnie. 2012. *Causativization as Antireflexivization: A Study of
Middle and Ingestive Verbs*. Master's Report, University of Texas at Austin.

## Core claims

1. **Middles** (wash, dress; agent acts on their own body, [kemmer-1994]) and
   **ingestives** (eat, drink; agent directs a consumed substance at themselves,
   with *learn* proposed as a metaphorical ingestive, a class label from
   [nedyalkov-silnitsky-1973]) are **lexically reflexive**: their simple forms
   have bieventive causative event structure with coidentified causer and
   causee — her (37), e.g.
   `eat = [[ACT⟨manipulate food⟩(x)] CAUSE [BECOME ⟨potentially digest⟩(x, y)]]`.

2. **Antireflexivization** (§4.2, (96)–(97)): the lexical causative splits the
   coidentified argument into two participants (eat→feed, learn→teach; wash and
   dress reuse the same form transitively). *Feed* ≠ *make eat*: with *eat* the
   eater must agentively manipulate food; with *feed* that entailment shifts to
   the feeder; with *make eat* it stays on the eater (§4.2.1).

3. **Five diagnostics** detect CAUSE in the English simple forms: the three
   [dowty-1979] complexity tests — *again* ambiguity, *re-* prefixation, and
   *almost* ambiguity (§4.3) — plus negation over CAUSE (§4.4) and *by itself*
   (§4.5, after [chierchia-2004]). All five come out positive for all four
   verbs, with hedges: some speakers reject the restitutive reading of *John
   washed again* (her fn. 8), and the negation evidence is offered as
   "tentative", with *I didn't eat any pie* marked "?" ((106a)).

4. The **causativizability hierarchy** — unaccusatives > middles/ingestives >
   unergatives > simple transitives — is implicational, and none of the 32
   surveyed languages skips a tier; twelve are tabulated in Table 2.8
   (`krejciLanguages`). The dedicated middles/ingestives tier is the report's
   typological contribution. (Her second, morphological evidence base — Marathi
   *-aw* causativization, her Section 5 — is not formalized here.)

## Main declarations

- `LexReflexiveVerb`, `allVerbs` — the four English verbs with their observed
  diagnostic profiles and `IntransitivizationType` analysis
- `reflexivePrediction`, `observed_matches_reflexive_analysis` — the reflexive
  analysis predicts every diagnostic positive, matching the observations
- `krejciLanguages`, `hierarchy_holds` — Table 2.8 and its implicational check
-/

namespace Krejci2012

open Verb
open ArgumentStructure
open Root.Kinds
open Causation.Morphological
open ArgumentStructure.EventStructure
open ArgumentStructure.ArgDerivation

/-! ### Lexically reflexive verbs -/

/-- Subtype of lexically reflexive verb.
    Middles: agent acts on their own body ([kemmer-1994]: one internally
    complex participant; her §4.1). Ingestives: agent causes a substance to
    enter themselves, including "metaphorical ingesting"
    ([nedyalkov-silnitsky-1973], her Table 2.5) such as *learn*. -/
inductive LexReflexiveSubtype where
  | middle
  | ingestive
  deriving DecidableEq, Repr

/-- Observed outcomes of the five CAUSE diagnostics for one verb's simple
    form (§4.3–4.5). Each field is a recorded English judgment, cited to the
    report's examples at the verb entries below. -/
structure DiagnosticProfile where
  /-- Postverbal *again* has restitutive + repetitive readings
      ([dowty-1979]; (70)–(73)). -/
  again : Bool
  /-- *re-* prefixation yields a restitutive reading ((76)–(82)). -/
  rePrefix : Bool
  /-- *almost* scopes over action vs. result sub-event ((85)–(88)). -/
  almost : Bool
  /-- The simple form can be logically negated while the causative variant is
      asserted, NPI-controlled against metalinguistic negation
      (§4.4, (106)–(109); after [koontz-garboden-2009]). -/
  negationOverCause : Bool
  /-- *by itself* "without outside help" is licensed
      (§4.5, (114); after [chierchia-2004]). -/
  byItself : Bool
  deriving DecidableEq, Repr

/-- A lexically reflexive verb: bieventive causative event structure with
    coidentified causer and causee in the simple form, per her (37). -/
structure LexReflexiveVerb where
  gloss : String
  subtype : LexReflexiveSubtype
  /-- Suppletive lexical causative (antireflexivized form), `none` when the
      same form serves transitively (wash, dress). -/
  lexicalCausative : Option String
  /-- [krejci-2012]'s analysis of the simple form: the causer position is
      retained, coidentified with the causee. -/
  intransType : IntransitivizationType
  /-- Observed diagnostic outcomes for the simple form. -/
  observed : DiagnosticProfile
  deriving DecidableEq, Repr

/-- *eat*: ingestive.
    `[[ACT⟨manipulate food⟩(x)] CAUSE [BECOME ⟨potentially digest⟩(x, y)]]`
    ((37a)); lexical causative *feed* (§4.2.1). -/
def eat : LexReflexiveVerb where
  gloss := "eat"
  subtype := .ingestive
  lexicalCausative := some "feed"
  intransType := .reflexive
  observed :=
    { again := true              -- (70) "Your guy ate the coin again..."
      rePrefix := true           -- (76)–(77) attested "re-eat all the coins"
      almost := true             -- (85) "John almost ate the pie"
      negationOverCause := true  -- (92)/(106) "I didn't eat pie; you fed pie to me!"
      byItself := true }         -- (114a) "The girl ate her food all by herself"

/-- *wash*: middle.
    `[[ACT⟨manipulate water⟩(x)] CAUSE [BECOME ⟨washed⟩(x)]]` ((37b));
    the transitive is the same form, antireflexivized (§4.2.2). -/
def wash : LexReflexiveVerb where
  gloss := "wash"
  subtype := .middle
  lexicalCausative := none
  intransType := .reflexive
  observed :=
    { again := true              -- (71) "John washed again..." (fn. 8: variation)
      rePrefix := true           -- (78)–(79) attested "rewash"
      almost := true             -- (86) "John almost washed"
      negationOverCause := true  -- (107) "I didn't wash; you washed me!"
      byItself := true }         -- (114b) "The girl washed all by herself"

/-- *dress*: middle.
    `[[ACT⟨manipulate clothes⟩(x)] CAUSE [BECOME ⟨dressed⟩(x)]]` ((37c));
    the transitive is the same form, antireflexivized (§4.2.3). -/
def dress : LexReflexiveVerb where
  gloss := "dress"
  subtype := .middle
  lexicalCausative := none
  intransType := .reflexive
  observed :=
    { again := true              -- (72) "John dressed again..."
      rePrefix := true           -- (80)–(81) attested "re-dressed"
      almost := true             -- (87) "John almost dressed"
      negationOverCause := true  -- (108) "I didn't dress; you dressed me!"
      byItself := true }         -- (114c) "The girl dressed all by herself"

/-- *learn*: proposed metaphorical ingestive.
    `[[ACT(x)] CAUSE [BECOME ⟨know⟩(x, y)]]` ((37d));
    lexical causative *teach* (§4.2.4). -/
def learn : LexReflexiveVerb where
  gloss := "learn"
  subtype := .ingestive
  lexicalCausative := some "teach"
  intransType := .reflexive
  observed :=
    { again := true              -- (73) "John learned English again..."
      rePrefix := true           -- (82) "John re-learned English..."
      almost := true             -- (88) "John almost learned French"
      negationOverCause := true  -- (109) "I didn't learn French; you taught French to me!"
      byItself := true }         -- (114d) "The girl learned to walk all by herself"

def allVerbs : List LexReflexiveVerb :=
  [eat, wash, dress, learn]

/-! ### Observed diagnostics match the reflexive analysis -/

/-- What the reflexive analysis predicts: bieventive structure supplies the
    result state the three [dowty-1979] tests scope over, and the retained
    (coidentified) causer supplies CAUSE for negation and *by itself*. Cells
    are derived from the substrate's `IntransitivizationType.reflexive` facts,
    not stipulated. -/
def reflexivePrediction : DiagnosticProfile where
  again := IntransitivizationType.reflexive.isBieventive
  rePrefix := IntransitivizationType.reflexive.isBieventive
  almost := IntransitivizationType.reflexive.isBieventive
  negationOverCause := IntransitivizationType.reflexive.isBieventive
  byItself := IntransitivizationType.reflexive.licensesBySelf

/-- The report's empirical core: all four verbs are analyzed as reflexive
    intransitivizers, and their observed diagnostic profiles are exactly what
    that analysis predicts. A single `false` observation would falsify the
    `.reflexive` typing. -/
theorem observed_matches_reflexive_analysis :
    ∀ v ∈ allVerbs,
      v.intransType = .reflexive ∧ v.observed = reflexivePrediction := by
  decide

/-- Antireflexivization is suppletive exactly for the ingestives (eat→feed,
    learn→teach); the middles reuse the same form transitively (§4.2). -/
theorem suppletive_iff_ingestive :
    ∀ v ∈ allVerbs,
      v.lexicalCausative.isSome = true ↔ v.subtype = .ingestive := by
  decide

/-! ### Root entailments and templates

Her (37) puts CAUSE in the simple forms of *eat* and *dress*; the substrate's
[beavers-koontz-garboden-2020]-style root classification agrees in carrying
`cause`: both roots are `causativeResult` ({state, result, cause}). The point
of contact is the *presence* of CAUSE, not its source — for [krejci-2012] the
causer is the coidentified agent itself, and she argues explicitly against
deriving the causative by adding an external causer ((93) vs. (96)–(97)).
`learn`'s root is still the substrate's conservative `minimal` placeholder, so
the bridge is stated for *eat* and *dress* only.

The accomplishment template licenses an intransitive (achievement) variant,
yet *"The food ate" / *"The clothes dressed" are out: on [krejci-2012]'s
account the alternation slot is already occupied — the simple form *is* the
reflexive variant, and the causative is derived from it by antireflexivization
rather than by adding CAUSE to an inchoative core. -/

/-- eat roots carry caused-consumption entailments. -/
theorem eat_is_causativeResult :
    LevinClass.rootEntailments .eat = causativeResult := rfl

/-- dress roots carry caused dressed-state entailments. -/
theorem dress_is_causativeResult :
    LevinClass.rootEntailments .dress = causativeResult := rfl

/-- causativeResult roots carry the `cause` kind — CAUSE is in the simple
    form, as her (37) requires. -/
theorem causativeResult_entails_cause :
    LexKind.cause ∈ causativeResult := by decide

/-- eat roots license the accomplishment template. -/
theorem eat_licenses_accomplishment :
    RootLicensesTemplate (LevinClass.rootEntailments .eat) .accomplishment := by
  decide

/-- eat's primary template is accomplishment. -/
theorem eat_primary_accomplishment :
    primaryTemplate (LevinClass.rootEntailments .eat) = some .accomplishment := rfl

/-- eat's RoleList is `consumption` (agent + incremental theme). -/
theorem eat_roleList_is_consumption :
    LevinClass.roleList .eat = some consumption := rfl

/-- The accomplishment template has an intransitive variant (achievement). -/
theorem accomplishment_has_variant :
    Template.intransitiveVariant .accomplishment = some .achievement := rfl

/-- The intransitive variant retains the result state (instance of
    `intransitive_has_resultState`). -/
theorem alternation_preserves_result : Template.HasResultState .achievement :=
  intransitive_has_resultState .accomplishment .achievement rfl

/-- The intransitive variant loses CAUSE on the deletion analysis (instance of
    `intransitive_no_cause`). -/
theorem alternation_loses_cause : ¬ Template.HasCause .achievement :=
  intransitive_no_cause .accomplishment .achievement rfl

/-! ### Causativizability hierarchy (Table 2.8)

unaccusatives > middles/ingestives > unergatives > simple transitives.
Implicational: a causative morpheme that reaches a lower tier reaches every
higher one, and none of the 32 surveyed languages skips a tier. Twelve are
tabulated in Table 2.8, three per type: Type 1 (unaccusatives only) Slave,
Mapudungun, Classical Nahuatl; Type 2 (+ middles/ingestives) Cora, Marathi,
Amharic; Type 3 (+ unergatives) Ahtna, Tariana, Malayalam; Type 4 (+ simple
transitives) Basque, Dulong/Rawang, Koyukon. The dedicated middles/ingestives
tier between unaccusatives and unergatives is the report's typological
contribution. Malayalam is grouped with Type 3 although its morpheme reaches
transitives with an instrumental-case causee (her fn. 6). -/

/-- Which verb classes one language's morphological causative applies to
    (one row of Table 2.8). -/
structure CausativizabilityData where
  language : String
  morpheme : String
  unaccusative : Bool
  middlesIngestive : Bool := false
  unergative : Bool := false
  simpleTransitive : Bool := false
  deriving DecidableEq, Repr

/-- The hierarchy is implicational: each level implies all higher levels.
    simpleTransitive → unergative → middlesIngestive → unaccusative. -/
def CausativizabilityData.respectsHierarchy (d : CausativizabilityData) : Bool :=
  (!d.simpleTransitive || d.unergative) &&
  (!d.unergative || d.middlesIngestive) &&
  (!d.middlesIngestive || d.unaccusative)

/-- Table 2.8: twelve languages, ordered from narrowest to broadest
    causative scope. -/
def krejciLanguages : List CausativizabilityData :=
  [ { language := "Slave",            morpheme := "-h-",    unaccusative := true }
  , { language := "Mapudungun",       morpheme := "-ɨm",    unaccusative := true }
  , { language := "Classical Nahuatl", morpheme := "-tia",  unaccusative := true }
  , { language := "Cora",             morpheme := "-te",    unaccusative := true
    , middlesIngestive := true }
  , { language := "Marathi",          morpheme := "-aw",    unaccusative := true
    , middlesIngestive := true }
  , { language := "Amharic",          morpheme := "a-",     unaccusative := true
    , middlesIngestive := true }
  , { language := "Ahtna",            morpheme := "-ɬ-",    unaccusative := true
    , middlesIngestive := true, unergative := true }
  , { language := "Tariana",          morpheme := "-i-ta",  unaccusative := true
    , middlesIngestive := true, unergative := true }
  , { language := "Malayalam",        morpheme := "-icc",   unaccusative := true
    , middlesIngestive := true, unergative := true }
  , { language := "Basque",           morpheme := "-arazi", unaccusative := true
    , middlesIngestive := true, unergative := true, simpleTransitive := true }
  , { language := "Dulong/Rawang",    morpheme := "shv-",   unaccusative := true
    , middlesIngestive := true, unergative := true, simpleTransitive := true }
  , { language := "Koyukon",          morpheme := "-ɬ-",    unaccusative := true
    , middlesIngestive := true, unergative := true, simpleTransitive := true }
  ]

/-- All twelve Table 2.8 languages respect the implicational hierarchy. -/
theorem hierarchy_holds :
    krejciLanguages.all (·.respectsHierarchy) = true := by decide

end Krejci2012
