import Linglib.Morphology.DM.Allosemy
import Linglib.Syntax.ConstructionGrammar.Basic
import Linglib.Features.Acceptability
import Linglib.Fragments.German.Predicates

/-!
# Benz (2025): Structure and Interpretation Across Categories

[benz-2025], PhD dissertation, University of Pennsylvania. Three case studies of
the syntax–LF interface in German, unified by contextual allosemy
(`Morphology.DM.Allosemy`):

1. **Content nominalizations** (Ch. 3): nominalizations like *Beobachtung* have
   event, referential (RN), and content readings, all from one syntactic
   structure — n over a prefixed complex verbal head — with the variation
   located in the allosemes of v and n. The content reading rests on an
   n[CONTENT] alloseme that composes with a CP complement.
2. **Prefixes, particles, and resultatives** (Ch. 4): the co-occurrence
   restrictions among the three preverbal-element types (Table 3) follow from
   the conjunction of two independent factors — phrase structure (particles and
   resultative secondary predicates are phrasal complements of the verb, which
   has only one complement position; prefixes form a complex head with the
   root) and event structure (an event is delimited at most once,
   [tenny-1994]'s Single Delimiting Constraint).
3. **Prefixes in nominalizations** (Ch. 5): the three nominalization types
   resolve the particle "structure problem" ([luedeling-2001]) differently —
   phrasal inputs (nominalized infinitive), particles-as-heads (*-ung*), outer
   attachment (*Ge-...-e*) — and the distribution of preverbal elements across
   them follows.
-/

namespace Benz2025

open Morphology.DM.Allosemy
open Features (Acceptability VendlerClass)
open German.Predicates
open ArgumentStructure

/-! ## Part I: Content nominalizations (Ch. 3) -/

/-! ### The three readings of *Beobachtung* -/

/-- A German nominalization datum: reading plus the diagnostic profile its
example sentence exhibits ([benz-2025] (32), diagnostics after
[grimshaw-1990]). -/
structure NominalizationDatum where
  /-- The nominalized form (lemma). -/
  form : String
  /-- Base verb. -/
  baseVerb : String
  /-- The nominalizing suffix. -/
  suffix : String := "-ung"
  /-- The reading exhibited in this example. -/
  reading : NominalizationReading
  /-- Example sentence. -/
  sentence : String
  /-- Translation. -/
  translation : String
  /-- Accepts temporal/durative modification in this reading? -/
  temporalModifiers : Bool
  /-- Pluralizable in this reading? -/
  pluralizable : Bool
  /-- Takes a content-specifying CP complement? -/
  takesCPComplement : Bool
  deriving Repr, BEq

/-- Event reading ([benz-2025] (32a)): duration predicate diagnoses the
complex event nominal; CENs resist pluralization ([grimshaw-1990]; Benz notes
the exceptions reported for German are marginal). -/
def beobachtung_CEN : NominalizationDatum :=
  { form := "Beobachtung"
  , baseVerb := "beobachten"
  , reading := .complexEvent
  , sentence := "Die Beobachtung des Nachthimmels dauerte drei Stunden"
  , translation := "The observation of the night sky took three hours"
  , temporalModifiers := true
  , pluralizable := false
  , takesCPComplement := false }

/-- Referential reading ([benz-2025] (32b)): pluralized, referring to concrete
objects (e.g. a ledger of observations). Benz uses the "RN" label loosely for
readings distinct from both the event and the content reading. -/
def beobachtung_RN : NominalizationDatum :=
  { form := "Beobachtung"
  , baseVerb := "beobachten"
  , reading := .simpleEntity
  , sentence := "Die Beobachtungen der Astronomin sind für immer verloren"
  , translation := "The astronomer's observations are lost forever"
  , temporalModifiers := false
  , pluralizable := true
  , takesCPComplement := false }

/-- Content reading ([benz-2025] (32c)): the CP complement specifies the
content the noun refers to. The content reading is also available in the
pluralized (32b), so it tolerates pluralization. -/
def beobachtung_CCN : NominalizationDatum :=
  { form := "Beobachtung"
  , baseVerb := "beobachten"
  , reading := .content
  , sentence := "Seine Beobachtung, dass Planeten sich bewegen, veränderte die Wissenschaft"
  , translation := "His observation that planets move changed the science"
  , temporalModifiers := false
  , pluralizable := true
  , takesCPComplement := true }

def allBeobachtungReadings : List NominalizationDatum :=
  [beobachtung_CEN, beobachtung_RN, beobachtung_CCN]

/-- *Beobachtung* exhibits all three readings ([benz-2025] (32)). -/
theorem beobachtung_three_readings :
    allBeobachtungReadings.map (·.reading) = [.complexEvent, .simpleEntity, .content] := rfl

/-- The three readings have pairwise distinct diagnostic profiles: duration
modification picks out the event reading, pluralization the referential and
content readings, CP complementation the content reading. -/
theorem beobachtung_diagnostics :
    allBeobachtungReadings.map
        (λ d => (d.temporalModifiers, d.pluralizable, d.takesCPComplement)) =
      [(true, false, false), (false, true, false), (false, true, true)] := rfl

/-! ### Readings from allosemes -/

/-- The alloseme pair deriving each reading, on the analysis the
dissertation's denotations adopt: v is semantically vacuous on all readings
but the CEN, so each non-CEN reading is carried by a contentful alloseme of n
([benz-2025] §3.5, following [wood-2023]). The alternative — attributing every
eventive component to v — is noted but not adopted; `readingFromAllosemes`
admits both. -/
def adoptedAllosemes : NominalizationReading → VAlloseme × NAlloseme
  | .complexEvent => (.eventive, .zero)
  | .simpleEvent  => (.zero, .simpleEvent)
  | .result       => (.zero, .result)
  | .simpleState  => (.zero, .state)
  | .simpleEntity => (.zero, .entity)
  | .content      => (.zero, .content)

/-- Each reading is recovered from its adopted alloseme pair. -/
theorem adopted_roundtrip (r : NominalizationReading) :
    readingFromAllosemes (adoptedAllosemes r).1 (adoptedAllosemes r).2 = some r := by
  cases r <;> rfl

/-- The event and result readings are "mirror images ... in terms of semantic
interpretation: In the event interpretation, (only) v is interpreted, in the
result interpretation, it is (only) n" ([benz-2025] §3.5). -/
theorem event_result_mirror :
    (adoptedAllosemes .complexEvent).1.introducesEvent = true ∧
    (adoptedAllosemes .complexEvent).2 = .zero ∧
    (adoptedAllosemes .result).1.introducesEvent = false ∧
    (adoptedAllosemes .result).2 ≠ .zero :=
  ⟨rfl, rfl, rfl, by decide⟩

/-- One structure, three readings: every attested *Beobachtung* reading is
derived by varying only the allosemes of v and n ([benz-2025] Ch. 3's chapter
claim). The content reading needs no eventive v — simple content nouns like
*Gerücht* 'rumor' have it with no corresponding verb at all (Table 2). -/
theorem beobachtung_readings_from_allosemy :
    allBeobachtungReadings.all (λ d =>
      readingFromAllosemes (adoptedAllosemes d.reading).1 (adoptedAllosemes d.reading).2
        == some d.reading) = true := by decide

/-! ## Part II: Prefixes, particles, and resultatives (Ch. 4) -/

/-! ### The three preverbal-element types -/

/-- The three types of German preverbal elements ([benz-2025] Ch. 4):
inseparable prefixes, separable particles, and resultative secondary
predicates (RSPs). -/
inductive PreverbalElement where
  | pfx  -- inseparable prefix (be-, ent-, er-, ge-, miss-, ver-, zer-)
  | prt  -- separable particle (ab-, an-, auf-, aus-, ein-, ...)
  | rsp  -- resultative secondary predicate (platt, tot, kaputt, ...)
  deriving DecidableEq, Repr

/-- The syntactic level of a morphological element: head (X⁰) or phrase (XP). -/
inductive SynLevel where
  | head    -- X⁰: can occur inside a complex head
  | phrase  -- XP: cannot incorporate
  deriving DecidableEq, Repr

/-- Prefixes are heads forming a complex head with the root (inseparable under
V2 movement); particles and RSPs are phrasal (stranded under V2; RSPs are
modifiable aPs). Following [wurmbrand-1998] and [zeller-2001], particles are
phrasal complements of the verb not dominated by further functional
material. -/
def PreverbalElement.synLevel : PreverbalElement → SynLevel
  | .pfx => .head
  | .prt => .phrase
  | .rsp => .phrase

/-- Whether an element obligatorily introduces a result-state specification.
Prefixes and RSPs always specify a result state; particles can have
non-delimiting (directional, completive) readings ([benz-2025] §4.4). -/
inductive ResultStateSpec where
  | specifies  -- obligatorily introduces a result state
  | neutral    -- has non-delimiting readings
  deriving DecidableEq, Repr

def PreverbalElement.resultSpec : PreverbalElement → ResultStateSpec
  | .pfx => .specifies
  | .prt => .neutral
  | .rsp => .specifies

/-! ### The two compatibility factors -/

/-- Structural combinability of an outer and an inner element (inner = closer
to the root). A phrasal inner element is impossible: a head outside it cannot
form a complex head with the root, and a phrasal outer element competes with
it for the verb's single complement position — "Because the verb can take only
one complement, these elements are structurally incompatible" ([benz-2025]
§4.4). -/
def incorporationAllowed (outer inner : SynLevel) : Bool :=
  match outer, inner with
  | .head,   .head   => true   -- complex head formation
  | .phrase, .head   => true   -- phrasal complement + complex head
  | .head,   .phrase => false  -- head cannot attach outside a phrase
  | .phrase, .phrase => false  -- one complement position

/-- Structural combinability depends only on the inner element's level —
derived, not stipulated. -/
theorem incorporation_only_depends_on_inner (outer inner : SynLevel) :
    incorporationAllowed outer inner = (inner == .head) := by
  cases outer <;> cases inner <;> rfl

/-- **Single Delimiting Constraint**: "The event described by a verb may only
have one measuring-out and be delimited only once" ([tenny-1994] p. 79, quoted
at [benz-2025] (159)). Two elements that both obligatorily specify a result
state cannot co-occur: the end state Pred₂ of the complex event semantics can
only be specified once. -/
def resultStatesCompatible (a b : ResultStateSpec) : Bool :=
  match a, b with
  | .specifies, .specifies => false
  | _, _ => true

def structurallyCompatible (outer inner : PreverbalElement) : Bool :=
  incorporationAllowed outer.synLevel inner.synLevel

def interpretivelyCompatible (outer inner : PreverbalElement) : Bool :=
  resultStatesCompatible outer.resultSpec inner.resultSpec

/-- A combination is predicted possible iff both factors permit it
([benz-2025] §4.4). -/
def predictedAllowed (outer inner : PreverbalElement) : Bool :=
  structurallyCompatible outer inner && interpretivelyCompatible outer inner

/-! ### Prefix and particle inventory (Table 4) -/

/-- German inseparable prefixes ([benz-2025] Table 4). *ge-* is the rare
non-participial prefix (*ge-bären*, *ge-denken*, *ge-fallen*). -/
def inseparablePrefixes : List String :=
  ["be", "ent", "er", "ge", "miss", "ver", "zer"]

/-- German prepositional separable particles ([benz-2025] Table 4; the table
additionally lists nominal and adjectival particles like *klavier-*, *rad-*,
*leicht-*, whose classification is controversial). -/
def separableParticles : List String :=
  ["ab", "an", "auf", "aus", "bei", "ein", "los", "nach", "vor", "zu"]

/-- Elements occurring both as prefix and as particle ([benz-2025] Table 4). -/
def ambiguousElements : List String :=
  ["durch", "hinter", "über", "um", "unter", "wider"]

/-- Table 4's three-way partition: the ambiguous elements appear in neither
pure inventory. -/
theorem ambiguous_not_pure :
    ambiguousElements.all (λ e =>
      !inseparablePrefixes.contains e && !separableParticles.contains e) = true := by
  decide

/-! ### The co-occurrence paradigm (Table 3) -/

/-- A cell of Table 3's factor columns: does this factor predict the
combination to be possible? `particleDependent` renders the table's
parenthesized check mark — "the predictions depend on the specific particles
involved" ([benz-2025] §4.1). -/
inductive FactorVerdict where
  | predicts           -- ✓: factor predicts the combination possible
  | particleDependent  -- (✓): possible for result-neutral particles
  | excludes           -- ✗: factor predicts the combination impossible
  deriving DecidableEq, Repr

/-- Boolean reading of a factor cell: `particleDependent` counts as possible
(the generic classification treats particles as result-neutral). -/
def FactorVerdict.possible : FactorVerdict → Bool
  | .predicts => true
  | .particleDependent => true
  | .excludes => false

/-- A row of [benz-2025] Table 3 (repeated as Table 5): outer element(s),
inner element (closer to the root), observed availability, and the two factor
verdicts. The printed table's final row merges pfx-RSP and PRT-RSP into one
row "pfx/PRT-RSP", rendered here by a two-element `outers` list. -/
structure CooccurrenceRow where
  outers : List PreverbalElement
  inner : PreverbalElement
  allowed : Bool
  structureVerdict : FactorVerdict
  interpretationVerdict : FactorVerdict
  deriving Repr, BEq

/-- [benz-2025] Table 3, cell for cell. Attested examples per row: pfx-pfx
(81) *ent-ver-trauen; pfx-PRT (83) *zer-ab-schneiden; PRT-pfx (84)
aus-er-wählen, an-ver-trauen, vor-ent-halten; PRT-PRT (82) *rad-ein-fahren;
RSP-pfx (87) *arm be-raubt; RSP-PRT (88) *nass an-gespuckt; RSP-RSP (86)
*sich kaputt müde gearbeitet. -/
def cooccurrenceTable : List CooccurrenceRow := [
  { outers := [.pfx], inner := .pfx, allowed := false
  , structureVerdict := .predicts, interpretationVerdict := .excludes },
  { outers := [.pfx], inner := .prt, allowed := false
  , structureVerdict := .excludes, interpretationVerdict := .particleDependent },
  { outers := [.prt], inner := .pfx, allowed := true
  , structureVerdict := .predicts, interpretationVerdict := .particleDependent },
  { outers := [.prt], inner := .prt, allowed := false
  , structureVerdict := .excludes, interpretationVerdict := .particleDependent },
  { outers := [.rsp], inner := .pfx, allowed := false
  , structureVerdict := .predicts, interpretationVerdict := .excludes },
  { outers := [.rsp], inner := .prt, allowed := false
  , structureVerdict := .excludes, interpretationVerdict := .particleDependent },
  { outers := [.rsp], inner := .rsp, allowed := false
  , structureVerdict := .excludes, interpretationVerdict := .excludes },
  { outers := [.pfx, .prt], inner := .rsp, allowed := false
  , structureVerdict := .excludes, interpretationVerdict := .excludes }
]

/-- The conjunction of the two factors reproduces the Allowed column at every
cell of Table 3. -/
theorem combined_prediction_matches :
    cooccurrenceTable.all (λ r => r.outers.all λ o =>
      predictedAllowed o r.inner == r.allowed) = true := by decide

/-- The structural factor reproduces the Structure column at every cell. -/
theorem structural_prediction_matches :
    cooccurrenceTable.all (λ r => r.outers.all λ o =>
      structurallyCompatible o r.inner == r.structureVerdict.possible) = true := by decide

/-- The interpretive factor reproduces the Interpretation column at every cell
except the merged row's particle half (see
`prt_rsp_interpretation_particle_dependent`). -/
theorem interpretive_prediction_matches :
    cooccurrenceTable.all (λ r => r.outers.all λ o =>
      (o == .prt && r.inner == .rsp) ||
        (interpretivelyCompatible o r.inner == r.interpretationVerdict.possible)) = true := by
  decide

/-- The printed table marks the merged pfx/PRT-RSP row's interpretation cell
✗, but on the account's own classification only the prefix half is
interpretively excluded: "the unavailability of particle verbs with RSPs is
due to the fact that RSPs cannot attach to phrasal VPs. Of course, some
RSP-particle verbs are additionally also ruled out semantically, because some
particles introduce end states" ([benz-2025] §4.4) — the structural factor
does the work, and the interpretive verdict is particle-dependent. -/
theorem prt_rsp_interpretation_particle_dependent :
    structurallyCompatible .prt .rsp = false ∧
    interpretivelyCompatible .prt .rsp = true := ⟨rfl, rfl⟩

/-- PRT-pfx is the unique allowed combination — "much more widely attested
than any of the others" ([benz-2025] (84): *aus-er-wählen*, *an-ver-trauen*,
*vor-ent-halten*, *um-ent-scheiden*, *ab-er-kennen*). -/
theorem prt_pfx_uniquely_allowed :
    (cooccurrenceTable.filter (·.allowed)).map (λ r => (r.outers, r.inner)) =
      [([.prt], .pfx)] := by decide

/-- Neither factor alone predicts the paradigm: structure alone misses the
double-delimitation rows (pfx-pfx, RSP-pfx), and interpretation alone misses
the phrase-structure rows (pfx-PRT, PRT-PRT, RSP-PRT). -/
theorem two_factors_needed :
    (cooccurrenceTable.any (λ r => r.structureVerdict.possible && !r.allowed)) = true ∧
    (cooccurrenceTable.any (λ r => r.interpretationVerdict.possible && !r.allowed)) = true := by
  constructor <;> decide

/-! ### Blocking derivations

The two principles as a derivation system: a combination is blocked iff a
derivation exists. Soundness and completeness against `predictedAllowed` show
the two principles exactly generate the paradigm. -/

/-- A proof that a preverbal-element combination violates one of the two
principles.

**`byPhrasalInner`**: a phrasal element cannot occupy the inner position —
a head outside it cannot form a complex head with the root, and a phrasal
outer competes for the verb's single complement position ([benz-2025] §4.4).

**`bySingleDelimiting`**: two obligatory result-state specifiers conflict —
the end state of a complex event can only be specified once ([tenny-1994]
p. 79's Single Delimiting Constraint, [benz-2025] (159)). -/
inductive Blocked : PreverbalElement → PreverbalElement → Prop where
  | byPhrasalInner {o i : PreverbalElement} :
      i.synLevel = .phrase → Blocked o i
  | bySingleDelimiting {o i : PreverbalElement} :
      o.resultSpec = .specifies → i.resultSpec = .specifies → Blocked o i

/-- **Soundness**: every blocking derivation corresponds to a predicted-blocked
combination — the theory does not over-generate. -/
theorem blocked_sound {o i : PreverbalElement} (h : Blocked o i) :
    predictedAllowed o i = false := by
  cases h with
  | byPhrasalInner hi =>
      cases o <;> cases i <;> first | rfl | exact absurd hi (by decide)
  | bySingleDelimiting ho _ =>
      cases o <;> cases i <;> first | rfl | exact absurd ho (by decide)

/-- **Completeness**: every blocked combination has a derivation — the two
principles account for all restrictions. -/
theorem blocked_complete {o i : PreverbalElement}
    (h : predictedAllowed o i = false) : Blocked o i := by
  cases o <;> cases i <;>
    first
    | exact .byPhrasalInner rfl
    | exact .bySingleDelimiting rfl rfl
    | exact absurd h (by decide)

/-- The allowed combination has no derivation: the prefix is a head, and the
particle is result-neutral. -/
theorem prt_pfx_no_derivation : ¬ Blocked .prt .pfx := by
  intro h
  cases h with
  | byPhrasalInner hi => exact absurd hi (by decide)
  | bySingleDelimiting ho _ => exact absurd ho (by decide)

/-- pfx-pfx is blocked only by the Single Delimiting Constraint (both are
heads), so the interpretive rule is not redundant. -/
theorem pfx_pfx_only_interpretive :
    Blocked .pfx .pfx ∧ PreverbalElement.pfx.synLevel ≠ .phrase :=
  ⟨.bySingleDelimiting rfl rfl, by decide⟩

/-- pfx-PRT is blocked only structurally (particles are result-neutral), so
the structural rule is not redundant. -/
theorem pfx_prt_only_structural :
    Blocked .pfx .prt ∧ PreverbalElement.prt.resultSpec ≠ .specifies :=
  ⟨.byPhrasalInner rfl, by decide⟩

/-! ### Cross-framework contrast: the phrase-in-word-slot cell

`ConstructionGrammar.Slot.IsPhraseInWordSlot` — a phrasal filler in a
zero-level position — is the configuration of phrasal compounds and the PAL
construction ([goldberg-shirtz-2025]; contemporaneous with this dissertation,
neither cites the other). In this file's terms that configuration is exactly
the banned phrasal-inner cell: the structural principle rejects what the
constructionist analysis licenses (cf. `GoldbergShirtz2025.pal_load_bearing`). -/

/-- A CxG bar level in `SynLevel` terms: zero-level positions are head sites;
bar- and phrase-level positions are phrasal. -/
def SynLevel.ofBarLevel : ConstructionGrammar.BarLevel → SynLevel
  | .zero => .head
  | .bar => .phrase
  | .phrase => .phrase

/-- The `SynLevel` of a CxG slot filler: word fillers are heads, phrasal
fillers (with or without a fixed head) are phrases; SEM+ fillers are
level-unspecified. -/
def _root_.ConstructionGrammar.SlotFiller.synLevel :
    ConstructionGrammar.SlotFiller String → Option SynLevel
  | .fixed _ => some .head
  | .open_ _ => some .head
  | .headed _ _ => some .phrase
  | .phrasal => some .phrase
  | .semantic _ => none

/-- A phrase in a word-level slot occupies the banned cell: its site is a
head, its filler a phrase, and `incorporationAllowed` rejects the pair. The
standing counterexample class is the PAL construction, which licenses exactly
this configuration. -/
theorem phraseInWordSlot_incorporation_banned
    (s : ConstructionGrammar.Slot String) (h : s.IsPhraseInWordSlot) :
    ∃ site filler,
      s.level.map SynLevel.ofBarLevel = some site ∧
      s.filler.synLevel = some filler ∧
      incorporationAllowed site filler = false := by
  obtain ⟨hf, hl⟩ := h
  refine ⟨.head, .phrase, ?_, ?_, rfl⟩ <;>
    simp [hl, hf, SynLevel.ofBarLevel, ConstructionGrammar.SlotFiller.synLevel]

/-! ### German resultative data (§4.2)

Complex predicate semantics after [williams-2015], adopted at [benz-2025]
(158): ⟦v⟧ = λx λe₁ ∃e₂ ∃s. Means(e₁,e₂) & Pred₁(e₂) & Theme(e₁,x) &
End(e₁,s) & Pred₂(s). The M(eans) predicate is the verb, the R(esult)
predicate the RSP; the End Theme Postulate (108) links the Theme of the
complex event to the end state. See `Causation.Resultatives` for the
complementary causal-dynamics analysis. -/

/-- A German resultative datum with gloss and judgment. -/
structure GermanResultativeDatum where
  sentence : String
  gloss : String
  translation : String
  judgment : Acceptability
  verbClass : String
  deriving Repr, BEq

/-- German RSP data ([benz-2025] (89), (115); (115a,e,f) after
[creemers-2020] and Rapp). German allows obligatorily transitive,
unaccusative, and inherently reflexive M predicates in resultatives. -/
def germanRSPData : List GermanResultativeDatum := [
  { sentence := "Er hämmerte das Metall platt"
  , gloss := "he hammered the.ACC metal flat"
  , translation := "He hammered the metal flat"
  , judgment := .ok
  , verbClass := "transitive" },
  { sentence := "Er schießt seinen Gegner tot"
  , gloss := "he shoots his.ACC opponent dead"
  , translation := "He shoots his opponent dead"
  , judgment := .ok
  , verbClass := "transitive" },
  { sentence := "Hans hat den Stock kaputt gebrochen"
  , gloss := "Hans has the.ACC stick broken broken.PTCP"
  , translation := "Hans broke the stick"
  , judgment := .ok
  , verbClass := "obligatorily transitive" },
  { sentence := "Das Wasser fror fest"
  , gloss := "the.NOM water froze solid"
  , translation := "The water froze solid"
  , judgment := .ok
  , verbClass := "unaccusative" },
  { sentence := "Sie haben sich krank/tot geschämt"
  , gloss := "they have REFL sick/dead shamed.PTCP"
  , translation := "They were embarrassed sick/dead"
  , judgment := .ok
  , verbClass := "inherently reflexive" }
]

/-- German allows non-unergative M predicates in resultatives ([benz-2025]
(115)) — against weak-resultative reanalyses of the whole class. -/
theorem german_allows_non_unergative_M :
    (germanRSPData.any (·.verbClass == "obligatorily transitive")) = true ∧
    (germanRSPData.any (·.verbClass == "unaccusative")) = true ∧
    (germanRSPData.any (·.verbClass == "inherently reflexive")) = true := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-! ### RSP co-occurrence contrasts (§4.1) -/

/-- RSPs are incompatible with prefixed verbs; the same RSP with the simplex
verb is fine ([benz-2025] (87), from [creemers-2020]). The *ge-* in the
grammatical examples is participial, not a prefix in the relevant sense. -/
def rsp_pfx_contrasts : List (GermanResultativeDatum × GermanResultativeDatum) := [
  ( { sentence := "*Sie haben uns arm be-raubt"
    , gloss := "they have us.ACC poor BE-robbed.PTCP"
    , translation := "They robbed us poor"
    , judgment := .unacceptable
    , verbClass := "prefix verb (be-)" },
    { sentence := "Sie haben uns arm geraubt"
    , gloss := "they have us.ACC poor robbed.PTCP"
    , translation := "They robbed us poor"
    , judgment := .ok
    , verbClass := "simplex verb" } ),
  ( { sentence := "*Sie haben ihn tot er-schossen"
    , gloss := "they have him.ACC dead ER-shot.PTCP"
    , translation := "They shot him dead"
    , judgment := .unacceptable
    , verbClass := "prefix verb (er-)" },
    { sentence := "Sie haben ihn tot geschossen"
    , gloss := "they have him.ACC dead shot.PTCP"
    , translation := "They shot him dead"
    , judgment := .ok
    , verbClass := "simplex verb" } ),
  ( { sentence := "*Hans hat den Stock kaputt zer-brochen"
    , gloss := "Hans has the.ACC stick broken ZER-broken.PTCP"
    , translation := "Hans broke the stick broken"
    , judgment := .unacceptable
    , verbClass := "prefix verb (zer-)" },
    { sentence := "Hans hat den Stock kaputt gebrochen"
    , gloss := "Hans has the.ACC stick broken.ADJ broken.PTCP"
    , translation := "Hans broke the stick broken"
    , judgment := .ok
    , verbClass := "simplex verb" } )
]

/-- Every RSP + prefix-verb contrast: prefixed verb out, simplex fine. -/
theorem rsp_pfx_contrast_pattern :
    rsp_pfx_contrasts.all (λ (bad, good) =>
      bad.judgment == .unacceptable && good.judgment == .ok) = true := by
  decide

/-- RSPs are likewise incompatible with particle verbs ([benz-2025] (88)) —
including particles not characterizable as resultative, like *an-* in
(88d). -/
def rsp_prt_contrasts : List (GermanResultativeDatum × GermanResultativeDatum) := [
  ( { sentence := "*Sie hat den Tisch trocken ab-gewischt"
    , gloss := "she has the.ACC table dry AB-wiped.PTCP"
    , translation := "She wiped the table off dry"
    , judgment := .unacceptable
    , verbClass := "particle verb (ab-)" },
    { sentence := "Sie hat den Tisch trocken gewischt"
    , gloss := "she has the.ACC table dry wiped.PTCP"
    , translation := "She wiped the table dry"
    , judgment := .ok
    , verbClass := "simplex verb" } ),
  ( { sentence := "*Das Baby hat mich nass an-gespuckt"
    , gloss := "the baby has me.ACC wet AN-spit.PTCP"
    , translation := "The baby spat up on me and I was wet as a result"
    , judgment := .unacceptable
    , verbClass := "particle verb (an-)" },
    { sentence := "Das Baby hat mich nass gespuckt"
    , gloss := "the baby has me.ACC wet spit.PTCP"
    , translation := "The baby spat up on me"
    , judgment := .ok
    , verbClass := "simplex verb" } )
]

/-- Every RSP + particle-verb contrast: particle verb out, simplex fine. -/
theorem rsp_prt_contrast_pattern :
    rsp_prt_contrasts.all (λ (bad, good) =>
      bad.judgment == .unacceptable && good.judgment == .ok) = true := by
  decide

/-! ### Interpretive transparency -/

/-- Whether the element can receive a non-transparent (idiosyncratic)
interpretation with the verb. Prefixes and particles can (*an-fangen* 'start',
[benz-2025] (161)); RSPs "are always interpreted transparently, in contrast to
particles" (*platt klopfen* 'pound flat', (162)) — RSPs sit outside the
locality domain for allosemy, while particles, though phrasal, are bare
complements not dominated by functional material. -/
def PreverbalElement.canBeNonTransparent : PreverbalElement → Bool
  | .pfx => true
  | .prt => true
  | .rsp => false

/-- Transparency cross-cuts the structural classification: particles pattern
with RSPs structurally (both phrasal) but with prefixes interpretively (both
can be non-transparent). This is the evidence that particles are phrasal yet
local enough for allosemy ([benz-2025] §4.3). -/
theorem transparency_crosscuts_synLevel :
    PreverbalElement.prt.synLevel = PreverbalElement.rsp.synLevel ∧
    PreverbalElement.prt.canBeNonTransparent ≠ PreverbalElement.rsp.canBeNonTransparent :=
  ⟨rfl, by decide⟩

/-! ## Part III: Prefixes in nominalizations (Ch. 5) -/

/-! ### Nominalization types and the structure problem -/

/-- German nominalization types discussed in [benz-2025] Ch. 5:
*-ung* suffixation (*Beobachtung*), *Ge-...-e* circumfixation (*Gerede*),
and the nominalized infinitive (*das Beobachten*). -/
inductive NominalizationType where
  | ung           -- -ung suffixation
  | ge_e          -- Ge-...-e circumfixation
  | nomInfinitive -- nominalized infinitive (das V-en)
  deriving DecidableEq, Repr

/-- A solution to the particle "structure problem" ([luedeling-2001]): how can
a phrasal particle end up inside a derived nominal? [benz-2025] Ch. 5 argues
the three nominalization types favor *different* solutions — reinforcing "the
strange status of particles in the grammar". -/
inductive StructureSolution where
  | phrasalInput    -- the nominalizer takes phrasal structure
  | particleAsHead  -- the particle attaches low, as a head
  | outerAttachment -- the particle attaches outside the nominalizer
  deriving DecidableEq, Repr

/-- The solution each nominalization type favors ([benz-2025] §5.2–5.4):
nominalized infinitives take phrasal inputs (even *das
Durch-den-Wald-Reiten*); *-ung* favors particles-as-heads (particles but not
resultatives occur, and *-ung* needs its input identifiable as complex
change-of-state); *Ge-...-e* favors outer attachment (particles and RSPs
attach outside *Ge-*, (223), while prefixes cannot, and its
no-internal-argument eventive semantics conflicts with prefix verbs'
argument-structural demands). -/
def NominalizationType.solution : NominalizationType → StructureSolution
  | .nomInfinitive => .phrasalInput
  | .ung => .particleAsHead
  | .ge_e => .outerAttachment

/-- Whether the element can attach as a (non-phrasal) head: prefixes always
do; particles can attach low as heads ([benz-2025] §5.3's particles-as-heads
solution); RSPs, "unlike particles, ... cannot be attached non-phrasally"
((205)–(206)). -/
def PreverbalElement.canAttachAsHead : PreverbalElement → Bool
  | .pfx => true
  | .prt => true
  | .rsp => false

/-- Which preverbal elements a structure-problem solution admits: phrasal
inputs admit everything; particles-as-heads admits exactly the head-attachers;
outer attachment admits exactly the phrasal elements (prefixes are verbal
heads and cannot attach outside a noun). -/
def StructureSolution.admits : StructureSolution → PreverbalElement → Bool
  | .phrasalInput, _ => true
  | .particleAsHead, pe => pe.canAttachAsHead
  | .outerAttachment, pe => pe.synLevel == .phrase

/-- The observed distribution ([benz-2025] Ch. 5): *-ung* takes prefixes
(197d–f) and particles (197a–c) but not RSPs ((204) **Platt-hämmer-ung*,
**Wach-küss-ung*); *Ge-...-e* takes particles (212) and (a subset of) RSPs
((216) *das Wach-ge-küss-e*, restricted to non-obligatorily-transitive bases
by its no-internal-argument semantics) but not prefixes ((218) **Ge-be-such-e*,
**Be-ge-such-e*, in either order); nominalized infinitives take all three
((193) *das Ver-kaufen*, *das Ein-führen*, *das Wach-küssen*). -/
def peAcceptable : NominalizationType → PreverbalElement → Bool
  | .ung,           .pfx => true
  | .ung,           .prt => true
  | .ung,           .rsp => false
  | .ge_e,          .pfx => false
  | .ge_e,          .prt => true
  | .ge_e,          .rsp => true
  | .nomInfinitive, _    => true

/-- **The Ch. 5 distribution is derived**: each nominalization type admits
exactly the elements its structure-problem solution can accommodate. The
distribution is a projection of the same head/phrase classification that
drives the Ch. 4 co-occurrence paradigm. -/
theorem peAcceptable_from_solutions (nt : NominalizationType) (pe : PreverbalElement) :
    peAcceptable nt pe = nt.solution.admits pe := by
  cases nt <;> cases pe <;> rfl

/-- Prefixes and RSPs are in complementary distribution across *-ung* and
*Ge-...-e*: head-attachment and outer attachment make opposite demands. -/
theorem pfx_rsp_complementary_ung_ge :
    peAcceptable .ung .pfx = true ∧ peAcceptable .ung .rsp = false ∧
    peAcceptable .ge_e .pfx = false ∧ peAcceptable .ge_e .rsp = true :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Particles occur in both *-ung* and *Ge-...-e* — the dual attachment
options (head or phrase) that constitute the structure problem. -/
theorem prt_accepted_in_both :
    peAcceptable .ung .prt = true ∧ peAcceptable .ge_e .prt = true := ⟨rfl, rfl⟩

/-- Nominalized infinitives accept all three element types ([benz-2025]
(193)). -/
theorem nom_inf_maximally_permissive (pe : PreverbalElement) :
    peAcceptable .nomInfinitive pe = true := by
  cases pe <;> rfl

/-! ### *-ung* and event structure -/

/-- Whether a verb can undergo *-ung* nominalization. [rossdeutscher-kamp-2010]
(endorsed at [benz-2025] §5.3.1): *-ung* requires complex ("bi-eventive")
change-of-state event structure. Over this fragment's entries, the bi-eventive
verbs are the accomplishments (prefix/particle change-of-state verbs); the
simplex deadjectival cases ([benz-2025] (199), *Klär-ung*) are not
represented. -/
def canUngNominalize : Option VendlerClass → Bool
  | some .accomplishment => true
  | _ => false

/-- The (198c) minimal pair: **Mal-ung* vs *Be-mal-ung* — the prefix supplies
the complex change-of-state structure *-ung* needs, derived here from the
fragment entries' Vendler classes. -/
theorem malen_bemalen_ung_contrast :
    canUngNominalize malen.vendlerClass = false ∧
    canUngNominalize bemalen.vendlerClass = true := ⟨rfl, rfl⟩

/-- Simplex activity verbs cannot form *-ung* nominalizations ([benz-2025]
(198): **Mal-ung*, **Arbeit-ung*, **Schieß-ung*; the other fragment activities
pattern identically). -/
theorem simplex_activity_no_ung :
    canUngNominalize haemmern.vendlerClass = false ∧
    canUngNominalize malen.vendlerClass = false ∧
    canUngNominalize kuessen.vendlerClass = false ∧
    canUngNominalize fuehren.vendlerClass = false ∧
    canUngNominalize rauben.vendlerClass = false :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Prefix and particle verbs with complex event structure form *-ung*
nominalizations ([benz-2025] (197): *Ein-führ-ung*, *Ver-bind-ung*; Ch. 3:
*Beobacht-ung*). -/
theorem complex_change_of_state_ung :
    canUngNominalize beobachten.vendlerClass = true ∧
    canUngNominalize einfuehren.vendlerClass = true ∧
    canUngNominalize verbinden.vendlerClass = true :=
  ⟨rfl, rfl, rfl⟩

/-! ### Fragment grounding -/

/-- Transitivity derived from fragment fields (not from a raw string). -/
def isTransitiveVerb (v : GermanVerbEntry) : Bool :=
  v.complementType == .np && !v.unaccusative

/-- The verb classifications in the RSP data are derivable from the fragment
entries' typed fields: changing *frieren*'s `unaccusative` field or
*hämmern*'s `complementType` would break this theorem without touching the
RSP data. -/
theorem rsp_data_grounded_in_fragments :
    isTransitiveVerb haemmern = true ∧
    isTransitiveVerb brechen = true ∧
    frieren.unaccusative = true ∧
    isTransitiveVerb frieren = false := ⟨rfl, rfl, rfl, rfl⟩

/-- *brechen* (result root) and *frieren* (property-concept root) yield
opposite canonical v allosemes, connecting the fragment's `rootType` to
`VAlloseme.fromRootType` and `VAlloseme.introducesEvent`. -/
theorem rootType_alloseme_divergence :
    brechen.rootType.map VAlloseme.fromRootType = some .eventive ∧
    frieren.rootType.map VAlloseme.fromRootType = some .zero ∧
    brechen.rootType.map (VAlloseme.fromRootType · |>.introducesEvent) = some true ∧
    frieren.rootType.map (VAlloseme.fromRootType · |>.introducesEvent) = some false :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- End-to-end for *brechen*: result root → eventive v → with vacuous n, the
complex event reading. -/
theorem brechen_cen_path :
    brechen.rootType.bind
      (λ rt => readingFromAllosemes (VAlloseme.fromRootType rt) .zero) =
      some .complexEvent := rfl

/-- End-to-end for *frieren*: property-concept root → vacuous v → with entity
n, the simple entity reading. Allosemy makes the eventive v available too —
the canonical alloseme is a default, not a constraint. -/
theorem frieren_entity_path :
    frieren.rootType.bind
      (λ rt => readingFromAllosemes (VAlloseme.fromRootType rt) .entity) =
      some .simpleEntity := rfl

end Benz2025
