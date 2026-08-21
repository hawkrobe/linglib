import Linglib.Morphology.DistributedMorphology.Allosemy
import Linglib.Syntax.ConstructionGrammar.Basic
import Linglib.Data.Examples.Benz2025
import Linglib.Fragments.German.Predicates

/-!
# Benz (2025): Structure and Interpretation Across Categories

Three case studies from [benz-2025] (PhD dissertation, University of
Pennsylvania) on the syntax–LF interface in German, all running on the
contextual-allosemy substrate of `DistributedMorphology.Allosemy`. Nominalizations
like *Beobachtung* carry event, referential, and content readings from a
single syntactic structure, with the variation located in the allosemes of v
and n (Ch. 3). The co-occurrence restrictions among prefixes, particles, and
resultative secondary predicates follow from the conjunction of a
phrase-structural factor and an event-structural one, [tenny-1994]'s Single
Delimiting Constraint (Ch. 4, Table 3). The three nominalization types
resolve the particle "structure problem" ([luedeling-2001]) in three
different ways — phrasal inputs, particles-as-heads, outer attachment — from
which the distribution of preverbal elements across them follows (Ch. 5).

The (32), (87)–(89), and (115) stimuli live in `Data.Examples.Benz2025`.
`availableReadings` derives the reading inventory from the exponence engine's
licensed allosemes, with `adopted_unique` characterizing the adopted analysis
as the unique economical derivation of each reading; `blocked_sound` and
`blocked_complete` show the two Ch. 4 principles exactly generate the
co-occurrence paradigm; `peAcceptable_from_solutions` derives the Ch. 5
distribution from the structure-problem solutions.
-/

namespace Benz2025

open DistributedMorphology DistributedMorphology.Allosemy Data.Examples German.Predicates
  ArgumentStructure
open Features (VendlerClass)

/-! ## Content nominalizations (Ch. 3) -/

/-! ### The three readings of *Beobachtung* -/

/-- The (32) stimulus rows, in margin-label order Event, RN, Content. -/
def beobachtungRows : List LinguisticExample :=
  [Examples.ex32a, Examples.ex32b, Examples.ex32c]

/-- The reading a stimulus row exemplifies, from its `reading` feature. The
paper's loose "RN" label is rendered as the simple entity reading. -/
def readingOf (e : LinguisticExample) : Option NominalizationReading :=
  match e.feature? "reading" with
  | some "Event" => some .complexEvent
  | some "RN" => some .simpleEntity
  | some "Content" => some .content
  | _ => none

/-- *Beobachtung* exhibits all three readings ((32)). -/
theorem beobachtung_three_readings :
    beobachtungRows.map readingOf =
      [some .complexEvent, some .simpleEntity, some .content] := rfl

/-- Each (32) example exhibits exactly its characteristic diagnostic —
duration modification for the event reading, pluralization for the RN
reading, CP complementation for the content reading ([grimshaw-1990]-style
diagnostics). -/
theorem beobachtung_diagnostics :
    beobachtungRows.map (λ e =>
        (e.feature? "duration_predicate", e.feature? "plural",
         e.feature? "cp_complement")) =
      [(some "yes", some "no", some "no"),
       (some "no", some "yes", some "no"),
       (some "no", some "no", some "yes")] := rfl

/-! ### Readings from allosemes -/

/-- The alloseme pair deriving each reading on the adopted analysis, where v
is semantically vacuous on all readings but the CEN (§3.5, following
[wood-2023]). By `adopted_roundtrip` and `adopted_unique`, this is the unique
derivation of each reading in which the two heads are not both contentful. -/
def adoptedAllosemes : NominalizationReading → Verbalizer.Alloseme × Nominalizer.Alloseme
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

/-- Among derivations in which the two heads are not both contentful, the
adopted pair is the only one deriving the reading — economy of interpretation
pins the analysis. -/
theorem adopted_unique (r : NominalizationReading) (v : Verbalizer.Alloseme)
    (n : Nominalizer.Alloseme) (hr : readingFromAllosemes v n = some r)
    (h : v.introducesEvent = false ∨ n = .zero) :
    (v, n) = adoptedAllosemes r := by
  revert hr h; revert r v n; decide

/-- The reading pins the division of labor (the "mirror image" claim of
§3.5): an event reading arises only from contentful v with vacuous n, while
a result or content reading forces the corresponding contentful n, whatever
v contributes. -/
theorem reading_determines_contentful_head (v : Verbalizer.Alloseme) (n : Nominalizer.Alloseme) :
    (readingFromAllosemes v n = some .complexEvent →
      v.introducesEvent = true ∧ n = .zero) ∧
    (readingFromAllosemes v n = some .result → n = .result) ∧
    (readingFromAllosemes v n = some .content → n = .content) := by
  revert v n; decide

/-! ### Alloseme selection in the nominalization structure

The selection side is DM's own engine, not a further table: allosemes are
Vocabulary Items over neighborhoods, applicability is the Subset Principle,
and canonical defaults are Elsewhere competition (`winner?`). The readings
available in the (66)/(68) structure [n [v √]] are whatever the licensed
allosemes compose to. -/

/-- v's context in the nominalization structure [n [v √]] — its complement is
the root, event-entailing or not, and it is embedded under n. -/
def vContext (eventive : Bool) : Neighborhood (List Feature) :=
  ⟨[], [if eventive then [.eventive] else []], [[.cat .n]]⟩

/-- n's context in [n [v √]] — a verbal complement, eventive or not. -/
def nContext (eventive : Bool) : Neighborhood (List Feature) :=
  complement (.cat .v :: if eventive then [.eventive] else [])

/-- The readings derivable in the nominalization structure: any licensed v
alloseme composed with any licensed n alloseme. -/
def availableReadings (eventive : Bool) : List NominalizationReading :=
  (licensed Verbalizer.vocabulary (vContext eventive)).flatMap (λ v =>
    (licensed Nominalizer.vocabulary (nContext eventive)).filterMap
      (readingFromAllosemes v))

/-- Over an event-entailing root both v allosemes are licensed — the premise
of the reading ambiguity — while a non-eventive root licenses only vacuous
v. -/
theorem v_allosemes_licensed :
    licensed Verbalizer.vocabulary (vContext true) = [.eventive, .zero] ∧
    licensed Verbalizer.vocabulary (vContext false) = [.zero] := ⟨rfl, rfl⟩

open Morphology.Exponence in
/-- The canonical v alloseme of the root typology is the engine's Elsewhere
winner: the more specified eventive entry beats vacuous v exactly when the
root entails an event, so `Verbalizer.Alloseme.fromRootType` is derived, not
stipulated. -/
theorem fromRootType_is_selectBy_winner (rt : Verb.Root.ChangeType) :
    (winner? Verbalizer.vocabulary (vContext rt.entailsChange)).map (·.exponent) =
      some (Verbalizer.Alloseme.fromRootType rt) := by
  cases rt <;> rfl

/-- Every attested *Beobachtung* reading is available in the single
structure: the engine licenses the allosemes and composition delivers the
readings (Ch. 3's chapter claim). -/
theorem beobachtung_readings_available :
    ∀ r ∈ beobachtungRows.filterMap readingOf, r ∈ availableReadings true := by
  decide

/-- Without an event-entailing root neither the complex event nor the result
reading is derivable; the content reading survives, since simple content
nouns like *Gerücht* 'rumor' need no verbal source (Table 2). -/
theorem nonEventive_readings :
    availableReadings false = [.content, .simpleEvent, .simpleState, .simpleEntity] := rfl

/-! ## Prefixes, particles, and resultatives (Ch. 4) -/

/-! ### The three preverbal-element types -/

/-- The three types of German preverbal elements (Ch. 4). -/
inductive PreverbalElement where
  | pfx  -- inseparable prefix (be-, ent-, er-, ge-, miss-, ver-, zer-)
  | prt  -- separable particle (ab-, an-, auf-, aus-, ein-, ...)
  | rsp  -- resultative secondary predicate (platt, tot, kaputt, ...)
  deriving DecidableEq, Repr

/-- A morphological element is either a head (X⁰) or a phrase (XP). -/
inductive SynLevel where
  | head    -- X⁰: can occur inside a complex head
  | phrase  -- XP: cannot incorporate
  deriving DecidableEq, Repr

/-- Prefixes are heads forming a complex head with the root (inseparable under
V2 movement), while particles and RSPs are phrasal (stranded under V2).
Following [wurmbrand-1998] and [zeller-2001], particles are phrasal
complements of the verb not dominated by further functional material. -/
def PreverbalElement.synLevel : PreverbalElement → SynLevel
  | .pfx => .head
  | .prt => .phrase
  | .rsp => .phrase

/-- Whether an element obligatorily introduces a result-state specification.
Prefixes and RSPs always specify a result state, while particles can have
non-delimiting (directional, completive) readings (§4.4). -/
inductive ResultStateSpec where
  | specifies  -- obligatorily introduces a result state
  | neutral    -- has non-delimiting readings
  deriving DecidableEq, Repr

def PreverbalElement.resultSpec : PreverbalElement → ResultStateSpec
  | .pfx => .specifies
  | .prt => .neutral
  | .rsp => .specifies

/-! ### The two compatibility factors -/

/-- Structural combinability of an outer and an inner element, the inner one
closer to the root. A phrasal inner element is impossible, since a head
outside it cannot form a complex head with the root, and a phrasal outer
element competes with it for the verb's single complement position (§4.4). -/
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

/-- Two elements that both obligatorily specify a result state cannot
co-occur, since the end state of a complex event can only be specified once —
[tenny-1994]'s Single Delimiting Constraint (p. 79, quoted at (159)). -/
def resultStatesCompatible (a b : ResultStateSpec) : Bool :=
  match a, b with
  | .specifies, .specifies => false
  | _, _ => true

def structurallyCompatible (outer inner : PreverbalElement) : Bool :=
  incorporationAllowed outer.synLevel inner.synLevel

def interpretivelyCompatible (outer inner : PreverbalElement) : Bool :=
  resultStatesCompatible outer.resultSpec inner.resultSpec

/-- A combination is predicted possible iff both factors permit it (§4.4). -/
def predictedAllowed (outer inner : PreverbalElement) : Bool :=
  structurallyCompatible outer inner && interpretivelyCompatible outer inner

/-! ### Prefix and particle inventory (Table 4) -/

/-- German inseparable prefixes (Table 4). *ge-* is the rare non-participial
prefix (*ge-bären*, *ge-denken*, *ge-fallen*). -/
def inseparablePrefixes : List String :=
  ["be", "ent", "er", "ge", "miss", "ver", "zer"]

/-- German prepositional separable particles (Table 4, which additionally
lists nominal and adjectival particles like *klavier-*, *rad-*, *leicht-*,
whose classification is controversial). -/
def separableParticles : List String :=
  ["ab", "an", "auf", "aus", "bei", "ein", "los", "nach", "vor", "zu"]

/-- Elements occurring both as prefix and as particle (Table 4). -/
def ambiguousElements : List String :=
  ["durch", "hinter", "über", "um", "unter", "wider"]

/-- The ambiguous elements appear in neither pure inventory. -/
theorem ambiguous_not_pure :
    ambiguousElements.all (λ e =>
      !inseparablePrefixes.contains e && !separableParticles.contains e) = true := by
  decide

/-! ### The co-occurrence paradigm (Table 3) -/

/-- A cell of Table 3's factor columns, recording whether the factor predicts
the combination to be possible. `particleDependent` renders the table's
parenthesized check mark, a prediction that depends on the specific particles
involved (§4.1). -/
inductive FactorVerdict where
  | predicts           -- ✓: factor predicts the combination possible
  | particleDependent  -- (✓): possible for result-neutral particles
  | excludes           -- ✗: factor predicts the combination impossible
  deriving DecidableEq, Repr

/-- Boolean reading of a factor cell, on which `particleDependent` counts as
possible since the generic classification treats particles as
result-neutral. -/
def FactorVerdict.possible : FactorVerdict → Bool
  | .predicts => true
  | .particleDependent => true
  | .excludes => false

/-- A row of Table 3 (repeated as Table 5). The printed table's final row
merges pfx-RSP and PRT-RSP into one row "pfx/PRT-RSP", rendered here by a
two-element `outers` list. -/
structure CooccurrenceRow where
  /-- The outer element(s) of the printed row. -/
  outers : List PreverbalElement
  /-- The inner element, closer to the root. -/
  inner : PreverbalElement
  /-- The Allowed column. -/
  allowed : Bool
  /-- The Structure Predicts column. -/
  structureVerdict : FactorVerdict
  /-- The Interpretation Predicts column. -/
  interpretationVerdict : FactorVerdict
  deriving Repr, BEq

/-- Table 3, cell for cell. -/
def cooccurrenceTable : List CooccurrenceRow := [
  -- pfx-pfx ((81) *ent-ver-trauen)
  { outers := [.pfx], inner := .pfx, allowed := false
  , structureVerdict := .predicts, interpretationVerdict := .excludes },
  -- pfx-PRT ((83) *zer-ab-schneiden)
  { outers := [.pfx], inner := .prt, allowed := false
  , structureVerdict := .excludes, interpretationVerdict := .particleDependent },
  -- PRT-pfx ((84) aus-er-wählen, an-ver-trauen, vor-ent-halten)
  { outers := [.prt], inner := .pfx, allowed := true
  , structureVerdict := .predicts, interpretationVerdict := .particleDependent },
  -- PRT-PRT ((82) *rad-ein-fahren)
  { outers := [.prt], inner := .prt, allowed := false
  , structureVerdict := .excludes, interpretationVerdict := .particleDependent },
  -- RSP-pfx ((87) *arm be-raubt)
  { outers := [.rsp], inner := .pfx, allowed := false
  , structureVerdict := .predicts, interpretationVerdict := .excludes },
  -- RSP-PRT ((88) *nass an-gespuckt)
  { outers := [.rsp], inner := .prt, allowed := false
  , structureVerdict := .excludes, interpretationVerdict := .particleDependent },
  -- RSP-RSP ((86) *sich kaputt müde gearbeitet)
  { outers := [.rsp], inner := .rsp, allowed := false
  , structureVerdict := .excludes, interpretationVerdict := .excludes },
  -- pfx/PRT-RSP (merged in the printed table)
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
interpretively excluded. For PRT-RSP the structural factor does the work,
while only "some RSP-particle verbs are additionally also ruled out
semantically" (§4.4). -/
theorem prt_rsp_interpretation_particle_dependent :
    structurallyCompatible .prt .rsp = false ∧
    interpretivelyCompatible .prt .rsp = true := ⟨rfl, rfl⟩

/-- PRT-pfx is the unique allowed combination ((84) *aus-er-wählen*,
*an-ver-trauen*, *vor-ent-halten*, *um-ent-scheiden*, *ab-er-kennen*). -/
theorem prt_pfx_uniquely_allowed :
    (cooccurrenceTable.filter (·.allowed)).map (λ r => (r.outers, r.inner)) =
      [([.prt], .pfx)] := by decide

/-- Neither factor alone predicts the paradigm — structure alone misses the
double-delimitation rows (pfx-pfx, RSP-pfx) and interpretation alone misses
the phrase-structure rows (pfx-PRT, PRT-PRT, RSP-PRT). -/
theorem two_factors_needed :
    (cooccurrenceTable.any (λ r => r.structureVerdict.possible && !r.allowed)) = true ∧
    (cooccurrenceTable.any (λ r => r.interpretationVerdict.possible && !r.allowed)) = true := by
  constructor <;> decide

/-! ### Blocking derivations -/

/-- A proof that a preverbal-element combination violates one of the two
principles. Soundness and completeness against `predictedAllowed` show the
two principles exactly generate the paradigm. -/
inductive Blocked : PreverbalElement → PreverbalElement → Prop where
  /-- A phrasal element cannot occupy the inner position, since a head
  outside it cannot form a complex head with the root and a phrasal outer
  competes for the verb's single complement position (§4.4). -/
  | byPhrasalInner {o i : PreverbalElement} :
      i.synLevel = .phrase → Blocked o i
  /-- Two obligatory result-state specifiers conflict, since the end state of
  a complex event can only be specified once ([tenny-1994]'s Single
  Delimiting Constraint, (159)). -/
  | bySingleDelimiting {o i : PreverbalElement} :
      o.resultSpec = .specifies → i.resultSpec = .specifies → Blocked o i

/-- Every blocking derivation corresponds to a predicted-blocked combination —
the theory does not over-generate. -/
theorem blocked_sound {o i : PreverbalElement} (h : Blocked o i) :
    predictedAllowed o i = false := by
  cases h with
  | byPhrasalInner hi =>
      cases o <;> cases i <;> first | rfl | exact absurd hi (by decide)
  | bySingleDelimiting ho _ =>
      cases o <;> cases i <;> first | rfl | exact absurd ho (by decide)

/-- Every blocked combination has a derivation — the two principles account
for all restrictions. -/
theorem blocked_complete {o i : PreverbalElement}
    (h : predictedAllowed o i = false) : Blocked o i := by
  cases o <;> cases i <;>
    first
    | exact .byPhrasalInner rfl
    | exact .bySingleDelimiting rfl rfl
    | exact absurd h (by decide)

/-- The allowed combination has no derivation, since the prefix is a head and
the particle is result-neutral. -/
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

/-- A CxG bar level in `SynLevel` terms, where zero-level positions are head
sites and bar- and phrase-level positions are phrasal. -/
def SynLevel.ofBarLevel : ConstructionGrammar.BarLevel → SynLevel
  | .zero => .head
  | .bar => .phrase
  | .phrase => .phrase

/-- The `SynLevel` of a CxG slot filler. Word fillers are heads, phrasal
fillers (with or without a fixed head) are phrases, and SEM+ fillers are
level-unspecified. -/
def _root_.ConstructionGrammar.SlotFiller.synLevel :
    ConstructionGrammar.SlotFiller String → Option SynLevel
  | .fixed _ => some .head
  | .open_ _ => some .head
  | .headed _ _ => some .phrase
  | .phrasal => some .phrase
  | .semantic _ => none

/-- A phrase in a word-level slot occupies the banned cell — its site is a
head and its filler a phrase, so `incorporationAllowed` rejects the pair. The
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

Complex predicate semantics after [williams-2015], adopted at (158):
⟦v⟧ = λx λe₁ ∃e₂ ∃s. Means(e₁,e₂) & Pred₁(e₂) & Theme(e₁,x) & End(e₁,s) &
Pred₂(s), where the M(eans) predicate is the verb, the R(esult) predicate the
RSP, and the End Theme Postulate (108) links the complex event's Theme to the
end state. See `Causation.Resultatives` for the complementary causal-dynamics
analysis. -/

/-- The resultative stimulus rows ((89), (115); the (115) rows are due to
[creemers-2020]). -/
def rspRows : List LinguisticExample :=
  [Examples.ex89a, Examples.ex89b, Examples.ex115a, Examples.ex115e, Examples.ex115f]

/-- German allows non-unergative M predicates in resultatives ((115)),
against weak-resultative reanalyses of the whole class. -/
theorem german_allows_non_unergative_M :
    [Examples.ex115a, Examples.ex115e, Examples.ex115f].map (·.feature? "verb_class") =
      [some "obligatorily transitive", some "unaccusative", some "inherently reflexive"] ∧
    rspRows.all (·.judgment == .acceptable) = true := ⟨rfl, rfl⟩

/-! ### RSP co-occurrence contrasts (§4.1) -/

/-- RSPs are incompatible with prefixed verbs, while the same RSP with the
simplex verb is fine ((87), from [creemers-2020]). Each row's grammatical
baseline carries its ungrammatical prefixed alternative, and the *ge-* of the
baselines is participial, not a prefix in the relevant sense. -/
theorem rsp_pfx_contrast_pattern :
    [Examples.ex87ab, Examples.ex87cd, Examples.ex87ef].all (λ e =>
      e.feature? "blocker_type" == some "prefix" &&
      e.judgment == .acceptable &&
      !e.alternatives.isEmpty &&
      e.alternatives.all (·.2 == .ungrammatical)) = true := by decide

/-- RSPs are likewise incompatible with particle verbs ((88)), including
particles not characterizable as resultative, like *an-* in (88d). -/
theorem rsp_prt_contrast_pattern :
    [Examples.ex88ab, Examples.ex88cd].all (λ e =>
      e.feature? "blocker_type" == some "particle" &&
      e.judgment == .acceptable &&
      !e.alternatives.isEmpty &&
      e.alternatives.all (·.2 == .ungrammatical)) = true := by decide

/-! ### Interpretive transparency -/

/-- Whether the element can receive a non-transparent interpretation with the
verb ((161) *an-fangen* 'start' vs. (162) *platt klopfen* 'pound flat'). RSPs
are always interpreted transparently since they sit outside the locality
domain for allosemy, while particles are bare phrasal complements local
enough for it. -/
def PreverbalElement.canBeNonTransparent : PreverbalElement → Bool
  | .pfx => true
  | .prt => true
  | .rsp => false

/-- Particles pattern with RSPs structurally (both phrasal) but with prefixes
interpretively (both can be non-transparent) — the evidence that particles
are phrasal yet local enough for allosemy (§4.3). -/
theorem transparency_crosscuts_synLevel :
    PreverbalElement.prt.synLevel = PreverbalElement.rsp.synLevel ∧
    PreverbalElement.prt.canBeNonTransparent ≠ PreverbalElement.rsp.canBeNonTransparent :=
  ⟨rfl, by decide⟩

/-! ## Prefixes in nominalizations (Ch. 5) -/

/-! ### Nominalization types and the structure problem -/

/-- The three German nominalization types discussed in Ch. 5. -/
inductive NominalizationType where
  | ung           -- -ung suffixation (Beobachtung)
  | ge_e          -- Ge-...-e circumfixation (Gerede)
  | nomInfinitive -- nominalized infinitive (das Beobachten)
  deriving DecidableEq, Repr

/-- A solution to the particle "structure problem" ([luedeling-2001]) — how a
phrasal particle can end up inside a derived nominal. Ch. 5 argues the three
nominalization types favor different solutions, reinforcing "the strange
status of particles in the grammar". -/
inductive StructureSolution where
  | phrasalInput    -- the nominalizer takes phrasal structure
  | particleAsHead  -- the particle attaches low, as a head
  | outerAttachment -- the particle attaches outside the nominalizer
  deriving DecidableEq, Repr

/-- The solution each nominalization type favors (§5.2–5.4). Nominalized
infinitives take phrasal inputs (even *das Durch-den-Wald-Reiten*), *-ung*
favors particles-as-heads, and *Ge-...-e* favors outer attachment ((223)),
since its no-internal-argument eventive semantics conflicts with prefix
verbs' argument-structural demands. -/
def NominalizationType.solution : NominalizationType → StructureSolution
  | .nomInfinitive => .phrasalInput
  | .ung => .particleAsHead
  | .ge_e => .outerAttachment

/-- Whether the element can attach as a non-phrasal head. Prefixes always do,
particles can attach low as heads (§5.3), and RSPs cannot be attached
non-phrasally ((205)–(206)). -/
def PreverbalElement.canAttachAsHead : PreverbalElement → Bool
  | .pfx => true
  | .prt => true
  | .rsp => false

/-- The preverbal elements a structure-problem solution accommodates. Phrasal
inputs admit everything, particles-as-heads admits the head-attachers, and
outer attachment admits the phrasal elements, since prefixes are verbal heads
and cannot attach outside a noun. -/
def StructureSolution.admits : StructureSolution → PreverbalElement → Bool
  | .phrasalInput, _ => true
  | .particleAsHead, pe => pe.canAttachAsHead
  | .outerAttachment, pe => pe.synLevel == .phrase

/-- The observed Ch. 5 distribution. *-ung* takes prefixes and particles but
not RSPs ((197), (204) **Platt-hämmer-ung*). *Ge-...-e* takes particles
((212)) and a subset of RSPs ((216) *das Wach-ge-küss-e*, restricted to
non-obligatorily-transitive bases) but not prefixes ((218) **Ge-be-such-e*,
in either affix order). Nominalized infinitives take all three ((193)). -/
def peAcceptable : NominalizationType → PreverbalElement → Bool
  | .ung,           .pfx => true
  | .ung,           .prt => true
  | .ung,           .rsp => false
  | .ge_e,          .pfx => false
  | .ge_e,          .prt => true
  | .ge_e,          .rsp => true
  | .nomInfinitive, _    => true

/-- Each nominalization type admits exactly the elements its
structure-problem solution accommodates — the Ch. 5 distribution projects the
same head/phrase classification that drives the Ch. 4 paradigm. -/
theorem peAcceptable_from_solutions (nt : NominalizationType) (pe : PreverbalElement) :
    peAcceptable nt pe = nt.solution.admits pe := by
  cases nt <;> cases pe <;> rfl

/-- Prefixes and RSPs are in complementary distribution across *-ung* and
*Ge-...-e*, since head attachment and outer attachment make opposite
demands. -/
theorem pfx_rsp_complementary_ung_ge :
    peAcceptable .ung .pfx = true ∧ peAcceptable .ung .rsp = false ∧
    peAcceptable .ge_e .pfx = false ∧ peAcceptable .ge_e .rsp = true :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Particles occur in both *-ung* and *Ge-...-e* — the dual attachment
options (head or phrase) that constitute the structure problem. -/
theorem prt_accepted_in_both :
    peAcceptable .ung .prt = true ∧ peAcceptable .ge_e .prt = true := ⟨rfl, rfl⟩

/-- Nominalized infinitives accept all three element types ((193)). -/
theorem nom_inf_maximally_permissive (pe : PreverbalElement) :
    peAcceptable .nomInfinitive pe = true := by
  cases pe <;> rfl

/-! ### *-ung* and event structure -/

/-- Whether a verb can undergo *-ung* nominalization, which requires complex
("bi-eventive") change-of-state event structure ([rossdeutscher-kamp-2010],
endorsed at §5.3.1). Over this fragment's entries the bi-eventive verbs are
the accomplishments (the simplex deadjectival cases of (199) are not
represented). -/
def canUngNominalize : Option VendlerClass → Bool
  | some .accomplishment => true
  | _ => false

/-- In the (198c) minimal pair **Mal-ung* vs *Be-mal-ung*, the prefix
supplies the complex change-of-state structure *-ung* needs, derived here
from the fragment entries' Vendler classes. -/
theorem malen_bemalen_ung_contrast :
    canUngNominalize malen.vendlerClass = false ∧
    canUngNominalize bemalen.vendlerClass = true := ⟨rfl, rfl⟩

/-- Simplex activity verbs cannot form *-ung* nominalizations ((198)
**Mal-ung*, **Arbeit-ung*, **Schieß-ung*; the other fragment activities
pattern identically). -/
theorem simplex_activity_no_ung :
    canUngNominalize haemmern.vendlerClass = false ∧
    canUngNominalize malen.vendlerClass = false ∧
    canUngNominalize kuessen.vendlerClass = false ∧
    canUngNominalize fuehren.vendlerClass = false ∧
    canUngNominalize rauben.vendlerClass = false :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Prefix and particle verbs with complex event structure form *-ung*
nominalizations ((197) *Ein-führ-ung*, *Ver-bind-ung*; Ch. 3
*Beobacht-ung*). -/
theorem complex_change_of_state_ung :
    canUngNominalize beobachten.vendlerClass = true ∧
    canUngNominalize einfuehren.vendlerClass = true ∧
    canUngNominalize verbinden.vendlerClass = true :=
  ⟨rfl, rfl, rfl⟩

/-! ### Fragment grounding -/

/-- Transitivity derived from the fragment entry's typed fields. -/
def isTransitiveVerb (v : GermanVerbEntry) : Bool :=
  v.complementType == .np && !v.unaccusative

/-- The stimulus rows' `verb_class` labels are derivable from the fragment
entries their `m_predicate` features name, so changing *frieren*'s
`unaccusative` field or *hämmern*'s `complementType` would break this theorem
without touching the rows. -/
theorem rsp_data_grounded_in_fragments :
    (Examples.ex89a.feature? "m_predicate" = some haemmern.form ∧
      isTransitiveVerb haemmern = true) ∧
    (Examples.ex115a.feature? "m_predicate" = some brechen.form ∧
      isTransitiveVerb brechen = true) ∧
    (Examples.ex115e.feature? "m_predicate" = some frieren.form ∧
      frieren.unaccusative = true ∧ isTransitiveVerb frieren = false) :=
  ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl, rfl⟩

/-- *brechen* (result root) and *frieren* (property-concept root) yield
opposite canonical v allosemes, connecting the fragment's `rootType` to
`Verbalizer.Alloseme.fromRootType` and `Verbalizer.Alloseme.introducesEvent`. -/
theorem rootType_alloseme_divergence :
    brechen.rootType.map Verbalizer.Alloseme.fromRootType = some .eventive ∧
    frieren.rootType.map Verbalizer.Alloseme.fromRootType = some .zero ∧
    brechen.rootType.map (Verbalizer.Alloseme.fromRootType · |>.introducesEvent) = some true ∧
    frieren.rootType.map (Verbalizer.Alloseme.fromRootType · |>.introducesEvent) = some false :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- A result root selects eventive v, which with vacuous n yields *brechen*'s
complex event reading. -/
theorem brechen_cen_path :
    brechen.rootType.bind
      (λ rt => readingFromAllosemes (Verbalizer.Alloseme.fromRootType rt) .zero) =
      some .complexEvent := rfl

/-- A property-concept root selects vacuous v, which with entity n yields
*frieren*'s simple entity reading. Allosemy leaves the eventive v available
too, since the canonical alloseme is a default rather than a constraint. -/
theorem frieren_entity_path :
    frieren.rootType.bind
      (λ rt => readingFromAllosemes (Verbalizer.Alloseme.fromRootType rt) .entity) =
      some .simpleEntity := rfl

end Benz2025
