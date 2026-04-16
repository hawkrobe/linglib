import Linglib.Theories.Semantics.Tense.Aspect.Core

/-!
# @cite{del-prete-2013} — Imperfectivity and Habituality in Italian

Fabio Del Prete, ch. 8 of *Genericity* (Mari, Beyssade, Del Prete eds.),
OUP, Oxford Studies in Theoretical Linguistics 43.

## Core Claim

The Italian Imperfetto (imperfective past) admits both habitual (HAB) and
progressive (PROG) readings. The chapter's key empirical contribution is
the **Same-Object Effect** (SOE): bare imperfectives with a singular
indefinite in object position show an implication that the same object is
involved across habitual events — e.g., "Gianni guidava un'auto sportiva"
implies the same sports car each time. When this same-object reading is
implausible (e.g., reading the same philosophy book repeatedly), HAB is
blocked while PROG survives.

## Chapter Sections Covered

- **§8.1**: Introduction — HAB/PROG readings, temporal anchoring (exx. 1–3)
- **§8.2**: GEN analysis and its inadequacy for SOEs (exx. 4–10)
- **§8.3**: Bare plural objects and 'kind-coerced' singular indefinites (exx. 11–14)
- **§8.4**: Semantic framework — PBT, LCH, IMPF (exx. 15–27) [concepts only]
- **§8.5**: SOE for bare imperfectives (exx. 22–27) [concepts only]
- **§8.6**: SOE, Q-adverbs, and bare plurals (exx. 28–30) [data]
- **§8.7**: Oddness explained via common knowledge (principle (O))
- **§8.8**: Conclusion

## Argument Structure

Del Prete argues the standard covert-quantifier GEN analysis (§8.2) cannot
account for the asymmetric distribution of SOEs across bare imperfectives
and their adverbially-quantified/bare-plural counterparts, unless one makes
stipulative assumptions about scope interactions between indefinites and GEN.

The proposed alternative (§8.4) is a **non-quantificational**, plurality-based
analysis: HAB readings arise from event plurality under the Lexical
Cumulativity Hypothesis (LCH; Kratzer 2008) combined with IMPF's
forward-expansion of the reference time in a Partial Branching Time (PBT)
model. The SOE is then derived as an entailment of the Sameness of Singular
Participant principle (SSP), and the oddness of (2b) on HAB follows from
the SOE conflicting with common knowledge (§8.7).

## Connection to Existing Infrastructure

1. **`ViewpointAspectB`** (`Tense/Aspect/Core.lean`): imperfective/perfective
   distinction. The `IMPF` operator formalizes the same TT⊂TSit relation
   that Del Prete uses as the starting point for his f-exp analysis.

2. **`Fragments/Italian/Tense.lean`**: `imperfetto` TAMEEntry — the tense
   form that this chapter is about.

3. **@cite{boneh-doron-2013}** (`BonehDoron2013.lean`): Boneh & Doron's HAB/GEN
   distinction in ch. 6 of the same volume. Del Prete's analysis is
   explicitly built on their modal analysis of HAB (§8.4, eq. 41).
   Their English same-object data (exx. 6b, 7b) parallels Del Prete's
   Italian SOEs — formalized as `sameObjectParallel` in BonehDoron2013.
-/

namespace DelPrete2013

open Semantics.Tense.Aspect.Core (ViewpointAspectB)

-- ═══ Reading Types ═══

/-- The two readings available for the Italian Imperfetto.

    @cite{del-prete-2013} §8.1: Imperfetto sentences "can have both
    habitual (HAB) and progressive (PROG) readings, in correlation
    with whether temporal anchoring is to a large or to a small
    reference time." -/
inductive ImperfettoReading where
  /-- Habitual: "Gianni used to read the newspaper." Temporal
      anchoring to a large reference time. -/
  | hab
  /-- Progressive: "Gianni was reading the newspaper." Temporal
      anchoring to a small reference time. -/
  | prog
  deriving DecidableEq, Repr

-- ═══ Object Type ═══

/-- The type of the object NP, which determines SOE behavior.

    @cite{del-prete-2013} §8.1, §8.3, §8.5: The crucial variable is
    whether the object is a singular indefinite (triggers SOE), a bare
    plural (no SOE, analyzed as kind-denoting), or a definite (no SOE). -/
inductive ObjectType where
  /-- Definite: "il giornale" (the newspaper) -/
  | definite
  /-- Singular indefinite: "un'auto sportiva" (a sports car) -/
  | singularIndefinite
  /-- Bare plural: "libri di filosofia" (philosophy books) -/
  | barePlural
  /-- No object (intransitive or PP complement) -/
  | none
  deriving DecidableEq, Repr

-- ═══ Same-Object Effect (SOE) ═══

/-- Whether a sentence displays a Same-Object Effect on its HAB reading.

    @cite{del-prete-2013} §8.1, §8.5: Singular indefinites in object
    position under Imperfetto trigger SOEs — the object must be
    the same across habitual events. When this is implausible, the
    HAB reading is blocked. -/
inductive SOEStatus where
  /-- SOE present and plausible (same object across events is natural). -/
  | plausible
  /-- SOE present but implausible (same object across events is odd). -/
  | implausible
  /-- Kind-level SOE: same *kind* of object, not same individual. -/
  | kindLevel
  /-- No SOE (bare plural, definite, or no object). -/
  | absent
  deriving DecidableEq, Repr

/-- An Italian imperfective datum from @cite{del-prete-2013}. -/
structure ItalianDatum where
  italian : String
  gloss : String
  aspect : ViewpointAspectB
  objectType : ObjectType
  habOK : Bool     -- HAB reading available?
  progOK : Bool    -- PROG reading available?
  soe : SOEStatus  -- Same-Object Effect status
  exNumber : String -- example number in the chapter
  deriving Repr

-- ═══ Data from the Chapter ═══

/-- Ex. (1): "Gianni leggeva il giornale" — definite object, no SOE issue.
    Both HAB and PROG are fine. -/
def gianniLeggeva : ItalianDatum :=
  { italian := "Gianni leggeva il giornale"
  , gloss := "Gianni read(Imp, 3sg) the newspaper"
  , aspect := .imperfective
  , objectType := .definite
  , habOK := true
  , progOK := true
  , soe := .absent
  , exNumber := "(1)"
  }

/-- Ex. (2a): "Gianni guidava un'auto sportiva" — singular indefinite,
    SOE plausible (one can habitually drive the same sports car).
    Both HAB and PROG are fine. -/
def gianniGuidava : ItalianDatum :=
  { italian := "Gianni guidava un'auto sportiva"
  , gloss := "Gianni drive(Imp, 3sg) a car sports"
  , aspect := .imperfective
  , objectType := .singularIndefinite
  , habOK := true
  , progOK := true
  , soe := .plausible
  , exNumber := "(2a)"
  }

/-- Ex. (2b): "Gianni leggeva un libro di filosofia" — singular indefinite,
    SOE implausible (reading the same philosophy book repeatedly is odd).
    HAB is blocked (#); only PROG survives. -/
def gianniLeggevaFilosofia : ItalianDatum :=
  { italian := "Gianni leggeva un libro di filosofia"
  , gloss := "Gianni read(Imp, 3sg) a book of philosophy"
  , aspect := .imperfective
  , objectType := .singularIndefinite
  , habOK := false
  , progOK := true
  , soe := .implausible
  , exNumber := "(2b)"
  }

/-- Ex. (3): "Gianni fumava un sigaro toscano (il Toscanello)" —
    singular indefinite, but SOE is at the *kind* level (a kind of
    Tuscan cigar, not an individual cigar). HAB is fine because
    the kind-level SOE is plausible.

    This is a key data point: SOEs can be satisfied at the kind level
    when the indefinite is coerced to a kind-reading. -/
def gianniFumavaSigaro : ItalianDatum :=
  { italian := "Gianni fumava un sigaro toscano (il Toscanello)"
  , gloss := "Gianni smoke(Imp, 3sg) a cigar Tuscan (the Toscanello)"
  , aspect := .imperfective
  , objectType := .singularIndefinite
  , habOK := true
  , progOK := true
  , soe := .kindLevel
  , exNumber := "(3)"
  }

/-- Ex. (4a): "Gianni viaggia in treno" — bare habitual (present tense,
    no object). Both HAB and PROG available (here we record the generic
    habitual reading). No SOE issue (intransitive). -/
def gianniViaggia : ItalianDatum :=
  { italian := "Gianni viaggia in treno"
  , gloss := "Gianni travel(Pres, 3sg) by train"
  , aspect := .imperfective
  , objectType := .none
  , habOK := true
  , progOK := true
  , soe := .absent
  , exNumber := "(4a)"
  }

/-- Ex. (11): "Gianni leggeva libri di filosofia" — bare plural object,
    no SOE. HAB is fine; PROG is marginal (#).
    Key contrast with (2b): bare plural rescues HAB. -/
def gianniLeggevaLibri : ItalianDatum :=
  { italian := "Gianni leggeva libri di filosofia"
  , gloss := "Gianni read(Imp, 3sg) books of philosophy"
  , aspect := .imperfective
  , objectType := .barePlural
  , habOK := true
  , progOK := false
  , soe := .absent
  , exNumber := "(11)"
  }

/-- Ex. (8)/(29): "Gianni leggeva sempre un libro di filosofia" —
    same predicate as (2b) but with Q-adverb *sempre* 'always'.
    HAB is now fine (✓). The Q-adverb provides a tripartite
    quantificational structure at LF (§8.6), so the singular
    indefinite scopes below the Q-adverb and no SOE arises.

    This is the key contrast with (2b): adding *sempre* rescues HAB
    for the same sentence frame. -/
def gianniLeggeva_sempre : ItalianDatum :=
  { italian := "Gianni leggeva sempre un libro di filosofia"
  , gloss := "Gianni read(Imp, 3sg) always a book of philosophy"
  , aspect := .imperfective
  , objectType := .singularIndefinite
  , habOK := true
  , progOK := true
  , soe := .absent  -- Q-adverb absorbs the SOE
  , exNumber := "(8)/(29)"
  }

def italianData : List ItalianDatum :=
  [ gianniLeggeva, gianniGuidava, gianniLeggevaFilosofia
  , gianniFumavaSigaro, gianniViaggia
  , gianniLeggevaLibri, gianniLeggeva_sempre ]

-- ═══ Key Predictions ═══

/-- All examples are imperfective (the chapter studies the Imperfetto). -/
theorem all_imperfective :
    italianData.all (λ d => d.aspect == .imperfective) := by
  native_decide

/-- The SOE contrast: when SOE is implausible, HAB is blocked.
    (2a) with plausible SOE → HAB ✓; (2b) with implausible SOE → HAB ✗. -/
theorem soe_blocks_hab :
    gianniGuidava.soe == .plausible ∧ gianniGuidava.habOK = true ∧
    gianniLeggevaFilosofia.soe == .implausible ∧ gianniLeggevaFilosofia.habOK = false := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The bare plural rescue: (2b) sing. indef. blocks HAB, but
    (11) bare plural with same predicate allows HAB. -/
theorem bare_plural_rescues_hab :
    gianniLeggevaFilosofia.habOK = false ∧
    gianniLeggevaLibri.habOK = true := by
  exact ⟨rfl, rfl⟩

/-- The Q-adverb rescue (§8.6): "sempre" rescues HAB for the same
    sentence frame where bare Imperfetto blocks it.
    (2b) without Q-adverb: HAB ✗; (29) with *sempre*: HAB ✓. -/
theorem qadverb_rescues_hab :
    gianniLeggevaFilosofia.habOK = false ∧
    gianniLeggeva_sempre.habOK = true := by
  exact ⟨rfl, rfl⟩

/-- The HAB/PROG complementarity for the SOE contrast:
    sing. indef. with implausible SOE: HAB ✗, PROG ✓
    bare plural: HAB ✓, PROG ✗ -/
theorem hab_prog_complementarity :
    gianniLeggevaFilosofia.habOK = false ∧ gianniLeggevaFilosofia.progOK = true ∧
    gianniLeggevaLibri.habOK = true ∧ gianniLeggevaLibri.progOK = false := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Definite object: both readings available, no SOE. -/
theorem definite_object_both_readings :
    gianniLeggeva.habOK = true ∧ gianniLeggeva.progOK = true ∧
    gianniLeggeva.soe == .absent ∧ gianniLeggeva.objectType == .definite := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Kind-level SOE: singular indefinite with kind coercion permits HAB
    because the SOE is satisfied at the kind level. -/
theorem kind_level_soe_permits_hab :
    gianniFumavaSigaro.soe == .kindLevel ∧
    gianniFumavaSigaro.habOK = true ∧
    gianniFumavaSigaro.objectType == .singularIndefinite := by
  exact ⟨rfl, rfl, rfl⟩

/-- In bare imperfectives (without Q-adverbs), singular indefinites
    trigger SOEs while other object types do not.
    The Q-adverb case (8)/(29) is excluded: a singular indefinite under
    *sempre* scopes below the Q-adverb, so no SOE arises. -/
theorem bare_indef_triggers_soe :
    -- Singular indefinites in bare imperfectives trigger SOEs
    gianniGuidava.objectType == .singularIndefinite ∧
    gianniGuidava.soe != .absent ∧
    gianniLeggevaFilosofia.objectType == .singularIndefinite ∧
    gianniLeggevaFilosofia.soe != .absent ∧
    gianniFumavaSigaro.objectType == .singularIndefinite ∧
    gianniFumavaSigaro.soe != .absent ∧
    -- Non-singular-indefinite objects in bare imperfectives: no SOE
    gianniLeggeva.objectType == .definite ∧
    gianniLeggeva.soe == .absent ∧
    gianniLeggevaLibri.objectType == .barePlural ∧
    gianniLeggevaLibri.soe == .absent := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩


-- ═══ §8.2: Critique of the GEN Analysis ═══

/-- The two problematic scope assumptions that the GEN analysis must
    make to explain the SOE data.

    @cite{del-prete-2013} §8.2, discussion around exx. (7)–(8): the GEN
    approach requires:
    (α1) Singular indefinites obligatorily scope above GEN
    (α2) Singular indefinites *can* scope below overt Q-adverbs

    The problem is that GEN is supposed to be a phonologically silent
    version of *sempre* 'always', and should have the same syntactic
    properties — making (α1) and (α2) contradictory. -/
structure GENScopeAssumption where
  label : String
  assumption : String
  problematic : Bool
  deriving Repr

def alpha1 : GENScopeAssumption :=
  { label := "α1"
  , assumption := "Singular indefinites obligatorily scope above GEN"
  , problematic := true }

def alpha2 : GENScopeAssumption :=
  { label := "α2"
  , assumption := "Singular indefinites can scope below overt Q-adverbs"
  , problematic := true }

/-- Both assumptions are needed but create a contradictory picture:
    GEN is supposed to be a covert *sempre* but doesn't behave like
    one with respect to scope of indefinites. -/
theorem gen_scope_assumptions_contradictory :
    alpha1.problematic = true ∧ alpha2.problematic = true := ⟨rfl, rfl⟩


-- ═══ §8.4: Key Theoretical Concepts (Not Yet Formalized) ═══

/-- Key theoretical concepts from Del Prete's non-quantificational
    analysis (§8.4).

    These are enumerated here for reference; full formalization would
    require substantial new infrastructure (PBT models, event structures
    with plural events, etc.). -/
inductive TheoreticalConcept where
  /-- **Partial Branching Time (PBT)**: A model based on Kratzerian
      situations where every situation has a unique past but many
      possible futures. Histories are maximal chains of situations. -/
  | partialBranchingTime
  /-- **Forward expansion (f-exp)**: The operation that expands a
      situation s forward in time, producing branches that represent
      expected continuations of s. Central to the lexical entry of IMPF. -/
  | forwardExpansion
  /-- **THR (Throughout)**: A topological operator that 'spreads out'
      a temporal property P over a situation s and its branches.
      IMPF is defined as: ⟦IMPF⟧ = λs.λP. THR(P, f-exp(s)). -/
  | throughoutOperator
  /-- **Lexical Cumulativity Hypothesis (LCH)**: Verbs can inherently
      refer to plural events (Kratzer 2008). This enables the
      non-quantificational analysis: plurality of events comes from
      the verb itself, not from a quantifier over situations. -/
  | lexicalCumulativity
  /-- **Sameness of Singular Participant (SSP)**: If a plural event e
      has a singular individual x as theme, then every atomic subevent
      of e has x as theme. This derives the SOE as an entailment. -/
  | samenessOfSingularParticipant
  /-- **Distribution to Subevents**: For kind-denoting themes, singular
      instances of the kind are distributed over atomic subevents of the
      plural event. This explains why bare plurals lack SOEs. -/
  | distributionToSubevents
  deriving DecidableEq, Repr


-- ═══ §8.7: Oddness Explained ═══

/-- Principle (O) from §8.7: "If a sentence S has implications that
    conflict with common knowledge, then S is perceived as odd."

    This pragmatic principle explains the asymmetric HAB availability:

    - (2a) "Gianni drove a sports car" — SOE (same car) is compatible
      with common knowledge (people do habitually drive one car).
      → HAB ✓

    - (2b) "Gianni read a philosophy book" — SOE (same book) conflicts
      with common knowledge (people don't repeatedly read the same
      philosophy book). → HAB perceived as odd (#).

    The SOE itself is a semantic entailment of the analysis (via SSP);
    the oddness arises from a pragmatic conflict with common knowledge.
    This two-step explanation (semantic SOE + pragmatic filter) is the
    chapter's main result. -/
structure OddnessPrinciple where
  sentence : String
  soeImplication : String
  conflictsWithCK : Bool  -- conflicts with common knowledge?
  perceivedAsOdd : Bool
  deriving Repr

def guidava_oddness : OddnessPrinciple :=
  { sentence := "Gianni guidava un'auto sportiva"
  , soeImplication := "Gianni habitually drove the same sports car"
  , conflictsWithCK := false
  , perceivedAsOdd := false }

def leggeva_filosofia_oddness : OddnessPrinciple :=
  { sentence := "Gianni leggeva un libro di filosofia"
  , soeImplication := "Gianni habitually read the same philosophy book"
  , conflictsWithCK := true
  , perceivedAsOdd := true }

/-- The oddness follows from common-knowledge conflict:
    no CK conflict → not odd; CK conflict → odd. -/
theorem oddness_from_ck_conflict :
    guidava_oddness.conflictsWithCK = false ∧
    guidava_oddness.perceivedAsOdd = false ∧
    leggeva_filosofia_oddness.conflictsWithCK = true ∧
    leggeva_filosofia_oddness.perceivedAsOdd = true := ⟨rfl, rfl, rfl, rfl⟩

/-- The two-step explanation: SOE is semantic (entailed by analysis),
    oddness is pragmatic (CK conflict). Matches `soe_blocks_hab`. -/
theorem twostep_soe_oddness :
    -- Semantic: (2b) has an implausible SOE
    gianniLeggevaFilosofia.soe == .implausible ∧
    -- Pragmatic: the SOE conflicts with common knowledge
    leggeva_filosofia_oddness.conflictsWithCK = true ∧
    -- Result: HAB is blocked
    gianniLeggevaFilosofia.habOK = false := ⟨rfl, rfl, rfl⟩


-- ═══ Bridge to Aspect ═══

/-- Whether a given viewpoint aspect permits habitual readings.

    Background observation: imperfective permits HAB; perfective does not.
    @cite{del-prete-2013} takes this as given — the chapter's contribution
    is analyzing HOW the Imperfetto gives rise to HAB readings via IMPF's
    forward expansion and event plurality. -/
def permitsHabitualReading : ViewpointAspectB → Bool
  | .imperfective => true
  | .perfective => false

/-- Imperfective permits habituals; perfective does not. -/
theorem imperfective_permits_habitual :
    permitsHabitualReading .imperfective = true ∧
    permitsHabitualReading .perfective = false :=
  ⟨rfl, rfl⟩

/-- All examples use imperfective aspect and the aspect permits HAB. -/
theorem aspect_permits_hab_for_all :
    italianData.all (λ d => permitsHabitualReading d.aspect) = true := by
  native_decide


-- ═══ Cross-Study Connections ═══

/-- The SOE phenomenon is cross-linguistic: English shows the same
    pattern. @cite{boneh-doron-2013} exx. (6b), (7b) in the same
    volume give the English counterparts:

    - "A flower grew out of the tree trunk" (plausible SOE → ✓)
    - "#Max killed a rabbit (repeatedly)" (implausible SOE → ✗)

    This parallel is formalized in `BonehDoron2013.sameObjectParallel`. -/
theorem soe_is_crosslinguistic :
    -- Italian: (2a) plausible → HAB ✓, (2b) implausible → HAB ✗
    gianniGuidava.habOK = true ∧ gianniLeggevaFilosofia.habOK = false := ⟨rfl, rfl⟩


end DelPrete2013
