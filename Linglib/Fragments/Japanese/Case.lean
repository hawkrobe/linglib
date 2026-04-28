import Linglib.Core.Case.Basic
import Linglib.Core.Case.Hierarchy
/-!
# Japanese Case Inventory @cite{blake-1994} @cite{tsujimura-2014} @cite{sadakane-koizumi-1995} @cite{kuroda-1972} @cite{kuno-1987}

Japanese marks grammatical and semantic relations on noun phrases with
postpositional morphemes. Following @cite{tsujimura-2014} (ch. 4 §§1.5–1.6,
pp. 133–137), those morphemes split into two morphosyntactic categories:

- **Case particles** (Tsujimura's narrow class): *-ga* (NOM), *-o* (ACC),
  *-ni* (DAT), *-no* (GEN). These lack inherent semantic content (their
  role is functionally determined by the verb) and may be omitted in casual
  speech (Tsujimura, p. 136, ex. 28).
- **Postpositions**: *-de* ('at, by'), *-e* ('to'), *-to* ('with'),
  *-kara* ('from'), *-made* ('until'), *-yori* ('than'). These bear inherent
  meaning and cannot be dropped (p. 136, ex. 29; the diagnostic contrast).

This Fragment groups both classes under a single `CaseMarker` schema with
an `omissibleInCasual : Bool` field encoding Tsujimura's primitive
diagnostic; the two enumerated lists (`caseParticles`, `postpositions`)
realize Tsujimura's classification, with consistency theorems forcing the
two encodings to agree. Both classes contribute to the language's
`Core.Case` inventory under the UD/Blake typological framing this library
uses (@cite{blake-1994} subsumes the postposition-marked roles
LOC/ALL/ABL/COM/TER/INST under the case hierarchy alongside the case-
particle-marked roles NOM/ACC/DAT/GEN).

§1 declares the markers; §2 derives the `Core.Case` inventory and proves
substantive properties (Blake-rank coverage, polysemy overlap).

## Theoretical commitments

This Fragment adopts @cite{tsujimura-2014}'s clean case-particle vs.
postposition partition (the diagnostic is omissibility in casual speech;
see `omissibleInCasual` field below) AND treats each particle as a single
lexical entry. @cite{sadakane-koizumi-1995} (*Linguistics* 33(1):5–33)
agree on the binary case-particle/postposition dichotomy at the schema
level (they explicitly defend Miyagawa 1989 / Kuroda 1965), but argue
the apparent ambiguity of *-ni* dissolves into HOMOPHONY: there are four
distinct *ni* lexemes (dative case marker *ni*, postposition *ni*,
*ni*-of-*ni*-insertion, copula *ni*), each respecting the binary split.
Under their analysis, the Fragment's single `ni : CaseMarker` entry with
`cases = {.dat, .loc, .all, .Tem}` collapses lexemes from at least three
of their four types — a *granularity* disagreement, not a *partition*
disagreement. The diagnostic separating the four is built from three
syntactic tests (floating numeral quantifier, cleft with particle, cleft
without particle; see Sadakane-Koizumi §2) plus an affectedness criterion
on the NP referent (their §4).

The Fragment keeps the single-entry schema for textbook-consensus reasons;
the four-way refinement is formalised in
`Phenomena/Case/Studies/SadakaneKoizumi1995.lean`, which derives the
conflation as a Lean theorem (`fragment_ni_conflates_sk_types`) and aligns
S&K's classification with Marantz's `CaseSource` partial map
(`sk_to_marantz`). Surfacing this contested commitment via that study
file is the point of this section — a downstream consumer that wants
the four-way refinement knows where to find it.

## Scope

This Fragment treats *-ga* as `.nom`, but that framing is a deliberate
simplification. The Kuroda–Kuno tradition (@cite{kuroda-1972} on
thetic/categorical judgements; @cite{kuno-1987} on functional syntax;
discussed by @cite{tsujimura-2014} ch. 6 §4.2.1, *Wa* vs. *Ga*; and
successors — Heycock, Tomioka — not yet in the bib) treats *-ga* as
ambiguous between a neutral-description marker and an exhaustive-
listing/focus marker, with *-wa* (intentionally excluded from this Fragment
as a topic/focus particle, not a case marker) covering categorical/topic
readings. The right home for those distinctions is a future
`Phenomena/InformationStructure/` study file, not this Fragment.

Other phenomena out of scope at the case-marking layer:
- Dative subjects in stative-experiencer constructions (*Tarō-ni eigo-ga
  wakaru* 'Taro understands English'). The flat inventory has both `.nom`
  and `.dat`, but does not predict which verbs license dative subjects.
- *Ga/no* conversion in relative clauses (*Tarō-no kaita hon* 'the book Taro
  wrote'); see @cite{tsujimura-2014} ch. 5 §6.1.
- *O*-causatives vs. *ni*-causatives (the syntactic alternation discussed
  in @cite{tsujimura-2014} ch. 5 §5.1). The Fragment records *-ni* as `.dat`
  here; the syntax of causative case assignment lives elsewhere.
- The Double-*o* Constraint (Harada 1973, treated in @cite{tsujimura-2014}
  ch. 5 §5.2): a categorical syntactic constraint barring two *-o*-marked
  NPs in a clause. A natural future `Phenomena/Case/Studies/Harada1973.lean`
  study file would import the Fragment to formalize the constraint's
  empirical effects.
- Case-particle and postposition stacking (*Tarō-ni-no tegami* 'a letter to
  Taro'; *koko-made-ga omoshiroi* 'up to this point is interesting',
  @cite{tsujimura-2014}, p. 137, ex. 30).

The polysemy of *-ni* (DAT/LOC/ALL/TEM) and *-de* (LOC/INST) is recorded
in the per-marker `cases` field below — those polysemy claims are
auditable Lean data, not prose-only assertions, and are stated as theorems
in §2 (e.g. `ni_de_share_loc`, `ni_e_share_all`). Per-particle citations
identify which uses are directly grounded in @cite{tsujimura-2014} vs.
which are standard descriptive consensus from other sources (Shibatani
1990, *The Languages of Japan*, CUP — not yet in the linglib bib).
-/

namespace Fragments.Japanese.Case

-- ============================================================================
-- § 1: Case Markers
-- ============================================================================

/-- A Japanese case-marking morpheme. `cases` records which `Core.Case`
    categories the marker realizes — most markers map to a single case,
    but *-ni* and *-de* are polysemous. `omissibleInCasual` records
    Tsujimura's diagnostic (ch. 4 §1.6, p. 136, ex. 28–29): case particles
    can be dropped in casual speech, postpositions cannot. Membership in
    `caseParticles` vs. `postpositions` (below) gives the same partition
    via Tsujimura's enumeration; the consistency theorems
    `caseParticles_all_omissible` and `postpositions_none_omissible` force
    the two encodings to agree. -/
structure CaseMarker where
  /-- Romanized form (Hepburn). -/
  romaji            : String
  /-- Hiragana form. -/
  kana              : String
  /-- The `Core.Case` categories this marker realizes. -/
  cases             : Finset Core.Case
  /-- Whether the marker can be dropped in casual speech (Tsujimura's
      diagnostic for case-particle status, p. 136, ex. 28–29). -/
  omissibleInCasual : Bool

/-! ### Case particles (Tsujimura 2014, ch. 4 §1.6, p. 134) -/

/-- *-ga* — nominative case particle. See the file's *Scope* section for the
    Kuroda–Kuno exhaustive-listing literature this Fragment abstracts away.
    Tsujimura (p. 134, ex. 22a–d): "normally indicates that the accompanying
    noun is the subject of the sentence". -/
def ga : CaseMarker :=
  { romaji := "ga", kana := "が", cases := {.nom}, omissibleInCasual := true }

/-- *-o* — accusative case particle. Tsujimura (p. 134, ex. 22b–c): "marks
    the noun that immediately precedes it as the direct object". -/
def o : CaseMarker :=
  { romaji := "o", kana := "を", cases := {.acc}, omissibleInCasual := true }

/-- *-no* — genitive case particle. Tsujimura (p. 134, ex. 22d): "establishes
    a modification relation to the following noun ... possessor–possessed
    relation, similar to English 's". The same form is also a nominalizer
    and the alternant in *ga/no* conversion inside relative clauses; both
    uses are out of scope at the case-marking layer (see file scope note). -/
def no_ : CaseMarker :=
  { romaji := "no", kana := "の", cases := {.gen}, omissibleInCasual := true }

/-- *-ni* — dative case particle (primary use per Tsujimura, p. 134, ex. 22c:
    "primarily associated with verbs of giving, and together with a noun, it
    implies the recipient"). Polysemous along three further axes:

    * **Allative** (motion-toward, `.all`): @cite{tsujimura-2014} p. 374
      ex. 209a, *Satoko-ga kooen-ni aruita* 'Satoko walked to the park',
      in the lexicalization-pattern (Talmy) discussion. Overlaps with the
      postposition *-e*.
    * **Temporal** (`.Tem`): @cite{tsujimura-2014} p. 129 ex. 8a,
      *maiasa goji-ni oki-te* 'every morning at 5 o'clock get-up'; p. 286
      ex. 164 *2008-nen-ni toosen-sita* '(was) elected in 2008'.
    * **Locative-of-existence** (`.loc`, *Tōkyō-ni iru* 'be in Tokyo'):
      standard descriptive claim (any Japanese reference grammar; not
      foregrounded in Tsujimura's case-particle section). The DAT–LOC–ALL
      clustering is a cross-linguistically common polysemy; @cite{blake-1994}
      discusses the ALL → DAT extension as a recurrent grammaticalization
      pathway. -/
def ni : CaseMarker :=
  { romaji := "ni", kana := "に", cases := {.dat, .loc, .all, .Tem}
  , omissibleInCasual := true }

/-! ### Postpositions (Tsujimura 2014, ch. 4 §1.5, p. 133) -/

/-- *-de* — locative postposition (Tsujimura, p. 133, ex. 20a: *uti-de*
    "at home"; p. 136: "*de* 'at' implies location"). Specifically marks
    location-of-action ('at/in the place where something happens'), in
    contrast with *-ni*'s locative-of-existence. The instrumental use
    (*kuruma-de iku* 'go by car') and means/material use are standard
    descriptive consensus; both are recorded as `.inst` here. -/
def de : CaseMarker :=
  { romaji := "de", kana := "で", cases := {.loc, .inst}, omissibleInCasual := false }

/-- *-e* — directional/allative postposition. Tsujimura (p. 133, ex. 20b):
    *gakkoo-e* "to school". Restricted to motion-toward; ungrammatical or
    marked in pure recipient or locative-of-existence contexts where *-ni*
    is fine. The Fragment encodes the case-relevant difference by giving
    *-e* only `.all`, while *-ni* carries `.dat, .loc, .all, .Tem`. -/
def e : CaseMarker :=
  { romaji := "e", kana := "へ", cases := {.all}, omissibleInCasual := false }

/-- *-to* — comitative postposition. Tsujimura (p. 133, ex. 20c:
    *tomodati-to* "with a friend"; p. 136: "*to* 'with' has comitative
    meaning"). The same form is also a quotative complementizer; that use
    is out of scope at the case-marking layer. -/
def to_ : CaseMarker :=
  { romaji := "to", kana := "と", cases := {.com}, omissibleInCasual := false }

/-- *-kara* — ablative postposition (source/origin, both spatial and
    temporal). Tsujimura (p. 133, ex. 20e: *yama-kara* "from the mountain").
    The same form is also a clause-final 'because' conjunction; that use is
    out of scope at the case-marking layer. -/
def kara : CaseMarker :=
  { romaji := "kara", kana := "から", cases := {.abl}, omissibleInCasual := false }

/-- *-made* — terminative postposition ('until, as far as'). Tsujimura
    (p. 133, ex. 20d: *gozi-made* "until 5 o'clock"; p. 137: "*made* 'until,
    as far as'"). Marks the endpoint of a spatial or temporal extent. UD
    `Core.Case` provides `.Ter` for this role (Hungarian *-ig*, Finnish
    *-asti*). -/
def made : CaseMarker :=
  { romaji := "made", kana := "まで", cases := {.Ter}, omissibleInCasual := false }

/-- *-yori* — literary/formal ablative; in modern colloquial Japanese
    primarily marks the standard of comparison ('than X'; cf.
    @cite{tsujimura-2014} p. 132, ex. 19d: *Hanako-yori zutto haya-ku*
    "a lot earlier than Hanako"). Only the case-marking ABL function is
    recorded here; the comparative-standard reading is out of scope at the
    case layer. -/
def yori : CaseMarker :=
  { romaji := "yori", kana := "より", cases := {.abl}, omissibleInCasual := false }

/-! ### Tsujimura's classification

Tsujimura enumerates the four case particles in ch. 4 §1.6 (p. 134, ex. 22)
and the postpositions in ch. 4 §1.5 (p. 133, ex. 20). The enumerated lists
are the primary source of truth here; `caseMarkers` is their concatenation.
-/

/-- Tsujimura's four case particles, in the order she presents them
    (p. 134, ex. 22). -/
def caseParticles : List CaseMarker :=
  [ga, o, no_, ni]

/-- The six postpositions with case-relevant semantics from Tsujimura's
    enumeration (p. 133, ex. 20). -/
def postpositions : List CaseMarker :=
  [de, e, to_, kara, made, yori]

/-- The full case-marker inventory: case particles ⊎ postpositions. -/
def caseMarkers : List CaseMarker :=
  caseParticles ++ postpositions

/-- Tsujimura's diagnostic (p. 136, ex. 28): every case particle in her
    enumeration is omissible in casual speech. -/
theorem caseParticles_all_omissible :
    ∀ m ∈ caseParticles, m.omissibleInCasual = true := by decide

/-- Tsujimura's diagnostic (p. 136, ex. 29): no postposition in her
    enumeration is omissible in casual speech. -/
theorem postpositions_none_omissible :
    ∀ m ∈ postpositions, m.omissibleInCasual = false := by decide

-- ============================================================================
-- § 2: Case Inventory
-- ============================================================================

/-- The `Core.Case` categories realized by Japanese case markers, derived
    from `caseMarkers`. Changing a marker's `cases` field automatically
    propagates here — there is no separately stipulated set to drift from. -/
def caseInventory : Finset Core.Case :=
  (caseMarkers.map (·.cases)).foldr (· ∪ ·) ∅

/-- Every Blake hierarchy rank from 0 to 6 is realized in the Japanese
    inventory. This is strictly stronger than `IsValidInventory` (which only
    rules out interior gaps) — Japanese is the maximally Blake-realizing
    inventory among the languages currently in `Fragments/`. -/
theorem caseInventory_realizes_all_blake_ranks :
    ∀ r : Fin 7, ∃ c ∈ caseInventory, c.hierarchyRank = r := by decide

/-- Contiguous on Blake's hierarchy. (Trivially follows from
    `caseInventory_realizes_all_blake_ranks`, but stated separately so that
    consumers comparing inventories across Fragments can `exact` it.) -/
theorem caseInventory_isValid :
    Core.Case.IsValidInventory caseInventory := by decide

/-! ### Polysemy as theorems

The polysemy claims advertised in the *-ni* and *-de* docstrings are
stated here as auditable Lean theorems rather than prose-only assertions.
A consumer who edits a marker's `cases` field will break exactly these
theorems if the polysemy claim no longer holds.
-/

/-- The case particle *-ni* and the postposition *-de* both realize `.loc`,
    distinguished semantically by locative-of-existence vs. locative-of-
    action (see per-marker docstrings). Tsujimura's morphosyntactic
    case-particle/postposition split therefore does NOT align with the
    semantic case split — `.loc` straddles both classes. -/
theorem ni_de_share_loc :
    .loc ∈ ni.cases ∧ .loc ∈ de.cases := by decide

/-- The case particle *-ni* and the postposition *-e* both realize `.all`,
    distinguished by the broader recipient/dative profile of *-ni* vs.
    *-e*'s pure motion-toward semantics. -/
theorem ni_e_share_all :
    .all ∈ ni.cases ∧ .all ∈ e.cases := by decide

/-- Both *-kara* and *-yori* realize `.abl`, with *-yori* additionally
    marking the standard of comparison (recorded in the docstring as out of
    scope at the case layer). The two postpositions are co-extensional on
    the case-marking dimension. -/
theorem kara_yori_share_abl :
    .abl ∈ kara.cases ∧ .abl ∈ yori.cases := by decide

end Fragments.Japanese.Case
