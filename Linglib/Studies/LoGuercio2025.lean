import Linglib.Pragmatics.Expressives.Basic
import Linglib.Semantics.Alternatives.Structural
import Linglib.Data.Examples.Schema

/-!
# [lo-guercio-2025] — Anti-Conventional Implicatures

Lo Guercio, N. (2025). Maximize Conventional Implicatures!
*Semantics & Pragmatics*, 18(9). <https://doi.org/10.3765/sp.18.9>

Scalar inferences can arise from comparing CI content, not just at-issue or
presuppositional content. These are *Anti-Conventional Implicatures* (ACIs).
Evidence comes from epithets, honorifics (*don/doña*), nominal appositives,
supplementary adverbs, and emotive markers.

The mechanism parallels:
- Scalar Implicatures: compare at-issue content (Conversational Principle,
  [katzir-2007])
- Antipresuppositions: compare presuppositional content (Maximize
  Presupposition, [schlenker-2012])
- ACIs: compare CI content (Maximize Conventional Implicatures!)

All three are instances of `violatesMaximize` from
`Semantics/Alternatives/Structural.lean`, applied to different content
dimensions; `violatesMCIs` is the CI-content instantiation. The two
structural-parallel theorems
`violatesMaximize_of_violatesMP` and `violatesMP_of_violatesMaximize_sameAssertion`
(in `Structural.lean`) discharge Lo Guercio's §4 diagnostic that "ACIs do
not require same assertive content, unlike antipresuppositions" — MP is
literally Maximize-on-presupposition *plus* a same-assertion clause.

The CI content function used in the §3 worked example follows the
[gutzmann-2015] / [kaplan-1999] felicity-set semantics adopted by
Lo Guercio (paper def 12, p. 9): ⟦φ⟧ᵘ is the set of contexts where φ is
felicitously usable. The bare sentence is felicitous everywhere (trivial CI);
the epithet construction is felicitous only at worlds where the speaker
holds the relevant CI-belief.

## Main declarations

* `Examples` — the paper's 15 empirical items, sourced from
  `Linglib/Data/Examples/LoGuercio2025.json`.
* `EWord`, `epithetLex`, `johnArrived`, `bastardJohnArrived`,
  `bastardPedroDP`, `priorContextLex` — vocabulary, lexicons, and trees
  for the §3 worked example.
* `expressiveCI` — concrete CI content function modeling Lo Guercio's
  felicity-set semantics for the epithet construction.
* `outOfBlue_no_ACI` — out-of-the-blue (paper (18)): no formal alternative
  supplies stronger epithet-CI than the bare sentence, so `violatesMCIs`
  does NOT fire.
* `priorMention_yes_ACI` — prior-mention configuration (paper (20a)):
  with the epithet construction contextually relevant (added to the
  substitution source), `violatesMCIs` DOES fire.
* `outOfBlue_vs_priorMention_contrast` — the paper's central diagnosis
  packaged as a single theorem: same content function, same host, two
  substitution sources, opposite outcomes.

## Implementation notes

Empirical items live as typed `LinguisticExample` rows in
`Linglib/Data/Examples/LoGuercio2025.json` and are inserted between
`-- BEGIN/END GENERATED EXAMPLES` markers by `scripts/gen_examples.py`.
The `paperFeatures` field records paper-internal classifications
(`aciStatus`, `expressionType`, `licensingMechanism`); downstream
theorems project these as needed.

The §3 worked example uses a STRUCTURAL PROXY for the felicity-set CI
semantics: `expressiveCI φ w` is true iff `φ` lacks the structural marker
of the epithet construction (`containsCat .DP` here — the bare-name
subject is intentionally modeled as a bare `[N john]` terminal, while
the epithet variant introduces the `[DP that bastard john]` node) OR the
speaker holds the CI belief at `w`. The structural proxy is faithful to
the paper's mechanism for this fragment — the CI is *triggered by* the
epithet DP construction — and lets `category_preservation` discharge the
out-of-the-blue case constructively. A full compositional interpretation
through `Pragmatics.Expressives.TwoDimProp.ci` would require a Pottsian
lexical entry for `bastard` and a tree-interpretation function; see the
Todo bullet below.

The contrastive-honorific ACI in (22a) is read in Lo Guercio (around (24),
paper p. 14) as a Horn-style upper-bounding inference — *at most* the
lower honorific attitude toward the bare-name referent — not as a literal
contrastive denial. The JSON `comment` field for that example records this
distinction.

The Japanese vs Spanish honorific systematicity contrast (paper §3.2.2,
JSON `outOfBlue_honorific` and `contrastive_honorific` comments) is the
paper's key cross-linguistic argument and is grounded in [mccready-2019]
(plain vs *desu/masu* polite-form competition) and [oshima-2023]
(*san*/*kun*/*chan* affixal designation terms). In Japanese, ADTs and
polite forms are systematically contextually relevant by virtue of a
default expectation of honorification; their omission systematically
triggers an ACI. Spanish *don/doña* lacks this default expectation, so
omission triggers an ACI only when honorification is locally relevant.

## Todo

* Replace `expressiveCI` with a compositional interpretation through
  `Pragmatics.Expressives.TwoDimProp.ci`: define a Pottsian lexical entry
  `bastardLex : TwoDimProp World` and an interpretation function
  `interpret : Tree Cat EWord → TwoDimProp World`, then derive
  `expressiveCI` as `(interpret φ).ci`. Substrate-level change; defer.
* §3.2.4 expressive-adjective argument extension (paper p. 25-27):
  Lo Guercio is explicit (p. 26) that he merely points to a tentative
  line of analysis (late-merge at PF following [lo-guercio-orlando-2022]);
  not formalized.
* §4 embeddability data (paper (55)-(60)) — paper devotes 3 pages;
  promote to a `Phenomena/Expressives/Embeddability.lean` hub once a
  second study (Kratzer 1999 or Potts 2007) contributes parallel stimuli.
* §4 Magri-style oddness puzzles (paper (64)-(68)) — paper itself
  declares this unresolved/erratic; defer.
* The `priorMention_yes_ACI` reachability hypothesis is currently
  supplied by the caller. A constructive proof requires either modeling
  the bare-name subject as `[DP [N john]]` (paper (24) notation) and a
  stronger structural-preservation lemma than `category_preservation`
  (one that tracks 1-child vs multi-child DP nodes), or a separate
  worked tree for the priorMention case. Substrate refactor; defer.
-/

namespace LoGuercio2025

open Pragmatics.Expressives
open Alternatives.Structural
open Syntax
open Data.Examples (LinguisticExample)

-- BEGIN GENERATED EXAMPLES
-- (Generated from Linglib/Data/Examples/LoGuercio2025.json by scripts/gen_examples.py.
-- Do not edit between markers; re-run the generator after editing the JSON.)

namespace Examples
open Data.Examples

def outOfBlue_epithet : LinguisticExample :=
  { id := "loguercio2025_outOfBlue_epithet"
    source := ⟨"lo-guercio-2025", "(epithet OOTB)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John arrived late."
    discourseSegments := []
    glossedTokens := []
    translation := "John arrived late."
    context := "Out of the blue, no prior mention of any epithet construction."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aciStatus", "doesNotArise"), ("expressionType", "epithet"), ("licensingMechanism", "outOfBlue")]
    comment := "Out-of-the-blue baseline (Lo Guercio 2025 §3.1). Bare proper-name sentence with no contextually-relevant epithet alternative. No ACI arises: hearer does not infer the speaker disbelieves any epithet attribution to John. Mechanism: the epithet construction `[DP that bastard John]` is structurally more complex than the bare name (introduces a DP node), so it is not a formal alternative reachable from the bare sentence without context-supplied material. Predicted by MCIs! via failure of the formal-alternative clause."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def priorMention_epithet : LinguisticExample :=
  { id := "loguercio2025_priorMention_epithet"
    source := ⟨"lo-guercio-2025", "(20a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John arrived first, then that bastard Pedro arrived."
    discourseSegments := ["John arrived first,", "then that bastard Pedro arrived."]
    glossedTokens := []
    translation := "John arrived first, then that bastard Pedro arrived."
    context := "Single conjoined utterance; the ACI target is the first conjunct's bare `John`."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aciStatus", "arises"), ("aciTarget", "John (first conjunct)"), ("expressionType", "epithet"), ("licensingMechanism", "priorMention")]
    comment := "Lo Guercio 2025 (20a). The second conjunct's epithet construction `that bastard Pedro` makes the parallel `that bastard John` contextually relevant (a formal alternative for the first conjunct's bare `John`). MCIs! then derives the ACI: ¬(speaker believes John is a bastard), because had the speaker so believed, the CI-stronger `that bastard John arrived first` was available and equally complex. The whole utterance is felicitous; the ACI targets only the bare-name first conjunct, not the asserted content."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def subconstituent_epithet : LinguisticExample :=
  { id := "loguercio2025_subconstituent_epithet"
    source := ⟨"lo-guercio-2025", "(epithet subconstituent)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Yesterday, John met with that bastard Pedro."
    discourseSegments := []
    glossedTokens := []
    translation := "Yesterday, John met with that bastard Pedro."
    context := "Single sentence; the epithet construction occurs as a subconstituent making the alternative for the matrix `John` available."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aciStatus", "arises"), ("aciTarget", "John (matrix subject)"), ("expressionType", "epithet"), ("licensingMechanism", "subconstituent")]
    comment := "Lo Guercio 2025 §3.1, sub-constituent licensing of the epithet alternative. `That bastard Pedro` as a subconstituent feeds the substitution source for the matrix `John`, making `that bastard John met with that bastard Pedro` a formal alternative. MCIs! derives ¬(speaker believes John is a bastard) by the same mechanism as (20a)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def outOfBlue_honorific : LinguisticExample :=
  { id := "loguercio2025_outOfBlue_honorific"
    source := ⟨"lo-guercio-2025", "(Spanish honorific OOTB)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Diego entró."
    discourseSegments := []
    glossedTokens := [("Diego", "Diego"), ("entró", "enter.PST.3SG")]
    translation := "Diego entered."
    context := "Out-of-the-blue Spanish utterance; no prior contextual relevance of *don/doña*."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aciStatus", "doesNotArise"), ("expressionType", "honorific"), ("licensingMechanism", "outOfBlue"), ("language", "Spanish")]
    comment := "Lo Guercio 2025 §3.1, Spanish honorifics. Unlike Japanese ADTs (*san*, *kun*, *chan*) and *desu/masu*-style polite forms (which carry a default expectation that any referent be properly honorified, so omission triggers a systematic ACI), Spanish *don/doña* is not systematically expected. Out of the blue, no honorific alternative is contextually relevant, so no ACI arises. Mechanism mirrors the epithet OOTB case: the formal-alternative clause fails."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def contrastive_honorific : LinguisticExample :=
  { id := "loguercio2025_contrastive_honorific"
    source := ⟨"lo-guercio-2025", "(22a)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Primero entró Donato. Después entró Don Pedro."
    discourseSegments := ["Primero entró Donato.", "Después entró Don Pedro."]
    glossedTokens := [("Primero", "first"), ("entró", "enter.PST.3SG"), ("Donato", "Donato"), ("Después", "afterwards"), ("entró", "enter.PST.3SG"), ("Don", "HON.M"), ("Pedro", "Pedro")]
    translation := "First Donato entered. Afterwards Don Pedro entered."
    context := "Two-segment discourse; the second segment uses honorific *Don* while the first uses bare name *Donato*."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aciStatus", "arises"), ("aciTarget", "Donato (first segment)"), ("expressionType", "honorific"), ("licensingMechanism", "priorMention"), ("language", "Spanish")]
    comment := "Lo Guercio 2025 (22a). Using *Don* for Pedro makes *Don Donato* a contextually-relevant CI-stronger alternative for the first segment's bare *Donato*. MCIs! derives an at-most upper-bounding ACI (Horn-style, cf. paper around (24), p. 14): the speaker conveys at most a lower honorific attitude toward Donato than toward Pedro. (Not a literal contrastive denial — the upper-bound reading is what Lo Guercio analyses as in scope.)"
    metaLanguage := "stan1293"
    lgrConformance := "" }

def outOfBlue_appositive : LinguisticExample :=
  { id := "loguercio2025_outOfBlue_appositive"
    source := ⟨"lo-guercio-2025", "(31a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Diego recommended an aspirin."
    discourseSegments := []
    glossedTokens := []
    translation := "Diego recommended an aspirin."
    context := "Out-of-the-blue; no prior appositive construction in discourse."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aciStatus", "doesNotArise"), ("expressionType", "appositive"), ("licensingMechanism", "outOfBlue")]
    comment := "Lo Guercio 2025 (31a). Bare-DP subject sentence with no prior appositive construction; no ACI arises about any descriptive property the appositive `Diego, a doctor` would otherwise contribute. The paper glosses the non-arising inference as ¬(Diego is a doctor) (or any other potential appositive content). Mechanism: no appositive alternative is contextually relevant."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def priorMention_appositive : LinguisticExample :=
  { id := "loguercio2025_priorMention_appositive"
    source := ⟨"lo-guercio-2025", "(31b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Diego recommended an aspirin. Laura, a doctor, recommended an antibiotic."
    discourseSegments := ["Diego recommended an aspirin.", "Laura, a doctor, recommended an antibiotic."]
    glossedTokens := []
    translation := "Diego recommended an aspirin. Laura, a doctor, recommended an antibiotic."
    context := "Two-segment discourse; the second segment's `, a doctor,` appositive makes the same-shape appositive a contextually-relevant alternative for `Diego`."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aciStatus", "arises"), ("aciTarget", "Diego (first segment)"), ("expressionType", "appositive"), ("licensingMechanism", "priorMention")]
    comment := "Lo Guercio 2025 (31b). With Laura's appositive `, a doctor,` in the second sentence, the parallel `Diego, a doctor, recommended an aspirin` becomes a formal alternative for the first. MCIs! derives ¬(speaker believes Diego is a doctor): had the speaker so believed, the CI-stronger appositive variant was available."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def outOfBlue_suppAdverb : LinguisticExample :=
  { id := "loguercio2025_outOfBlue_suppAdverb"
    source := ⟨"lo-guercio-2025", "(33a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Juan signed up for the tournament."
    discourseSegments := []
    glossedTokens := []
    translation := "Juan signed up for the tournament."
    context := "Out-of-the-blue assertion with no supplementary-adverb construction in discourse."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aciStatus", "doesNotArise"), ("expressionType", "supplementaryAdverb"), ("licensingMechanism", "outOfBlue")]
    comment := "Lo Guercio 2025 (33a). No supplementary adverb is contextually relevant, so no ACI of the form ¬*luckily/amazingly*(Juan signed up) arises. Mechanism: formal-alternative clause fails."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def priorMention_suppAdverb : LinguisticExample :=
  { id := "loguercio2025_priorMention_suppAdverb"
    source := ⟨"lo-guercio-2025", "(supp-adv prior mention)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Juan signed up for the tournament and luckily, Pedro signed up for the tournament."
    discourseSegments := ["Juan signed up for the tournament", "and luckily, Pedro signed up for the tournament."]
    glossedTokens := []
    translation := "Juan signed up for the tournament and luckily, Pedro signed up for the tournament."
    context := "Conjoined utterance; the second conjunct's `luckily,` makes the parallel adverb-modified variant available for the first conjunct."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aciStatus", "arises"), ("aciTarget", "Juan-signup proposition (first conjunct)"), ("expressionType", "supplementaryAdverb"), ("licensingMechanism", "priorMention")]
    comment := "Lo Guercio 2025 §3.1, supplementary adverbs. Using `luckily,` for Pedro's signup makes `luckily, Juan signed up for the tournament` a CI-stronger formal alternative. MCIs! derives ¬*luckily*(Juan signed up): the speaker does not consider Juan's signup lucky. Parallel structure replaces *luckily* with *amazingly* in (33b)/(35) etc."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def priorMention_emotiveMarker : LinguisticExample :=
  { id := "loguercio2025_priorMention_emotiveMarker"
    source := ⟨"lo-guercio-2025", "(38a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Juan signed up for the tournament, and Alas, Pedro signed up too."
    discourseSegments := ["Juan signed up for the tournament,", "and Alas, Pedro signed up too."]
    glossedTokens := []
    translation := "Juan signed up for the tournament, and Alas, Pedro signed up too."
    context := "Conjoined utterance; second conjunct's emotive marker `Alas,` parallels the first conjunct."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aciStatus", "arises"), ("aciTarget", "Juan-signup proposition (first conjunct)"), ("expressionType", "emotiveMarker"), ("licensingMechanism", "priorMention")]
    comment := "Lo Guercio 2025 (38a). Same mechanism as supplementary-adverb prior-mention case (above), with emotive marker `Alas`/`Wow` etc. ACI: ¬(speaker is disappointed/surprised about Juan signing up for the tournament)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def registerBlocking : LinguisticExample :=
  { id := "loguercio2025_registerBlocking"
    source := ⟨"lo-guercio-2025", "(28a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "That bastard John is late."
    discourseSegments := []
    glossedTokens := []
    translation := "That bastard John is late."
    context := "Both *bastard* and *motherfucker* are lexical items in the substitution source, with *motherfucker* CI-stronger; the prediction would be an ACI ¬(speaker believes John is a motherfucker)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aciStatus", "doesNotArise"), ("expressionType", "epithet"), ("licensingMechanism", "register"), ("registerContrast", "bastard~motherfucker")]
    comment := "Lo Guercio 2025 (28a-b), p. 19. Despite *motherfucker* being CI-stronger than *bastard* (both lexical, both in substitution source), the predicted ACI ¬(John is a motherfucker) does NOT arise. Lo Guercio attributes the blocking to register/coarseness difference, citing [levinson-2000] (`items in the same scale must be in salient opposition: of the same form class, in the same dialect or register, and lexicalised to the same degree`). Note: Lo Guercio is explicit (p. 20) that he does not yet have a full explanation for how register differs from other not-at-issue dimensions in blocking alternativehood."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def disjunction_independent_of_assertion : LinguisticExample :=
  { id := "loguercio2025_disjunction_independent_of_assertion"
    source := ⟨"lo-guercio-2025", "(50)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Juan called María or that bastard Pedro."
    discourseSegments := []
    glossedTokens := []
    translation := "Juan called María or that bastard Pedro."
    context := "Test of independence-of-assertion: the CI-stronger conjunctive variant has different at-issue content from the disjunctive utterance, yet the ACI still arises."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aciStatus", "arises"), ("aciTarget", "María"), ("expressionType", "epithet"), ("aciProperty", "independentOfAssertion")]
    comment := "Lo Guercio 2025 (50). The CI-stronger alternative `Juan called María and that bastard Pedro` differs in at-issue content (conjunction vs disjunction), yet the ACI ¬(speaker believes María is a bastard) still arises. Distinguishes ACIs from antipresuppositions (which require same assertive content per MP!) — confirming that `violatesMCIs` does NOT include the same-assertion clause that `violatesMP` does."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def DE_aci_survives : LinguisticExample :=
  { id := "loguercio2025_DE_aci_survives"
    source := ⟨"lo-guercio-2025", "(DE-embedding)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I doubt that Juan or that bastard Pedro passed the exam."
    discourseSegments := []
    glossedTokens := []
    translation := "I doubt that Juan or that bastard Pedro passed the exam."
    context := "Downward-entailing embedding under `doubt`; tests whether DE blocks ACI computation."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aciStatus", "arises"), ("aciTarget", "Juan"), ("expressionType", "epithet"), ("aciProperty", "unaffectedByDE")]
    comment := "Lo Guercio 2025 §4. Under `I doubt that`, scalar implicatures are blocked (DE reverses entailment), but the ACI ¬(speaker believes Juan is a bastard) still arises. Because CI content is independent of at-issue truth-conditional entailment (Potts 2005), DE environments have no effect on MCIs! computation. Diagnostic contrast: paired SI ¬(both passed) is blocked here, while the ACI is not."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def cancellation : LinguisticExample :=
  { id := "loguercio2025_cancellation"
    source := ⟨"lo-guercio-2025", "(ACI cancellation)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Juan arrived first. Then that bastard Pedro arrived. By the way, Juan is also a bastard."
    discourseSegments := ["Juan arrived first.", "Then that bastard Pedro arrived.", "By the way, Juan is also a bastard."]
    glossedTokens := []
    translation := "Juan arrived first. Then that bastard Pedro arrived. By the way, Juan is also a bastard."
    context := "Tests cancellability of the ACI ¬(speaker believes John is a bastard) triggered by the prior-mention configuration."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aciStatus", "cancelled"), ("aciProperty", "cancellable")]
    comment := "Lo Guercio 2025 §4. The parenthetical `By the way, Juan is also a bastard` cancels the ACI that would otherwise be derived from the prior-mention configuration. Distinguishes ACIs from presuppositions, which would sound redundant when reinforced/cancelled this way."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def reinforcement : LinguisticExample :=
  { id := "loguercio2025_reinforcement"
    source := ⟨"lo-guercio-2025", "(ACI reinforcement)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Juan arrived first. That bastard Pedro arrived second. By the way, Juan is not a bastard."
    discourseSegments := ["Juan arrived first.", "That bastard Pedro arrived second.", "By the way, Juan is not a bastard."]
    glossedTokens := []
    translation := "Juan arrived first. That bastard Pedro arrived second. By the way, Juan is not a bastard."
    context := "Tests reinforceability of the ACI ¬(speaker believes Juan is a bastard)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aciStatus", "arises"), ("aciProperty", "reinforceable")]
    comment := "Lo Guercio 2025 §4. The reinforcement `By the way, Juan is not a bastard` is informative, not redundant — contrasting with presupposition reinforcement (which is redundant)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [outOfBlue_epithet, priorMention_epithet, subconstituent_epithet, outOfBlue_honorific, contrastive_honorific, outOfBlue_appositive, priorMention_appositive, outOfBlue_suppAdverb, priorMention_suppAdverb, priorMention_emotiveMarker, registerBlocking, disjunction_independent_of_assertion, DE_aci_survives, cancellation, reinforcement]

end Examples
-- END GENERATED EXAMPLES

/-! ### §3 worked example: epithet as structural alternative

The §3 mechanism in two stages:

1. **Out of the blue**: the epithet construction `[DP that bastard John]`
   requires more structural complexity than the bare-name sentence
   provides. `category_preservation` (`Structural.lean`) closes the
   "no DP reachable" lemma constructively.
2. **Prior mention**: when the epithet construction occurs elsewhere in
   the discourse (paper's `[DP that bastard Pedro]` in (20a)), the
   substitution source clause (a) admits it as "contextually relevant"
   ([fox-katzir-2011] def 41). We model this by adding
   `bastardPedroDP` to `priorContextLex`. Now two Katzir substitutions
   reach `bastardJohnArrived`: outer DP → bastardPedroDP, then inner
   Pedro → John. -/

/-- Vocabulary for the epithet worked example. -/
inductive EWord where
  | john | pedro | arrived | first | andThen
  | that_ | bastard
  deriving DecidableEq, Repr

instance : BEq EWord := ⟨fun a b => decide (a = b)⟩
instance : LawfulBEq EWord where
  eq_of_beq h := of_decide_eq_true h
  rfl := decide_eq_true rfl

open EWord

/-- Out-of-the-blue lexicon: terminals only, no DP-shaped items. -/
def epithetLex : List (Tree Cat EWord) :=
  [.terminal .N .john, .terminal .N .pedro,
   .terminal .V .arrived, .terminal .Adv .first,
   .terminal .Conj .andThen,
   .terminal .Det .that_, .terminal .N .bastard]

/-- φ = "John arrived first" — bare-name subject, NO DP node.

The bare-name N-terminal modeling is the structural proxy that lets
`category_preservation` close the OOTB no-ACI direction (the source has
no DP, so no reachable tree does). The paper's actual modeling of John
as a DP (`[DP John]`, paper (24)) would require a richer subtree-tracking
lemma. -/
def johnArrived : Tree Cat EWord :=
  .node .S [.terminal .N .john,
            .node .VP [.terminal .V .arrived, .terminal .Adv .first]]

/-- φ' = "[DP that bastard John] arrived first" — epithet DP subject.
Strictly more complex than `johnArrived`: replaces the terminal `[N John]`
with a 3-child DP `[DP that bastard John]`. -/
def bastardJohnArrived : Tree Cat EWord :=
  .node .S [.node .DP [.terminal .Det .that_,
                       .terminal .N .bastard,
                       .terminal .N .john],
            .node .VP [.terminal .V .arrived, .terminal .Adv .first]]

/-- The epithet DP for Pedro: `[DP that bastard Pedro]`. In the paper's
prior-mention configuration (20a), this constituent is introduced by the
second conjunct ("then that bastard Pedro arrived") and becomes
contextually relevant — by Fox-Katzir's substitution-source clause (a)
it then enters the source for the first conjunct's alternatives. -/
def bastardPedroDP : Tree Cat EWord :=
  .node .DP [.terminal .Det .that_,
             .terminal .N .bastard,
             .terminal .N .pedro]

/-- Prior-mention lexicon: out-of-the-blue lexicon augmented by the
contextually-relevant `bastardPedroDP` constituent. This is the
substitution-source clause (a) in [fox-katzir-2011] def 41 made
concrete: "α is contextually relevant in c (e.g., by virtue of having
been mentioned)" → α enters the substitution source. -/
def priorContextLex : List (Tree Cat EWord) :=
  epithetLex ++ [bastardPedroDP]

/-! ### Structural lemmas (OOTB case via `category_preservation`) -/

/-- The epithet sentence contains a DP node. -/
theorem epithet_has_dp :
    bastardJohnArrived.containsCat .DP = true := by decide

/-- The bare sentence has no DP node. -/
theorem bare_lacks_dp :
    johnArrived.containsCat .DP = false := by decide

/-- The OOTB substitution source contains no DP. -/
theorem source_lacks_dp :
    (substitutionSource epithetLex johnArrived).all
      (fun t => !t.containsCat .DP) = true := by decide

/-- The OOTB epithet sentence is NOT a structural alternative.
Discharged by `category_preservation`: no source item has a DP, the
host has no DP, so no reachable tree has a DP — but the epithet variant
does. -/
theorem epithet_not_alternative_outOfBlue :
    bastardJohnArrived ∉ structuralAlternatives epithetLex johnArrived := by
  intro h
  have h_preserved := category_preservation
    (substitutionSource epithetLex johnArrived) .DP
    johnArrived bastardJohnArrived
    (by intro s hs
        have := List.all_eq_true.mp source_lacks_dp s hs
        simpa using this)
    bare_lacks_dp
    h
  exact absurd epithet_has_dp (by rw [h_preserved]; decide)

/-! ### CI content via felicity-set semantics

`expressiveCI` is the operative content function fed to `violatesMCIs`.
It models Lo Guercio's def-12 felicity-set semantics (Gutzmann 2015 /
Kaplan 1999): the bare sentence is felicitous everywhere (trivial CI);
the epithet construction is felicitous only at worlds where the speaker
holds the negative-attitude CI toward John. -/

/-- World type for the §3 example: a Bool flag for whether the speaker
believes John is a bastard at this world. -/
abbrev World : Type := Bool

/-- The speaker-belief predicate (just `w` under the Bool world model). -/
def speakerBelievesJohnBastard : World → Prop := fun w => w = true

/-- A tree carries the epithet CI iff it contains a DP node (structural
proxy for "the epithet construction is present"; see Implementation
notes). -/
abbrev hasEpithetStructure (φ : Tree Cat EWord) : Prop :=
  φ.containsCat .DP = true

/-- Felicity-set CI content ([gutzmann-2015] / [kaplan-1999];
adopted by Lo Guercio (paper def 12, p. 9)).

`expressiveCI φ w` holds iff φ is felicitous at world w on the
CI dimension: either it doesn't carry the epithet CI (true vacuously
for non-epithet sentences) or the speaker actually believes the CI
content at w (the felicity condition for using the epithet). -/
def expressiveCI : Tree Cat EWord → World → Prop :=
  fun φ w => ¬ hasEpithetStructure φ ∨ speakerBelievesJohnBastard w

/-- The epithet variant is CI-stronger than the bare sentence: the bare
sentence is felicitous at every world; the epithet variant only at
worlds where the speaker believes. -/
theorem epithet_ciStronger_than_bare :
    (∀ w, expressiveCI bastardJohnArrived w → expressiveCI johnArrived w) ∧
    (∃ w, expressiveCI johnArrived w ∧ ¬ expressiveCI bastardJohnArrived w) := by
  refine ⟨?_, ?_⟩
  · intro w _
    left
    show ¬ johnArrived.containsCat .DP = true
    rw [bare_lacks_dp]; decide
  · refine ⟨false, ?_, ?_⟩
    · left; show ¬ johnArrived.containsCat .DP = true
      rw [bare_lacks_dp]; decide
    · rintro (h | h)
      · exact h epithet_has_dp
      · exact Bool.false_ne_true h

/-! ### Thesis discharge — the OOTB / priorMention contrast -/

/-- **Out of the blue**, the bare sentence "John arrived first" does NOT
violate MCIs!: no formal alternative in the substitution source supplies
stronger epithet-CI content than the bare sentence itself.

The proof works by contradiction. Any φ' witnessing `violatesMCIs` must
have `¬ expressiveCI φ' w` at some world — which by the felicity-set
definition forces `hasEpithetStructure φ' = True`, i.e. φ' contains a
DP. But `category_preservation` says no Katzir-reachable tree from the
DP-free source has a DP. Contradiction. -/
theorem outOfBlue_no_ACI :
    ¬ violatesMCIs (W := EWord) (World := World)
      (katzirSource epithetLex) expressiveCI johnArrived (fun _ => True) := by
  rintro ⟨φ', hφ', _himp, ⟨w, _h_host, h_alt⟩, _⟩
  -- h_alt : ¬ expressiveCI φ' w  ⟹  hasEpithetStructure φ' ∧ ¬ speakerBelieves w
  have hStruct : hasEpithetStructure φ' := by
    by_contra hNoStruct
    exact h_alt (Or.inl hNoStruct)
  -- But category_preservation forbids DP in any reachable tree
  have h_preserved : φ'.containsCat .DP = false :=
    category_preservation
      (substitutionSource epithetLex johnArrived) .DP
      johnArrived φ'
      (by intro s hs
          have := List.all_eq_true.mp source_lacks_dp s hs
          simpa using this)
      bare_lacks_dp
      hφ'
  exact absurd hStruct (by rw [show hasEpithetStructure φ' = (φ'.containsCat .DP = true) from rfl,
                              h_preserved]; decide)

/-- **Prior mention** (paper (20a)): when an alternative source
makes the epithet variant `bastardJohnArrived` reachable (by Fox-Katzir
def 41 clause (a): "α is contextually relevant in c (e.g., by virtue
of having been mentioned)" — the second conjunct's `[DP that bastard
Pedro]` enters the substitution source for the first conjunct's
alternatives), the bare sentence violates MCIs!.

The reachability is supplied as a hypothesis (`h_reach`) rather than
proved constructively. The paper's substitution-source clause (a) IS
what provides this hypothesis: the constructive proof would require
either modeling the bare-name subject as `[DP [N john]]` (paper (24)
notation) — which breaks the `category_preservation` route used by
`outOfBlue_no_ACI` — or a stronger structural-preservation lemma
distinguishing 1-child from multi-child DPs. Either route is a
substrate refactor and is flagged in the Todo bullet for
`expressiveCI`'s compositional-interpretation upgrade. -/
theorem priorMention_yes_ACI
    (priorSrc : Alternatives.AlternativeSource (Tree Cat EWord))
    (h_reach : bastardJohnArrived ∈ priorSrc johnArrived) :
    violatesMCIs (W := EWord) (World := World)
      priorSrc expressiveCI johnArrived (fun _ => True) :=
  ⟨bastardJohnArrived, h_reach,
    epithet_ciStronger_than_bare.1,
    epithet_ciStronger_than_bare.2,
    trivial⟩

/-- **The paper's central contrast** (paper §3.2.1, contrasting (18)-(19)
with (20)-(23)): same content function, same host sentence, two
substitution sources — opposite `violatesMCIs` outcomes. The contrast
turns purely on whether the CI-stronger formal alternative is in the
source (the second hypothesis); under `expressiveCI` the epithet IS
CI-stronger in both cases.

This is the operational content of Lo Guercio's claim that ACI
licensing depends on *whether the CI alternative is a formal
alternative*, NOT on whether it is theoretically CI-stronger. -/
theorem outOfBlue_vs_priorMention_contrast
    (priorSrc : Alternatives.AlternativeSource (Tree Cat EWord))
    (h_reach : bastardJohnArrived ∈ priorSrc johnArrived) :
    ¬ violatesMCIs (W := EWord) (World := World)
        (katzirSource epithetLex) expressiveCI johnArrived (fun _ => True) ∧
    violatesMCIs (W := EWord) (World := World)
        priorSrc expressiveCI johnArrived (fun _ => True) :=
  ⟨outOfBlue_no_ACI, priorMention_yes_ACI priorSrc h_reach⟩

end LoGuercio2025
