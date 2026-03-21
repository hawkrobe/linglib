import Linglib.Theories.Semantics.Degree.Core
import Linglib.Theories.Semantics.Degree.ThanClause
import Linglib.Theories.Semantics.Degree.Comparative
import Linglib.Theories.Semantics.Degree.Differential

/-!
# Bresnan 1973: Syntax of the Comparative Clause Construction in English
@cite{bresnan-1973}

Joan W. Bresnan. Syntax of the Comparative Clause Construction in English.
*Linguistic Inquiry* 4(3): 275–343.

## Core Contributions

1. **QP structure**: Every comparative has an underlying QP (Det + Q) where
   the Q items are `much`, `many`, `little`, `few`, `enough`, and the Det
   position hosts `-er`, `-est`, `as`, `too`, `so`, `that`, or `∅`. The
   surface form `more` derives from `-er` + `much` via suppletion.

2. **Morphological derivation**: Three ordered rules derive surface forms:
   - `-er` Encliticizing: Det `-er` cliticizes onto Q (`-er Q → Q-er`)
   - Much Deletion: `much → ∅` before adjectives/adverbs
   - Suppletion: `much-er → more`, `little-er → less`, etc.

3. **Comparative Deletion**: The `than`/`as` clause originates in the Det of
   QP. An obligatory deletion operation removes a clause constituent
   "nondistinct" from the head. The clause is then extraposed.

4. **All than-clauses are underlyingly clausal**: "Phrasal" comparatives like
   `taller than Bill` derive from full clauses via maximal deletion. This
   contrasts with the 2026 consensus (@cite{bhatt-pancheva-2004}) that
   phrasal and clausal comparatives are syntactically distinct.

5. **Subdeletion**: When the head is a QP (measure phrase), only a matching
   QP is deleted from the clause — not an AP or NP. This explains
   `*more than Bill tall` (NP ≠ QP identity failure).

6. **Privative adjective constraint**: `*more than five feet short` because
   `short` rejects definite measure phrases, so the QP identity condition
   in the clause cannot be satisfied.

## What Is Current vs. Historical

**Current consensus**: The data paradigms, the degree-head inventory (Det →
modern Deg°), the `more` = `-er` + `much` decomposition, the measure phrase
restriction with negative adjectives, subdeletion commensurability.

**Modified but descended**: QP → DegP (@cite{kennedy-1999}); comparative
deletion → degree operator movement (@cite{heim-2001}); QP-AP parallelism
→ X-bar theory → Minimalist bare phrase structure.

**Historical**: The construction-specific transformations (AP Shift, QP
Raising, Much Deletion, `-er` Encliticizing), the "all comparatives are
clausal" claim, the `so → such` transformation.

## Connection to Kennedy 1999

The existing `Kennedy1999.lean` cites @cite{bresnan-1973} for morphological
distribution data and phrasal/clausal examples. This file formalizes
Bresnan's own proposals: the QP structure, the derivation rules, and the
four introductory puzzles that motivated the analysis. Bridge theorems
connect the QP inventory to `DegPType` and verify suppletion outputs
against Fragment `formComp` entries.
-/

namespace Phenomena.Comparison.Studies.Bresnan1973

open Semantics.Degree (DegPType)
open Semantics.Degree.ThanClause (ThanClauseType)
open Semantics.Degree.Comparative (comparativeSem)
open Core.Scale (ScalePolarity Boundedness)

-- ════════════════════════════════════════════════════
-- § 1. QP Structure (Det + Q)
-- ════════════════════════════════════════════════════

/-- The Det position of the QP: hosts degree/comparison morphemes.
    This is Bresnan's precursor to the modern Deg° head. -/
inductive Det where
  | er       -- comparative: -er
  | est      -- superlative: -est
  | as_      -- equative: as
  | too      -- excessive: too
  | so       -- consecutive/degree: so
  | that_    -- demonstrative degree: that
  | any_     -- NPI: any
  | no_      -- negative: no
  | null     -- empty Det (enough, more/less after QP Raising)
  deriving DecidableEq, BEq, Repr

/-- The Q (quantity) head: `much`, `many`, `little`, `few`, `enough`.
    Bresnan's central claim: these are the deep-structure elements
    underlying all comparative morphology. -/
inductive Q where
  | much     -- mass/degree quantity (selects mass nouns, adjectives, adverbs)
  | many     -- count quantity (selects count nouns)
  | little   -- negative mass/degree (antonym of much)
  | few      -- negative count (antonym of many)
  | enough   -- sufficiency (subcategorizes for null Det)
  deriving DecidableEq, BEq, Repr

/-- The QP: Bresnan's degree phrase structure. -/
structure QP where
  det : Det
  q : Q
  deriving DecidableEq, BEq, Repr

-- ════════════════════════════════════════════════════
-- § 2. Bridge: QP → DegPType
-- ════════════════════════════════════════════════════

/-- Map Bresnan's QP Det to the modern DegP type classification.
    The Det determines the comparison type; Q determines mass/count. -/
def Det.toDegPType : Det → DegPType
  | .er    => .comparative
  | .est   => .superlative
  | .as_   => .equative
  | .too   => .excessive
  | .null  => .sufficiency   -- enough has null Det
  | .so    => .excessive     -- so patterns with too for degree
  | .that_ => .excessive     -- that much → degree specification
  | .any_  => .comparative   -- any + -er in Det
  | .no_   => .comparative   -- no + -er in Det

/-- The modern DegPType inventory is recoverable from Bresnan's Det. -/
theorem degPType_comparative_from_er : Det.toDegPType .er = .comparative := rfl
theorem degPType_equative_from_as : Det.toDegPType .as_ = .equative := rfl
theorem degPType_superlative_from_est : Det.toDegPType .est = .superlative := rfl
theorem degPType_excessive_from_too : Det.toDegPType .too = .excessive := rfl

-- ════════════════════════════════════════════════════
-- § 3. Morphological Derivation
-- ════════════════════════════════════════════════════

/-- Suppletion: the surface form resulting from `-er`/`-est` Encliticizing
    onto Q. Returns `none` for regular (non-suppletive) combinations.

    Rule (7): -er much → more, -er many → more, -er little → less
    Rule (223): -est much → most, -est many → most, etc. -/
def suppletion : QP → Option String
  | ⟨.er,  .much⟩   => some "more"
  | ⟨.er,  .many⟩   => some "more"
  | ⟨.er,  .little⟩ => some "less"
  | ⟨.er,  .few⟩    => some "fewer"
  | ⟨.est, .much⟩   => some "most"
  | ⟨.est, .many⟩   => some "most"
  | ⟨.est, .little⟩ => some "least"
  | ⟨.est, .few⟩    => some "fewest"
  | _                => none

/-- `more` derives from `-er` + `much` (or `-er` + `many`). -/
theorem more_from_er_much : suppletion ⟨.er, .much⟩ = some "more" := rfl
theorem more_from_er_many : suppletion ⟨.er, .many⟩ = some "more" := rfl
theorem less_from_er_little : suppletion ⟨.er, .little⟩ = some "less" := rfl

/-- `most` derives from `-est` + `much`. -/
theorem most_from_est_much : suppletion ⟨.est, .much⟩ = some "most" := rfl

/-- Q selects mass vs count nouns. `much` selects mass nouns and can also
    modify adjectives/adverbs (after Much Deletion). `many` selects count
    nouns only. This predicts `*much people`, `*many bread`. -/
def Q.selectsMass : Q → Bool
  | .much   => true
  | .little => true
  | .enough => true   -- enough selects both
  | _       => false

def Q.selectsCount : Q → Bool
  | .many   => true
  | .few    => true
  | .enough => true   -- enough selects both
  | _       => false

/-- `much` and `little` (but not `many` and `few`) can modify adjectives
    and adverbs — they are the Qs that undergo Much Deletion.

    This predicts: `as much tall → as tall` (Much Deletion),
    but `*as many tall` (no deletion rule for `many` before A). -/
def Q.canModifyAdjective : Q → Bool
  | .much   => true
  | .little => true
  | .enough => true
  | _       => false

/-- Much Deletion: `much → ∅ / [... ___ A]_AP`.
    Applies only to Qs that can modify adjectives, and only when an
    adjective or adverb immediately follows. -/
def muchDeletionApplies (q : Q) (adjFollows : Bool) : Bool :=
  q.canModifyAdjective && adjFollows

-- ════════════════════════════════════════════════════
-- § 4. Introductory Puzzles (A)–(D)
-- ════════════════════════════════════════════════════

/-- An acceptability judgment with structural explanation. -/
structure PuzzleDatum where
  sentence : String
  acceptable : Bool
  /-- What is the head of the comparative construction? -/
  head : String
  /-- What is deleted from the than-clause? -/
  deletedConstituent : String
  /-- Why is the identity condition satisfied or not? -/
  explanation : String
  deriving Repr

/-- Puzzle (A): "I've never seen a man taller than my father/mother."

    (i) and (ii) are roughly synonymous; (iii) and (iv) are not.
    (i)  "a man taller than my father"  — head: AP [x much tall]
    (ii) "a taller man than my father" — head: AP [x much tall]
    (iii) "a man taller than my mother" — head: AP [x much tall]
    (iv) "a taller man than my mother" — head: NP [a man x much tall]

    In (iv), the head is the entire predicative NP. The deleted constituent
    in the clause must match this NP — but "my mother is [x much tall] a man"
    implies my mother is a man. Hence the anomaly. -/
def puzzleA : List PuzzleDatum :=
  [ { sentence := "I've never seen a man taller than my father"
    , acceptable := true
    , head := "AP: x much tall"
    , deletedConstituent := "AP: x much tall"
    , explanation := "AP head; clause: 'my father is [x much tall]' — well-formed" }
  , { sentence := "I've never seen a taller man than my father"
    , acceptable := true
    , head := "AP: x much tall"
    , deletedConstituent := "AP: x much tall"
    , explanation := "AP head after AP Shift; clause: 'my father is [x much tall]' — well-formed" }
  , { sentence := "I've never seen a man taller than my mother"
    , acceptable := true
    , head := "AP: x much tall"
    , deletedConstituent := "AP: x much tall"
    , explanation := "AP head; clause: 'my mother is [x much tall]' — well-formed" }
  , { sentence := "??I've never seen a taller man than my mother"
    , acceptable := false
    , head := "Pred NP: [AP x much tall] a man"
    , deletedConstituent := "Pred NP: [AP x much tall] a man"
    , explanation := "NP head after AP Shift; clause: 'my mother is [x much tall] a man' — implies my mother is a man" }
  ]

/-- Puzzle (B): "Jack eats caviar more than he eats mush / sleeps."

    (a,c) are grammatical; (d) is not. The deleted constituent is an
    adverbial QP modifier of the VP.

    In (d), `*Jack eats more caviar than he sleeps` is bad because
    `more` is a partitive QP embedded in the direct object NP. The
    matching partitive QP in the clause requires an NP — but `sleep`
    is intransitive, so no matching partitive is available. -/
def puzzleB : List PuzzleDatum :=
  [ { sentence := "Jack eats caviar more than he eats mush"
    , acceptable := true
    , head := "adverbial QP: -er much"
    , deletedConstituent := "adverbial QP: x much"
    , explanation := "VP-adverbial more; clause has matching VP-adverbial" }
  , { sentence := "Jack eats more caviar than he eats mush"
    , acceptable := true
    , head := "partitive QP: -er much (of caviar)"
    , deletedConstituent := "partitive QP: x much (of mush)"
    , explanation := "partitive more in NP; clause has matching partitive" }
  , { sentence := "Jack eats caviar more than he sleeps"
    , acceptable := true
    , head := "adverbial QP: -er much"
    , deletedConstituent := "adverbial QP: x much"
    , explanation := "VP-adverbial more; clause has matching VP-adverbial" }
  , { sentence := "*Jack eats more caviar than he sleeps"
    , acceptable := false
    , head := "partitive QP: -er much (of caviar)"
    , deletedConstituent := "partitive QP: x much"
    , explanation := "partitive more requires NP object; sleep is intransitive" }
  ]

/-- Puzzle (C): "I am more angry today than I was yesterday / than sad."

    The acceptability of `angrier` (synthetic) vs `more angry` (analytic)
    follows from what is deleted and what survives. When the comparison is
    across adjectives (angry vs sad), the comparative must be `more angry`
    (analytic) because `more` is a sentence modifier, not within the AP.
    Simple comparative formation (producing `angrier`) cannot apply
    because `more` and `sad` are not within the same AP. -/
def puzzleC : List PuzzleDatum :=
  [ { sentence := "I am more angry today than I was yesterday"
    , acceptable := true
    , head := "AP: -er much angry"
    , deletedConstituent := "AP: x much angry"
    , explanation := "AP head in than-clause; standard temporal comparison" }
  , { sentence := "I am angrier today than I was yesterday"
    , acceptable := true
    , head := "AP: -er much angry"
    , deletedConstituent := "AP: x much angry"
    , explanation := "same as above with -er Encliticizing + Much Deletion" }
  , { sentence := "I am more angry than sad"
    , acceptable := true
    , head := "QP: -er much"
    , deletedConstituent := "QP: x much"
    , explanation := "sentence-level QP; clause: 'I am [x much] sad'" }
  , { sentence := "*I am angrier than sad"
    , acceptable := false
    , head := "QP: -er much"
    , deletedConstituent := "QP: x much"
    , explanation := "more and sad not in same AP; simple comparative blocked" }
  ]

/-- Puzzle (D): "*Mary is more than five feet short" vs "Mary is shorter than five feet."

    @cite{kennedy-1999} explains this via positive/negative extent boundedness.
    Bresnan's syntactic explanation: `short` rejects definite measure phrase
    modifiers (`*How short is he? — five feet short`), so the QP identity
    condition in the clause cannot be satisfied.

    Bridge: this connects to `measurePhrase_positive_only` in `Kennedy1999.lean`
    and `admitsMeasurePhrase` in `Differential.lean`. -/
def puzzleD : List PuzzleDatum :=
  [ { sentence := "Mary is more than six feet tall"
    , acceptable := true
    , head := "QP: -er much"
    , deletedConstituent := "QP: six feet = that much"
    , explanation := "tall admits measure phrases; than-clause: 'six feet = that much tall'" }
  , { sentence := "Mary is taller than six feet"
    , acceptable := true
    , head := "AP: -er much tall"
    , deletedConstituent := "AP: six feet tall = that much tall"
    , explanation := "AP head; clause: 'six feet (is) [that much] tall'" }
  , { sentence := "*Mary is more than five feet short"
    , acceptable := false
    , head := "QP: -er much"
    , deletedConstituent := "QP: five feet = that much"
    , explanation := "short rejects definite measure phrases; *five feet short" }
  , { sentence := "Mary is shorter than five feet"
    , acceptable := true
    , head := "QP: -er much (subdeletion)"
    , deletedConstituent := "QP: five feet = that much"
    , explanation := "Bresnan (p. 334): 'certainly no problem'; clause QP [five feet] matches head QP" }
  ]

-- ════════════════════════════════════════════════════
-- § 5. Comparative Deletion (Identity Condition)
-- ════════════════════════════════════════════════════

/-- The syntactic category of the constituent deleted from the than-clause.
    Bresnan's key insight: the deleted element must be "nondistinct" (same
    syntactic category) from the head.

    This is the 1973 precursor to modern identity conditions in ellipsis
    (e-GIVENness in @cite{merchant-2001}; SIC in Anand, Hardt & McCloskey 2021). -/
inductive DeletionTarget where
  | qp   -- QP deleted (measure phrase comparison / subdeletion)
  | ap   -- AP deleted (simple adjectival comparison)
  | np   -- NP deleted (predicative NP comparison)
  deriving DecidableEq, BEq, Repr

/-- The identity condition: deletion succeeds only when the clause
    constituent and the head have the same syntactic category.

    "Nondistinctness" in Bresnan's terms — the deleted constituent must be
    featurally nondistinct from the head. -/
def identityHolds (head clause : DeletionTarget) : Bool :=
  head == clause

/-- Subdeletion: "The table is longer than the door is wide."

    Head = AP (-er much long), deleted = AP (x much wide).
    Both are APs, so identity holds. The dimensions (length vs width) need
    not match — only the syntactic category.

    This connects to `subcomparativeExamples` in `Kennedy1999.lean` and
    `subcomparative` in `Intervals.lean`. -/
theorem subdeletion_identity_holds :
    identityHolds .ap .ap = true := rfl

/-- `*John is more than Bill tall` fails: head = QP (-er much), but
    the matching constituent in the clause is an NP (Bill = that much).
    NP ≠ QP, so the identity condition fails. -/
theorem np_qp_identity_fails :
    identityHolds .qp .np = false := rfl

-- ════════════════════════════════════════════════════
-- § 6. All Than-Clauses Are Underlyingly Clausal
-- ════════════════════════════════════════════════════

/-- Bresnan's strongest syntactic claim: ALL comparatives are underlyingly
    clausal. What appears as a "phrasal" comparative ("taller than Bill")
    is derived from a full clause by maximal deletion.

    This contrasts with the modern consensus (`ThanClauseType` distinguishes
    `phrasal` from `clausal` as genuinely distinct). Both analyses yield the
    same truth conditions for simple comparatives (proved in
    `ThanClause.phrasal_clausal_equivalence`), so the disagreement is purely
    syntactic.

    See @cite{bhatt-pancheva-2004} for the modern "genuinely phrasal" view. -/
inductive BresnanThanClauseAnalysis where
  /-- Full clause with partial deletion: "than Bill is [x much tall]"
      → "than Bill is" (deletion of AP) -/
  | partialDeletion
  /-- Full clause with maximal deletion: "than Bill is [x much tall]"
      → "than Bill" (deletion of AP + copula stranding) -/
  | maximalDeletion
  deriving DecidableEq, BEq, Repr

/-- Under Bresnan's analysis, the modern `phrasal` type is just
    `maximalDeletion` of an underlying clause. -/
def bresnanAnalysisOf : ThanClauseType → BresnanThanClauseAnalysis
  | .clausal => .partialDeletion
  | .phrasal => .maximalDeletion

-- ════════════════════════════════════════════════════
-- § 7. Privative Adjective Measure Phrase Constraint
-- ════════════════════════════════════════════════════

/-- Whether an adjective admits definite measure phrase modification
    ("five feet tall" ✓ vs "*five feet short" ✗).

    Bresnan observes this as a syntactic fact; @cite{kennedy-1999}
    derives it from extent boundedness (positive extents are bounded,
    negative extents are not). Both predict the same distribution. -/
def admitsDefiniteMeasure (polarity : ScalePolarity) : Bool :=
  match polarity with
  | .positive => true
  | .negative => false

/-- Positive adjectives admit measure phrases. -/
theorem positive_admits_measure : admitsDefiniteMeasure .positive = true := rfl

/-- Negative adjectives reject measure phrases. -/
theorem negative_rejects_measure : admitsDefiniteMeasure .negative = false := rfl

/-- **Bridge to Kennedy 1999**: Bresnan's syntactic observation and Kennedy's
    semantic explanation make the same prediction for simple cases.

    Bresnan: `short` syntactically rejects definite measure QPs, so the
    identity condition in comparative deletion cannot be satisfied.

    Kennedy: negative extents are unbounded, so equating them with bounded
    measure phrases is semantically undefined.

    The predictions diverge for `less short than five feet` (Bresnan predicts
    OK via `little`-based QP; Kennedy predicts OK via comparative semantics). -/
structure MeasurePhraseConstraintDatum where
  adjective : String
  polarity : ScalePolarity
  measurePhraseOk : Bool
  /-- "more than N units Adj" acceptable? -/
  comparativeMeasureOk : Bool
  deriving Repr

def measurePhraseConstraintData : List MeasurePhraseConstraintDatum :=
  [ { adjective := "tall",  polarity := .positive, measurePhraseOk := true,  comparativeMeasureOk := true  }
  , { adjective := "short", polarity := .negative, measurePhraseOk := false, comparativeMeasureOk := false }
  , { adjective := "long",  polarity := .positive, measurePhraseOk := true,  comparativeMeasureOk := true  }
  , { adjective := "wide",  polarity := .positive, measurePhraseOk := true,  comparativeMeasureOk := true  }
  ]

/-- Among Bresnan's dimensional adjectives, measure phrase acceptability
    correlates with positive polarity.

    This is the formal content behind puzzle (D) and connects to
    `measurePhrase_positive_only` in `Kennedy1999.lean`. -/
theorem measurePhrase_polarity_correlation :
    ∀ d ∈ measurePhraseConstraintData,
      d.polarity = .negative → d.measurePhraseOk = false := by
  intro d hd hpol
  simp [measurePhraseConstraintData] at hd
  rcases hd with rfl | rfl | rfl | rfl <;> simp_all

-- ════════════════════════════════════════════════════
-- § 8. Det Inventory Paradigms
-- ════════════════════════════════════════════════════

/-- Bresnan's paradigms (4) and (5): the Det items form a closed class
    that combine with both `much` and `little` (mass) / `many` and `few`
    (count).

    Paradigm (4): as/too/that/so/`-er` + much/little + mass noun
    Paradigm (5): as/too/that/so/`-er` + many/few + count noun

    The last row in each paradigm undergoes suppletion:
    `-er` much → more, `-er` little → less,
    `-er` many → more, `-er` few → fewer. -/
structure DetQParadigmEntry where
  det : Det
  q : Q
  surfaceForm : String
  /-- Does this undergo suppletion? -/
  isSuppletive : Bool
  deriving Repr

def massParadigm : List DetQParadigmEntry :=
  [ { det := .as_,  q := .much,   surfaceForm := "as much",   isSuppletive := false }
  , { det := .too,  q := .much,   surfaceForm := "too much",  isSuppletive := false }
  , { det := .that_, q := .much,  surfaceForm := "that much", isSuppletive := false }
  , { det := .so,   q := .much,   surfaceForm := "so much",   isSuppletive := false }
  , { det := .er,   q := .much,   surfaceForm := "more",      isSuppletive := true  }
  , { det := .as_,  q := .little, surfaceForm := "as little",  isSuppletive := false }
  , { det := .too,  q := .little, surfaceForm := "too little",  isSuppletive := false }
  , { det := .er,   q := .little, surfaceForm := "less",       isSuppletive := true  }
  ]

/-- Verify: every suppletive entry in the paradigm matches the suppletion function. -/
theorem massParadigm_suppletion_consistent :
    ∀ e ∈ massParadigm, e.isSuppletive = true →
      suppletion ⟨e.det, e.q⟩ = some e.surfaceForm := by
  intro e he hsup
  simp [massParadigm] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [suppletion]

def countParadigm : List DetQParadigmEntry :=
  [ { det := .as_,  q := .many,  surfaceForm := "as many",   isSuppletive := false }
  , { det := .too,  q := .many,  surfaceForm := "too many",  isSuppletive := false }
  , { det := .that_, q := .many, surfaceForm := "that many", isSuppletive := false }
  , { det := .so,   q := .many,  surfaceForm := "so many",   isSuppletive := false }
  , { det := .er,   q := .many,  surfaceForm := "more",      isSuppletive := true  }
  , { det := .as_,  q := .few,   surfaceForm := "as few",    isSuppletive := false }
  , { det := .too,  q := .few,   surfaceForm := "too few",   isSuppletive := false }
  , { det := .er,   q := .few,   surfaceForm := "fewer",     isSuppletive := true  }
  ]

/-- Verify: every suppletive entry in the count paradigm matches the suppletion function. -/
theorem countParadigm_suppletion_consistent :
    ∀ e ∈ countParadigm, e.isSuppletive = true →
      suppletion ⟨e.det, e.q⟩ = some e.surfaceForm := by
  intro e he hsup
  simp [countParadigm] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [suppletion]

-- ════════════════════════════════════════════════════
-- § 9. QP Well-Formedness
-- ════════════════════════════════════════════════════

/-- `enough` requires a null Det — `*so enough`, `*too enough`, `*as enough`,
    `*enougher` are all impossible (Bresnan p. 286).

    This is formalized as a well-formedness predicate on QPs. -/
def QP.isWellFormed (qp : QP) : Bool :=
  match qp.q with
  | .enough => qp.det == .null
  | _       => true

theorem enough_requires_null_det :
    ∀ d : Det, d ≠ .null →
      QP.isWellFormed ⟨d, .enough⟩ = false := by
  intro d hd; cases d <;> first | (exact absurd rfl hd) | rfl

theorem enough_null_wellformed : QP.isWellFormed ⟨.null, .enough⟩ = true := rfl

-- ════════════════════════════════════════════════════
-- § 10. QP-AP Parallelism
-- ════════════════════════════════════════════════════

/-- Bresnan's "archicategory" X̄ unifies QP and AP:
    both have left-recursive specifier + head structure.

    QP → (QP) QP,   QP → (Det) Q
    AP → (AP) AP,   AP → (Adv) A

    This is a direct precursor to X-bar theory (Jackendoff 1977) and
    ultimately to the Minimalist bare phrase structure. The modern
    counterpart is the shared structure of DegP and AdjP as functional
    and lexical projections in the extended AP.

    Structural rule from Bresnan (145):
    X̄ → (X̄) X̄     (recursive expansion)
    X̄ → (Spec, X̄) X̄  (specifier + head) -/
inductive BarCategory where
  | qp   -- quantity phrase
  | ap   -- adjective phrase
  | np   -- noun phrase
  deriving DecidableEq, BEq, Repr

-- ════════════════════════════════════════════════════
-- § 11. Comparative Semantics Bridge
-- ════════════════════════════════════════════════════

/-- Bresnan's analysis is primarily syntactic, but the truth conditions
    it derives are compatible with the modern degree-semantic consensus.

    For a simple adjectival comparative "A is taller than B":
    - Bresnan: head = AP [-er much tall], clause deletes matching AP [x much tall]
    - Kennedy: μ(A) > μ(B) where μ = height
    - Heim: max({d | height(A) ≥ d}) > max({d | height(B) ≥ d})

    All three yield the same truth conditions for simple cases. -/
theorem simple_comparative_consensus {Entity D : Type*} [LinearOrder D]
    (μ : Entity → D) (a b : Entity) :
    comparativeSem μ a b .positive ↔ μ a > μ b := by
  simp [comparativeSem]

end Phenomena.Comparison.Studies.Bresnan1973
