import Linglib.Semantics.Degree.Boundedness
import Linglib.Syntax.Category.Degree.Basic

/-!
# Bresnan 1973: syntax of the comparative clause construction

[bresnan-1973] (Linguistic Inquiry 4) argues that underlying every English
comparative is a quantifier phrase: a Det position hosting -er, -est, as,
too, so, that, or nothing over a Q drawn from much, many, little, few,
enough. Three rules derive the surface forms — -er Encliticizing (20), Much
Deletion (10), and the suppletions of (7) and (223), so *more* is -er +
much — and the than-clause, always underlyingly clausal, loses a
constituent featurally nondistinct from the head under Comparative
Deletion. The four introductory puzzles (A)–(D) then each turn on one
structural fact about the head and the deleted constituent.

## Main definitions

* `Det`, `Q`, `QP`, `suppletion`, `muchDeletionApplies` — the QP structure
  (6), (108)–(109), and the morphological rules.
* `DeletionTarget`, `identityHolds` — the nondistinctness condition on
  Comparative Deletion.
* `ThanClauseType`, `BresnanThanClauseAnalysis`, `bresnanAnalysisOf` — every
  than-phrase as a clause under partial or maximal deletion.

## Main results

* `massParadigm_suppletion_consistent`, `countParadigm_suppletion_consistent`
  — the (4) and (5) paradigms against the suppletion rules.
* `enough_requires_null_det` — (107): *enough* is a Q subcategorized for a
  null Det.
* `puzzleA_from_head`, `puzzleB_from_partitivity`,
  `puzzleC_from_encliticizing`, `puzzleD_from_measure_constraint` — the
  acceptability pattern of each introductory puzzle derived from the one
  structural bit the paper's Section 2 account assigns it.
* `subdeletion_identity_holds`, `np_qp_identity_fails` — the identity
  condition at work.

## References

* [bresnan-1973] — the paper.
-/

namespace Bresnan1973

open Degree (Head)
open Degree (ScalePolarity)

/-- The two syntactic forms of than-clauses: phrasal "than Bill" vs
    clausal "than Bill is tall". -/
inductive ThanClauseType where
  | phrasal
  | clausal
  deriving DecidableEq, Repr
/-! ### QP Structure (Det + Q) -/

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
  deriving DecidableEq, Repr

/-- The Q (quantity) head: `much`, `many`, `little`, `few`, `enough`.
    Bresnan's central claim: these are the deep-structure elements
    underlying all comparative morphology. -/
inductive Q where
  | much     -- mass/degree quantity (selects mass nouns, adjectives, adverbs)
  | many     -- count quantity (selects count nouns)
  | little   -- negative mass/degree (antonym of much)
  | few      -- negative count (antonym of many)
  | enough   -- sufficiency (subcategorizes for null Det)
  deriving DecidableEq, Repr

/-- The QP: Bresnan's degree phrase structure. -/
structure QP where
  det : Det
  q : Q
  deriving DecidableEq, Repr

/-! ### Bridge: QP → Head -/

/-- Map Bresnan's QP Det to the modern DegP type classification.
    The Det determines the comparison type; Q determines mass/count. -/
def Det.toHead : Det → Head
  | .er    => .comparative
  | .est   => .superlative
  | .as_   => .equative
  | .too   => .excessive
  | .null  => .sufficiency   -- enough has null Det
  | .so    => .excessive     -- so patterns with too for degree
  | .that_ => .excessive     -- that much → degree specification
  | .any_  => .comparative   -- any + -er in Det
  | .no_   => .comparative   -- no + -er in Det

/-- The modern Head inventory is recoverable from Bresnan's Det. -/
theorem head_comparative_from_er : Det.toHead .er = .comparative := rfl
theorem head_equative_from_as : Det.toHead .as_ = .equative := rfl
theorem head_superlative_from_est : Det.toHead .est = .superlative := rfl
theorem head_excessive_from_too : Det.toHead .too = .excessive := rfl

/-! ### Morphological Derivation -/

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

/-! ### The four puzzles ((242), (256), (273), (296))

Section 2's method: identify the head, then the constituent deleted from
the clause under nondistinctness. Each puzzle turns on one structural bit,
and the acceptability pattern follows from it. -/

/-- (242): the head is either the bare AP — the reduced-relative source of
(a) and (c), (251) — or the predicative NP `[x much tall] a man` of the
AP-shifted source (243) for (b) and (d); with an NP head the clause
predicates that NP of the standard, fine for *my father*, anomalous for
*my mother*. -/
structure TallerManDatum where
  sentence : String
  /-- The head is the predicative NP of (243), not the bare AP. -/
  headIsPredNP : Bool
  /-- The standard can be predicated of the head NP: *my father is a man*. -/
  standardFitsHead : Bool
  acceptable : Bool
  deriving Repr

def puzzleA : List TallerManDatum :=
  [⟨"I've never seen a man taller than my father", false, true, true⟩,
   ⟨"I've never seen a taller man than my father", true, true, true⟩,
   ⟨"I've never seen a man taller than my mother", false, false, true⟩,
   ⟨"??I've never seen a taller man than my mother", true, false, false⟩]

/-- Puzzle (A) derived: a sentence is anomalous exactly when the head is
the predicative NP and the standard fails to fit it. -/
theorem puzzleA_from_head :
    ∀ d ∈ puzzleA, d.acceptable = (!d.headIsPredNP || d.standardFitsHead) := by
  decide

/-- (256): adverbial *more* modifies the VP and needs only a matching
adverbial in the clause (257) — available with intransitives too — while
partitive *more* is embedded in the object NP and needs a matching
partitive there (260); *sleeps* supplies none. -/
structure CaviarDatum where
  sentence : String
  /-- The head QP is the partitive inside the object NP. -/
  headIsPartitive : Bool
  /-- The clause supplies an object NP to host a matching partitive. -/
  clauseHasObjectNP : Bool
  acceptable : Bool
  deriving Repr

def puzzleB : List CaviarDatum :=
  [⟨"Jack eats caviar more than he eats mush", false, true, true⟩,
   ⟨"Jack eats more caviar than he eats mush", true, true, true⟩,
   ⟨"Jack eats caviar more than he sleeps", false, false, true⟩,
   ⟨"*Jack eats more caviar than he sleeps", true, false, false⟩]

/-- Puzzle (B) derived: a partitive head demands an object NP in the
clause. -/
theorem puzzleB_from_partitivity :
    ∀ d ∈ puzzleB, d.acceptable = (!d.headIsPartitive || d.clauseHasObjectNP) := by
  decide

/-- (273): the synthetic comparative arises only when the QP is a left
branch of the AP with the adjective — -er encliticizes (20) and *much*
deletes (10); comparison across adjectives leaves the QP outside the AP
(272), so only analytic *more angry* survives. -/
structure AngryDatum where
  sentence : String
  /-- The surface form is the synthetic comparative (*angrier*). -/
  synthetic : Bool
  /-- The QP is AP-internal, a left branch with the adjective. -/
  qpInsideAP : Bool
  acceptable : Bool
  deriving Repr

def puzzleC : List AngryDatum :=
  [⟨"I am more angry today than I was yesterday", false, true, true⟩,
   ⟨"I am angrier today than I was yesterday", true, true, true⟩,
   ⟨"I am more angry than sad", false, false, true⟩,
   ⟨"*I am angrier than sad", true, false, false⟩]

/-- Puzzle (C) derived: the synthetic form needs the AP-internal QP. -/
theorem puzzleC_from_encliticizing :
    ∀ d ∈ puzzleC, d.acceptable = (!d.synthetic || d.qpInsideAP) := by decide

/-- (296)–(297): privative adjectives reject definite measures — *five
feet tall* against *\*five feet short* — so a derivation equating the Q
that modifies *short* with a definite measure phrase fails nondistinctness,
while *shorter than five feet* requires no such equation. -/
structure ShortDatum where
  sentence : String
  /-- The derivation equates a Q modifying a privative adjective with a
  definite measure phrase. -/
  definiteMeasureOnPrivative : Bool
  acceptable : Bool
  deriving Repr

def puzzleD : List ShortDatum :=
  [⟨"Mary is more than six feet tall", false, true⟩,
   ⟨"Mary is taller than six feet", false, true⟩,
   ⟨"*Mary is more than five feet short", true, false⟩,
   ⟨"Mary is shorter than five feet", false, true⟩]

/-- Puzzle (D) derived: the (297) identity failure is the only source of
anomaly in the paradigm. -/
theorem puzzleD_from_measure_constraint :
    ∀ d ∈ puzzleD, d.acceptable = !d.definiteMeasureOnPrivative := by decide

/-! ### Comparative Deletion (Identity Condition) -/

/-- The syntactic category of the constituent deleted from the than-clause:
    the deleted element must be featurally nondistinct from the head. -/
inductive DeletionTarget where
  | qp   -- QP deleted (measure phrase comparison / subdeletion)
  | ap   -- AP deleted (simple adjectival comparison)
  | np   -- NP deleted (predicative NP comparison)
  deriving DecidableEq, Repr

/-- The identity condition: deletion succeeds only when the clause
    constituent and the head have the same syntactic category.

    "Nondistinctness" in Bresnan's terms — the deleted constituent must be
    featurally nondistinct from the head. -/
def identityHolds (head clause : DeletionTarget) : Bool :=
  head == clause

/-- Subdeletion: "The table is longer than the door is wide."

    Head = AP (-er much long), deleted = AP (x much wide).
    Both are APs, so identity holds; the dimensions need not match, only
    the syntactic category. -/
theorem subdeletion_identity_holds :
    identityHolds .ap .ap = true := rfl

/-- `*John is more than Bill tall` fails: head = QP (-er much), but
    the matching constituent in the clause is an NP (Bill = that much).
    NP ≠ QP, so the identity condition fails. -/
theorem np_qp_identity_fails :
    identityHolds .qp .np = false := rfl

/-! ### All Than-Clauses Are Underlyingly Clausal -/

/-- Bresnan's strongest syntactic claim: all comparatives are underlyingly
    clausal — what appears as a "phrasal" comparative (*taller than Bill*)
    derives from a full clause by maximal deletion. -/
inductive BresnanThanClauseAnalysis where
  /-- Full clause with partial deletion: "than Bill is [x much tall]"
      → "than Bill is" (deletion of AP) -/
  | partialDeletion
  /-- Full clause with maximal deletion: "than Bill is [x much tall]"
      → "than Bill" (deletion of AP + copula stranding) -/
  | maximalDeletion
  deriving DecidableEq, Repr

/-- Under Bresnan's analysis, the modern `phrasal` type is just
    `maximalDeletion` of an underlying clause. -/
def bresnanAnalysisOf : ThanClauseType → BresnanThanClauseAnalysis
  | .clausal => .partialDeletion
  | .phrasal => .maximalDeletion

/-! ### Privative Adjective Measure Phrase Constraint -/

/-- Whether an adjective admits definite measure phrase modification —
    *five feet tall* against *\*five feet short*: privative adjectives do
    not admit modifiers of definite measurement, though they do permit
    comparison. -/
def admitsDefiniteMeasure (polarity : ScalePolarity) : Bool :=
  match polarity with
  | .positive => true
  | .negative => false

/-- Positive adjectives admit measure phrases. -/
theorem positive_admits_measure : admitsDefiniteMeasure .positive = true := rfl

/-- Negative adjectives reject measure phrases. -/
theorem negative_rejects_measure : admitsDefiniteMeasure .negative = false := rfl

/-- An adjective's polarity with its measure-phrase behavior: *short*
    rejects definite measure QPs, so the identity condition in Comparative
    Deletion cannot be satisfied there. -/
structure MeasurePhraseConstraintDatum where
  adjective : String
  polarity : ScalePolarity
  measurePhraseOk : Bool
  /-- "more than N units Adj" acceptable? -/
  comparativeMeasureOk : Bool
  deriving Repr

def measurePhraseConstraintData : List MeasurePhraseConstraintDatum :=
  [ { adjective := "tall", polarity := .positive
      measurePhraseOk := true, comparativeMeasureOk := true }
  , { adjective := "short", polarity := .negative
      measurePhraseOk := false, comparativeMeasureOk := false }
  , { adjective := "long", polarity := .positive
      measurePhraseOk := true, comparativeMeasureOk := true }
  , { adjective := "wide", polarity := .positive
      measurePhraseOk := true, comparativeMeasureOk := true } ]

/-- Among the dimensional adjectives, measure-phrase acceptability
    correlates with positive polarity — the classification behind puzzle
    (D). -/
theorem measurePhrase_polarity_correlation :
    ∀ d ∈ measurePhraseConstraintData,
      d.polarity = .negative → d.measurePhraseOk = false := by
  intro d hd hpol
  simp [measurePhraseConstraintData] at hd
  rcases hd with rfl | rfl | rfl | rfl <;> simp_all

/-! ### Det Inventory Paradigms -/

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

/-! ### QP Well-Formedness -/

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

end Bresnan1973
