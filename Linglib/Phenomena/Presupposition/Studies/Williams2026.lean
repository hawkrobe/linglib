import Linglib.Theories.Semantics.Verb.VerbEntry

/-!
# Williams 2026: The Presuppositions of *forget*
@cite{williams-2026} @cite{kiparsky-kiparsky-1970} @cite{white-2014}

Empirical data and classification from @cite{williams-2026}, who argues
that *forget* is **canonically factive, independent of complement type**,
but the **content** of the factive presupposition varies by frame:

- **Cognition reading** (finite CP): non-modal — directly presupposes complement truth
- **PRO-ing gerund**: non-modal — patterns with finite CP, refuting an MCA-only account
- **Psych-action reading** (plain infinitive): modal — presupposes a modalized
  proposition (an obligation/plan held before the forgetting)

The cross-linguistic generalization is the **SMINC** (Selectivity of Modal
Insertion in Non-finite Contexts): a covert modal heads the complement of
*forget* iff the embedded lexical verb is a plain infinitive, and is banned
elsewhere. Williams' Table 1 (§3.1.3) attests this pattern across English,
Spanish, Italian, German, and Hungarian; this file records the English
data points.

## Scope

Williams' opening contrast (his (1)/(2)) is that *forgot to V* both fails
to presuppose the lower event AND is implicatively-negative
(*forgot to V* → ¬V; @cite{karttunen-1971}, Karttunen 1971a, Horn 1972,
Jackendoff 1985). Williams (fn 1) brackets the implicative-negative entailment
to focus on presupposition; he does not refute it. The
`implicativeNegative` field below records it for cross-paper consistency
with the Karttunen tradition (formalized in
`Phenomena/Complementation/Studies/Karttunen1971.lean` and
`Theories/Semantics/Causation/Implicative.lean`).

A second presupposition Williams identifies for the psych-action reading,
the *necessity-and-sufficiency* presupposition (his (5b), citing Karttunen
1971a — "if John stopped, it is because he remembered to do it") is left
to future work in the paper and is not encoded here.

## Naming

The English Fragment splits *forget* into two `VerbEntry` records:
`forget` (negative implicative, infinitival) and `forget_rog`
(factive/rogative, finite). Williams argues these are *one* lexical item
with uniform factivity and a frame-driven presupposition split (the
pre-existence analysis is in `Theories/Semantics/Attitudes/PreExistence.lean`).
The Fragment split is a practical separation of entailment patterns;
`White2014.lean` makes the consistency claim formal.

-/

namespace Phenomena.Presupposition.Studies.Williams2026

open Core.Verbs (ComplementType)

/-- Whether a factive presupposition has modal content.

    Following @cite{williams-2026}: with finite CPs and gerunds, the
    presupposition is *non-modal* (event truth); with plain infinitives,
    it is *modal* (Williams' (5a): "John was supposed to V"). -/
inductive PresupContent where
  /-- Directly presupposes complement truth (Williams (4a)). -/
  | nonModal
  /-- Presupposes a modalized proposition: covert Mod over the embedded
      VP, yielding an obligation reading (Williams (5a)). -/
  | modal
  deriving DecidableEq, Repr

/-- An empirical judgment about *forget*'s presupposition in a given
    complement frame.

    Every entry has a presupposition (uniform factivity per Williams).
    The `content` field records the modal/non-modal split; the
    `implicativeNegative` field records the orthogonal Karttunen
    entailment that Williams (fn 1) brackets. -/
structure ForgetJudgment where
  /-- Complement frame being tested. -/
  frame : ComplementType
  /-- Example sentence (Williams uses *John* throughout §1–§3.1). -/
  sentence : String
  /-- Paraphrase of what is presupposed. -/
  presupParaphrase : String
  /-- Modal vs. non-modal presupposition content. -/
  content : PresupContent
  /-- Negative implicative entailment (*forgot to V* → ¬V; Karttunen 1971a).
      Williams (fn 1) brackets this; recorded here for cross-paper
      consistency with @cite{karttunen-1971}. -/
  implicativeNegative : Bool
  deriving DecidableEq, Repr

/-! ## Cognition reading — finite CP

Williams (1)/(4): "John forgot that he stopped by the flower shop"
presupposes that John stopped. This is the canonical factive reading
recognized since @cite{kiparsky-kiparsky-1970}.
-/

def forget_finiteCP : ForgetJudgment where
  frame := .finiteClause
  sentence := "John forgot that he stopped by the flower shop"
  presupParaphrase := "John stopped by the flower shop"
  content := .nonModal
  implicativeNegative := false

/-! ## English PRO-ing gerund

Williams (7)/(9), §3.1.1: "John forgot stopping by the flower shop" patterns
with the finite-CP case (non-modal presupposition) — a critical datum against
the Modalized Complement Analysis, which would predict a modal presupposition
for any non-finite complement. The gerund is non-finite but *not* modalized.
Test: continuation "...but he didn't stop by the flower shop" is judged
infelicitous, indicating the lower-event presupposition is present.
-/

def forget_gerund : ForgetJudgment where
  frame := .gerund
  sentence := "John forgot stopping by the flower shop"
  presupParaphrase := "John stopped by the flower shop"
  content := .nonModal
  implicativeNegative := false

/-! ## Psych-action reading — plain infinitive

Williams (2)/(5), §1: "John forgot to stop by the flower shop" does *not*
presuppose John stopped (and per the Karttunen tradition, entails he did
not). What it presupposes (Williams (5a)) is the modalized proposition
"John was supposed to stop by the flower shop". Williams' analysis (§4–§5):
the plain infinitive's forward-oriented temporal profile violates the
pre-existence presupposition, triggering covert Mod insertion that lets the
obligation/plan be the target of the memory.
-/

def forget_infinitival : ForgetJudgment where
  frame := .infinitival
  sentence := "John forgot to stop by the flower shop"
  presupParaphrase := "John was supposed to stop by the flower shop"
  content := .modal
  implicativeNegative := true

/-- The English data points covered in Williams §1 and §3.1. -/
def allForgetJudgments : List ForgetJudgment :=
  [forget_finiteCP, forget_gerund, forget_infinitival]

/-- Williams' modal-presupposition split tracks Karttunen's
    implicative-negative entailment: the plain-infinitive frame is the
    locus of both. This is the cross-paper coherence claim — the two
    asymmetries identified in Williams' (1)/(2) (presupposition flip and
    implicative entailment flip) co-vary in the English data, even
    though Williams' analysis only addresses the presupposition side. -/
theorem modal_iff_implicative :
    allForgetJudgments.all
      (fun j => (decide (j.content = .modal)) == j.implicativeNegative) = true := by
  decide

end Phenomena.Presupposition.Studies.Williams2026
