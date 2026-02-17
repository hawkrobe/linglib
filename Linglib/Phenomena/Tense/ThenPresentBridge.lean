import Linglib.Core.Reichenbach
import Linglib.Theories.Semantics.Tense.TsiliaEtAl2026
import Linglib.Fragments.English.TemporalDeictic
import Linglib.Fragments.German.TemporalDeictic
import Linglib.Fragments.Mandarin.TemporalDeictic
import Linglib.Fragments.Japanese.TemporalDeictic
import Linglib.Fragments.Greek.TemporalDeictic
import Linglib.Fragments.Russian.TemporalDeictic
import Linglib.Fragments.Hebrew.TemporalDeictic

/-!
# Then-Present Puzzle (Zhao 2026, Tsilia, Zhao & Sharvit 2026)
@cite{zhao-2026} @cite{tsilia-zhao-sharvit-2026}

Temporal "then" is cross-linguistically incompatible with present tense.
Zhao (2026) explains this via a perspective parameter π (= Kiparsky's P):
present tense requires P = R, but "then" shifts P away from S, making
P ≠ S. In root clauses, isSimpleCase requires P = S, so present + then
forces R = P ≠ S — but present tense in root clauses needs R = S,
creating a contradiction.

Tsilia, Zhao & Sharvit (2026) provide the presuppositional analysis: tenses
are presupposition triggers anchored to π, and the incompatibility is a
presupposition clash between ⌈then⌉ (P ≠ local eval) and OP_π (P = local
eval).

## Cross-linguistic data

| Language | "then" form      | Shifts perspective? |
|----------|------------------|---------------------|
| English  | then             | yes                 |
| German   | damals/dann      | yes                 |
| Mandarin | 那时 nà-shí       | yes                 |
| Japanese | その時 sono-toki   | yes                 |
| Greek    | τότε tóte         | yes                 |
| Russian  | тогда togda       | yes                 |
| Hebrew   | אז az             | yes                 |

## Key theorem

`then_present_incompatible`: In a simple root clause (P = S) with present
tense (R = P), "then" (P ≠ S) leads to contradiction.

The presuppositional generalization (`then_perspective_clash` in
`TsiliaEtAl2026.lean`) subsumes this: OP_π forces P = localEval while
⌈then⌉ requires P ≠ localEval.

## References

- Zhao, Z. (2026). Cross-Linguistic and Cross-Domain Parallels in the
  Semantics of Degree and Time. MIT dissertation, Part I.
- Tsilia, D., Zhao, Z. & Sharvit, Y. (2026). Tense and perspective.
- Kiparsky, P. (2002). Event structure and the perfect.
-/

namespace Phenomena.Tense.ThenPresentBridge

open Core.Reichenbach
open Semantics.Tense
open Semantics.Tense.TsiliaEtAl2026

-- ════════════════════════════════════════════════════
-- § 1. Cross-Linguistic "Then" Inventory
-- ════════════════════════════════════════════════════

/-- All "then" adverbs from Fragment entries. -/
def thenAdverbs : List ThenAdverb :=
  [ Fragments.English.TemporalDeictic.then_
  , Fragments.German.TemporalDeictic.damals
  , Fragments.Mandarin.TemporalDeictic.nashi
  , Fragments.Japanese.TemporalDeictic.sonotoki
  , Fragments.Greek.TemporalDeictic.tote
  , Fragments.Russian.TemporalDeictic.togda
  , Fragments.Hebrew.TemporalDeictic.az ]

-- ════════════════════════════════════════════════════
-- § 2. Per-Datum Verification
-- ════════════════════════════════════════════════════

/-- Every "then" adverb in our inventory shifts perspective. -/
theorem all_then_shift_perspective :
    ∀ a ∈ thenAdverbs, a.shiftsPerspective = true := by
  intro a ha
  simp only [thenAdverbs, List.mem_cons, List.mem_nil_iff, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

-- ════════════════════════════════════════════════════
-- § 3. The Then-Present Incompatibility
-- ════════════════════════════════════════════════════

/-- The then-present incompatibility (Zhao 2026, Part I):
    In a simple root clause (P = S) with present tense (R = P),
    "then" requires P ≠ S — contradiction.

    This is the formal core of why *"Then John is sick" (with temporal
    "then" = at that time) is infelicitous. -/
theorem then_present_incompatible {Time : Type*} [LinearOrder Time]
    (f : ReichenbachFrame Time)
    (_hPresent : f.isPresent)    -- R = P (present tense)
    (hSimple : f.isSimpleCase)   -- P = S (root clause)
    (hShift : f.perspectiveTime ≠ f.speechTime)  -- "then": P ≠ S
    : False :=
  hShift hSimple

-- ════════════════════════════════════════════════════
-- § 4. Presuppositional Bridge Theorems
-- ════════════════════════════════════════════════════

/-- The root-clause incompatibility is a corollary of the presuppositional
    theorem: in root clauses, P = S is the default (no OP_π applied),
    so localEval = S and `then_perspective_clash` applies. -/
theorem root_clause_is_presuppositional_corollary {Time : Type*}
    (f : ReichenbachFrame Time)
    (hSimple : f.isSimpleCase)
    (hThen : f.perspectiveTime ≠ f.speechTime) :
    False :=
  then_perspective_clash f f.speechTime hSimple hThen

/-- ⌈then⌉ + deleted tense is compatible: when SOT deletes the embedded
    tense, no presupposition anchors π, so ⌈then⌉ can freely shift P. -/
theorem then_compatible_with_deleted_tense {Time : Type*}
    (f : ReichenbachFrame Time)
    (hShifted : f.perspectiveTime ≠ f.speechTime)
    (hOverlap : f.referenceTime = f.perspectiveTime) :
    thenPresup f :=
  then_deleted_tense_compatible f hShifted hOverlap

end Phenomena.Tense.ThenPresentBridge
