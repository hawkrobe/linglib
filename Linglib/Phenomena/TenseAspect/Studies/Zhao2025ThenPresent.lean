import Linglib.Core.Temporal.Reichenbach
import Linglib.Theories.Semantics.Tense.Perspective
import Linglib.Fragments.English.TemporalDeictic
import Linglib.Fragments.German.TemporalDeictic
import Linglib.Fragments.Mandarin.TemporalDeictic
import Linglib.Fragments.Japanese.TemporalDeictic
import Linglib.Fragments.Greek.TemporalDeictic
import Linglib.Fragments.Russian.TemporalDeictic
import Linglib.Fragments.Hebrew.TemporalDeictic
import Linglib.Fragments.Hungarian.TemporalDeictic

/-!
# Then-Present Puzzle (@cite{zhao-2025})
@cite{zhao-2025} @cite{kiparsky-2002}

Temporal ⌈then⌉ is cross-linguistically incompatible with present tense.

## The puzzle

⌈then⌉ presupposes ¬(g(n) ○ π): its reference is disjoint from the
temporal perspective. PRES presupposes g(n) ○ π: overlap with the
perspective. When composition forces the PRES reference inside the then
reference ("during then"), the presuppositions clash.

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
| Hungarian| akkor             | yes                 |

-/

namespace Zhao2025ThenPresent

open Core.Reichenbach
open Semantics.Tense
open Semantics.Tense.Perspective


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
  , Fragments.Hebrew.TemporalDeictic.az
  , Fragments.Hungarian.TemporalDeictic.akkor ]

/-- Every "then" adverb in our inventory shifts perspective. -/
theorem all_then_shift_perspective :
    ∀ a ∈ thenAdverbs, a.shiftsPerspective = true := by
  intro a ha
  simp only [thenAdverbs, List.mem_cons, List.mem_nil_iff, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl


-- ════════════════════════════════════════════════════
-- § 2. The Then-Present Incompatibility (Root Clause)
-- ════════════════════════════════════════════════════

/-- Root clause: PRES (R = P) + isSimpleCase (P = S) means R = S.
    ⌈then⌉ requires its reference ≠ π = S. Since composition puts
    the PRES reference inside the then reference, both equal S in the
    point model, contradicting then's presupposition. -/
theorem then_present_incompatible {Time : Type*} [LinearOrder Time]
    (f : ReichenbachFrame Time)
    (_hPresent : f.isPresent)    -- R = P (present tense)
    (hSimple : f.isSimpleCase)   -- P = S (root clause)
    (hShift : f.perspectiveTime ≠ f.speechTime)  -- "then": P ≠ S
    : False :=
  hShift hSimple


-- ════════════════════════════════════════════════════
-- § 3. Presuppositional Bridge Theorems
-- ════════════════════════════════════════════════════

/-- The root-clause incompatibility is a corollary of the general
    perspective clash: in root clauses, π = S (no OP_π), so
    localEval = S and `then_perspective_clash` applies. -/
theorem root_clause_is_presuppositional_corollary {Time : Type*}
    (f : ReichenbachFrame Time)
    (hSimple : f.isSimpleCase)
    (hThen : f.perspectiveTime ≠ f.speechTime) :
    False :=
  then_perspective_clash f f.speechTime hSimple hThen

/-- ⌈then⌉ + deleted tense is compatible: when SOT deletes the embedded
    tense, no presupposition anchors it to π, so ⌈then⌉ can freely
    pick a reference disjoint from π. -/
theorem then_compatible_with_deleted_tense {Time : Type*}
    (thenRef perspective : Time)
    (hDisjoint : thenRef ≠ perspective) :
    thenPresup thenRef perspective :=
  then_deleted_tense_compatible thenRef perspective hDisjoint


end Zhao2025ThenPresent
