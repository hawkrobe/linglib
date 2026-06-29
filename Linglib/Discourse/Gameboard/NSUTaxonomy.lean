/-!
# KOS: NSU Classification (Table 7.3 + Table 7.4)
[ginzburg-2012] Ch. 7 §7.2 (pp. 219–222)
[fernandez-2006]

The empirical taxonomy of non-sentential utterances from
[ginzburg-2012] Tables 7.3 and 7.4, derived from the BNC subcorpus
study by [fernandez-2006] (200 speaker-turns from 54 BNC files;
14,315 sentences; 1,299 NSUs found, of which 1,283 = 98.9% classified).

## Class enumeration (Table 7.3, p. 221)

Sixteen classes — the original Table 7.3 lists 15 because Sluice (24)
is undivided there, but Table 7.4 (p. 222) splits Sluice into
*Reprise Sluice* (13, a metacommunicative query) and *Direct Sluice*
(11, an extension move). To match Table 7.4 functional grouping
arithmetic, we adopt the split here.

## Functional grouping (Table 7.4, p. 222)

Four functional categories with cell-summed totals:

| Group                  | Cell sum | Members                                                                           |
|------------------------|----------|-----------------------------------------------------------------------------------|
| Positive Feedback      | 685      | plainAck (599), repeatedAck (86)                                                  |
| Answers                | 403      | shortAnswer (188), affirmAnswer (105), rejection (49), repeatedAffirm (26),       |
|                        |          | helpfulRejection (24), propositionalModifier (11)                                 |
| Metacommunicative Q's  | 132      | clarificationEllipsis (79), repriseSluice (13), checkQuestion (22), filler (18)   |
| Extension Moves        | 63       | factiveModifier (27), bareModifier (15), conjFrag (10), directSluice (11)         |

Cell-sum total: 685 + 403 + 132 + 63 = 1283 ✓ (matches Table 7.3 total).

(Ginzburg's Table 7.4 *header* totals show 685/413/132/63 = 1293, off by
10 from the cell sums — the 10-utterance discrepancy is internal to
the book.)

## Anti-pattern avoided: aggregate count theorems

Earlier formaliser versions had `theorem nsu_total_1283 : ... = 1283` and
`theorem functional_groups_sum_to_total : pf + ans + mcq + ext = 1283`.
Per MEMORY.md `feedback_no_aggregate_count_theorems`, these go stale on
any data revision and prove nothing about Ginzburg's framework — only
that the formaliser's transcription is internally consistent.

The pattern this file uses instead: a single `freqTable` source of truth
with a structural coherence theorem (`frequency_coherent`) that enforces
both `NSUClass.frequency` and `NSUClass.toFunction` to agree with the
table per class. If any cell changes, the coherence theorem fails until
both functions are updated — automatic drift detection without numeric
assertions.

-/

namespace Discourse.Gameboard

-- ════════════════════════════════════════════════════
-- § 1. NSU Classes (Table 7.3 with Table 7.4 sluice split)
-- ════════════════════════════════════════════════════

/-- The 16 NSU classes from [ginzburg-2012] Table 7.3 + Table 7.4.

Sluice is split into Reprise Sluice (metacommunicative) and Direct Sluice
(extension move) per Table 7.4 — the original Table 7.3 had a single
Sluice (24) entry but Table 7.4 partitions it 13 + 11. -/
inductive NSUClass where
  /-- "mmh", "uh-huh" — acknowledges preceding utterance (599). -/
  | plainAcknowledgement
  /-- "Bo" — fills argument slot in MaxQUD (188). -/
  | shortAnswer
  /-- "Yes" — positive answer to polar query (105). -/
  | affirmativeAnswer
  /-- "Bo, hmm" — acknowledgement with repetition (86). -/
  | repeatedAcknowledgement
  /-- "Bo?" — clarification ellipsis (79). -/
  | clarificationEllipsis
  /-- "No" — negative answer to polar query / assertion (49). -/
  | rejection
  /-- "Great!" — factive modifier (27). -/
  | factiveModifier
  /-- "Bo, yes" — affirmative with repetition (26). -/
  | repeatedAffirmativeAnswer
  /-- "No, Max" — rejection with helpful alternative (24). -/
  | helpfulRejection
  /-- "Who?" — bare wh-phrase reprising the antecedent (13). -/
  | repriseSluice
  /-- "Who?" — bare wh-phrase requesting new information (11). -/
  | directSluice
  /-- "Okay?" — rising-intonation check (22). -/
  | checkQuestion
  /-- "uh", "well" — hesitation / floor-holding (18). -/
  | filler
  /-- "Yesterday" — bare modifier phrase (15). -/
  | bareModifierPhrase
  /-- "Maybe" — propositional modifier (11). -/
  | propositionalModifier
  /-- "And Max" — conjunction + fragment (10). -/
  | conjunctionFragment
  deriving Repr, DecidableEq

-- ════════════════════════════════════════════════════
-- § 2. Functional Groups (Table 7.4)
-- ════════════════════════════════════════════════════

/-- Functional grouping from [ginzburg-2012] Table 7.4 (p. 222). -/
inductive NSUFunction where
  /-- Positive feedback (685): plain + repeated acknowledgement. -/
  | positiveFeedback
  /-- Answers (403): short, affirmative, rejection, repeated affirmative,
      helpful rejection, propositional modifier. -/
  | answer
  /-- Metacommunicative queries (132): CE + reprise sluice + check + filler. -/
  | metacommunicativeQuery
  /-- Extension moves (63): factive modifier + bare modifier + conj+frag
      + direct sluice. -/
  | extensionMove
  deriving Repr, DecidableEq

-- ════════════════════════════════════════════════════
-- § 3. The freqTable Source of Truth
-- ════════════════════════════════════════════════════

/-- Single source of truth for Tables 7.3 + 7.4: each row pairs an
NSU class with its functional group and BNC frequency. Every entry below
is verifiable against the published tables.

Updating Table 7.3 or Table 7.4 means editing exactly one row here; the
coherence theorem `frequency_coherent` ensures `NSUClass.frequency` and
`NSUClass.toFunction` stay in sync. -/
def freqTable : List (NSUClass × NSUFunction × Nat) := [
  (.plainAcknowledgement,     .positiveFeedback,        599),
  (.shortAnswer,               .answer,                  188),
  (.affirmativeAnswer,         .answer,                  105),
  (.repeatedAcknowledgement,   .positiveFeedback,         86),
  (.clarificationEllipsis,     .metacommunicativeQuery,   79),
  (.rejection,                 .answer,                   49),
  (.factiveModifier,           .extensionMove,            27),
  (.repeatedAffirmativeAnswer, .answer,                   26),
  (.helpfulRejection,          .answer,                   24),
  (.repriseSluice,             .metacommunicativeQuery,   13),
  (.directSluice,              .extensionMove,            11),
  (.checkQuestion,             .metacommunicativeQuery,   22),
  (.filler,                    .metacommunicativeQuery,   18),
  (.bareModifierPhrase,        .extensionMove,            15),
  (.propositionalModifier,     .answer,                   11),
  (.conjunctionFragment,       .extensionMove,            10)
]

/-- All 16 NSU classes, ordered to match `freqTable`. -/
def allNSUClasses : List NSUClass :=
  freqTable.map (·.1)

-- ════════════════════════════════════════════════════
-- § 4. Per-class Projections
-- ════════════════════════════════════════════════════

/-- BNC frequency for each NSU class (Table 7.3 cell + Table 7.4 sluice split). -/
def NSUClass.frequency : NSUClass → Nat
  | .plainAcknowledgement     => 599
  | .shortAnswer               => 188
  | .affirmativeAnswer         => 105
  | .repeatedAcknowledgement   => 86
  | .clarificationEllipsis     => 79
  | .rejection                 => 49
  | .factiveModifier           => 27
  | .repeatedAffirmativeAnswer => 26
  | .helpfulRejection          => 24
  | .repriseSluice             => 13
  | .directSluice              => 11
  | .checkQuestion             => 22
  | .filler                    => 18
  | .bareModifierPhrase        => 15
  | .propositionalModifier     => 11
  | .conjunctionFragment       => 10

/-- Functional group for each NSU class (Table 7.4 partitioning). -/
def NSUClass.toFunction : NSUClass → NSUFunction
  | .plainAcknowledgement     => .positiveFeedback
  | .repeatedAcknowledgement  => .positiveFeedback
  | .shortAnswer              => .answer
  | .affirmativeAnswer        => .answer
  | .rejection                => .answer
  | .repeatedAffirmativeAnswer => .answer
  | .helpfulRejection         => .answer
  | .propositionalModifier    => .answer
  | .clarificationEllipsis    => .metacommunicativeQuery
  | .repriseSluice            => .metacommunicativeQuery
  | .checkQuestion            => .metacommunicativeQuery
  | .filler                   => .metacommunicativeQuery
  | .factiveModifier          => .extensionMove
  | .bareModifierPhrase       => .extensionMove
  | .conjunctionFragment      => .extensionMove
  | .directSluice             => .extensionMove

-- ════════════════════════════════════════════════════
-- § 5. Coherence (BruRow-style drift sentry)
-- ════════════════════════════════════════════════════

/-- Coherence: every class has a row in `freqTable` whose function-tag
and frequency match the per-class projections. Updating the table without
updating the projections (or vice versa) breaks this theorem.

This is the structural drift sentry that replaces the previous aggregate
`nsu_total_1283` and `functional_groups_sum_to_total` count theorems. -/
theorem frequency_coherent :
    allNSUClasses.all (fun c =>
      (c, c.toFunction, c.frequency) ∈ freqTable) = true := by decide

/-- All 16 classes are present in the freqTable (in order). -/
theorem allNSUClasses_complete : allNSUClasses.length = 16 := by decide

end Discourse.Gameboard
