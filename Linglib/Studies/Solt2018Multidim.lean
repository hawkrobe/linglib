/-!
# [solt-2018-multidim]: Multidimensionality, Subjectivity and Scales

Stephanie Solt (2018). Multidimensionality, Subjectivity and Scales:
Experimental Evidence. In *The Semantics of Gradability, Vagueness, and
Scale Structure*, pp. 59–91. Springer.

## Status

This file formalizes ONLY the experimental five-class typology from
Solt's Figure 1 (pp. 5–6). The full theory (Section 5: dimensional
measure functions for subjective vs objective comparatives, the
qualitative-vs-quantitative distinction, the Hare-style criteria-vs-
meaning split) is unformalized. The reason for the partial formalization
is to provide the typology *enum as a substrate-adjacent primitive*
that other gradability study files can reference by name —
specifically:

- `Studies/Tham2025.lean` (already in codebase;
  *cracked* belongs to AbsPart, the closest sibling class to
  *clean*/*dirty*/*salty* per Solt's classification)
- A future `Lasersohn2005`/`Stephenson2007`/`Kennedy2013` study file
  on faultless disagreement would consume this as the typological
  partition that ordering-subjectivity respects

When a second consumer beyond Tham2025 lands, the full Section 5
theory becomes the natural extension to formalize.

## The five classes (Solt's Figure 1, ordered by % "fact" judgments)

The experiment used a forced-choice subjectivity test on the
comparative form of 35 adjectives. The five classes that emerged:

| Class    | % fact | Examples                                              |
|----------|--------|-------------------------------------------------------|
| RelNum   |   98%  | tall, expensive, old, new                             |
| AbsTot   |   94%  | full, empty                                           |
| AbsPart  |   67%  | wet, dry, straight, curved, rough, smooth, clean,    |
|          |        | dirty, salty                                          |
| RelNo    |   55%  | sharp, dull, dark, light, hard, soft                  |
| Eval     |    4%  | good, bad, beautiful, pretty, ugly, easy, interesting,|
|          |        | boring, tasty, fun, intelligent, happy, sad           |

The empirical finding: ordering subjectivity correlates with
measurability (RelNum has measurement units; AbsTot has endpoints;
Eval has neither), NOT with the standard objective/subjective binary.
The middle class (AbsPart) is analytically interesting — these
adjectives describe physical properties yet allow faultless
disagreement about orderings. Tham 2025's *cracked* belongs here.
-/

namespace Solt2018Multidim

/-- Solt 2018 (Springer multidim chapter, Fig. 1) five-class typology
    of gradable adjectives, ordered by ordering-subjectivity:

    `relNum` (most objective, 98% fact judgments) →
    `absTot` (94%) → `absPart` (67%) → `relNo` (55%) →
    `eval` (most subjective, 4% fact judgments).

    The ordering is empirical (Solt's experimental result), not
    stipulative. -/
inductive SubjectivityClass where
  /-- Relative gradable, numerical measure (e.g. *tall*, *expensive*). -/
  | relNum
  /-- Absolute gradable, totally-closed scale (e.g. *full*, *empty*). -/
  | absTot
  /-- Absolute gradable, partially-closed scale (e.g. *wet*, *dry*,
      *clean*, *dirty*, *salty* — and Tham 2025's *cracked*). -/
  | absPart
  /-- Relative gradable, no numerical measure (e.g. *sharp*, *dull*). -/
  | relNo
  /-- Evaluative (e.g. *good*, *bad*, *beautiful*, *tasty*). -/
  | eval
  deriving Repr, BEq, DecidableEq

/-- Ordering-subjectivity rank (1 = most objective, 5 = most
    subjective). Reflects Solt's experimental ranking, not the % fact
    judgments themselves. -/
def SubjectivityClass.subjectivityRank : SubjectivityClass → Nat
  | .relNum  => 1
  | .absTot  => 2
  | .absPart => 3
  | .relNo   => 4
  | .eval    => 5

/-- The empirical ordering-subjectivity ranking from Solt's experiment:
    relNum < absTot < absPart < relNo < eval. -/
theorem subjectivityRank_strictly_ordered :
    SubjectivityClass.relNum.subjectivityRank <
      SubjectivityClass.absTot.subjectivityRank ∧
    SubjectivityClass.absTot.subjectivityRank <
      SubjectivityClass.absPart.subjectivityRank ∧
    SubjectivityClass.absPart.subjectivityRank <
      SubjectivityClass.relNo.subjectivityRank ∧
    SubjectivityClass.relNo.subjectivityRank <
      SubjectivityClass.eval.subjectivityRank := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- A concrete adjective in Solt's 35-item sample, classified by the
    experiment. Solt's full Table is partially encoded here (the
    high-information cases — RelNum and Eval anchor points + the
    AbsPart middle class that Tham 2025 builds on). The complete
    35-adjective table is unformalized; per-adjective classifications
    can be derived from the table on Fig. 1, p. 6. -/
structure ClassifiedAdj where
  form : String
  cls  : SubjectivityClass
  deriving Repr, BEq

/-- A representative slice of Solt's 35-adjective sample, including
    the AbsPart middle class that Tham 2025's *cracked* extends. -/
def representativeSample : List ClassifiedAdj :=
  -- RelNum (98%): numerical measures, almost universal "fact" judgment
  [⟨"tall", .relNum⟩, ⟨"expensive", .relNum⟩, ⟨"old", .relNum⟩, ⟨"new", .relNum⟩,
   -- AbsTot (94%): totally-closed scales
   ⟨"full", .absTot⟩, ⟨"empty", .absTot⟩,
   -- AbsPart (67%): partially-closed scales (Tham's *cracked* sibling class)
   ⟨"wet", .absPart⟩, ⟨"dry", .absPart⟩, ⟨"clean", .absPart⟩, ⟨"dirty", .absPart⟩,
   ⟨"salty", .absPart⟩, ⟨"smooth", .absPart⟩, ⟨"rough", .absPart⟩,
   -- RelNo (55%): relative without numerical measures
   ⟨"sharp", .relNo⟩, ⟨"dull", .relNo⟩, ⟨"dark", .relNo⟩, ⟨"light", .relNo⟩,
   -- Eval (4%): evaluative, almost universal "opinion" judgment
   ⟨"good", .eval⟩, ⟨"beautiful", .eval⟩, ⟨"tasty", .eval⟩, ⟨"intelligent", .eval⟩]

/-- Tham 2025's *cracked* belongs to the AbsPart class — the same
    class as *clean*, *dirty*, *wet*, *dry*. This is the cross-paper
    pointer that lets Tham 2025's substantive analysis be located in
    Solt's typology without requiring the full multidim chapter
    formalization. -/
def crackedClass : SubjectivityClass := .absPart

theorem cracked_is_AbsPart : crackedClass = .absPart := rfl

/-- *cracked* shares Solt's experimental class with *dirty* — both are
    AbsPart predicates per Fig. 1. The look-up is via `Option.bind` to
    avoid `.get!` (no `Inhabited` instance needed). -/
theorem cracked_shares_class_with_dirty :
    (representativeSample.find? (fun a => a.form == "dirty")).map
      ClassifiedAdj.cls = some crackedClass := rfl

end Solt2018Multidim
