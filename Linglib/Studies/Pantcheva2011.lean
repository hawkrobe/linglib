import Linglib.Morphology.Paradigm.Contiguity
import Linglib.Syntax.Case.Order

/-!
# Pantcheva (2011): Decomposing Path

This file formalizes the syncretism typology of the ninth chapter of [pantcheva-2011]. The
directional heads Place, Goal, Source, and Route form the containment sequence of
`Case.PathDir`, and a syncretism pattern over the four is a paradigm over that sequence
(`Pattern`). Two constraints cut the fifteen set-partitions of the four roles to the four
attested patterns, Types 1 to 4 (`Possible`, `possible_syncretisms`): the *ABA generalization
of Bobaljik ([bobaljik-2012], then circulating in manuscript), on which a syncretism targets
only adjacent heads of the sequence, the same contiguity that governs nominal case in
[caha-2009] (`Morphology.IsContiguous`); and *A&¬A, on which Goal and Source never share a
marker, because the Source head is the locus of a reversal of the Goal path (§5.4), so one
marker for both would be contradictory (`GoalSourceMerged`, `goalSource_distinct_denotation`).
Seven of the eleven excluded patterns fall to *ABA and the other four to *A&¬A, the
chapter's Table 9.3 (`aba_excluded`, `ana_excluded`). The containment itself is visible where
the Source marker contains the Goal marker, as in Imbabura Quechua *-man* against *-man-da*
(Table 4.2, `source_contains_goal`), and Georgian instantiates Type 3, with Location and Goal
syncretic (Table 9.1, `georgian_loc_goal_possible`).

## Implementation notes

The patterns are restricted-growth strings over the four positions, one representative per
set-partition; the attested lexicalization patterns of §9.3.1 are described in prose.

## References

* [pantcheva-2011]
* [bobaljik-2012]
* [caha-2009]
-/

namespace Pantcheva2011

open Morphology

/-- A syncretism pattern over the four path roles, in containment order
    [Place, Goal, Source, Route], as form-class indices: the n = 4
    instance of `Morphology.Paradigm`. -/
abbrev Pattern := Morphology.Paradigm 4 ℕ

/-- The 15 canonical syncretism patterns — restricted-growth strings over
    four positions, i.e. the set-partitions of {Place, Goal, Source,
    Route} up to relabeling. -/
def allPatterns : List Pattern :=
  [![0, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 1, 0], ![0, 0, 1, 1], ![0, 0, 1, 2],
   ![0, 1, 0, 0], ![0, 1, 0, 1], ![0, 1, 0, 2], ![0, 1, 1, 0], ![0, 1, 1, 1],
   ![0, 1, 1, 2], ![0, 1, 2, 0], ![0, 1, 2, 1], ![0, 1, 2, 2], ![0, 1, 2, 3]]

/-- **\*A&¬A**: Goal (position 1) and Source (position 2) share a form
    class. Forbidden — Source is the reversal of Goal, so a Goal=Source
    marker is contradictory ([pantcheva-2011] §9.2.2). -/
def GoalSourceMerged (p : Pattern) : Prop := p 1 = p 2

instance (p : Pattern) : Decidable (GoalSourceMerged p) :=
  inferInstanceAs (Decidable (_ = _))

/-- A syncretism pattern is **possible** iff it is contiguous (\*ABA, via
    the shared `Morphology.Containment` object) and keeps Goal distinct
    from Source (\*A&¬A). -/
def Possible (p : Pattern) : Prop :=
  IsContiguous p ∧ ¬ GoalSourceMerged p

instance (p : Pattern) : Decidable (Possible p) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- **The syncretism typology** ([pantcheva-2011] Tables 9.2/9.3): of the
    15 logically possible patterns, exactly four are attested — the
    contiguous ones keeping Goal and Source distinct. These are her
    Types 1–4: all-distinct (Type 1, English), Place=Goal (Type 3,
    Georgian), Source=Route (Type 2), and Place=Goal with Source=Route
    (Type 4). -/
theorem possible_syncretisms :
    allPatterns.filter (λ p => Possible p) =
      [![0, 0, 1, 1], ![0, 0, 1, 2], ![0, 1, 2, 2], ![0, 1, 2, 3]] := by decide

/-- Seven of the eleven excluded patterns violate \*ABA (non-contiguous —
    a syncretism spanning non-adjacent path roles). -/
theorem aba_excluded :
    (allPatterns.filter (λ p => ¬ IsContiguous p)).length = 7 := by decide

/-- The remaining four excluded patterns are contiguous but merge Goal
    with Source — the \*A&¬A constraint, unique to the directional domain
    (the nominal Caha containment has no analogue). -/
theorem ana_excluded :
    (allPatterns.filter
      (λ p => IsContiguous p ∧ GoalSourceMerged p)).length = 4 := by
  decide

/-! ### Morphological containment (Table 4.2)

The Source structure contains the Goal structure, visible where the
Source marker contains the Goal marker (Quechua `-man` ⊂ `-man-da`).
This is the shell containment of the shared `PathDir` object — not a
fact re-stipulated here, but read off `Case.PathDir.shells`. -/

/-- Source contains Goal contains Place, as shell-stack inclusion — the
    morphological-containment fact, from the substrate decomposition. -/
theorem source_contains_goal :
    Case.PathDir.place.shells ⊂ Case.PathDir.goal.shells ∧
    Case.PathDir.goal.shells ⊂ Case.PathDir.source.shells ∧
    Case.PathDir.source.shells ⊂ Case.PathDir.route.shells := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- Georgian's Location=Goal syncretism ([pantcheva-2011] Table 9.1) is
    one of the four possible patterns (Type 3). -/
theorem georgian_loc_goal_possible : Possible ![0, 0, 1, 2] := by decide

/-! ### The *A&¬A constraint, grounded in the denotation (Ch. 5)

The Goal=Source exclusion (`GoalSourceMerged`) is not a stipulation: it
follows from the directional *interpretation*. Source denotes the
**reversal** of Goal (`PathDir.source_denote_eq_goal_reverse`, §5.4), so
Goal and Source have distinct, in fact opposite, denotations — a single
marker for both would be semantically contradictory. -/

/-- Goal and Source have distinct denotations (Source reverses Goal), so a
    Goal=Source marker would be contradictory — the semantic ground of the
    *A&¬A constraint that excludes `GoalSourceMerged` patterns. -/
theorem goalSource_distinct_denotation :
    Case.PathDir.goal.denote ≠ Case.PathDir.source.denote := by decide

end Pantcheva2011
