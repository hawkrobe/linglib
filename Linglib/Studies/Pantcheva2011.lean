import Linglib.Morphology.Paradigm.Contiguity
import Linglib.Syntax.Case.Order

/-!
# Pantcheva 2011: syncretism in directional expressions
[pantcheva-2011] [bobaljik-2012] [caha-2009]

The directional containment object Place ⊂ Goal ⊂ Source ⊂ Route lives in
`Syntax/Case/Order.lean` (`Case.PathDir`); this study tests its
**syncretism prediction**. Of the logically possible syncretism patterns
over the four path roles, only a few are attested, under two constraints
([pantcheva-2011] §9.2):

* **\*ABA** (contiguity): a syncretism targets only *adjacent* heads on
  the containment chain — the framework-neutral
  `Morphology.Containment` object, *the same* used for nominal case
  allomorphy ([caha-2009], [bobaljik-2012]).
* **\*A&¬A**: Goal and Source never share a marker. Source is the
  semantic *reversal* of Goal ([pantcheva-2011] §9.2.2), so a
  Goal=Source marker would be contradictory — a *pragmatic* constraint,
  not a structural one.

Together they cut the 15 set-partitions of {Place, Goal, Source, Route}
to **four** possible patterns (`possible_syncretisms`), Pantcheva's
Types 1–4. (Her Tables 9.2/9.3 enumerate 14, omitting one *ABA-excluded
pattern — Goal=Route skipping Source; the enumeration here is over all
15.) Attested instantiations (her Table 9.4): English *at*/*to*/*from*
(all distinct, Type 1); Estonian `-l`/`-l-le`/`-l-t` and Imbabura
Quechua `-pi`/`-man`/`-man-da`, where the Source marker morphologically
contains the Goal marker — the shell containment made visible; Georgian
Location=Goal (Type 3, her Table 9.1).

## Main declarations

* `Pantcheva2011.possible` — the two-constraint filter (*ABA via
  `Containment`, *A&¬A via `GoalSourceMerged`)
* `Pantcheva2011.possible_syncretisms` — exactly the four attested
  patterns; `four_possible`, `aba_excluded`, `ana_excluded`
* `Pantcheva2011.source_contains_goal` — the morphological-containment
  fact, read off the shared `PathDir` shell decomposition
-/

namespace Pantcheva2011

open Morphology (IsContiguous)

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

/-- Exactly four syncretism patterns are possible. -/
theorem four_possible : (allPatterns.filter (λ p => Possible p)).length = 4 := by
  decide

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
