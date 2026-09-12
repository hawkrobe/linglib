import Linglib.Data.Generalizations.HomogeneityProjection

/-!
# Križ and Chemla (2015): Two Methods to Find Truth-Value Gaps

This file formalizes the theoretical assessment in [kriz-chemla-2015], which introduces two
experimental methods for detecting truth-value gaps, separate completely-true and
completely-false tasks in Experiments A0 to A3 and one-shot ternary judgments in
Experiments B1 to B3 and C2 to C4, and applies them to the projection of plural-definite
homogeneity from the scope of sentential negation, *every* or *all*, *no*, and *exactly 2*.
The gap projects in every tested environment except the gap? configuration, where the
some- and all-substituted variants of the sentence are both false; under *no* it emerges
only in Experiment C2, small but robust.

The paper's guiding principle locates a gap wherever the variant of the sentence with an
existential in place of the definite is true while the variant with a universal is false.
`someReading` and `allReading` are those two variants over a `Display` of homogeneous or
`mixed` cells, and the three approaches assessed in §6 are combinations of them and of the
globally exhaustified meaning (30): `supervaluation` after [spector-2013], equivalently the
local-exhaustification construals, `globalConstrual`, the literal-versus-global
exhaustification construals after [magri-2009], and `universalPresupposition` after
[schwarzschild-1994], [lobner-2000] and [gajewski-2005]. Each is run over the Table 13
display recorded on each row of `Data/Examples/KrizChemla2015`, read into cells by
`displayOf`, against the pooled judgments of `Generalizations.HomogeneityProjection` and
`Generalizations.HomogeneityGap`. The supervaluation prediction reproduces every pooled
judgment (`supervaluation_matches_pool`); the global construals fail on exactly the C2 *no*
gap and the C4 gap?? gap (`globalConstrual_divergence`); universal projection fails on
exactly the bivalent conditions containing non-homogeneous cells, the argument from (42),
plus the gap? condition (`universalPresupposition_divergence`).

## Implementation notes

A display is a list of `Cell`s, one per array of nine objects, since only the full, mixed,
or empty classification of each array enters the readings; a row's Table 13 number string
is read cell by cell, `9` full, `0` empty, anything else mixed. The `notEvery` operator of
the pool postdates the paper ([augurzky-etal-2023]); `globalExh` gives it the general clause
of (30) and no theorem here exercises it. `bareLiteralNegative` and `wideScopeParse`
reconstruct the diagnosis in §6.1.3 of the downward-entailing problem for the implicature
approach: the bare existential literal meaning predicts no gap under negation, and parsing
the definite above negation restores the fit for plain negation but not for *no*, whose
definite contains a variable bound by the quantifier ([steedman-2012]).

## TODO

* The [george-2008]-style trivalent projection theory that §6.3 credits with matching the
  supervaluation predictions is not implemented, nor are the richer-candidate
  supervaluation variants of §6.2, which over-predict a gap in the gap? condition.

## References

* [kriz-chemla-2015]
* [spector-2013]
* [magri-2009]
* [magri-2014]
* [chierchia-fox-spector-2012]
* [schwarzschild-1994]
* [lobner-2000]
* [gajewski-2005]
* [george-2008]
* [steedman-2012]
* [augurzky-etal-2023]
-/

namespace KrizChemla2015

open Features (Polarity)
open Generalizations Generalizations.HomogeneityProjection Data.Examples

/-! ### Displays -/

/-- One array of a display — one boy's presents (C series) or one cell of
shapes (A/B series) — classified by how much of it is target-satisfying:
all of it, some but not all (`mixed`), or none. -/
inductive Cell where
  | full
  | mixed
  | empty
  deriving DecidableEq, Repr

/-- A display: one `Cell` per boy. -/
abbrev Display := List Cell

/-- A cell is homogeneous when the target property holds of all of it or none
of it — the presupposition [schwarzschild-1994]-style accounts attach to
plural predication. -/
def Cell.homogeneous (c : Cell) : Prop := c ≠ .mixed

instance : DecidablePred Cell.homogeneous :=
  λ c => inferInstanceAs (Decidable (c ≠ .mixed))

/-- Number of cells whose boy found at least some of his presents. -/
def occupied (d : Display) : ℕ := d.countP (· != Cell.empty)

/-- Number of cells whose boy found all of his presents. -/
def filled (d : Display) : ℕ := d.count .full

/-! ### The some- and all-substituted readings

§3's guiding principle: a sentence with a definite plural has a gap in a
situation where the variant with an existential in place of the definite is
true while the variant with a universal is false. -/

/-- The some-substituted reading: *some (of his) presents* in place of the
definite. This is the literal meaning on [magri-2014]'s analysis and the
existential resolution of the definite on [spector-2013]'s. -/
def someReading : EmbeddingOperator → Display → Prop
  | .every,      d => ∀ c ∈ d, c ≠ .empty
  | .no,         d => ∀ c ∈ d, c = .empty
  | .exactlyTwo, d => occupied d = 2
  | .notEvery,   d => ¬ ∀ c ∈ d, c ≠ .empty

/-- The all-substituted reading: *all of his presents* in place of the
definite. This is the locally exhaustified parse on [magri-2014]'s analysis
and the universal resolution on [spector-2013]'s. -/
def allReading : EmbeddingOperator → Display → Prop
  | .every,      d => ∀ c ∈ d, c = .full
  | .no,         d => ∀ c ∈ d, c ≠ .full
  | .exactlyTwo, d => filled d = 2
  | .notEvery,   d => ¬ ∀ c ∈ d, c = .full

instance (op : EmbeddingOperator) (d : Display) : Decidable (someReading op d) := by
  cases op <;> simp only [someReading] <;> infer_instance

instance (op : EmbeddingOperator) (d : Display) : Decidable (allReading op d) := by
  cases op <;> simp only [allReading] <;> infer_instance

/-- The globally double-exhaustified meaning, (30) in [kriz-chemla-2015]:
exhaustification is vacuous in the downward-entailing scope of `no` and
conjoins the some- and all-substituted readings elsewhere. (`notEvery`
postdates the paper's grid — [augurzky-etal-2023] — and takes the general
clause; no theorem below exercises it.) -/
def globalExh : EmbeddingOperator → Display → Prop
  | .no, d => someReading .no d
  | op,  d => someReading op d ∧ allReading op d

instance (op : EmbeddingOperator) (d : Display) : Decidable (globalExh op d) := by
  cases op <;> simp only [globalExh] <;> infer_instance

/-! ### The three approaches -/

/-- Trivalent verdict from two meaning components: clearly true when both
hold, clearly false when neither does, a truth-value gap when they conflict.
Each §6 construal instantiates this with a different pair of components. -/
def gapValue (p q : Prop) [Decidable p] [Decidable q] : Trivalent :=
  if p ∧ q then .true else if ¬p ∧ ¬q then .false else .indet

/-- Two-candidate supervaluation ([spector-2013]; §6.2): supervaluate over
the existential and universal resolutions of the definite. Extensionally this
is also the (si2)/(si4) implicature construal of §6.1.2 — gap iff the literal
and locally exhaustified meanings conflict — which is how §6.2 argues the two
approaches make the same projection predictions. -/
def supervaluation (op : EmbeddingOperator) (d : Display) : Trivalent :=
  gapValue (someReading op d) (allReading op d)

/-- Implicature construals (si1)/(si3) of §6.1.2 ([magri-2009]'s oddness
condition): gap iff the literal meaning and the globally exhaustified meaning
conflict. -/
def globalConstrual (op : EmbeddingOperator) (d : Display) : Trivalent :=
  gapValue (someReading op d) (globalExh op d)

/-- Homogeneity as a presupposition projecting universally from the
quantifier's scope ([schwarzschild-1994], [lobner-2000], [gajewski-2005], as
assessed in §6.3): presupposition failure unless every cell is homogeneous,
in which case the universal-force assertion decides the sentence. -/
def universalPresupposition (op : EmbeddingOperator) (d : Display) : Trivalent :=
  if (∀ c ∈ d, c.homogeneous) ∧ allReading op d then .true
  else if (∀ c ∈ d, c.homogeneous) then .false
  else .indet

/-! ### The tested grid -/

/-- A cell of a Table 13 number string: `9` of the nine objects is a full cell, `0` an empty
one, and anything else a mixed one. -/
def Cell.ofChar (c : Char) : Cell :=
  if c = '9' then .full else if c = '0' then .empty else .mixed

/-- The display recorded on a row, read cell by cell; e.g. the (*every*, gap) display 9929,
three boys who found all nine of their presents and one who found two, is
`[full, full, mixed, full]`. -/
def displayOf (e : LinguisticExample) : Option Display :=
  (e.feature? "display").map λ s => s.toList.map Cell.ofChar

/-! ### Predictions against the projection pool -/

/-- The supervaluation (equivalently, local-exhaustification) prediction reproduces every
pooled projection judgment, the bottom line of §6.4. The fit is bought either by allowing
local exhaustification in downward-entailing contexts, contra [chierchia-fox-spector-2012],
or by restricting the supervaluation candidates to the existential and universal
resolutions. -/
theorem supervaluation_matches_pool :
    ∀ e ∈ Examples.all, ∀ d ∈ fromExample e, ∀ disp ∈ displayOf e,
      supervaluation d.operator disp = d.observed := by
  decide

/-- Construals locating the gap in a literal-vs-global-exhaustification conflict fail on
exactly two cells: the small-but-robust *no* gap of Experiment C2, where no implicature
arises in a downward-entailing context (§6.1.3), and the gap?? gap of Experiment C4, where
the literal meaning and the implicature are false and true respectively, so their
conjunction is simply false. Both cells are predicted clearly false but observed gappy. -/
theorem globalConstrual_divergence :
    ∀ e ∈ Examples.all, ∀ d ∈ fromExample e, ∀ disp ∈ displayOf e,
      (globalConstrual d.operator disp ≠ d.observed ↔
        (d.operator, d.scenario) ∈
          [(EmbeddingOperator.no, GapScenario.gap), (.exactlyTwo, .gapQQ)]) := by
  decide

/-- Universal projection of the homogeneity presupposition fails on exactly the bivalently
judged conditions whose displays contain non-homogeneous cells, the false conditions of
Experiments C2 and C3, argument (42) of §6.3, plus the gap? condition, where a
presupposition failure is predicted but falsity observed. -/
theorem universalPresupposition_divergence :
    ∀ e ∈ Examples.all, ∀ d ∈ fromExample e, ∀ disp ∈ displayOf e,
      (universalPresupposition d.operator disp ≠ d.observed ↔
        (d.operator, d.scenario) ∈
          [(EmbeddingOperator.every, GapScenario.falseScenario),
           (.no, .falseScenario), (.exactlyTwo, .falseScenario),
           (.exactlyTwo, .gapQ)]) := by
  decide

/-! ### Structural observations (§6.1.3) -/

/-- In the scope of `every` the implicature construals all align: comparing
the literal meaning with global exhaustification and with local
exhaustification comes to the same thing, on any display. -/
theorem globalConstrual_every (d : Display) :
    globalConstrual .every d = supervaluation .every d := by
  have h : allReading .every d → someReading .every d :=
    λ ha c hc => by simp [ha c hc]
  by_cases hs : someReading .every d <;> by_cases ha : allReading .every d <;>
    simp_all [globalConstrual, supervaluation, globalExh, gapValue]

/-- Without local exhaustification, no gap can arise in the scope of `no`:
exhaustification is vacuous there, so the literal and globally exhaustified
meanings never conflict. The observed C2 gap therefore forces either local
exhaustification or the supervaluation/presupposition alternatives. -/
theorem globalConstrual_no_never_gap (d : Display) :
    globalConstrual .no d ≠ .indet := by
  by_cases h : someReading .no d <;>
    simp [globalConstrual, globalExh, gapValue, h]

/-! ### The unembedded grid

The polarity × scenario cells of Exps. A0/A1/B1 live in the
[[Generalizations.HomogeneityGap]] pool. An unembedded display is a single
cell: nine shapes, of which all, some, or none are target-colored. -/

/-- The display cell realizing each unembedded scenario. -/
def scenarioCell : HomogeneityGap.GapScenario → Cell
  | .all  => .full
  | .none => .empty
  | .gap  => .mixed

/-- Supervaluation over the unembedded grid: resolve the definite
existentially and universally, under negation for negative polarity. -/
def supervaluationGap (pol : Polarity) (sc : HomogeneityGap.GapScenario) : Trivalent :=
  match pol with
  | .positive => gapValue (scenarioCell sc ≠ .empty) (scenarioCell sc = .full)
  | .negative => gapValue (scenarioCell sc = .empty) (scenarioCell sc ≠ .full)

/-- The supervaluation account reproduces the paper's unembedded and negated
judgments: truth on uniform displays, the gap on mixed ones, projected
through negation (Exps. A1/B1). -/
theorem supervaluationGap_matches_pool :
    ∀ d ∈ HomogeneityGap.allData, d.source.bibkey = "kriz-chemla-2015" →
      supervaluationGap d.polarity d.scenario = d.observed := by
  decide

/-- The bare implicature construal assigns a negated sentence its existential
literal meaning outright — negation is downward-entailing, so no implicature
arises and no gap is predicted (§6.1.3). -/
def bareLiteralNegative (sc : HomogeneityGap.GapScenario) : Trivalent :=
  if scenarioCell sc = .empty then .true else .false

/-- The E-neg gap of Exps. A1/B1 refutes the bare implicature construal: the
negated mixed-display cell is observed gappy but predicted clearly false.
This is §6.1.3's downward-entailing problem, which for plain negation the
wide-scope parse solves (`wideScopeParse_matches_pool`) but for `no` — whose
definite contains a variable bound by the quantifier ([steedman-2012]) —
nothing does. -/
theorem bareLiteral_misses_negation_gap :
    ∃ d ∈ HomogeneityGap.allData, d.source.bibkey = "kriz-chemla-2015" ∧
      d.polarity = .negative ∧ d.scenario = .gap ∧
      bareLiteralNegative d.scenario ≠ d.observed := by
  decide

/-- The negated sentence with the definite parsed above negation (§6.1.3):
the existential and universal resolutions now scope over the negated
predicate. -/
def wideScopeParse (sc : HomogeneityGap.GapScenario) : Trivalent :=
  gapValue (scenarioCell sc ≠ .full) (scenarioCell sc = .empty)

/-- With the wide-scope parse, the implicature construal again reproduces the
negated judgments — the paper's rescue for plain negation. -/
theorem wideScopeParse_matches_pool :
    ∀ d ∈ HomogeneityGap.allData, d.source.bibkey = "kriz-chemla-2015" →
      d.polarity = .negative → wideScopeParse d.scenario = d.observed := by
  decide

end KrizChemla2015
