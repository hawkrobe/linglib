import Linglib.Data.Generalizations.HomogeneityProjection

/-!
# [kriz-chemla-2015]: Two methods to find truth-value gaps

[kriz-chemla-2015] introduce two experimental methods for detecting truth-value
gaps — separate completely-true and completely-false tasks (Exps. A0-A3) and
one-shot ternary judgments (Exps. B1-B3, C2-C4) — and apply them to the
projection of plural-definite homogeneity from the scope of sentential negation,
`every`/`all`, `no`, and `exactly 2`. The gap projects in every tested
environment except the gap? configuration (where the some- and all-substituted
variants of the sentence are both false); under `no` it emerges only with the
grammatical restimulation of Exp. C2, small but robust (fn. 14).

The stimulus rows live in the generated `Data.Examples.KrizChemla2015` module
and are pooled by [[Generalizations.HomogeneityProjection]] (embedded cells) and
[[Generalizations.HomogeneityGap]] (unembedded and negated cells). This file
implements §6's assessment of the three theoretical approaches to homogeneity
against those pools.

## Main declarations

* `Cell`, `Display` — the experimental displays: arrays of nine objects, each
  array classified by whether it is fully, partially, or not at all
  target-satisfying.
* `someReading`, `allReading` — the paper's guiding principle (§3): the
  sentence variants with the definite plural replaced by an existential or a
  universal quantifier.
* `supervaluation` — two-candidate supervaluation ([spector-2013]): true iff
  true on both resolutions of the definite, false iff false on both. As §6.2
  notes, this coincides with the local-exhaustification implicature construals
  (si2)/(si4) of §6.1.2 on the projection data.
* `globalConstrual` — implicature construals (si1)/(si3) ([magri-2009],
  [magri-2014]): gap iff the literal and globally exhaustified meanings
  conflict.
* `universalPresupposition` — homogeneity as a presupposition projecting
  universally from the quantifier's scope ([schwarzschild-1994],
  [lobner-2000], [gajewski-2005]).
* `display` — a representative Table 13 display for each tested C-series cell.

## Main results

* `supervaluation_matches_pool` — the supervaluation/local-exhaustification
  prediction reproduces every pooled projection judgment: §6.4's bottom line,
  at the price of either local exhaustification in downward-entailing contexts
  (contra [chierchia-fox-spector-2012]) or a restricted candidate set.
* `globalConstrual_divergence` — construals comparing the literal meaning with
  *global* exhaustification fail on exactly the C2 `no` gap and the C4 gap??
  gap, the paper's two problem cells for (si1)/(si3).
* `universalPresupposition_divergence` — universal projection fails on exactly
  the bivalently-judged conditions containing non-homogeneous cells (argument
  (42) of §6.3) plus the gap? condition.
* `globalConstrual_every`, `globalConstrual_no_never_gap` — §6.1.3's structural
  observations: all implicature construals align in the scope of `every`, and
  without local exhaustification no gap can arise in the scope of `no`.
* `supervaluationGap_matches_pool`, `bareLiteral_misses_negation_gap`,
  `wideScopeParse_matches_pool` — the unembedded grid: supervaluation predicts
  the polarity × scenario judgments; the bare existential literal meaning
  predicts no gap under negation (the downward-entailing problem of §6.1.3);
  the wide-scope parse of the definite (fn. 18) restores the fit.

## Todo

* [george-2008]-style trivalent presupposition projection — the variant §6.3
  endorses as matching the supervaluation predictions — is not implemented,
  nor are the richer-candidate supervaluation variants of fn. 19, which
  over-predict a gap in the gap? condition.
-/

namespace KrizChemla2015

open Features (Polarity)
open Generalizations Generalizations.HomogeneityProjection

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
  fun c => inferInstanceAs (Decidable (c ≠ .mixed))

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

/-- A representative Table 13 display for each condition of Exps. C2-C4
(`none` for cells the paper did not test). Read `[cell₁, ..., cell₄]` for the
four boys; e.g. the `(every, gap)` display 9929 — three boys found all nine of
their presents, one found two — is `[full, full, mixed, full]`. -/
def display : EmbeddingOperator → GapScenario → Option Display
  | .every, .trueScenario       => some [.full, .full, .full, .full]     -- 9999
  | .every, .falseScenario      => some [.full, .mixed, .mixed, .empty]  -- 9770
  | .every, .gap                => some [.full, .full, .mixed, .full]    -- 9929
  | .no, .trueScenario          => some [.empty, .empty, .empty, .empty] -- 0000
  | .no, .falseScenario         => some [.mixed, .empty, .empty, .full]  -- 5009
  | .no, .gap                   => some [.empty, .empty, .mixed, .empty] -- 0070
  | .exactlyTwo, .trueScenario  => some [.full, .full, .empty, .empty]   -- 9900
  | .exactlyTwo, .falseScenario => some [.mixed, .empty, .empty, .empty] -- 4000
  | .exactlyTwo, .gap           => some [.full, .mixed, .empty, .empty]  -- 9200
  | .exactlyTwo, .gapQ          => some [.full, .mixed, .empty, .mixed]  -- 9202
  | .exactlyTwo, .gapQQ         => some [.full, .mixed, .empty, .full]   -- 9209
  | _, _ => none

/-- Restrict a display-level account to the paper's tested grid, `none`
marking cells the paper did not test. -/
def predictOn (account : EmbeddingOperator → Display → Trivalent)
    (op : EmbeddingOperator) (sc : GapScenario) : Option Trivalent :=
  (display op sc).map (account op)

/-! ### Predictions against the projection pool -/

/-- The supervaluation (equivalently, local-exhaustification) prediction
reproduces every pooled projection judgment — §6.4's bottom line. The fit is
bought either by allowing local exhaustification in downward-entailing
contexts, contra [chierchia-fox-spector-2012], or by restricting the
supervaluation candidates to the existential and universal resolutions. -/
theorem supervaluation_matches_pool :
    ∀ d ∈ allData, d.source.bibkey = "kriz-chemla-2015" →
      predictOn supervaluation d.operator d.scenario = some d.observed := by
  decide

/-- Construals locating the gap in a literal-vs-global-exhaustification
conflict fail on exactly two cells: the small-but-robust `no` gap of Exp. C2
(no implicature arises in a downward-entailing context, §6.1.3) and the gap??
gap of Exp. C4 (Table 12's s6, where the literal meaning and the implicature
are false and true respectively, so their conjunction is simply false). Both
cells are predicted clearly false but observed gappy. -/
theorem globalConstrual_divergence :
    ∀ d ∈ allData, d.source.bibkey = "kriz-chemla-2015" →
      (predictOn globalConstrual d.operator d.scenario ≠ some d.observed ↔
        (d.operator, d.scenario) ∈
          [(EmbeddingOperator.no, GapScenario.gap), (.exactlyTwo, .gapQQ)]) := by
  decide

/-- Universal projection of the homogeneity presupposition fails on exactly
the bivalently-judged conditions whose displays contain non-homogeneous cells
— the false conditions of Exps. C2/C3, argument (42) of §6.3 — plus the gap?
condition, where a presupposition failure is predicted but falsity observed. -/
theorem universalPresupposition_divergence :
    ∀ d ∈ allData, d.source.bibkey = "kriz-chemla-2015" →
      (predictOn universalPresupposition d.operator d.scenario ≠ some d.observed ↔
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
    fun ha c hc => by simp [ha c hc]
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

/-- The negated sentence with the definite parsed above negation (fn. 18):
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
