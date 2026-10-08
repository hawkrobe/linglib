module

public import Linglib.Data.Experiments.Schema

/-!
# SolstadBott2024: experimental results (generated)

Auto-generated from `Linglib/Data/Experiments/SolstadBott2024.json` by `scripts/gen_experiments.py`.
Do not edit by hand: edit the JSON and re-run the generator.

Block 2 of Experiments 1 and 2: the projectivity and at-issueness of the occasion implication of
German occasion verbs, and of the implications of stimulus-experiencer and experiencer-stimulus
psychological verbs, measured in the paradigm of Tonhauser, Beaver and Degen (2018) by certain-that
and asking-whether questions on a slider, transformed to [0, 1] with 1 the maximal projectivity and
the maximal at-issueness. The established triggers run alongside (possessive NP, NRRC, stop, know,
discover, personal pronoun, demonstrative in Experiment 1; appositives, again, too, cleft,
implicative, definites besides in Experiment 2) are plotted only.

## Raw data

* <https://osf.io/76rxb/>: materials, trial-level data and the analysis scripts of the three
  experiments (footnote 6); the Block 2 means can be recomputed from them

## References

* [solstad-bott-2024]
-/

@[expose] public section

namespace SolstadBott2024

open Data.Experiments

/-- The two experiments with a Block 2. -/
inductive Experiment where
  /-- Experiment 1: 16 occasion verbs beside seven established triggers, 71 participants -/
  | exp1
  /-- Experiment 2: 14 occasion verbs and 18 psychological verbs beside six established triggers,
  60 participants -/
  | exp2
  deriving DecidableEq, Repr, Fintype

/-- The Implicit Causality verb classes whose implications were rated. -/
inductive Trigger where
  /-- occasion verbs: agent-evocator verbs; the occasion implication -/
  | occasion
  /-- se-verbs: stimulus-experiencer psychological verbs -/
  | stimulusExperiencer
  /-- es-verbs: experiencer-stimulus psychological verbs -/
  | experiencerStimulus
  deriving DecidableEq, Repr, Fintype

/-- The unit over which a correlation was computed. -/
inductive Level where
  /-- trigger types: ratings aggregated over trigger types -/
  | triggerTypes
  /-- occasion verbs: the individual occasion verbs -/
  | occasionVerbs
  deriving DecidableEq, Repr, Fintype

/-- Whether a printed p-value is exact or an upper bound. -/
inductive PBound where
  /-- =: p as printed -/
  | exact
  /-- <: p is below the printed value -/
  | below
  deriving DecidableEq, Repr, Fintype

/-- Participants remaining in Experiment 1 after exclusions. (§2.2.1, p. 11:19; checked against
the page images.) -/
def participantsExp1 : ℕ := 71

/-- Native German participants in Experiment 2, all included in the analysis. (§3.1.1, pp.
11:30-31; checked against the page images.) -/
def participantsExp2 : ℕ := 60

/-- A row of §2.3.1, p. 11:25; §3.2.1, pp. 11:33-34; the by-trigger points of Figures 1 and 4 are
plotted only: the mean projectivity and at-issueness ratings of a verb class's implication in
Block 2, with the range over individual verbs where printed -/
structure Rating where
  /-- The experiment. -/
  experiment : Experiment
  /-- The verb class. -/
  trigger : Trigger
  /-- The number of verbs analysed. -/
  verbs : ℕ
  /-- Mean certain-that rating, 1 maximal. -/
  projectivity : Decimal
  /-- Mean asking-whether rating, 1 maximal at-issueness. -/
  atIssueness : Decimal
  /-- The range over individual verbs, where printed. -/
  projectivityRange : Option (List Decimal)
  /-- The range over individual verbs, where printed. -/
  atIssuenessRange : Option (List Decimal)
  deriving DecidableEq, Repr

/-- The 4 rows of §2.3.1, p. 11:25; §3.2.1, pp. 11:33-34; the by-trigger points of Figures 1 and
4 are plotted only, in the paper's order; checked against the page images. -/
def blockTwo : List Rating :=
  [⟨.exp1, .occasion, 16, ⟨79, 2⟩, ⟨32, 2⟩, some [⟨73, 2⟩, ⟨87, 2⟩], some [⟨17, 2⟩, ⟨57, 2⟩]⟩,
   ⟨.exp2,  -- loben and gratulieren excluded for copy-and-paste errors, §3.2, p. 11:33
     .occasion,
     14,
     ⟨69, 2⟩,
     ⟨35, 2⟩,
     none,
     none⟩,
   ⟨.exp2, .stimulusExperiencer, 9, ⟨54, 2⟩, ⟨52, 2⟩, none, none⟩,
   ⟨.exp2, .experiencerStimulus, 9, ⟨52, 2⟩, ⟨46, 2⟩, none, none⟩]

/-- A row of §2.3.1, pp. 11:24-26; §3.2.1, p. 11:34: Pearson correlations of mean projectivity
with mean at-issueness -/
structure Correlation where
  /-- The experiment. -/
  experiment : Experiment
  /-- The unit of aggregation. -/
  level : Level
  /-- Pearson's r. -/
  r : Decimal
  /-- Degrees of freedom of the t test. -/
  df : ℕ
  /-- The t statistic. -/
  t : Decimal
  /-- The printed p. -/
  p : Decimal
  /-- Whether p is exact or a bound. -/
  pBound : PBound
  deriving DecidableEq, Repr

/-- The 3 rows of §2.3.1, pp. 11:24-26; §3.2.1, p. 11:34, in the paper's order; checked against
the page images. -/
def correlations : List Correlation :=
  [⟨.exp1,  -- marginally significant; the sentence cites Tonhauser, Beaver and Degen 2018 as the pattern replicated
     .triggerTypes,
     ⟨-70, 2⟩,
     6,
     ⟨-237, 2⟩,
     ⟨6, 2⟩,
     .exact⟩,
   ⟨.exp1,  -- one lexicalization per verb; the paper cautions against reading the breakdown as more than limited data
     .occasionVerbs,
     ⟨5, 2⟩,
     14,
     ⟨18, 2⟩,
     ⟨86, 2⟩,
     .exact⟩,
   ⟨.exp2, .triggerTypes, ⟨-90, 2⟩, 7, ⟨-533, 2⟩, ⟨1, 2⟩, .below⟩]

end SolstadBott2024
