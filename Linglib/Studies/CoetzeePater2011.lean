import Linglib.Phonology.OptimalityTheory.PartiallyOrderedConstraints
import Linglib.Phonology.HarmonicGrammar.Expressivity
import Linglib.Phonology.Constraints.Harmony
import Linglib.Core.Optimization.System

/-!
# Coetzee and Pater (2011): the place of variation in phonological theory

A variable process realizes one morpheme in more than one phonetic form in a single
environment. Coetzee and Pater argue from English word-final t/d-deletion (*west* ~ *wes*)
that variation belongs to the grammar rather than to phonetic implementation, since its rate
is conditioned by morphology (table (7), after Guy) and by the lexicon (§5), and they compare
the models of grammar that assign a probability distribution to the outputs of one input. In
the partially ordered constraints (POC) model of Kiparsky and Anttila a grammar is a partial
order on the constraint set, each evaluation samples one of its linear extensions, and the
probability of an output is the fraction of extensions selecting it ((9)). The chapter's
four-constraint analysis (11), after Coetzee's dissertation, protects t/d by MAX everywhere
and by the cue-based MAX-PRE-V and MAX-FINAL before a vowel and phrase-finally, so deletion is
highest before a consonant in every ranking, the cross-dialectal generalization Labov reports
and table (10) instantiates. Stochastic OT, which samples rankings from noisy constraint
values, and Harmonic Grammar with non-negative weights keep this restriction; MaxEnt-HG with
negative weights and Labov's variable rules do not (§4.4, tables (23) and (25)). Harmonic
Grammar also expresses the cumulative constraint interaction of Japanese loanword devoicing
((18)–(19), after Itô and Mester and Kawahara), which no ranking does.

We derive table (12) and the rates of table (13) from the POC substrate, prove the
restriction for every distribution over rankings, and check the MaxEnt-HG and variable-rule
computations of tables (23) and (25).

## Implementation notes

Locators follow the ROA-946 draft of 6 October 2009. Constraint indices follow (11):
0 = \*CT, 1 = MAX, 2 = MAX-PRE-V, 3 = MAX-FINAL. The stochastic OT and Noisy HG rows of
tables (14), (21), (23) and (32) are Praat simulations and are not formalized.

## TODO

* Table (13) rows (b)–(e) print 6/12 for pre-consonantal deletion under every single fixed
  ranking. Counting linear extensions as (9) prescribes gives 4/12, 8/12, 4/12 and 8/12, with
  the other contexts likewise off (`deletionProb_maxPreV_starCT` and its siblings), and
  MAX-PRE-V ≫ \*CT gives the pre-consonantal rate 1/3 that §3.3 excludes. The published
  chapter has not been checked for a correction.

## References

* [A. W. Coetzee and J. Pater, *The Place of Variation in Phonological Theory*
  (2011)][coetzee-pater-2011]
* [P. Kiparsky, *An OT Perspective on Phonological Variation* (1993)][kiparsky-1993b]
* [A. Anttila, *Deriving Variation from Grammar* (1997)][anttila-1997]
* [W. Labov, *Contraction, Deletion, and Inherent Variability of the English Copula*
  (1969)][labov-1969]
* [W. Labov, *The Child as Linguistic Historian* (1989)][labov-1989]
* [G. R. Guy, *Explanation in Variable Phonology: An Exponential Model of Morphological
  Constraints* (1991)][guy-1991]
* [H. J. Cedergren and D. Sankoff, *Variable Rules: Performance as a Statistical Reflection of
  Competence* (1974)][cedergren-sankoff-1974]
* [P. Boersma, *Functional Phonology* (1998)][boersma-1998]
* [P. Boersma and B. Hayes, *Empirical Tests of the Gradual Learning Algorithm*
  (2001)][boersma-hayes-2001]
* [P. Smolensky and G. Legendre, *The Harmonic Mind: From Neural Computation to
  Optimality-Theoretic Grammar* (2006)][smolensky-legendre-2006]
* [S. Goldwater and M. Johnson, *Learning OT Constraint Rankings Using a Maximum Entropy
  Model* (2003)][goldwater-johnson-2003]
* [G. Jäger, *Maximum Entropy Models and Stochastic Optimality Theory* (2007)][jaeger-2007]
* [A. W. Coetzee, *What It Means to Be a Loser: Non-Optimal Candidates in Optimality Theory*
  (2004)][coetzee-2004]
* [J. Itô and A. Mester, *The Phonology of Voicing in Japanese* (1986)][ito-mester-1986]
* [S. Kawahara, *A Faithfulness Ranking Projected from a Perceptibility Scale: The Case of
  [+voice] in Japanese* (2006)][kawahara-2006]
-/

namespace CoetzeePater2011

open Constraints OptimalityTheory Core.Optimization HarmonicGrammar Finset Real

/-! ### Deletion rates by context and by morphology (tables (10) and (7)) -/

/-- What follows the word-final cluster: *west end*, *west*, *west side*. -/
inductive Context
  | preV
  | pause
  | preC
  deriving DecidableEq, Fintype

/-- The dialects of table (10). -/
inductive Dialect
  | aave
  | chicano
  | jamaican
  | newYorkCity
  | tejano
  | trinidad
  | philadelphia
  deriving DecidableEq, Fintype

/-- Percent deletion by dialect and following context, table (10). -/
def deletionRate : Dialect → Context → ℕ
  | .aave, .preV => 29 | .aave, .pause => 73 | .aave, .preC => 76
  | .chicano, .preV => 45 | .chicano, .pause => 37 | .chicano, .preC => 62
  | .jamaican, .preV => 63 | .jamaican, .pause => 71 | .jamaican, .preC => 85
  | .newYorkCity, .preV => 66 | .newYorkCity, .pause => 83 | .newYorkCity, .preC => 100
  | .tejano, .preV => 25 | .tejano, .pause => 46 | .tejano, .preC => 62
  | .trinidad, .preV => 21 | .trinidad, .pause => 31 | .trinidad, .preC => 81
  | .philadelphia, .preV => 38 | .philadelphia, .pause => 12 | .philadelphia, .preC => 100

/-- Deletion is highest pre-consonantally in every dialect of table (10), Labov's
cross-dialectal generalization. -/
theorem deletionRate_le_preC (d : Dialect) (ctx : Context) :
    deletionRate d ctx ≤ deletionRate d .preC := by
  cases d <;> cases ctx <;> decide

/-- Chicano and Philadelphia delete more pre-vocalically than phrase-finally, and the other
dialects the reverse. -/
theorem pause_lt_preV_iff (d : Dialect) :
    deletionRate d .pause < deletionRate d .preV ↔ d = .chicano ∨ d = .philadelphia := by
  cases d <;> decide

theorem preV_lt_pause_iff (d : Dialect) :
    deletionRate d .preV < deletionRate d .pause ↔ d ≠ .chicano ∧ d ≠ .philadelphia := by
  cases d <;> decide

/-- Morphological status of the final t/d: *missed*, *kept*, *mist*. -/
inductive MorphStatus
  | regularPast
  | semiWeakPast
  | monomorpheme
  deriving DecidableEq, Fintype

/-- Percent deletion by morphological status, table (7), for the three dialects it reports. -/
def morphDeletionRate : Dialect → Option (MorphStatus → ℕ)
  | .philadelphia => some λ | .regularPast => 17 | .semiWeakPast => 34 | .monomorpheme => 38
  | .chicano => some λ | .regularPast => 26 | .semiWeakPast => 41 | .monomorpheme => 58
  | .tejano => some λ | .regularPast => 24 | .semiWeakPast => 34 | .monomorpheme => 56
  | _ => none

/-- Guy's three-way ordering, regular past below semi-weak past below monomorpheme, holds in
every dialect of table (7). -/
theorem morphDeletionRate_lt {d : Dialect} {r : MorphStatus → ℕ}
    (h : morphDeletionRate d = some r) :
    r .regularPast < r .semiWeakPast ∧ r .semiWeakPast < r .monomorpheme := by
  cases d <;> simp only [morphDeletionRate, Option.some.injEq, reduceCtorEq] at h <;>
    subst h <;> decide

/-- Tejano′, the Tejano rates with pre-vocalic and pre-consonantal traded (§4.4). -/
def tejanoPrime : Context → ℕ
  | .preV => deletionRate .tejano .preC
  | .pause => deletionRate .tejano .pause
  | .preC => deletionRate .tejano .preV

/-! ### The constraints of (11) -/

/-- Retain the final t/d (*west*) or delete it (*wes*). -/
inductive Output
  | retain
  | delete
  deriving DecidableEq, Fintype

/-- A candidate: the following context with the output. -/
abbrev Candidate := Context × Output

/-- \*CT: a consonant cluster ending in a coronal stop. -/
def starCT : Constraint Candidate := Constraint.binary (·.2 = .retain)

/-- MAX: an input consonant missing from the output. -/
def maxC : Constraint Candidate := Constraint.binary (·.2 = .delete)

/-- MAX-PRE-V: a pre-vocalic input consonant missing from the output. -/
def maxPreV : Constraint Candidate := Constraint.binary λ c => c.2 = .delete ∧ c.1 = .preV

/-- MAX-FINAL: a phrase-final input consonant missing from the output. -/
def maxFinal : Constraint Candidate := Constraint.binary λ c => c.2 = .delete ∧ c.1 = .pause

/-- The constraint set (11), in the paper's order. -/
def con : CON Candidate 4 := ![starCT, maxC, maxPreV, maxFinal]

/-- Violation profiles in the shape POC's `winProb` consumes. -/
def vp (ctx : Context) (o : Output) (i : Fin 4) : ℕ := con i (ctx, o)

/-- Both outputs compete in every context. -/
def cands : Context → Finset Output := λ _ => univ

theorem cands_eq (ctx : Context) : cands ctx = {.delete, .retain} := by cases ctx <;> decide

/-! ### Categorical systems (table (12)) -/

/-- Ranking `σ` deletes in `ctx` if deletion is its unique optimum. -/
def Deletes (σ : Ranking 4) (ctx : Context) : Prop := PicksAt cands vp σ ctx .delete

instance (σ : Ranking 4) (ctx : Context) : Decidable (Deletes σ ctx) :=
  inferInstanceAs (Decidable (PicksAt cands vp σ ctx .delete))

/-- Pre-consonantal deletion needs only \*CT ≫ MAX. -/
theorem deletes_preC_iff : ∀ σ : Ranking 4, Deletes σ .preC ↔ σ.Dominates 0 1 := by decide

/-- Pre-vocalic deletion needs \*CT above both MAX and MAX-PRE-V. -/
theorem deletes_preV_iff :
    ∀ σ : Ranking 4, Deletes σ .preV ↔ σ.Dominates 0 1 ∧ σ.Dominates 0 2 := by decide

/-- Phrase-final deletion needs \*CT above both MAX and MAX-FINAL. -/
theorem deletes_pause_iff :
    ∀ σ : Ranking 4, Deletes σ .pause ↔ σ.Dominates 0 1 ∧ σ.Dominates 0 3 := by decide

/-- The contexts in which `σ` deletes, the categorical system it generates. -/
def system (σ : Ranking 4) : Finset Context := univ.filter (Deletes σ)

/-- The five systems of table (12), rows (a)–(e), from no deletion to deletion in all three
contexts. -/
theorem image_system :
    univ.image system = {∅, {.pause, .preC}, {.preV, .preC}, {.preC}, univ} := by decide

/-- Twelve rankings, those with MAX ≫ \*CT, delete nowhere (table (12)). -/
theorem card_system_empty : (univ.filter (system · = ∅)).card = 12 := by decide

theorem card_system_pause_preC : (univ.filter (system · = {.pause, .preC})).card = 2 := by
  decide

theorem card_system_preV_preC : (univ.filter (system · = {.preV, .preC})).card = 2 := by
  decide

theorem card_system_preC : (univ.filter (system · = {.preC})).card = 2 := by decide

/-- Six rankings, those with \*CT on top, delete everywhere. -/
theorem card_system_univ : (univ.filter (system · = univ)).card = 6 := by decide

/-! ### Deletion probabilities (9), table (13) -/

/-- The probability that grammar `r` deletes in `ctx`, the fraction of its linear extensions
picking deletion (9). -/
def deletionProb (r : Fin 4 → Fin 4 → Prop) [DecidableRel r] (ctx : Context) : ℚ :=
  winProb cands vp r ctx .delete

/-- Only \*CT favors deletion, in every context. -/
theorem favoring_eq (ctx : Context) : favoring vp ctx .delete .retain = {0} := by
  cases ctx <;> decide

/-- MAX alone protects t/d pre-consonantally. -/
theorem active_preC : active vp .preC .delete .retain = {0, 1} := by decide

/-- MAX-PRE-V joins MAX pre-vocalically. -/
theorem active_preV : active vp .preV .delete .retain = {0, 1, 2} := by decide

/-- MAX-FINAL joins MAX phrase-finally. -/
theorem active_pause : active vp .pause .delete .retain = {0, 1, 3} := by decide

/-- With no ranking imposed (row (a)), 8 of the 24 rankings delete pre-vocalically, since
\*CT must outrank both protecting constraints. -/
theorem deletionProb_discrete_preV : deletionProb (· = ·) .preV = 1/3 := by
  rw [deletionProb, winProb_discrete_binary_rate (cands_eq _) (by decide), favoring_eq,
    active_preV]
  decide +kernel

/-- With no ranking imposed, 8 of 24 delete phrase-finally. -/
theorem deletionProb_discrete_pause : deletionProb (· = ·) .pause = 1/3 := by
  rw [deletionProb, winProb_discrete_binary_rate (cands_eq _) (by decide), favoring_eq,
    active_pause]
  decide +kernel

/-- With no ranking imposed, 12 of 24 delete pre-consonantally, where \*CT need only outrank
MAX. -/
theorem deletionProb_discrete_preC : deletionProb (· = ·) .preC = 1/2 := by
  rw [deletionProb, winProb_discrete_binary_rate (cands_eq _) (by decide), favoring_eq,
    active_preC]
  decide +kernel

/-- The grammar fixing the single ranking `a ≫ b`, rows (b)–(e). -/
def ranked (a b : Fin 4) : Fin 4 → Fin 4 → Prop := λ x y => x = y ∨ x = a ∧ y = b

instance (a b : Fin 4) : DecidableRel (ranked a b) :=
  λ _ _ => inferInstanceAs (Decidable (_ ∨ _ ∧ _))

/-- A single ranking of distinct constraints is a partial order, so a POC grammar. -/
theorem ranked_isPartialOrder {a b : Fin 4} (h : a ≠ b) :
    IsPartialOrder (Fin 4) (ranked a b) where
  refl _ := Or.inl rfl
  trans _ _ _ hxy hyz := by
    rcases hxy with rfl | ⟨rfl, rfl⟩
    · exact hyz
    · rcases hyz with rfl | ⟨rfl, -⟩
      · exact Or.inr ⟨rfl, rfl⟩
      · exact absurd rfl h
  antisymm _ _ hxy hyx := by
    rcases hxy with rfl | ⟨rfl, rfl⟩
    · rfl
    · rcases hyx with h' | ⟨rfl, -⟩
      · exact h'.symm
      · exact absurd rfl h

/-- Under MAX-PRE-V ≫ \*CT (row (b)), 0, 2 and 4 of the 12 linear extensions delete. The
pre-consonantal rate 1/3 is not among the 0, .50 and 1 that §3.3 says POC derives there. -/
theorem deletionProb_maxPreV_starCT :
    deletionProb (ranked 2 0) .preV = 0 ∧ deletionProb (ranked 2 0) .pause = 1/6 ∧
      deletionProb (ranked 2 0) .preC = 1/3 := by
  decide +kernel

/-- Under \*CT ≫ MAX-PRE-V (row (c)), 8, 6 and 8 of 12 delete. -/
theorem deletionProb_starCT_maxPreV :
    deletionProb (ranked 0 2) .preV = 2/3 ∧ deletionProb (ranked 0 2) .pause = 1/2 ∧
      deletionProb (ranked 0 2) .preC = 2/3 := by
  decide +kernel

/-- Under MAX-FINAL ≫ \*CT (row (d)), 2, 0 and 4 of 12 delete. -/
theorem deletionProb_maxFinal_starCT :
    deletionProb (ranked 3 0) .preV = 1/6 ∧ deletionProb (ranked 3 0) .pause = 0 ∧
      deletionProb (ranked 3 0) .preC = 1/3 := by
  decide +kernel

/-- Under \*CT ≫ MAX-FINAL (row (e)), 6, 8 and 8 of 12 delete. -/
theorem deletionProb_starCT_maxFinal :
    deletionProb (ranked 0 3) .preV = 1/2 ∧ deletionProb (ranked 0 3) .pause = 2/3 ∧
      deletionProb (ranked 0 3) .preC = 2/3 := by
  decide +kernel

/-! ### The restriction shared by POC and stochastic OT (§3.2, §4.4) -/

/-- Pre-vocalic or phrase-final deletion entails pre-consonantal deletion, so no ranking
deletes only where a contextual faithfulness constraint protects t/d. -/
theorem deletes_preC_of_deletes {σ : Ranking 4} {ctx : Context} (h : Deletes σ ctx) :
    Deletes σ .preC := by
  cases ctx
  · exact (deletes_preC_iff σ).mpr ((deletes_preV_iff σ).mp h).1
  · exact (deletes_preC_iff σ).mpr ((deletes_pause_iff σ).mp h).1
  · exact h

/-- Any distribution over rankings, POC's or stochastic OT's, deletes at least as often
pre-consonantally as in either other context. -/
theorem sum_le_sum_preC (μ : Ranking 4 → ℝ) (hμ : 0 ≤ μ) (ctx : Context) :
    ∑ σ ∈ univ.filter (Deletes · ctx), μ σ ≤
      ∑ σ ∈ univ.filter (Deletes · .preC), μ σ :=
  sum_le_sum_of_subset_of_nonneg (monotone_filter_right _ λ _ _ => deletes_preC_of_deletes)
    λ σ _ _ => hμ σ

/-- Under every POC grammar the pre-consonantal rate is the highest. -/
theorem deletionProb_le_preC (r : Fin 4 → Fin 4 → Prop) [DecidableRel r] (ctx : Context) :
    deletionProb r ctx ≤ deletionProb r .preC :=
  winProb_mono λ _ _ => deletes_preC_of_deletes

/-- No POC grammar produces Tejano′, whose pre-consonantal rate is its lowest. -/
theorem tejanoPrime_not_poc (r : Fin 4 → Fin 4 → Prop) [DecidableRel r] :
    ¬ ∀ ctx, deletionProb r ctx = tejanoPrime ctx / 100 := by
  intro h
  have := deletionProb_le_preC r .preV
  rw [h, h] at this
  norm_num [tejanoPrime, deletionRate] at this

/-! ### Harmonic Grammar (§4.2) -/

variable {w : Fin 4 → ℝ}

/-- Retention violates only \*CT. -/
@[simp] theorem harmonyScore_retain (ctx : Context) :
    harmonyScore con w (ctx, .retain) = -w 0 := by
  cases ctx <;> simp [harmonyScore_eq_neg_sum, Fin.sum_univ_four, con, starCT, maxC, maxPreV,
    maxFinal]

/-- Pre-vocalic deletion violates MAX and MAX-PRE-V. -/
@[simp] theorem harmonyScore_delete_preV :
    harmonyScore con w (.preV, .delete) = -(w 1 + w 2) := by
  simp [harmonyScore_eq_neg_sum, Fin.sum_univ_four, con, starCT, maxC, maxPreV, maxFinal]

/-- Phrase-final deletion violates MAX and MAX-FINAL. -/
@[simp] theorem harmonyScore_delete_pause :
    harmonyScore con w (.pause, .delete) = -(w 1 + w 3) := by
  simp [harmonyScore_eq_neg_sum, Fin.sum_univ_four, con, starCT, maxC, maxPreV, maxFinal]

/-- Pre-consonantal deletion violates MAX alone. -/
@[simp] theorem harmonyScore_delete_preC :
    harmonyScore con w (.preC, .delete) = -w 1 := by
  simp [harmonyScore_eq_neg_sum, Fin.sum_univ_four, con, starCT, maxC, maxPreV, maxFinal]

/-- Deletion in `ctx` has greater harmony than retention under weights `w` ((16)–(17)). -/
def HGDeletes (w : Fin 4 → ℝ) (ctx : Context) : Prop :=
  harmonyDominates con w (ctx, .delete) (ctx, .retain)

@[simp] theorem hgDeletes_preC_iff : HGDeletes w .preC ↔ w 1 < w 0 := by
  simp [HGDeletes]

@[simp] theorem hgDeletes_preV_iff : HGDeletes w .preV ↔ w 1 + w 2 < w 0 := by
  simp [HGDeletes]

@[simp] theorem hgDeletes_pause_iff : HGDeletes w .pause ↔ w 1 + w 3 < w 0 := by
  simp [HGDeletes]

/-- Tableau (17), \*CT weighted 2 over MAX weighted 1. -/
example : HGDeletes ![2, 1, 0, 0] .preC := by simp

/-- With non-negative weights, HG shares POC's implication. -/
theorem hgDeletes_preC_of_hgDeletes (hw : ∀ i, 0 ≤ w i) {ctx : Context} (h : HGDeletes w ctx) :
    HGDeletes w .preC := by
  rw [hgDeletes_preC_iff]
  cases ctx
  · rw [hgDeletes_preV_iff] at h; linarith [hw 2]
  · rw [hgDeletes_pause_iff] at h; linarith [hw 3]
  · rwa [hgDeletes_preC_iff] at h

/-- With non-negative weights, HG generates one of the five systems of table (12)
(footnote 8). -/
theorem hg_system_mem (hw : ∀ i, 0 ≤ w i) :
    ∃ S ∈ univ.image system, ∀ ctx, HGDeletes w ctx ↔ ctx ∈ S := by
  rw [image_system]
  by_cases h1 : w 1 < w 0
  · by_cases h2 : w 1 + w 2 < w 0 <;> by_cases h3 : w 1 + w 3 < w 0
    · exact ⟨univ, by decide, λ ctx => by
        cases ctx <;> simp [*]⟩
    · exact ⟨{.preV, .preC}, by decide, λ ctx => by
        cases ctx <;> simp [*]⟩
    · exact ⟨{.pause, .preC}, by decide, λ ctx => by
        cases ctx <;> simp [*]⟩
    · exact ⟨{.preC}, by decide, λ ctx => by
        cases ctx <;> simp [*]⟩
  · refine ⟨∅, by decide, λ ctx => ?_⟩
    cases ctx <;> simp <;> linarith [hw 2, hw 3]

/-- Each of the five systems is generated by some non-negative weighting. -/
theorem exists_hg_of_mem {S : Finset Context} (hS : S ∈ univ.image system) :
    ∃ w : Fin 4 → ℝ, (∀ i, 0 ≤ w i) ∧ ∀ ctx, HGDeletes w ctx ↔ ctx ∈ S := by
  rw [image_system] at hS
  simp only [mem_insert, mem_singleton] at hS
  rcases hS with rfl | rfl | rfl | rfl | rfl
  · exact ⟨![0, 1, 0, 0], λ i => by fin_cases i <;> norm_num, λ ctx => by
      cases ctx <;> simp [Matrix.cons_val_two, Matrix.cons_val_three]⟩
  · exact ⟨![1, 0, 1, 0], λ i => by fin_cases i <;> norm_num, λ ctx => by
      cases ctx <;> simp [Matrix.cons_val_two, Matrix.cons_val_three]⟩
  · exact ⟨![1, 0, 0, 1], λ i => by fin_cases i <;> norm_num, λ ctx => by
      cases ctx <;> simp [Matrix.cons_val_two, Matrix.cons_val_three]⟩
  · exact ⟨![1, 0, 1, 1], λ i => by fin_cases i <;> norm_num, λ ctx => by
      cases ctx <;> simp [Matrix.cons_val_two, Matrix.cons_val_three]⟩
  · exact ⟨![1, 0, 0, 0], λ i => by fin_cases i <;> norm_num, λ ctx => by
      cases ctx <;> simp [Matrix.cons_val_two, Matrix.cons_val_three]⟩

/-- A negative MAX-PRE-V weight rewards pre-vocalic deletion, giving deletion pre-vocalically
alone (§4.4). -/
theorem hgDeletes_neg (ctx : Context) : HGDeletes ![0, 0, -1, 0] ctx ↔ ctx = .preV := by
  cases ctx <;> simp [Matrix.cons_val_two, Matrix.cons_val_three]

/-- Deletion pre-vocalically alone is not among the systems of table (12). -/
theorem singleton_preV_not_mem : {Context.preV} ∉ univ.image system := by decide

/-! ### Cumulativity: Japanese loanword devoicing (18)–(19) -/

/-- The loanwords of (18)–(19): *bobu* 'Bob', *webbu* 'web', *guddo* 'good'. -/
inductive Loan
  | bobu
  | webbu
  | guddo
  deriving DecidableEq, Fintype

/-- The tableaux (18)–(19) as a realization problem over IDENT-VOICE, OCP-VOICE and
\*VOICED-GEMINATE, after Itô and Mester and Kawahara. The faithful output (`true`) violates
OCP-VOICE in *bobu*, \*VOICED-GEMINATE in *webbu* and both in *guddo*, the devoiced output
violates IDENT-VOICE, and only *guddo* devoices. -/
def loanwordDevoicing : RealizationProblem Loan Bool 3 where
  inputs := univ
  cands _ := univ
  vp
    | .bobu, true => ![0, 1, 0]
    | .webbu, true => ![0, 0, 1]
    | .guddo, true => ![0, 1, 1]
    | _, false => ![1, 0, 0]
  target
    | .guddo => false
    | _ => true
  target_mem _ _ := mem_univ _

/-- The weights of (18)–(19), IDENT-VOICE 1.5 over OCP-VOICE 1 and \*VOICED-GEMINATE 1,
realize the pattern, since the two lower weights sum past the higher one only in *guddo*. -/
theorem loanwordDevoicing_realizedByWeighting :
    loanwordDevoicing.realizedByWeighting ![3/2, 1, 1] := by
  intro i _ o _ hne
  cases i <;> cases o <;>
    simp [loanwordDevoicing, weightedViolations, Fin.sum_univ_three] at hne ⊢ <;> norm_num

/-- No ranking realizes the pattern, the instance behind `hg_strictly_contains_ot`. -/
theorem loanwordDevoicing_not_isOTRealizable : ¬ loanwordDevoicing.IsOTRealizable := by decide

/-- With IDENT-VOICE weighted 2 over 1 and 1, *guddo* and *gutto* tie at harmony −2 and
MaxEnt-HG gives each probability ½ (tableau (22)). -/
theorem guddo_maxEnt_half :
    let s : ConstraintSystem Bool ℝ :=
      ⟨univ, λ o => -weightedViolations ![2, 1, 1] (loanwordDevoicing.vp .guddo o),
        softmaxDecoder 1⟩
    s.predict true = 2⁻¹ ∧ s.predict false = 2⁻¹ := by
  intro s
  have heq : s.predict true = s.predict false :=
    s.predict_softmax_eq_of_score_eq rfl (mem_univ _) (mem_univ _) (by
      simp [s, loanwordDevoicing, weightedViolations, Fin.sum_univ_three]; norm_num)
  have hsum := s.predict_softmax_isProb rfl ⟨true, mem_univ _⟩
  rw [Fintype.sum_bool] at hsum
  constructor <;> linarith

/-! ### MaxEnt-HG (§4.3–4.4) -/

/-- The MaxEnt-HG grammar for `ctx` under weights `w`, with probability proportional to the
exponential of harmony. -/
noncomputable def maxEnt (w : Fin 4 → ℝ) (ctx : Context) : ConstraintSystem Output ℝ :=
  ⟨univ, λ o => harmonyScore con w (ctx, o), softmaxDecoder 1⟩

/-- MaxEnt-HG's deletion probability in `ctx`. -/
noncomputable def maxEntProb (w : Fin 4 → ℝ) (ctx : Context) : ℝ :=
  (maxEnt w ctx).predict .delete

/-- With two candidates, the deletion probability is the logistic of the harmony
difference. -/
theorem maxEntProb_eq_sigmoid (w : Fin 4 → ℝ) (ctx : Context) :
    maxEntProb w ctx =
      sigmoid (harmonyScore con w (ctx, .delete) - harmonyScore con w (ctx, .retain)) := by
  rw [maxEntProb, (maxEnt w ctx).predict_softmax_pair rfl (by decide) (cands_eq ctx), one_mul]
  rfl

/-- MaxEnt-HG deletes by majority exactly when HG deletes. -/
theorem half_lt_maxEntProb_iff (ctx : Context) : 2⁻¹ < maxEntProb w ctx ↔ HGDeletes w ctx := by
  rw [maxEntProb_eq_sigmoid, ← sigmoid_zero, sigmoid_lt_iff, sub_pos, HGDeletes,
    harmonyDominates_iff]

/-- Non-negative contextual faithfulness keeps MaxEnt-HG within the POC restriction (§4.4). -/
theorem maxEntProb_le_preC (hw : ∀ i, 0 ≤ w i) (ctx : Context) :
    maxEntProb w ctx ≤ maxEntProb w .preC := by
  rw [maxEntProb_eq_sigmoid, maxEntProb_eq_sigmoid, sigmoid_le_iff]
  cases ctx <;> simp <;> linarith [hw 2, hw 3]

/-- The MaxEnt-HG weights learned for AAVE, table (23), in the order of (11). -/
noncomputable def aave : Fin 4 → ℝ := ![100.6, 99.4, 2.1, 0.2]

/-- Under the AAVE weights deletion is a minority pre-vocalically and a majority elsewhere,
highest pre-consonantally, as observed (.29, .73 and .76). -/
theorem aave_ordering :
    maxEntProb aave .preV < 2⁻¹ ∧ 2⁻¹ < maxEntProb aave .pause ∧
      maxEntProb aave .pause < maxEntProb aave .preC := by
  refine ⟨?_, ?_, ?_⟩
  · rw [maxEntProb_eq_sigmoid, ← sigmoid_zero, sigmoid_lt_iff]; simp [aave]; norm_num
  · rw [maxEntProb_eq_sigmoid, ← sigmoid_zero, sigmoid_lt_iff]; simp [aave]; norm_num
  · rw [maxEntProb_eq_sigmoid, maxEntProb_eq_sigmoid, sigmoid_lt_iff]; simp [aave]; norm_num

/-- The MaxEnt-HG weights learned for Tejano′, table (23), with negative contextual
faithfulness. -/
noncomputable def tejanoPrimeW : Fin 4 → ℝ := ![99.4, 100.6, -1.6, -0.8]

/-- Negative weights reward pre-vocalic and phrase-final deletion, so pre-consonantal deletion
is the rarest (the encoded .61, .42 and .24). -/
theorem tejanoPrimeW_ordering :
    maxEntProb tejanoPrimeW .preC < maxEntProb tejanoPrimeW .pause ∧
      maxEntProb tejanoPrimeW .pause < maxEntProb tejanoPrimeW .preV := by
  constructor <;>
    (rw [maxEntProb_eq_sigmoid, maxEntProb_eq_sigmoid, sigmoid_lt_iff]; simp [tejanoPrimeW];
      norm_num)

/-! ### Variable rules (§4.5) -/

/-- Cedergren and Sankoff's multiplicative variable-rule probability (24), from the input
probability `p₀` and one factor weight per contextual factor present. -/
def variableRule (p₀ : ℚ) (ps : List ℚ) : ℚ :=
  p₀ * ps.prod / (p₀ * ps.prod + (1 - p₀) * (ps.map (1 - ·)).prod)

/-- Goldvarb's Tejano weights, input .44 and pre-vocalic factor .30, give .25 ((26)). -/
theorem variableRule_tejano_preV : variableRule (44/100) [30/100] = 33/131 := by
  norm_num [variableRule]

/-- An informal-register factor .70 raises it to .44 ((27)). -/
theorem variableRule_informal : variableRule (44/100) [30/100, 70/100] = 44/100 := by
  norm_num [variableRule]

/-- One factor group with input probability ½ reproduces any rates, so Tejano′ fits as well
as Tejano ((25)) and the model imposes no typological restriction. -/
theorem variableRule_half (t : ℚ) : variableRule 2⁻¹ [t] = t := by
  unfold variableRule
  simp only [List.prod_cons, List.prod_nil, List.map_cons, List.map_nil, mul_one]
  have : 2⁻¹ * t + (1 - 2⁻¹) * (1 - t) = 2⁻¹ := by ring
  rw [this, div_eq_iff (by norm_num), mul_comm]

end CoetzeePater2011
