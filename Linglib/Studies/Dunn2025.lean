import Linglib.Syntax.ConstructionGrammar.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

/-!
# Dunn (2025): Syntactic Variation from Individuals to Populations

This file formalizes the model of grammar and the similarity pipeline of [dunn-2025], a
computational construction grammar in which a construction is a contiguous sequence of
slot-constraints drawn from three ontologies, lexical, syntactic and semantic, §1.2, and a
grammar is a network of constructions organized by order of emergence, the LEX-only,
SYN-only and SEM+ stages, by level of abstraction, first-order constructions bundled into
third-order and those into fourth-order constructions, and by centrality, §1.3. A first-order
construction's stage is read off its slot fillers, `emergenceStage`, and its level of
abstraction off the network, `Network`, whose siblings share a third-order parent and cousins
a fourth-order one, (6) to (11). The grammar of an individual or a population is the usage
frequency of the constructions, `Grammar`, the entrenchment of the umbrella grammar within
that group, §1.4; a central construction lies more than one standard deviation above the
mean frequency and a peripheral one below it, `Grammar.IsCentral`, and the frequency of a
higher-order construction is the sum over its children, `Grammar.lift`. Variation is measured
by the pipeline of Figure 3, §2.3: token frequencies are standardized across the samples,
weighted by the classifier's feature weights, compared by cosine distance, and the distances
standardized across the comparisons, so that a standardized distance of `1` is one standard
deviation more different than average. Cosine similarity is the cosine of the angle between
usage vectors, `Grammar.cosineSim`, invariant under scaling a profile, and standardized
values average to zero, `sum_zscore`.

## Implementation notes

Dunn's learned syntactic categories are rendered by the part of speech their exemplars share
and his noun phrase slots as phrasal slots, in the substrate's `SlotFiller`; semantic
constraints keep their human-readable labels. Frequencies are rational and the similarity
vectors real, on `EuclideanSpace ℝ C`, so that the cosine bounds and the self-similarity of a
nonzero profile are mathlib's facts about angles. The grammar induction by minimum
description length, the classifiers whose weights the pipeline takes, the Bayesian confidence
intervals, and the corpus results, Figure 1's counts and the accuracy tables, are not
represented.

## References

* [dunn-2025]
* [goldberg-2006]
-/

namespace Dunn2025

open ConstructionGrammar

/-! ### Constructions and their stage of emergence, §1.2 -/

/-- (1a): the ditransitive, a semantic constraint on the verb slot and two noun phrases. -/
def example1a : TypedForm String :=
  [ { filler := .semantic "transfer-event", isHead := true }, { filler := .phrasal }
  , { filler := .phrasal } ]

/-- (1c): the same construction with a lexical constraint in place of the semantic one,
*give NP a hand*. -/
def example1c : TypedForm String :=
  [ { filler := .fixed "give", isHead := true }, { filler := .phrasal }
  , { filler := .fixed "a hand" } ]

/-- (2): an early-stage noun phrase with two syntactic constraints, *peanut butter cup*. -/
def example2 : TypedForm String :=
  [ { filler := .open_ .NOUN }, { filler := .open_ .NOUN, isHead := true } ]

/-- (3): a late-stage noun phrase whose slot-constraints draw on all three ontologies,
`[ SEM:141 ⟨which–whereas⟩ – SYN:66 ⟨shadiest–silliest⟩ – LEX: "person" ]`, *the happiest
person*. -/
def example3 : TypedForm String :=
  [ { filler := .semantic "which-whereas" }, { filler := .open_ .ADJ }
  , { filler := .fixed "person", isHead := true } ]

/-- A lexical constraint in place of a semantic one makes the construction item-specific,
(1a) to (1c); (3) mixes open and fixed slots. -/
theorem specificity :
    derivedSpecificity example1a = .fullyAbstract ∧
      derivedSpecificity example1c = .partiallyOpen ∧
      derivedSpecificity example3 = .partiallyOpen := by
  decide

/-- The stages of emergence of Figure 1: lexical constraints only, syntactic constraints only,
and semantic constraints as well. -/
inductive Stage
  | lexOnly
  | synOnly
  | semPlus
  deriving DecidableEq, Repr

/-- Whether a filler is a semantic constraint. -/
def isSemantic {Lex : Type*} : SlotFiller Lex → Bool
  | .semantic _ => true
  | _ => false

/-- The stage at which a first-order construction emerges, read off its constraints. -/
def emergenceStage {Lex : Type*} (form : TypedForm Lex) : Stage :=
  if form.any (isSemantic ·.filler) then .semPlus
  else if form.any (·.filler.isOpen) then .synOnly
  else .lexOnly

/-- (2) is early-stage and (3) late-stage. -/
theorem emergenceStage_examples :
    emergenceStage example2 = .synOnly ∧ emergenceStage example3 = .semPlus := by
  decide

/-! ### The network, §1.3 -/

/-- The inheritance network: every first-order construction has a third-order parent and
every third-order construction a fourth-order parent. -/
structure Network (C₁ C₃ C₄ : Type*) where
  /-- The third-order construction bundling a first-order construction. -/
  parent₁ : C₁ → C₃
  /-- The fourth-order construction bundling a third-order construction. -/
  parent₃ : C₃ → C₄

namespace Network

variable {C₁ C₃ C₄ : Type*} (n : Network C₁ C₃ C₄)

/-- Siblings: first-order constructions of one third-order construction, (6) to (8). -/
def siblings : Setoid C₁ := Setoid.ker n.parent₁

/-- Cousins: first-order constructions of one fourth-order construction, (6) to (8) against
(9) to (11). -/
def cousins : Setoid C₁ := Setoid.ker (n.parent₃ ∘ n.parent₁)

/-- The levels of abstraction nest: siblings are cousins. -/
theorem siblings_le_cousins : n.siblings ≤ n.cousins := λ _ _ h => congrArg n.parent₃ h

end Network

/-! ### Grammars as frequency profiles and the centrality strata, §1.3 and §1.4 -/

/-- The grammar of an individual or population: the usage frequency of each construction,
relative frequencies rather than probabilities. -/
structure Grammar (C : Type*) where
  /-- Usage frequency of each construction. -/
  freq : C → ℚ
  freq_nonneg : ∀ c, 0 ≤ freq c

namespace Grammar

variable {C : Type*}

/-- Mean frequency across an inventory of constructions. -/
def meanFreq (g : Grammar C) (inv : Finset C) : ℚ := (∑ c ∈ inv, g.freq c) / inv.card

/-- Frequency variance across an inventory. -/
def varFreq (g : Grammar C) (inv : Finset C) : ℚ :=
  (∑ c ∈ inv, (g.freq c - g.meanFreq inv) ^ 2) / inv.card

/-- A construction is central when its frequency is more than one standard deviation above
the inventory mean. -/
def IsCentral (g : Grammar C) (inv : Finset C) (c : C) : Prop :=
  (g.meanFreq inv : ℝ) + Real.sqrt (g.varFreq inv) < g.freq c

/-- A construction is peripheral when its frequency is below the inventory mean. -/
def IsPeripheral (g : Grammar C) (inv : Finset C) (c : C) : Prop := g.freq c < g.meanFreq inv

/-- Centrality without the square root: above the mean, with squared deviation exceeding the
variance, which keeps it decidable in `ℚ`. -/
theorem isCentral_iff (g : Grammar C) (inv : Finset C) (c : C) :
    g.IsCentral inv c ↔
      g.meanFreq inv < g.freq c ∧ g.varFreq inv < (g.freq c - g.meanFreq inv) ^ 2 := by
  unfold IsCentral
  constructor
  · intro h
    have h0 := Real.sqrt_nonneg ((g.varFreq inv : ℚ) : ℝ)
    have hx : (0 : ℝ) < (g.freq c : ℝ) - g.meanFreq inv := by linarith
    have hsq := (Real.sqrt_lt' hx).mp (by linarith)
    exact ⟨by exact_mod_cast sub_pos.mp hx, by exact_mod_cast hsq⟩
  · rintro ⟨h1, h2⟩
    have hx : (0 : ℝ) < (g.freq c : ℝ) - g.meanFreq inv := by exact_mod_cast sub_pos.mpr h1
    have h2' : ((g.varFreq inv : ℚ) : ℝ) < ((g.freq c : ℝ) - g.meanFreq inv) ^ 2 := by
      exact_mod_cast h2
    have := (Real.sqrt_lt' hx).mpr h2'
    linarith

instance (g : Grammar C) (inv : Finset C) (c : C) : Decidable (g.IsCentral inv c) :=
  decidable_of_iff' _ (g.isCentral_iff inv c)

instance (g : Grammar C) (inv : Finset C) (c : C) : Decidable (g.IsPeripheral inv c) :=
  inferInstanceAs (Decidable (_ < _))

/-- The strata are disjoint. -/
theorem IsCentral.not_isPeripheral {g : Grammar C} {inv : Finset C} {c : C}
    (h : g.IsCentral inv c) : ¬ g.IsPeripheral inv c :=
  λ hp => lt_asymm ((g.isCentral_iff inv c).mp h).1 hp

/-- The frequency profile at a higher level of abstraction: each parent construction's
frequency is the sum of its children's, so that variation can be observed at any level. -/
def lift {D : Type*} [Fintype C] [DecidableEq D] (f : C → D) (g : Grammar C) : Grammar D where
  freq d := ∑ c ∈ Finset.univ.filter (f · = d), g.freq c
  freq_nonneg _ := Finset.sum_nonneg λ c _ => g.freq_nonneg c

/-- Lifting preserves total usage. -/
theorem sum_lift {D : Type*} [Fintype C] [Fintype D] [DecidableEq D] (f : C → D)
    (g : Grammar C) : ∑ d, (g.lift f).freq d = ∑ c, g.freq c :=
  Finset.sum_fiberwise _ f g.freq

/-! ### Similarity, Figure 3 -/

/-- A grammar's usage vector. -/
noncomputable def vec (g : Grammar C) : EuclideanSpace ℝ C := WithLp.toLp 2 λ c => (g.freq c : ℝ)

/-- A profile scaled by a nonnegative factor. -/
def smul (k : ℚ) (hk : 0 ≤ k) (g : Grammar C) : Grammar C where
  freq c := k * g.freq c
  freq_nonneg c := mul_nonneg hk (g.freq_nonneg c)

theorem vec_smul (k : ℚ) (hk : 0 ≤ k) (g : Grammar C) : (g.smul k hk).vec = (k : ℝ) • g.vec := by
  ext c
  simp [vec, smul]

variable [Fintype C]

/-- Cosine similarity: the cosine of the angle between usage vectors. -/
noncomputable def cosineSim (p q : Grammar C) : ℝ :=
  Real.cos (InnerProductGeometry.angle p.vec q.vec)

theorem cosineSim_comm (p q : Grammar C) : cosineSim p q = cosineSim q p := by
  rw [cosineSim, cosineSim, InnerProductGeometry.angle_comm]

theorem cosineSim_le_one (p q : Grammar C) : cosineSim p q ≤ 1 := Real.cos_le_one _

/-- Usage vectors are nonnegative, so their cosine is. -/
theorem cosineSim_nonneg (p q : Grammar C) : 0 ≤ cosineSim p q := by
  rw [cosineSim, InnerProductGeometry.cos_angle]
  refine div_nonneg ?_ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  simp only [vec, EuclideanSpace.inner_toLp_toLp, dotProduct, Pi.star_apply, star_trivial]
  exact Finset.sum_nonneg λ c _ =>
    mul_nonneg (by exact_mod_cast q.freq_nonneg c) (by exact_mod_cast p.freq_nonneg c)

/-- A nonzero profile has cosine similarity `1` with itself. -/
theorem cosineSim_self (p : Grammar C) (h : p.vec ≠ 0) : cosineSim p p = 1 := by
  rw [cosineSim, InnerProductGeometry.angle_self h, Real.cos_zero]

/-- Cosine similarity ignores the absolute size of a profile: only the distribution over
constructions matters. -/
theorem cosineSim_smul {k : ℚ} (hk : 0 < k) (p q : Grammar C) :
    cosineSim (p.smul k hk.le) q = cosineSim p q := by
  rw [cosineSim, vec_smul, InnerProductGeometry.angle_smul_left_of_pos _ _ (by exact_mod_cast hk)]
  rfl

/-- Cosine distance, the dissimilarity the pipeline standardizes and ranks. -/
noncomputable def cosineDist (p q : Grammar C) : ℝ := 1 - cosineSim p q

theorem cosineDist_nonneg (p q : Grammar C) : 0 ≤ cosineDist p q :=
  sub_nonneg.mpr (cosineSim_le_one p q)

theorem cosineDist_le_one (p q : Grammar C) : cosineDist p q ≤ 1 := by
  have := cosineSim_nonneg p q
  unfold cosineDist
  linarith

theorem cosineDist_self (p : Grammar C) (h : p.vec ≠ 0) : cosineDist p p = 0 := by
  rw [cosineDist, cosineSim_self p h, sub_self]

end Grammar

/-! ### Standardization, Figure 3 -/

variable {ι : Type*}

/-- The mean of a real feature over a finite set of samples. -/
noncomputable def mean (s : Finset ι) (x : ι → ℝ) : ℝ := (∑ i ∈ s, x i) / s.card

/-- The standard deviation of a real feature over a finite set of samples. -/
noncomputable def sd (s : Finset ι) (x : ι → ℝ) : ℝ :=
  Real.sqrt ((∑ i ∈ s, (x i - mean s x) ^ 2) / s.card)

/-- The z-score of a sample's value: its distance from the mean in standard deviations, the
standardization applied to construction frequencies across samples and to cosine distances
across comparisons. -/
noncomputable def zscore (s : Finset ι) (x : ι → ℝ) (i : ι) : ℝ := (x i - mean s x) / sd s x

/-- Deviations from the mean sum to zero. -/
theorem sum_sub_mean (s : Finset ι) (x : ι → ℝ) : ∑ i ∈ s, (x i - mean s x) = 0 := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mean]
  rcases s.eq_empty_or_nonempty with h | h
  · simp [h]
  · rw [mul_div_cancel₀ _ (by exact_mod_cast h.card_pos.ne')]
    exact sub_self _

/-- Standardized values average to zero: a standardized distance of `0` is an average
distance, and of `1` one standard deviation above it. -/
theorem sum_zscore (s : Finset ι) (x : ι → ℝ) : ∑ i ∈ s, zscore s x i = 0 := by
  unfold zscore
  rw [← Finset.sum_div, sum_sub_mean, zero_div]

/-- The standardized, weighted usage vector of a sample: each construction's frequency as a
z-score across the samples, weighted by the classifier's mean absolute feature weight. -/
noncomputable def standardizedVec {S C : Type*} [Fintype C] (samples : Finset S)
    (usage : S → Grammar C) (w : C → ℝ) (s : S) : EuclideanSpace ℝ C :=
  WithLp.toLp 2 λ c => w c * zscore samples (λ t => ((usage t).freq c : ℝ)) s

/-- The cosine distance between two samples' standardized vectors. -/
noncomputable def sampleDist {S C : Type*} [Fintype C] (samples : Finset S)
    (usage : S → Grammar C) (w : C → ℝ) (s t : S) : ℝ :=
  1 - Real.cos (InnerProductGeometry.angle (standardizedVec samples usage w s)
    (standardizedVec samples usage w t))

/-- The output of the pipeline: cosine distances standardized across the sampled pairs of
comparisons, which ranks the pairs from the most to the least similar. -/
noncomputable def standardizedDist {S C : Type*} [Fintype C] (samples : Finset S)
    (usage : S → Grammar C) (w : C → ℝ) (pairs : Finset (S × S)) (st : S × S) : ℝ :=
  zscore pairs (λ p => sampleDist samples usage w p.1 p.2) st

/-- Across the sampled comparisons the standardized distances average to zero. -/
theorem sum_standardizedDist {S C : Type*} [Fintype C] (samples : Finset S)
    (usage : S → Grammar C) (w : C → ℝ) (pairs : Finset (S × S)) :
    ∑ st ∈ pairs, standardizedDist samples usage w pairs st = 0 :=
  sum_zscore _ _

end Dunn2025
