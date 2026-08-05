import Linglib.Syntax.ConstructionGrammar.Basic
import Mathlib.Analysis.Real.Sqrt

/-!
# Dunn (2025): Syntactic Variation from Individuals to Populations

[dunn-2025] (Cambridge Elements in Construction Grammar) models syntactic
variation across individuals, populations (dialects), and contexts
(registers) in a computational CxG: constructions are sequences of
slot-constraints at the LEX/SYN/SEM levels (the `SlotFiller` levels of
`ConstructionGrammar`), and an individual's grammar is a frequency
profile over constructions. Formalized here: the frequency-profile
grammar (`Grammar`), the Element's centrality strata (central = more
than one standard deviation above the mean frequency; peripheral =
below the mean), and the cosine similarity underlying its
grammar-distance pipeline. The corpus case studies — classifier-based
variation detection, feature weighting, z-standardization of distances,
and the induced first- to fourth-order construction hierarchy — are
empirical pipeline, not formalized.
-/

namespace Dunn2025

open ConstructionGrammar

/-! ### Slot-constraints at three levels -/

/-- The Element's example (3): a late-stage noun-phrase construction whose
slot-constraints draw on all three sources — `[ SEM:141 ⟨which–whereas⟩ –
SYN:66 ⟨shadiest–silliest⟩ – LEX: "person" ]` — producing definite noun
phrases like "the worst person" and "the happiest person". The induced
SYN category, glossed by its superlative-adjective exemplars, is rendered
`ADJ`. -/
def example3 : TypedForm String :=
  [ { filler := .semantic "which-whereas" }
  , { filler := .open_ .ADJ }
  , { filler := .fixed "person", isHead := true } ]

/-- Example (3) mixes open (SEM, SYN) and fixed (LEX) slots. -/
theorem example3_specificity :
    derivedSpecificity example3 = .partiallyOpen := by decide

/-! ### Grammars as frequency profiles -/

/-- An individual's grammar: a nonnegative frequency profile over
constructions. The weights are relative frequencies, not probabilities —
no normalization is imposed. -/
structure Grammar (C : Type*) where
  /-- Usage frequency of each construction. -/
  freq : C → ℚ
  /-- Frequencies are nonnegative. -/
  freq_nonneg : ∀ c, 0 ≤ freq c

namespace Grammar

variable {C : Type*}

/-- Mean frequency across an inventory of constructions. -/
def meanFreq (g : Grammar C) (inv : Finset C) : ℚ :=
  (∑ c ∈ inv, g.freq c) / inv.card

/-- Frequency variance across an inventory. -/
def varFreq (g : Grammar C) (inv : Finset C) : ℚ :=
  (∑ c ∈ inv, (g.freq c - g.meanFreq inv) ^ 2) / inv.card

/-- A construction is central when its frequency is more than one standard
deviation above the inventory mean — the Element's operationalization of
the centrality strata. -/
def IsCentral (g : Grammar C) (inv : Finset C) (c : C) : Prop :=
  (g.meanFreq inv : ℝ) + Real.sqrt (g.varFreq inv) < g.freq c

/-- A construction is peripheral when its frequency is below the inventory
mean. -/
def IsPeripheral (g : Grammar C) (inv : Finset C) (c : C) : Prop :=
  g.freq c < g.meanFreq inv

/-- Squared characterization of centrality: above the mean, with squared
deviation exceeding the variance. Keeps centrality decidable in `ℚ`. -/
theorem isCentral_iff (g : Grammar C) (inv : Finset C) (c : C) :
    g.IsCentral inv c ↔
      g.meanFreq inv < g.freq c ∧
        g.varFreq inv < (g.freq c - g.meanFreq inv) ^ 2 := by
  unfold IsCentral
  constructor
  · intro h
    have h0 := Real.sqrt_nonneg ((g.varFreq inv : ℚ) : ℝ)
    have hx : (0 : ℝ) < (g.freq c : ℝ) - g.meanFreq inv := by linarith
    have hsq := (Real.sqrt_lt' hx).mp (by linarith)
    exact ⟨by exact_mod_cast sub_pos.mp hx, by exact_mod_cast hsq⟩
  · rintro ⟨h1, h2⟩
    have hx : (0 : ℝ) < (g.freq c : ℝ) - g.meanFreq inv := by
      exact_mod_cast sub_pos.mpr h1
    have h2' : ((g.varFreq inv : ℚ) : ℝ) < ((g.freq c : ℝ) - g.meanFreq inv) ^ 2 := by
      exact_mod_cast h2
    have := (Real.sqrt_lt' hx).mpr h2'
    linarith

instance (g : Grammar C) (inv : Finset C) (c : C) :
    Decidable (g.IsCentral inv c) :=
  decidable_of_iff' _ (g.isCentral_iff inv c)

instance (g : Grammar C) (inv : Finset C) (c : C) :
    Decidable (g.IsPeripheral inv c) :=
  inferInstanceAs (Decidable (_ < _))

/-- The strata are disjoint: no construction is both central and
peripheral. -/
theorem IsCentral.not_isPeripheral {g : Grammar C} {inv : Finset C} {c : C}
    (h : g.IsCentral inv c) : ¬ g.IsPeripheral inv c :=
  fun hp => lt_asymm ((g.isCentral_iff inv c).mp h).1 hp

/-! ### Similarity between grammars -/

/-- Cosine similarity of two frequency profiles over a shared inventory —
the inner-product measure underlying the Element's standardized
cosine-distance pipeline. -/
noncomputable def cosineSim (p q : Grammar C) (inv : Finset C) : ℝ :=
  (∑ c ∈ inv, (p.freq c : ℝ) * q.freq c) /
    (Real.sqrt (∑ c ∈ inv, (p.freq c : ℝ) ^ 2) *
      Real.sqrt (∑ c ∈ inv, (q.freq c : ℝ) ^ 2))

theorem cosineSim_comm (p q : Grammar C) (inv : Finset C) :
    cosineSim p q inv = cosineSim q p inv := by
  unfold cosineSim
  rw [mul_comm (Real.sqrt _), Finset.sum_congr rfl
    fun c _ => mul_comm ((p.freq c : ℝ)) ((q.freq c : ℝ))]

theorem cosineSim_nonneg (p q : Grammar C) (inv : Finset C) :
    0 ≤ cosineSim p q inv := by
  unfold cosineSim
  exact div_nonneg
    (Finset.sum_nonneg fun c _ => mul_nonneg
      (by exact_mod_cast p.freq_nonneg c) (by exact_mod_cast q.freq_nonneg c))
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

theorem cosineSim_le_one (p q : Grammar C) (inv : Finset C) :
    cosineSim p q inv ≤ 1 := by
  unfold cosineSim
  rcases eq_or_lt_of_le (mul_nonneg (Real.sqrt_nonneg
      (∑ c ∈ inv, (p.freq c : ℝ) ^ 2)) (Real.sqrt_nonneg _)) with h | h
  · rw [← h, div_zero]; exact zero_le_one
  · exact div_le_one_of_le₀ (Real.sum_mul_le_sqrt_mul_sqrt _ _ _) h.le

/-- A nonzero profile has cosine similarity 1 with itself. -/
theorem cosineSim_self (p : Grammar C) (inv : Finset C)
    (h : ∑ c ∈ inv, (p.freq c : ℝ) ^ 2 ≠ 0) : cosineSim p p inv = 1 := by
  unfold cosineSim
  rw [Real.mul_self_sqrt (Finset.sum_nonneg fun c _ => sq_nonneg _),
    Finset.sum_congr rfl fun c (_ : c ∈ inv) => (pow_two ((p.freq c : ℝ))).symm]
  exact div_self h

/-- Cosine distance: the dissimilarity the Element's pipeline standardizes
and ranks. -/
noncomputable def cosineDist (p q : Grammar C) (inv : Finset C) : ℝ :=
  1 - cosineSim p q inv

/-- A nonzero profile is at distance 0 from itself. -/
theorem cosineDist_self (p : Grammar C) (inv : Finset C)
    (h : ∑ c ∈ inv, (p.freq c : ℝ) ^ 2 ≠ 0) : cosineDist p p inv = 0 := by
  rw [cosineDist, cosineSim_self p inv h, sub_self]

theorem cosineDist_nonneg (p q : Grammar C) (inv : Finset C) :
    0 ≤ cosineDist p q inv :=
  sub_nonneg.mpr (cosineSim_le_one p q inv)

theorem cosineDist_le_one (p q : Grammar C) (inv : Finset C) :
    cosineDist p q inv ≤ 1 := by
  have := cosineSim_nonneg p q inv
  unfold cosineDist
  linarith

end Grammar

end Dunn2025
