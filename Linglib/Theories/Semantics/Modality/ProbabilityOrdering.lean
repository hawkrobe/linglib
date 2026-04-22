import Linglib.Theories.Semantics.Modality.Kratzer.Operators
import Linglib.Theories.Semantics.Attitudes.Intensional
import Mathlib.Data.Fintype.Basic

/-!
# Probability-Ordering Bridge — @cite{kratzer-2012}

Connects probability assignments to Kratzer ordering sources.

A probability assignment P over worlds induces an ordering source where
more probable worlds are ranked higher. For each world v, the ordering
source generates the proposition "at least as probable as v":
  λ w => P(w) ≥ P(v)

This means w ≥_A z iff every probability threshold that z meets, w also meets,
which reduces to P(w) ≥ P(z).

## Key result

When the probability assignment is uniform, the induced ordering is trivial
(all worlds equivalent). When skewed, the best worlds are those with
maximal probability.

UNVERIFIED reference: Kratzer (2012) Modals and Conditionals, OUP — chapter
and section number not checked against the original.
-/

namespace Semantics.Modality.ProbabilityOrdering

open Semantics.Modality.Kratzer

/-! ## Polymorphic core -/

/-- A probability assignment maps worlds to rational probabilities. -/
abbrev ProbAssignment (W : Type*) := W → ℚ

/-- Convert a probability assignment to a Kratzer ordering source over a
    finite world type.

    For each world v in `Finset.univ`, generate the proposition "at least
    as probable as v": w satisfies this iff P(w) ≥ P(v). The resulting
    ordering ranks worlds by probability: w ≥_A z iff P(w) ≥ P(z). -/
def probToOrdering {W : Type*} [Fintype W] (prob : ProbAssignment W) :
    OrderingSource W := fun _ =>
  (Finset.univ : Finset W).toList.map fun v => fun w => prob w ≥ prob v

/-- `probToOrdering` is world-independent: the ordering source is the
    same regardless of which evaluation world is chosen. -/
theorem probToOrdering_const {W : Type*} [Fintype W] (prob : ProbAssignment W)
    (w w' : W) :
    probToOrdering prob w = probToOrdering prob w' :=
  rfl

/-- Convenience reducer: ordering relation reduces to probability comparison
    via transitivity over the threshold propositions. If `prob w₁ ≥ prob w₂`
    then `w₁ ≥_(probToOrdering prob w) w₂`. -/
lemma higher_prob_dominates {W : Type*} [Fintype W]
    {prob : ProbAssignment W} {w1 w2 wEval : W}
    (hOrd : prob w1 ≥ prob w2) :
    atLeastAsGoodAs ((probToOrdering prob) wEval) w1 w2 := by
  intro p hp
  rw [probToOrdering, List.mem_map] at hp
  obtain ⟨v, _, rfl⟩ := hp
  intro h
  exact le_trans h hOrd

/-- **Uniform probability makes all worlds equivalent under the ordering.** -/
theorem uniform_all_equivalent {W : Type*} [Fintype W] [Inhabited W]
    (c : ℚ) (w z wEval : W) :
    atLeastAsGoodAs ((probToOrdering (fun _ : W => c)) wEval) w z :=
  higher_prob_dominates (le_refl _)

/-! ## Concrete World-specific examples

These examples instantiate the polymorphic core at `Attitudes.Intensional.World`
(the toy 4-world type) for direct demonstration. -/

open Semantics.Attitudes.Intensional (World allWorlds)

/-- A skewed probability assignment: P(w0) > P(w1) > P(w2) > P(w3). -/
def skewedProb : ProbAssignment World := λ w =>
  match w with | .w0 => 4/10 | .w1 => 3/10 | .w2 => 2/10 | .w3 => 1/10

/-- A uniform probability assignment: P(w) = 1/4 for all w. -/
def uniformProb : ProbAssignment World := λ _ => 1/4

private lemma w0_mem_univ_toList :
    (.w0 : World) ∈ (Finset.univ : Finset World).toList := by
  simp

/-- **Under skewed P, best worlds (from universal base) = {w0}.**
    w0 has the highest probability and dominates all others. -/
theorem prob_ordering_best_w0 (w : World) :
    bestWorlds emptyBackground (probToOrdering skewedProb) w = ({.w0} : Set World) := by
  ext w'
  rw [bestWorlds, Set.mem_setOf_eq, Set.mem_singleton_iff]
  refine ⟨?_, ?_⟩
  · rintro ⟨_, hAll⟩
    have hUniv : (.w0 : World) ∈ accessibleWorlds emptyBackground w := by
      rw [empty_base_universal_access]; exact Set.mem_univ _
    have hLeq := hAll _ hUniv
    have hp_mem : (λ x => skewedProb x ≥ skewedProb (.w0 : World))
        ∈ probToOrdering skewedProb w := by
      rw [probToOrdering, List.mem_map]
      exact ⟨.w0, w0_mem_univ_toList, rfl⟩
    have h_w' : skewedProb w' ≥ skewedProb (.w0 : World) :=
      hLeq _ hp_mem (le_refl _)
    cases w' with
    | w0 => rfl
    | w1 => simp [skewedProb] at h_w'; norm_num at h_w'
    | w2 => simp [skewedProb] at h_w'; norm_num at h_w'
    | w3 => simp [skewedProb] at h_w'; norm_num at h_w'
  · rintro rfl
    refine ⟨?_, ?_⟩
    · rw [empty_base_universal_access]; exact Set.mem_univ _
    · intro w'' _
      apply higher_prob_dominates
      cases w'' <;> simp [skewedProb] <;> norm_num

/-- **Probability ordering preserves ranking**: w0 ≥ w1 ≥ w2 ≥ w3. -/
theorem prob_ordering_w0_ge_w1 :
    atLeastAsGoodAs ((probToOrdering skewedProb) .w0) .w0 .w1 :=
  higher_prob_dominates (by show (3 : ℚ) / 10 ≤ 4 / 10; norm_num)

theorem prob_ordering_w1_ge_w2 :
    atLeastAsGoodAs ((probToOrdering skewedProb) .w0) .w1 .w2 :=
  higher_prob_dominates (by show (2 : ℚ) / 10 ≤ 3 / 10; norm_num)

theorem prob_ordering_w2_ge_w3 :
    atLeastAsGoodAs ((probToOrdering skewedProb) .w0) .w2 .w3 :=
  higher_prob_dominates (by show (1 : ℚ) / 10 ≤ 2 / 10; norm_num)

/-- **Strict ordering**: w0 > w1 (w0 beats w1 but not vice versa). -/
theorem prob_ordering_w0_strict_w1 :
    strictlyBetter ((probToOrdering skewedProb) .w0) .w0 .w1 := by
  refine ⟨prob_ordering_w0_ge_w1, ?_⟩
  intro h
  have hp_mem : (λ x => skewedProb x ≥ skewedProb (.w0 : World))
      ∈ probToOrdering skewedProb .w0 := by
    rw [probToOrdering, List.mem_map]
    exact ⟨.w0, w0_mem_univ_toList, rfl⟩
  have hp1 : skewedProb (.w1 : World) ≥ skewedProb (.w0 : World) :=
    h _ hp_mem (le_refl _)
  simp [skewedProb] at hp1
  norm_num at hp1

/-- **Necessity under probability ordering**: with skewed P and universal base,
    any proposition true at w0 is necessary (since best = {w0}). -/
theorem prob_necessity_at_best (p : World → Prop) (w : World) (hp : p .w0) :
    necessity emptyBackground (probToOrdering skewedProb) p w := by
  rw [necessity_iff_all, prob_ordering_best_w0]
  intro w' hw'
  rw [Set.mem_singleton_iff.mp hw']
  exact hp

end Semantics.Modality.ProbabilityOrdering
