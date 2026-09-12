import Linglib.Pragmatics.RSA.Uniform
import Linglib.Core.Probability.Kernel.Mixture
import Mathlib.Data.NNRat.BigOperators
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Data.Rat.Cast.Order

/-!
# Potts and Levy (2015): Negotiating Lexical Uncertainty and Speaker Expertise with Disjunction

This file formalizes the lexical-uncertainty model of [potts-levy-2015] and its Hurfordian
context. Disjunctions *A or X* whose disjunct *X* covers *A* violate the generalization of
[hurford-1974] yet are used, and the listener who hears one infers both that the speaker is
uncertain between the disjuncts and that her lexicon keeps them apart. The model is a
rational-speech-acts tower over states, messages, and lexica (§3). A literal listener conditions
a flat prior on a message's extension under a lexicon (10), a speaker chooses messages by the
listener's mass at the state under a rationality and a cost (11), and a pragmatic listener
inverts the speaker (12) (`L0`, `S1`, `l1`); the lexical-uncertainty listener infers state and
lexicon jointly (14) (`L1`), the expertise speaker weighs the world information and the lexicon
information a message carries (15) (`S2`), the next listener inverts her (`L2`), and
marginalization recovers simple signaling (16), (17) (`S2exp`). The state space is closed under
joins so that a disjunction can convey uncertainty, a join state satisfying a message when all
its atoms do (§4, Figure 6), and the lexica refine the unknown term *X* (13) (`World`, `Msg`,
`Lex`, `sem`). In the Hurfordian context of §5.2, three atoms, the terms *A*, *B*, *X* with their
disjunctions, and the lexica reading *X* as the general term, its exclusivization, or the
synonym of *A*, at α = 2, β = 1 and a disjunction cost of 1 (Figure 10): the listener hearing
*A or X* ranks the uncertain state first and the exclusivized lexicon first at both levels
(`l1_uncertainty`, `l1_lexicon`, `l2_uncertainty`, `l2_lexicon`), the exclusivizing speaker uses
the disjunction exactly when uncertain (`s1_disjunction_iff_uncertain`), the disjunction
signals exclusivization where the bare disjunct does not (`AorX_signals_excl`), and the
expertise speaker who is uncertain and exclusivizes prefers the disjunction to every other
message, the paper's production claim for this context (`s2_prefers_disjunction`,
`s2exp_disjunction_iff_uncertain`).

## Implementation notes

The agents are kernels of `Pragmatics/RSA`, the speakers power-weight kernels and the
listeners Bayesian inverses against uniform priors; the expertise speaker is a weight kernel
built from the fixed-lexicon listener and the lexicon posterior, the rationality inside the
weights. The cost factor `exp (−1)` of the disjunctions is rationalized as `37/100`, and every
prediction is certified by an exact rational computation of the tower (`s1q` to `s2expq`),
each kernel value shown equal to its rational counterpart. The definitional regime of §5.1,
which needs β > α, and the parameter exploration of §5.4 are not formalized.

## References

* [potts-levy-2015]
* [hurford-1974]
-/

open MeasureTheory ProbabilityTheory RSA
open scoped ENNReal NNReal NNRat

namespace PottsLevy2015

/-! ### The domain (§4, §5) -/

/-- The three atomic states of the context. -/
inductive Atom where
  | w₁
  | w₂
  | w₃
  deriving DecidableEq, Fintype

/-- The states: the nonempty joins of the atoms (Figure 6). -/
inductive World where
  | w₁
  | w₂
  | w₃
  | w₁₂
  | w₁₃
  | w₂₃
  | w₁₂₃
  deriving DecidableEq, Fintype, Nonempty

instance : MeasurableSpace World := ⊤

/-- The atoms a state joins. -/
def World.atoms : World → Finset Atom
  | .w₁ => {.w₁}
  | .w₂ => {.w₂}
  | .w₃ => {.w₃}
  | .w₁₂ => {.w₁, .w₂}
  | .w₁₃ => {.w₁, .w₃}
  | .w₂₃ => {.w₂, .w₃}
  | .w₁₂₃ => {.w₁, .w₂, .w₃}

/-- The messages: the basic terms, their disjunctions, and the null message. -/
inductive Msg where
  | A
  | B
  | X
  | AorB
  | AorX
  | BorX
  | AorBorX
  | null
  deriving DecidableEq, Fintype, Nonempty

instance : MeasurableSpace Msg := ⊤

/-- Whether a message is a disjunction, the messages that carry a cost. -/
def Msg.IsDisjunction : Msg → Prop
  | .AorB | .AorX | .BorX | .AorBorX => True
  | _ => False

instance : DecidablePred Msg.IsDisjunction := λ m => by
  cases m <;> unfold Msg.IsDisjunction <;> infer_instance

/-- The lexica (13): the base lexicon reading *X* as the general term over the first two atoms,
its exclusivization to the second atom, and the synonym of *A*. -/
inductive Lex where
  | base
  | excl
  | syn
  deriving DecidableEq, Fintype, Nonempty

instance : MeasurableSpace Lex := ⊤

/-- The atoms *X* denotes under a lexicon. -/
def Lex.x : Lex → Finset Atom
  | .base => {.w₁, .w₂}
  | .excl => {.w₂}
  | .syn => {.w₁}

/-- The atoms a message denotes under a lexicon: *A* the first atom, *B* the second,
disjunction union, and the null message everything. -/
def atomDen (l : Lex) : Msg → Finset Atom
  | .A => {.w₁}
  | .B => {.w₂}
  | .X => l.x
  | .AorB => {.w₁, .w₂}
  | .AorX => {.w₁} ∪ l.x
  | .BorX => {.w₂} ∪ l.x
  | .AorBorX => {.w₁, .w₂} ∪ l.x
  | .null => Finset.univ

/-- The extension of a message in the join-closed state space: the states all of whose atoms
the message denotes. -/
def sem (l : Lex) (m : Msg) : Finset World :=
  Finset.univ.filter λ w => w.atoms ⊆ atomDen l m

/-- Under the exclusivized lexicon *A* and *X* are disjoint, the Hurford rescue; under the
synonym lexicon *A or X* is *A*, the Hurford violation; and under the exclusivized lexicon the
uncertain state satisfies exactly the disjunctions containing *A* and the null message. -/
theorem lexica_facts :
    Disjoint (atomDen .excl .A) (atomDen .excl .X) ∧ atomDen .syn .AorX = atomDen .syn .A ∧
      (∀ m, World.w₁₂ ∈ sem .excl m ↔ m = .AorX ∨ m = .AorB ∨ m = .AorBorX ∨ m = .null) := by
  decide

instance : IsProbabilityMeasure (uniformOn (Set.univ : Set World)) :=
  isProbabilityMeasure_uniformOn Set.finite_univ Set.univ_nonempty

instance : IsProbabilityMeasure (uniformOn (Set.univ : Set (World × Lex))) :=
  isProbabilityMeasure_uniformOn Set.finite_univ Set.univ_nonempty

/-! ### The tower (§3) -/

section Tower

variable (κ : ℝ≥0∞)

/-- The cost factor of a message: `κ` for a disjunction and 1 otherwise. -/
def cost (m : Msg) : ℝ≥0∞ := if m.IsDisjunction then κ else 1

/-- The literal listener (10) at a flat prior: uniform on the message's extension. -/
noncomputable def L0 (l : Lex) : Kernel Msg World := uniformListener (sem l)

/-- The speaker (11) at α = 2: the substrate's power-weight speaker. -/
noncomputable def S1 (l : Lex) : Kernel World Msg := speaker 2 (cost κ) (L0 l)

instance (l : Lex) : IsFiniteKernel (S1 κ l) := inferInstanceAs (IsFiniteKernel (speaker _ _ _))

/-- The fixed-lexicon pragmatic listener (12): the speaker's Bayesian inverse at a flat prior. -/
noncomputable def l1 (l : Lex) : Kernel Msg World := (S1 κ l)†(uniformOn Set.univ)

/-- The lexical-uncertainty listener (14) at k = 1: the joint posterior over states and lexica
against a flat prior, the substrate's family listener. -/
noncomputable def L1 : Kernel Msg (World × Lex) :=
  familyListener L0 2 (cost κ) (uniformOn Set.univ)

/-- The expertise speaker (15) at k = 2, α = 2 and β = 1: weights the square of the
fixed-lexicon listener's mass at the state by the lexicon posterior and the cost. -/
noncomputable def S2 : Kernel (World × Lex) Msg :=
  Kernel.ofWeights λ p m => l1 κ p.2 m {p.1} ^ 2 * (L1 κ m).snd {p.2} * cost κ m

instance : IsFiniteKernel (S2 κ) := inferInstanceAs (IsFiniteKernel (Kernel.ofWeights _))

/-- The lexical-uncertainty listener (14) at k = 2. -/
noncomputable def L2 : Kernel Msg (World × Lex) := (S2 κ)†(uniformOn Set.univ)

/-- The marginal expertise speaker (17) at a flat lexicon prior. -/
noncomputable def S2exp : Kernel World Msg :=
  Kernel.mixture (λ _ : Lex => 3⁻¹) λ l => (S2 κ).comap (·, l) (measurable_of_countable _)

end Tower

/-! ### The rational face -/

/-- Normalization of a rational score over a finite type. -/
def normalize {σ : Type*} [Fintype σ] (f : σ → ℚ≥0) (x : σ) : ℚ≥0 := f x / ∑ y, f y

/-- The rational cost factor. -/
def costq (κ : ℚ≥0) (m : Msg) : ℚ≥0 := if m.IsDisjunction then κ else 1

/-- The literal listener's mass. -/
def l0q (l : Lex) (m : Msg) (w : World) : ℚ≥0 :=
  if w ∈ sem l m then ((sem l m).card : ℚ≥0)⁻¹ else 0

/-- The speaker's shares. -/
def s1q (κ : ℚ≥0) (l : Lex) (w : World) : Msg → ℚ≥0 :=
  normalize λ m => l0q l m w ^ 2 * costq κ m

/-- The fixed-lexicon listener's masses. -/
def l1q (κ : ℚ≥0) (l : Lex) (m : Msg) : World → ℚ≥0 := normalize λ w => s1q κ l w m

/-- The joint listener's masses. -/
def L1q (κ : ℚ≥0) (m : Msg) : World × Lex → ℚ≥0 := normalize λ p => s1q κ p.2 p.1 m

/-- The lexicon posterior. -/
def L1latq (κ : ℚ≥0) (m : Msg) (l : Lex) : ℚ≥0 := ∑ w, L1q κ m (w, l)

/-- The state posterior. -/
def L1worldq (κ : ℚ≥0) (m : Msg) (w : World) : ℚ≥0 := ∑ l, L1q κ m (w, l)

/-- The expertise speaker's shares. -/
def s2q (κ : ℚ≥0) (p : World × Lex) : Msg → ℚ≥0 :=
  normalize λ m => l1q κ p.2 m p.1 ^ 2 * L1latq κ m p.2 * costq κ m

/-- The level-two joint listener's masses. -/
def L2q (κ : ℚ≥0) (m : Msg) : World × Lex → ℚ≥0 := normalize λ p => s2q κ p m

/-- The level-two lexicon posterior. -/
def L2latq (κ : ℚ≥0) (m : Msg) (l : Lex) : ℚ≥0 := ∑ w, L2q κ m (w, l)

/-- The level-two state posterior. -/
def L2worldq (κ : ℚ≥0) (m : Msg) (w : World) : ℚ≥0 := ∑ l, L2q κ m (w, l)

/-- The marginal expertise speaker's shares. -/
def s2expq (κ : ℚ≥0) (w : World) (m : Msg) : ℚ≥0 := (∑ l, s2q κ (w, l) m) / 3

/-- The rationalized disjunction cost, `exp (−1)` to two places. -/
abbrev κ₀ : ℚ≥0 := 37 / 100

/-- The cost factor at the rationalized cost. -/
abbrev K : ℝ≥0∞ := ((κ₀ : ℝ≥0) : ℝ≥0∞)

/-! ### Each kernel value is its rational counterpart -/

private theorem s1_weight_ne_zero (l : Lex) (w : World) :
    ∑ m, l0q l m w ^ 2 * costq κ₀ m ≠ 0 := by
  revert l w; decide +kernel

private theorem s1q_sum_ne_zero (l : Lex) (m : Msg) : ∑ w, s1q κ₀ l w m ≠ 0 := by
  revert l m; decide +kernel

private theorem s1q_joint_sum_ne_zero (m : Msg) : ∑ p : World × Lex, s1q κ₀ p.2 p.1 m ≠ 0 := by
  revert m; decide +kernel

private theorem s2_weight_ne_zero (p : World × Lex) :
    ∑ m, l1q κ₀ p.2 m p.1 ^ 2 * L1latq κ₀ m p.2 * costq κ₀ m ≠ 0 := by
  revert p; decide +kernel

private theorem s2q_sum_ne_zero (m : Msg) : ∑ p : World × Lex, s2q κ₀ p m ≠ 0 := by
  revert m; decide +kernel

/-- The cast of a normalized rational score. -/
theorem coe_normalize {σ : Type*} [Fintype σ] (f : σ → ℚ≥0) (h : ∑ y, f y ≠ 0) (x : σ) :
    ((f x : ℝ≥0) : ℝ≥0∞) / ∑ y, ((f y : ℝ≥0) : ℝ≥0∞) = ((normalize f x : ℝ≥0) : ℝ≥0∞) := by
  rw [normalize, NNRat.cast_div, ENNReal.coe_div (NNRat.cast_ne_zero.2 h), NNRat.cast_sum,
    ENNReal.ofNNReal_finsetSum]

/-- A weight kernel with rational weights has rational rows. -/
theorem ofWeights_coe {α β : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [Fintype β] [MeasurableSingletonClass β] (q : α → β → ℚ≥0) (a : α)
    (h : ∑ b, q a b ≠ 0) (b : β) :
    Kernel.ofWeights (λ a b => ((q a b : ℝ≥0) : ℝ≥0∞)) a {b} =
      ((normalize (q a) b : ℝ≥0) : ℝ≥0∞) := by
  rw [Kernel.ofWeights_apply_singleton]
  exact coe_normalize (q a) h b

theorem cost_coe (κ : ℚ≥0) (m : Msg) :
    cost ((κ : ℝ≥0) : ℝ≥0∞) m = ((costq κ m : ℝ≥0) : ℝ≥0∞) := by
  unfold cost costq
  split_ifs <;> simp

theorem L0_apply (l : Lex) (m : Msg) (w : World) : L0 l m {w} = ((l0q l m w : ℝ≥0) : ℝ≥0∞) := by
  rw [L0, uniformListener_apply_singleton, l0q]
  split_ifs with h
  · rw [NNRat.cast_inv, NNRat.cast_natCast,
      ENNReal.coe_inv (by exact_mod_cast (Finset.card_pos.2 ⟨w, h⟩).ne'), ENNReal.coe_natCast]
  · simp

theorem S1_apply (l : Lex) (w : World) (m : Msg) :
    S1 K l w {m} = ((s1q κ₀ l w m : ℝ≥0) : ℝ≥0∞) := by
  have hw : (λ w u => L0 l u {w} ^ (2 : ℝ) * cost K u) =
      λ w u => (((l0q l u w ^ 2 * costq κ₀ u : ℚ≥0) : ℝ≥0) : ℝ≥0∞) := by
    funext w u
    rw [L0_apply, cost_coe, ENNReal.rpow_two]
    norm_cast
  rw [S1, speaker, hw]
  exact ofWeights_coe (λ w u => l0q l u w ^ 2 * costq κ₀ u) w (s1_weight_ne_zero l w) m

theorem l1_apply (l : Lex) (m : Msg) (w : World) :
    l1 K l m {w} = ((l1q κ₀ l m w : ℝ≥0) : ℝ≥0∞) := by
  have hx : ∑ w', S1 K l w' {m} ≠ 0 := by
    simp only [S1_apply]
    rw [← ENNReal.ofNNReal_finsetSum, ← NNRat.cast_sum]
    exact_mod_cast s1q_sum_ne_zero l m
  rw [l1, posterior_uniformOn_univ_apply_singleton _ hx w]
  simp only [S1_apply]
  exact coe_normalize (λ w => s1q κ₀ l w m) (s1q_sum_ne_zero l m) w

theorem L1_apply (m : Msg) (p : World × Lex) : L1 K m {p} = ((L1q κ₀ m p : ℝ≥0) : ℝ≥0∞) := by
  have hs : ∀ p : World × Lex,
      familySpeaker L0 2 (cost K) p {m} = ((s1q κ₀ p.2 p.1 m : ℝ≥0) : ℝ≥0∞) := λ p => by
    rw [familySpeaker_apply]
    exact S1_apply p.2 p.1 m
  have hx : ∑ p : World × Lex, familySpeaker L0 2 (cost K) p {m} ≠ 0 := by
    simp only [hs]
    rw [← ENNReal.ofNNReal_finsetSum, ← NNRat.cast_sum]
    exact_mod_cast s1q_joint_sum_ne_zero m
  rw [L1, familyListener, posterior_uniformOn_univ_apply_singleton _ hx p]
  simp only [hs]
  exact coe_normalize (λ p : World × Lex => s1q κ₀ p.2 p.1 m) (s1q_joint_sum_ne_zero m) p

theorem L1_snd_apply (m : Msg) (l : Lex) :
    (L1 K m).snd {l} = ((L1latq κ₀ m l : ℝ≥0) : ℝ≥0∞) := by
  rw [Measure.snd_apply_singleton, L1latq, NNRat.cast_sum, ENNReal.ofNNReal_finsetSum]
  exact Finset.sum_congr rfl λ w _ => L1_apply m (w, l)

theorem L1_fst_apply (m : Msg) (w : World) :
    (L1 K m).fst {w} = ((L1worldq κ₀ m w : ℝ≥0) : ℝ≥0∞) := by
  rw [Measure.fst_apply_singleton, L1worldq, NNRat.cast_sum, ENNReal.ofNNReal_finsetSum]
  exact Finset.sum_congr rfl λ l _ => L1_apply m (w, l)

theorem S2_apply (p : World × Lex) (m : Msg) : S2 K p {m} = ((s2q κ₀ p m : ℝ≥0) : ℝ≥0∞) := by
  have hw : (λ (p : World × Lex) m => l1 K p.2 m {p.1} ^ 2 * (L1 K m).snd {p.2} * cost K m) =
      λ p m => (((l1q κ₀ p.2 m p.1 ^ 2 * L1latq κ₀ m p.2 * costq κ₀ m : ℚ≥0) : ℝ≥0) : ℝ≥0∞) := by
    funext p m
    rw [l1_apply, L1_snd_apply, cost_coe]
    norm_cast
  rw [S2, hw]
  exact ofWeights_coe (λ (p : World × Lex) m => l1q κ₀ p.2 m p.1 ^ 2 * L1latq κ₀ m p.2 * costq κ₀ m)
    p (s2_weight_ne_zero p) m

theorem L2_apply (m : Msg) (p : World × Lex) : L2 K m {p} = ((L2q κ₀ m p : ℝ≥0) : ℝ≥0∞) := by
  have hx : ∑ p : World × Lex, S2 K p {m} ≠ 0 := by
    simp only [S2_apply]
    rw [← ENNReal.ofNNReal_finsetSum, ← NNRat.cast_sum]
    exact_mod_cast s2q_sum_ne_zero m
  rw [L2, posterior_uniformOn_univ_apply_singleton _ hx p]
  simp only [S2_apply]
  exact coe_normalize (λ p : World × Lex => s2q κ₀ p m) (s2q_sum_ne_zero m) p

theorem L2_snd_apply (m : Msg) (l : Lex) :
    (L2 K m).snd {l} = ((L2latq κ₀ m l : ℝ≥0) : ℝ≥0∞) := by
  rw [Measure.snd_apply_singleton, L2latq, NNRat.cast_sum, ENNReal.ofNNReal_finsetSum]
  exact Finset.sum_congr rfl λ w _ => L2_apply m (w, l)

theorem L2_fst_apply (m : Msg) (w : World) :
    (L2 K m).fst {w} = ((L2worldq κ₀ m w : ℝ≥0) : ℝ≥0∞) := by
  rw [Measure.fst_apply_singleton, L2worldq, NNRat.cast_sum, ENNReal.ofNNReal_finsetSum]
  exact Finset.sum_congr rfl λ l _ => L2_apply m (w, l)

theorem S2exp_apply (w : World) (m : Msg) : S2exp K w {m} = ((s2expq κ₀ w m : ℝ≥0) : ℝ≥0∞) := by
  rw [S2exp, Kernel.mixture_apply']
  simp only [Kernel.comap_apply', S2_apply]
  rw [s2expq, NNRat.cast_div, NNRat.cast_sum, NNRat.cast_ofNat, ENNReal.coe_div three_ne_zero,
    ENNReal.ofNNReal_finsetSum, ENNReal.coe_ofNat, div_eq_mul_inv, Finset.sum_mul]
  exact Finset.sum_congr rfl λ l _ => mul_comm _ _

/-! ### The Hurfordian context (§5.2, Figure 10) -/

private theorem real_lt {x y : ℚ≥0} (h : x < y) :
    ((x : ℝ≥0) : ℝ≥0∞).toReal < ((y : ℝ≥0) : ℝ≥0∞).toReal := by
  rw [ENNReal.coe_toReal, ENNReal.coe_toReal]
  exact NNReal.coe_lt_coe.2 (NNRat.cast_lt.2 h)

/-- The ignorance implicature: hearing *A or X*, the lexical-uncertainty listener ranks the
uncertain state above the first atom and that above the second. -/
theorem l1_uncertainty :
    (L1 K .AorX).fst.real {.w₂} < (L1 K .AorX).fst.real {.w₁} ∧
      (L1 K .AorX).fst.real {.w₁} < (L1 K .AorX).fst.real {.w₁₂} := by
  simp only [measureReal_def, L1_fst_apply]
  exact ⟨real_lt (by decide +kernel), real_lt (by decide +kernel)⟩

/-- The Hurford rescue: hearing *A or X*, the listener ranks the exclusivized lexicon above the
base lexicon and that above the synonym lexicon. -/
theorem l1_lexicon :
    (L1 K .AorX).snd.real {.syn} < (L1 K .AorX).snd.real {.base} ∧
      (L1 K .AorX).snd.real {.base} < (L1 K .AorX).snd.real {.excl} := by
  simp only [measureReal_def, L1_snd_apply]
  exact ⟨real_lt (by decide +kernel), real_lt (by decide +kernel)⟩

/-- The exclusivizing speaker uses the disjunction exactly when uncertain: at the uncertain
state it beats both bare disjuncts, while knowing the first atom the bare *A* wins. -/
theorem s1_disjunction_iff_uncertain :
    (S1 K .excl .w₁₂).real {.A} < (S1 K .excl .w₁₂).real {.AorX} ∧
      (S1 K .excl .w₁₂).real {.X} < (S1 K .excl .w₁₂).real {.AorX} ∧
      (S1 K .excl .w₁).real {.AorX} < (S1 K .excl .w₁).real {.A} := by
  simp only [measureReal_def, S1_apply]
  exact ⟨real_lt (by decide +kernel), real_lt (by decide +kernel), real_lt (by decide +kernel)⟩

/-- The expertise component: *A or X* signals the exclusivized lexicon more strongly than the
bare *A* does, which every lexicon reads alike. -/
theorem AorX_signals_excl : (L1 K .A).snd.real {.excl} < (L1 K .AorX).snd.real {.excl} := by
  simp only [measureReal_def, L1_snd_apply]
  exact real_lt (by decide +kernel)

/-- At the second level the listener hearing *A or X* again ranks the uncertain state first. -/
theorem l2_uncertainty :
    (L2 K .AorX).fst.real {.w₂} < (L2 K .AorX).fst.real {.w₁} ∧
      (L2 K .AorX).fst.real {.w₁} < (L2 K .AorX).fst.real {.w₁₂} := by
  simp only [measureReal_def, L2_fst_apply]
  exact ⟨real_lt (by decide +kernel), real_lt (by decide +kernel)⟩

/-- At the second level the listener hearing *A or X* again ranks the exclusivized lexicon
first. -/
theorem l2_lexicon :
    (L2 K .AorX).snd.real {.syn} < (L2 K .AorX).snd.real {.base} ∧
      (L2 K .AorX).snd.real {.base} < (L2 K .AorX).snd.real {.excl} := by
  simp only [measureReal_def, L2_snd_apply]
  exact ⟨real_lt (by decide +kernel), real_lt (by decide +kernel)⟩

/-- The paper's production claim for the context: the expertise speaker who observes the
uncertain state with the exclusivized lexicon prefers *A or X* to every other message. -/
theorem s2_prefers_disjunction (m : Msg) (hm : m ≠ .AorX) :
    (S2 K (.w₁₂, .excl)).real {m} < (S2 K (.w₁₂, .excl)).real {.AorX} := by
  simp only [measureReal_def, S2_apply]
  exact real_lt (by revert m; decide +kernel)

/-- The marginal expertise speaker uses the disjunction exactly when uncertain. -/
theorem s2exp_disjunction_iff_uncertain :
    (S2exp K .w₁₂).real {.A} < (S2exp K .w₁₂).real {.AorX} ∧
      (S2exp K .w₁).real {.AorX} < (S2exp K .w₁).real {.A} := by
  simp only [measureReal_def, S2exp_apply]
  exact ⟨real_lt (by decide +kernel), real_lt (by decide +kernel)⟩

end PottsLevy2015
