import Linglib.Pragmatics.RSA.Rational
import Linglib.Core.Probability.Kernel.Mixture

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
each kernel value shown equal to its rational counterpart through the register of
`Pragmatics/RSA/Rational`. The definitional regime of §5.1,
which needs β > α, and the parameter exploration of §5.4 are not formalized.

## References

* [potts-levy-2015]
* [hurford-1974]
-/

open MeasureTheory ProbabilityTheory RSA
open scoped ENNReal NNRat

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
noncomputable def l1 (l : Lex) : Kernel Msg World :=
  pragmaticListener 2 (cost κ) (L0 l) (uniformOn Set.univ)

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

/-- The rational cost factor. -/
def costq (κ : ℚ≥0) (m : Msg) : ℚ≥0 := if m.IsDisjunction then κ else 1

/-- The literal listener's mass. -/
def l0q (l : Lex) (m : Msg) (w : World) : ℚ≥0 :=
  if w ∈ sem l m then ((sem l m).card : ℚ≥0)⁻¹ else 0

/-- The speaker's shares. -/
def s1q (κ : ℚ≥0) (l : Lex) (w : World) : Msg → ℚ≥0 :=
  share λ m => l0q l m w ^ 2 * costq κ m

/-- The fixed-lexicon listener's masses. -/
def l1q (κ : ℚ≥0) (l : Lex) (m : Msg) : World → ℚ≥0 := share λ w => s1q κ l w m

/-- The joint listener's masses. -/
def L1q (κ : ℚ≥0) (m : Msg) : World × Lex → ℚ≥0 := share λ p => s1q κ p.2 p.1 m

/-- The lexicon posterior. -/
def L1latq (κ : ℚ≥0) (m : Msg) (l : Lex) : ℚ≥0 := ∑ w, L1q κ m (w, l)

/-- The state posterior. -/
def L1worldq (κ : ℚ≥0) (m : Msg) (w : World) : ℚ≥0 := ∑ l, L1q κ m (w, l)

/-- The expertise speaker's shares. -/
def s2q (κ : ℚ≥0) (p : World × Lex) : Msg → ℚ≥0 :=
  share λ m => l1q κ p.2 m p.1 ^ 2 * L1latq κ m p.2 * costq κ m

/-- The level-two joint listener's masses. -/
def L2q (κ : ℚ≥0) (m : Msg) : World × Lex → ℚ≥0 := share λ p => s2q κ p m

/-- The level-two lexicon posterior. -/
def L2latq (κ : ℚ≥0) (m : Msg) (l : Lex) : ℚ≥0 := ∑ w, L2q κ m (w, l)

/-- The level-two state posterior. -/
def L2worldq (κ : ℚ≥0) (m : Msg) (w : World) : ℚ≥0 := ∑ l, L2q κ m (w, l)

/-- The marginal expertise speaker's shares. -/
def s2expq (κ : ℚ≥0) (w : World) (m : Msg) : ℚ≥0 := (∑ l, s2q κ (w, l) m) / 3

/-- The rationalized disjunction cost, `exp (−1)` to two places. -/
abbrev κ₀ : ℚ≥0 := 37 / 100

/-- The cost factor at the rationalized cost. -/
abbrev K : ℝ≥0∞ := κ₀

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

theorem cost_coe (κ : ℚ≥0) (m : Msg) : cost κ m = (costq κ m : ℝ≥0∞) := by
  unfold cost costq
  split_ifs <;> simp

theorem L0_apply (l : Lex) (m : Msg) (w : World) : L0 l m {w} = (l0q l m w : ℝ≥0∞) :=
  uniformListener_nnratCast_apply_singleton (sem l) m w

theorem S1_apply (l : Lex) (w : World) (m : Msg) : S1 K l w {m} = (s1q κ₀ l w m : ℝ≥0∞) :=
  speaker_nnratCast_apply_singleton (by norm_num) (cost_coe κ₀) (L0_apply l)
    (s1_weight_ne_zero l w) m

theorem l1_apply (l : Lex) (m : Msg) (w : World) : l1 K l m {w} = (l1q κ₀ l m w : ℝ≥0∞) :=
  pragmaticListener_uniformOn_nnratCast_apply_singleton 2 (cost K) (L0 l) (S1_apply l)
    (s1q_sum_ne_zero l m) w

theorem L1_apply (m : Msg) (p : World × Lex) : L1 K m {p} = (L1q κ₀ m p : ℝ≥0∞) :=
  familyListener_uniformOn_nnratCast_apply_singleton L0 2 (cost K)
    (λ p m => S1_apply p.2 p.1 m) (s1q_joint_sum_ne_zero m) p

theorem L1_fst_apply (m : Msg) (w : World) : (L1 K m).fst {w} = (L1worldq κ₀ m w : ℝ≥0∞) :=
  familyListener_uniformOn_nnratCast_fst_apply_singleton L0 2 (cost K)
    (λ p m => S1_apply p.2 p.1 m) (s1q_joint_sum_ne_zero m) w

theorem L1_snd_apply (m : Msg) (l : Lex) : (L1 K m).snd {l} = (L1latq κ₀ m l : ℝ≥0∞) :=
  familyListener_uniformOn_nnratCast_snd_apply_singleton L0 2 (cost K)
    (λ p m => S1_apply p.2 p.1 m) (s1q_joint_sum_ne_zero m) l

theorem S2_apply (p : World × Lex) (m : Msg) : S2 K p {m} = (s2q κ₀ p m : ℝ≥0∞) := by
  have hw : (λ (p : World × Lex) m => l1 K p.2 m {p.1} ^ 2 * (L1 K m).snd {p.2} * cost K m)
      = λ p m => ((l1q κ₀ p.2 m p.1 ^ 2 * L1latq κ₀ m p.2 * costq κ₀ m : ℚ≥0) : ℝ≥0∞) := by
    funext p m
    rw [l1_apply, L1_snd_apply, cost_coe, ENNReal.nnratCast_mul, ENNReal.nnratCast_mul,
      ENNReal.nnratCast_pow]
  rw [S2, hw]
  exact Kernel.ofWeights_nnratCast_apply_singleton _ p (s2_weight_ne_zero p) m

theorem L2_apply (m : Msg) (p : World × Lex) : L2 K m {p} = (L2q κ₀ m p : ℝ≥0∞) :=
  posterior_uniformOn_univ_nnratCast_apply_singleton _ _ S2_apply (s2q_sum_ne_zero m) p

theorem L2_fst_apply (m : Msg) (w : World) : (L2 K m).fst {w} = (L2worldq κ₀ m w : ℝ≥0∞) := by
  rw [Measure.fst_apply_singleton, L2worldq, ENNReal.nnratCast_sum]
  exact Finset.sum_congr rfl λ l _ => L2_apply m (w, l)

theorem L2_snd_apply (m : Msg) (l : Lex) : (L2 K m).snd {l} = (L2latq κ₀ m l : ℝ≥0∞) := by
  rw [Measure.snd_apply_singleton, L2latq, ENNReal.nnratCast_sum]
  exact Finset.sum_congr rfl λ w _ => L2_apply m (w, l)

theorem S2exp_apply (w : World) (m : Msg) : S2exp K w {m} = (s2expq κ₀ w m : ℝ≥0∞) := by
  rw [S2exp, Kernel.mixture_apply']
  simp only [Kernel.comap_apply', S2_apply]
  rw [s2expq, ENNReal.nnratCast_div _ _ three_ne_zero, ENNReal.nnratCast_sum,
    ENNReal.nnratCast_ofNat, div_eq_mul_inv, Finset.sum_mul]
  exact Finset.sum_congr rfl λ l _ => mul_comm _ _

/-! ### The Hurfordian context (§5.2, Figure 10) -/

/-- The ignorance implicature: hearing *A or X*, the lexical-uncertainty listener ranks the
uncertain state above the first atom and that above the second. -/
theorem l1_uncertainty :
    (L1 K .AorX).fst.real {.w₂} < (L1 K .AorX).fst.real {.w₁} ∧
      (L1 K .AorX).fst.real {.w₁} < (L1 K .AorX).fst.real {.w₁₂} := by
  simp only [measureReal_def, L1_fst_apply, ENNReal.toReal_nnratCast]
  exact ⟨NNRat.cast_lt.2 (by decide +kernel), NNRat.cast_lt.2 (by decide +kernel)⟩

/-- The Hurford rescue: hearing *A or X*, the listener ranks the exclusivized lexicon above the
base lexicon and that above the synonym lexicon. -/
theorem l1_lexicon :
    (L1 K .AorX).snd.real {.syn} < (L1 K .AorX).snd.real {.base} ∧
      (L1 K .AorX).snd.real {.base} < (L1 K .AorX).snd.real {.excl} := by
  simp only [measureReal_def, L1_snd_apply, ENNReal.toReal_nnratCast]
  exact ⟨NNRat.cast_lt.2 (by decide +kernel), NNRat.cast_lt.2 (by decide +kernel)⟩

/-- The exclusivizing speaker uses the disjunction exactly when uncertain: at the uncertain
state it beats both bare disjuncts, while knowing the first atom the bare *A* wins. -/
theorem s1_disjunction_iff_uncertain :
    (S1 K .excl .w₁₂).real {.A} < (S1 K .excl .w₁₂).real {.AorX} ∧
      (S1 K .excl .w₁₂).real {.X} < (S1 K .excl .w₁₂).real {.AorX} ∧
      (S1 K .excl .w₁).real {.AorX} < (S1 K .excl .w₁).real {.A} := by
  simp only [measureReal_def, S1_apply, ENNReal.toReal_nnratCast]
  exact ⟨NNRat.cast_lt.2 (by decide +kernel), NNRat.cast_lt.2 (by decide +kernel),
    NNRat.cast_lt.2 (by decide +kernel)⟩

/-- The expertise component: *A or X* signals the exclusivized lexicon more strongly than the
bare *A* does, which every lexicon reads alike. -/
theorem AorX_signals_excl : (L1 K .A).snd.real {.excl} < (L1 K .AorX).snd.real {.excl} := by
  simp only [measureReal_def, L1_snd_apply, ENNReal.toReal_nnratCast]
  exact NNRat.cast_lt.2 (by decide +kernel)

/-- At the second level the listener hearing *A or X* again ranks the uncertain state first. -/
theorem l2_uncertainty :
    (L2 K .AorX).fst.real {.w₂} < (L2 K .AorX).fst.real {.w₁} ∧
      (L2 K .AorX).fst.real {.w₁} < (L2 K .AorX).fst.real {.w₁₂} := by
  simp only [measureReal_def, L2_fst_apply, ENNReal.toReal_nnratCast]
  exact ⟨NNRat.cast_lt.2 (by decide +kernel), NNRat.cast_lt.2 (by decide +kernel)⟩

/-- At the second level the listener hearing *A or X* again ranks the exclusivized lexicon
first. -/
theorem l2_lexicon :
    (L2 K .AorX).snd.real {.syn} < (L2 K .AorX).snd.real {.base} ∧
      (L2 K .AorX).snd.real {.base} < (L2 K .AorX).snd.real {.excl} := by
  simp only [measureReal_def, L2_snd_apply, ENNReal.toReal_nnratCast]
  exact ⟨NNRat.cast_lt.2 (by decide +kernel), NNRat.cast_lt.2 (by decide +kernel)⟩

/-- The paper's production claim for the context: the expertise speaker who observes the
uncertain state with the exclusivized lexicon prefers *A or X* to every other message. -/
theorem s2_prefers_disjunction (m : Msg) (hm : m ≠ .AorX) :
    (S2 K (.w₁₂, .excl)).real {m} < (S2 K (.w₁₂, .excl)).real {.AorX} := by
  simp only [measureReal_def, S2_apply, ENNReal.toReal_nnratCast]
  exact NNRat.cast_lt.2 (by revert m; decide +kernel)

/-- The marginal expertise speaker uses the disjunction exactly when uncertain. -/
theorem s2exp_disjunction_iff_uncertain :
    (S2exp K .w₁₂).real {.A} < (S2exp K .w₁₂).real {.AorX} ∧
      (S2exp K .w₁).real {.AorX} < (S2exp K .w₁).real {.A} := by
  simp only [measureReal_def, S2exp_apply, ENNReal.toReal_nnratCast]
  exact ⟨NNRat.cast_lt.2 (by decide +kernel), NNRat.cast_lt.2 (by decide +kernel)⟩

end PottsLevy2015
