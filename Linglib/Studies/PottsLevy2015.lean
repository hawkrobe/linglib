import Linglib.Pragmatics.RSA.Uniform
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
`Lex`, `sem`).

In the Hurfordian context of §5.2, three atoms, the terms *A*, *B*, *X* with their
disjunctions, and the lexica reading *X* as the general term, its exclusivization, or the
synonym of *A*, at the paper's rationality α = 2 and lexicon weight β = 1, with the disjunction
cost a free factor κ: the level-one listener hearing *A or X* ranks the uncertain state first
and the exclusivized lexicon first (`l1_uncertainty`, `l1_lexicon`), the exclusivizing speaker
uses the disjunction exactly when uncertain (`s1_disjunction_iff_uncertain`), the disjunction
signals exclusivization where the bare disjunct does not (`AorX_signals_excl`), and the
expertise speaker who is uncertain and exclusivizes prefers the disjunction to every other
message, the paper's production claim for this context (`s2_prefers_disjunction`,
`s2exp_uncertain`). Each ordering is stated on a range of disjunction costs containing the
paper's `exp (−1)`.

## Implementation notes

The agents are kernels of `Pragmatics/RSA`, the speakers power-weight kernels and the
listeners Bayesian inverses against uniform priors; the expertise speaker is a weight kernel
built from the fixed-lexicon listener and the lexicon posterior. Listener preferences reduce
to speaker preferences (`l1_real_lt_iff`, `L1_fst_real_lt_iff`, `S2_real_lt_iff`), and a
speaker's share is a rational function of the cost factor, so each ordering is a polynomial
inequality in κ certified by its Bernstein coefficients on the stated range. The definitional
regime of §5.1, which needs β > α, and the parameter exploration of §5.4 are not formalized.

## TODO

The level-two readings of Figure 10, the listener `L2` hearing *A or X* ranking the uncertain
state and the exclusivized lexicon first, and the marginal speaker `S2exp` preferring the bare
*A* when certain of the first atom, are rational inequalities in κ of very high degree whose
symbolic certificates are out of reach; the paper reports them numerically at κ = exp (−1).

## References

* [potts-levy-2015]
* [hurford-1974]
-/

open MeasureTheory ProbabilityTheory RSA
open scoped ENNReal NNReal

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

/-- Every message is true at some state under every lexicon. -/
theorem sem_nonempty (l : Lex) (m : Msg) : ∃ w, w ∈ sem l m := by
  revert l m; decide

/-- The extension sizes: seven states for the null message, three for a message denoting two
atoms, and one otherwise. -/
def semCard : Lex → Msg → ℕ
  | _, .null => 7
  | _, .AorB | _, .AorBorX | .base, .X | .base, .AorX | .base, .BorX | .excl, .AorX
  | .syn, .BorX => 3
  | _, _ => 1

theorem card_sem (l : Lex) (m : Msg) : (sem l m).card = semCard l m := by
  revert l m; decide

/-! ### The tower (§3) -/

section Tower

variable (α β : ℝ) (κ : ℝ≥0)

/-- The cost factor of a message: `κ` for a disjunction and 1 otherwise. -/
def cost (m : Msg) : ℝ≥0∞ := if m.IsDisjunction then κ else 1

/-- The literal listener (10) at a flat prior: uniform on the message's extension. -/
noncomputable def L0 (l : Lex) : Kernel Msg World := uniformListener (sem l)

/-- The speaker (11): the substrate's power-weight speaker. -/
noncomputable def S1 (l : Lex) : Kernel World Msg := speaker α (cost κ) (L0 l)

instance (l : Lex) : IsFiniteKernel (S1 α κ l) := inferInstanceAs (IsFiniteKernel (speaker _ _ _))

/-- The fixed-lexicon pragmatic listener (12): the speaker's Bayesian inverse at a flat prior. -/
noncomputable def l1 (l : Lex) : Kernel Msg World :=
  pragmaticListener α (cost κ) (L0 l) (uniformOn Set.univ)

instance (l : Lex) : IsMarkovKernel (l1 α κ l) :=
  inferInstanceAs (IsMarkovKernel (pragmaticListener _ _ _ _))

/-- The lexical-uncertainty listener (14) at k = 1: the joint posterior over states and lexica
against a flat prior, the substrate's family listener. -/
noncomputable def L1 : Kernel Msg (World × Lex) :=
  familyListener L0 α (cost κ) (uniformOn Set.univ)

instance : IsMarkovKernel (L1 α κ) :=
  inferInstanceAs (IsMarkovKernel ((familySpeaker L0 α (cost κ))†(uniformOn Set.univ)))

/-- The expertise speaker (15) at k = 2: weights the fixed-lexicon listener's mass at the state
to the rationality, the lexicon posterior to the lexicon weight, and the cost. -/
noncomputable def S2 : Kernel (World × Lex) Msg :=
  Kernel.ofWeights λ p m => l1 α κ p.2 m {p.1} ^ α * (L1 α κ m).snd {p.2} ^ β * cost κ m

instance : IsFiniteKernel (S2 α β κ) := inferInstanceAs (IsFiniteKernel (Kernel.ofWeights _))

/-- The lexical-uncertainty listener (14) at k = 2. -/
noncomputable def L2 : Kernel Msg (World × Lex) := (S2 α β κ)†(uniformOn Set.univ)

/-- The marginal expertise speaker (17) at a flat lexicon prior. -/
noncomputable def S2exp : Kernel World Msg :=
  Kernel.mixture (λ _ : Lex => 3⁻¹) λ l => (S2 α β κ).comap (·, l) (measurable_of_countable _)

end Tower

private theorem cost_ne_zero {κ : ℝ≥0} (hκ : κ ≠ 0) (m : Msg) : cost κ m ≠ 0 := by
  unfold cost; split_ifs <;> simp [hκ]

private theorem cost_ne_top (κ : ℝ≥0) (m : Msg) : cost κ m ≠ ∞ := by
  unfold cost; split_ifs <;> simp

/-! ### Support and preference reductions -/

section Model

variable {α : ℝ} (hα : 0 < α) {κ : ℝ≥0} (hκ : κ ≠ 0)
include hα hκ

/-- The speaker produces a message at a state exactly when it is true there. -/
theorem S1_ne_zero_iff (l : Lex) (w : World) (m : Msg) : S1 α κ l w {m} ≠ 0 ↔ w ∈ sem l m :=
  speaker_uniformListener_apply_singleton_ne_zero_iff (sem l) hα (cost_ne_zero hκ)
    (cost_ne_top κ) w m

/-- The fixed-lexicon listener assigns mass to a state exactly when the message is true
there. -/
theorem l1_ne_zero_iff (l : Lex) (m : Msg) (w : World) : l1 α κ l m {w} ≠ 0 ↔ w ∈ sem l m := by
  obtain ⟨w₀, h₀⟩ := sem_nonempty l m
  rw [show l1 α κ l = (S1 α κ l)†(uniformOn Set.univ) from rfl,
    posterior_apply_singleton_ne_zero_iff _ _
      (comp_apply_singleton_ne_zero _ _ (uniformOn_univ_singleton_ne_zero w₀)
        ((S1_ne_zero_iff hα hκ l w₀ m).2 h₀)),
    and_iff_right (uniformOn_univ_singleton_ne_zero w)]
  exact S1_ne_zero_iff hα hκ l w m

/-- The joint listener assigns mass to a state–lexicon pair exactly when the message is true
at the state under the lexicon. -/
theorem L1_ne_zero_iff (m : Msg) (p : World × Lex) : L1 α κ m {p} ≠ 0 ↔ p.1 ∈ sem p.2 m := by
  obtain ⟨w₀, h₀⟩ := sem_nonempty p.2 m
  rw [L1, familyListener, posterior_apply_singleton_ne_zero_iff _ _
    (comp_familySpeaker_ne_zero (uniformOn_univ_singleton_ne_zero (w₀, p.2))
      ((S1_ne_zero_iff hα hκ p.2 w₀ m).2 h₀)),
    and_iff_right (uniformOn_univ_singleton_ne_zero p), familySpeaker_apply]
  exact S1_ne_zero_iff hα hκ p.2 p.1 m

/-- Every lexicon keeps positive posterior mass under every message. -/
theorem L1_snd_ne_zero (m : Msg) (l : Lex) : (L1 α κ m).snd {l} ≠ 0 := by
  obtain ⟨w₀, h₀⟩ := sem_nonempty l m
  rw [Measure.snd_apply_singleton]
  exact λ h => (L1_ne_zero_iff hα hκ m (w₀, l)).2 h₀
    (Finset.sum_eq_zero_iff.1 h w₀ (Finset.mem_univ _))

/-- State preference of the fixed-lexicon listener is the speaker's preference. -/
theorem l1_real_lt_iff (l : Lex) (m : Msg) (v v' : World) :
    (l1 α κ l m).real {v} < (l1 α κ l m).real {v'} ↔
      (S1 α κ l v).real {m} < (S1 α κ l v').real {m} :=
  let ⟨w₀, h₀⟩ := sem_nonempty l m
  pragmaticListener_real_lt_iff α (cost κ) (L0 l) (uniformOn Set.univ)
    uniformOn_univ_singleton_eq uniformOn_univ_singleton_ne_zero
    ((S1_ne_zero_iff hα hκ l w₀ m).2 h₀)

/-- State preference of the joint listener is the pooled speaker preference. -/
theorem L1_fst_real_lt_iff (m : Msg) (v v' : World) :
    (L1 α κ m).fst.real {v} < (L1 α κ m).fst.real {v'} ↔
      ∑ l, (S1 α κ l v).real {m} < ∑ l, (S1 α κ l v').real {m} :=
  let ⟨w₀, h₀⟩ := sem_nonempty .base m
  familyListener_fst_real_lt_iff L0 uniformOn_univ_singleton_eq uniformOn_univ_singleton_ne_zero
    ((S1_ne_zero_iff hα hκ .base w₀ m).2 h₀)

/-- Lexicon preference of the joint listener is the speaker preference pooled over states. -/
theorem L1_snd_real_lt_iff (m : Msg) (l₁ l₂ : Lex) :
    (L1 α κ m).snd.real {l₁} < (L1 α κ m).snd.real {l₂} ↔
      ∑ w, (S1 α κ l₁ w).real {m} < ∑ w, (S1 α κ l₂ w).real {m} :=
  let ⟨w₀, h₀⟩ := sem_nonempty .base m
  familyListener_snd_real_lt_iff L0 uniformOn_univ_singleton_eq uniformOn_univ_singleton_ne_zero
    ((S1_ne_zero_iff hα hκ .base w₀ m).2 h₀)

/-- The fixed-lexicon listener's mass on reals: the speaker's share of the message at the
state over its shares at every state. -/
theorem l1_real (l : Lex) (m : Msg) (w : World) :
    (l1 α κ l m).real {w} = (S1 α κ l w).real {m} / ∑ w', (S1 α κ l w').real {m} := by
  obtain ⟨w₀, h₀⟩ := sem_nonempty l m
  have hx : ∑ w', S1 α κ l w' {m} ≠ 0 := λ h =>
    (S1_ne_zero_iff hα hκ l w₀ m).2 h₀ (Finset.sum_eq_zero_iff.1 h w₀ (Finset.mem_univ _))
  simp only [measureReal_def]
  rw [show l1 α κ l = (S1 α κ l)†(uniformOn Set.univ) from rfl,
    posterior_uniformOn_univ_apply_singleton _ hx w, ENNReal.toReal_div,
    ENNReal.toReal_sum λ _ _ => measure_ne_top _ _]

/-- The lexicon posterior on reals: the lexicon's speakers' shares of the message pooled over
states, over the shares of every state–lexicon pair. -/
theorem L1_snd_real (m : Msg) (l : Lex) :
    (L1 α κ m).snd.real {l}
      = (∑ w, (S1 α κ l w).real {m}) / ∑ p : World × Lex, (S1 α κ p.2 p.1).real {m} := by
  obtain ⟨w₀, h₀⟩ := sem_nonempty l m
  have hx : (familySpeaker L0 α (cost κ) ∘ₘ uniformOn (Set.univ : Set (World × Lex))) {m} ≠ 0 :=
    comp_familySpeaker_ne_zero (uniformOn_univ_singleton_ne_zero (w₀, l))
      ((S1_ne_zero_iff hα hκ l w₀ m).2 h₀)
  rw [L1, familyListener, posterior_snd_real_singleton _ _ hx l, Measure.comp_real_singleton]
  simp only [uniformOn_univ_real_singleton, familySpeaker_apply]
  rw [← Finset.mul_sum, ← Finset.mul_sum, mul_div_mul_left _ _ (by positivity)]
  rfl

end Model

/-- The cost factor on reals. -/
def costr (κ : ℝ≥0) (m : Msg) : ℝ := if m.IsDisjunction then κ else 1

theorem cost_toReal (κ : ℝ≥0) (m : Msg) : (cost κ m).toReal = costr κ m := by
  unfold cost costr; split_ifs <;> simp

/-- The literal listener's mass at a state on reals. -/
noncomputable def l0r (l : Lex) (m : Msg) (w : World) : ℝ :=
  if w ∈ sem l m then ((sem l m).card : ℝ)⁻¹ else 0

theorem L0_rpow_toReal {α : ℝ} (hα : 0 < α) (l : Lex) (m : Msg) (w : World) :
    (L0 l m {w} ^ α).toReal = l0r l m w ^ α := by
  rw [L0, uniformListener_apply_singleton, l0r]
  split_ifs
  · rw [← ENNReal.toReal_rpow, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  · rw [ENNReal.zero_rpow_of_pos hα, ENNReal.toReal_zero, Real.zero_rpow hα.ne']

/-- The speaker's share of a message: its weight, the literal listener's mass to the
rationality times the cost factor, over the weights of every message. -/
theorem S1_real {α : ℝ} (hα : 0 < α) (κ : ℝ≥0) (l : Lex) (w : World) (m : Msg) :
    (S1 α κ l w).real {m}
      = l0r l m w ^ α * costr κ m / ∑ m', l0r l m' w ^ α * costr κ m' := by
  rw [S1, speaker_real_singleton (L := L0 l) hα.le (cost_ne_top κ)
    (λ u => uniformListener_apply_singleton_le_one (sem l) u w)]
  simp only [L0_rpow_toReal hα, cost_toReal]

section Expertise

variable {α β : ℝ} (hα : 0 < α) (hβ : 0 ≤ β) {κ : ℝ≥0} (hκ : κ ≠ 0)
include hα hβ hκ

omit hκ in
private theorem S2_weight_ne_top (p : World × Lex) (m : Msg) :
    l1 α κ p.2 m {p.1} ^ α * (L1 α κ m).snd {p.2} ^ β * cost κ m ≠ ∞ :=
  ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hα.le (measure_ne_top _ _))
    (ENNReal.rpow_ne_top_of_nonneg hβ (measure_ne_top _ _))) (cost_ne_top κ m)

omit hβ in
private theorem S2_weight_ne_zero {p : World × Lex} {m : Msg} (hm : p.1 ∈ sem p.2 m) :
    l1 α κ p.2 m {p.1} ^ α * (L1 α κ m).snd {p.2} ^ β * cost κ m ≠ 0 :=
  mul_ne_zero (mul_ne_zero
    (ENNReal.rpow_pos (pos_iff_ne_zero.2 ((l1_ne_zero_iff hα hκ p.2 m p.1).2 hm))
      (measure_ne_top _ _)).ne'
    (ENNReal.rpow_pos (pos_iff_ne_zero.2 (L1_snd_ne_zero hα hκ m p.2)) (measure_ne_top _ _)).ne')
    (cost_ne_zero hκ m)

/-- Message preference of the expertise speaker is weight preference on reals. -/
theorem S2_real_lt_iff (p : World × Lex) (m₁ m₂ : Msg) :
    (S2 α β κ p).real {m₁} < (S2 α β κ p).real {m₂} ↔
      (l1 α κ p.2 m₁).real {p.1} ^ α * (L1 α κ m₁).snd.real {p.2} ^ β * costr κ m₁
        < (l1 α κ p.2 m₂).real {p.1} ^ α * (L1 α κ m₂).snd.real {p.2} ^ β * costr κ m₂ := by
  have hnull : ∀ p : World × Lex, p.1 ∈ sem p.2 .null := by decide
  have h0 : ∑ m, l1 α κ p.2 m {p.1} ^ α * (L1 α κ m).snd {p.2} ^ β * cost κ m ≠ 0 := λ h =>
    S2_weight_ne_zero hα hκ (hnull p) (Finset.sum_eq_zero_iff.1 h .null (Finset.mem_univ _))
  rw [S2, Kernel.ofWeights_real_singleton_lt_iff _ h0
    (ENNReal.sum_ne_top.2 λ m _ => S2_weight_ne_top hα hβ p m),
    ← ENNReal.toReal_lt_toReal (S2_weight_ne_top hα hβ p m₁) (S2_weight_ne_top hα hβ p m₂)]
  simp only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, cost_toReal, measureReal_def]

omit hβ in
/-- The expertise speaker gives no mass to a message false at the state under her lexicon. -/
theorem S2_apply_eq_zero {p : World × Lex} {m : Msg} (hm : p.1 ∉ sem p.2 m) : S2 α β κ p {m} = 0 :=
  Kernel.ofWeights_apply_singleton_eq_zero (by
    rw [not_ne_iff.1 (mt (l1_ne_zero_iff hα hκ p.2 m p.1).1 hm), ENNReal.zero_rpow_of_pos hα,
      zero_mul, zero_mul])

end Expertise

/-! ### The sums -/

/-- The states as `Fin 7`. -/
def World.equivFin : World ≃ Fin 7 where
  toFun | .w₁ => 0 | .w₂ => 1 | .w₃ => 2 | .w₁₂ => 3 | .w₁₃ => 4 | .w₂₃ => 5 | .w₁₂₃ => 6
  invFun | 0 => .w₁ | 1 => .w₂ | 2 => .w₃ | 3 => .w₁₂ | 4 => .w₁₃ | 5 => .w₂₃ | 6 => .w₁₂₃
  left_inv w := by cases w <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-- The messages as `Fin 8`. -/
def Msg.equivFin : Msg ≃ Fin 8 where
  toFun
    | .A => 0 | .B => 1 | .X => 2 | .AorB => 3 | .AorX => 4 | .BorX => 5 | .AorBorX => 6
    | .null => 7
  invFun
    | 0 => .A | 1 => .B | 2 => .X | 3 => .AorB | 4 => .AorX | 5 => .BorX | 6 => .AorBorX
    | 7 => .null
  left_inv m := by cases m <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-- The lexica as `Fin 3`. -/
def Lex.equivFin : Lex ≃ Fin 3 where
  toFun | .base => 0 | .excl => 1 | .syn => 2
  invFun | 0 => .base | 1 => .excl | 2 => .syn
  left_inv l := by cases l <;> rfl
  right_inv i := by fin_cases i <;> rfl

theorem World.sum_univ {M : Type*} [AddCommMonoid M] (f : World → M) :
    ∑ w, f w = f .w₁ + f .w₂ + f .w₃ + f .w₁₂ + f .w₁₃ + f .w₂₃ + f .w₁₂₃ := by
  rw [Fintype.sum_equiv World.equivFin f (f ∘ World.equivFin.symm) λ w => by simp,
    Fin.sum_univ_seven]
  rfl

theorem Msg.sum_univ {M : Type*} [AddCommMonoid M] (f : Msg → M) :
    ∑ m, f m = f .A + f .B + f .X + f .AorB + f .AorX + f .BorX + f .AorBorX + f .null := by
  rw [Fintype.sum_equiv Msg.equivFin f (f ∘ Msg.equivFin.symm) λ m => by simp,
    Fin.sum_univ_eight]
  rfl

theorem Lex.sum_univ {M : Type*} [AddCommMonoid M] (f : Lex → M) :
    ∑ l, f l = f .base + f .excl + f .syn := by
  rw [Fintype.sum_equiv Lex.equivFin f (f ∘ Lex.equivFin.symm) λ l => by simp,
    Fin.sum_univ_three]
  rfl

/-! ### The Hurfordian context (§5.2, Figure 10) -/

/-- The Bernstein monomials of an interval are nonnegative on it. -/
private theorem bern {x a b : ℝ} (ha : a ≤ x) (hb : x ≤ b) (i j : ℕ) :
    0 ≤ (x - a) ^ i * (b - x) ^ j :=
  mul_nonneg (pow_nonneg (sub_nonneg.2 ha) i) (pow_nonneg (sub_nonneg.2 hb) j)

section Findings

variable {κ : ℝ≥0} (hκ : 0 < κ)
include hκ

/-- The ignorance implicature: hearing *A or X*, the lexical-uncertainty listener ranks the
uncertain state above the first atom and that above the second. -/
theorem l1_uncertainty (hκ1 : κ ≤ 1) :
    (L1 2 κ .AorX).fst.real {.w₂} < (L1 2 κ .AorX).fst.real {.w₁} ∧
      (L1 2 κ .AorX).fst.real {.w₁} < (L1 2 κ .AorX).fst.real {.w₁₂} := by
  have hκ' : (0 : ℝ) < κ := hκ
  have hκ1' : (κ : ℝ) ≤ 1 := hκ1
  simp +decide only [L1_fst_real_lt_iff two_pos hκ.ne', Lex.sum_univ, S1_real two_pos,
    Msg.sum_univ, l0r, costr, card_sem, semCard, ↓reduceIte, Real.rpow_two, Nat.cast_ofNat,
    Nat.cast_one, inv_one, one_pow, mul_one, zero_pow, zero_mul, add_zero, zero_add, zero_div]
  constructor <;> field_simp <;> ring_nf
  · linarith [pow_pos hκ' 2, pow_pos hκ' 3]
  · linarith [bern hκ'.le hκ1' 4 0, bern hκ'.le hκ1' 3 1, bern hκ'.le hκ1' 2 2,
      bern hκ'.le hκ1' 1 3, bern hκ'.le hκ1' 0 4]

/-- The Hurford rescue: hearing *A or X*, the listener ranks the exclusivized lexicon above the
base lexicon and that above the synonym lexicon. -/
theorem l1_lexicon (hκ1 : κ ≤ 1) :
    (L1 2 κ .AorX).snd.real {.syn} < (L1 2 κ .AorX).snd.real {.base} ∧
      (L1 2 κ .AorX).snd.real {.base} < (L1 2 κ .AorX).snd.real {.excl} := by
  have hκ' : (0 : ℝ) < κ := hκ
  have hκ1' : (κ : ℝ) ≤ 1 := hκ1
  simp +decide only [L1_snd_real_lt_iff two_pos hκ.ne', World.sum_univ, S1_real two_pos,
    Msg.sum_univ, l0r, costr, card_sem, semCard, ↓reduceIte, Real.rpow_two, Nat.cast_ofNat,
    Nat.cast_one, inv_one, one_pow, mul_one, zero_pow, zero_mul, add_zero, zero_add, zero_div]
  constructor <;> field_simp <;> ring_nf
  · linarith [bern hκ'.le hκ1' 3 0, bern hκ'.le hκ1' 2 1, bern hκ'.le hκ1' 1 2,
      bern hκ'.le hκ1' 0 3]
  · linarith [pow_pos hκ' 2, pow_pos hκ' 3]

/-- The exclusivizing speaker uses the disjunction exactly when uncertain: at the uncertain
state it beats both bare disjuncts, while knowing the first atom the bare *A* wins. -/
theorem s1_disjunction_iff_uncertain (hκ1 : κ ≤ 1) :
    (S1 2 κ .excl .w₁₂).real {.A} < (S1 2 κ .excl .w₁₂).real {.AorX} ∧
      (S1 2 κ .excl .w₁₂).real {.X} < (S1 2 κ .excl .w₁₂).real {.AorX} ∧
      (S1 2 κ .excl .w₁).real {.AorX} < (S1 2 κ .excl .w₁).real {.A} := by
  have hκ' : (0 : ℝ) < κ := hκ
  have hκ1' : (κ : ℝ) ≤ 1 := hκ1
  simp +decide only [ S1_real two_pos, Msg.sum_univ, l0r, costr, card_sem,
    semCard, ↓reduceIte, Real.rpow_two, Nat.cast_ofNat, Nat.cast_one, inv_one, one_pow, mul_one,
    zero_pow, zero_mul, add_zero, zero_add, zero_div]
  refine ⟨by positivity, by positivity, ?_⟩
  field_simp
  ring_nf
  linarith

/-- The expertise component: at a disjunction cost of at least `log 2`, *A or X* signals the
exclusivized lexicon more strongly than the bare *A* does, which every lexicon reads alike. -/
theorem AorX_signals_excl (hκ2 : κ ≤ 1 / 2) :
    (L1 2 κ .A).snd.real {.excl} < (L1 2 κ .AorX).snd.real {.excl} := by
  have hκ' : (0 : ℝ) < κ := hκ
  have hκ2' : (κ : ℝ) ≤ 1 / 2 := by exact_mod_cast hκ2
  simp +decide only [L1_snd_real two_pos hκ.ne', Fintype.sum_prod_type, World.sum_univ,
    Lex.sum_univ, S1_real two_pos, Msg.sum_univ, l0r, costr, card_sem,
    semCard, ↓reduceIte, Real.rpow_two, Nat.cast_ofNat, Nat.cast_one, inv_one, one_pow, mul_one,
    zero_pow, zero_mul, add_zero, zero_add, zero_div]
  field_simp
  ring_nf
  linarith [bern hκ'.le hκ2' 6 0, bern hκ'.le hκ2' 5 1, bern hκ'.le hκ2' 4 2, bern hκ'.le hκ2' 3 3,
    bern hκ'.le hκ2' 2 4, bern hκ'.le hκ2' 1 5, bern hκ'.le hκ2' 0 6]

/-- The paper's production claim for the context: at a disjunction cost between `log 10` and
0, the expertise speaker who observes the uncertain state with the exclusivized lexicon prefers
*A or X* to every other message. -/
theorem s2_prefers_disjunction (hκ10 : 1 / 10 ≤ κ) (hκ1 : κ ≤ 1) (m : Msg) (hm : m ≠ .AorX) :
    (S2 2 1 κ (.w₁₂, .excl)).real {m} < (S2 2 1 κ (.w₁₂, .excl)).real {.AorX} := by
  have hκ' : (0 : ℝ) < κ := hκ
  have hκ10' : (1 / 10 : ℝ) ≤ κ := by exact_mod_cast hκ10
  have hκ1' : (κ : ℝ) ≤ 1 := hκ1
  rw [S2_real_lt_iff two_pos zero_le_one hκ.ne']
  cases m
  case AorX => exact absurd rfl hm
  all_goals
    simp +decide only [l1_real two_pos hκ.ne', L1_snd_real two_pos hκ.ne', Fintype.sum_prod_type,
      World.sum_univ, Lex.sum_univ, Real.rpow_one, S1_real two_pos, Msg.sum_univ, l0r, costr,
      card_sem, semCard, ↓reduceIte, Real.rpow_two, Nat.cast_ofNat, Nat.cast_one, inv_one,
      one_pow, mul_one, zero_pow, zero_mul, add_zero, zero_add, zero_div]
  case A => positivity
  case B => positivity
  case X => positivity
  case BorX => positivity
  case AorB =>
    field_simp
    ring_nf
    linarith [bern hκ10' hκ1' 5 0, bern hκ10' hκ1' 4 1, bern hκ10' hκ1' 3 2, bern hκ10' hκ1' 2 3,
      bern hκ10' hκ1' 1 4, bern hκ10' hκ1' 0 5]
  case AorBorX =>
    field_simp
    ring_nf
    linarith [bern hκ10' hκ1' 5 0, bern hκ10' hκ1' 4 1, bern hκ10' hκ1' 3 2, bern hκ10' hκ1' 2 3,
      bern hκ10' hκ1' 1 4, bern hκ10' hκ1' 0 5]
  case null =>
    field_simp
    ring_nf
    linarith [bern hκ10' hκ1' 10 0, bern hκ10' hκ1' 9 1, bern hκ10' hκ1' 8 2, bern hκ10' hκ1' 7 3,
      bern hκ10' hκ1' 6 4, bern hκ10' hκ1' 5 5, bern hκ10' hκ1' 4 6, bern hκ10' hκ1' 3 7,
      bern hκ10' hκ1' 2 8, bern hκ10' hκ1' 1 9, bern hκ10' hκ1' 0 10]

/-- The marginal expertise speaker at the uncertain state never uses the bare *A* and does use
the disjunction. -/
theorem s2exp_uncertain : S2exp 2 1 κ .w₁₂ {.A} = 0 ∧ S2exp 2 1 κ .w₁₂ {.AorX} ≠ 0 := by
  refine ⟨?_, ?_⟩
  · rw [S2exp, Kernel.mixture_apply']
    exact Finset.sum_eq_zero λ l _ => by
      rw [Kernel.comap_apply', S2_apply_eq_zero two_pos hκ.ne' (by cases l <;> decide), mul_zero]
  · rw [S2exp, Kernel.mixture_apply_ne_zero_iff]
    exact ⟨.excl, by simp, by
      rw [Kernel.comap_apply']
      exact Kernel.ofWeights_apply_singleton_ne_zero
        (S2_weight_ne_zero two_pos hκ.ne' (by decide))
        (S2_weight_ne_top two_pos zero_le_one _)⟩

end Findings

end PottsLevy2015
