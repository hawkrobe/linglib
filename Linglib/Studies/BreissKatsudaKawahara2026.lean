import Linglib.Core.Probability.LogitChoice
import Linglib.Phonology.Constraints.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation

/-!
# Breiss, Katsuda and Kawahara 2026: modelling frequency-conditioned paradigm uniformity

This file formalizes the Voting Bases analysis of Japanese voiced velar nasalisation in
[breiss-katsuda-kawahara-2026b]: a MaxEnt grammar with one markedness constraint against
word-internal [g] and two faithfulness constraints, to the listed free-standing N2 and to the listed
whole compound, whose violations are scaled by the resting activation of the base they are assessed
against ([breiss-2024]). The data are the frequency effects of [breiss-katsuda-kawahara-2026a] as
the modelling article recapitulates them: in compounds with a free N2 nasalisation is variable, more
likely the more frequent the compound and less likely the more frequent the free N2, in existing and
novel compounds alike; with a bound N2 it is exceptionless.

The model derives the opposite signs of the two effects from one mechanism. Activation strengthens
faithfulness to a base; the free N2 is listed with the [g] it shows word-initially, and an existing
compound is listed, by Lexicon Optimisation, with its nasalised medial; bound N2s and novel
compounds contribute no base, so their faithfulness constraints are inert. The output–output
account of [breiss-katsuda-kawahara-2021] fixed the direction of each effect by stipulation, and the
traditional account ([ito-mester-1996], [ito-mester-2003]) has markedness drive the alternation,
whereas the fitted grammar puts the markedness weight at zero.

## Main definitions

* `Base`, `Item` — a listed allomorph with its resting activation; a compound's optional N2 and
  whole-compound bases
* `con`, `scaledWeights`, `pNasal` — the three constraints, the activation-scaled weights, and the
  MaxEnt probability of nasalisation

## Main results

* `pNasal_eq_sigmoid` — nasalisation probability is the sigmoid of the markedness weight plus the
  weighted pulls of the bases, each signed by its listed velar
* `existing_strictAnti_n2`, `existing_strictMono_compound`, `novel_strictAnti_n2` — the two
  frequency effects, with their signs, in existing and novel compounds
* `novel_lt_existing`, `bound_half_le` — a stored compound adds nasalisation; a bound-N2 compound
  nasalises at least half the time, whatever its frequency
* `zero_markedness_iff` — with the markedness weight at zero, nasalisation wins exactly when the
  compound base outpulls the N2 base
* `tableau7`, `tableau8`, `tableau9` — the schematic tableaux

## References

* [breiss-katsuda-kawahara-2026b]
* [breiss-katsuda-kawahara-2026a]
* [breiss-2024]
* [breiss-katsuda-kawahara-2021]
* [steriade-1997]
* [ito-mester-1996]
* [ito-mester-2003]
* [coetzee-kawahara-2013]
-/

namespace BreissKatsudaKawahara2026

open Constraints Real

/-- The compound-medial velar, oral [g] or nasal [ŋ]. -/
inductive Velar | oral | nasal
  deriving DecidableEq, Fintype

/-- A listed allomorph, identified by its velar, with its resting activation — the sigmoid of its
centred log-frequency (§4.4), or any scalar salience measure (§4.1). -/
structure Base where
  velar : Velar
  activation : ℝ

/-- A compound's lexical situation (§4.1): the free-standing N2's listed allomorph if N2 is free,
and the whole compound's listed allomorph if the compound is existing. -/
structure Item where
  n2 : Option Base
  compound : Option Base

/-- A free N2 is listed with the [g] it shows word-initially, at activation `a`. -/
def freeN2 (a : ℝ) : Base := ⟨.oral, a⟩

/-- An existing compound is listed with its nasalised medial (Lexicon Optimisation), at activation
`b`. -/
def storedCompound (b : ℝ) : Base := ⟨.nasal, b⟩

/-- A novel compound with a free N2. -/
def novel (a : ℝ) : Item := ⟨some (freeN2 a), none⟩

/-- An existing compound with a free N2. -/
def existing (a b : ℝ) : Item := ⟨some (freeN2 a), some (storedCompound b)⟩

/-- An existing compound with a bound N2. -/
def bound (b : ℝ) : Item := ⟨none, some (storedCompound b)⟩

/-! ### Constraints, scaling, and the MaxEnt probability -/

/-- ID-[nasal] to an optional listed base (6b–c): one violation when the candidate's velar differs
from the base's, none when there is no base. -/
def idNasal : Option Base → Constraint Velar
  | some β => Constraint.binary (· ≠ β.velar)
  | none => 0

/-- The constraint set (6): `*INTERNAL-[g]`, ID-[nasal] to the N2, ID-[nasal] to the compound. -/
def con (it : Item) : CON Velar 3 :=
  ![Constraint.binary (· = .oral), idNasal it.n2, idNasal it.compound]

/-- Constraint weights, indexed like `con`. -/
structure Weights where
  markedness : ℝ
  n2 : ℝ
  compound : ℝ

/-- A base's resting activation, `0` for no base. -/
def activation : Option Base → ℝ
  | some β => β.activation
  | none => 0

/-- Voting Bases scaling (§4.2): a faithfulness violation counts in proportion to the activation of
the base it is assessed against, so each faithfulness weight is scaled by that activation. The
relation runs opposite to [coetzee-kawahara-2013]'s, where higher frequency lowers faithfulness
(§6.4). -/
def scaledWeights (w : Weights) (it : Item) : Fin 3 → ℝ :=
  ![w.markedness, w.n2 * activation it.n2, w.compound * activation it.compound]

/-- The MaxEnt probability that the compound nasalises. -/
noncomputable def pNasal (w : Weights) (it : Item) : ℝ :=
  softmax (harmonyScore (con it) (scaledWeights w it)) .nasal

/-- A base's pull toward nasalisation: its activation, signed by its listed velar. -/
def pull : Option Base → ℝ
  | some ⟨.oral, a⟩ => -a
  | some ⟨.nasal, a⟩ => a
  | none => 0

@[simp] theorem pull_freeN2 (a : ℝ) : pull (some (freeN2 a)) = -a := rfl
@[simp] theorem pull_storedCompound (b : ℝ) : pull (some (storedCompound b)) = b := rfl
@[simp] theorem pull_none : pull none = 0 := rfl

theorem sum_velar (f : Velar → ℝ) : ∑ x, f x = f .oral + f .nasal := by
  show ∑ x ∈ ({.oral, .nasal} : Finset Velar), f x = _
  rw [Finset.sum_pair (by decide)]

theorem softmax_nasal (s : Velar → ℝ) : softmax s .nasal = sigmoid (s .nasal - s .oral) := by
  rw [sigmoid_def, ← one_div]
  simp only [softmax, sum_velar]
  have h : exp (s .oral) + exp (s .nasal) = exp (s .nasal) * (1 + exp (-(s .nasal - s .oral))) := by
    rw [mul_add, mul_one, ← exp_add, show s .nasal + -(s .nasal - s .oral) = s .oral by ring,
      add_comm]
  rw [h, ← div_div, div_self (exp_pos _).ne']

theorem harmony_sub (w : Weights) (it : Item) :
    harmonyScore (con it) (scaledWeights w it) .nasal
        - harmonyScore (con it) (scaledWeights w it) .oral
      = w.markedness + w.n2 * pull it.n2 + w.compound * pull it.compound := by
  obtain ⟨n2, c⟩ := it
  rcases n2 with _ | ⟨_ | _, a⟩ <;> rcases c with _ | ⟨_ | _, b⟩ <;>
    simp [harmonyScore, weightedViolations, Fin.sum_univ_three, con, scaledWeights, idNasal, pull,
      activation, Constraint.binary] <;> ring

/-- The probability of nasalisation is the sigmoid of the markedness weight plus the weighted pulls
of the two bases, so each frequency effect takes the sign of its base's listed velar. -/
theorem pNasal_eq_sigmoid (w : Weights) (it : Item) :
    pNasal w it = sigmoid (w.markedness + w.n2 * pull it.n2 + w.compound * pull it.compound) := by
  rw [pNasal, softmax_nasal, harmony_sub]

/-! ### The frequency effects -/

/-- An existing compound with a free N2 nasalises with probability `σ(w_M − w_N2·a + w_C·b)`. -/
theorem pNasal_existing (w : Weights) (a b : ℝ) :
    pNasal w (existing a b) = sigmoid (w.markedness - w.n2 * a + w.compound * b) := by
  rw [pNasal_eq_sigmoid]; simp only [existing, pull_freeN2, pull_storedCompound]; ring_nf

/-- A novel compound has no whole-compound base. -/
theorem pNasal_novel (w : Weights) (a : ℝ) :
    pNasal w (novel a) = sigmoid (w.markedness - w.n2 * a) := by
  rw [pNasal_eq_sigmoid]; simp only [novel, pull_freeN2, pull_none]; ring_nf

/-- A bound N2 (5) has no free base. -/
theorem pNasal_bound (w : Weights) (b : ℝ) :
    pNasal w (bound b) = sigmoid (w.markedness + w.compound * b) := by
  rw [pNasal_eq_sigmoid]; simp only [bound, pull_none, pull_storedCompound]; ring_nf

/-- The N2 effect (Figure 2, right): the more active the free N2, the less nasalisation. -/
theorem existing_strictAnti_n2 (w : Weights) (hw : 0 < w.n2) (b : ℝ) :
    StrictAnti fun a => pNasal w (existing a b) := fun _ _ h => by
  simp only [pNasal_existing]
  exact sigmoid_lt (by nlinarith)

/-- The compound effect (Figure 2, left): the more active the stored compound, the more
nasalisation. -/
theorem existing_strictMono_compound (w : Weights) (hw : 0 < w.compound) (a : ℝ) :
    StrictMono fun b => pNasal w (existing a b) := fun _ _ h => by
  simp only [pNasal_existing]
  exact sigmoid_lt (by nlinarith)

/-- The N2 effect persists, with the same sign, in novel compounds (Figure 3). -/
theorem novel_strictAnti_n2 (w : Weights) (hw : 0 < w.n2) :
    StrictAnti fun a => pNasal w (novel a) := fun _ _ h => by
  simp only [pNasal_novel]
  exact sigmoid_lt (by nlinarith)

/-- A stored compound's pull adds nasalisation at any N2 activation. -/
theorem novel_lt_existing (w : Weights) (hw : 0 < w.compound) (a : ℝ) {b : ℝ} (hb : 0 < b) :
    pNasal w (novel a) < pNasal w (existing a b) := by
  rw [pNasal_novel, pNasal_existing]
  exact sigmoid_lt (by nlinarith)

/-- A bound-N2 compound nasalises at least half the time under nonnegative weights, and its
probability mentions no N2 activation. -/
theorem bound_half_le (w : Weights) (hM : 0 ≤ w.markedness) (hC : 0 ≤ w.compound) {b : ℝ}
    (hb : 0 ≤ b) : 2⁻¹ ≤ pNasal w (bound b) := by
  rw [pNasal_bound, ← sigmoid_zero]
  exact sigmoid_le (add_nonneg hM (mul_nonneg hC hb))

/-- With `*INTERNAL-[g]` at zero weight, as in the fitted grammar (Table 1), nasalisation is the
majority outcome exactly when the compound base's weighted activation exceeds the N2 base's:
analogical faithfulness does all the work (§5.1, §6.2). -/
theorem zero_markedness_iff (w : Weights) (hM : w.markedness = 0) (a b : ℝ) :
    2⁻¹ < pNasal w (existing a b) ↔ w.n2 * a < w.compound * b := by
  rw [pNasal_existing, ← sigmoid_zero, sigmoid_lt_iff, hM]
  constructor <;> intro h <;> linarith

/-! ### The schematic tableaux -/

/-- The weights of tableaux (7) and (8): markedness 2, both faithfulness constraints 1. -/
def w78 : Weights := ⟨2, 1, 1⟩

/-- The weights of tableau (9): markedness 0.1, N2 faithfulness 1, compound faithfulness 2. -/
noncomputable def w9 : Weights := ⟨1 / 10, 1, 2⟩

/-- Tableau (7): novel compounds whose N2 activations are 0.7 and 0.3. The higher-activation N2's
candidates have harmonies `-2` and `-0.7`, so it nasalises with probability `σ(1.3)`, less often
than the lower-activation N2. -/
theorem tableau7 :
    harmonyScore (con (novel (7 / 10))) (scaledWeights w78 (novel (7 / 10))) .oral = -2 ∧
    harmonyScore (con (novel (7 / 10))) (scaledWeights w78 (novel (7 / 10))) .nasal = -(7 / 10) ∧
    pNasal w78 (novel (7 / 10)) = sigmoid (13 / 10) ∧
    pNasal w78 (novel (7 / 10)) < pNasal w78 (novel (3 / 10)) := by
  refine ⟨?_, ?_, ?_, novel_strictAnti_n2 w78 (by norm_num [w78]) (by norm_num)⟩
  · norm_num [harmonyScore, weightedViolations, Fin.sum_univ_three, con, scaledWeights, idNasal,
      activation, novel, freeN2, w78, Constraint.binary]
  · norm_num [harmonyScore, weightedViolations, Fin.sum_univ_three, con, scaledWeights, idNasal,
      activation, novel, freeN2, w78, Constraint.binary]
    decide
  · rw [pNasal_novel]; norm_num [w78]

/-- Tableau (8): existing compounds with N2 activation 0.5 and compound activations 0.7 and 0.3.
The higher-activation compound nasalises more, and either nasalises more than the novel compound
of (7) with the same N2. -/
theorem tableau8 :
    pNasal w78 (existing (1 / 2) (3 / 10)) < pNasal w78 (existing (1 / 2) (7 / 10)) ∧
    pNasal w78 (novel (1 / 2)) < pNasal w78 (existing (1 / 2) (3 / 10)) :=
  ⟨existing_strictMono_compound w78 (by norm_num [w78]) _ (by norm_num),
    novel_lt_existing w78 (by norm_num [w78]) _ (by norm_num)⟩

/-- Tableau (9): with markedness weak and faithfulness strong, the nasal candidate is still the
majority outcome for either compound of (8), and the compound effect keeps its sign. -/
theorem tableau9 :
    2⁻¹ < pNasal w9 (existing (1 / 2) (3 / 10)) ∧
    pNasal w9 (existing (1 / 2) (3 / 10)) < pNasal w9 (existing (1 / 2) (7 / 10)) := by
  refine ⟨?_, existing_strictMono_compound w9 (by norm_num [w9]) _ (by norm_num)⟩
  rw [pNasal_existing, ← sigmoid_zero, sigmoid_lt_iff]
  norm_num [w9]

end BreissKatsudaKawahara2026
