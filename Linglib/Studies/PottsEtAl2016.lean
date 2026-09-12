import Linglib.Pragmatics.RSA.Silence

/-!
# Potts, Lassiter, Levy and Frank (2016): Embedded Implicatures as Pragmatic Inferences under Compositional Lexical Uncertainty

This file formalizes the compositional lexical-uncertainty model of [potts-etal-2016] in the
context of its experiment (§6). Three players each hit none, some, or all of their shots, a
state being the multiset of outcomes (16); a message composes a quantifier over players with a
quantifier over shots, the null message added (18); and the lexica are the neo-Gricean
refinement set of *some*, itself or *some but not all* (14), (19d). The literal listener
conditions a flat prior on a message's extension under a lexicon, the speaker weights messages
by the listener's mass at the state and a cost, and the uncertainty listener inverts the speaker
jointly over states and lexica (13) (`L0`, `S1`, `L1`); the fixed-lexicon pragmatics of (19b)
inverts the base-lexicon speaker alone (`L1fixed`). The uncertainty listener assigns mass to a
state exactly when some refinement makes the message true there, the fixed-lexicon listener
exactly when the base lexicon does, so *exactly one player hit some of his shots* is heard as
compatible with the locally enriched states NSA and SAA and *no player hit some of his shots*
with NNA, NAA and AAA, which the fixed-lexicon model excludes (`one_some_local`,
`no_some_local`), the low but non-negligible enrichment under a negative quantifier that
[chemla-spector-2011] report. The uncertainty listener still ranks the literal construal first,
NNS and NNN (`one_some_literal_first`, `no_some_literal_first`), and for *every player hit some
of his shots* mirrors the human ordering, SSS first and AAA last among the true states, where
the fixed-lexicon listener puts SAA first (`every_some_ordering`, `every_some_fixed`). Every
ordering holds at every rationality and every cost of the null message.

## Implementation notes

The state and lexicon priors are flat (18). The null message is true at every state, so its
cost adds the same weight to every row of the speaker, and the share of a statement is its
informativity weight over the sum of the weights of the statements true at the state plus that
constant; each ordering is an inequality between such fractions in the weights `4^{-α}`,
`3^{-α}`, `2^{-α}`, `1`. The unconstrained refinement model (19c), whose lexica are the nonempty
subsets of the denotation of *some* over sets of shots, and the fit to the response data are not
formalized.

## References

* [potts-etal-2016]
* [chemla-spector-2011]
-/

open MeasureTheory ProbabilityTheory RSA
open scoped ENNReal NNReal

namespace PottsEtAl2016

/-! ### The context (§6, (16) and (18)) -/

/-- A player's outcome: hit none of the shots, some but not all, or all. -/
inductive Outcome where
  | nothing
  | scored
  | aced
  deriving DecidableEq, Fintype

/-- The states (16): the multisets of three outcomes, named by their outcomes. -/
inductive World where
  | NNN
  | NNS
  | NNA
  | NSS
  | NSA
  | NAA
  | SSS
  | SSA
  | SAA
  | AAA
  deriving DecidableEq, Fintype, Nonempty

instance : MeasurableSpace World := ⊤

/-- The outcomes of a state. -/
def World.outcomes : World → Multiset Outcome
  | .NNN => {.nothing, .nothing, .nothing}
  | .NNS => {.nothing, .nothing, .scored}
  | .NNA => {.nothing, .nothing, .aced}
  | .NSS => {.nothing, .scored, .scored}
  | .NSA => {.nothing, .scored, .aced}
  | .NAA => {.nothing, .aced, .aced}
  | .SSS => {.scored, .scored, .scored}
  | .SSA => {.scored, .scored, .aced}
  | .SAA => {.scored, .aced, .aced}
  | .AAA => {.aced, .aced, .aced}

/-- The quantifiers over a player's shots: *every*, *no*, *some*. -/
inductive ShotQ where
  | every
  | no
  | some_
  deriving DecidableEq, Fintype

/-- The quantifiers over the players: *every*, *exactly one*, *no*. -/
inductive PlayerQ where
  | every
  | exactlyOne
  | no
  deriving DecidableEq, Fintype

/-- The lexica of the neo-Gricean refinement set (14), (19d): *some* read as itself or as
*some but not all*. -/
inductive Lex where
  | weak
  | strong
  deriving DecidableEq, Fintype, Nonempty

instance : MeasurableSpace Lex := ⊤

/-- The outcomes *some* covers under a lexicon: any hit, or some but not all. -/
def Lex.someDen : Lex → Finset Outcome
  | .weak => {.scored, .aced}
  | .strong => {.scored}

/-- The refinement condition (11): each lexicon reads *some* as a nonempty part of its base
denotation, which the base lexicon is. -/
theorem lex_refines : ∀ l : Lex, l.someDen.Nonempty ∧ l.someDen ⊆ Lex.weak.someDen := by
  decide

/-- Whether an outcome satisfies the quantifier over shots under a lexicon. -/
def ShotQ.Holds (l : Lex) : ShotQ → Outcome → Prop
  | .every, o => o = .aced
  | .no, o => o = .nothing
  | .some_, o => o ∈ l.someDen

instance (l : Lex) (s : ShotQ) : DecidablePred (s.Holds l) := λ o => by
  cases s <;> unfold ShotQ.Holds <;> infer_instance

/-- Whether a number of players satisfies the quantifier over players. -/
def PlayerQ.Holds : PlayerQ → ℕ → Prop
  | .every, n => n = 3
  | .exactlyOne, n => n = 1
  | .no, n => n = 0

instance (q : PlayerQ) : DecidablePred q.Holds := λ n => by
  cases q <;> unfold PlayerQ.Holds <;> infer_instance

/-- A statement (18c): a quantifier over players applied to a quantifier over shots. -/
abbrev Stmt := PlayerQ × ShotQ

/-- The truth of a statement at a state under a lexicon: the quantifier over players applied to
the number of players whose outcome satisfies the quantifier over shots. -/
def Stmt.Truth (l : Lex) (s : Stmt) (w : World) : Prop :=
  s.1.Holds (w.outcomes.countP (s.2.Holds l))

instance (l : Lex) (s : Stmt) : DecidablePred (s.Truth l) := λ w =>
  inferInstanceAs (Decidable (s.1.Holds (w.outcomes.countP (s.2.Holds l))))

/-- The extension of a statement under a lexicon. -/
def stmtSem (l : Lex) (s : Stmt) : Finset World := Finset.univ.filter (s.Truth l)

/-- The messages (18c): the statements and the null message of (12a). -/
abbrev Msg := WithSilence Stmt

instance : MeasurableSpace Msg := ⊤

/-- The extension of a message under a lexicon, the null message true at every state. -/
def sem (l : Lex) : Msg → Finset World := liftSem (stmtSem l)

/-- *Every player hit some of his shots*. -/
abbrev everySome : Stmt := (.every, .some_)

/-- *Exactly one player hit some of his shots*. -/
abbrev oneSome : Stmt := (.exactlyOne, .some_)

/-- *No player hit some of his shots*. -/
abbrev noSome : Stmt := (.no, .some_)

/-- The lexica agree off *some*, and the refinement narrows the extension of *some* under
*every* while widening it under *no*, the source of the asymmetry; under *exactly one* the
refinement admits the locally enriched states NSA and SAA. -/
theorem refinement_facts :
    (∀ q : PlayerQ, stmtSem .weak (q, .every) = stmtSem .strong (q, .every) ∧
      stmtSem .weak (q, .no) = stmtSem .strong (q, .no)) ∧
    stmtSem .strong everySome ⊂ stmtSem .weak everySome ∧
    stmtSem .weak noSome ⊂ stmtSem .strong noSome ∧
    stmtSem .weak oneSome = {.NNS, .NNA} ∧ stmtSem .strong oneSome = {.NNS, .NSA, .SAA} := by
  decide

/-- Every message is true at some state under the base lexicon. -/
theorem sem_weak_nonempty (m : Msg) : ∃ w, w ∈ sem .weak m := by
  revert m; decide

/-! ### The model (13), (18), (19) -/

section Tower

variable (α : ℝ) (κ : ℝ≥0)

/-- The cost factor (18d): `κ` for the null message and 1 for every statement. -/
def cost : Msg → ℝ≥0∞ := liftCostFactor κ 1

/-- The literal listener (13a) at a flat prior: uniform on the message's extension. -/
noncomputable def L0 (l : Lex) : Kernel Msg World := uniformListener (sem l)

/-- The speaker (13b). -/
noncomputable def S1 (l : Lex) : Kernel World Msg := speaker α (cost κ) (L0 l)

/-- The uncertainty listener (13c): the joint posterior over states and lexica at flat priors,
whose state marginal is the paper's listener. -/
noncomputable def L1 : Kernel Msg (World × Lex) :=
  familyListener L0 α (cost κ) (uniformOn Set.univ)

/-- The fixed-lexicon pragmatic listener (19b): the base lexicon's speaker inverted at a flat
prior. -/
noncomputable def L1fixed : Kernel Msg World :=
  pragmaticListener α (cost κ) (L0 .weak) (uniformOn Set.univ)

end Tower

private theorem cost_ne_zero {κ : ℝ≥0} (hκ : κ ≠ 0) (m : Msg) : cost κ m ≠ 0 := by
  cases m <;> simp [cost, hκ]

private theorem cost_ne_top (κ : ℝ≥0) (m : Msg) : cost κ m ≠ ∞ := by
  cases m <;> simp [cost]

section Model

variable {α : ℝ} (hα : 0 < α) {κ : ℝ≥0} (hκ : κ ≠ 0)
include hα hκ

/-! ### Support: local enrichment (§6.3) -/

/-- The uncertainty listener assigns mass to a state exactly when some lexicon makes the
message true there. -/
theorem L1_fst_ne_zero_iff (m : Msg) (w : World) :
    (L1 α κ m).fst {w} ≠ 0 ↔ ∃ l, w ∈ sem l m :=
  familyListener_uniform_fst_apply_singleton_ne_zero_iff sem hα (cost_ne_zero hκ)
    (cost_ne_top κ) (let ⟨w, h⟩ := sem_weak_nonempty m; ⟨.weak, w, h⟩) w

/-- The fixed-lexicon listener assigns mass to a state exactly when the base lexicon makes the
message true there. -/
theorem L1fixed_ne_zero_iff (m : Msg) (w : World) :
    L1fixed α κ m {w} ≠ 0 ↔ w ∈ sem .weak m := by
  obtain ⟨w₀, h₀⟩ := sem_weak_nonempty m
  have hs := speaker_uniformListener_apply_singleton_ne_zero_iff (sem .weak) hα
    (cost_ne_zero hκ) (cost_ne_top κ)
  rw [L1fixed, pragmaticListener, L0, posterior_apply_singleton_ne_zero_iff _ _
    (comp_apply_singleton_ne_zero _ _ (uniformOn_univ_singleton_ne_zero w₀) ((hs w₀ m).2 h₀)),
    and_iff_right (uniformOn_univ_singleton_ne_zero w), hs]

/-- *Exactly one player hit some of his shots*: the locally enriched states NSA and SAA, false
on the literal construal, receive mass from the uncertainty listener and none from the
fixed-lexicon listener. -/
theorem one_some_local :
    ∀ w ∈ ({.NSA, .SAA} : Finset World),
      (L1 α κ (some oneSome)).fst {w} ≠ 0 ∧ L1fixed α κ (some oneSome) {w} = 0 := by
  intro w hw
  rw [L1_fst_ne_zero_iff hα hκ, ← not_ne_iff, (L1fixed_ne_zero_iff hα hκ _ w).not]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl <;> decide

/-- *No player hit some of his shots*: the locally enriched states NNA, NAA and AAA receive mass
from the uncertainty listener and none from the fixed-lexicon listener. -/
theorem no_some_local :
    ∀ w ∈ ({.NNA, .NAA, .AAA} : Finset World),
      (L1 α κ (some noSome)).fst {w} ≠ 0 ∧ L1fixed α κ (some noSome) {w} = 0 := by
  intro w hw
  rw [L1_fst_ne_zero_iff hα hκ, ← not_ne_iff, (L1fixed_ne_zero_iff hα hκ _ w).not]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl <;> decide

/-! ### Preference orderings (§6.2, §6.3) -/

/-- State preference of the uncertainty listener is the pooled speaker preference. -/
theorem L1_fst_real_lt_iff (m : Msg) (w₁ w₂ : World) :
    (L1 α κ m).fst.real {w₁} < (L1 α κ m).fst.real {w₂} ↔
      ∑ l, (S1 α κ l w₁).real {m} < ∑ l, (S1 α κ l w₂).real {m} :=
  let ⟨w₀, h₀⟩ := sem_weak_nonempty m
  familyListener_fst_real_lt_iff L0 uniformOn_univ_singleton_eq uniformOn_univ_singleton_ne_zero
    ((speaker_uniformListener_apply_singleton_ne_zero_iff (sem .weak) hα (cost_ne_zero hκ)
      (cost_ne_top κ) w₀ m).2 h₀)

/-- State preference of the fixed-lexicon listener is the base-lexicon speaker's preference. -/
theorem L1fixed_real_lt_iff (m : Msg) (w₁ w₂ : World) :
    (L1fixed α κ m).real {w₁} < (L1fixed α κ m).real {w₂} ↔
      (S1 α κ .weak w₁).real {m} < (S1 α κ .weak w₂).real {m} :=
  let ⟨w₀, h₀⟩ := sem_weak_nonempty m
  pragmaticListener_real_lt_iff α (cost κ) (L0 .weak) (uniformOn Set.univ)
    uniformOn_univ_singleton_eq uniformOn_univ_singleton_ne_zero
    ((speaker_uniformListener_apply_singleton_ne_zero_iff (sem .weak) hα (cost_ne_zero hκ)
      (cost_ne_top κ) w₀ m).2 h₀)

omit hκ in
/-- The speaker's share of a statement: its informativity weight over the weights of the
statements true at the state plus the null message's weight. -/
theorem S1_real (l : Lex) (w : World) (s : Stmt) :
    (S1 α κ l w).real {some s}
      = (if w ∈ stmtSem l s then (((stmtSem l s).card : ℝ))⁻¹ ^ α else 0)
        / ((∑ s', if w ∈ stmtSem l s' then (((stmtSem l s').card : ℝ))⁻¹ ^ α else 0)
            + κ * (10 : ℝ)⁻¹ ^ α) := by
  have h := speaker_liftCostFactor_uniformListener_real_singleton_some (stmtSem l) hα
    (ENNReal.coe_ne_top (r := κ)) w s
  rw [profile_invPowSum_toReal _ hα.le, ENNReal.coe_toReal,
    (by decide : Fintype.card World = 10), Nat.cast_ofNat] at h
  exact h

end Model

/-! #### The weights and the sums -/

/-- The two lexica as `Fin 2`, for sums over the family. -/
def Lex.equivFin : Lex ≃ Fin 2 where
  toFun | .weak => 0 | .strong => 1
  invFun | 0 => .weak | 1 => .strong
  left_inv l := by cases l <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-- The quantifiers over players as `Fin 3`. -/
def PlayerQ.equivFin : PlayerQ ≃ Fin 3 where
  toFun | .every => 0 | .exactlyOne => 1 | .no => 2
  invFun | 0 => .every | 1 => .exactlyOne | 2 => .no
  left_inv q := by cases q <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-- The quantifiers over shots as `Fin 3`. -/
def ShotQ.equivFin : ShotQ ≃ Fin 3 where
  toFun | .every => 0 | .no => 1 | .some_ => 2
  invFun | 0 => .every | 1 => .no | 2 => .some_
  left_inv s := by cases s <;> rfl
  right_inv i := by fin_cases i <;> rfl

theorem Lex.sum_univ {M : Type*} [AddCommMonoid M] (f : Lex → M) :
    ∑ l, f l = f .weak + f .strong := by
  rw [Fintype.sum_equiv Lex.equivFin f (f ∘ Lex.equivFin.symm) λ l => by simp,
    Fin.sum_univ_two]
  rfl

theorem PlayerQ.sum_univ {M : Type*} [AddCommMonoid M] (f : PlayerQ → M) :
    ∑ q, f q = f .every + f .exactlyOne + f .no := by
  rw [Fintype.sum_equiv PlayerQ.equivFin f (f ∘ PlayerQ.equivFin.symm) λ q => by simp,
    Fin.sum_univ_three]
  rfl

theorem ShotQ.sum_univ {M : Type*} [AddCommMonoid M] (f : ShotQ → M) :
    ∑ s, f s = f .every + f .no + f .some_ := by
  rw [Fintype.sum_equiv ShotQ.equivFin f (f ∘ ShotQ.equivFin.symm) λ s => by simp,
    Fin.sum_univ_three]
  rfl

/-- The extension sizes of the statements. -/
private theorem cards :
    (stmtSem .weak (.every, .every)).card = 1 ∧ (stmtSem .strong (.every, .every)).card = 1 ∧
    (stmtSem .weak (.every, .no)).card = 1 ∧ (stmtSem .strong (.every, .no)).card = 1 ∧
    (stmtSem .weak everySome).card = 4 ∧ (stmtSem .strong everySome).card = 1 ∧
    (stmtSem .weak (.exactlyOne, .every)).card = 3 ∧
    (stmtSem .strong (.exactlyOne, .every)).card = 3 ∧
    (stmtSem .weak (.exactlyOne, .no)).card = 3 ∧ (stmtSem .strong (.exactlyOne, .no)).card = 3 ∧
    (stmtSem .weak oneSome).card = 2 ∧ (stmtSem .strong oneSome).card = 3 ∧
    (stmtSem .weak (.no, .every)).card = 4 ∧ (stmtSem .strong (.no, .every)).card = 4 ∧
    (stmtSem .weak (.no, .no)).card = 4 ∧ (stmtSem .strong (.no, .no)).card = 4 ∧
    (stmtSem .weak noSome).card = 1 ∧ (stmtSem .strong noSome).card = 4 := by
  decide

section Findings

variable {α : ℝ} (hα : 0 < α) {κ : ℝ≥0} (hκ : κ ≠ 0)
include hα hκ

/-- The informativity weights `4^{-α} < 3^{-α} < 2^{-α} < 1`, positive, and the null message's
nonnegative weight. -/
private theorem weights :
    0 < (4 : ℝ)⁻¹ ^ α ∧ (4 : ℝ)⁻¹ ^ α < (3 : ℝ)⁻¹ ^ α ∧ (3 : ℝ)⁻¹ ^ α < (2 : ℝ)⁻¹ ^ α ∧
      (2 : ℝ)⁻¹ ^ α < 1 ∧ 0 ≤ (κ : ℝ) * (10 : ℝ)⁻¹ ^ α :=
  ⟨Real.rpow_pos_of_pos (by norm_num) α, Real.rpow_lt_rpow (by norm_num) (by norm_num) hα,
    Real.rpow_lt_rpow (by norm_num) (by norm_num) hα,
    Real.rpow_lt_one (by norm_num) (by norm_num) hα, by positivity⟩

/-- *Every player hit some of his shots*: the uncertainty listener ranks the locally enriched
SSS above the other true states and AAA below the two remaining ones, the ordering of the human
responses. -/
theorem every_some_ordering :
    (L1 α κ (some everySome)).fst.real {.SSA} < (L1 α κ (some everySome)).fst.real {.SSS} ∧
    (L1 α κ (some everySome)).fst.real {.SAA} < (L1 α κ (some everySome)).fst.real {.SSS} ∧
    (L1 α κ (some everySome)).fst.real {.AAA} < (L1 α κ (some everySome)).fst.real {.SSA} ∧
    (L1 α κ (some everySome)).fst.real {.AAA} < (L1 α κ (some everySome)).fst.real {.SAA} := by
  obtain ⟨ha, hab, hbc, hc1, ht⟩ := weights hα hκ
  have ha1 : (4 : ℝ)⁻¹ ^ α < 1 := hab.trans (hbc.trans hc1)
  obtain ⟨c1, c2, -, -, c5, c6, c7, c8, -, -, -, c12, c13, c14, c15, c16, -, c18⟩ := cards
  simp +decide only [L1_fst_real_lt_iff hα hκ, Lex.sum_univ, S1_real hα, Fintype.sum_prod_type,
    PlayerQ.sum_univ, ShotQ.sum_univ, c1, c2, c5, c6, c7, c8, c12, c13, c14, c15, c16, c18,
    Nat.cast_ofNat, Nat.cast_one, inv_one, Real.one_rpow, ↓reduceIte, add_zero, zero_add,
    zero_div]
  refine ⟨(div_lt_div_of_pos_left ha (by positivity) (by linarith)).trans_le
    (le_add_of_nonneg_right (by positivity)), ?_,
    div_lt_div_of_pos_left ha (by positivity) (by linarith),
    div_lt_div_of_pos_left ha (by positivity) (by linarith)⟩
  rw [div_add_div _ _ (by positivity) (by positivity), div_lt_div_iff₀ (by positivity)
    (by positivity)]
  nlinarith [mul_pos ha ha, mul_pos (mul_pos ha ha) (sub_pos.2 ha1), mul_nonneg ha.le ht,
    mul_nonneg (mul_nonneg ha.le ht) (sub_pos.2 ha1).le, mul_nonneg ht ht]

/-- The fixed-lexicon listener instead puts SAA above SSS. -/
theorem every_some_fixed :
    (L1fixed α κ (some everySome)).real {.SSS} < (L1fixed α κ (some everySome)).real {.SAA} := by
  obtain ⟨ha, -, -, -, -⟩ := weights hα hκ
  obtain ⟨-, -, -, -, c5, -, -, -, -, -, -, -, c13, -, c15, -, -, -⟩ := cards
  simp +decide only [L1fixed_real_lt_iff hα hκ, S1_real hα, Fintype.sum_prod_type,
    PlayerQ.sum_univ, ShotQ.sum_univ, c5, c13, c15, Nat.cast_ofNat, ↓reduceIte, add_zero,
    zero_add]
  exact div_lt_div_of_pos_left ha (by positivity) (by linarith)

/-- *Exactly one player hit some of his shots*: the literal construal NNS stays the most
preferred state, above NNA and above the locally enriched NSA and SAA. -/
theorem one_some_literal_first :
    (L1 α κ (some oneSome)).fst.real {.NNA} < (L1 α κ (some oneSome)).fst.real {.NNS} ∧
    (L1 α κ (some oneSome)).fst.real {.NSA} < (L1 α κ (some oneSome)).fst.real {.NNS} ∧
    (L1 α κ (some oneSome)).fst.real {.SAA} < (L1 α κ (some oneSome)).fst.real {.NNS} := by
  obtain ⟨ha, hab, hbc, -, -⟩ := weights hα hκ
  obtain ⟨-, -, -, -, c5, -, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, -, c18⟩ := cards
  simp +decide only [L1_fst_real_lt_iff hα hκ, Lex.sum_univ, S1_real hα, Fintype.sum_prod_type,
    PlayerQ.sum_univ, ShotQ.sum_univ, c5, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c18,
    Nat.cast_ofNat, ↓reduceIte, add_zero, zero_add, zero_div]
  exact ⟨(div_lt_div_of_pos_left (ha.trans (hab.trans hbc)) (by positivity) (by linarith)).trans_le
      (le_add_of_nonneg_right (by positivity)),
    (div_lt_div_of_pos_left (ha.trans hab) (by positivity) (by linarith)).trans_le
      (le_add_of_nonneg_left (by positivity)),
    lt_add_of_pos_left _ (by positivity)⟩

/-- *No player hit some of his shots*: the literal construal NNN stays the most preferred state,
above the locally enriched NNA, NAA and AAA. -/
theorem no_some_literal_first :
    (L1 α κ (some noSome)).fst.real {.NNA} < (L1 α κ (some noSome)).fst.real {.NNN} ∧
    (L1 α κ (some noSome)).fst.real {.NAA} < (L1 α κ (some noSome)).fst.real {.NNN} ∧
    (L1 α κ (some noSome)).fst.real {.AAA} < (L1 α κ (some noSome)).fst.real {.NNN} := by
  obtain ⟨ha, hab, -, -, ht⟩ := weights hα hκ
  obtain ⟨c1, c2, c3, c4, c5, -, c7, c8, c9, c10, c11, -, c13, c14, c15, c16, c17, c18⟩ := cards
  simp +decide only [L1_fst_real_lt_iff hα hκ, Lex.sum_univ, S1_real hα, Fintype.sum_prod_type,
    PlayerQ.sum_univ, ShotQ.sum_univ, c1, c2, c3, c4, c5, c7, c8, c9, c10, c11, c13, c14, c15,
    c16, c17, c18, Nat.cast_ofNat, Nat.cast_one, inv_one, Real.one_rpow, ↓reduceIte, add_zero,
    zero_add, zero_div]
  have hab' : 0 < (3 : ℝ)⁻¹ ^ α - (4 : ℝ)⁻¹ ^ α := sub_pos.2 hab
  have key : (4 : ℝ)⁻¹ ^ α / ((3 : ℝ)⁻¹ ^ α + (4 : ℝ)⁻¹ ^ α + κ * (10 : ℝ)⁻¹ ^ α)
      < 1 / (1 + ((4 : ℝ)⁻¹ ^ α + 1) + κ * (10 : ℝ)⁻¹ ^ α)
        + (4 : ℝ)⁻¹ ^ α / (1 + ((4 : ℝ)⁻¹ ^ α + (4 : ℝ)⁻¹ ^ α) + κ * (10 : ℝ)⁻¹ ^ α) := by
    rw [div_add_div _ _ (by positivity) (by positivity), div_lt_div_iff₀ (by positivity)
      (by positivity)]
    nlinarith [mul_pos ha ha, mul_pos (mul_pos ha ha) hab', mul_nonneg ha.le ht,
      mul_nonneg (mul_nonneg ha.le ht) hab'.le, mul_pos ha hab', mul_nonneg ht ht,
      mul_nonneg hab'.le ht]
  exact ⟨key, key, lt_add_of_pos_left _ (by positivity)⟩

end Findings

end PottsEtAl2016
