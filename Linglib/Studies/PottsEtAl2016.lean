import Linglib.Pragmatics.RSA.Rational
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
[chemla-spector-2011] report. At the paper's parameters the uncertainty listener still ranks
the literal construal first, NNS and NNN (`one_some_literal_first`, `no_some_literal_first`),
and for *every player hit some of his shots* mirrors the human ordering, SSS first and AAA last
among the true states, where the fixed-lexicon listener puts SAA first (`every_some_ordering`,
`every_some_fixed`).

## Implementation notes

The state and lexicon priors are flat and the rationality is 1, the setting of the model
assessment; the null message costs 5 (18d), the factor `exp (−5)` rationalized to `67/10000`,
and the other messages are free. Positivity is proved for every positive finite null-message
cost, and the orderings are certified at the rationalized cost through the register of
`Pragmatics/RSA/Rational`. The unconstrained
refinement model (19c), whose lexica are the nonempty subsets of the denotation of *some* over
sets of shots, and the fit to the response data are not formalized.

## References

* [potts-etal-2016]
* [chemla-spector-2011]
-/

open MeasureTheory ProbabilityTheory RSA
open scoped ENNReal NNRat

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

/-- The messages (18c): the statements and the null message of (12a). -/
abbrev Msg := WithSilence Stmt

instance : MeasurableSpace Msg := ⊤

/-- The extension of a message under a lexicon, the null message true at every state. -/
def sem (l : Lex) (m : Msg) : Finset World :=
  Finset.univ.filter (liftMeaning (Stmt.Truth l) m)

/-- *Every player hit some of his shots*. -/
abbrev everySome : Msg := some (.every, .some_)

/-- *Exactly one player hit some of his shots*. -/
abbrev oneSome : Msg := some (.exactlyOne, .some_)

/-- *No player hit some of his shots*. -/
abbrev noSome : Msg := some (.no, .some_)

/-- The lexica agree off *some*, and the refinement narrows the extension of *some* under
*every* while widening it under *no*, the source of the asymmetry; under *exactly one* the
refinement admits the locally enriched states NSA and SAA. -/
theorem refinement_facts :
    (∀ q : PlayerQ, sem .weak (some (q, .every)) = sem .strong (some (q, .every)) ∧
      sem .weak (some (q, .no)) = sem .strong (some (q, .no))) ∧
    sem .strong everySome ⊂ sem .weak everySome ∧ sem .weak noSome ⊂ sem .strong noSome ∧
    sem .weak oneSome = {.NNS, .NNA} ∧ sem .strong oneSome = {.NNS, .NSA, .SAA} := by
  decide

/-- Every message is true at some state under the base lexicon. -/
theorem sem_weak_nonempty (m : Msg) : ∃ w, w ∈ sem .weak m := by
  revert m; decide

/-! ### The model (13), (18), (19) -/

section Tower

variable (κ : ℝ≥0∞)

/-- The cost factor (18d): `κ` for the null message and 1 for every statement. -/
def cost : Msg → ℝ≥0∞ := liftCostFactor κ 1

/-- The literal listener (13a) at a flat prior: uniform on the message's extension. -/
noncomputable def L0 (l : Lex) : Kernel Msg World := uniformListener (sem l)

/-- The speaker (13b) at rationality 1. -/
noncomputable def S1 (l : Lex) : Kernel World Msg := speaker 1 (cost κ) (L0 l)

/-- The uncertainty listener (13c): the joint posterior over states and lexica at flat priors,
whose state marginal is the paper's listener. -/
noncomputable def L1 : Kernel Msg (World × Lex) :=
  familyListener L0 1 (cost κ) (uniformOn Set.univ)

/-- The fixed-lexicon pragmatic listener (19b): the base lexicon's speaker inverted at a flat
prior. -/
noncomputable def L1fixed : Kernel Msg World :=
  pragmaticListener 1 (cost κ) (L0 .weak) (uniformOn Set.univ)

end Tower

/-! ### Support: local enrichment (§6.3) -/

section Support

variable {κ : ℝ≥0∞}

private theorem cost_ne_zero (hκ : κ ≠ 0) (m : Msg) : cost κ m ≠ 0 := by
  cases m <;> simp [cost, hκ]

private theorem cost_ne_top (hκ' : κ ≠ ∞) (m : Msg) : cost κ m ≠ ∞ := by
  cases m <;> simp [cost, hκ']

variable (hκ : κ ≠ 0) (hκ' : κ ≠ ∞)
include hκ hκ'

/-- The uncertainty listener assigns mass to a state exactly when some lexicon makes the
message true there. -/
theorem L1_fst_ne_zero_iff (m : Msg) (w : World) :
    (L1 κ m).fst {w} ≠ 0 ↔ ∃ l, w ∈ sem l m :=
  familyListener_uniform_fst_apply_singleton_ne_zero_iff sem zero_lt_one (cost_ne_zero hκ)
    (cost_ne_top hκ') (let ⟨w, h⟩ := sem_weak_nonempty m; ⟨.weak, w, h⟩) w

/-- The fixed-lexicon listener assigns mass to a state exactly when the base lexicon makes the
message true there. -/
theorem L1fixed_ne_zero_iff (m : Msg) (w : World) : L1fixed κ m {w} ≠ 0 ↔ w ∈ sem .weak m := by
  obtain ⟨w₀, h₀⟩ := sem_weak_nonempty m
  have hs := speaker_uniformListener_apply_singleton_ne_zero_iff (sem .weak) zero_lt_one
    (cost_ne_zero hκ) (cost_ne_top hκ')
  rw [L1fixed, pragmaticListener, L0, posterior_apply_singleton_ne_zero_iff _ _
    (comp_apply_singleton_ne_zero _ _ (uniformOn_univ_singleton_ne_zero w₀) ((hs w₀ m).2 h₀)),
    and_iff_right (uniformOn_univ_singleton_ne_zero w), hs]

/-- *Exactly one player hit some of his shots*: the locally enriched states NSA and SAA, false
on the literal construal, receive mass from the uncertainty listener and none from the
fixed-lexicon listener. -/
theorem one_some_local :
    ∀ w ∈ ({.NSA, .SAA} : Finset World),
      (L1 κ oneSome).fst {w} ≠ 0 ∧ L1fixed κ oneSome {w} = 0 := by
  intro w hw
  rw [L1_fst_ne_zero_iff hκ hκ', ← not_ne_iff, (L1fixed_ne_zero_iff hκ hκ' _ w).not]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl <;> decide

/-- *No player hit some of his shots*: the locally enriched states NNA, NAA and AAA receive mass
from the uncertainty listener and none from the fixed-lexicon listener. -/
theorem no_some_local :
    ∀ w ∈ ({.NNA, .NAA, .AAA} : Finset World),
      (L1 κ noSome).fst {w} ≠ 0 ∧ L1fixed κ noSome {w} = 0 := by
  intro w hw
  rw [L1_fst_ne_zero_iff hκ hκ', ← not_ne_iff, (L1fixed_ne_zero_iff hκ hκ' _ w).not]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl <;> decide

end Support

/-! ### The rational face -/

/-- The rational cost factor. -/
def costq (κ : ℚ≥0) : Msg → ℚ≥0
  | some _ => 1
  | none => κ

/-- The literal listener's mass. -/
def l0q (l : Lex) (m : Msg) (w : World) : ℚ≥0 :=
  if w ∈ sem l m then ((sem l m).card : ℚ≥0)⁻¹ else 0

/-- The speaker's shares. -/
def s1q (κ : ℚ≥0) (l : Lex) (w : World) : Msg → ℚ≥0 := share λ m => l0q l m w * costq κ m

/-- The uncertainty listener's joint masses. -/
def L1q (κ : ℚ≥0) (m : Msg) : World × Lex → ℚ≥0 := share λ p => s1q κ p.2 p.1 m

/-- The uncertainty listener's state masses. -/
def L1worldq (κ : ℚ≥0) (m : Msg) (w : World) : ℚ≥0 := ∑ l, L1q κ m (w, l)

/-- The fixed-lexicon listener's masses. -/
def L1fixedq (κ : ℚ≥0) (m : Msg) : World → ℚ≥0 := share λ w => s1q κ .weak w m

/-- The rationalized cost factor of the null message, `exp (−5)` to two significant digits. -/
abbrev κ₀ : ℚ≥0 := 67 / 10000

/-- The cost factor at the rationalized cost. -/
abbrev K : ℝ≥0∞ := κ₀

private theorem s1_weight_ne_zero (l : Lex) (w : World) : ∑ m, l0q l m w * costq κ₀ m ≠ 0 := by
  revert l w; decide +kernel

private theorem s1q_sum_ne_zero (m : Msg) : ∑ w, s1q κ₀ .weak w m ≠ 0 := by
  revert m; decide +kernel

private theorem s1q_joint_sum_ne_zero (m : Msg) : ∑ p : World × Lex, s1q κ₀ p.2 p.1 m ≠ 0 := by
  revert m; decide +kernel

theorem cost_coe (κ : ℚ≥0) (m : Msg) : cost κ m = (costq κ m : ℝ≥0∞) := by
  cases m <;> simp [cost, costq]

theorem L0_apply (l : Lex) (m : Msg) (w : World) : L0 l m {w} = (l0q l m w : ℝ≥0∞) :=
  uniformListener_nnratCast_apply_singleton (sem l) m w

theorem S1_apply (l : Lex) (w : World) (m : Msg) : S1 K l w {m} = (s1q κ₀ l w m : ℝ≥0∞) :=
  speaker_one_nnratCast_apply_singleton (cost_coe κ₀) (L0_apply l) (s1_weight_ne_zero l w) m

theorem L1_fst_apply (m : Msg) (w : World) : (L1 K m).fst {w} = (L1worldq κ₀ m w : ℝ≥0∞) :=
  familyListener_uniformOn_nnratCast_fst_apply_singleton L0 1 (cost K)
    (λ p m => S1_apply p.2 p.1 m) (s1q_joint_sum_ne_zero m) w

theorem L1fixed_apply (m : Msg) (w : World) : L1fixed K m {w} = (L1fixedq κ₀ m w : ℝ≥0∞) :=
  pragmaticListener_uniformOn_nnratCast_apply_singleton 1 (cost K) (L0 .weak) (S1_apply .weak)
    (s1q_sum_ne_zero m) w

/-! ### Preference orderings at the paper's parameters (§6.2, §6.3) -/

/-- *Every player hit some of his shots*: the uncertainty listener ranks the locally enriched
SSS above every other state and AAA below the two other literally true states, the ordering of
the human responses. -/
theorem every_some_ordering :
    (∀ w ≠ World.SSS,
      (L1 K everySome).fst.real {w} < (L1 K everySome).fst.real {.SSS}) ∧
    (L1 K everySome).fst.real {.AAA} < (L1 K everySome).fst.real {.SSA} ∧
    (L1 K everySome).fst.real {.AAA} < (L1 K everySome).fst.real {.SAA} := by
  simp only [measureReal_def, L1_fst_apply, ENNReal.toReal_nnratCast]
  exact ⟨λ w hw => NNRat.cast_lt.2 (by revert w; decide +kernel),
    NNRat.cast_lt.2 (by decide +kernel), NNRat.cast_lt.2 (by decide +kernel)⟩

/-- The fixed-lexicon listener instead puts SAA above SSS. -/
theorem every_some_fixed :
    (L1fixed K everySome).real {.SSS} < (L1fixed K everySome).real {.SAA} := by
  simp only [measureReal_def, L1fixed_apply, ENNReal.toReal_nnratCast]
  exact NNRat.cast_lt.2 (by decide +kernel)

/-- *Exactly one player hit some of his shots*: the literal construal NNS stays the most
preferred state, local enrichment being available without being preferred. -/
theorem one_some_literal_first :
    ∀ w ≠ World.NNS, (L1 K oneSome).fst.real {w} < (L1 K oneSome).fst.real {.NNS} := by
  intro w hw
  simp only [measureReal_def, L1_fst_apply, ENNReal.toReal_nnratCast]
  exact NNRat.cast_lt.2 (by revert w; decide +kernel)

/-- *No player hit some of his shots*: the literal construal NNN stays the most preferred
state. -/
theorem no_some_literal_first :
    ∀ w ≠ World.NNN, (L1 K noSome).fst.real {w} < (L1 K noSome).fst.real {.NNN} := by
  intro w hw
  simp only [measureReal_def, L1_fst_apply, ENNReal.toReal_nnratCast]
  exact NNRat.cast_lt.2 (by revert w; decide +kernel)

end PottsEtAl2016
