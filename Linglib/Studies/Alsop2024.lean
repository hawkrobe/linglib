import Linglib.Pragmatics.RSA.Canonical
import Linglib.Data.Examples.Alsop2024

/-!
# Alsop (2024): the pragmatics of free choice *any*

*You may read any book* does not entail that each book may be read on its own — the
exclusiveness reading Menéndez-Benito observes and Dayal's Viability Constraint builds in:
symmetric predicates (3) and world knowledge (22) block it and (23) cancels it, so on
Szabolcsi's Revised Viability Constraint semantics it is a robust implicature. The two
constraints are the two licit exhaustified parses (34a)–(34b) of the utterance (`meaning`,
Table 2), and a Global Intentions listener resolves which parse a speaker intended: the
speaker chooses an utterance–parse pair (`speaker`), and the listener recovers state and
parse from the utterance alone (`listener`).

At a uniform prior the strong parse (34b) is the speaker's choice at the exclusiveness
states for every exponent (`speaker_prefers_strong_parse`), so hearing *may any* puts the
posterior on Only 1 and Any # (`exclusiveness_derived`, Table 3) with the strong parse
inferred (`listener_infers_strong_parse`), while *may S* communicates Only S
(`literal_s_communicates_onlyS`). The parse (35b) of *may every*, true at Any # but not at
Only 1, makes Only 1 the strictly likelier of the two (`only1_over_anyNum`) — the asymmetry
behind the *not every* implicature, which Table 3 rounds to 0.50/0.50. The prior
manipulations of Tables 5–9 are outside the parameter-free statements here.

## References

* [alsop-2024]
* [menendez-benito-2010]
* [dayal-2013]
* [szabolcsi-2019]
* [chierchia-2013]
* [champollion-alsop-grosu-2019]
* [franke-bergen-2020]
* [xiang-2020]
-/

namespace Alsop2024

open scoped ENNReal
open RSA.Canonical Data.Examples

/-! ### States, utterances, parses (Tables 1–2) -/

/-- The seven permission states (Table 1): the accessible worlds among taking nothing, only
Semantics, only Phonology, or both; taking nothing is always accessible. -/
inductive State where
  | onlyS | onlyP | only1 | anyNum | only2 | sOr2 | pOr2
  deriving DecidableEq, Repr, Fintype, Inhabited

/-- The four utterances (31). -/
inductive Utterance where
  | mayS | mayP | mayAny | mayEvery
  deriving DecidableEq, Repr, Fintype

/-- The twelve utterance–parse pairs (32)–(35), `a` the weakest parse of each utterance.
*May any* has two: the weak parse (34a), Szabolcsi's meaning, and the strong parse (34b),
Dayal's. -/
inductive Parse where
  | sA | sB | sC
  | pA | pB | pC
  | anyA | anyB
  | evA | evB | evC | evD
  deriving DecidableEq, Repr, Fintype

/-- The utterance a parse belongs to. -/
def Parse.utt : Parse → Utterance
  | .sA | .sB | .sC => .mayS
  | .pA | .pB | .pC => .mayP
  | .anyA | .anyB => .mayAny
  | .evA | .evB | .evC | .evD => .mayEvery

/-- The states at which each parse is true (Table 2). -/
def meaning : Parse → State → Prop
  | .sA, s => s ≠ .onlyP
  | .sB, s => s = .onlyS ∨ s = .only1 ∨ s = .anyNum ∨ s = .sOr2
  | .sC, s => s = .onlyS
  | .pA, s => s ≠ .onlyS
  | .pB, s => s = .onlyP ∨ s = .only1 ∨ s = .anyNum ∨ s = .pOr2
  | .pC, s => s = .onlyP
  | .anyA, s => s ≠ .onlyS ∧ s ≠ .onlyP
  | .anyB, s => s = .only1 ∨ s = .anyNum
  | .evA, s => s ≠ .onlyS ∧ s ≠ .onlyP
  | .evB, s => s = .anyNum ∨ s = .only2 ∨ s = .sOr2 ∨ s = .pOr2
  | .evC, s => s = .only1 ∨ s = .anyNum
  | .evD, s => s = .only2

instance (p : Parse) : DecidablePred (meaning p) := fun _ => by
  cases p <;> unfold meaning <;> infer_instance

/-- *May any* is literally true at a state when some parse of it is. -/
def LiterallyTrue (s : State) : Prop := ∃ p, p.utt = .mayAny ∧ meaning p s

instance : DecidablePred LiterallyTrue := fun _ => inferInstanceAs (Decidable (∃ _, _ ∧ _))

/-- The strong parse (34b) entails the weak parse (34a), so *may any* is literally true
exactly where Szabolcsi's meaning holds. -/
theorem literallyTrue_iff (s : State) : LiterallyTrue s ↔ meaning .anyA s := by
  revert s; decide

theorem anyA_of_anyB (s : State) (h : meaning .anyB s) : meaning .anyA s := by
  revert s h; decide

private theorem ext_nonempty : ∀ (_ : Unit) (p : Parse),
    (RSA.extensionOf (fun q => meaning q) p).Nonempty := by
  intro _ p
  cases p <;> decide

/-! ### The Global Intentions model (36)–(41) -/

/-- The literal listener for a parse (36) at a uniform state prior: uniform on the parse's
extension. -/
noncomputable abbrev l0 : Unit → Parse → PMF State :=
  L0OfPred (fun _ p => meaning p) ext_nonempty

instance (α : ℕ) : ViableSpeaker (powUtility α l0) :=
  viableSpeaker_powUtility_of_witness α l0 fun s => by
    obtain ⟨w, ⟨⟩⟩ := s
    cases w
    · exact ⟨.sA, L0OfPred_ne_zero _ _ (by decide)⟩
    · exact ⟨.pA, L0OfPred_ne_zero _ _ (by decide)⟩
    · exact ⟨.anyB, L0OfPred_ne_zero _ _ (by decide)⟩
    · exact ⟨.anyB, L0OfPred_ne_zero _ _ (by decide)⟩
    · exact ⟨.evD, L0OfPred_ne_zero _ _ (by decide)⟩
    · exact ⟨.evB, L0OfPred_ne_zero _ _ (by decide)⟩
    · exact ⟨.evB, L0OfPred_ne_zero _ _ (by decide)⟩

/-- The speaker's joint choice of utterance and parse (37)–(38): `S1(u,p|s) ∝ L0(s|u,p)^α`
at equal costs. -/
noncomputable abbrev speaker (α : ℕ) (s : State) : PMF Parse := S1 (powUtility α l0) (s, ())

/-- The speaker's utterance choice (39), marginalizing over parses. -/
noncomputable def speakerU (α : ℕ) (s : State) (u : Utterance) : ℝ≥0∞ :=
  ∑ p with p.utt = u, speaker α s p

/-- The uniform state prior. -/
noncomputable abbrev prior : PMF State := PMF.uniformOfFintype State

theorem marginal_ne_zero (α : ℕ) (u : Utterance) :
    PMF.marginal (fun s => (speaker α s).map Parse.utt) prior u ≠ 0 := by
  have key : ∀ (s : State) (p : Parse), p.utt = u → meaning p s → _ := fun s p hpu hps =>
    L1Intent_uniform_marginal_ne_zero Parse.utt (speaker α)
      (S1_ne_zero (powUtility α l0)
        (PMF.coe_mul_log_ne_bot (by positivity) (L0OfPred_ne_zero _ _ hps))) hpu
  cases u
  · exact key .onlyS .sA rfl (by decide)
  · exact key .onlyP .pA rfl (by decide)
  · exact key .only1 .anyB rfl (by decide)
  · exact key .only2 .evD rfl (by decide)

/-- The pragmatic listener (40): the joint posterior over state and intended parse given
the utterance. -/
noncomputable def listener (α : ℕ) (u : Utterance) : PMF (State × Parse) :=
  L1Intent Parse.utt (speaker α) prior u (marginal_ne_zero α u)

/-- The event that the state lies in `A`. -/
abbrev stateEvent (A : Finset State) : Set (State × Parse) := ↑(A ×ˢ (Finset.univ : Finset Parse))

/-- The event that the intended parse lies in `P`. -/
abbrev parseEvent (P : Finset Parse) : Set (State × Parse) := ↑((Finset.univ : Finset State) ×ˢ P)

/-- Comparing the listener's posterior over sets of states (41) reduces to comparing summed
speaker utterance probabilities. -/
theorem listener_state_lt_iff (α : ℕ) (u : Utterance) (A B : Finset State) :
    (listener α u).toOuterMeasure (stateEvent A) < (listener α u).toOuterMeasure (stateEvent B)
      ↔ (∑ s ∈ A, speakerU α s u) < ∑ s ∈ B, speakerU α s u := by
  rw [listener, stateEvent, stateEvent, L1Intent_uniform_event_lt_iff]
  simp only [speakerU, Finset.sum_filter, Finset.sum_product]

private theorem speakerU_mayAny (α : ℕ) (s : State) :
    speakerU α s .mayAny = speaker α s .anyA + speaker α s .anyB := by
  rw [speakerU,
      show Finset.univ.filter (fun p => Parse.utt p = .mayAny) = {Parse.anyA, Parse.anyB}
        from by decide,
      Finset.sum_insert (by decide), Finset.sum_singleton]

private theorem speakerU_mayS (α : ℕ) (s : State) :
    speakerU α s .mayS = speaker α s .sA + (speaker α s .sB + speaker α s .sC) := by
  rw [speakerU,
      show Finset.univ.filter (fun p => Parse.utt p = .mayS) = {Parse.sA, Parse.sB, Parse.sC}
        from by decide,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]

/-! ### Extension sizes (Table 2 row sums) -/

private theorem card_sA : (RSA.extensionOf (fun p => meaning p) Parse.sA).card = 6 := by decide
private theorem card_sB : (RSA.extensionOf (fun p => meaning p) Parse.sB).card = 4 := by decide
private theorem card_anyA : (RSA.extensionOf (fun p => meaning p) Parse.anyA).card = 5 := by
  decide
private theorem card_anyB : (RSA.extensionOf (fun p => meaning p) Parse.anyB).card = 2 := by
  decide
private theorem card_evB : (RSA.extensionOf (fun p => meaning p) Parse.evB).card = 4 := by decide
private theorem card_evD : (RSA.extensionOf (fun p => meaning p) Parse.evD).card = 1 := by decide

/-! ### *May any* and *may every* exclude the single-class states -/

private theorem speaker_eq_zero {α : ℕ} (hα : α ≠ 0) {s : State} {p : Parse}
    (h : ¬ meaning p s) : speaker α s p = 0 :=
  S1_powUtility_eq_zero α l0 hα (L0OfPred_eq_zero _ _ h)

/-- Hearing *may any*, the listener assigns no posterior to Only S under any parse. -/
theorem mayAny_rules_out_onlyS {α : ℕ} (hα : α ≠ 0) (p : Parse) :
    listener α .mayAny (.onlyS, p) = 0 := by
  rw [listener, L1Intent, PMF.emissionPosterior_apply]
  split_ifs with h
  · rw [speaker_eq_zero hα (by revert h; cases p <;> decide), mul_zero, zero_mul]
  · exact zero_mul _

/-- Hearing *may every*, the listener assigns no posterior to Only S under any parse. -/
theorem mayEvery_rules_out_onlyS {α : ℕ} (hα : α ≠ 0) (p : Parse) :
    listener α .mayEvery (.onlyS, p) = 0 := by
  rw [listener, L1Intent, PMF.emissionPosterior_apply]
  split_ifs with h
  · rw [speaker_eq_zero hα (by revert h; cases p <;> decide), mul_zero, zero_mul]
  · exact zero_mul _

/-! ### The mechanism: the strong parse wins -/

/-- At an exclusiveness state the speaker prefers the strong parse (34b) of *may any* to
the weak parse (34a) for every exponent: the weak parse is true in five states, the strong
in two, and within one state the softmax partition cancels. At `α = 100` the ratio is
`(5/2)^100`, the paper's "almost 100% of the time". -/
theorem speaker_prefers_strong_parse {α : ℕ} (hα : α ≠ 0) {s : State} (hs : meaning .anyB s) :
    speaker α s .anyA < speaker α s .anyB := by
  rw [speaker, S1_powUtility_eq_normalize, PMF.normalize_apply, PMF.normalize_apply,
      ENNReal.mul_lt_mul_iff_left
        (ENNReal.inv_ne_zero.mpr (tsum_powWeight_ne_top α l0 _))
        (ENNReal.inv_ne_top.mpr (tsum_powWeight_ne_zero α l0 _)),
      powWeight_L0OfPred_of_mem (fun _ q => meaning q) ext_nonempty 5 (anyA_of_anyB s hs) card_anyA,
      powWeight_L0OfPred_of_mem (fun _ q => meaning q) ext_nonempty 2 hs card_anyB]
  exact ENNReal.pow_lt_pow_left hα (ENNReal.inv_lt_inv' (show (2 : ℝ≥0∞) < 5 by norm_num))

/-! ### Exclusiveness (Table 3, uniform prior, α = 100)

Per-state speaker bounds: at the exclusiveness states the strong parse alone gives *may
any* more than a third of the speaker's mass; at the non-exclusive states only the weak
parse survives and is dominated. -/

private theorem inv_pow_le_inv_pow {a b : ℕ} (h : a ≤ b) (n : ℕ) :
    ((b : ℝ≥0∞)⁻¹) ^ n ≤ ((a : ℝ≥0∞)⁻¹) ^ n :=
  pow_le_pow_left' (ENNReal.inv_le_inv' (by exact_mod_cast h)) n

private theorem third_lt_speaker_only1 :
    ((2 : ℝ≥0∞) + 1)⁻¹ < speaker 100 .only1 .anyB := by
  refine inv_succ_lt_S1_powUtility (n := 2) 100 l0 (s := (State.only1, ())) (a := Parse.anyB) ?_
  rw [show Finset.univ.erase Parse.anyB
        = {Parse.sA, Parse.sB, Parse.sC, Parse.pA, Parse.pB, Parse.pC,
           Parse.anyA, Parse.evA, Parse.evB, Parse.evC, Parse.evD}
      from by decide,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton,
      powWeight_L0OfPred_of_mem _ _ 6 (by decide) card_sA,
      powWeight_L0OfPred_of_mem _ _ 4 (by decide) card_sB,
      powWeight_L0OfPred_of_not_mem _ _ (by norm_num) (by decide),
      powWeight_L0OfPred_of_mem _ _ 6 (by decide) (by decide),
      powWeight_L0OfPred_of_mem _ _ 4 (by decide) (by decide),
      powWeight_L0OfPred_of_not_mem _ _ (by norm_num) (by decide),
      powWeight_L0OfPred_of_mem _ _ 5 (by decide) card_anyA,
      powWeight_L0OfPred_of_mem _ _ 5 (by decide) (by decide),
      powWeight_L0OfPred_of_not_mem _ _ (by norm_num) (by decide),
      powWeight_L0OfPred_of_mem _ _ 2 (by decide) (by decide),
      powWeight_L0OfPred_of_not_mem _ _ (by norm_num) (by decide),
      powWeight_L0OfPred_of_mem _ _ 2 (by decide) card_anyB]
  -- 2·6⁻¹⁰⁰ + 2·4⁻¹⁰⁰ + 2·5⁻¹⁰⁰ + 2⁻¹⁰⁰ < 2·2⁻¹⁰⁰
  calc _ = (2 : ℝ≥0∞) * ((6 : ℝ≥0∞)⁻¹) ^ 100 + 2 * ((4 : ℝ≥0∞)⁻¹) ^ 100
        + 2 * ((5 : ℝ≥0∞)⁻¹) ^ 100 + ((2 : ℝ≥0∞)⁻¹) ^ 100 := by ring_nf
    _ ≤ 2 * ((4 : ℝ≥0∞)⁻¹) ^ 100 + 2 * ((4 : ℝ≥0∞)⁻¹) ^ 100
        + 2 * ((4 : ℝ≥0∞)⁻¹) ^ 100 + ((2 : ℝ≥0∞)⁻¹) ^ 100 := by
        refine add_le_add (add_le_add (add_le_add ?_ le_rfl) ?_) le_rfl <;>
          exact mul_le_mul_right (inv_pow_le_inv_pow (by norm_num) 100) 2
    _ = (6 : ℝ≥0∞) * ((4 : ℝ≥0∞)⁻¹) ^ 100 + ((2 : ℝ≥0∞)⁻¹) ^ 100 := by ring
    _ < ((2 : ℝ≥0∞)⁻¹) ^ 100 + ((2 : ℝ≥0∞)⁻¹) ^ 100 :=
        ENNReal.add_lt_add_right (ENNReal.pow_ne_top (by norm_num))
          (ENNReal.natCast_mul_inv_pow_lt (by norm_num) (by norm_num) (by norm_num))
    _ = 2 * ((2 : ℝ≥0∞)⁻¹) ^ 100 := (two_mul _).symm

private theorem third_lt_speaker_anyNum :
    ((2 : ℝ≥0∞) + 1)⁻¹ < speaker 100 .anyNum .anyB := by
  refine inv_succ_lt_S1_powUtility (n := 2) 100 l0 (s := (State.anyNum, ())) (a := Parse.anyB) ?_
  rw [show Finset.univ.erase Parse.anyB
        = {Parse.sA, Parse.sB, Parse.sC, Parse.pA, Parse.pB, Parse.pC,
           Parse.anyA, Parse.evA, Parse.evB, Parse.evC, Parse.evD}
      from by decide,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton,
      powWeight_L0OfPred_of_mem _ _ 6 (by decide) card_sA,
      powWeight_L0OfPred_of_mem _ _ 4 (by decide) card_sB,
      powWeight_L0OfPred_of_not_mem _ _ (by norm_num) (by decide),
      powWeight_L0OfPred_of_mem _ _ 6 (by decide) (by decide),
      powWeight_L0OfPred_of_mem _ _ 4 (by decide) (by decide),
      powWeight_L0OfPred_of_not_mem _ _ (by norm_num) (by decide),
      powWeight_L0OfPred_of_mem _ _ 5 (by decide) card_anyA,
      powWeight_L0OfPred_of_mem _ _ 5 (by decide) (by decide),
      powWeight_L0OfPred_of_mem _ _ 4 (by decide) card_evB,
      powWeight_L0OfPred_of_mem _ _ 2 (by decide) (by decide),
      powWeight_L0OfPred_of_not_mem _ _ (by norm_num) (by decide),
      powWeight_L0OfPred_of_mem _ _ 2 (by decide) card_anyB]
  -- 2·6⁻¹⁰⁰ + 3·4⁻¹⁰⁰ + 2·5⁻¹⁰⁰ + 2⁻¹⁰⁰ < 2·2⁻¹⁰⁰ (the extra 4⁻¹⁰⁰: parse (35b))
  calc _ = (2 : ℝ≥0∞) * ((6 : ℝ≥0∞)⁻¹) ^ 100 + 3 * ((4 : ℝ≥0∞)⁻¹) ^ 100
        + 2 * ((5 : ℝ≥0∞)⁻¹) ^ 100 + ((2 : ℝ≥0∞)⁻¹) ^ 100 := by ring_nf
    _ ≤ 2 * ((4 : ℝ≥0∞)⁻¹) ^ 100 + 3 * ((4 : ℝ≥0∞)⁻¹) ^ 100
        + 2 * ((4 : ℝ≥0∞)⁻¹) ^ 100 + ((2 : ℝ≥0∞)⁻¹) ^ 100 := by
        refine add_le_add (add_le_add (add_le_add ?_ le_rfl) ?_) le_rfl
        · exact mul_le_mul_right (inv_pow_le_inv_pow (by norm_num) 100) 2
        · exact mul_le_mul_right (inv_pow_le_inv_pow (by norm_num) 100) 2
    _ = (7 : ℝ≥0∞) * ((4 : ℝ≥0∞)⁻¹) ^ 100 + ((2 : ℝ≥0∞)⁻¹) ^ 100 := by ring
    _ < ((2 : ℝ≥0∞)⁻¹) ^ 100 + ((2 : ℝ≥0∞)⁻¹) ^ 100 :=
        ENNReal.add_lt_add_right (ENNReal.pow_ne_top (by norm_num))
          (ENNReal.natCast_mul_inv_pow_lt (by norm_num) (by norm_num) (by norm_num))
    _ = 2 * ((2 : ℝ≥0∞)⁻¹) ^ 100 := (two_mul _).symm

/-- The weak parse is dominated wherever another parse has a smaller extension. -/
private theorem speaker_anyA_lt_ninth {s : State} {p : Parse} {k : ℕ} (hp : p ≠ .anyA)
    (hs : meaning .anyA s) (hps : meaning p s)
    (hk : (RSA.extensionOf (fun q => meaning q) p).card = k) (hcert : 8 * k ^ 100 < 5 ^ 100) :
    speaker 100 s .anyA < ((8 : ℝ≥0∞) + 1)⁻¹ :=
  S1_L0OfPred_lt_inv_succ_of_dominator _ _ (Ne.symm hp) hs hps card_anyA hk (by norm_num) hcert

private theorem speaker_only1_anyA_lt : speaker 100 .only1 .anyA < ((8 : ℝ≥0∞) + 1)⁻¹ :=
  speaker_anyA_lt_ninth (p := .anyB) (by decide) (by decide) (by decide) card_anyB (by norm_num)

private theorem speaker_anyNum_anyA_lt : speaker 100 .anyNum .anyA < ((8 : ℝ≥0∞) + 1)⁻¹ :=
  speaker_anyA_lt_ninth (p := .anyB) (by decide) (by decide) (by decide) card_anyB (by norm_num)

private theorem speaker_only2_anyA_lt : speaker 100 .only2 .anyA < ((8 : ℝ≥0∞) + 1)⁻¹ :=
  speaker_anyA_lt_ninth (p := .evD) (by decide) (by decide) (by decide) card_evD (by norm_num)

private theorem speaker_sOr2_anyA_lt : speaker 100 .sOr2 .anyA < ((8 : ℝ≥0∞) + 1)⁻¹ :=
  speaker_anyA_lt_ninth (p := .evB) (by decide) (by decide) (by decide) card_evB (by norm_num)

private theorem speaker_pOr2_anyA_lt : speaker 100 .pOr2 .anyA < ((8 : ℝ≥0∞) + 1)⁻¹ :=
  speaker_anyA_lt_ninth (p := .evB) (by decide) (by decide) (by decide) card_evB (by norm_num)

private theorem speakerU_nonexclusive_lt {s : State} (hs : ¬ meaning .anyB s)
    (h : speaker 100 s .anyA < ((8 : ℝ≥0∞) + 1)⁻¹) :
    speakerU 100 s .mayAny < ((8 : ℝ≥0∞) + 1)⁻¹ := by
  rwa [speakerU_mayAny, speaker_eq_zero (by norm_num) hs, add_zero]

private theorem three_ninths_lt_two_thirds :
    ((8 : ℝ≥0∞) + 1)⁻¹ + (((8 : ℝ≥0∞) + 1)⁻¹ + ((8 : ℝ≥0∞) + 1)⁻¹)
      < ((2 : ℝ≥0∞) + 1)⁻¹ + ((2 : ℝ≥0∞) + 1)⁻¹ := by
  rw [show ((8 : ℝ≥0∞) + 1) = 9 from by norm_num, show ((2 : ℝ≥0∞) + 1) = 3 from by norm_num,
      show (9 : ℝ≥0∞)⁻¹ + ((9 : ℝ≥0∞)⁻¹ + (9 : ℝ≥0∞)⁻¹) = 3 * 9⁻¹ from by ring,
      show (9 : ℝ≥0∞) = 3 * 3 from by norm_num,
      ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num)),
      ← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
  exact ENNReal.lt_add_right (ENNReal.inv_ne_top.mpr (by norm_num))
    (ENNReal.inv_ne_zero.mpr (by norm_num))

/-- **The exclusiveness implicature** (Table 3): hearing *may any* at a uniform prior, the
listener puts more posterior mass on the exclusiveness states Only 1 and Any #, where each
class may be taken on its own (the paper's 0.50 + 0.50), than on Only 2, S or 2, and P or 2
(each ≈ 0). -/
theorem exclusiveness_derived :
    (listener 100 .mayAny).toOuterMeasure (stateEvent {.only2, .sOr2, .pOr2})
      < (listener 100 .mayAny).toOuterMeasure (stateEvent {.only1, .anyNum}) := by
  rw [listener_state_lt_iff, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton, Finset.sum_insert (by decide), Finset.sum_singleton]
  refine (ENNReal.add_lt_add (speakerU_nonexclusive_lt (by decide) speaker_only2_anyA_lt)
    (ENNReal.add_lt_add (speakerU_nonexclusive_lt (by decide) speaker_sOr2_anyA_lt)
      (speakerU_nonexclusive_lt (by decide) speaker_pOr2_anyA_lt))).trans
    (three_ninths_lt_two_thirds.trans (ENNReal.add_lt_add ?_ ?_))
  · exact third_lt_speaker_only1.trans_le (speakerU_mayAny 100 _ ▸ le_add_self)
  · exact third_lt_speaker_anyNum.trans_le (speakerU_mayAny 100 _ ▸ le_add_self)

private theorem five_ninths_lt_two_thirds :
    ((8 : ℝ≥0∞) + 1)⁻¹ + (((8 : ℝ≥0∞) + 1)⁻¹ + (((8 : ℝ≥0∞) + 1)⁻¹
        + (((8 : ℝ≥0∞) + 1)⁻¹ + ((8 : ℝ≥0∞) + 1)⁻¹)))
      < ((2 : ℝ≥0∞) + 1)⁻¹ + ((2 : ℝ≥0∞) + 1)⁻¹ := by
  rw [show ((8 : ℝ≥0∞) + 1) = 9 from by norm_num, show ((2 : ℝ≥0∞) + 1) = 3 from by norm_num,
      show (9 : ℝ≥0∞)⁻¹ + ((9 : ℝ≥0∞)⁻¹ + ((9 : ℝ≥0∞)⁻¹ + ((9 : ℝ≥0∞)⁻¹ + (9 : ℝ≥0∞)⁻¹)))
        = 5 * 9⁻¹ from by ring,
      show (3 : ℝ≥0∞)⁻¹ + 3⁻¹ = 6 * 9⁻¹ from by
        rw [show (9 : ℝ≥0∞) = 3 * 3 from by norm_num,
            ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num)),
            show (6 : ℝ≥0∞) = 2 * 3 from by norm_num, mul_mul_mul_comm,
            ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one, two_mul]]
  exact (ENNReal.mul_lt_mul_iff_left (ENNReal.inv_ne_zero.mpr (by norm_num))
    (ENNReal.inv_ne_top.mpr (by norm_num))).mpr (by norm_num)

/-- Hearing *may any*, the listener infers the strong parse (34b) over the weak parse
(34a): the speaker's near-categorical parse preference, pooled over states. -/
theorem listener_infers_strong_parse :
    (listener 100 .mayAny).toOuterMeasure (parseEvent {.anyA})
      < (listener 100 .mayAny).toOuterMeasure (parseEvent {.anyB}) := by
  rw [listener, parseEvent, parseEvent, L1Intent_uniform_event_lt_iff,
      show (Finset.univ ×ˢ {Parse.anyA}).filter (fun x => Parse.utt x.2 = .mayAny)
        = Finset.univ ×ˢ {Parse.anyA} from by decide,
      show (Finset.univ ×ˢ {Parse.anyB}).filter (fun x => Parse.utt x.2 = .mayAny)
        = Finset.univ ×ˢ {Parse.anyB} from by decide,
      Finset.sum_product, Finset.sum_product]
  simp only [Finset.sum_singleton]
  rw [show (Finset.univ : Finset State)
        = {.onlyS, .onlyP, .only1, .anyNum, .only2, .sOr2, .pOr2} from by decide,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton,
      speaker_eq_zero (s := .onlyS) (p := .anyA) (by norm_num) (by decide),
      speaker_eq_zero (s := .onlyP) (p := .anyA) (by norm_num) (by decide),
      speaker_eq_zero (s := .onlyS) (p := .anyB) (by norm_num) (by decide),
      speaker_eq_zero (s := .onlyP) (p := .anyB) (by norm_num) (by decide),
      zero_add, zero_add, zero_add, zero_add]
  calc _ < ((8 : ℝ≥0∞) + 1)⁻¹ + (((8 : ℝ≥0∞) + 1)⁻¹ + (((8 : ℝ≥0∞) + 1)⁻¹
          + (((8 : ℝ≥0∞) + 1)⁻¹ + ((8 : ℝ≥0∞) + 1)⁻¹))) :=
        ENNReal.add_lt_add speaker_only1_anyA_lt (ENNReal.add_lt_add speaker_anyNum_anyA_lt
          (ENNReal.add_lt_add speaker_only2_anyA_lt
            (ENNReal.add_lt_add speaker_sOr2_anyA_lt speaker_pOr2_anyA_lt)))
    _ < ((2 : ℝ≥0∞) + 1)⁻¹ + ((2 : ℝ≥0∞) + 1)⁻¹ := five_ninths_lt_two_thirds
    _ < speaker 100 .only1 .anyB + speaker 100 .anyNum .anyB :=
        ENNReal.add_lt_add third_lt_speaker_only1 third_lt_speaker_anyNum
    _ ≤ speaker 100 .only1 .anyB + (speaker 100 .anyNum .anyB + (speaker 100 .only2 .anyB
          + (speaker 100 .sOr2 .anyB + speaker 100 .pOr2 .anyB))) :=
        add_le_add le_rfl le_self_add

/-! ### *May S* communicates Only S (Table 3: 0.67 vs 0.33) -/

private theorem half_lt_speaker_onlyS_sC :
    (((1 : ℕ) : ℝ≥0∞) + 1)⁻¹ < speaker 100 .onlyS .sC := by
  refine inv_succ_lt_S1_powUtility (n := 1) 100 l0 (s := (State.onlyS, ())) (a := Parse.sC) ?_
  rw [show Finset.univ.erase Parse.sC
        = {Parse.sA, Parse.sB, Parse.pA, Parse.pB, Parse.pC,
           Parse.anyA, Parse.anyB, Parse.evA, Parse.evB, Parse.evC, Parse.evD}
      from by decide,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton,
      powWeight_L0OfPred_of_mem _ _ 6 (by decide) card_sA,
      powWeight_L0OfPred_of_mem _ _ 4 (by decide) card_sB,
      powWeight_L0OfPred_of_not_mem _ _ (by norm_num) (by decide),
      powWeight_L0OfPred_of_not_mem _ _ (by norm_num) (by decide),
      powWeight_L0OfPred_of_not_mem _ _ (by norm_num) (by decide),
      powWeight_L0OfPred_of_not_mem _ _ (by norm_num) (by decide),
      powWeight_L0OfPred_of_not_mem _ _ (by norm_num) (by decide),
      powWeight_L0OfPred_of_not_mem _ _ (by norm_num) (by decide),
      powWeight_L0OfPred_of_not_mem _ _ (by norm_num) (by decide),
      powWeight_L0OfPred_of_not_mem _ _ (by norm_num) (by decide),
      powWeight_L0OfPred_of_not_mem _ _ (by norm_num) (by decide),
      powWeight_L0OfPred_of_mem _ _ 1 (by decide) (by decide)]
  -- 6⁻¹⁰⁰ + 4⁻¹⁰⁰ < 1 · 1⁻¹⁰⁰
  calc _ = ((6 : ℝ≥0∞)⁻¹) ^ 100 + ((4 : ℝ≥0∞)⁻¹) ^ 100 := by ring_nf
    _ ≤ ((4 : ℝ≥0∞)⁻¹) ^ 100 + ((4 : ℝ≥0∞)⁻¹) ^ 100 :=
        add_le_add (inv_pow_le_inv_pow (by norm_num) 100) le_rfl
    _ = 2 * ((4 : ℝ≥0∞)⁻¹) ^ 100 := (two_mul _).symm
    _ < ↑(1 : ℕ) * (((1 : ℕ) : ℝ≥0∞))⁻¹ ^ 100 := by
        have h := ENNReal.natCast_mul_inv_pow_lt (n := 2) (a := 4) (b := 1) (e := 100)
          (by norm_num) (by norm_num) (by norm_num)
        simpa using h

private theorem sum_speaker_eq_mul_inv (s : State) (p q : Parse) :
    speaker 100 s p + speaker 100 s q
      = (powWeight 100 l0 (s, ()) p + powWeight 100 l0 (s, ()) q)
        * (∑' r, powWeight 100 l0 (s, ()) r)⁻¹ := by
  rw [speaker, S1_powUtility_eq_normalize, PMF.normalize_apply, PMF.normalize_apply]
  exact (add_mul _ _ _).symm

private theorem Z_sOr2 :
    (∑' r, powWeight 100 l0 (.sOr2, ()) r)
      = 2 * (((6 : ℝ≥0∞)⁻¹) ^ 100 + ((5 : ℝ≥0∞)⁻¹) ^ 100 + ((4 : ℝ≥0∞)⁻¹) ^ 100) := by
  rw [tsum_fintype,
      show (Finset.univ : Finset Parse)
        = {Parse.sA, Parse.sB, Parse.sC, Parse.pA, Parse.pB, Parse.pC,
           Parse.anyA, Parse.anyB, Parse.evA, Parse.evB, Parse.evC, Parse.evD}
      from by decide,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton,
      powWeight_L0OfPred_of_mem _ _ 6 (by decide) card_sA,
      powWeight_L0OfPred_of_mem _ _ 4 (by decide) card_sB,
      powWeight_L0OfPred_of_not_mem _ _ (by norm_num) (by decide),
      powWeight_L0OfPred_of_mem _ _ 6 (by decide) (by decide),
      powWeight_L0OfPred_of_not_mem _ _ (by norm_num) (by decide),
      powWeight_L0OfPred_of_not_mem _ _ (by norm_num) (by decide),
      powWeight_L0OfPred_of_mem _ _ 5 (by decide) card_anyA,
      powWeight_L0OfPred_of_not_mem _ _ (by norm_num) (by decide),
      powWeight_L0OfPred_of_mem _ _ 5 (by decide) (by decide),
      powWeight_L0OfPred_of_mem _ _ 4 (by decide) (by decide),
      powWeight_L0OfPred_of_not_mem _ _ (by norm_num) (by decide),
      powWeight_L0OfPred_of_not_mem _ _ (by norm_num) (by decide)]
  push_cast
  ring

private theorem speakerU_sOr2_mayS_lt_half :
    speakerU 100 .sOr2 .mayS < (((1 : ℕ) : ℝ≥0∞) + 1)⁻¹ := by
  rw [speakerU_mayS, speaker_eq_zero (by norm_num) (by decide : ¬ meaning .sC .sOr2), add_zero,
      sum_speaker_eq_mul_inv,
      powWeight_L0OfPred_of_mem _ _ 6 (by decide) card_sA,
      powWeight_L0OfPred_of_mem _ _ 4 (by decide) card_sB,
      show (((1 : ℕ) : ℝ≥0∞) + 1)⁻¹ = 2⁻¹ from by norm_num, ← division_def,
      ENNReal.div_lt_iff (Or.inl (tsum_powWeight_ne_zero 100 l0 _))
        (Or.inl (tsum_powWeight_ne_top 100 l0 _)),
      Z_sOr2, ← mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
  calc ((6 : ℝ≥0∞)⁻¹) ^ 100 + ((4 : ℝ≥0∞)⁻¹) ^ 100
      < ((6 : ℝ≥0∞)⁻¹) ^ 100 + ((4 : ℝ≥0∞)⁻¹) ^ 100 + ((5 : ℝ≥0∞)⁻¹) ^ 100 :=
        ENNReal.lt_add_right
          (ENNReal.add_ne_top.mpr
            ⟨ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr (by norm_num)),
             ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr (by norm_num))⟩)
          (pow_ne_zero 100 (ENNReal.inv_ne_zero.mpr (by norm_num)))
    _ = ((6 : ℝ≥0∞)⁻¹) ^ 100 + ((5 : ℝ≥0∞)⁻¹) ^ 100 + ((4 : ℝ≥0∞)⁻¹) ^ 100 := by ring

/-- Hearing *may S*, the listener prefers Only S to S or 2 (Table 3: 0.67 vs 0.33): the
doubly exhaustified parse (32c) is available only at Only S. -/
theorem literal_s_communicates_onlyS :
    (listener 100 .mayS).toOuterMeasure (stateEvent {.sOr2})
      < (listener 100 .mayS).toOuterMeasure (stateEvent {.onlyS}) := by
  rw [listener_state_lt_iff, Finset.sum_singleton, Finset.sum_singleton]
  refine speakerU_sOr2_mayS_lt_half.trans (half_lt_speaker_onlyS_sC.trans_le ?_)
  rw [speakerU_mayS]
  exact le_add_self.trans le_add_self

/-! ### Only 1 over Any # -/

private theorem Z_only1_lt_Z_anyNum :
    (∑' r, powWeight 100 l0 (.only1, ()) r) < ∑' r, powWeight 100 l0 (.anyNum, ()) r := by
  apply ENNReal.tsum_lt_tsum (tsum_powWeight_ne_top 100 l0 _) (i := Parse.evB)
  · intro p
    by_cases h1 : meaning p State.only1
    · have h2 : meaning p State.anyNum := by revert h1; cases p <;> decide
      rw [powWeight_L0OfPred_of_mem (fun _ q => meaning q) ext_nonempty _ h1 rfl,
          powWeight_L0OfPred_of_mem (fun _ q => meaning q) ext_nonempty _ h2 rfl]
    · rw [powWeight_L0OfPred_of_not_mem (fun _ q => meaning q) ext_nonempty (by norm_num) h1]
      exact zero_le
  · rw [powWeight_L0OfPred_of_not_mem _ _ (by norm_num) (by decide),
        powWeight_L0OfPred_of_mem _ _ 4 (by decide) (by decide)]
    exact ENNReal.pow_pos (ENNReal.inv_pos.mpr (by norm_num)) 100

/-- Hearing *may any* at a uniform prior, Only 1 is strictly likelier than Any #: both
parses of *may any* weigh the same at the two states, but the parse (35b) of *may every*
is true at Any # and not at Only 1, inflating the speaker's partition there. Table 3 reports
0.50/0.50 (the difference is ≈ 2·10⁻³¹); the same asymmetry drives the *not every*
implicature under an Only-1-favouring prior (Table 6). -/
theorem only1_over_anyNum :
    (listener 100 .mayAny).toOuterMeasure (stateEvent {.anyNum})
      < (listener 100 .mayAny).toOuterMeasure (stateEvent {.only1}) := by
  rw [listener_state_lt_iff, Finset.sum_singleton, Finset.sum_singleton, speakerU_mayAny,
      speakerU_mayAny, sum_speaker_eq_mul_inv, sum_speaker_eq_mul_inv,
      powWeight_L0OfPred_of_mem _ _ 5 (by decide) card_anyA,
      powWeight_L0OfPred_of_mem _ _ 2 (by decide) card_anyB,
      powWeight_L0OfPred_of_mem _ _ 5 (by decide) card_anyA,
      powWeight_L0OfPred_of_mem _ _ 2 (by decide) card_anyB]
  exact (ENNReal.mul_lt_mul_iff_right
      (ne_of_gt (lt_of_lt_of_le
        (ENNReal.pow_pos (ENNReal.inv_pos.mpr (by norm_num)) 100) le_self_add))
      (ENNReal.add_ne_top.mpr
        ⟨ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr (by norm_num)),
         ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr (by norm_num))⟩)).mpr
    (ENNReal.inv_lt_inv.mpr Z_only1_lt_Z_anyNum)

/-! ### The paper's scenarios -/

/-- The state a scenario fixes, where the paper says which. -/
def rowState (row : LinguisticExample) : Option State :=
  match row.feature? "state" with
  | some "only1" => some .only1
  | some "anyNum" => some .anyNum
  | some "only2" => some .only2
  | _ => none

/-- Whether the row's literal truth is judged: an explicit `literal` reading, else the
row's own judgment. -/
def observedLiteral (row : LinguisticExample) : Bool :=
  match row.readings.lookup "literal" with
  | some j => j == .acceptable
  | none => row.judgment == .acceptable

/-- At every scenario with a fixed state, *may any* is literally true exactly where the
paper judges it so, and the exclusiveness reading holds exactly where Dayal's parse (34b)
is true: the all-or-nothing scenarios are true but not exclusive. -/
theorem rows_agree : ∀ row ∈ Examples.all, ∀ s ∈ rowState row,
    (LiterallyTrue s ↔ observedLiteral row = true) ∧
      ∀ j ∈ row.readings.lookup "exclusiveness", (meaning .anyB s ↔ j = .acceptable) := by
  decide +kernel

end Alsop2024
