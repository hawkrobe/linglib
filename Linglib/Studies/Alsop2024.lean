import Linglib.Pragmatics.RSA.Basic
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

The strong parse (34b) is the speaker's choice at the exclusiveness states for every
rationality (`speaker_prefers_strong_parse`), and at a uniform prior the listener hearing
*may any* prefers each of Only 1 and Any # to each of Only 2, S or 2, and P or 2 — again for
every rationality (`exclusiveness_derived`, Table 3) — while inferring the strong parse at the
paper's α = 100 (`listener_infers_strong_parse`). *May S* communicates Only S
(`literal_s_communicates_onlyS`), and the parse (35b) of *may every*, true at Any # but not at
Only 1, makes Only 1 the strictly likelier of the two (`only1_over_anyNum`) — the asymmetry
behind the *not every* implicature, which Table 3 rounds to 0.50/0.50. The prior
manipulations of Tables 5–9 enter the literal listener (`listenerWith`); their numerical
results are not re-derived here.

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

open MeasureTheory ProbabilityTheory RSA Data.Examples
open scoped ENNReal

/-! ### States, utterances, parses (Tables 1–2) -/

/-- The seven permission states (Table 1): the accessible worlds among taking nothing, only
Semantics, only Phonology, or both; taking nothing is always accessible. -/
inductive State where
  | onlyS | onlyP | only1 | anyNum | only2 | sOr2 | pOr2
  deriving DecidableEq, Repr, Fintype, Inhabited

instance : MeasurableSpace State := ⊤
instance : DiscreteMeasurableSpace State := ⟨fun _ => trivial⟩

/-- The four utterances (31). -/
inductive Utterance where
  | mayS | mayP | mayAny | mayEvery
  deriving DecidableEq, Repr, Fintype

instance : MeasurableSpace Utterance := ⊤
instance : DiscreteMeasurableSpace Utterance := ⟨fun _ => trivial⟩

/-- The twelve utterance–parse pairs (32)–(35), `a` the weakest parse of each utterance.
*May any* has two: the weak parse (34a), Szabolcsi's meaning, and the strong parse (34b),
Dayal's. -/
inductive Parse where
  | sA | sB | sC
  | pA | pB | pC
  | anyA | anyB
  | evA | evB | evC | evD
  deriving DecidableEq, Repr, Fintype, Inhabited

instance : MeasurableSpace Parse := ⊤
instance : DiscreteMeasurableSpace Parse := ⟨fun _ => trivial⟩

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

/-- The extension of each parse. -/
def sem (p : Parse) : Finset State := Finset.univ.filter (meaning p)

@[simp] theorem mem_sem {p : Parse} {s : State} : s ∈ sem p ↔ meaning p s := by simp [sem]

/-- Every state is truthfully describable. -/
theorem expressible : ∀ s, ∃ p, s ∈ sem p := by decide

/-- *May any* is literally true at a state when some parse of it is. -/
def LiterallyTrue (s : State) : Prop := ∃ p, p.utt = .mayAny ∧ meaning p s

instance : DecidablePred LiterallyTrue := fun _ => inferInstanceAs (Decidable (∃ _, _ ∧ _))

/-- The strong parse (34b) entails the weak parse (34a), so *may any* is literally true
exactly where Szabolcsi's meaning holds. -/
theorem literallyTrue_iff (s : State) : LiterallyTrue s ↔ meaning .anyA s := by
  revert s; decide

/-! ### The Global Intentions model (36)–(41) -/

/-- The speaker's joint choice of utterance and parse (37)–(38) at a uniform prior:
`S1(u,p|s) ∝ L0(s|u,p)^α` at equal costs. -/
noncomputable abbrev speaker (α : ℝ) : Kernel State Parse := classicalSpeaker sem α

/-- The pragmatic listener (40) at a uniform prior: the joint posterior over state and
intended parse given the utterance; `.fst` is its state marginal (41). -/
noncomputable abbrev listener (α : ℝ) : Kernel Utterance (State × Parse) :=
  classicalJointListener sem Parse.utt α

/-- The model at an arbitrary state prior, which enters the literal listener (36) and the
pragmatic listener (40) alike — the setting of Tables 5–9. -/
noncomputable def listenerWith (μ : Measure State) [IsFiniteMeasure μ] (α : ℝ) :
    Kernel Utterance (State × Parse) :=
  jointListener α 1 (literalListener μ fun p => (↑(sem p) : Set State).indicator 1) μ Parse.utt

/-- At the uniform prior, `listenerWith` is `listener`. -/
theorem listenerWith_uniformOn (α : ℝ) : listenerWith (uniformOn Set.univ) α = listener α := rfl

/-! ### The findings -/

/-- At an exclusiveness state the speaker prefers the strong parse (34b) of *may any* to the
weak parse (34a) at every rationality: the weak parse is true in five states, the strong in
two. At `α = 100` the ratio is `(5/2)^100`, the paper's "almost 100% of the time". -/
theorem speaker_prefers_strong_parse {α : ℝ} (hα : 0 < α) {s : State} (hs : meaning .anyB s) :
    (speaker α s).real {.anyA} < (speaker α s).real {.anyB} :=
  classicalSpeaker_real_singleton_lt_of_card_lt sem hα
    (mem_sem.mpr (by revert s hs; decide)) (mem_sem.mpr hs) (by decide)

/-- Hearing *may any*, the listener assigns no posterior to Only S under any parse. -/
theorem mayAny_rules_out_onlyS {α : ℝ} (hα : 0 < α) (p : Parse) :
    listener α .mayAny {(.onlyS, p)} = 0 := by
  rw [listener, classicalJointListener, jointListener_apply_singleton _ _ _ _ _
    (map_comp_classicalSpeaker_ne_zero sem Parse.utt hα.le (o := .mayAny) (c := .anyB) rfl
      (mem_sem.mpr (Or.inl rfl : meaning .anyB .only1)))]
  split_ifs with h
  · rw [classicalSpeaker_apply_singleton_eq_zero sem hα (by revert h; cases p <;> decide),
      mul_zero, ENNReal.zero_div]
  · exact ENNReal.zero_div

/-- Hearing *may every*, the listener assigns no posterior to Only S under any parse. -/
theorem mayEvery_rules_out_onlyS {α : ℝ} (hα : 0 < α) (p : Parse) :
    listener α .mayEvery {(.onlyS, p)} = 0 := by
  rw [listener, classicalJointListener, jointListener_apply_singleton _ _ _ _ _
    (map_comp_classicalSpeaker_ne_zero sem Parse.utt hα.le (o := .mayEvery) (c := .evD) rfl
      (mem_sem.mpr (rfl : meaning .evD .only2)))]
  split_ifs with h
  · rw [classicalSpeaker_apply_singleton_eq_zero sem hα (by revert h; cases p <;> decide),
      mul_zero, ENNReal.zero_div]
  · exact ENNReal.zero_div

/-- **The exclusiveness implicature** (Table 3): hearing *may any* at a uniform prior, the
listener prefers each exclusiveness state — Only 1 and Any #, where each class may be taken
on its own (the paper's 0.50 + 0.50) — to each of Only 2, S or 2, and P or 2 (each ≈ 0), at
every rationality. -/
theorem exclusiveness_derived {α : ℝ} (hα : 0 < α) :
    ∀ s ∈ ({.only2, .sOr2, .pOr2} : Finset State), ∀ s' ∈ ({.only1, .anyNum} : Finset State),
      (listener α .mayAny).fst.real {s} < (listener α .mayAny).fst.real {s'} := by
  intro s hs s' hs'
  fin_cases hs <;> fin_cases hs' <;>
    exact classicalJointListener_fst_real_lt_of_prodMul_strictDominates sem Parse.utt
      expressible hα (by decide +kernel)

/-- Hearing *may any* at the paper's α = 100, the listener infers the strong parse (34b) over
the weak parse (34a): the speaker's near-categorical parse preference, pooled over states. -/
theorem listener_infers_strong_parse :
    (listener 100 .mayAny).snd.real {.anyA} < (listener 100 .mayAny).snd.real {.anyB} :=
  classicalJointListener_snd_real_lt_of_divPowSum sem Parse.utt expressible (k := 100) (D := 60)
    (by decide +kernel) rfl rfl (by decide +kernel)

/-- Hearing *may S*, the listener prefers Only S to S or 2 at every rationality (Table 3:
0.67 vs 0.33): the doubly exhaustified parse (32c) is available only at Only S. -/
theorem literal_s_communicates_onlyS {α : ℝ} (hα : 0 < α) :
    (listener α .mayS).fst.real {.sOr2} < (listener α .mayS).fst.real {.onlyS} :=
  classicalJointListener_fst_real_lt_of_prodMul_strictDominates sem Parse.utt expressible hα
    (by decide +kernel)

/-- Hearing *may any* at a uniform prior, Only 1 is strictly likelier than Any # at every
rationality: both parses of *may any* weigh the same at the two states, but the parse (35b)
of *may every* is true at Any # and not at Only 1, inflating the speaker's partition there.
Table 3 reports 0.50/0.50 (at α = 100 the difference is ≈ 2·10⁻³¹); the same asymmetry
drives the *not every* implicature under an Only-1-favouring prior (Table 6). -/
theorem only1_over_anyNum {α : ℝ} (hα : 0 < α) :
    (listener α .mayAny).fst.real {.anyNum} < (listener α .mayAny).fst.real {.only1} :=
  classicalJointListener_fst_real_lt_of_prodMul_strictDominates sem Parse.utt expressible hα
    (by decide +kernel)

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
