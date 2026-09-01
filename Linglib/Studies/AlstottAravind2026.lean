import Linglib.Studies.Rett2020
import Linglib.Data.Examples.AlstottAravind2026

/-!
# Alstott & Aravind (2026): aspectual coercion in *before*- and *after*-clauses

Telic *before*-clauses and atelic *after*-clauses each have a weak and a strong reading.
Under-specification theories (Anscombe's entries with a weakened *before*, `weakBefore`,
`weakAfter`) give them one LF with the weak truth conditions; Rett's ambiguity theory
(`Rett.before`, `Rett.after`) gives the strong reading by default and derives the weak one
by inserting `COMPLET` or `INCHOAT`. Since coercion has a processing cost, only Rett's
theory predicts that a *before*-clause is harder to read in a before-finish context than
in a before-start context, and an *after*-clause harder in an after-start context: on the
paper's own experimental contexts the default reading is true in one context and false in
the other (`exp2_rett_asymmetric`, `exp4_rett_asymmetric`), while the under-specification
reading, and the *while*-competition implicature that might strengthen it, hold in both
(`exp2_underspecification_symmetric`, `exp4_underspecification_symmetric`). Four self-paced
reading experiments find the predicted asymmetries for *before* (Exp. 2) and *after*
(Exp. 4), a cost for completive coercion in *at*-modifier sentences (Exp. 1b), and no cost
for inchoative coercion in atelic *within*-modifier sentences (Exps. 1a, 3), against
Brennan & Pylkkänen.

The last result motivates the paper's non-coercive account of *within*-modifiers: the
assertion (33b) together with the scalar implicature over shorter spans entails that the
state began inside the span, with no operator involved (`within_implicature_onset`), and
the same entry handles telic *within*-sentences (`within_accomplishment_iff`). Rett's
operator assignment (`rettOperator`) matches the observed costs on every construction but
atelic *within* (`connective_costs_track_rett`, `within_disconfirms_inchoat`), and the
revised assignment matches all of them (`costs_track_revised`); coerced sentences are also
rated less natural exactly where they are slower (`naturalness_tracks_cost`). The costs in
Exps. 2 and 4 appear one word later than in Exp. 1b, which the paper tentatively attributes
to pragmatic as against semantic coercion.

## References

* [alstott-aravind-2026]
* [rett-2020]
* [anscombe-1964]
* [heinamaki-1974]
* [krifka-2010b]
* [condoravdi-2010]
* [brennan-pylkkanen-2010]
* [dell-1983]
-/

namespace AlstottAravind2026

open Tense Rett2020 Data.Examples
open Core.Order

/-! ### The two theories (§2.1) -/

variable {Time : Type*} [LinearOrder Time]

/-- The under-specification entry for *before* (7a): some run-time of the main clause is
partly preceded by every run-time of the embedded clause — Anscombe's entry with *some*
subinterval following in place of *every*, the weakening accomplishments require. -/
def weakBefore (A B : RunTimes Time) : Prop := ∃ i ∈ A, ∀ j ∈ B, i.snd < j.snd

/-- The under-specification entry for *after* (7b): some run-time of the main clause fully
follows some run-time of the embedded clause. -/
def weakAfter (A B : RunTimes Time) : Prop := ∃ i ∈ A, ∃ j ∈ B, j.snd < i.fst

/-- Temporal overlap — the *while* reading a competition-based implicature negates (§8.1). -/
def Overlap (A B : RunTimes Time) : Prop := ∃ t, t ∈ timeTrace A ∧ t ∈ timeTrace B

/-- A stative is weakly *before* an accomplishment iff its onset precedes the telos. -/
theorem weakBefore_stative_accomplishment_iff (a b : NonemptyInterval Time) :
    weakBefore (stativeDenotation a) (accomplishmentDenotation b) ↔ a.fst < b.snd := by
  constructor
  · rintro ⟨i, hi, h⟩
    exact lt_of_le_of_lt ((Set.mem_Iic.mp hi).1.trans i.fst_le_snd) (h b rfl)
  · intro h
    exact ⟨NonemptyInterval.pure a.fst, Set.mem_Iic.mpr ⟨le_rfl, a.fst_le_snd⟩,
      fun j hj => hj ▸ h⟩

/-- A stative is weakly *after* a stative iff its end follows the other's onset. -/
theorem weakAfter_stative_stative_iff (a b : NonemptyInterval Time) :
    weakAfter (stativeDenotation a) (stativeDenotation b) ↔ b.fst < a.snd := by
  constructor
  · rintro ⟨i, hi, j, hj, h⟩
    exact lt_of_le_of_lt ((Set.mem_Iic.mp hj).1.trans j.fst_le_snd)
      (h.trans_le (i.fst_le_snd.trans (Set.mem_Iic.mp hi).2))
  · intro h
    exact ⟨NonemptyInterval.pure a.snd, Set.mem_Iic.mpr ⟨a.fst_le_snd, le_rfl⟩,
      NonemptyInterval.pure b.fst, Set.mem_Iic.mpr ⟨le_rfl, b.fst_le_snd⟩, h⟩

/-- A stative and an accomplishment overlap iff neither ends before the other starts. -/
theorem overlap_stative_accomplishment_iff (a b : NonemptyInterval Time) :
    Overlap (stativeDenotation a) (accomplishmentDenotation b) ↔ a.fst ≤ b.snd ∧ b.fst ≤ a.snd := by
  simp only [Overlap, timeTrace_stative_closedInterval, timeTrace_accomplishment_closedInterval,
    Set.mem_ofPred_eq]
  constructor
  · rintro ⟨t, ⟨h1, h2⟩, h3, h4⟩
    exact ⟨h1.trans h4, h3.trans h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨max a.fst b.fst, ⟨le_max_left _ _, max_le a.fst_le_snd h2⟩,
      le_max_right _ _, max_le h1 b.fst_le_snd⟩

/-! ### The experimental contexts (29) and (31)

Time is measured in minutes; a stative denotes an interval with its subintervals, an
accomplishment its single run-time. -/

/-- Hector builds the tent 4:00–4:30pm, minutes after noon. -/
def hectorBuilds : NonemptyInterval ℕ := ⟨⟨240, 270⟩, by omega⟩
/-- Emma is irritable 2:00–4:30pm (29a): the before-start context. -/
def emmaIrritableA : NonemptyInterval ℕ := ⟨⟨120, 270⟩, by omega⟩
/-- Emma is irritable 4:15–4:30pm (29b): the before-finish context. -/
def emmaIrritableB : NonemptyInterval ℕ := ⟨⟨255, 270⟩, by omega⟩
/-- Lara fears the dog 10:00–10:15am, minutes after midnight. -/
def laraFears : NonemptyInterval ℕ := ⟨⟨600, 615⟩, by omega⟩
/-- Dave is regretful 10:05–10:15am (31a): the after-start context. -/
def daveRegretfulA : NonemptyInterval ℕ := ⟨⟨605, 615⟩, by omega⟩
/-- Dave is regretful from 10:05am for many days (31b): the after-finish context. -/
def daveRegretfulB : NonemptyInterval ℕ := ⟨⟨605, 4935⟩, by omega⟩

abbrev tent := accomplishmentDenotation hectorBuilds
abbrev irritableA := stativeDenotation emmaIrritableA
abbrev irritableB := stativeDenotation emmaIrritableB
abbrev fear := stativeDenotation laraFears
abbrev regretfulA := stativeDenotation daveRegretfulA
abbrev regretfulB := stativeDenotation daveRegretfulB

/-- Exp. 2: Rett's default before-start reading is true in the before-start context and
false in the before-finish context, where `COMPLET` restores truth — coercion is needed in
(29b) only. -/
theorem exp2_rett_asymmetric :
    Rett.before irritableA tent ∧ ¬ Rett.before irritableB tent ∧
      Rett.before irritableB (COMPLET tent) := by
  simp only [Rett.before_stative_accomplishment_iff, Rett.before_stative_complet_iff]
  decide

/-- Exp. 2: the under-specification reading is true in both contexts, and so is the
overlap a *while*-competition implicature would negate — neither distinguishes (29a) from
(29b) (§8.1). -/
theorem exp2_underspecification_symmetric :
    (weakBefore irritableA tent ∧ weakBefore irritableB tent) ∧
      (Overlap irritableA tent ∧ Overlap irritableB tent) := by
  simp only [weakBefore_stative_accomplishment_iff, overlap_stative_accomplishment_iff]
  decide

/-- Exp. 4: Rett's default after-finish reading is false in the after-start context, where
`INCHOAT` restores truth, and true in the after-finish context — coercion is needed in
(31a) only. -/
theorem exp4_rett_asymmetric :
    ¬ Rett.after regretfulA fear ∧ Rett.after regretfulA (INCHOAT fear) ∧
      Rett.after regretfulB fear := by
  simp only [Rett.after_stative_stative_iff, Rett.after_stative_inchoat_iff]
  decide

/-- Exp. 4: the under-specification reading is true in both contexts. -/
theorem exp4_underspecification_symmetric :
    weakAfter regretfulA fear ∧ weakAfter regretfulB fear := by
  simp only [weakAfter_stative_stative_iff]
  decide

private theorem mem_stative {i j : NonemptyInterval ℕ} :
    j ∈ stativeDenotation i ↔ i.fst ≤ j.fst ∧ j.snd ≤ i.snd := by
  simp [stativeDenotation, NonemptyInterval.le_def]

/-! ### A non-coercive account of *within*-modifiers (§8.2) -/

/-- *Within d* at the reference time `t` (33b): the clause holds throughout some subinterval
of `[t, t + d]`. -/
def within (t d : ℕ) (p : RunTimes ℕ) : Prop := ∃ i ∈ p, t ≤ i.fst ∧ i.snd ≤ t + d

/-- For a state holding throughout `[s, f]`, *within d* says the state reaches into the
span, and the negation of the alternative with a shorter span `d'` (35) says it does not
reach into the shorter span; together they locate the state's onset inside `(t + d', t + d]`
— the change-of-state reading without any operator. -/
theorem within_implicature_onset {s f t d d' : ℕ} (hsf : s ≤ f)
    (h : within t d (stativeDenotation ⟨⟨s, f⟩, hsf⟩))
    (h' : ¬ within t d' (stativeDenotation ⟨⟨s, f⟩, hsf⟩)) : t + d' < s ∧ s ≤ t + d := by
  obtain ⟨i, hi, hti, hit⟩ := h
  rw [mem_stative] at hi
  simp only [] at hi
  have hi' := i.fst_le_snd
  refine ⟨?_, by omega⟩
  by_contra hle
  exact h' ⟨⟨⟨max s t, max s t⟩, le_rfl⟩, mem_stative.mpr ⟨by simp, by simp; omega⟩,
    by simp, by simp; omega⟩

/-- For an accomplishment with run-time `i`, *within d* says the whole run-time lies in the
span (36): the same entry, with no operator either. -/
theorem within_accomplishment_iff (t d : ℕ) (i : NonemptyInterval ℕ) :
    within t d (accomplishmentDenotation i) ↔ t ≤ i.fst ∧ i.snd ≤ t + d := by
  simp [within, accomplishmentDenotation]

/-! ### Predictions against the four experiments -/

/-- The operator Rett's theory inserts (§3): `INCHOAT` for atelic *within*-modifier
sentences and after-start readings of atelic *after*-clauses, `COMPLET` for accomplishment
*at*-modifier sentences and before-finish readings of telic *before*-clauses. -/
def rettOperator (row : LinguisticExample) : Option String :=
  match row.feature? "construction", row.feature? "telicity", row.feature? "context" with
  | some "within", some "atelic", _ => some "INCHOAT"
  | some "at", some "telic", _ => some "COMPLET"
  | some "before", some "telic", some "beforeFinish" => some "COMPLET"
  | some "after", some "atelic", some "afterStart" => some "INCHOAT"
  | _, _, _ => none

/-- The paper's revision (§8.2): no operator in *within*-modifier sentences. -/
def revisedOperator (row : LinguisticExample) : Option String :=
  if row.feature? "construction" = some "within" then none else rettOperator row

/-- The aspectual-coercion trials and their controls. -/
def IsAspectualTrial (row : LinguisticExample) : Prop :=
  row.feature? "trial" = some "aspectualCoercion" ∨ row.feature? "trial" = some "aspectualControl"

instance : DecidablePred IsAspectualTrial := fun _ => inferInstanceAs (Decidable (_ ∨ _))

/-- Off the *within*-modifier trials, a sentence was read more slowly than its control
exactly when Rett's theory inserts an operator (Exps. 1b, 2, 4). -/
theorem connective_costs_track_rett :
    ∀ row ∈ Examples.all, IsAspectualTrial row → row.feature? "construction" ≠ some "within" →
      ((rettOperator row).isSome ↔ row.feature? "rtCost" = some "yes") := by
  decide +kernel

/-- On the atelic *within*-modifier trials Rett's theory inserts `INCHOAT` and no cost was
found (Exps. 1a, 3). -/
theorem within_disconfirms_inchoat :
    ∀ row ∈ Examples.all, IsAspectualTrial row → row.feature? "construction" = some "within" →
      rettOperator row = some "INCHOAT" ∧ row.feature? "rtCost" = some "no" := by
  decide +kernel

/-- With the §8.2 revision, operator insertion and observed cost coincide on every
aspectual trial. -/
theorem costs_track_revised :
    ∀ row ∈ Examples.all, IsAspectualTrial row →
      ((revisedOperator row).isSome ↔ row.feature? "rtCost" = some "yes") := by
  decide +kernel

/-- Coerced sentences are rated less natural than their controls exactly where they are
read more slowly. -/
theorem naturalness_tracks_cost :
    ∀ row ∈ Examples.all, IsAspectualTrial row →
      (row.feature? "naturalness" = some "lower" ↔ row.feature? "rtCost" = some "yes") := by
  decide +kernel

end AlstottAravind2026
