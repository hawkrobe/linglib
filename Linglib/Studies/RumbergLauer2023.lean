module

public import Linglib.Semantics.Modality.BranchingTime
public import Mathlib.Tactic.DeriveFintype

/-!
# Rumberg and Lauer (2023): What if, and when? Conditionals, tense, and branching time

This file formalizes the paper's account of tense in indicative conditionals over branching
time. An isolated futurate present is felicitous only when the eventuality is settled, true on
every history through the moment of utterance: the game the Red Sox play tomorrow is scheduled,
their winning it is not (`Game.played_inevitable`). The paper reconstructs
[kaufmann-2005-truth]'s account as Ockhamist and [schulz-2008]'s as Peircean, both reading the
present as non-pastness, and evaluates them against four questions. Its own account uses the
transition semantics of [rumberg-2016]: truth is relative to a moment and a course of events,
the future operator quantifies only over the histories the course admits, and a conditional
evaluates its consequent at the first moment of decidedness of each minimal course making the
antecedent true (`tCond`). At the utterance index the future operator is settledness, which
answers the first question; a present antecedent is true relative to a course leading to a
witness without being settled (`tFut_of_lt`), so the conditional lifts the requirement; a
consequent is shifted only when its antecedent is not yet true at the actual past, and a past
antecedent's minimal course is the actual past, so its consequent stays at the utterance
moment (`tCond_tPast`), while the rival accounts shift it. On the two-trains scenario Schulz's
restriction to the earliest antecedent moment validates *if John comes today, he arrives at
two* and the transition account rejects both conditionals (`Trains.tCond_fails`).

## Implementation notes

The substrate's `IsInevitable` is the Peircean future. The paper's transition sets with a last
transition are the pasts of moments, so a course of events is represented by the moment whose
past it is: an index is a pair of moments, the actual past at `m` is the pair `(m, m)`,
extending a course is moving up the order, and the first moment of decidedness of a course is
the moment itself. Schulz's ordering of ontic alternatives by time takes a time projection as
a parameter, and Kaufmann's conditional is taken without its contextual restriction. The
finite models are decided through the substrate's reduction of histories to maximal moments.

## References

* [rumberg-lauer-2023]
* [rumberg-2016]
* [kaufmann-2005-truth]
* [schulz-2008]
* [prior-1967]
-/

@[expose] public section

namespace RumbergLauer2023

open BranchingTime

variable {M : Type*} [PartialOrder M]

/-! ### The tenses under the three postsemantics -/

/-- The Peircean present: non-pastness, truth now or a settled future. -/
def pPresent (φ : MProp M) : MProp M := λ m => φ m ∨ IsInevitable φ m

/-- The Ockhamist present: truth now or later on the history. -/
def oPresent (φ : OProp M) : OProp M := λ m h => φ m h ∨ oFut φ m h

/-- A transition proposition: truth at a moment relative to a course of events, given by the
moment whose past the course is. -/
abbrev TProp (M : Type*) := M → M → Prop

/-- An atomic transition proposition depends only on the moment. -/
def tAtom (φ : MProp M) : TProp M := λ m _ => φ m

/-- The transition past. -/
def tPast (φ : TProp M) : TProp M := λ m n => ∃ m' < m, φ m' n

/-- The transition future: on every history through the moment that the course admits, a
later `φ`-moment. -/
def tFut (φ : TProp M) : TProp M := λ m n => ∀ h ∈ Hist m, n ∈ h → ∃ m' ∈ h, m < m' ∧ φ m' n

/-- Stability: truth under every extension of the course compatible with the moment. -/
def tStable (φ : TProp M) : TProp M := λ m n => ∀ n', n ≤ n' → (∃ h ∈ Hist m, n' ∈ h) → φ m n'

/-- The transition present: non-pastness. -/
def tPresent (φ : TProp M) : TProp M := λ m n => φ m n ∨ tFut φ m n

/-- At the actual past the future operator is settledness: the course admits every history
through the moment. -/
theorem tFut_self (φ : MProp M) (m : M) : tFut (tAtom φ) m m ↔ IsInevitable φ m :=
  forall₂_congr λ _ hm => ⟨λ H => H hm, λ H _ => H⟩

/-- An isolated present is the Peircean present: future reference requires settledness. -/
theorem tPresent_self (φ : MProp M) (m : M) : tPresent (tAtom φ) m m ↔ pPresent φ m :=
  or_congr Iff.rfl (tFut_self φ m)

/-- Relative to a course leading to a later `φ`-moment, `φ` will be the case, settled or not. -/
theorem tFut_of_lt {φ : MProp M} {m n : M} (hmn : m < n) (hn : φ n) : tFut (tAtom φ) m n :=
  λ _ _ hn' => ⟨n, hn', hmn, hn⟩

/-- The past does not depend on the course of events. -/
theorem tPast_tAtom (φ : MProp M) (m n : M) : tPast (tAtom φ) m n ↔ pPast φ m := Iff.rfl

/-! ### Conditionals -/

/-- A minimal course of events at `m` making `A` true: no course between the actual past and
it does. -/
def MinimalFor (A : TProp M) (m n : M) : Prop :=
  m ≤ n ∧ A m n ∧ ∀ n', m ≤ n' → n' < n → ¬ A m n'

/-- Predictive conditionals in transition semantics: at the utterance moment, every minimal
course making the antecedent true makes the consequent true at its first moment of
decidedness. -/
def tCond (A C : TProp M) (m : M) : Prop := ∀ n, MinimalFor A m n → C n n

/-- [schulz-2008]'s conditional in branching time: the earliest later moments, by time, at
which the antecedent is true make the consequent true. -/
def sCond {T : Type*} [LinearOrder T] (time : M → T) (A C : MProp M) (m : M) : Prop :=
  ∀ m', m ≤ m' → A m' → (∀ m'', m ≤ m'' → A m'' → ¬ time m'' < time m') → C m'

/-- [kaufmann-2005-truth]'s conditional in Ockhamist branching time, without the contextual
restriction: at every later index at which the antecedent is settled, the consequent holds. -/
def kCond (A C : OProp M) (m : M) : Prop :=
  ∀ m', m ≤ m' → ∀ h' ∈ Hist m', oSettled A m' h' → C m' h'

/-- An antecedent already true at the actual past has it as its only minimal course: the
consequent is shifted only when the antecedent is not yet true. -/
theorem minimalFor_eq_of_self {A : TProp M} {m n : M} (hA : A m m) (h : MinimalFor A m n) :
    n = m :=
  of_not_not λ hne => h.2.2 m le_rfl (lt_of_le_of_ne h.1 (Ne.symm hne)) hA

/-- A past antecedent's only minimal course is the actual past. -/
theorem minimalFor_tPast_iff (φ : MProp M) (m n : M) :
    MinimalFor (tPast (tAtom φ)) m n ↔ n = m ∧ pPast φ m :=
  ⟨λ h => ⟨minimalFor_eq_of_self h.2.1 h, h.2.1⟩, by
    rintro ⟨rfl, hA⟩
    exact ⟨le_rfl, hA, λ _ hmn' hlt => absurd (lt_of_le_of_lt hmn' hlt) (lt_irrefl _)⟩⟩

/-- No shifted readings with past antecedents: the consequent is evaluated at the utterance
moment. -/
theorem tCond_tPast (φ : MProp M) (C : TProp M) (m : M) :
    tCond (tPast (tAtom φ)) C m ↔ (pPast φ m → C m m) := by
  simp only [tCond, minimalFor_tPast_iff]
  exact ⟨λ h hA => h m ⟨rfl, hA⟩, λ h n ⟨hn, hA⟩ => hn ▸ h hA⟩

/-- The settled past is the past: it does not depend on the history. -/
theorem oSettled_oPast_oAtom (φ : MProp M) (m : M) (h : Flag M) :
    oSettled (oPast (oAtom φ)) m h ↔ pPast φ m :=
  let ⟨h', hh'⟩ := hist_nonempty m
  ⟨λ H => H h' hh', λ H _ _ => H⟩

/-- Kaufmann's conditional with a past antecedent and consequent quantifies over the later
moments at which the antecedent has come true, and evaluates the consequent there. -/
theorem kCond_oPast (φ ψ : MProp M) (m : M) :
    kCond (oPast (oAtom φ)) (oPast (oAtom ψ)) m ↔
      ∀ m', m ≤ m' → pPast φ m' → pPast ψ m' := by
  simp only [kCond, oSettled_oPast_oAtom]
  exact forall₂_congr λ m' _ =>
    ⟨λ H hφ => let ⟨h', hh'⟩ := hist_nonempty m'; H h' hh' hφ, λ H _ _ hφ => H hφ⟩

/-! ### Decidability on finite frames -/

/-- The transition future of an atom on a finite frame. -/
theorem tFut_tAtom_iff [IsLeftLinear M] [Finite M] (φ : MProp M) (m n : M) :
    tFut (tAtom φ) m n ↔ ∀ x, IsMax x → m ≤ x → n ≤ x → ∃ m', m < m' ∧ m' ≤ x ∧ φ m' := by
  have : Nonempty M := ⟨m⟩
  rw [tFut, forall_hist_iff]
  exact forall_congr' λ x => forall_congr' λ _ => imp_congr_right λ _ => imp_congr_right λ _ =>
    ⟨λ ⟨m', hm', hlt, hφ⟩ => ⟨m', hlt, hm', hφ⟩, λ ⟨m', hlt, hm', hφ⟩ => ⟨m', hm', hlt, hφ⟩⟩

section Decidable

variable [IsLeftLinear M] [Fintype M] [DecidableEq M] [DecidableRel (· ≤ · : M → M → Prop)]
  [DecidableLT M]

instance (φ : MProp M) [DecidablePred φ] (m n : M) : Decidable (tFut (tAtom φ) m n) :=
  decidable_of_iff _ (tFut_tAtom_iff φ m n).symm

instance (φ : MProp M) [DecidablePred φ] (m n : M) : Decidable (tPresent (tAtom φ) m n) :=
  inferInstanceAs (Decidable (φ m ∨ tFut (tAtom φ) m n))

instance (φ : MProp M) [DecidablePred φ] (m n : M) : Decidable (tPast (tAtom φ) m n) := by
  unfold tPast tAtom; infer_instance

instance (A : TProp M) [∀ m n, Decidable (A m n)] (m n : M) : Decidable (MinimalFor A m n) := by
  unfold MinimalFor; infer_instance

instance (A C : TProp M) [∀ m n, Decidable (A m n)] [∀ n, Decidable (C n n)] (m : M) :
    Decidable (tCond A C m) := by
  unfold tCond; infer_instance

instance (φ : MProp M) [DecidablePred φ] (m : M) : Decidable (pPresent φ m) := by
  unfold pPresent; infer_instance

instance (φ : MProp M) [DecidablePred φ] (m : M) : Decidable (pPast φ m) := by
  unfold pPast; infer_instance

instance {T : Type*} [LinearOrder T] (time : M → T) (A C : MProp M) [DecidablePred A]
    [DecidablePred C] (m : M) : Decidable (sCond time A C m) := by
  unfold sCond; infer_instance

end Decidable

/-! ### The game -/

/-- The moments of the game scenario: `now`, below the two incomparable outcomes. -/
inductive Game | now | win | lose
  deriving DecidableEq, Fintype, Repr

namespace Game

instance : LE Game := ⟨λ a b => a = now ∨ a = b⟩

instance : DecidableRel (· ≤ · : Game → Game → Prop) :=
  λ a b => inferInstanceAs (Decidable (a = now ∨ a = b))

instance : PartialOrder Game where
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide

instance : DecidableLT Game := decidableLTOfDecidableLE
instance : IsLeftLinear Game := ⟨by decide⟩
instance : IsCodirectedOrder Game := ⟨by decide⟩
instance : IsBranchingTime Game := ⟨⟩

/-- *The Red Sox play the Yankees*: true at both outcomes. -/
def played : MProp Game := λ m => m = win ∨ m = lose

/-- *The Red Sox beat the Yankees*: true at the winning outcome. -/
def beat : MProp Game := λ m => m = win

instance : DecidablePred played := λ m => inferInstanceAs (Decidable (m = win ∨ m = lose))
instance : DecidablePred beat := λ m => inferInstanceAs (Decidable (m = win))

/-- The scheduled game is settled, so its futurate present is felicitous; the win is not. -/
theorem played_inevitable : IsInevitable played now ∧ ¬ IsInevitable beat now := by decide

/-- The win is future-true on the winning history yet not settled: Ockhamist future truth
and Peircean settledness come apart. -/
theorem oFut_beat_not_inevitable :
    (∃ h ∈ Hist now, oFut (oAtom beat) now h) ∧ ¬ IsInevitable beat now :=
  ⟨⟨flagOfMax win (by decide), by show (now : Game) ≤ win; decide, win,
    by show (win : Game) ≤ win; decide, by decide, rfl⟩, played_inevitable.2⟩

/-- A futurate present antecedent needs no settledness: relative to the course of events
leading to the win, *the Red Sox beat the Yankees tomorrow* is true at `now`, where it is not
settled. -/
theorem tPresent_beat : tPresent (tAtom beat) now win ∧ ¬ pPresent beat now := by decide

end Game

/-! ### The two trains -/

/-- The moments of the two-trains scenario: at one John may decide on the early train and
arrive at two, or wait and then either decide on the late train and arrive at three, or
stay. -/
inductive Trains | now | early | arriveTwo | wait | late | arriveThree | stay
  deriving DecidableEq, Fintype, Repr

namespace Trains

/-- The clock time of a moment. -/
def time : Trains → ℕ
  | now => 0
  | early | wait => 1
  | arriveTwo | late | stay => 2
  | arriveThree => 3

def leB : Trains → Trains → Bool
  | now, _ => true
  | early, arriveTwo => true
  | wait, late | wait, arriveThree | wait, stay => true
  | late, arriveThree => true
  | a, b => a == b

instance : LE Trains := ⟨λ a b => leB a b = true⟩

instance : DecidableRel (· ≤ · : Trains → Trains → Prop) :=
  λ a b => inferInstanceAs (Decidable (leB a b = true))

instance : PartialOrder Trains where
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide

instance : DecidableLT Trains := decidableLTOfDecidableLE
instance : IsLeftLinear Trains := ⟨by decide⟩
instance : IsCodirectedOrder Trains := ⟨by decide⟩
instance : IsBranchingTime Trains := ⟨⟩

/-- *John comes to Konstanz today*: true on arrival. -/
def come : MProp Trains := λ m => m = arriveTwo ∨ m = arriveThree

/-- *John arrives at two*. -/
def atTwo : MProp Trains := λ m => m = arriveTwo

/-- *John arrives at three*. -/
def atThree : MProp Trains := λ m => m = arriveThree

instance : DecidablePred come :=
  λ m => inferInstanceAs (Decidable (m = arriveTwo ∨ m = arriveThree))
instance : DecidablePred atTwo := λ m => inferInstanceAs (Decidable (m = arriveTwo))
instance : DecidablePred atThree := λ m => inferInstanceAs (Decidable (m = arriveThree))

/-- Schulz's restriction to the earliest antecedent moment validates *if John comes to
Konstanz today, he arrives at two*: only the early decision counts. -/
theorem sCond_validates : sCond time (pPresent come) (pPresent atTwo) now := by decide

/-- On the transition account both conditionals fail: the early and the late decisions are
both minimal courses making the antecedent true, and each falsifies one consequent. -/
theorem tCond_fails :
    ¬ tCond (tPresent (tAtom come)) (tPresent (tAtom atTwo)) now ∧
      ¬ tCond (tPresent (tAtom come)) (tPresent (tAtom atThree)) now := by
  decide

/-- The shifted consequent: the late decision is a minimal course, later than the utterance,
and the consequent is evaluated there. -/
theorem minimalFor_late : MinimalFor (tPresent (tAtom come)) now late ∧ now < late := by decide

end Trains

/-! ### The interview -/

/-- Three moments in a line: before the interview, John leaving it with the job, and after. -/
abbrev Interview := Fin 3

/-- *John left the interview*. -/
def leftInterview : MProp Interview := λ m => m = 1

/-- *John got the job*. -/
def gotJob : MProp Interview := λ m => m = 1

instance : DecidablePred leftInterview := λ m => inferInstanceAs (Decidable (m = 1))
instance : DecidablePred gotJob := λ m => inferInstanceAs (Decidable (m = 1))

/-- Both rival accounts shift a past antecedent: before the interview, *if John left the
interview, he got the job* has its antecedent possibilities in the future of the utterance and
comes out true on both, though the interview is yet to take place. -/
theorem past_antecedent_shifted :
    ¬ pPast leftInterview 0 ∧ (∀ m', 0 ≤ m' → pPast leftInterview m' → 0 < m') ∧
      sCond id (pPast leftInterview) (pPast gotJob) 0 ∧
      kCond (oPast (oAtom leftInterview)) (oPast (oAtom gotJob)) 0 :=
  ⟨by decide, by decide, by decide, (kCond_oPast _ _ _).2 (by decide)⟩

end RumbergLauer2023
