import Mathlib.Data.Finset.Insert
import Mathlib.Order.Monotone.Defs
import Mathlib.Tactic.DeriveFintype
import Linglib.Discourse.Commitment.Table
import Linglib.Logic.Natural.Basic
import Linglib.Semantics.Conditionals.Basic
import Linglib.Semantics.Denotation
import Linglib.Semantics.Presupposition.Context

/-!
# Readings of a conditional

This file defines the two readings of a conditional, hypothetical and premise, with the
denotation of *if p, q* under each, the felicity condition each places on the antecedent, the
entailment direction of each clause, and the markers that lexicalize the distinction.

A conditional is read as *hypothetical* when its antecedent is supposed and left open, and as
a *premise* conditional when the antecedent echoes prior discourse and is treated as
established ([iatridou-1991], [haegeman-2003]). On the hypothetical reading *if p, q* denotes
the conditional proposition of whatever operator the theory supplies; on the premise reading
it asserts *q* with *p* presupposed, the *given that* paraphrase. The two agree wherever the
antecedent holds and differ in what they make of the antecedent: the hypothetical reading puts
it in a downward-entailing position and the premise reading in an upward-entailing one, the
source of their opposite polarity-item profiles ([iatridou-1991]); the consequent is upward
entailing on either reading. A premise conditional is felicitous once its antecedent
has been committed to or is common ground, which is where its presupposition is satisfied, and
a hypothetical one while the antecedent's polar question is open. Languages may lexicalize the
split: Japanese *-ra* and German *falls* mark only hypothetical conditionals, *nara* and *wenn*
mark either ([lassiter-2025]).

## Main definitions

* `Reading`: the hypothetical and premise readings.
* `Reading.denote`: the denotation of *if p, q* under a reading, a partial proposition.
* `Conditional`: a conditional under a reading; `⟦c⟧` is its denotation.
* `Reading.Felicitous`: the felicity condition a reading places on the antecedent, relative
  to a commitment Table; `felicitous_iff_of_mem_commonGround` and
  `felicitous_iff_of_not_decidedBy` read the reading off the antecedent's discourse status.
* `Clause`, `Reading.clausePolarity`: the entailment direction of each clause under a reading.
* `Marker`: a conditional marker with the readings it can mark; per-language entries live in
  `Fragments/{Language}/Conditional.lean`.

## References

* [iatridou-1991]
* [haegeman-2003]
* [lassiter-2025]
-/

namespace Conditional

open Commitment NaturalLogic Presupposition Semantics

/-- The readings of a conditional: the antecedent is supposed and left open, or echoes prior
discourse and is treated as established. -/
inductive Reading
  | hypothetical
  | premise
  deriving DecidableEq, Fintype, Repr

/-- The two clauses of a conditional. -/
inductive Clause
  | antecedent
  | consequent
  deriving DecidableEq, Fintype, Repr

namespace Reading

@[simp] theorem «forall» {P : Reading → Prop} : (∀ ct, P ct) ↔ P .hypothetical ∧ P .premise :=
  ⟨fun h ↦ ⟨h _, h _⟩, fun ⟨h₁, h₂⟩ ct ↦ by cases ct <;> assumption⟩

@[simp] theorem «exists» {P : Reading → Prop} : (∃ ct, P ct) ↔ P .hypothetical ∨ P .premise :=
  ⟨fun ⟨ct, h⟩ ↦ by cases ct; exacts [.inl h, .inr h], fun h ↦ h.elim (⟨_, ·⟩) (⟨_, ·⟩)⟩

section Denotation

variable {W : Type*} (cond : Set W → Set W → Set W) (p q : Set W)

/-- The denotation of *if p, q* under a reading, for a conditional operator `cond` on total
propositions: the hypothetical reading is the conditional `cond p q`, the premise reading
asserts `q` with `p` presupposed. -/
def denote : Reading → PartialProp W
  | .hypothetical => .ofProp (· ∈ cond p q)
  | .premise => .condAssert (· ∈ p) (· ∈ q)

variable {cond p q} {w : W}

@[simp] theorem holds_denote_hypothetical :
    (hypothetical.denote cond p q).holds w ↔ w ∈ cond p q := by
  simp [denote, PartialProp.ofProp, PartialProp.holds]

@[simp] theorem holds_denote_premise :
    (premise.denote cond p q).holds w ↔ w ∈ p ∧ w ∈ q := Iff.rfl

/-- Where the antecedent holds, the hypothetical reading of the material conditional and the
premise reading agree; the readings differ only off the presupposition. -/
theorem holds_denote_materialImp_iff (hw : w ∈ p) :
    (hypothetical.denote materialImp p q).holds w ↔
      (premise.denote materialImp p q).holds w := by
  simp [hw, mem_materialImp]

/-- The hypothetical antecedent is a downward-entailing position. -/
theorem antitone_truthSet_hypothetical (q : Set W) :
    Antitone fun p ↦ (hypothetical.denote materialImp p q).truthSet :=
  fun _ _ h _ hw ↦ holds_denote_hypothetical.2 fun hp ↦
    mem_materialImp.1 (holds_denote_hypothetical.1 hw) (h hp)

/-- The premise antecedent is an upward-entailing position. -/
theorem monotone_truthSet_premise (cond : Set W → Set W → Set W) (q : Set W) :
    Monotone fun p ↦ (premise.denote cond p q).truthSet :=
  fun _ _ h _ hw ↦ ⟨h hw.1, hw.2⟩

/-- The consequent is an upward-entailing position on either reading. -/
theorem monotone_truthSet_consequent (ct : Reading) (p : Set W) :
    Monotone fun q ↦ (ct.denote materialImp p q).truthSet := by
  cases ct
  · exact fun _ _ h _ hw ↦ holds_denote_hypothetical.2 fun hp ↦
      h (mem_materialImp.1 (holds_denote_hypothetical.1 hw) hp)
  · exact fun _ _ h _ hw ↦ ⟨hw.1, h hw.2⟩

end Denotation

section Felicity

variable {A W : Type*} (K : Table A W) (p : Set W)

/-- A reading is felicitous for the antecedent `p` when `p` meets its discourse condition: a
hypothetical conditional leaves `p` undecided in the common ground, a premise conditional needs
`p` echoed, committed to by some participant or already common ground. -/
def Felicitous : Reading → Prop
  | .hypothetical => ¬ (Question.polar p).DecidedBy K.commonGround
  | .premise => (∃ a, p ∈ K.discourseCommitments a) ∨ p ∈ K.commonGround

variable {K p}

theorem premise_felicitous_of_mem_commonGround (h : p ∈ K.commonGround) :
    premise.Felicitous K p := .inr h

theorem premise_felicitous_of_shared [Nonempty A] (h : K.Shared p) : premise.Felicitous K p :=
  .inl <| (‹Nonempty A›).elim fun a ↦ ⟨a, h a⟩

theorem not_hypothetical_felicitous_of_mem_commonGround (h : p ∈ K.commonGround) :
    ¬ hypothetical.Felicitous K p :=
  fun h' ↦ h' (Question.decidedBy_polar.2 (.inl h))

theorem not_premise_felicitous (h₁ : ∀ a, p ∉ K.discourseCommitments a)
    (h₂ : ¬ (Question.polar p).DecidedBy K.commonGround) : ¬ premise.Felicitous K p :=
  fun h ↦ h.elim (fun ⟨a, ha⟩ ↦ h₁ a ha) fun hp ↦ h₂ (Question.decidedBy_polar.2 (.inl hp))

/-- An antecedent the common ground entails is read as a premise. -/
theorem felicitous_iff_of_mem_commonGround (h : p ∈ K.commonGround) {ct : Reading} :
    ct.Felicitous K p ↔ ct = .premise := by
  cases ct
  · exact iff_of_false (not_hypothetical_felicitous_of_mem_commonGround h) (by decide)
  · exact iff_of_true (premise_felicitous_of_mem_commonGround h) rfl

/-- An antecedent nobody has committed to and whose polar question is open is read
hypothetically. -/
theorem felicitous_iff_of_not_decidedBy (h₁ : ∀ a, p ∉ K.discourseCommitments a)
    (h₂ : ¬ (Question.polar p).DecidedBy K.commonGround) {ct : Reading} :
    ct.Felicitous K p ↔ ct = .hypothetical := by
  cases ct
  · exact iff_of_true h₂ rfl
  · exact iff_of_false (not_premise_felicitous h₁ h₂) (by decide)

/-- In a context whose common ground entails the antecedent, the premise reading's
presupposition is satisfied on the context set. -/
theorem presupSatisfied_denote_premise_of_mem_commonGround (cond : Set W → Set W → Set W)
    (q : Set W) (h : p ∈ K.commonGround) :
    Context.presupSatisfied (HasCommonGround.contextSet K) (premise.denote cond p q) :=
  fun _ hw ↦ Filter.mem_ker.1 hw p h

end Felicity

/-- The entailment direction of a clause under a reading: the antecedent is downward entailing
on the hypothetical reading (`antitone_truthSet_hypothetical`) and upward entailing on the
premise reading (`monotone_truthSet_premise`), the consequent upward entailing on either
(`monotone_truthSet_consequent`). -/
def clausePolarity : Reading → Clause → ContextPolarity
  | .hypothetical, .antecedent => .downward
  | _, _ => .upward

end Reading

end Conditional

/-- A conditional *if p, q* under a reading, interpreted by the conditional operator `cond`
on its hypothetical reading. -/
structure Conditional (W : Type*) (cond : Set W → Set W → Set W) where
  /-- The antecedent proposition. -/
  antecedent : Set W
  /-- The consequent proposition. -/
  consequent : Set W
  /-- The reading the conditional is taken on. -/
  reading : Conditional.Reading

namespace Conditional

open Presupposition Semantics

variable {W : Type*} {cond : Set W → Set W → Set W}

/-- The denotation of a conditional under its reading. -/
def denote (c : Conditional W cond) : PartialProp W :=
  c.reading.denote cond c.antecedent c.consequent

instance : Denotes (Conditional W cond) (PartialProp W) := ⟨denote⟩

@[simp] theorem denote_mk (p q : Set W) (r : Reading) :
    ⟦(⟨p, q, r⟩ : Conditional W cond)⟧ = r.denote cond p q := rfl

/-- A conditional marker is a form together with the readings it can mark: Japanese *-ra* and
German *falls* mark only hypothetical conditionals, *nara*, *wenn*, and English *if* mark either
([lassiter-2025]). Per-language entries live in `Fragments/{Language}/Conditional.lean`. -/
structure Marker where
  /-- The marker's citation form. -/
  form : String
  /-- The readings the marker can mark. -/
  readings : Finset Reading
  deriving DecidableEq

end Conditional
