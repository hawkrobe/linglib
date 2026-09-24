module

public import Mathlib.Data.Finset.Insert
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Logic.Natural.Soundness
public import Linglib.Semantics.Conditionals.Basic
public import Linglib.Semantics.Presupposition.Defs

/-!
# Readings of a conditional

This file defines the two readings of a conditional. A conditional is read as *hypothetical* when
its antecedent is supposed and left open, and as a *premise* conditional when the antecedent
echoes prior discourse and is treated as established, the distinction of Iatridou and Haegeman.
On the hypothetical reading *if p, q* denotes the conditional proposition of whatever operator
the theory supplies, and on the premise reading it asserts *q* with *p* presupposed, the *given
that* paraphrase. The two readings give the antecedent opposite entailment directions, the
source of their opposite polarity-item profiles: for a conditional over a domain that grows with
the antecedent, such as the material or the strict conditional, the hypothetical antecedent is
downward entailing and every other clause upward entailing, while over the closest
antecedent-worlds the antecedent is neither. Languages may lexicalize the split, as Japanese
*-ra* and German *falls* mark only hypothetical conditionals.

## Main definitions

* `Conditional.Reading`: the hypothetical and premise readings.
* `Conditional.Reading.denote`: the denotation of *if p, q* under a reading.
* `Conditional.Reading.clauseSignature`: the projectivity signature of each clause under a
  reading, whose sign is `Conditional.Reading.clausePolarity`.
* `Conditional.Marker`: a conditional marker with the readings it can mark.

## Main results

* `Conditional.Reading.soundFor_clauseSignature`: over a monotone domain the signatures are
  sound.
* `Conditional.Reading.exists_not_antitone_hypothetical_closestImp`: over the closest
  antecedent-worlds the hypothetical antecedent is not downward entailing.

## References

* [S. Iatridou, *Topics in Conditionals* (1991)][iatridou-1991]
* [L. Haegeman, *Conditional clauses: External and internal syntax* (2003)][haegeman-2003]
* [D. Lassiter, *Sorting Out Left-Nested Conditionals* (2025)][lassiter-2025]
-/

@[expose] public section

namespace Conditional

open NaturalLogic Presupposition

/-- The readings of a conditional, on which the antecedent is supposed and left open or echoes
prior discourse and is treated as established. -/
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
propositions. The hypothetical reading is `cond p q`, and the premise reading asserts `q` with
`p` presupposed. -/
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
premise reading agree. -/
theorem holds_denote_materialImp_iff (hw : w ∈ p) :
    (hypothetical.denote materialImp p q).holds w ↔
      (premise.denote materialImp p q).holds w := by
  simp [hw, mem_materialImp]

end Denotation

/-! ### Entailment directions

The clauses of a conditional over a domain of antecedent-worlds have the projectivity
signatures of natural logic: the hypothetical antecedent is antitone when the domain grows with
the antecedent, and every other clause is monotone. The material and the strict conditional
have such domains; the conditional of the closest antecedent-worlds does not, since antecedent
strengthening fails for it. -/

section Signature

variable {W : Type*} {D : W → Set W → Set W} (cond : Set W → Set W → Set W) (p q : Set W)

/-- The projectivity signature of a clause under a reading is antitone for the hypothetical
antecedent and monotone for every other clause. -/
def clauseSignature : Reading → Clause → Signature
  | .hypothetical, .antecedent => .anti
  | _, _ => .mono

/-- The entailment direction of a clause under a reading, the sign of its signature. -/
def clausePolarity (ct : Reading) (c : Clause) : SignType := (clauseSignature ct c).sign

/-- The function of a clause under a reading, the other clause held fixed, on truth sets. -/
def clauseMap (ct : Reading) : Clause → Set W → Set W
  | .antecedent => fun p' ↦ (ct.denote cond p' q).truthSet
  | .consequent => fun q' ↦ (ct.denote cond p q').truthSet

variable {cond p q}

/-- The hypothetical antecedent is antitone over a domain that grows with the antecedent. -/
theorem antitone_truthSet_hypothetical (hD : ∀ w, Monotone (D w)) (q : Set W) :
    Antitone fun p ↦ (hypothetical.denote (ofDomain D) p q).truthSet :=
  fun _ _ h _ hw ↦ holds_denote_hypothetical.2
    (ofDomain_anti_left (fun i ↦ hD i h) (holds_denote_hypothetical.1 hw))

/-- The premise antecedent is monotone for every operator. -/
theorem monotone_truthSet_premise (cond : Set W → Set W → Set W) (q : Set W) :
    Monotone fun p ↦ (premise.denote cond p q).truthSet :=
  fun _ _ h _ hw ↦ ⟨h hw.1, hw.2⟩

/-- The consequent is monotone on either reading of a conditional over a domain. -/
theorem monotone_truthSet_consequent (ct : Reading) (p : Set W) :
    Monotone fun q ↦ (ct.denote (ofDomain D) p q).truthSet := by
  cases ct
  · exact fun _ _ h _ hw ↦
      holds_denote_hypothetical.2 (ofDomain_mono_right h (holds_denote_hypothetical.1 hw))
  · exact fun _ _ h _ hw ↦ ⟨hw.1, h hw.2⟩

/-- Over a domain that grows with the antecedent, each clause's signature is sound for the
clause's function. -/
theorem soundFor_clauseSignature (hD : ∀ w, Monotone (D w)) (p q : Set W) (ct : Reading)
    (c : Clause) : (clauseSignature ct c).SoundFor (clauseMap (ofDomain D) p q ct c) := by
  cases ct <;> cases c
  · exact soundFor_anti_iff.2 (antitone_truthSet_hypothetical hD q)
  · exact soundFor_mono_iff.2 (monotone_truthSet_consequent .hypothetical p)
  · exact soundFor_mono_iff.2 (monotone_truthSet_premise _ q)
  · exact soundFor_mono_iff.2 (monotone_truthSet_consequent .premise p)

/-- Over the closest antecedent-worlds the hypothetical antecedent is not antitone: with three
worlds ranked `0 < 1 < 2` from `0`, *if 1 or 2, then 1* holds at `0` while *if 2, then 1* does
not. -/
theorem exists_not_antitone_hypothetical_closestImp :
    ∃ (ord : Fin 3 → Preorder (Fin 3)) (q : Set (Fin 3)),
      ¬ Antitone fun p ↦ (hypothetical.denote (closestImp ord) p q).truthSet := by
  let ord : Fin 3 → Preorder (Fin 3) := fun _ ↦ Preorder.lift fun v : Fin 3 ↦ (v : ℕ)
  refine ⟨ord, {1}, fun h ↦ ?_⟩
  have h1 : (0 : Fin 3) ∈ (hypothetical.denote (closestImp ord) {1, 2} {1}).truthSet := by
    simp only [PartialProp.mem_truthSet, holds_denote_hypothetical]
    decide
  have h2 := h (show ({2} : Set (Fin 3)) ⊆ {1, 2} by simp) h1
  simp only [PartialProp.mem_truthSet, holds_denote_hypothetical] at h2
  revert h2; decide

end Signature

end Reading

/-- A conditional marker is a form together with the readings it can mark. Japanese *-ra* and German
*falls* mark only hypothetical conditionals, and *nara*, *wenn* and English *if* mark either
([lassiter-2025]). -/
structure Marker where
  /-- The marker's citation form. -/
  form : String
  /-- The readings the marker can mark. -/
  readings : Finset Reading
  deriving DecidableEq

end Conditional
