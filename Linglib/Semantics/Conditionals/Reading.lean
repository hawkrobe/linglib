import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.DeriveFintype
import Linglib.Discourse.Commitment.Table
import Linglib.Semantics.Polarity.Licensing

/-!
# Readings of a conditional

This file defines the two readings of a conditional, hypothetical and premise, with the
felicity condition each places on its antecedent, the polarity items each admits there, and the
markers that lexicalize the distinction.

A conditional is construed as *hypothetical* when its antecedent is supposed and left open, and
as a *premise* conditional when the antecedent echoes prior discourse and is treated as
established ([iatridou-1991], [haegeman-2003]). The readings share their truth conditions and
differ in felicity: a premise antecedent can be paraphrased with *given that* or *since*, and
must have been committed to or be common ground. They also differ in polarity: a hypothetical
antecedent is the conditional-antecedent licensing context and admits the negative polarity
items that context licenses, whereas a premise antecedent, presuppositional like *since*,
licenses none and admits positive polarity items instead. Languages may lexicalize the split:
Japanese *-ra* and German *falls* mark only hypothetical conditionals, *nara* and *wenn* mark
either ([lassiter-2025]).

## Main definitions

* `Reading`: the hypothetical and premise readings.
* `Reading.Felicitous`: the felicity condition a reading places on the antecedent, relative
  to a commitment Table.
* `Reading.AdmitsInAntecedent`: the polarity items a reading admits in its antecedent.
* `Marker`: a conditional marker with the readings it can mark; per-language entries live in
  `Fragments/{Language}/Conditionals.lean`.

## References

* [iatridou-1991]
* [haegeman-2003]
* [lassiter-2025]
-/

namespace Conditionals

open Commitment Polarity

/-- The readings of a conditional: the antecedent is supposed and left open, or echoes prior
discourse and is treated as established. -/
inductive Reading
  | hypothetical
  | premise
  deriving DecidableEq, Fintype, Repr

namespace Reading

section Felicity

variable {A W : Type*} (K : Table A W) (p : Set W)

/-- A reading is felicitous for the antecedent `p` when `p` meets its discourse condition: a
hypothetical conditional leaves `p` undecided in the common ground, a premise conditional needs
`p` echoed, committed to by some participant or already common ground. -/
def Felicitous : Reading → Prop
  | .hypothetical => ¬ K.Decided p
  | .premise => (∃ a, p ∈ K.dc a) ∨ p ∈ K.cg

variable {K p}

theorem premise_felicitous_of_mem_cg (h : p ∈ K.cg) : premise.Felicitous K p := .inr h

theorem premise_felicitous_of_shared [Nonempty A] (h : K.Shared p) : premise.Felicitous K p :=
  .inl <| (‹Nonempty A›).elim λ a => ⟨a, h a⟩

theorem not_hypothetical_felicitous_of_mem_cg (h : p ∈ K.cg) :
    ¬ hypothetical.Felicitous K p :=
  λ h' => h' (.inl h)

end Felicity

/-- A reading admits the polarity item `e` in its antecedent when a hypothetical antecedent,
the conditional-antecedent licensing context, licenses it, or a premise antecedent,
presuppositional like *since* and licensing nothing, hosts it as a positive polarity item
([iatridou-1991]). -/
def AdmitsInAntecedent : Reading → Item → Prop
  | .hypothetical, e => LicensingContext.conditionalAntecedent.licenses e
  | .premise, e => e.isPPI

instance (c : Reading) (e : Item) : Decidable (c.AdmitsInAntecedent e) := by
  cases c <;> unfold AdmitsInAntecedent <;> infer_instance

end Reading

/-- A conditional marker is a form together with the readings it can mark: Japanese *-ra* and
German *falls* mark only hypothetical conditionals, *nara*, *wenn*, and English *if* mark either
([lassiter-2025]). Per-language entries live in `Fragments/{Language}/Conditionals.lean`. -/
structure Marker where
  /-- The marker's citation form. -/
  form : String
  /-- The readings the marker can mark. -/
  readings : Finset Reading
  deriving DecidableEq

end Conditionals
