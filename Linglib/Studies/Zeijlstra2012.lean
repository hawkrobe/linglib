module

public import Linglib.Syntax.Minimalist.Agree.Basic
public import Linglib.Syntax.Minimalist.Phase.Domain

/-!
# Zeijlstra (2012): There Is Only One Way to Agree

This file formalizes [zeijlstra-2012]'s proposal that Agree applies upward only: an element
carrying an uninterpretable feature is checked by the closest c-commanding element carrying the
matching interpretable feature (`isUpwardGoalIn`), reversing the direction of
[chomsky-2000]'s Agree, and several such elements may be checked by one goal at once
(`MultipleAgree`). The evidence is the concord phenomena, Negative Concord and Sequence of
Tense, whose configurations place one interpretable feature above one or more uninterpretable
ones. In Sequence of Tense, an abstract past operator carries `[iPAST]` and every finite past
morpheme, the matrix verb included, carries a vacuous `[uPAST]`; the matrix and the subordinate
verb of *John said Mary was ill* both Agree upward with the operator (`sot_multipleAgree`),
which no downward-probing Agree could establish (`sot_not_downward`). Agree across a phase
boundary requires the phase edge to participate: the corollary of phase theory that
distinguishes the two phenomena, since the embedding complementizer carries an uninterpretable
tense feature but no uninterpretable negative feature, so Sequence of Tense crosses the
clause boundary (`sot_licit`) while Negative Concord does not (`nc_across_cp_illicit`,
`nc_clausemate_licit`).

## Implementation notes

* Feature bearers are given by predicates on the leaves of a syntactic object, as the paper
  annotates its bracketings; the lexical items themselves carry only categories and selection.
* The phase-edge condition is stated for a phase head leaf through the substrate's phase
  domains: when the probe lies in the phase interior and the goal outside the phase, some
  element of the phase edge must carry the uninterpretable feature.
* The semantics of the subordinate past morpheme as a relative non-future, which the paper
  leaves to later work, is not formalized.

## References

* [zeijlstra-2012]
* [chomsky-2000]
* [chomsky-2001]
-/

@[expose] public section

namespace Zeijlstra2012

open Minimalist Minimalist.SyntacticObject

variable {root probe goal : SyntacticObject} {pred : SyntacticObject → Prop}

/-! ### Upward Agree -/

/-- Upward Agree: `goal`, carrying the interpretable feature marked by `pred`, c-commands the
uninterpretable `probe` and is the closest such element, no other `pred`-node c-commanding the
probe being asymmetrically c-commanded by it. -/
def isUpwardGoalIn (root probe goal : SyntacticObject) (pred : SyntacticObject → Prop) : Prop :=
  cCommandsIn root goal probe ∧ pred goal ∧
    ∀ x ∈ root.terms, cCommandsIn root x probe → pred x → ¬ asymCCommandsIn root goal x

instance [DecidablePred pred] (root probe goal : SyntacticObject) :
    Decidable (isUpwardGoalIn root probe goal pred) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ ∀ x ∈ root.terms, _))

/-- Multiple Agree: every probe in the list is checked by the same goal. -/
def MultipleAgree (root goal : SyntacticObject) (probes : List SyntacticObject)
    (pred : SyntacticObject → Prop) : Prop :=
  ∀ p ∈ probes, isUpwardGoalIn root p goal pred

instance [DecidablePred pred] (root goal : SyntacticObject) (probes : List SyntacticObject) :
    Decidable (MultipleAgree root goal probes pred) :=
  inferInstanceAs (Decidable (∀ p ∈ probes, _))

/-- The phase-edge condition on Agree across a phase: with `ℓ` a phase head, a probe in the
phase interior may Agree with a goal outside the phase only if an element of the phase edge
carries the uninterpretable feature `uF` too. -/
def EdgeParticipates (root probe goal : SyntacticObject) (uF : SyntacticObject → Prop)
    (ℓ : LIToken) : Prop :=
  probe ∈ root.phaseInterior ℓ → goal ∉ root.phase ℓ → ∃ e ∈ root.phaseEdge ℓ, uF e

instance {uF : SyntacticObject → Prop} [DecidablePred uF] (root probe goal : SyntacticObject)
    (ℓ : LIToken) : Decidable (EdgeParticipates root probe goal uF ℓ) :=
  have : Decidable (∃ e ∈ root.phaseEdge ℓ, uF e) := Multiset.decidableExistsMultiset
  inferInstanceAs (Decidable (_ → _ → _))

/-! ### Sequence of Tense -/

/-- The abstract past operator carrying `[iPAST]`. -/
def opPast : PlanarSyntacticObject := .leaf ⟨.simple .T [.V] "Op[PAST]", 1⟩
def john : PlanarSyntacticObject := .leaf ⟨.simple .D [] "John", 2⟩
/-- The matrix verb, with its own vacuous `[uPAST]`. -/
def said : PlanarSyntacticObject := .leaf ⟨.simple .V [.C] "said", 3⟩
/-- The embedding complementizer, carrying `[uT]`. -/
def thatC : PlanarSyntacticObject := .leaf ⟨.simple .C [.V] "that", 4⟩
def mary : PlanarSyntacticObject := .leaf ⟨.simple .D [] "Mary", 5⟩
/-- The subordinate verb, with `[uPAST]`. -/
def was : PlanarSyntacticObject := .leaf ⟨.simple .V [.A] "was", 6⟩
def ill : PlanarSyntacticObject := .leaf ⟨.simple .A [] "ill", 7⟩

/-- *John said Mary was ill*, with the past operator above both verbs. -/
def sot : PlanarSyntacticObject :=
  {john, {opPast, {said, {thatC, {mary, {was, ill}}}}}}

/-- The bearers of `[iPAST]`. -/
def iPast (s : SyntacticObject) : Prop := s = opPast

private instance : DecidablePred iPast := λ s => inferInstanceAs (Decidable (s = _))

/-- The bearers of `[uPAST]` or `[uT]`: both finite verbs and the complementizer. -/
def uPast (s : SyntacticObject) : Prop := s = said ∨ s = was ∨ s = thatC

private instance : DecidablePred uPast := λ _ => inferInstanceAs (Decidable (_ ∨ _ ∨ _))

/-- Both past morphemes Agree upward with the single past operator. -/
theorem sot_multipleAgree : MultipleAgree sot opPast [said, was] iPast := by decide

/-- Neither verb c-commands the operator, so no downward-probing Agree relates them. -/
theorem sot_not_downward : ¬ cCommandsIn sot said opPast ∧ ¬ cCommandsIn sot was opPast := by
  decide

/-- Sequence of Tense crosses the clause boundary: the subordinate verb sits in the interior of
the phase headed by the complementizer, which itself carries an uninterpretable tense feature
and so lies in the participating edge. -/
theorem sot_licit :
    EdgeParticipates sot was opPast uPast ⟨.simple .C [.V] "that", 4⟩ := by decide

/-! ### Negative Concord -/

def gianni : PlanarSyntacticObject := .leaf ⟨.simple .D [] "Gianni", 11⟩
/-- The negative marker carrying `[iNEG]`. -/
def non : PlanarSyntacticObject := .leaf ⟨.simple .Neg [.T] "non", 12⟩
def ha : PlanarSyntacticObject := .leaf ⟨.simple .T [.V] "ha", 13⟩
def detto : PlanarSyntacticObject := .leaf ⟨.simple .V [.D] "detto", 14⟩
def dettoC : PlanarSyntacticObject := .leaf ⟨.simple .V [.C] "detto", 15⟩
def niente : PlanarSyntacticObject := .leaf ⟨.simple .D [.P] "niente", 16⟩
def a : PlanarSyntacticObject := .leaf ⟨.simple .P [.D] "a", 17⟩
def nessuno : PlanarSyntacticObject := .leaf ⟨.simple .D [] "nessuno", 18⟩
/-- The embedding complementizer, without any negative feature. -/
def che : PlanarSyntacticObject := .leaf ⟨.simple .C [.T] "che", 19⟩
def ha₂ : PlanarSyntacticObject := .leaf ⟨.simple .T [.V] "ha", 20⟩
def telefonato : PlanarSyntacticObject := .leaf ⟨.simple .V [.P] "telefonato", 21⟩

/-- *Gianni non ha detto niente a nessuno*: two n-words under one negative marker. -/
def ncClausemate : PlanarSyntacticObject :=
  {gianni, {non, {ha, {detto, {niente, {a, nessuno}}}}}}

/-- *Gianni non ha detto che ha telefonato a nessuno*: the n-word inside an embedded clause. -/
def ncAcrossCP : PlanarSyntacticObject :=
  {gianni, {non, {ha, {dettoC, {che, {ha₂, {telefonato, {a, nessuno}}}}}}}}

/-- The bearers of `[iNEG]`. -/
def iNeg (s : SyntacticObject) : Prop := s = non

private instance : DecidablePred iNeg := λ s => inferInstanceAs (Decidable (s = _))

/-- The bearers of `[uNEG]`, the n-words. -/
def uNeg (s : SyntacticObject) : Prop := s = niente ∨ s = nessuno

private instance : DecidablePred uNeg := λ _ => inferInstanceAs (Decidable (_ ∨ _))

/-- Both n-words Agree upward with the negative marker. -/
theorem nc_clausemate_multipleAgree : MultipleAgree ncClausemate non [niente, nessuno] iNeg := by
  decide

/-- Within the clause no phase intervenes, so the concord relation is licit. -/
theorem nc_clausemate_licit :
    EdgeParticipates ncClausemate nessuno non uNeg ⟨.simple .C [.T] "che", 19⟩ := by decide

/-- Across the embedded clause the complementizer carries no negative feature, so the phase
edge does not participate and the concord relation is blocked. -/
theorem nc_across_cp_illicit :
    ¬ EdgeParticipates ncAcrossCP nessuno non uNeg ⟨.simple .C [.T] "che", 19⟩ := by decide

end Zeijlstra2012
