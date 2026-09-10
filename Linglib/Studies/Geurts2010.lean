import Linglib.Studies.GeurtsPouscoulous2009

/-!
# Geurts (2010): Quantity Implicatures

This file formalizes the textbook's case against conventionalism in section 7.3 of [geurts-2010],
which rests on [geurts-pouscoulous-2009]'s verification experiment. Conventionalist theories of
scalar inference agree that *some* is read as *some but not all* under an upward-entailing
quantifier such as *all* or *more than one*, and the stronger versions predict the same under a
non-monotone quantifier such as *exactly two*, while none predicts it under a downward-entailing
one; the experiment found no such readings. The three quantifiers of (62) are the earlier study's
`Quant`, and the weak and strong predictions are its `PredictsLocalSIWeak` and `PredictsLocalSI`
(`conventionalist_predictions`). Chapter 3's observation that a downward-entailing environment
reverses a scale, so that *not all* blocks the local inference, is the negated case
(`downward_entailing_blocks`).

## References

* [geurts-2010]
* [geurts-pouscoulous-2009]
-/

namespace Geurts2010

open Quantification GeurtsPouscoulous2009

/-- *Exactly two* is not upward entailing in its scope: two of three squares connected with some
circle, all three with some circle or other. -/
theorem exactlyTwo_not_scopeUp : ¬ ScopeUpwardMono (Quant.exactlyTwo.sem : GQ (Fin 3)) := by
  intro h
  have key := h (λ _ => True) (λ s => s = 0 ∨ s = 1) (λ _ => True) (λ _ _ => trivial)
  simp only [Quant.sem, exactly_n_sem] at key
  rw [count_eq_decidable (λ s : Fin 3 => True ∧ (s = 0 ∨ s = 1)),
    count_eq_decidable (λ _ : Fin 3 => True ∧ True)] at key
  revert key
  decide

/-- *Not all* is not upward entailing in its scope. -/
theorem notAll_not_scopeUp : ¬ ScopeUpwardMono (Quant.notAll.sem : GQ (Fin 3)) := λ h =>
  h (λ _ => True) (λ _ => False) (λ _ => True) (λ _ hf => hf.elim) (λ hall => hall 0 trivial)
    (λ _ _ => trivial)

/-- Section 7.3, (62): every conventionalist theory predicts the local reading under *all* and
*more than one*; only the stronger versions predict it under *exactly two*, which is neither
upward nor downward entailing in its scope. -/
theorem conventionalist_predictions :
    PredictsLocalSIWeak (Quant.all.sem : GQ (Fin 3)) ∧
      PredictsLocalSIWeak (Quant.moreThanOne.sem : GQ (Fin 3)) ∧
      ¬ PredictsLocalSIWeak (Quant.exactlyTwo.sem : GQ (Fin 3)) ∧
      PredictsLocalSI (Quant.exactlyTwo.sem : GQ (Fin 3)) :=
  ⟨all_predictsLocalSIWeak, moreThanOne_predictsLocalSIWeak, exactlyTwo_not_scopeUp,
   exactlyTwo_predictsLocalSI⟩

/-- Section 3.2: the downward-entailing scope of *not all* supports no local inference on either
version of the prediction. -/
theorem downward_entailing_blocks :
    ¬ PredictsLocalSI (Quant.notAll.sem : GQ (Fin 3)) ∧
      ¬ PredictsLocalSIWeak (Quant.notAll.sem : GQ (Fin 3)) :=
  ⟨notAll_not_predictsLocalSI, notAll_not_scopeUp⟩

end Geurts2010
