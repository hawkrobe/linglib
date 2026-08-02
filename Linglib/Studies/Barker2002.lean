import Linglib.Studies.HeimKratzer1998

/-!
# Barker (2002): Continuations and the Nature of Quantification

[barker-2002]'s thesis is that the generalized-quantifier type is the
continuation type — a fact the carrier states as
`Quantification.quantifier_eq_cont` — and that this identification does
real work: continuizing application and varying the evaluation order
derives quantification in situ, with the two orders yielding the two
scope readings of a transitive clause. This study carries out that
derivation and checks the paper's coverage claim against movement: on the
shared toy model, the two evaluation orders compute exactly the two
propositions [heim-kratzer-1998]'s quantifier raising derives, with no
movement and no storage.
-/

namespace Barker2002

open Quantification (Quantifier individual every_sem some_sem)
open Semantics.Montague
open Semantics.Montague.ToyLexicon (person_sem)

variable {α E : Type}

/-! ### Scope ambiguity as evaluation order

Continuized application can evaluate the function's or the argument's
continuation first. On a transitive clause the two orders deliver the
two relative scopes — ambiguity without movement. -/

/-- Continuized application, function's continuation first: the left
quantifier takes wide scope. -/
def combineFunFirst (mf : Cont Prop (α → Prop)) (mx : Cont Prop α) : Cont Prop Prop :=
  mf <*> mx

/-- Continuized application, argument's continuation first: the right
quantifier takes wide scope. -/
def combineArgFirst (mf : Cont Prop (α → Prop)) (mx : Cont Prop α) : Cont Prop Prop :=
  λ κ => mx (λ x => mf (λ f => κ (f x)))

/-- Function-first evaluation of a transitive clause is surface scope:
the subject quantifier outscopes the object. -/
theorem combineFunFirst_surface (q₁ q₂ : Quantifier E) (rel : E → E → Prop) :
    ContT.lower (combineFunFirst (rel <$> (q₁ : Cont Prop E)) q₂) =
    q₁ (λ x => q₂ (λ y => rel x y)) := rfl

/-- Argument-first evaluation of the same clause is inverse scope: the
object quantifier outscopes the subject. -/
theorem combineArgFirst_inverse (q₁ q₂ : Quantifier E) (rel : E → E → Prop) :
    ContT.lower (combineArgFirst (rel <$> (q₁ : Cont Prop E)) q₂) =
    q₂ (λ y => q₁ (λ x => rel x y)) := rfl

/-- On lifted individuals the two orders agree — continuizing the whole
grammar is harmless for names; ambiguity is detectable only for genuine
quantifiers. -/
theorem combine_orders_agree_on_individuals (a b : E) (rel : E → E → Prop) :
    ContT.lower (combineFunFirst (rel <$> individual a) (individual b)) =
    ContT.lower (combineArgFirst (rel <$> individual a) (individual b)) := rfl

/-! ### The same readings as movement

The paper's coverage claim: in-situ continuized application derives
exactly the readings quantifier raising derives. On the toy model of
`Studies/HeimKratzer1998.lean`, the two evaluation orders of "every
person sees some person" compute the two QR propositions on the nose. -/

/-- Function-first evaluation computes QR's surface-scope proposition. -/
theorem funFirst_eq_qr_surface :
    ContT.lower (combineFunFirst
      ((λ x y => ToyLexicon.sees_sem y x) <$>
        (every_sem person_sem : Quantifier ToyEntity))
      (some_sem person_sem)) = HeimKratzer1998.surfaceScopeProp := rfl

/-- Argument-first evaluation computes QR's inverse-scope proposition. -/
theorem argFirst_eq_qr_inverse :
    ContT.lower (combineArgFirst
      ((λ x y => ToyLexicon.sees_sem y x) <$>
        (every_sem person_sem : Quantifier ToyEntity))
      (some_sem person_sem)) = HeimKratzer1998.inverseScopeProp := rfl

/-- The ambiguity is semantically real: the two evaluation orders yield
genuinely different propositions on the toy model. -/
theorem evaluation_orders_differ :
    ContT.lower (combineFunFirst
      ((λ x y => ToyLexicon.sees_sem y x) <$>
        (every_sem person_sem : Quantifier ToyEntity))
      (some_sem person_sem)) ≠
    ContT.lower (combineArgFirst
      ((λ x y => ToyLexicon.sees_sem y x) <$>
        (every_sem person_sem : Quantifier ToyEntity))
      (some_sem person_sem)) := by
  rw [funFirst_eq_qr_surface, argFirst_eq_qr_inverse]
  exact HeimKratzer1998.scope_readings_differ

end Barker2002
