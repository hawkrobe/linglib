import Linglib.Semantics.Quantification.Defs
import Linglib.Semantics.Composition.Cont
import Linglib.Semantics.Composition.Combinator

/-!
# Barker (2002): Continuations and the Nature of Quantification

[barker-2002]'s thesis is an identification: the generalized-quantifier
type is the continuation type. A quantificational noun phrase denotes a
function on its own continuation, so quantification is what continuation
passing looks like in natural language — no movement or storage needed.
This study states the identification over linglib's carriers: `Quantifier`
is `Cont Prop` definitionally, Montague lift (`individual`) is the monadic
unit and the `T` combinator, and continuizing application in its two
possible evaluation orders yields exactly the two scope readings of a
transitive clause, which is the paper's account of scope ambiguity.
-/

namespace Barker2002

open Quantification (Quantifier individual)

variable {α E : Type}

/-! ### The identification -/

/-- The generalized-quantifier type is the continuation type: a
quantifier is a computation handed its own scope. -/
theorem quantifier_eq_cont : Quantifier α = Cont Prop α := rfl

/-- A proper name denotes its lifted individual, and lifting is the
continuation monad's unit. -/
theorem individual_eq_pure (a : α) : individual a = (pure a : Cont Prop α) := rfl

/-- The same lift is combinatory logic's `T` (type-raising), closing the
circle with the categorial tradition. -/
theorem individual_eq_T (a : α) : individual a = Combinator.T (β := Prop) a := rfl

/-! ### Scope ambiguity as evaluation order

Continuized application can evaluate the function's or the argument's
continuation first. The two orders are interdefinable choices, and on a
transitive clause they deliver the two relative scopes — ambiguity
without movement. -/

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

/-- On lifted individuals the two orders agree — scope ambiguity is
detectable only for genuine quantifiers, so continuizing the whole
grammar is harmless for names. -/
theorem combine_orders_agree_on_individuals (a b : E) (rel : E → E → Prop) :
    ContT.lower (combineFunFirst (rel <$> individual a) (individual b)) =
    ContT.lower (combineArgFirst (rel <$> individual a) (individual b)) := rfl

end Barker2002
