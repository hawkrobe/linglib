module

public import Eval.Basic
public import Linglib.Studies.Schlenker2009
public import Linglib.Studies.Kalomoiros2023

/-!
# Accounts of presupposition projection

The accounts of projection in the propositional fragment that linglib formalizes
(`Eval.Projection.Account`), each registered by the theory's own acceptability predicate, from
`Semantics/Presupposition` or the paper's study (`Account.Accepts`): [heim-1983]'s context change
potentials with [beaver-2001]'s disjunction, [peters-1979]'s filtering connectives, the
Transparency, local satisfaction, Strong Kleene and supervaluationist theories of
[schlenker-2009] and its manuscript [schlenker-2008b], each checked incrementally and
symmetrically, and [kalomoiros-2023]'s Limited Symmetry. An account is stronger than another when
every context that accepts a formula by the first accepts it by the second, so that it predicts
presuppositions at least as strong (`Account.Stronger`).

## References

* [heim-1983]
* [beaver-2001]
* [peters-1979]
* [schlenker-2009]
* [schlenker-2008b]
* [kalomoiros-2023]
-/

@[expose] public section

namespace Eval.Projection

open Presupposition

/-- The accounts of projection in the propositional fragment. -/
inductive Account where
  /-- [heim-1983]'s context change potentials, with [beaver-2001]'s disjunction. -/
  | dynamic
  /-- [peters-1979]'s filtering connectives. -/
  | filtering
  /-- [schlenker-2009]'s Transparency, over every good final. -/
  | transparencyIncremental
  /-- [schlenker-2009]'s Transparency, over the actual sentence. -/
  | transparencySymmetric
  /-- [schlenker-2009]'s local satisfaction, over every good final. -/
  | satisfactionIncremental
  /-- [schlenker-2009]'s local satisfaction, over the actual sentence. -/
  | satisfactionSymmetric
  /-- Strong Kleene definedness after each trigger with every good final ([schlenker-2008b]). -/
  | kleeneIncremental
  /-- Strong Kleene definedness of the sentence ([schlenker-2008b]). -/
  | kleeneSymmetric
  /-- Supervaluationist definedness after each trigger with every good final
  ([schlenker-2008b]). -/
  | supervaluationIncremental
  /-- Supervaluationist definedness of the sentence ([schlenker-2008b]). -/
  | supervaluationSymmetric
  /-- [kalomoiros-2023]'s Limited Symmetry. -/
  | limitedSymmetry
  deriving DecidableEq, Repr

namespace Account

variable {Atom W : Type*}

/-- When an account accepts a formula in a context, under an interpretation of the atoms: the
theory's own predicate. -/
noncomputable def Accepts : Account → (Atom → Set W) → Set W → Formula Atom → Prop
  | dynamic => fun I C F ↦ (F.ccp I).Admits C
  | filtering => fun I C F ↦ (F.filter I).Admits C
  | transparencyIncremental => Schlenker2009.TranspI
  | transparencySymmetric => Schlenker2009.TranspS
  | satisfactionIncremental => Schlenker2009.SatI
  | satisfactionSymmetric => Schlenker2009.SatS
  | kleeneIncremental => Schlenker2009.KleeneI
  | kleeneSymmetric => Schlenker2009.KleeneS
  | supervaluationIncremental => Schlenker2009.SuperI
  | supervaluationSymmetric => Schlenker2009.SuperS
  | limitedSymmetry => Kalomoiros2023.TranspLS

/-- `a` predicts presuppositions at least as strong as `b`: every context that accepts a formula
by `a` accepts it by `b`. -/
def Stronger (a b : Account) : Prop :=
  ∀ (Atom W : Type) (I : Atom → Set W) (C : Set W) (F : Formula Atom),
    a.Accepts I C F → b.Accepts I C F

theorem Stronger.refl (a : Account) : a.Stronger a := fun _ _ _ _ _ h ↦ h

theorem Stronger.trans {a b c : Account} (hab : a.Stronger b) (hbc : b.Stronger c) :
    a.Stronger c :=
  fun Atom W I C F h ↦ hbc Atom W I C F (hab Atom W I C F h)

end Account

end Eval.Projection
