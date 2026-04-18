import Linglib.Core.Case.Basic
/-!
# Split Ergativity
@cite{blake-1994} @cite{dixon-1994}

A `SplitErgativity Factor` is parameterised by the conditioning factor
(aspect, person, animacy, …); `alignment` projects to either the
ergative or accusative family. The Hindi aspect-conditioned split
(perfective ⇒ ergative; imperfective ⇒ accusative) is the canonical
worked example.
-/

namespace Core

/-- A split-ergative system (@cite{blake-1994}, @cite{dixon-1994}):
    alignment varies by some conditioning factor. -/
structure SplitErgativity (Factor : Type) where
  ergCondition : Factor → Bool

def SplitErgativity.alignment {Factor : Type} (split : SplitErgativity Factor)
    (f : Factor) : AlignmentFamily :=
  if split.ergCondition f then .ergative else .accusative

inductive Aspect where
  | perfective
  | imperfective
  deriving DecidableEq, Repr

def hindiSplit : SplitErgativity Aspect :=
  { ergCondition := fun a => a == .perfective }

theorem hindi_perfective_erg :
    hindiSplit.alignment .perfective = .ergative := rfl

theorem hindi_imperfective_acc :
    hindiSplit.alignment .imperfective = .accusative := rfl

end Core
