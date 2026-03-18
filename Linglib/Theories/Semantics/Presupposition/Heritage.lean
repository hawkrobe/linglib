import Linglib.Core.Semantics.Presupposition

/-!
# Heritage Functions
@cite{karttunen-peters-1979} @cite{beaver-2001}

Karttunen & Peters (1979) proposed that presupposition projection is computed
by a SEPARATE compositional function — the "heritage function" — independent
of truth-conditional composition. Each connective has both a truth-conditional
rule and a heritage rule that determines how presuppositions of the parts
contribute to presuppositions of the whole.

@cite{beaver-2001} Ch. 2.3 reviews this approach and shows it is empirically
equivalent to Heim's CCP filtering for the basic connectives.

## Heritage vs. Filtering

The heritage function approach and CCP filtering make the same predictions
for conjunction and implication. The key difference is architectural:
- Heritage: two separate composition dimensions (truth + heritage)
- CCP: one dimension (context change) from which projection follows

We prove the equivalence (`heritage_eq_impFilter_presup`) to connect them.

## Symmetry Problem

For disjunction, heritage functions naturally give a SYMMETRIC prediction
(both disjuncts filter each other), matching `PrProp.orFilter`. This
contrasts with the ASYMMETRIC CCP prediction via De Morgan (`CCP.disj`).
@cite{beaver-2001} Ch. 2 identifies this as the central tension in
presupposition projection theory.
-/

namespace Semantics.Presupposition.Heritage

open Core.Presupposition
open Core.Proposition

variable {W : Type*}

/-- A heritage system pairs truth-conditional composition with a
    separate presupposition projection function.

    @cite{karttunen-peters-1979}: each connective has a "heritage
    function" that computes the resulting presupposition from the
    presuppositions and assertions of the parts. -/
structure HeritageSystem (W : Type*) where
  /-- Truth-conditional composition (including presupposition structure). -/
  compose : PrProp W → PrProp W → PrProp W
  /-- Heritage function: computes resulting presupposition. -/
  heritage : PrProp W → PrProp W → BProp W

/-- Karttunen & Peters heritage for conditional (if p then q):
    the presupposition of the conditional is p.presup ∧ (p.assertion → q.presup).

    This is Karttunen's (1973) filtering condition formalized as
    a heritage function: the antecedent's presupposition must hold,
    and the consequent's presupposition must hold given the antecedent. -/
def heritageConditional : HeritageSystem W where
  compose := PrProp.impFilter
  heritage := λ p q w => p.presup w && (!p.assertion w || q.presup w)

/-- Karttunen & Peters heritage for conjunction (p and q):
    the presupposition is p.presup ∧ (p.assertion → q.presup). -/
def heritageConjunction : HeritageSystem W where
  compose := PrProp.andFilter
  heritage := λ p q w => p.presup w && (!p.assertion w || q.presup w)

/-- Heritage for negation (not p): presupposition = p.presup. -/
def heritageNeg (p : PrProp W) : BProp W := p.presup

/-- Heritage for conditional EQUALS impFilter presupposition.

    This is the key bridge theorem: Karttunen & Peters' heritage function
    for conditionals computes the same presupposition as Heim's filtering
    implication. @cite{beaver-2001} Ch. 3 shows this equivalence. -/
theorem heritage_eq_impFilter_presup (p q : PrProp W) :
    heritageConditional.heritage p q = (PrProp.impFilter p q).presup := rfl

/-- Heritage for conjunction EQUALS andFilter presupposition. -/
theorem heritage_eq_andFilter_presup (p q : PrProp W) :
    heritageConjunction.heritage p q = (PrProp.andFilter p q).presup := rfl

/-- Heritage for negation preserves presupposition. -/
theorem heritageNeg_eq_neg_presup (p : PrProp W) :
    heritageNeg p = (PrProp.neg p).presup := rfl

/-- Symmetric heritage for disjunction (p or q).

    The heritage is:
      (¬p.assertion → q.presup) ∧ (¬q.assertion → p.presup) ∧ (p.presup ∨ q.presup)

    This is Karttunen & Peters' symmetric prediction for disjunction,
    formalized as `PrProp.orFilter`. Contrast with the ASYMMETRIC CCP
    prediction via De Morgan (`CCP.disj`). @cite{beaver-2001} Ch. 2
    identifies this divergence as the "symmetry problem." -/
def heritageDisjunction : HeritageSystem W where
  compose := PrProp.orFilter
  heritage := λ p q w =>
    (!p.assertion w || q.presup w) &&
    (!q.assertion w || p.presup w) &&
    (p.presup w || q.presup w)

/-- Heritage for disjunction EQUALS orFilter presupposition. -/
theorem heritage_eq_orFilter_presup (p q : PrProp W) :
    heritageDisjunction.heritage p q = (PrProp.orFilter p q).presup := rfl

/-- Heritage functions are compositional: the heritage of a complex
    sentence is determined by the heritages and assertions of its parts.
    This is the defining architectural property that distinguishes the
    K&P approach from CCP. -/
theorem heritage_compositional_conditional (p q : PrProp W) (w : W) :
    heritageConditional.heritage p q w =
    (p.presup w && (!p.assertion w || q.presup w)) := rfl

end Semantics.Presupposition.Heritage
