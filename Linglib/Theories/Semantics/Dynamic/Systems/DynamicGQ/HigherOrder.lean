import Linglib.Core.Continuation
import Linglib.Theories.Semantics.Dynamic.Systems.DynamicGQ.Basic

/-!
# Higher-Order Dynamic Generalized Quantifiers

Charlow's (2021) first solution to cumulative readings: higher-order
dynamic GQs using the continuation monad. A modified numeral like
"exactly 3" denotes a *scope-taking* dynamic meaning — type
`(DRS S → DRS S) → DRS S` — rather than a flat `DRS S`.

The key insight: the continuation structure allows the cardinality test
to take scope outside maximization, producing cumulative readings via
LOWER (Barker & Shan 2014).

## References

- Charlow, S. (2021). Post-suppositions and semantic theory. *L&P* 44, 701–765.
  §3–4, equations 24–27.
- Barker, C. & Shan, C. (2014). *Continuations and Natural Language*. OUP.
-/

namespace Semantics.Dynamic.DynamicGQ.HigherOrder

open Semantics.Dynamic.Core.DynamicTy2
open Semantics.Dynamic.DynamicGQ.Basic
open Core.Continuation
open Mereology

variable {S E : Type*}

/-- Higher-order dynamic GQ: a continuized DRS.
    Type: `(DRS S → DRS S) → DRS S`.
    This is `Cont (DRS S) (DRS S)`, but we define it as an abbreviation
    for clarity in the linguistic application. -/
abbrev HODGQ (S : Type*) := Cont (DRS S) (DRS S)

/-- Lift a flat DRS to higher-order (trivially scope-taking).
    This is Cont.pure specialized to DRS. -/
def liftGQ (D : DRS S) : HODGQ S := Cont.pure D

/-- Lower a higher-order GQ back to flat DRS.
    Applies the identity continuation. -/
def lowerGQ (m : HODGQ S) : DRS S := Cont.lower m

/-- "Exactly N" as higher-order GQ (equation 24):
    `λc. c(M_v(E^v P ; ·)) ; n_v`
    The cardinality test `n_v` is placed OUTSIDE the continuation,
    enabling it to scope over other quantifiers. -/
def exactlyN_ho [AssignmentStructure S E] [PartialOrder E] [Fintype E]
    (v : Dref S E) (P : E → Prop) (n : Nat) : HODGQ S :=
  λ c => dseq (c (Mvar v (Evar v P))) (CardTest v n)

/-- Combine two higher-order GQs (Appendix A, equation 114):
    Thread the inner GQ through the outer's continuation. -/
def combineHO (outer inner : HODGQ S) : HODGQ S :=
  Cont.bind outer (λ D₁ => Cont.bind inner (λ D₂ => Cont.pure (dseq D₁ D₂)))

/-- Combine + Lower on two "exactly N" GQs yields the cumulative logical form.
    TODO: Prove by unfolding definitions. -/
theorem ho_cumulative_derivation [AssignmentStructure S E] [PartialOrder E] [Fintype E]
    (v u : Dref S E) (boys movies : E → Prop) (saw' : E → E → Prop) :
    lowerGQ (combineHO (exactlyN_ho v boys 3) (exactlyN_ho u movies 5)) =
    dseq (dseq
      (Mvar v (dseq (Evar v boys) (Mvar u (dseq (Evar u movies) (sawDRS u v saw')))))
      (CardTest u 5))
      (CardTest v 3) := by
  sorry

end Semantics.Dynamic.DynamicGQ.HigherOrder
