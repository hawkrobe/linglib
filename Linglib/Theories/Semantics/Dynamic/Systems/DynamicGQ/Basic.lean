import Linglib.Theories.Semantics.Dynamic.Core.DynamicTy2
import Linglib.Core.Mereology

/-!
# Pointwise Dynamic Generalized Quantifiers

Muskens/Brasoveanu-style dynamic GQ operators defined over the pointwise
`DRS S := S → S → Prop` type. These correspond to Charlow (2021) §2.

The key operators:
- `Evar`: existential dref introduction (equation 17)
- `Mvar`: mereological maximization (equation 18)
- `CardTest`: cardinality test (equation 19)
- `exactlyN_pw`: composed modified numeral "exactly N" (pointwise)

Charlow shows that in the pointwise setting, sequencing `Mvar` inside vs outside
`CardTest` yields pseudo-cumulative vs cumulative readings — and the pointwise
system can only derive pseudo-cumulative.

## References

- Charlow, S. (2021). Post-suppositions and semantic theory. *L&P* 44, 701–765.
  §2, equations 17–19.
- Brasoveanu, A. (2007). *Structured Nominal and Modal Reference*.
-/

namespace DynamicSemantics.DynamicGQ.Basic

open DynamicSemantics.Core.DynamicTy2
open Mereology

variable {S E : Type*}

/-- Existential dref introduction (equation 17): introduce a new referent
    satisfying P into the assignment at dref v.
    `Evar v P i j ⟺ ∃x. P(x) ∧ j = extend(i, v, x)` -/
def Evar [AssignmentStructure S E] (v : Dref S E) (P : E → Prop) : DRS S :=
  λ i j => ∃ (x : E), P x ∧ j = AssignmentStructure.extend i v x

/-- Mereological maximization (equation 18): retain only assignments where v
    is maximal in the output set of D.
    In the pointwise setting, this checks maximality of v(j) among all
    j reachable from i via D. -/
def Mvar (v : Dref S E) (D : DRS S) [PartialOrder E] : DRS S :=
  λ i j => D i j ∧ Mereology.isMaximal (λ x => ∃ (k : S), D i k ∧ v k = x) (v j)

/-- Cardinality test (equation 19): test that atomCount of v equals n.
    Identity on assignments (a test in the dynamic sense). -/
def CardTest (v : Dref S E) (n : Nat) [PartialOrder E] [Fintype E] : DRS S :=
  λ i j => i = j ∧ Mereology.atomCount E (v j) = n

/-- Transitive verb as DRS: test that R holds between two drefs. -/
def sawDRS (u v : Dref S E) (R : E → E → Prop) : DRS S :=
  test (λ i => R (u i) (v i))

/-- Composed pointwise "exactly N": E^v; M_v; n_v (equation 20). -/
def exactlyN_pw [AssignmentStructure S E] [PartialOrder E] [Fintype E]
    (v : Dref S E) (P : E → Prop) (n : Nat) : DRS S :=
  dseq (dseq (Evar v P) (Mvar v (Evar v P))) (CardTest v n)

/-- Pseudo-cumulative formula (5): M_v scopes over the cardinality test on u.
    "Exactly 3 boys saw exactly 5 movies" with pseudo-cumulative reading:
    M_v(E^v boys ; M_u(E^u movies ; saw u v) ; 5_u) ; 3_v -/
def pseudoCumulative [AssignmentStructure S E] [PartialOrder E] [Fintype E]
    (v u : Dref S E) (boys movies : E → Prop) (saw' : E → E → Prop) : DRS S :=
  dseq
    (Mvar v (dseq (dseq (Evar v boys) (Mvar u (dseq (Evar u movies) (sawDRS u v saw'))))
                   (CardTest u 5)))
    (CardTest v 3)

/-- Cumulative formula (6): cardinality tests scope outside both M operators.
    M_v(E^v boys ; M_u(E^u movies ; saw u v)) ; 5_u ; 3_v -/
def cumulative [AssignmentStructure S E] [PartialOrder E] [Fintype E]
    (v u : Dref S E) (boys movies : E → Prop) (saw' : E → E → Prop) : DRS S :=
  dseq (dseq
    (Mvar v (dseq (Evar v boys) (Mvar u (dseq (Evar u movies) (sawDRS u v saw')))))
    (CardTest u 5))
    (CardTest v 3)

end DynamicSemantics.DynamicGQ.Basic
