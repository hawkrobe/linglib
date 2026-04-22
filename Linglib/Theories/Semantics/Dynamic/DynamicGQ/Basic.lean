import Linglib.Theories.Semantics.Dynamic.Core.DynamicTy2
import Linglib.Core.Mereology

/-!
# Pointwise Dynamic Generalized Quantifiers
@cite{brasoveanu-2007} @cite{charlow-2021}

@cite{muskens-1996}/@cite{brasoveanu-2007}-style dynamic GQ operators defined over the pointwise
`DRS S := S → S → Prop` type. These correspond to @cite{charlow-2021} §2.

The key operators:
- `Evar`: existential dref introduction (equation 17)
- `Mvar`: mereological maximization (equation 18)
- `CardTest`: cardinality test (equation 19)
- `exactlyN_pw`: composed modified numeral "exactly N" (pointwise)

Charlow shows that in the pointwise setting, sequencing `Mvar` inside vs outside
`CardTest` yields pseudo-cumulative vs cumulative readings — and the pointwise
system can only derive pseudo-cumulative.

## Cross-cutting smell: five DynamicGQ variants, no "which to use" map

`DynamicGQ/` hosts five formalizations of dynamic generalized quantifiers,
each coping with the cumulative-reading problem differently. They are not
ranked or ordered; downstream consumers must pick by hand.

| Variant | State type | Cumulative? | File |
|---------|-----------|-------------|------|
| Pointwise (this file) | `S → S → Prop` | ✗ pseudo-cumulative only | `DynamicGQ/Basic.lean` |
| Update-theoretic | `State W E → State W E` | ✓ via non-distributive `Mvar_u` | `DynamicGQ/UpdateTheoretic.lean` |
| Higher-order tower | `((DRS S → DRS S) → DRS S) → DRS S` | ✓ via `LOWER` placement | `DynamicGQ/HigherOrder.lean` |
| Post-suppositional | `Writer (DRS S) A` | ✓ via deferred cardinality tests | `DynamicGQ/PostSuppositional.lean` |
| Subtype-polymorphic | `DRS S` with `Completeness` enum | rules out pseudo-cumulative by typing | `DynamicGQ/SubtypePolymorphism.lean` |

All five are @cite{charlow-2021}'s work — the paper canvasses them as
alternative repairs to the pointwise system's failure on
`exactly 3 boys saw exactly 5 movies`. The variants are not equivalent:
Update-theoretic and Higher-order produce genuine cumulative readings
operationally; Post-suppositional defers the cardinality test as
conventional implicature; Subtype-polymorphic blocks the pseudo-
cumulative reading by type discipline rather than by deriving the
cumulative one. New consumers should pick based on what they need:
flat state-threading (Update-theoretic), explicit scope (Higher-order),
post-suppositional content (Post-suppositional), or static well-
formedness (Subtype-polymorphic). Pointwise is the baseline and the
empirical counterexample, kept here primarily as the reference against
which the other four are measured.

-/

namespace Semantics.Dynamic.DynamicGQ.Basic

open Semantics.Dynamic.Core
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
    M_v(E^v boys; M_u(E^u movies; saw u v); 5_u); 3_v -/
def pseudoCumulative [AssignmentStructure S E] [PartialOrder E] [Fintype E]
    (v u : Dref S E) (boys movies : E → Prop) (saw' : E → E → Prop) : DRS S :=
  dseq
    (Mvar v (dseq (dseq (Evar v boys) (Mvar u (dseq (Evar u movies) (sawDRS u v saw'))))
                   (CardTest u 5)))
    (CardTest v 3)

/-- Cumulative formula (6): cardinality tests scope outside both M operators.
    M_v(E^v boys; M_u(E^u movies; saw u v)); 5_u; 3_v -/
def cumulative [AssignmentStructure S E] [PartialOrder E] [Fintype E]
    (v u : Dref S E) (boys movies : E → Prop) (saw' : E → E → Prop) : DRS S :=
  dseq (dseq
    (Mvar v (dseq (Evar v boys) (Mvar u (dseq (Evar u movies) (sawDRS u v saw')))))
    (CardTest u 5))
    (CardTest v 3)

end Semantics.Dynamic.DynamicGQ.Basic
