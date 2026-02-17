import Linglib.Core.Continuation
import Linglib.Theories.Semantics.Dynamic.Systems.DynamicGQ.Basic

/-!
# Higher-Order Dynamic Generalized Quantifiers

Charlow's (2021) first solution to cumulative readings: higher-order
dynamic GQs using a "tower" continuation type. A modified numeral like
"exactly 3" denotes a *scope-taking* dynamic meaning — type
`((DRS S → DRS S) → DRS S) → DRS S` — rather than a flat `DRS S`.

The key insight: the tower structure allows the nuclear scope (VP body) to
be placed INSIDE maximization while the cardinality test escapes OUTSIDE,
producing genuine cumulative readings via LOWER (Barker & Shan 2014).

The simpler `HODGQ` type `(DRS S → DRS S) → DRS S` (= `Cont (DRS S) (DRS S)`)
cannot achieve this because its continuation receives an already-maximized
flat DRS — the nuclear scope can only be placed outside maximization.

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

-- ════════════════════════════════════════════════════
-- § Flat higher-order GQs (HODGQ)
-- ════════════════════════════════════════════════════

/-- Higher-order dynamic GQ: a continuized DRS.
    Type: `(DRS S → DRS S) → DRS S`.
    This is `Cont (DRS S) (DRS S)`, useful for scope-taking in general
    but insufficient for cumulative readings (see `TowerGQ` below). -/
abbrev HODGQ (S : Type*) := Cont (DRS S) (DRS S)

/-- Lift a flat DRS to higher-order (trivially scope-taking).
    This is Cont.pure specialized to DRS. -/
def liftGQ (D : DRS S) : HODGQ S := Cont.pure D

/-- Lower a higher-order GQ back to flat DRS.
    Applies the identity continuation. -/
def lowerGQ (m : HODGQ S) : DRS S := Cont.lower m

-- ════════════════════════════════════════════════════
-- § Tower GQs for cumulative readings
-- ════════════════════════════════════════════════════

/-- Tower-type dynamic GQ (Charlow 2021 §3, equation 24).

    The continuation receives a *scope-taking function* `DRS S → DRS S`
    rather than a flat DRS. This allows the nuclear scope (VP body) to be
    placed INSIDE maximization while the cardinality test escapes outside.

    In Barker & Shan's tower notation, this is `[DRS S | DRS S → DRS S]`,
    the type of an expression that contributes a `DRS S → DRS S` at the
    local level but produces a `DRS S` at the top level. -/
abbrev TowerGQ (S : Type*) := ((DRS S → DRS S) → DRS S) → DRS S

/-- "Exactly N" as tower GQ (equation 24):
    `λk. k(λbody. M_v(E^v P ; body)) ; n_v`

    The continuation `k` receives a scope-taker `λbody. M_v(E^v P ; body)`,
    allowing the nuclear scope to be threaded inside maximization.
    The cardinality test `n_v` is placed OUTSIDE the continuation,
    ensuring it scopes over any embedded operators. -/
def exactlyN_tower [AssignmentStructure S E] [PartialOrder E] [Fintype E]
    (v : Dref S E) (P : E → Prop) (n : Nat) : TowerGQ S :=
  λ k => dseq (k (λ body => Mvar v (dseq (Evar v P) body))) (CardTest v n)

/-- The cumulative derivation (equation 27) via tower composition.

    For "exactly 3 boys saw exactly 5 movies" (cumulative reading):
    - The outer tower (boys) receives the inner tower's result as its body
    - The inner tower (movies) receives the relation `saw'` as its body
    - Both cardinality tests end up OUTSIDE both maximizations

    This is the derivation that ONLY the tower system can produce;
    the pointwise system from `Basic.lean` is limited to pseudo-cumulative. -/
def cumulativeTower [AssignmentStructure S E] [PartialOrder E] [Fintype E]
    (v u : Dref S E) (boys movies : E → Prop) (saw' : E → E → Prop) : DRS S :=
  (exactlyN_tower v boys 3) (λ fv =>
    (exactlyN_tower u movies 5) (λ fu =>
      fv (fu (sawDRS u v saw'))))

/-- The tower derivation produces exactly the cumulative logical form.

    The higher-order derivation threads the `saw'` relation through both
    maximization operators, placing both cardinality tests OUTSIDE:
    `M_v(E^v boys ; M_u(E^u movies ; saw')) ; 5_u ; 3_v`

    This matches `cumulative` from `Basic.lean` and is what distinguishes
    the cumulative reading from the pseudo-cumulative reading, where at
    least one cardinality test is trapped inside a maximization operator. -/
theorem ho_cumulative_derivation [AssignmentStructure S E] [PartialOrder E] [Fintype E]
    (v u : Dref S E) (boys movies : E → Prop) (saw' : E → E → Prop) :
    cumulativeTower v u boys movies saw' =
    cumulative v u boys movies saw' := by
  rfl

end Semantics.Dynamic.DynamicGQ.HigherOrder
