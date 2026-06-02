import Linglib.Semantics.Composition.Continuation
import Linglib.Studies.Charlow2021.Basic

/-!
# Higher-Order Dynamic Generalized Quantifiers
[barker-shan-2014] [charlow-2021]

[charlow-2021]'s first solution to cumulative readings: higher-order
dynamic GQs using a "tower" continuation type. A modified numeral like
"exactly 3" denotes a *scope-taking* dynamic meaning — type
`((Update S → Update S) → Update S) → Update S` — rather than a flat `Update S`.

The key insight: the tower structure allows the nuclear scope (VP body) to
be placed INSIDE maximization while the cardinality test escapes OUTSIDE,
producing genuine cumulative readings via LOWER.

The simpler `HODGQ` type `(Update S → Update S) → Update S` (= `Cont (Update S) (Update S)`)
cannot achieve this because its continuation receives an already-maximized
flat Update — the nuclear scope can only be placed outside maximization.

-/

namespace Charlow2021.HigherOrder

open Semantics.Dynamic.Core
open Charlow2021.Basic
open Semantics.Composition.Continuation
open _root_.Mereology

variable {S E : Type*}

-- ════════════════════════════════════════════════════
-- § Flat higher-order GQs (HODGQ)
-- ════════════════════════════════════════════════════

/-- Higher-order dynamic GQ: a continuized Update.
    Type: `(Update S → Update S) → Update S`.
    This is `Cont (Update S) (Update S)`, useful for scope-taking in general
    but insufficient for cumulative readings (see `TowerGQ` below). -/
abbrev HODGQ (S : Type*) := Cont (Update S) (Update S)

/-- Lift a flat Update to higher-order (trivially scope-taking).
    This is Cont.pure specialized to Update. -/
def liftGQ (D : Update S) : HODGQ S := Cont.pure D

/-- Lower a higher-order GQ back to flat Update.
    Applies the identity continuation. -/
def lowerGQ (m : HODGQ S) : Update S := Cont.lower m

-- ════════════════════════════════════════════════════
-- § Tower GQs for cumulative readings
-- ════════════════════════════════════════════════════

/-- Tower-type dynamic GQ ([charlow-2021] §3, equation 24).

    The continuation receives a *scope-taking function* `Update S → Update S`
    rather than a flat Update. This allows the nuclear scope (VP body) to be
    placed INSIDE maximization while the cardinality test escapes outside.

    In Barker & Shan's tower notation, this is `[Update S | Update S → Update S]`,
    the type of an expression that contributes a `Update S → Update S` at the
    local level but produces a `Update S` at the top level. -/
abbrev TowerGQ (S : Type*) := ((Update S → Update S) → Update S) → Update S

/-- "Exactly N" as tower GQ (equation 24):
    `λk. k(λbody. M_v(E^v P; body)); n_v`

    The continuation `k` receives a scope-taker `λbody. M_v(E^v P; body)`,
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
    (v u : Dref S E) (boys movies : E → Prop) (saw' : E → E → Prop) : Update S :=
  (exactlyN_tower v boys 3) (λ fv =>
    (exactlyN_tower u movies 5) (λ fu =>
      fv (fu (sawDRS u v saw'))))

/-- The tower derivation produces exactly the cumulative logical form.

    The higher-order derivation threads the `saw'` relation through both
    maximization operators, placing both cardinality tests OUTSIDE:
    `M_v(E^v boys; M_u(E^u movies; saw')); 5_u; 3_v`

    This matches `cumulative` from `Basic.lean` and is what distinguishes
    the cumulative reading from the pseudo-cumulative reading, where at
    least one cardinality test is trapped inside a maximization operator. -/
theorem ho_cumulative_derivation [AssignmentStructure S E] [PartialOrder E] [Fintype E]
    (v u : Dref S E) (boys movies : E → Prop) (saw' : E → E → Prop) :
    cumulativeTower v u boys movies saw' =
    cumulative v u boys movies saw' := by
  rfl

end Charlow2021.HigherOrder
