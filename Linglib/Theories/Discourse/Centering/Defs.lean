import Mathlib.Order.Basic
import Mathlib.Order.Nat
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype

/-!
# Centering Theory — Core Definitions
@cite{grosz-joshi-weinstein-1995} @cite{kameyama-1986} @cite{sidner-1979}

Theory-neutral types for Centering Theory: realizations, utterances,
and the typeclass plug-in points that let one set of definitions serve
multiple ranking schemes (grammatical role, thematic role) and multiple
"realizes" semantics (list-based, DRT, situations).

The shape of Centering as a framework:

* An `Utterance E R` carries a list of `Realization E R` — entity, role,
  pronoun-flag triples. The role type `R` is a parameter, instantiated
  by `GrammaticalRole` (@cite{kameyama-1986}) in the `Instances/`
  module. @cite{sidner-1979}'s focus-based account does not fit a
  ranker shape and is formalized as its own architecture in
  `Phenomena/Reference/Studies/Sidner1983.lean`.

* `[CfRankerOf E R]` provides the per-realization rank used to order
  Cf. Higher rank = more prominent. The simpler `[CfRanker R]` (rank
  by role only) is sugar — every `CfRanker R` lifts automatically to
  a `CfRankerOf E R` via the low-priority `cfRankerOf_of_role` default
  instance, projecting through `.role`. Rankers that depend on the
  full realization (linear order @cite{rambow-1993}, info-status
  @cite{strube-hahn-1999}) provide `CfRankerOf` directly.

* `[Realizes U E]` is the plug-in semantics of "u realizes e". The
  `outParam` on `E` lets Lean infer the entity type from the utterance.
  An instance for `Utterance E R` is provided in `Basic.lean`; the
  DRT bridge in `Theories/Interfaces/SemanticsDiscourse/CenteringDRSExpr.lean`
  provides an instance for `DRSExpr`, so Cb computation works on either
  representation.

* `[Pronominalizes U E]` is the analogous plug-in for "u pronominalizes e",
  used by Rule 1.

This is mathlib-style: small typeclass interfaces, instances supplied
where they belong, no premature bundling. Per CLAUDE.md's grounding
discipline, these definitions are imported by the GroszJoshiWeinstein1995
study file rather than re-stipulated there.
-/

set_option autoImplicit false

namespace Discourse.Centering

-- ════════════════════════════════════════════════════
-- § 1. Cf Ranking Plug-In
-- ════════════════════════════════════════════════════

/-- Numeric rank over a role type used to order forward-looking centers.
    Higher rank ⇒ more prominent in Cf. The choice of role type and
    its ranking is a theoretical commitment, supplied by an instance.
    See `Instances/GrammaticalRole.lean` for the
    @cite{kameyama-1986} / @cite{grosz-joshi-weinstein-1995} default
    `SUBJECT > OBJECT > OTHER` ranking standard for English.

    Earlier work (@cite{sidner-1979}, @cite{sidner-1983}) used a
    different focus architecture that does not fit a single ranking
    scheme — see `Phenomena/Reference/Studies/Sidner1983.lean` for
    that formalization. -/
class CfRanker (R : Type) where
  rank : R → Nat

/-- Lift a `CfRanker` instance to a `LinearOrder` whose `<` agrees with
    rank-ascending order on the underlying `Nat`. For a finite enum
    role type with `[DecidableEq R] [Fintype R]`, the injectivity
    obligation is decidable and the default `by decide` discharges it.

    This packages the `LinearOrder.lift'` boilerplate that every
    `CfRanker` instance previously restated. Usage:
    ```
    instance : LinearOrder GrammaticalRole := CfRanker.toLinearOrder _
    ```
    -/
abbrev CfRanker.toLinearOrder (R : Type) [CfRanker R]
    [DecidableEq R] [Fintype R]
    (h : ∀ a b : R, CfRanker.rank a = CfRanker.rank b → a = b := by decide) :
    LinearOrder R :=
  LinearOrder.lift' CfRanker.rank h

-- ════════════════════════════════════════════════════
-- § 2. Realization and Utterance
-- ════════════════════════════════════════════════════

/-- A single noun-phrase realization: which entity it refers to, what
    role it occupies, and whether the surface form is pronominal.

    @cite{grosz-joshi-weinstein-1995} §3 leaves the "role" parameter
    open at the level of theory — different proposals use grammatical
    role, thematic role, or surface position — so we abstract it. -/
structure Realization (E : Type) (R : Type) where
  entity : E
  role : R
  isPronoun : Bool
  deriving Repr, DecidableEq

/-- An utterance, abstractly: a list of NP realizations. The order
    of the list is the surface (textual) order; the Cf order is
    derived by the Cf-ranker, with surface order as the secondary
    sort. See `Basic.lean`.

    **Why a structure wrapper over `List (Realization E R)`?** A nominal
    `structure` (rather than `def Utterance := List ...`) buys us
    three things: (i) typeclass instances can be hung on `Utterance E R`
    without colliding with potential global instances on `List`; (ii)
    additional fields (speaker, time, prosody, segment id) can be added
    in the future without rewriting the API; (iii) `deriving Repr` gives
    a clear pretty-print that distinguishes utterances from raw lists. -/
structure Utterance (E : Type) (R : Type) where
  realizations : List (Realization E R)
  deriving Repr, DecidableEq

-- ════════════════════════════════════════════════════
-- § 3. Generalized Cf Ranking (per-realization)
-- ════════════════════════════════════════════════════

/-- Rank a full `Realization E R`, not just its role.

    `CfRanker R` (§ 1) ranks roles only — sufficient for grammatical
    function (Kameyama 1986: SUBJ > OBJ > OTHER) where rank depends on
    `r.role` alone. But several rankers in the centering literature
    depend on the **full realization**, not just its role:

    * **Linear-order ranking** (@cite{rambow-1993}, motivated by German
      scrambling): rank by surface position within the utterance.
    * **Information-status ranking** (@cite{strube-hahn-1999} for
      German): HEARER-OLD ≺ MEDIATED ≺ HEARER-NEW with linear-order
      tiebreak — needs both info-status (a per-entity property) and
      surface position (a per-realization property).

    `CfRankerOf E R` is the canonical typeclass; `CfRanker R` is sugar
    for "rank depends only on the role" (low-priority default instance
    `cfRankerOf_of_role` lifts every `CfRanker R` to a `CfRankerOf E R`
    by projecting through `.role`). Mathlib analogue: `Module R M` is
    the canonical typeclass; specializations like `Algebra R A` extend
    it. The single canonical typeclass over the more general thing,
    not parallel typeclasses with explicit conversion. -/
class CfRankerOf (E : Type) (R : Type) where
  rank : Realization E R → Nat

/-- Default instance: any `CfRanker R` (rank-by-role-only) lifts to
    a `CfRankerOf E R` (rank-by-realization) by projecting through the
    realization's `role` field. Low priority so explicit per-realization
    instances win. -/
instance (priority := low) cfRankerOf_of_role {E R : Type} [r : CfRanker R] :
    CfRankerOf E R where
  rank rl := r.rank rl.role

-- ════════════════════════════════════════════════════
-- § 4. Realizes / Pronominalizes Plug-Ins
-- ════════════════════════════════════════════════════

/-- "u realizes e": the entity `e` is among the referents contributed
    by `u`. The exact semantics depends on what `u` is: for an
    `Utterance E R`, it is list membership of `e` among the realizations;
    for a `DRSExpr`, it is membership of `e` among the box's discourse
    referents (see the DRT bridge).

    The field is `Bool`-valued (not `Prop`) because the computational
    form is what `cb`'s `List.find?` consumes, and because every
    centering example we care about has decidable realization. The
    `Prop` wrapper `realizes` and the auto-derived `Decidable` instance
    are provided as the user-facing API.

    **Why `outParam` on `E`?** A given utterance representation `U`
    determines its entity type uniquely (an `Utterance E R` realizes
    elements of `E`; a `DRSExpr` realizes `Nat` drefs). Marking `E` as
    `outParam` tells Lean's typeclass search to defer constraint
    propagation to `E` until `U` is known, so that `realizes u e` and
    `cb prev cur` work without explicit type annotations. Without
    `outParam`, every call site would need `@realizes _ E _ u e`. -/
class Realizes (U : Type) (E : outParam Type) where
  /-- Decidable Bool-valued realization predicate. Use the wrapper
      `realizes` (Prop) for proofs. -/
  decide : U → E → Bool

/-- "u realizes e", as a `Prop`. The `Decidable` instance is derived
    from `Realizes.decide` via `Bool` equality. -/
def realizes {U E : Type} [Realizes U E] (u : U) (e : E) : Prop :=
  Realizes.decide u e = true

theorem realizes_iff_decide {U E : Type} [Realizes U E] (u : U) (e : E) :
    realizes u e ↔ Realizes.decide u e = true := Iff.rfl

instance {U E : Type} [Realizes U E] (u : U) (e : E) :
    Decidable (realizes u e) :=
  inferInstanceAs (Decidable (Realizes.decide u e = true))

/-- "u pronominalizes e": some realization of `e` in `u` uses a
    pronominal form. Used by Rule 1. -/
class Pronominalizes (U : Type) (E : outParam Type) where
  /-- Decidable Bool-valued pronominalization predicate. Use the
      wrapper `pronominalizes` (Prop) for proofs. -/
  decide : U → E → Bool

/-- "u pronominalizes e", as a `Prop`. -/
def pronominalizes {U E : Type} [Pronominalizes U E] (u : U) (e : E) : Prop :=
  Pronominalizes.decide u e = true

theorem pronominalizes_iff_decide {U E : Type} [Pronominalizes U E]
    (u : U) (e : E) :
    pronominalizes u e ↔ Pronominalizes.decide u e = true := Iff.rfl

instance {U E : Type} [Pronominalizes U E] (u : U) (e : E) :
    Decidable (pronominalizes u e) :=
  inferInstanceAs (Decidable (Pronominalizes.decide u e = true))

end Discourse.Centering
