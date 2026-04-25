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
  by `GrammaticalRole` (Kameyama 1985) or `ThematicRole` (Sidner 1979)
  in the `Instances/` modules.

* `[CfRanker R]` provides the per-role rank used to order Cf.
  Higher rank = more prominent.

* `[Realizes U E]` is the plug-in semantics of "u realizes e". The
  `outParam` on `E` lets Lean infer the entity type from the utterance.
  An instance for `Utterance E R` is provided in `Basic.lean`; the
  DRT bridge in `Theories/Interfaces/SemanticsDiscourse/CenteringDRT.lean`
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

namespace Discourse.Coherence.Centering

-- ════════════════════════════════════════════════════
-- § 1. Cf Ranking Plug-In
-- ════════════════════════════════════════════════════

/-- Numeric rank over a role type used to order forward-looking centers.
    Higher rank ⇒ more prominent in Cf. The choice of role type and
    its ranking is a theoretical commitment, supplied by an instance.
    See `Instances/GrammaticalRole.lean` (Kameyama 1985, the standard
    English assumption) and `Instances/ThematicRole.lean` (Sidner 1979,
    the original proposal). -/
class CfRanker (R : Type) where
  rank : R → Nat

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
  deriving Repr

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
  deriving Repr

-- ════════════════════════════════════════════════════
-- § 3. Realizes / Pronominalizes Plug-Ins
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

end Discourse.Coherence.Centering
