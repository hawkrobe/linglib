/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Semantics.Polarity.Item

/-!
# The scalar model of polarity items
[israel-1996] [israel-2001] [israel-2011]

The scalar-model classification of polarity items and its canonicity
prediction. `ScalarItem` extends `Polarity.Item` with the [israel-2001]
axes — scalar value, canonicity, and the propositional role's likelihood
effect — and is built only for items that have the classification, so no
axis carries an "unknown" case. The central empirical claim: for
emphatic polarity items, canonical vs inverted is determined by
likelihood effect (impeding roles → canonical, facilitating → inverted),
dissolving the pecuniary paradox (*a red cent* NPI vs *for peanuts* PPI
in one monetary domain) — explanatory weight that per-context
monotonicity accounts lack. The Israel↔Ladusaw refutation theorem — a
context where role-likelihood and monotonicity licensing diverge —
remains deferred to `Studies/Israel2001.lean`.

## Main declarations

* `ScalarValue`, `Canonicity`, `LikelihoodEffect` — the scalar-model
  axes.
* `ScalarItem` — a polarity item with its scalar-model classification.
* `predictCanonicity`, `ScalarItem.canonicityConsistent` — the
  role-likelihood prediction and its validation predicate (checked over
  the English lexicon and `Studies/Israel2001.lean`).
-/

namespace Polarity

/-! ### The scalar-model axes -/

/-- Where the item sits on its scale relative to the norm: emphatic NPIs
    typically denote low values (*a wink*), emphatic PPIs high ones
    (*tons*); inverted items reverse the pattern ([israel-2001]). -/
inductive ScalarValue where
  | high
  | low
  deriving DecidableEq, Repr

/-- Whether scalar value tracks polarity in the default way (canonical
    emphatic NPIs low, PPIs high) or inversely (*wild horses*, *at the
    drop of a hat*); inversion tracks propositional role
    ([israel-2001]). -/
inductive Canonicity where
  | canonical
  | inverted
  deriving DecidableEq, Repr

/-- How increasing the referent's scalar value affects event likelihood:
    facilitating roles (agent, stimulus, reward) invert the scale,
    impeding roles (patient, increment, expense) keep it canonical —
    [israel-2001]'s resolution of the maximizer/minimizer puzzle. -/
inductive LikelihoodEffect where
  | facilitating
  | impeding
  deriving DecidableEq, Repr

/-! ### The classified item -/

/-- A polarity item together with its [israel-2001] scalar-model
    classification. Built only for items the literature classifies;
    unclassified items stay plain `Item`s. The likelihood effect is the
    propositional-role *explanans* of the canonicity — present exactly
    where the literature gives the role analysis. -/
structure ScalarItem extends Item where
  /-- Scalar value relative to the norm. -/
  scalarValue : ScalarValue
  /-- Canonical or inverted value–polarity linkage. -/
  canonicity : Canonicity
  /-- The propositional role's likelihood effect; `none` = no role
      analysis in the literature. -/
  likelihoodEffect : Option LikelihoodEffect := none
  deriving Repr

/-! ### The canonicity prediction -/

/-- Israel's prediction ([israel-2001]): for emphatic polarity items,
    canonical vs inverted is determined principally by likelihood effect —
    impeding roles → canonical, facilitating → inverted. Scalar value
    determines WHERE on the scale an item sits; likelihood effect
    determines WHETHER the item is canonical or inverted.

    The pure-FC case returns `none`: an editorial decision that the
    substrate declines to predict canonicity for FCIs; Israel 2001 mostly
    bracketed FCIs rather than asserting they have no canonicity. The
    mapping is applied uniformly across item classes although it is most
    robust for emphatic strengtheners and PPIs; attenuators interact
    differently and Israel allows lexical exceptions — consumers should
    consult `scalarDirection` separately when distinguishing emphatic
    from attenuating items. -/
def predictCanonicity (le : LikelihoodEffect) (pureFC : Bool) :
    Option Canonicity :=
  if pureFC then none
  else match le with
    | .impeding => some .canonical
    | .facilitating => some .inverted

/-- A classified item's stated canonicity agrees with the role-likelihood
    prediction, wherever a role analysis exists (vacuously for items
    without one and for pure FCIs, where the substrate declines to
    predict). -/
abbrev ScalarItem.canonicityConsistent (p : ScalarItem) : Prop :=
  ∀ le ∈ p.likelihoodEffect,
    ∀ c ∈ predictCanonicity le (p.freeChoice && p.licensor.isNone),
      p.canonicity = c

end Polarity
