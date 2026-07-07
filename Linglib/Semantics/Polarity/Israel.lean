/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Semantics.Polarity.Item

/-!
# Israel's scalar model: canonicity predictions
[israel-1996] [israel-2001] [israel-2011]

Israel's central empirical claim: for emphatic polarity items,
canonical vs inverted is determined by likelihood effect (impeding
roles → canonical, facilitating → inverted), dissolving the pecuniary
paradox (*a red cent* NPI vs *for peanuts* PPI in one monetary domain)
— explanatory weight that per-context monotonicity accounts lack. The
scalar axes live on `Polarity.Item`; this file holds the predictions:
`predictCanonicity` and the `canonicityConsistent` validation
predicate (checked over the English lexicon and `Studies/Israel2001`).
The Israel↔Ladusaw refutation theorem — a context where role-likelihood
and monotonicity licensing diverge — remains deferred to
`Studies/Israel2001.lean`.
-/

namespace Semantics.Polarity

/-- Israel's prediction ([israel-2001]): for emphatic polarity items,
    canonical/inverted is determined principally by likelihood effect
    (propositional role).

    - Impeding roles → canonical items
    - Facilitating roles → inverted items

    Scalar value determines WHERE on the scale an item sits; likelihood
    effect determines WHETHER the item is canonical or inverted.

    **CAVEATS** (the function is a strong reading, not Israel verbatim):
    - The pure-FC case returns `.unknown`: an editorial decision that the
      substrate declines to predict canonicity for FCIs; Israel 2001
      mostly bracketed FCIs rather than asserting they have no canonicity.
    - Israel's role-likelihood mapping is most robust for emphatic
      strengtheners (NPIs) and PPIs; attenuators interact differently
      (he allows lexical exceptions). The function applies the impeding/
      facilitating mapping uniformly across item classes regardless of
      `ScalarDirection`; downstream consumers should consult the
      `scalarDirection` field separately when distinguishing emphatic
      from attenuating items.
    - Israel acknowledges lexical exceptions; `canonicityConsistent` below
      tolerates `.unknown` either side to permit data without forcing the
      prediction. -/
def predictCanonicity (le : LikelihoodEffect) (pureFC : Bool) : Canonicity :=
  if pureFC then .unknown  -- editorial decision; see docstring caveat
  else match le with
  | .impeding => .canonical
  | .facilitating => .inverted
  | .unknown => .unknown

/-- Check if a polarity item's stated canonicity agrees with the prediction.
    Holds if canonicity or likelihood effect is unknown (insufficient data),
    or if the stated canonicity matches the prediction from likelihood effect. -/
abbrev Item.canonicityConsistent (p : Item) : Prop :=
  p.canonicity = .unknown ∨
  p.likelihoodEffect = .unknown ∨
  p.canonicity =
    predictCanonicity p.likelihoodEffect (p.freeChoice && p.licensor.isNone)

end Semantics.Polarity
