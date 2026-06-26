import Linglib.Semantics.Polarity.Item

/-!
# Semantics.Polarity.Israel
[israel-1996] [israel-2001] [israel-2011]

Israel's theoretical predictions on polarity-sensitive items: the
`predictCanonicity` function and `canonicityConsistent` validation
predicate. The Israel scalar enums themselves
(`ScalarValue`/`ScalarDirection`/`Canonicity`/`LikelihoodEffect`)
live in `Typology/PolarityItem.lean` (Fragment-importable substrate);
the *predictions* about how they relate to each other are theoretical
content and live here.

## Provenance

Extracted from `Typology/PolarityItem.lean` after audit consensus
that `predictCanonicity` is Israel's main empirical claim — not
neutral typology — and belongs in `Theories/`. Sibling of
`Semantics/Polarity/Licensing.lean` (the Ladusaw/K&L
monotonicity theory hub).

## Framework commitment

Israel's central empirical claim ([israel-2001]) is that for
emphatic polarity items, canonicality is determined principally by
**likelihood effect** (propositional role): impeding roles
(patient/theme) → canonical items, facilitating roles (agent/stimulus)
→ inverted items. The pecuniary-paradox dissolution
(*a red cent* NPI vs *for peanuts* PPI in the same monetary domain) is
the canonical witness of role-likelihood mapping carrying explanatory
weight that pure-monotonicity accounts (Ladusaw, K&L) lack.

This file enshrines the Israel framework. Alternative scalar accounts
([lahiri-1998] EVEN-based, [chierchia-2006] EXH+D-alternatives,
Krifka 1995 STA) would live as sibling Theories files; the
`Typology/PolarityItem.lean` Israel-shaped data fields would carry
each framework's analysis as an optional projection.

## Cross-framework gap (Israel ↔ Ladusaw)

The cross-file gap with `Semantics/Polarity/Licensing.lean`
remains unclosed by this restructure. The refutation theorem —
showing a context where Israel's role-likelihood mapping and Ladusaw's
monotonicity-licensing diverge in their predictions — is **planned**
for `Studies/Israel2001.lean`. The natural witness
is the pecuniary paradox above. NOTE: `Israel2001.lean §8` currently
formalizes Israel↔Ladusaw *agreement* via a `ScaleDirection` bridge
enum — that's the wrong direction; the refutation work is genuinely
deferred.
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
    - The `_, .fci => .unknown` case reflects an editorial decision that
      the substrate declines to predict canonicity for FCIs; Israel 2001
      mostly bracketed FCIs rather than asserting they have no canonicity.
    - Israel's role-likelihood mapping is most robust for emphatic
      strengtheners (NPIs) and PPIs; attenuators interact differently
      (he allows lexical exceptions). The function applies the impeding/
      facilitating mapping uniformly across `PolarityType` regardless of
      `ScalarDirection`; downstream consumers should consult the
      `scalarDirection` field separately when distinguishing emphatic
      from attenuating items.
    - Israel acknowledges lexical exceptions; `canonicityConsistent` below
      tolerates `.unknown` either side to permit data without forcing the
      prediction. -/
def predictCanonicity (le : LikelihoodEffect) (pt : PolarityType) : Canonicity :=
  match le, pt with
  | _, .fci => .unknown  -- editorial decision; see docstring caveat
  | .impeding, _ => .canonical
  | .facilitating, _ => .inverted
  | .unknown, _ => .unknown

/-- Check if a polarity item's stated canonicity agrees with the prediction.
    Holds if canonicity or likelihood effect is unknown (insufficient data),
    or if the stated canonicity matches the prediction from likelihood effect. -/
abbrev PolarityItemEntry.canonicityConsistent (p : PolarityItemEntry) : Prop :=
  p.canonicity = .unknown ∨
  p.likelihoodEffect = .unknown ∨
  p.canonicity = predictCanonicity p.likelihoodEffect p.polarityType

end Semantics.Polarity
