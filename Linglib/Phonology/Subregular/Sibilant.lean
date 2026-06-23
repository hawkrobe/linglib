/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/

/-!
# The sibilant-harmony tier alphabet

The minimal segment alphabet shared by sibilant-harmony phonotactics: an *anterior*
class (`[s, z, ts, …]`), a *posterior* (postalveolar) class (`[ʃ, ʒ, tʃ, …]`), and a
*neutral* class for everything off the harmony tier. `Sibilant.onTier` is the tier-
membership predicate the subregular harmony grammars project on.

Substrate only: a study of a particular system supplies its own forbidden-pair relation
over this alphabet — symmetric (`TSLGrammar.agree`) or asymmetric
(`TSLGrammar.ofForbiddenPairs`) — and keeps its language-specific data and citations.
-/

namespace Subregular

/-- The three sibilant-harmony classes: `anterior` (`s`-class), `posterior` (`ʃ`-class),
and `neutral` (off the harmony tier). -/
inductive Sibilant
  | anterior | posterior | neutral
  deriving DecidableEq, Repr

/-- The harmony-tier predicate: sibilants project, neutral material is transparent. -/
@[reducible] def Sibilant.onTier : Sibilant → Prop
  | .anterior | .posterior => True
  | .neutral => False

instance : DecidablePred Sibilant.onTier
  | .anterior | .posterior => isTrue trivial
  | .neutral => isFalse not_false

end Subregular
