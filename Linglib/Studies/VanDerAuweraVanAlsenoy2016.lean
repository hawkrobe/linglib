/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.Negation
import Linglib.Features.NegativeConcord

/-!
# [van-der-auwera-van-alsenoy-2016] — negative concord ↔ n-word status

The cross-linguistic bridge between a language's WALS 115A negative-indefinite
*strategy* ([haspelmath-2013], typed in `Syntax.Negation`) and the item-level
*n-word status* of its negation-sensitive indefinites ([giannakidou-2000], typed
in `Features.NegativeConcord`): an n-word needs a negative-concord system, an
inherently negative quantifier needs a non-concord (double-negation /
neg-existential) one, and an NPI is admitted by either.

Anchored here (rather than left in `Syntax.Negation` substrate) because it is a
paper-specific prediction with no other consumer; keeping it study-local lets
`Syntax.Negation` stay free of the `Features.NegativeConcord` import.

## Main definitions

* `hasNegativeConcord` — whether a WALS 115A strategy is a concord system.
* `admits` — whether an n-word status is consistent with a strategy.
-/

namespace VanDerAuweraVanAlsenoy2016

open Syntax.Negation (NegIndefiniteStrategy)
open Features.NegativeConcord (NWordStatus)

/-- Whether the negative-indefinite system shows negative concord
    ([van-der-auwera-van-alsenoy-2016]): WALS 115A `cooccur` (concord) and `mixed`
    (position-dependent) do; `preclude` (double negation) and `negExistential` do not.
    Broader than `NegationProfile.hasNegConcord`, which tests `cooccur` only. -/
def hasNegativeConcord : NegIndefiniteStrategy → Bool
  | .cooccur | .mixed => true
  | .preclude | .negExistential => false

/-- Whether an item-level n-word status is consistent with a language's WALS 115A
    negative-indefinite strategy: an n-word needs a concord system, an inherently
    negative quantifier a non-concord (double-negation / neg-existential) one, an NPI
    any ([van-der-auwera-van-alsenoy-2016]). -/
def admits : NegIndefiniteStrategy → NWordStatus → Bool
  | strat, .nWord => hasNegativeConcord strat
  | strat, .negQuantifier => !hasNegativeConcord strat
  | _, .npi => true

/-- N-words live in negative-concord systems, inherently negative quantifiers in
    double-negation ones ([van-der-auwera-van-alsenoy-2016]). -/
theorem nWord_vs_negQuantifier :
    admits .cooccur .nWord = true ∧
    admits .preclude .nWord = false ∧
    admits .preclude .negQuantifier = true := by decide

end VanDerAuweraVanAlsenoy2016
