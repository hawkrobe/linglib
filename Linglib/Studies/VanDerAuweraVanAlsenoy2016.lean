/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.Negation
import Linglib.Data.WALS.Features.F115A

/-!
# [van-der-auwera-van-alsenoy-2016] — negative concord ↔ n-word status

The cross-linguistic bridge between a language's WALS 115A negative-indefinite
*strategy* ([haspelmath-2013], typed in `Syntax.Negation`) and the item-level
*n-word status* of its negation-sensitive indefinites ([giannakidou-2000], `NWordStatus`
below): an n-word needs a negative-concord system, an
inherently negative quantifier needs a non-concord (double-negation /
neg-existential) one, and an NPI is admitted by either.

Anchored here (rather than left in `Syntax.Negation` substrate) because it is a
paper-specific prediction with no other consumer, and the n-word and concord types are the
paper's own typology.

## Main definitions

* `NWordStatus`, `NegConcordSubtype`, `NWordPosition` — the n-word trichotomy and the concord
  subtypes, with `NegConcordSubtype.nmRequired` deriving the strict/non-strict contrast.
* `hasNegativeConcord` — whether a WALS 115A strategy is a concord system.
* `admits` — whether an n-word status is consistent with a strategy.
-/

namespace VanDerAuweraVanAlsenoy2016

open Data.WALS
/-- Item-level status of a negation-sensitive indefinite: the n-word vs
    negative-quantifier vs NPI trichotomy. [giannakidou-2000] gives the minimal,
    deliberately theory-neutral definition — n-words "occur in NC structures and can be
    associated with negative meaning" — and stresses their heterogeneity. The *internal*
    semantics is contested; this enum records only the distributional class, which
    [van-der-auwera-van-alsenoy-2016] take as the basis of the NC typology. -/
inductive NWordStatus where
  /-- N-word: occurs in negative-concord structures (Romance *nessuno*, Slavic никто,
      Greek *típota*, Hungarian *semmi*); licenses a negative fragment answer yet typically
      co-occurs with a clausal negation marker. -/
  | nWord
  /-- Inherently negative quantifier: negates on its own with no concord; two stack to
      double negation. English *nobody*, German *niemand*. -/
  | negQuantifier
  /-- Negative-polarity item: non-negative, licensed by negation, occurs across a wider
      range of contexts. English *anybody*. -/
  | npi
  deriving DecidableEq, Repr

/-- Subtype of negative concord ([van-der-auwera-van-alsenoy-2016]; [giannakidou-2000]).
    `strict` keeps the clausal negation marker regardless of n-word position (Greek,
    Hungarian, Slavic); `nonStrict` drops it when the n-word is preverbal but requires it
    postverbally (Italian, Spanish, Portuguese); `negativeSpread` has several n-words share
    one negation with no clausal marker at all. -/
inductive NegConcordSubtype where
  | strict
  | nonStrict
  | negativeSpread
  deriving DecidableEq, Repr

/-- Position of an n-word relative to the finite verb, the parameter the strict versus
    non-strict contrast turns on. -/
inductive NWordPosition where
  | preverbal
  | postverbal
  deriving DecidableEq, Repr

/-- Whether a clausal negation marker is required, given the concord subtype and the
    n-word's position: strict concord keeps the marker regardless of position, non-strict
    drops it for a preverbal n-word but requires it postverbally, and negative spread has no
    clausal marker. -/
def NegConcordSubtype.nmRequired : NegConcordSubtype → NWordPosition → Bool
  | .strict, _ => true
  | .nonStrict, .preverbal => false
  | .nonStrict, .postverbal => true
  | .negativeSpread, _ => false

/-- The strict versus non-strict contrast: both require the marker postverbally, but only
    strict requires it preverbally ([giannakidou-2000]). -/
theorem strict_nonstrict_contrast :
    NegConcordSubtype.strict.nmRequired .preverbal = true ∧
    NegConcordSubtype.nonStrict.nmRequired .preverbal = false ∧
    NegConcordSubtype.nonStrict.nmRequired .postverbal = true := by decide

/-- Whether the negative-indefinite system shows negative concord
    ([van-der-auwera-van-alsenoy-2016]): WALS Ch 115A's predicate-negation-also-present (concord)
    and mixed-behaviour (position-dependent) do; no-predicate-negation (double
    negation) and the negative-existential construction do not. -/
def hasNegativeConcord : F115A.NegativeIndefiniteType → Bool
  | .predicateNegationAlsoPresent | .mixedBehaviour => true
  | .noPredicateNegation | .negativeExistentialConstruction => false

/-- Whether an item-level n-word status is consistent with a language's WALS 115A
    negative-indefinite strategy: an n-word needs a concord system, an inherently
    negative quantifier a non-concord (double-negation / neg-existential) one, an NPI
    any ([van-der-auwera-van-alsenoy-2016]). -/
def admits : F115A.NegativeIndefiniteType → NWordStatus → Bool
  | strat, .nWord => hasNegativeConcord strat
  | strat, .negQuantifier => !hasNegativeConcord strat
  | _, .npi => true

/-- N-words live in negative-concord systems, inherently negative quantifiers in
    double-negation ones ([van-der-auwera-van-alsenoy-2016]). -/
theorem nWord_vs_negQuantifier :
    admits .predicateNegationAlsoPresent .nWord = true ∧
    admits .noPredicateNegation .nWord = false ∧
    admits .noPredicateNegation .negQuantifier = true := by decide

end VanDerAuweraVanAlsenoy2016
