import Linglib.Theories.Syntax.Minimalist.Features

/-!
# Basque Auxiliary Postsyntactic Inventory @cite{arregi-nevins-2012} @cite{middleton-2026}
@cite{halle-marantz-1993} @cite{harbour-2014} @cite{harbour-2016}

The fragment-level data needed to formalize the postsyntactic argument
about Basque auxiliaries in @cite{middleton-2026} §3.1 (extending
@cite{arregi-nevins-2012} §3.1.1, §4.6).

A finite Basque auxiliary linearizes as a sequence of terminal
nodes (each a `FeatureBundle`): an absolutive clitic, a T head, an
ergative clitic, and a complementizer. The two postsyntactic rules
that diagnose the impoverishment-before-metathesis ordering operate
on **whole terminals**, not on features within a single bundle:

* **Rule (16) Participant Dissimilation** — deletes a 1p
  (`[+participant +author]`) absolutive clitic when followed by a
  participant ergative clitic.
* **Rule (13) Ergative Metathesis** — swaps the T head with an
  immediately-following ergative clitic when T is leftmost in the
  auxiliary.

This file provides only the bundle constructors and predicates the
rules need to fire. The rules themselves and the divergence proof
live in `Phenomena/Allomorphy/Studies/Middleton2026.lean`.

## Encoding choices

* Clitics carry a `[CL]` marker via the `.case .erg`/`.case .abs`
  constructor (already in `Minimalist.FeatureVal`); together with
  the `[+participant]`/`[+author]` Harbour features this is enough
  to distinguish the four configurations the rules care about.
* T is marked with `[+tense]`, present in `Minimalist.FeatureVal`.
* The complementizer is dropped from the witness phrase: it is not
  referenced by either rule, and including it would add noise.
-/

namespace Fragments.Basque.Postsyntax

open Minimalist

-- ============================================================================
-- § 1: Terminal Constructors
-- ============================================================================

/-- A 1st-person absolutive clitic: `[CL ABS +participant +author]`.
    The trigger of @cite{middleton-2026} (16) Participant
    Dissimilation. -/
def abs1pAuthor : FeatureBundle :=
  [.valued (.case .abs),
   .valued (.participant true),
   .valued (.author true)]

/-- A 2nd-person ergative clitic: `[CL ERG +participant −author]`.
    The right-context of @cite{middleton-2026} (16) — the participant
    ergative that licenses deletion of `abs1pAuthor`. -/
def erg2s : FeatureBundle :=
  [.valued (.case .erg),
   .valued (.participant true),
   .valued (.author false)]

/-- A T head with `[+tense]`. The leftmost-position trigger and
    swap-source of @cite{middleton-2026} (13) Ergative Metathesis. -/
def tPast : FeatureBundle :=
  [.valued (.tense true)]

-- ============================================================================
-- § 2: Terminal Predicates
-- ============================================================================

/-- Does the bundle bear `[+tense]`? Diagnoses a T head. -/
def isT (fb : FeatureBundle) : Bool :=
  fb.any (λ f => f.featureType.sameType (.tense true))

/-- Does the bundle bear an ergative case marker? Diagnoses an ERG
    clitic. -/
def isErgClitic (fb : FeatureBundle) : Bool :=
  fb.any (λ f => f.featureType.sameType (.case .erg))

/-- Does the bundle bear an absolutive case marker? Diagnoses an ABS
    clitic. -/
def isAbsClitic (fb : FeatureBundle) : Bool :=
  fb.any (λ f => f.featureType.sameType (.case .abs))

/-- Does the bundle bear `[+participant]`? -/
def isParticipant (fb : FeatureBundle) : Bool :=
  hasValuedFeature fb (.participant true) &&
  fb.any (λ f => match f with
    | .valued (.participant true) => true
    | _ => false)

/-- Does the bundle bear `[+author]`? -/
def isAuthor (fb : FeatureBundle) : Bool :=
  fb.any (λ f => match f with
    | .valued (.author true) => true
    | _ => false)

/-- A 1st-person absolutive clitic — `[CL ABS +participant +author]`,
    the deletion target of Participant Dissimilation. -/
def isAbsParticipantAuthor (fb : FeatureBundle) : Bool :=
  isAbsClitic fb && isParticipant fb && isAuthor fb

/-- A participant ergative clitic — `[CL ERG +participant ...]`, the
    right-context that licenses Participant Dissimilation. -/
def isErgParticipant (fb : FeatureBundle) : Bool :=
  isErgClitic fb && isParticipant fb

-- ============================================================================
-- § 3: Predicate Sanity Checks
-- ============================================================================

/-- `abs1pAuthor` is recognised as an absolutive 1p clitic. -/
theorem abs1pAuthor_isAbsParticipantAuthor :
    isAbsParticipantAuthor abs1pAuthor = true := by decide

/-- `erg2s` is recognised as an ergative participant clitic. -/
theorem erg2s_isErgParticipant : isErgParticipant erg2s = true := by decide

/-- `tPast` is recognised as a T head. -/
theorem tPast_isT : isT tPast = true := by decide

/-- T is not an ergative clitic. -/
theorem tPast_not_isErgClitic : isErgClitic tPast = false := by decide

/-- ERG is not a T head. -/
theorem erg2s_not_isT : isT erg2s = false := by decide

end Fragments.Basque.Postsyntax
