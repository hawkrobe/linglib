import Linglib.Discourse.Gameboard.Defs
import Linglib.Discourse.Gameboard.RepriseContent

/-!
# Purver & Ginzburg (2004): Clarifying Noun Phrase Semantics
[purver-ginzburg-2004]

[purver-ginzburg-2004] use **fragment-reprise** clarification data to
constrain admissible NP denotations. The empirical lever is the Reprise
Content Hypothesis (RCH): a fragment reprise question must query the
standard semantic content of the fragment being reprised. Anything a theory
says about NP denotation has to survive this test.

## The empirical contrast

> A: *Jo arrived yesterday.*  B: *Jo?*
> A: *A thief broke in last night.*  B: *A thief?*

Both responses are reprise fragments. The first naturally queries identity
("who is Jo?"); the second cannot — it queries the *property* ("someone you
believe to be a thief?") rather than identity ("which specific thief?"). The
asymmetry tracks the referential / non-referential distinction on the host
NP, not its surface form.

## The argument against generalized-quantifier denotations

Standard generalized-quantifier theory assigns *a thief* the denotation
`λP. ∃x. thief(x) ∧ P(x)` of type `(e → t) → t`. A reprise of this fragment,
if it queried the standard semantic content, would query at this *functional*
type — but no observed reprise ever does. The empirical record only shows
queries at individual or property type.

[purver-ginzburg-2004] resolve this by splitting the sign's contextual
parameters into two fields:

- **dgb-params**: referential entities, anchored against context
- **q-params**: existentially-bound indices, closed at proposition level

Both have the same record-type shape — record entries with `INDEX` and
`RESTR(ICTION)`. The split lives at the sign level: 'Jo' contributes a
dgb-params entry; 'a thief' contributes a q-params entry. Reprises operate
on the q-params record, not on a higher-order GQ denotation. RCH then
*does* hold under this revised account.

## What this file proves

Two theorems about RCH (defined in
`Pragmatics/Dialogue/Gameboard/RepriseContent.lean`):

1. `gq_reprise_type_mismatch`: a predictor that licenses only `.functional`
   queries — the GQ prediction — fails Weak RCH against any reprise event
   whose observed content includes `.individual` or `.property` queries.

2. `qparams_split_satisfies_weakRCH`: the predictor derived from the
   q-params/dgb-params split (`qParamsPredictor`) satisfies Weak RCH by
   construction.

Both theorems take a `RepriseEvent` carrying a host LocProp; the LocProp's
new `qcparams` field (added in `Gameboard/Basic.lean`) is what makes the q-params
record visible at the reprise interface.
-/

namespace PurverGinzburg2004

open Discourse.Gameboard

-- ════════════════════════════════════════════════════
-- § 1. A worked example: 'a thief broke in'
-- ════════════════════════════════════════════════════

/-- Sub-utterance 'a thief'. -/
def aThiefSub : SubUtterance where
  phon := "a thief"
  cat := "NP"
  cont := "thief"

/-- Host LocProp for "A thief broke in last night."
    The non-referential 'a thief' contributes a q-param `[x:IND, restr:thief(x)]`
    via the sign-level architecture in `Grammar.lean`. -/
def aThiefBrokeIn : LocProp String where
  phon := "A thief broke in last night."
  cat := "S"
  cont := "∃x. thief(x) ∧ broke_in(x)"
  qcparams := [{ index := "x", restriction := "thief" }]
  constits := [aThiefSub]

/-- The intended-content reprise of 'a thief' in this host. -/
def aThiefReprise : RepriseEvent String where
  host := aThiefBrokeIn
  sub := aThiefSub
  reading := .intendedContent

-- ════════════════════════════════════════════════════
-- § 2. The GQ predictor and its violation
-- ════════════════════════════════════════════════════

/-- The generalized-quantifier predictor ([purver-ginzburg-2004] target):
licenses only `.functional`-typed queries, since GQ denotations have type
`(e → t) → t`. Stated as a predictor for empirical refutation. -/
def gqPredictor : RchPredictor String :=
  fun _ => [.functional]

/-- The observed reprise content for 'a thief' under intended-content reading
includes an `.individual` query — querying the witness of the existential. -/
theorem aThief_reprise_observes_individual :
    QueryType.individual ∈ reprisedContent aThiefReprise.host
                                            aThiefReprise.sub
                                            aThiefReprise.reading := by
  unfold reprisedContent aThiefReprise aThiefBrokeIn
  simp

/-- The GQ predictor licenses *only* `.functional` queries — no `.individual`. -/
theorem gqPredictor_licenses_only_functional (ev : RepriseEvent String) :
    gqPredictor ev = [.functional] := rfl

/-- `.individual` is not in the GQ predictor's licensed set for any event. -/
theorem individual_not_in_gqPredictor (ev : RepriseEvent String) :
    QueryType.individual ∉ gqPredictor ev := by
  simp [gqPredictor_licenses_only_functional]

/-- **Type-mismatch theorem** ([purver-ginzburg-2004], [ginzburg-2012] §8.5.1):
the GQ predictor fails Weak RCH. Empirically, fragment reprises of indefinite
NPs query at *individual* (and property) type; the GQ denotation predicts
queries only at *functional* type. The two sets are disjoint, so even Weak
RCH (observed ⊆ predicted) fails.

Witness: the 'a thief' / 'A thief?' reprise event constructed above. -/
theorem gq_reprise_type_mismatch :
    ¬ WeakRCH (gqPredictor : RchPredictor String) := by
  intro h
  exact individual_not_in_gqPredictor aThiefReprise
    (h aThiefReprise QueryType.individual aThief_reprise_observes_individual)

-- ════════════════════════════════════════════════════
-- § 3. The q-params/dgb-params split satisfies Weak RCH
-- ════════════════════════════════════════════════════

/-- The constructive alternative satisfies Weak RCH by construction.

[purver-ginzburg-2004]'s revision routes 'a thief'-style indefinites
through the `qcparams` channel on the LocProp. The `qParamsPredictor`
licenses exactly the queries that `reprisedContent` reports — every
observed query is predicted, so Weak RCH holds. (Inherited from
`qParamsPredictor_satisfies_weakRCH` in
`Gameboard/RepriseContent.lean`; restated here for the empirical paper context.) -/
theorem qparams_split_satisfies_weakRCH :
    WeakRCH (qParamsPredictor : RchPredictor String) :=
  qParamsPredictor_satisfies_weakRCH

-- ════════════════════════════════════════════════════
-- § 4. Cross-check on the referential case
-- ════════════════════════════════════════════════════

/-- Sub-utterance 'Jo'. -/
def joSub : SubUtterance where
  phon := "Jo"
  cat := "PROPN"
  cont := "jo"

/-- Host LocProp for "Jo arrived yesterday."
    'Jo' is referential — contributes a `cparams` entry, *not* `qcparams`.
    Its reprise queries identity, not property. -/
def joArrived : LocProp String where
  phon := "Jo arrived yesterday."
  cat := "S"
  cont := "arrived(jo)"
  cparams := [{ index := "jo_ref", restriction := "named(Jo)" }]
  constits := [joSub]

/-- For 'Jo' (referential), the intended-content reprise queries a property
    over the sub-utterance's content — not an individual witness. The
    q-params channel is empty, so the property fallback applies. -/
theorem jo_intendedContent_property_only :
    reprisedContent joArrived joSub .intendedContent = [.property "jo"] := by
  unfold reprisedContent joArrived joSub
  rfl

end PurverGinzburg2004
