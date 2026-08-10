import Linglib.Features.Aktionsart
import Linglib.Fragments.Mandarin.AspectComparison
import Linglib.Semantics.Tense.Perspective
import Linglib.Fragments.English.TemporalDeictic
import Linglib.Fragments.Japanese.TemporalDeictic
import Linglib.Fragments.Greek.StandardModern.TemporalDeictic
import Linglib.Fragments.Slavic.Russian.TemporalDeictic
import Linglib.Fragments.Hebrew.TemporalDeictic

/-!
# Zhao 2025: Cross-Linguistic and Cross-Domain Temporal Expressions

Two results from [zhao-2025]: the VendlerClass ↔ Mandarin-particle licensing
bridge, and the ⌈then⌉-present puzzle.

## Mandarin particle licensing

Lexical facts about three Mandarin particles' anti-AtomDist
requirements (from `Fragments/Mandarin/AspectComparison.lean`).
Composed with Aktionsart's `dynamicity` projection — which assigns
`.stative` to exactly the `.state` VendlerClass — these yield the
licensing pattern of [zhao-2025]: `le` and `meiyou` are
licensed by the dynamic classes (activity / achievement /
accomplishment / semelfactive); `guo` is licensed by every class
including state.

The cross-domain bridge is the composition of two
independently-decidable facts (the lexical requirement here + the
dynamicity projection in Aktionsart), not a single theorem.

`le.requiresAntiAtomDist = true` is the Fragment-level encoding of
[zhao-2025] Def. 5.36 (p. 165) ATOM-DIST_t at the verb-quantifier
level. The substrate-side treatment lives in `Core/Time/AtomDist.lean`
(`AtomDist τ V`, with `EvQuant.ofPred` bridging from event predicates
to event quantifiers); for the witness-universal subinterval form on
event predicates, see `HasSubintervalProp` in
`Semantics/Aspect/SubintervalProperty.lean`. The
unification: Zhao 2025's particle-licensing condition is the
quantifier-level atomic-granularity stativity test along the time
dimension. Bridging Fragment Bool fields to substrate `Prop`s for
specific Mandarin verbs requires per-verb denotations (theory-hub
denotation discipline; follow-up).

## The ⌈then⌉-present puzzle

Temporal ⌈then⌉ is cross-linguistically incompatible with the present tense:
⌈then⌉ presupposes a reference disjoint from the temporal perspective π
(`Tense.Perspective.thenPresup`), PRES presupposes overlap with π
(`ReichenbachFrame.isPresent` in the point approximation), and the temporal
assertion ("during then") forces the PRES reference inside the ⌈then⌉
reference — so no reference satisfies both (`then_present_root_clash`).
Deleted (SOT) tense escapes: it contributes no perspectival presupposition,
and ⌈then⌉'s own presupposition is satisfiable on any nontrivial timeline
(`Tense.Perspective.thenPresup_satisfiable`).

The attested ⌈then⌉ adverbs (`thenAdverbs`, from the Fragment lexicons):
English *then*, Japanese 当時 *tōji*, Greek τότε *tóte*, Russian тогда
*togda*, Hebrew אז *az* — root-clause ⌈then⌉ + PRES is ungrammatical in
each. (English ⌈then⌉ with an embedded present under future is variably
acceptable, an exception the paper leaves open.)
-/

namespace Zhao2025

open Features
open Mandarin.AspectComparison
open Semantics.Aspect

/-! ### Mandarin particle licensing -/

/-- `le` requires anti-AtomDist (a lexical-entry fact). -/
theorem le_requires_anti_atomDist : le.requiresAntiAtomDist = true := rfl

/-- `meiyou` requires anti-AtomDist (a lexical-entry fact). -/
theorem meiyou_requires_anti_atomDist : meiyou.requiresAntiAtomDist = true := rfl

/-- `guo` imposes no ATOM-DIST restriction; compatible with all
    VendlerClasses including states. -/
theorem guo_compatible_with_all :
    guo.requiresAntiAtomDist = false := rfl

/-! ### The ⌈then⌉-present puzzle -/

open Time Tense.Perspective

/-- The ⌈then⌉ adverbs of [zhao-2025]'s language sample, from the Fragment
    lexicons. -/
def thenAdverbs : List ThenAdverb :=
  [ English.TemporalDeictic.then_
  , Japanese.TemporalDeictic.tooji
  , Greek.StandardModern.TemporalDeictic.tote
  , Russian.TemporalDeictic.togda
  , Hebrew.TemporalDeictic.az ]

/-- Root clause ("Mary is feeling sick (*then)"): π = S, so a present-tensed
    clause admits no ⌈then⌉ restriction — no reference satisfies both the
    "during then" containment and ⌈then⌉'s disjointness from π. -/
theorem then_present_root_clash {Time : Type*} (f : ReichenbachFrame Time)
    (hSimple : f.isSimpleCase) (hPres : f.isPresent) :
    ¬∃ thenRef, f.referenceTime = thenRef ∧ thenPresup thenRef f.speechTime :=
  λ ⟨_, hDuring, hThen⟩ =>
    then_present_clash f hPres hDuring (λ hEq => hThen (hEq.trans hSimple))

end Zhao2025
