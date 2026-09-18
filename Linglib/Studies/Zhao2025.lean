import Linglib.Semantics.Aspect.Basic
import Linglib.Fragments.Mandarin.AspectComparison

/-!
# Zhao 2025: Cross-Linguistic and Cross-Domain Temporal Expressions

The licensing of the Mandarin particles *le*, *méi-yǒu* and *guò* by lexical aspect, from the
second part of [zhao-2025]. The first part, the ⌈then⌉-present puzzle, is the joint work
published as [tsilia-zhao-2026] and is formalized in `Studies/TsiliaZhao2026.lean`.

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
level. The substrate-side treatment lives in `Core/T/AtomDist.lean`
(`AtomDist τ V`, with `EvQuant.ofPred` bridging from event predicates
to event quantifiers); for the witness-universal subinterval form on
event predicates, see `HasSubintervalProp` in
`Semantics/Aspect/SubintervalProperty.lean`. The
unification: Zhao 2025's particle-licensing condition is the
quantifier-level atomic-granularity stativity test along the time
dimension. Bridging Fragment Bool fields to substrate `Prop`s for
specific Mandarin verbs requires per-verb denotations (theory-hub
denotation discipline; follow-up).

## References

* [zhao-2025]
* [tsilia-zhao-2026]
-/

namespace Zhao2025

open Mandarin.AspectComparison
open Aspect

/-! ### Mandarin particle licensing -/

/-- `le` requires anti-AtomDist (a lexical-entry fact). -/
theorem le_requires_anti_atomDist : le.requiresAntiAtomDist = true := rfl

/-- `meiyou` requires anti-AtomDist (a lexical-entry fact). -/
theorem meiyou_requires_anti_atomDist : meiyou.requiresAntiAtomDist = true := rfl

/-- `guo` imposes no ATOM-DIST restriction; compatible with all
    VendlerClasses including states. -/
theorem guo_compatible_with_all :
    guo.requiresAntiAtomDist = false := rfl

end Zhao2025
