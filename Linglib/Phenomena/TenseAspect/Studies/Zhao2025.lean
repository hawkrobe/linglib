import Linglib.Features.Aktionsart
import Linglib.Fragments.Mandarin.AspectComparison

/-!
# Cross-Domain Bridge: VendlerClass ↔ Mandarin Particles
@cite{zhao-2025}

Lexical facts about three Mandarin particles' anti-AtomDist requirements
(from `Fragments/Mandarin/AspectComparison.lean`). Composed with
Aktionsart's `dynamicity` projection — which assigns `.stative` to exactly
the `.state` VendlerClass — these yield the licensing pattern of
@cite{zhao-2025}: `le` and `meiyou` are licensed by the dynamic classes
(activity / achievement / accomplishment / semelfactive); `guo` is
licensed by every class including state.

The cross-domain bridge is the composition of two independently-decidable
facts (the lexical requirement here + the dynamicity projection in
Aktionsart), not a single theorem.
-/

namespace Phenomena.TenseAspect.CrossDomainBridge

open Features
open Fragments.Mandarin.AspectComparison
open Core.Time

/-- `le` requires anti-AtomDist (a lexical-entry fact). -/
theorem le_requires_anti_atomDist : le.requiresAntiAtomDist = true := rfl

/-- `meiyou` requires anti-AtomDist (a lexical-entry fact). -/
theorem meiyou_requires_anti_atomDist : meiyou.requiresAntiAtomDist = true := rfl

/-- `guo` imposes no ATOM-DIST restriction; compatible with all
    VendlerClasses including states. -/
theorem guo_compatible_with_all :
    guo.requiresAntiAtomDist = false := rfl

end Phenomena.TenseAspect.CrossDomainBridge
