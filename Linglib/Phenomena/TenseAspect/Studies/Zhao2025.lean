import Linglib.Features.Aktionsart
import Linglib.Fragments.Mandarin.AspectComparison

/-!
# Cross-Domain Bridge: VendlerClass ↔ Mandarin Particles
@cite{zhao-2025}

Connects @cite{zhao-2025}'s ATOM-DIST_t prediction — that only states
distribute over temporal atoms, while dynamic VendlerClasses do not — to
the Mandarin cross-domain particle entries in
`Fragments/Mandarin/AspectComparison.lean`. The relevant per-class
witness here is `c.dynamicity = .dynamic` (equivalently, `c ≠ .state`),
which is the consumer-side recovery of the deleted Bool predictor
`predictsAtomDist` formerly in `Features/Aktionsart.lean`.

-/

namespace Phenomena.TenseAspect.CrossDomainBridge

open Features
open Fragments.Mandarin.AspectComparison
open Core.Time

/-- le is temporally licensed for a VendlerClass iff the class is dynamic:
    states predict ATOM-DIST_t → le NOT licensed;
    dynamic classes predict ¬ATOM-DIST_t → le licensed. -/
theorem le_temporal_licensed_iff_dynamic (c : VendlerClass) :
    (c.dynamicity = .dynamic) ↔ (le.requiresAntiAtomDist = true ∧ c.dynamicity = .dynamic) := by
  cases c <;> simp [VendlerClass.dynamicity, le]

/-- meiyou has the same licensing pattern as le. -/
theorem meiyou_temporal_licensed_iff_dynamic (c : VendlerClass) :
    (c.dynamicity = .dynamic) ↔ (meiyou.requiresAntiAtomDist = true ∧ c.dynamicity = .dynamic) := by
  cases c <;> simp [VendlerClass.dynamicity, meiyou]

/-- guo imposes no ATOM-DIST restriction, so it is compatible with all
    VendlerClasses including states. -/
theorem guo_compatible_with_all :
    guo.requiresAntiAtomDist = false := rfl

end Phenomena.TenseAspect.CrossDomainBridge
