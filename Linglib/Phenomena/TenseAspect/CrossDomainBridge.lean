import Linglib.Theories.Semantics.Lexical.Verb.Aspect
import Linglib.Fragments.Mandarin.AspectComparison

/-!
# Cross-Domain Bridge: VendlerClass ↔ Mandarin Particles (Zhao 2026)
@cite{zhao-2026}

Bridges VendlerClass ATOM-DIST predictions (from Theories/) to the
Mandarin cross-domain particle entries (from Fragments/).

The core classification (`predictsAtomDist`, `predictsAtomDist_iff_stative`,
etc.) lives in `Theories/Semantics/Lexical/Verb/Aspect.lean` alongside
the other VendlerClass feature functions. This file connects those
predictions to the Fragment-level particle licensing.

## References

- Zhao, Z. (2026). Cross-Linguistic and Cross-Domain Parallels in the
  Semantics of Degree and Time. MIT dissertation, Ch. 5–6.
-/

namespace Phenomena.TenseAspect.CrossDomainBridge

open Semantics.Lexical.Verb.Aspect
open Fragments.Mandarin.AspectComparison
open Core.Time

/-- le is temporally licensed for a VendlerClass iff the class is dynamic:
    states predict ATOM-DIST_t → le NOT licensed;
    dynamic classes predict ¬ATOM-DIST_t → le licensed.

    Connects `VendlerClass.predictsAtomDist` (Theories/) to
    `CrossDomainParticle.requiresAntiAtomDist` (Fragments/). -/
theorem le_temporal_licensed_iff_dynamic (c : VendlerClass) :
    (c.predictsAtomDist = false) ↔ (le.requiresAntiAtomDist = true ∧ c.dynamicity = .dynamic) := by
  cases c <;> simp [VendlerClass.predictsAtomDist, VendlerClass.dynamicity, le]

/-- meiyou has the same licensing pattern as le. -/
theorem meiyou_temporal_licensed_iff_dynamic (c : VendlerClass) :
    (c.predictsAtomDist = false) ↔ (meiyou.requiresAntiAtomDist = true ∧ c.dynamicity = .dynamic) := by
  cases c <;> simp [VendlerClass.predictsAtomDist, VendlerClass.dynamicity, meiyou]

/-- guo imposes no ATOM-DIST restriction, so it is compatible with all
    VendlerClasses including states. -/
theorem guo_compatible_with_all :
    guo.requiresAntiAtomDist = false := rfl

end Phenomena.TenseAspect.CrossDomainBridge
