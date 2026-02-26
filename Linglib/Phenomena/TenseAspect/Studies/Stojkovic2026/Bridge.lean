import Linglib.Phenomena.TenseAspect.Studies.Stojkovic2026.Data
import Linglib.Fragments.Serbian.LParticiple
import Linglib.Fragments.Bulgarian.Evidentials

/-!
# Stojković (2026): Compositional TAME Bridge

Bridge theorems connecting the compositional TAME derivations (from Fragment
files) to the empirical data (from Data.lean). The core result is that
SC and BG share the same Evid head semantics and differ in (1) the T head
semantics (past vs. nonfuture) and (2) which head the L-form realizes
(T in SC vs. Asp in BG).

## Key Theorems

1. `sc_withAux_past`: SC AUX+L composes to UP = past, EP = downstream
2. `sc_bareL_direct`: SC bare L composes to UP = past, EP unconstrained
3. `bg_withAux_past`: BG AUX+L composes to UP = nonfuture, EP unconstrained
4. `bg_bareL_evidential`: BG bare L composes to EP = downstream (evidential)
5. `bg_bareL_ep_matches_nfutL`: BG bare L EP matches existing nfutL fragment
6. `shared_evid_semantics`: SC and BG share Evid head semantics
7. `exponent_difference`: SC and BG differ in L-form realization site

## References

- Stojković, S. (2026). L-participle variation in South Slavic.
- Cumming, S. (2026). Tense and evidence. *L&P* 49:153–175.
-/

namespace Phenomena.TenseAspect.Studies.Stojkovic2026.Bridge

open Minimalism
open Semantics.Tense.Evidential
open Theories.Interfaces.SyntaxSemantics.TAMEComposition
open Fragments.Serbian.LParticiple
open Fragments.Bulgarian.Evidentials

-- ════════════════════════════════════════════════════
-- § 1. SC Composition Theorems
-- ════════════════════════════════════════════════════

/-- SC AUX+L composes to UP = past, EP = downstream.
    Full evidP spine: [V, v, Voice, Asp, T, Evid].
    T contributes past, Evid contributes downstream. -/
theorem sc_withAux_past :
    withAux.compose = ⟨some .downstream, some .past⟩ := by native_decide

/-- SC bare L composes to UP = past, EP unconstrained.
    Cartographic TP spine: [V, v, Voice, Asp, T].
    T contributes past, no Evid head → EP stays none. -/
theorem sc_bareL_direct :
    bareL.compose = ⟨none, some .past⟩ := by native_decide

/-- SC AUX+L TAMEEntry has EP = downstream and UP = past. -/
theorem sc_withAux_ep_up :
    (withAux.compose.toTAMEEntry "SC AUX+L").ep = .downstream ∧
    (withAux.compose.toTAMEEntry "SC AUX+L").up = .past := by native_decide

/-- SC bare L TAMEEntry has EP = unconstrained and UP = past. -/
theorem sc_bareL_ep_up :
    (bareL.compose.toTAMEEntry "SC bare L").ep = .unconstrained ∧
    (bareL.compose.toTAMEEntry "SC bare L").up = .past := by native_decide

-- ════════════════════════════════════════════════════
-- § 2. BG Composition Theorems
-- ════════════════════════════════════════════════════

/-- BG AUX+L composes to UP = nonfuture, EP unconstrained.
    Cartographic TP spine: [V, v, Voice, Asp, T].
    T contributes nonfuture, no Evid head → EP stays none. -/
theorem bg_withAux_past :
    bgWithAux.compose = ⟨none, some .nonfuture⟩ := by native_decide

/-- BG bare L composes to EP = downstream, UP unconstrained.
    Spine [V, v, Voice, Asp, Evid]: Evid contributes downstream,
    no T head → UP stays none. -/
theorem bg_bareL_evidential :
    bgBareL.compose = ⟨some .downstream, none⟩ := by native_decide

/-- BG AUX+L TAMEEntry has EP = unconstrained and UP = nonfuture. -/
theorem bg_withAux_ep_up :
    (bgWithAux.compose.toTAMEEntry "BG AUX+L").ep = .unconstrained ∧
    (bgWithAux.compose.toTAMEEntry "BG AUX+L").up = .nonfuture := by native_decide

/-- BG bare L TAMEEntry has EP = downstream and UP = unconstrained. -/
theorem bg_bareL_ep_up :
    (bgBareL.compose.toTAMEEntry "BG bare L").ep = .downstream ∧
    (bgBareL.compose.toTAMEEntry "BG bare L").up = .unconstrained := by native_decide

-- ════════════════════════════════════════════════════
-- § 3. Bridge to Existing Fragment Data
-- ════════════════════════════════════════════════════

/-- The composed EP for BG bare L matches the existing nfutL entry's EP.
    This bridges the new compositional infrastructure to Cumming (2026)'s
    fragment data: both yield EP = downstream. -/
theorem bg_bareL_ep_matches_nfutL :
    (bgBareL.compose.toTAMEEntry "BG bare L").ep = nfutL.ep := by native_decide

-- ════════════════════════════════════════════════════
-- § 4. Cross-Linguistic Parameter
-- ════════════════════════════════════════════════════

/-- SC and BG share Evid head semantics: both assign EP = downstream to Evid.
    The evidential dimension is universally downstream across South Slavic. -/
theorem shared_evid_semantics :
    scHeadSemantics .Evid = bgHeadSemantics .Evid := by native_decide

/-- SC and BG differ in T head semantics: SC T = past, BG T = nonfuture.
    This reflects the different tense systems of the two languages. -/
theorem t_semantics_differ :
    (scHeadSemantics .T).up = some .past ∧
    (bgHeadSemantics .T).up = some .nonfuture := by native_decide

/-- SC and BG differ in exponent mapping: SC maps L to T, BG maps L to Asp.
    This is the single parameter that accounts for the L-participle's
    different grammatical function across the two languages. -/
theorem exponent_difference :
    scExponents .T = some "L" ∧ bgExponents .T = some "AUX" ∧
    scExponents .Evid = some "AUX" ∧ bgExponents .Asp = some "L" := by native_decide

-- ════════════════════════════════════════════════════
-- § 5. Surface Form Predictions
-- ════════════════════════════════════════════════════

/-- SC AUX+L surfaces as ["L", "AUX"]. -/
theorem sc_withAux_forms :
    withAux.forms = ["L", "AUX"] := by native_decide

/-- SC bare L surfaces as ["L"]. -/
theorem sc_bareL_forms :
    bareL.forms = ["L"] := by native_decide

/-- BG AUX+L surfaces as ["L", "AUX"]. -/
theorem bg_withAux_forms :
    bgWithAux.forms = ["L", "AUX"] := by native_decide

/-- BG bare L surfaces as ["L"]. -/
theorem bg_bareL_forms :
    bgBareL.forms = ["L"] := by native_decide

end Phenomena.TenseAspect.Studies.Stojkovic2026.Bridge
