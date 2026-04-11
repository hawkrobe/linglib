import Linglib.Phenomena.Questions.Typology
import Linglib.Phenomena.Questions.Studies.ChanShen2026

/-!
# Mandarin Wh-Question Formation
@cite{chan-shen-2026} @cite{chou-2012}

Mandarin is a wh-in-situ language (WALS 93A: `notInitialInterrogativePhrase`).
Content questions are formed with the wh-phrase remaining in its base-generated
position, interpreted via unselective binding by a Q operator in C.

## ANDL modifier: *到底 daodi*

Mandarin *daodi* ('on earth') is the functional equivalent of English
*the-hell* — both are aggressively non-D-linked (ANDL) modifiers bearing
an unvalued POV feature [*ud*] that must be checked in matrix Spec-CP
(@cite{chou-2012}).

The key cross-linguistic difference (@cite{chan-shen-2026}):
- *The-hell* is **parasitic**: it must adjoin to the wh-phrase and rides
  along with wh-movement. In a wh-in-situ language (or strategy), the
  wh-phrase doesn't move, so *the-hell* is stranded.
- *Daodi* is **independent**: it can undergo covert movement to Spec-CP
  on its own, so it is licensed even when the wh-phrase stays in situ.

This single parameter (`ANDLMovementType`) explains why Mandarin *daodi*
is compatible with wh-in-situ but Singlish *the-hell* is not.
-/

namespace Fragments.Mandarin.Questions

open Phenomena.Questions.Typology (WhInterpMechanism WhMovementStrategy)
open Phenomena.Questions.Studies.ChanShen2026
  (ANDLMovementType theHellFeature andlLicensedInSitu)
open Minimalism (GramFeature)

-- ============================================================================
-- Mandarin wh-interpretation mechanism
-- ============================================================================

/-- Mandarin uses unselective binding for wh-interpretation.
    The Q operator in C binds the wh-variable in situ — no overt or
    covert wh-movement occurs. -/
def whMechanism : WhInterpMechanism := .unselectiveBinding

-- ============================================================================
-- ANDL modifier: 到底 daodi
-- ============================================================================

/-- A lexical entry for an ANDL (aggressively non-D-linked) modifier. -/
structure ANDLEntry where
  /-- Written form. -/
  form : String
  /-- Romanization. -/
  romanization : String
  /-- Gloss. -/
  gloss : String
  /-- Movement type: parasitic on wh-host or independent. -/
  movementType : ANDLMovementType
  /-- Unvalued POV feature [*ud*] — same as English *the-hell*. -/
  povFeature : GramFeature
  deriving Repr, DecidableEq

/-- 到底 *daodi* ('on earth') — Mandarin ANDL modifier.
    Bears the same POV feature [*ud*] as *the-hell* but can undergo
    independent covert movement to matrix Spec-CP (@cite{chou-2012}). -/
def daodi : ANDLEntry :=
  { form := "到底"
  , romanization := "dàodǐ"
  , gloss := "on earth (ANDL)"
  , movementType := .independent
  , povFeature := theHellFeature }

-- ============================================================================
-- Verification theorems
-- ============================================================================

/-- *Daodi* has the same POV feature as *the-hell*. -/
theorem daodi_same_pov_as_theHell :
    daodi.povFeature = theHellFeature := rfl

/-- *Daodi* uses independent movement (not parasitic). -/
theorem daodi_is_independent :
    daodi.movementType = .independent := rfl

/-- *Daodi* is licensed with wh-in-situ — derived from independent movement. -/
theorem daodi_licensed_insitu :
    andlLicensedInSitu daodi.movementType = true := rfl

/-- Mandarin wh-in-situ does not involve movement to Spec-CP. -/
theorem mandarin_wh_no_specCP :
    whMechanism.reachesSpecCP = false := rfl

/-- Mandarin wh-in-situ is island-insensitive (binding, not movement). -/
theorem mandarin_wh_island_free :
    whMechanism.islandSensitive = false := rfl

-- ============================================================================
-- Cross-linguistic contrast: daodi vs the-hell
-- ============================================================================

/-- The single parameter differentiating *daodi* from *the-hell*:
    independent vs parasitic movement. Everything else (POV feature,
    ANDL semantics) is shared. -/
theorem daodi_theHell_minimal_pair :
    daodi.movementType = .independent ∧
    andlLicensedInSitu .independent = true ∧
    andlLicensedInSitu .parasitic = false := ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- Bridge to ShenHuang2026 WhDependencyType
-- ============================================================================

/-- Mandarin wh-in-situ uses binding — same dependency type as Singlish
    wh-in-situ. Both are predicted to be island-insensitive by
    @cite{shen-huang-2026}. -/
theorem mandarin_insitu_is_binding :
    whMechanism.toDependencyType = .binding := rfl

end Fragments.Mandarin.Questions
