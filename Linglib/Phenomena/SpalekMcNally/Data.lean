import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Fragments.Spanish.Predicates
import Linglib.Core.RootDimensions

/-!
# Spalek & McNally (forthcoming): The Anatomy of a Verb

Empirical data and bridge theorems for the contrastive study of English
*tear* and Spanish *rasgar*. These putative translation equivalents share
event structure (both Levin 45.1 Break Verbs, binary-scale result verbs
with causative alternation) but differ in root content — specifically in
patient restrictions, separation geometry, and agent control.

## Key findings

1. **Shared event structure**: Both are simple result verbs with
   causative alternation (§3.1). Binary-scale change: *almost* modification
   entails no change has yet occurred.

2. **Different root content** (§3.2):
   - *rasgar* requires flimsy/insubstantial patients; *tear* is unrestricted
   - *tear* implies contrary-direction separation with force; *rasgar* implies
     linear/gash-like separation
   - *tear* is compatible with careful action; *rasgar* is not

3. **Figurative extensions differ predictably** (§3.3): root content predicts
   which figurative uses each verb supports.

4. **Translation equivalence is partial** (§4.2): in P-ACTRES parallel corpus,
   *tear* translates to many Spanish verbs; *rasgar* predominantly translates
   to *tear* only in specific contexts (Tables 1–2).

## References

- Spalek, A.A. & McNally, L. (forthcoming). The anatomy of a verb: *Tear*,
  *rasgar*, and lexical equivalence. *Linguistics in Contrast*.
-/

namespace Phenomena.SpalekMcNally

open Fragments.English.Predicates.Verbal
open Fragments.Spanish.Predicates

-- ════════════════════════════════════════════════════
-- § 1. Shared Event Structure (§3.1)
-- ════════════════════════════════════════════════════

/-- Both *tear* and *rasgar* are Levin 45.1 Break Verbs. -/
theorem shared_levin_class :
    tear_.levinClass = rasgar.levinClass := rfl

/-- Both use the `make` causative builder (sufficiency semantics). -/
theorem shared_causative_builder :
    tear_.causativeBuilder = rasgar.causativeBuilder := rfl

/-- Both are causative verbs. -/
theorem both_causative :
    tear_.verbClass = .causative ∧
    rasgar.verbClass = .causative := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 2. Different Root Content (§3.2)
-- ════════════════════════════════════════════════════

/-- *tear* accepts robust patients; *rasgar* does not.
    Spalek & McNally ex. (14): "she tore a chunk off her slice of bread" ✓
    vs. "??rasgó un trozo de pan" (§3.2). -/
theorem patient_restriction_differs :
    tear_.rootProfile ≠ rasgar.rootProfile := by
  simp [tear_, rasgar]

/-- *tear* implies bidirectional (contrary-direction) force;
    *rasgar* implies unidirectional (linear/gash-like) force. -/
theorem force_direction_differs :
    tear_.rootProfile.bind (·.forceDir) ≠
    rasgar.rootProfile.bind (·.forceDir) := by
  simp [tear_, rasgar]

/-- *tear* is compatible with controlled action; *rasgar* is not.
    Spalek & McNally ex. (17): "carefully tore the tin foil" ✓
    vs. "??rasgaron con cuidado el papel de aluminio" (§3.2). -/
theorem agent_control_differs :
    tear_.rootProfile.bind (·.agentControl) ≠
    rasgar.rootProfile.bind (·.agentControl) := by
  simp [tear_, rasgar]

-- ════════════════════════════════════════════════════
-- § 3. Root Overlap (Translation Equivalence Zone)
-- ════════════════════════════════════════════════════

/-- The roots of *tear* and *rasgar* overlap: there exists a region of the
    conceptual space (flimsy patients, moderate force, separation result)
    where both verbs are applicable. This overlap zone is where they
    function as translation equivalents (§4.2, Table 1). -/
theorem roots_overlap :
    (tear_.rootProfile.get!).overlaps (rasgar.rootProfile.get!) = true := by
  native_decide

-- ════════════════════════════════════════════════════
-- § 4. Translation Data (§4.2, Tables 1–2)
-- ════════════════════════════════════════════════════

/-- Translation of transitive *tear* in P-ACTRES 2.0 (Table 1).
    66 instances total; *rasgar* accounts for only 8 (12.1%). -/
structure TranslationDatum where
  targetVerb : String
  instances : Nat
  deriving Repr, Inhabited

/-- Table 1: Translation of transitive *tear* into Spanish. -/
def tearToSpanish : List TranslationDatum :=
  [ ⟨"arrancar", 12⟩,    -- "pull out" — most frequent
    ⟨"desgarrar", 8⟩,     -- "rip"
    ⟨"rasgar", 8⟩,        -- "tear (gash)"
    ⟨"romper", 4⟩,        -- "break"
    ⟨"partir", 3⟩,        -- "divide"
    ⟨"quitar", 3⟩ ]       -- "remove"
    -- + 27 other verbs with 1–2 instances each

/-- Table 2: Translation of transitive *rasgar* into English. -/
def rasgarToEnglish : List TranslationDatum :=
  [ ⟨"tear", 4⟩,
    ⟨"rend", 1⟩,
    ⟨"rip", 1⟩ ]

/-- *rasgar* is not the preferred translation of *tear*.
    Only 8 of 66 instances (12.1%). -/
theorem rasgar_not_preferred_for_tear :
    (tearToSpanish.filter (·.targetVerb == "rasgar")).head!.instances <
    (tearToSpanish.filter (·.targetVerb == "arrancar")).head!.instances := by
  native_decide

/-- *tear* IS the preferred translation of *rasgar* (4 of 6 instances). -/
theorem tear_preferred_for_rasgar :
    (rasgarToEnglish.filter (·.targetVerb == "tear")).head!.instances >
    (rasgarToEnglish.filter (·.targetVerb == "rend")).head!.instances := by
  native_decide

end Phenomena.SpalekMcNally
