import Linglib.Fragments.Finnish.Case

/-!
# Finnish Infinitive System @cite{karlsson-2018}

Finnish has **four productive infinitive forms** (Karlsson 2018, Ch. 10),
each built from the verb stem plus a characteristic marker and case suffix:

| Infinitive | Marker | Case forms                               |
|------------|--------|------------------------------------------|
| I (A)      | -a / -ä  | translative only (basic citation form)    |
| II (E)     | -e-    | inessive, instructive                     |
| III (MA)   | -ma-   | inessive, elative, illative, adessive, abessive |
| IV (MINEN) | -minen | nominative (verbal noun)                  |

The **III infinitive** is linguistically remarkable: it takes **local case
suffixes** on verbal stems, mirroring the nominal local case system. Four of
its five case forms correspond exactly to cells in the 3×2 local case matrix
(see `Fragments.Finnish.Case.localCaseMatrix`):

- inessive -massa = static + internal
- elative -masta = source + internal
- illative -maan = goal + internal
- adessive -malla = static + external

The fifth, abessive -matta ('without V-ing'), comes from outside the local
case matrix — abessive is a "marginal" case (Karlsson 2018, Ch. 13).

This structural parallel — the same case paradigm applying to both nouns
and nonfinite verbs — is evidence that Finnish local cases are genuine
morphosyntactic features, not frozen adverbial suffixes.

## References

- Karlsson, F. (2018). *Finnish: A Comprehensive Grammar* (3rd ed.). Ch. 10.
-/

namespace Fragments.Finnish.Infinitives

open Fragments.Finnish.Case (Direction LocationType LocalCase localCaseMatrix)

-- ============================================================================
-- § 1: Infinitive Types
-- ============================================================================

/-- The four Finnish infinitive classes. -/
inductive InfClass where
  | i    -- A-infinitive: -a / -ä (basic infinitive / citation form)
  | ii   -- E-infinitive: -e- + case
  | iii  -- MA-infinitive: -ma- + case (mirrors local cases)
  | iv   -- MINEN-infinitive: -minen (verbal noun)
  deriving DecidableEq, BEq, Repr, Inhabited

/-- A case form available to an infinitive class. -/
structure InfForm where
  infClass : InfClass
  caseName : String
  suffix : String
  gloss : String
  deriving DecidableEq, BEq, Repr, Inhabited

-- ============================================================================
-- § 2: Infinitive Paradigms
-- ============================================================================

/-- I infinitive (A-infinitive): the basic citation form.
    "lukea" = 'to read'. Only appears in translative. -/
def inf1 : List InfForm :=
  [ ⟨.i, "translative", "-a / -ä", "to V"⟩ ]

/-- II infinitive (E-infinitive): -e- + inessive or instructive.
    "lukiessa" = 'while reading', "lukien" = 'by reading'. -/
def inf2 : List InfForm :=
  [ ⟨.ii, "inessive",    "-e-ssA",  "while V-ing"⟩
  , ⟨.ii, "instructive",  "-e-n",    "by V-ing"⟩ ]

/-- III infinitive (MA-infinitive): -ma- + local case suffixes.
    The paradigm that mirrors the nominal local case matrix.
    "lukemassa" = 'reading' (at it), "lukemasta" = 'from reading',
    "lukemaan" = 'to read' (goal), "lukemalla" = 'by reading',
    "lukematta" = 'without reading'. -/
def inf3 : List InfForm :=
  [ ⟨.iii, "inessive",  "-ma-ssA",  "V-ing (at it)"⟩
  , ⟨.iii, "elative",   "-ma-stA",  "from V-ing"⟩
  , ⟨.iii, "illative",  "-ma-Vn",   "to V (goal)"⟩
  , ⟨.iii, "adessive",  "-ma-llA",  "by V-ing"⟩
  , ⟨.iii, "abessive",  "-ma-ttA",  "without V-ing"⟩ ]

/-- IV infinitive (MINEN-infinitive): verbal noun, nominative only.
    "lukeminen" = 'reading' (the act of). -/
def inf4 : List InfForm :=
  [ ⟨.iv, "nominative", "-minen", "the act of V-ing"⟩ ]

/-- All infinitive forms across all classes. -/
def allInfForms : List InfForm := inf1 ++ inf2 ++ inf3 ++ inf4

/-- Total number of infinitive forms. -/
theorem allInfForms_count : allInfForms.length = 9 := by native_decide

/-- The III infinitive has the richest paradigm (5 forms). -/
theorem inf3_richest : inf3.length = 5 := by native_decide

-- ============================================================================
-- § 3: III Infinitive ↔ Local Case Matrix
-- ============================================================================

/-- A III-infinitive case form paired with the local case matrix cell it
    mirrors. `none` for abessive (outside the local matrix). -/
structure Inf3LocalMapping where
  infForm : InfForm
  localCell : Option LocalCase
  deriving Repr, Inhabited

/-- The mapping from III infinitive forms to local case matrix cells.
    Four of five forms correspond to matrix cells; abessive does not. -/
def inf3LocalMappings : List Inf3LocalMapping :=
  [ ⟨inf3[0]!, some (localCaseMatrix .static .internal)⟩   -- inessive
  , ⟨inf3[1]!, some (localCaseMatrix .source .internal)⟩   -- elative
  , ⟨inf3[2]!, some (localCaseMatrix .goal   .internal)⟩   -- illative
  , ⟨inf3[3]!, some (localCaseMatrix .static .external)⟩   -- adessive
  , ⟨inf3[4]!, none⟩ ]                                      -- abessive (marginal)

/-- Exactly 4 of 5 III-infinitive forms map to local case matrix cells. -/
theorem inf3_local_overlap :
    (inf3LocalMappings.filter (·.localCell.isSome)).length = 4 := by native_decide

/-- The one unmapped form is abessive. -/
theorem inf3_unmapped_is_abessive :
    (inf3LocalMappings.filter (·.localCell.isNone)).length = 1 ∧
    (inf3LocalMappings.filter (·.localCell.isNone))[0]!.infForm.caseName = "abessive" := by
  native_decide

/-- The III infinitive's inessive matches the nominal inessive
    (static + internal cell of the matrix). -/
theorem inf3_inessive_matches_nominal :
    (localCaseMatrix .static .internal).name = "inessive" ∧
    inf3[0]!.caseName = "inessive" := by native_decide

/-- The III infinitive's elative matches the nominal elative
    (source + internal cell of the matrix). -/
theorem inf3_elative_matches_nominal :
    (localCaseMatrix .source .internal).name = "elative" ∧
    inf3[1]!.caseName = "elative" := by native_decide

/-- The III infinitive's illative matches the nominal illative
    (goal + internal cell of the matrix). -/
theorem inf3_illative_matches_nominal :
    (localCaseMatrix .goal .internal).name = "illative" ∧
    inf3[2]!.caseName = "illative" := by native_decide

/-- The III infinitive's adessive matches the nominal adessive
    (static + external cell of the matrix). -/
theorem inf3_adessive_matches_nominal :
    (localCaseMatrix .static .external).name = "adessive" ∧
    inf3[3]!.caseName = "adessive" := by native_decide

/-- The 4 mapped III-infinitive forms cover 3 of the 6 local case matrix cells
    (the 3 internal cases + adessive), leaving ablative and allative unused.

    This asymmetry — all internal cases but only one external case — reflects
    that the III infinitive is primarily about containment ("in the process of"),
    departure ("from the process"), and goal ("into doing"), with adessive
    ("by means of") as the sole external form. -/
theorem inf3_covers_internal_column :
    let mapped := inf3LocalMappings.filterMap (·.localCell)
    mapped.all (fun lc =>
      lc.locationType == .internal ||
      (lc.direction == .static && lc.locationType == .external)) = true := by
  native_decide

end Fragments.Finnish.Infinitives
