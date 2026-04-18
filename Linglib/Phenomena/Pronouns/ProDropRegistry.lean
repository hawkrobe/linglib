import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype
import Linglib.Core.WALS.Features.F101A
import Linglib.Phenomena.Control.Studies.Allotey2021
import Linglib.Phenomena.Control.Studies.Ostrove2026

/-!
# Pro-Drop / Overt-PRO Registry @cite{ostrove-2026}

Coverage registry for the languages currently formalized against
@cite{ostrove-2026}'s implicational universal (overt PRO ⇒
non-*pro*-drop). Each language constructor names a profile defined in
a study file; `profile : Language → ProDropProfile` is the unified
endpoint.

The two universal claims — "every formalized language satisfies the
universal" and "the forbidden cell stays empty" — are both `decide`-
closed `∀` theorems over the `Language` enum. Adding a new language
fires both proofs at typecheck. If a future formalization placed a
language into the `overtPROProDrop` cell, `forbidden_cell_empty`
would fail and the universal would be falsified by an explicit
witness rather than a side observation.

This file is the closest thing in linglib to a "cross-linguistic
typological database" for pro-drop / overt-PRO: every entry is
verified against the universal by construction.

## Coverage (as of writing)

| Language | Source                                | Cell                |
|----------|---------------------------------------|---------------------|
| English  | @cite{ostrove-2026}                   | nullPRONoProDrop    |
| SMPM     | @cite{ostrove-2026}                   | overtPRONoProDrop   |
| Büli     | @cite{ostrove-2026} via Sulemana 2021 | overtPRONoProDrop   |
| Gã       | @cite{allotey-2021}                   | overtPRONoProDrop   |

The forbidden cell `overtPROProDrop` has no formalized witness, in
agreement with the universal.

## WALS F101A bridge (@cite{dryer-2013-wals})

`F101A.toAllowsProDrop` derives a partial `allowsProDrop : Option Bool`
from Dryer's "Expression of Pronominal Subjects" classification (711
languages). The mapping is the standard typological reading:

| F101A value                            | `allowsProDrop` |
|----------------------------------------|-----------------|
| obligatoryPronounsInSubjectPosition    | `some false`    |
| subjectAffixesOnVerb                   | `some true`     |
| subjectCliticsOnVariableHost           | `some true`     |
| subjectPronounsInDifferentPosition     | `some true`     |
| optionalPronounsInSubjectPosition      | `some true`     |
| mixed                                  | `none`          |

The classification is **lossy**: WALS does not record overt PRO (so
`hasOvertPRO` cannot be derived from F101A alone), and the
agreement-as-pro-drop reading inflates the *pro*-drop count for
languages whose "subject affixes" are arguably overt pronominal
clitics. Gã is exactly such a case: WALS classifies its subject
proclitic as a "subject affix" (→ *pro*-drop), while @cite{allotey-2021}
treats it as an overt pronominal clitic that fills subject position
(→ non-*pro*-drop and overt PRO). The disagreement is surfaced as a
named theorem (`ga_disagrees_with_F101A`) rather than papered over.
-/

namespace Phenomena.Pronouns.ProDropRegistry

open Core.NullSubject
open Core.WALS.F101A

/-- The languages currently formalized in linglib for the pro-drop /
    overt-PRO universal. Adding a constructor here requires extending
    `profile` and re-fires the two universal theorems by `decide`. -/
inductive Language where
  | english
  | smpm
  | buli
  | ga
  deriving DecidableEq, Repr, Fintype

/-- The unified endpoint: each formalized language's profile, sourced
    from its study file. -/
def profile : Language → ProDropProfile
  | .english => Ostrove2026.englishProfile
  | .smpm    => Ostrove2026.smpmProfile
  | .buli    => Ostrove2026.buliProfile
  | .ga      => Allotey2021.gaProfile

/-- Every language formalized in linglib satisfies @cite{ostrove-2026}'s
    implicational universal. Closed by `cases L <;> decide`:
    case-checks all constructors of `Language`, decides `Satisfies`
    for each profile. Adding a constructor that lands in
    `overtPROProDrop` will break this proof at typecheck. -/
theorem all_satisfy (L : Language) : (profile L).Satisfies := by
  cases L <;> decide

/-- The forbidden cell of @cite{ostrove-2026}'s typology
    (`overtPROProDrop`) has no formalized witness. This is the
    explicit, falsifiable form of the universal: a future language
    formalization that placed its profile in the forbidden cell would
    falsify this theorem. -/
theorem forbidden_cell_empty (L : Language) :
    (profile L).classify ≠ Typology.overtPROProDrop := by
  cases L <;> decide

/-- How many formalized languages fall into a given typological cell. -/
def cellCount (c : Typology) : Nat :=
  (Finset.univ.filter (fun L : Language => (profile L).classify = c)).card

/-- The forbidden cell is empty (cardinality form). -/
theorem cellCount_overtPROProDrop_eq_zero :
    cellCount Typology.overtPROProDrop = 0 := by decide

-- ════════════════════════════════════════════════════════════════
-- § WALS F101A Bridge
-- ════════════════════════════════════════════════════════════════

/-- Derived *pro*-drop classification from a WALS F101A strategy.
    `none` means WALS leaves the question open (the `mixed` cell). -/
def F101A.toAllowsProDrop : ExpressionOfPronominalSubjects → Option Bool
  | .obligatoryPronounsInSubjectPosition => some false
  | .subjectAffixesOnVerb                => some true
  | .subjectCliticsOnVariableHost        => some true
  | .subjectPronounsInDifferentPosition  => some true
  | .optionalPronounsInSubjectPosition   => some true
  | .mixed                               => none

/-- WALS-derived `allowsProDrop` for a language by WALS code. `none`
    if the language is absent from F101A or its value is `mixed`. -/
def F101A.allowsProDropOf (walsCode : String) : Option Bool :=
  (Core.WALS.F101A.allData.find? (·.walsCode == walsCode)) |>.bind
    (F101A.toAllowsProDrop ·.value)

/-- A registry language's WALS code, when one exists. SMPM
    (Chalcatongo Mixtec is the closest WALS proxy but is not the same
    variety) and Büli are absent from F101A. -/
def walsCodeOf : Language → Option String
  | .english => some "eng"
  | .smpm    => none
  | .buli    => none
  | .ga      => some "ga"

-- ════════════════════════════════════════════════════════════════
-- § Coverage Theorems: registry vs F101A
-- ════════════════════════════════════════════════════════════════

/-- English agrees with WALS F101A: obligatory subject pronouns →
    `allowsProDrop = false`, matching the registry profile. -/
theorem english_agrees_with_F101A :
    F101A.allowsProDropOf "eng" = some (profile .english).allowsProDrop := by
  native_decide

/-- **Gã disagreement.** WALS classifies Gã's subject proclitic as a
    "subject affix on verb" (→ pro-drop under the standard reading),
    while @cite{allotey-2021} treats it as an overt pronominal clitic
    that fills subject position (→ non-pro-drop, overt PRO). The
    project deliberately surfaces the disagreement rather than papering
    over it with a fudge in the WALS-bridging direction. -/
theorem ga_disagrees_with_F101A :
    F101A.allowsProDropOf "ga" ≠ some (profile .ga).allowsProDrop := by
  native_decide

/-- The two registry languages with WALS F101A coverage are exactly
    English and Gã (SMPM and Büli are absent). -/
theorem walsCovered_languages :
    Finset.univ.filter (fun L : Language => (walsCodeOf L).isSome) =
      {Language.english, Language.ga} := by
  decide

end Phenomena.Pronouns.ProDropRegistry
