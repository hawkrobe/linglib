/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Data.WALS.Features.F98A
import Linglib.Data.WALS.Features.F99A
import Linglib.Data.WALS.Features.F100A

/-!
# WALS alignment distribution facts (Chs 98/99/100)

Theory-neutral frequency facts about morphosyntactic alignment in the WALS
sample: neutral NP alignment is modal, accusative outnumbers ergative, and
tripartite is rare. Pure statistics over the WALS feature data, co-located with
it (relocated from the former `Typology/Alignment.lean` drawer, which had no
business holding them).
-/

namespace Data.WALS

private abbrev ch98  := F98A.allData
private abbrev ch99  := F99A.allData
private abbrev ch100 := F100A.allData

/-- Ch 98: neutral NP alignment is the modal pattern (no case marking). -/
theorem ch98_neutral_modal :
    let neutral := (ch98.filter (·.value == .neutral)).length
    neutral > (ch98.filter (·.value == .ergativeAbsolutive)).length ∧
    neutral > (ch98.filter (·.value == .tripartite)).length ∧
    neutral > (ch98.filter (·.value == .activeInactive)).length := by
  exact ⟨by native_decide, by native_decide, by native_decide⟩

/-- Ch 98: among case-marking systems, accusative outnumbers ergative. -/
theorem ch98_accusative_gt_ergative :
    (ch98.filter (·.value == .nominativeAccusative)).length +
    (ch98.filter (·.value == .nominativeAccusative_3)).length >
    (ch98.filter (·.value == .ergativeAbsolutive)).length := by
  native_decide

/-- Ch 99: accusative outnumbers ergative for pronoun case marking. -/
theorem ch99_accusative_gt_ergative :
    (ch99.filter (·.value == .nominativeAccusative)).length +
    (ch99.filter (·.value == .nominativeAccusative_3)).length >
    (ch99.filter (·.value == .ergativeAbsolutive)).length := by
  native_decide

/-- Ch 100: accusative is the dominant verbal-person-marking pattern. -/
theorem ch100_accusative_dominant :
    (ch100.filter (·.value == .accusative)).length >
    (ch100.filter (·.value == .ergative)).length ∧
    (ch100.filter (·.value == .accusative)).length >
    (ch100.filter (·.value == .active)).length := by
  exact ⟨by native_decide, by native_decide⟩

/-- Ch 98: tripartite NP alignment is extremely rare. -/
theorem ch98_tripartite_rare :
    (ch98.filter (·.value == .tripartite)).length * 30 < ch98.length := by
  native_decide

/-- Ch 99: tripartite pronoun alignment is extremely rare. -/
theorem ch99_tripartite_rare :
    (ch99.filter (·.value == .tripartite)).length * 30 < ch99.length := by
  native_decide

end Data.WALS
