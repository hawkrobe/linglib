/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Order.Flat
import Linglib.Features.Agreement
import Linglib.Features.Case.Basic

/-!
# The case-bearing capability

`HasCase` equips a carrier with the grammatical case it bears;
`HasCase.Compatible` is the induced case-concord relation, slot compatibility
in the flat information order: symmetric NP-internal agreement in case, not
the asymmetric government/assignment by which case enters an NP
(`Syntax/Case/Dependent.lean`, `Syntax/Case/Licensing.lean`). Case is a
non-canonical agreement feature ([corbett-2006]); [blake-1994]'s treatment of
assignment and concord is the typological anchor. The carrier is
single-valued, so syncretism, case-stacking, and coordinate case resolution
are out of scope.
-/

/-- A carrier of grammatical case. `⊥` = the carrier does not mark case. -/
class HasCase (α : Type*) where
  /-- The case value the carrier bears, if marked. -/
  caseOf : α → Flat Case

export HasCase (caseOf)

instance : HasCase UD.MorphFeatures :=
  ⟨fun mf => mf.case_.map Case.fromUD⟩

instance : HasCase Case := ⟨(↑·)⟩

/-- `Option Case` is the free case-bearer: `some c` bears `c`, `none` is
caseless. -/
instance : HasCase (Option Case) := ⟨id⟩

/-- Case compatibility (concord): valued cases coincide, an unvalued carrier
is a wildcard. -/
abbrev HasCase.Compatible {α β : Type*} [HasCase α] [HasCase β]
    (a : α) (b : β) : Prop :=
  Compat (caseOf a) (caseOf b)

/-- φ-compatibility of UD bundles entails case compatibility. -/
theorem UD.MorphFeatures.compatible_hasCase {f1 f2 : UD.MorphFeatures}
    (h : f1.compatible f2 = true) :
    HasCase.Compatible f1 f2 :=
  Features.compat_of_clause_map Case.fromUD (UD.MorphFeatures.compatible_case h)
