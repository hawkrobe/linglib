/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Order.Flat
import Linglib.Features.Agreement
import Linglib.Features.Number.Basic

/-!
# The number-bearing capability

`HasNumber` equips a carrier with the grammatical number it bears;
`HasNumber.Compatible` is the induced agreement relation, slot compatibility
in the flat information order. Underspecification is the typologically normal
case ([corbett-2000]): an unmarked carrier (`none`) is a wildcard, not a
default singular.
-/

/-- A carrier of grammatical number. `⊥` = the carrier does not mark
number. -/
class HasNumber (α : Type*) where
  /-- The number value the carrier bears, if marked. -/
  numberOf : α → Flat Number

export HasNumber (numberOf)

/-- A UD bundle bears the number its `number` tag ingests (`Number.fromUD`);
`Inv`/`Coll`/`Count` have no analytical value and leave it unmarked. -/
instance : HasNumber UD.MorphFeatures :=
  ⟨fun f => f.number.bind Number.fromUD⟩

instance : HasNumber Number := ⟨(↑·)⟩

/-- Number compatibility: valued numbers coincide, an unvalued carrier is a
wildcard. -/
abbrev HasNumber.Compatible {α β : Type*} [HasNumber α] [HasNumber β]
    (a : α) (b : β) : Prop :=
  Compat (numberOf a) (numberOf b)

/-- φ-compatibility of UD bundles entails number compatibility. -/
theorem UD.MorphFeatures.compatible_hasNumber {f1 f2 : UD.MorphFeatures}
    (h : f1.compatible f2 = true) :
    HasNumber.Compatible f1 f2 :=
  Features.compat_of_clause Number.fromUD (UD.MorphFeatures.compatible_number h)
