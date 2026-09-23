module

public import Linglib.Data.WALS.Features.F106A
public import Linglib.Syntax.Reciprocal
public import Linglib.Fragments.English.Reciprocals
public import Linglib.Fragments.German.Reciprocals
public import Linglib.Fragments.Greek.StandardModern.Reciprocals
public import Linglib.Fragments.Romance.French.Reciprocals
public import Linglib.Fragments.Romance.Spanish.Reciprocals
public import Linglib.Fragments.Slavic.Russian.Reciprocals
public import Linglib.Fragments.Swahili.Reciprocals
public import Linglib.Fragments.Wambaya.Reciprocals

/-!
# Maslova and Nedjalkov (2013): Reciprocal Constructions

[maslova-nedjalkov-2013] classify languages by the polysemy of their non-iconic reciprocal
constructions (§2). A reciprocal construction either can also express the reflexive meaning or
cannot, so a language has reflexive reciprocal constructions, non-reflexive ones, both (the mixed
type), or no non-iconic reciprocal construction at all. This file computes that value from a
marker inventory (`ofInventory`) and characterizes each value by the kinds of marker the
inventory contains (`ofInventory_eq_mixed_iff` and its siblings). The chapter's own examples come
out as it states, English with only non-reflexive reciprocals and German of the mixed type
(`ofInventory_english`, `ofInventory_german`, §2.2), and every language of the chapter's sample
whose reciprocal markers a fragment records has the value the chapter codes
(`ofInventory_eq_wals`).

## Implementation notes

A marker's polysemy is its `Reciprocal.Marker.readings`; the value reads only whether each
reciprocal marker also covers the reflexive reading. Mandarin, coded non-reflexive, is left out
of `Language`: its fragment's one marker, the compound *dǎ-lái-dǎ-qù*, repeats its verb, the
iconic encoding the chapter sets aside (§2.1).

## TODO

`ofInventory` reads every marker of an inventory, while the chapter counts only the non-iconic
constructions; `Reciprocal.Strategy` would need to record iconicity for the value to be exact.

## References

* [E. Maslova and V. P. Nedjalkov, *Reciprocal Constructions* (2013)][maslova-nedjalkov-2013]
-/

@[expose] public section

namespace MaslovaNedjalkov2013

open Reciprocal Data.WALS.F106A

/-! ### Reflexive and non-reflexive reciprocals -/

section Kinds

variable (m : Marker)

/-- The marker expresses the reciprocal and also the reflexive meaning: a reflexive reciprocal
construction. -/
def IsReflexiveReciprocal : Prop :=
  Reading.reciprocal ∈ m.readings ∧ Reading.reflexive ∈ m.readings

/-- The marker expresses the reciprocal meaning but not the reflexive one: a non-reflexive
reciprocal construction. -/
def IsNonreflexiveReciprocal : Prop :=
  Reading.reciprocal ∈ m.readings ∧ Reading.reflexive ∉ m.readings

instance : Decidable (IsReflexiveReciprocal m) := instDecidableAnd
instance : Decidable (IsNonreflexiveReciprocal m) := instDecidableAnd

end Kinds

/-- The value of an inventory: reflexive reciprocal markers, non-reflexive ones, both (the mixed
type), or neither. -/
def ofInventory (inv : Finset Marker) : ReciprocalType :=
  if ∃ m ∈ inv, IsReflexiveReciprocal m then
    if ∃ m ∈ inv, IsNonreflexiveReciprocal m then .mixed else .identicalToReflexive
  else if ∃ m ∈ inv, IsNonreflexiveReciprocal m then .distinctFromReflexive
  else .noReciprocalConstruction

variable {inv : Finset Marker}

@[simp]
theorem ofInventory_eq_mixed_iff : ofInventory inv = .mixed ↔
    (∃ m ∈ inv, IsReflexiveReciprocal m) ∧ ∃ m ∈ inv, IsNonreflexiveReciprocal m := by
  unfold ofInventory; split_ifs <;> simp_all

@[simp]
theorem ofInventory_eq_identicalToReflexive_iff : ofInventory inv = .identicalToReflexive ↔
    (∃ m ∈ inv, IsReflexiveReciprocal m) ∧ ∀ m ∈ inv, ¬ IsNonreflexiveReciprocal m := by
  unfold ofInventory; split_ifs <;> simp_all

@[simp]
theorem ofInventory_eq_distinctFromReflexive_iff : ofInventory inv = .distinctFromReflexive ↔
    (∀ m ∈ inv, ¬ IsReflexiveReciprocal m) ∧ ∃ m ∈ inv, IsNonreflexiveReciprocal m := by
  unfold ofInventory; split_ifs <;> simp_all

/-- An inventory has no reciprocal construction when none of its markers is reciprocal. -/
@[simp]
theorem ofInventory_eq_noReciprocalConstruction_iff :
    ofInventory inv = .noReciprocalConstruction ↔ ∀ m ∈ inv, Reading.reciprocal ∉ m.readings := by
  unfold ofInventory IsReflexiveReciprocal IsNonreflexiveReciprocal
  split_ifs <;> grind

/-! ### The chapter's examples (§2.2) -/

/-- English has only non-reflexive reciprocals, *each other* and *one another*. -/
theorem ofInventory_english : ofInventory English.Reciprocals.markers = .distinctFromReflexive := by
  decide

/-- German is of the mixed type: *sich* is also reflexive, *einander* is not. -/
theorem ofInventory_german : ofInventory German.Reciprocals.markers = .mixed := by
  decide

/-! ### The sample -/

/-- The languages of the chapter's sample whose reciprocal markers a fragment records. -/
inductive Language where
  | english | french | german | greek | russian | spanish | swahili | wambaya
  deriving DecidableEq

/-- The ISO 639-3 code under which the chapter's data lists the language. -/
def Language.iso : Language → String
  | .english => "eng" | .french => "fra" | .german => "deu" | .greek => "ell"
  | .russian => "rus" | .spanish => "spa" | .swahili => "swh" | .wambaya => "wmb"

/-- The language's reciprocal markers, from its fragment. -/
def Language.markers : Language → Finset Marker
  | .english => English.Reciprocals.markers
  | .french => French.Reciprocals.markers
  | .german => German.Reciprocals.markers
  | .greek => Greek.StandardModern.Reciprocals.markers
  | .russian => Russian.Reciprocals.markers
  | .spanish => Spanish.Reciprocals.markers
  | .swahili => Swahili.Reciprocals.markers
  | .wambaya => Wambaya.Reciprocals.markers

/-- Each language's inventory has the value the chapter codes for it. -/
theorem ofInventory_eq_wals (l : Language) :
    (lookupISO l.iso).map (·.value) = some (ofInventory l.markers) := by
  cases l <;> decide +kernel

end MaslovaNedjalkov2013
