import Linglib.Logic.Team.Atoms
import Linglib.Studies.Haspelmath1997

/-!
# Degano and Aloni (2025): How to be (non-)specific?

This file formalizes the typology of marked indefinites of [degano-aloni-2025]. An indefinite
has three uses, specific known, specific unknown and non-specific, and a marked indefinite is
restricted to some of them: of the seven possible restrictions, six are attested and the one
covering the specific known and the non-specific use without the specific unknown is not. In
two-sorted team semantics a team of assignments to a world variable and an individual variable
is the speaker's information state, and the uses are constancy and variation conditions on the
individual variable, (11): constancy across the team for specific known, constancy within a
world with variation across the team for specific unknown, and variation within a world for
non-specific. Each marked type requires an atom, Table 14, and a type admits a use when the
use's condition entails its requirement. The requirements reproduce the attested profiles,
while the unattested type's requirement, constancy across the team together with variation
within a world, cannot be met, since variation within a world is variation across the team,
so that type admits no use at all. German *irgend-*, Russian *koe-* and *-nibud'* and Kannada
*-oo* instantiate types (iv), (v), (iii) and (vii): the uses are three of the functions of
[haspelmath-1997]'s map, the non-specific use being the irrealis function, and a series covers
the uses whose functions lie in the region the book draws for it.

## References

* [degano-aloni-2025]
* [haspelmath-1997]
-/

namespace DeganoAloni2025

open Team Indefinite
open Haspelmath1997 (Series)

/-! ### Uses and types -/

/-- The three uses of an indefinite, (3). -/
inductive Use where
  | specificKnown
  | specificUnknown
  | nonSpecific
  deriving DecidableEq, Fintype, Repr

/-- The function on Haspelmath's map a use is: the non-specific use is the irrealis
function. -/
def Use.haspelmath : Use → HaspelmathFunction
  | .specificKnown => .specificKnown
  | .specificUnknown => .specificUnknown
  | .nonSpecific => .irrealis

/-- The seven types of Table 14: the restriction a marked indefinite imposes on its uses, the
unmarked indefinite imposing none. -/
inductive DAType where
  | unmarked
  | specific
  | nonSpecific
  | epistemic
  | specificKnown
  | skPlusNS
  | specificUnknown
  deriving DecidableEq, Fintype, Repr

/-- The uses a type is built for, the check marks of Table 14. -/
def DAType.profile : DAType → Finset Use
  | .unmarked => {.specificKnown, .specificUnknown, .nonSpecific}
  | .specific => {.specificKnown, .specificUnknown}
  | .nonSpecific => {.nonSpecific}
  | .epistemic => {.specificUnknown, .nonSpecific}
  | .specificKnown => {.specificKnown}
  | .skPlusNS => {.specificKnown, .nonSpecific}
  | .specificUnknown => {.specificUnknown}

/-- The seven types are the seven non-empty sets of uses. -/
theorem DAType.profile_injective : Function.Injective DAType.profile := by decide

/-! ### Conditions on teams -/

section Teams

variable {V E : Type*} [DecidableEq E] (T : Finset (V → E)) (v x : V)

/-- The rendering (11) of a use on a team, `v` the world variable and `x` the individual:
constancy, constancy within a world with variation across the team, and variation within a
world. -/
def Use.Renders : Use → Prop
  | .specificKnown => Dep T ∅ x
  | .specificUnknown => Dep T {v} x ∧ Var T ∅ x
  | .nonSpecific => Var T {v} x

instance : (u : Use) → Decidable (u.Renders T v x)
  | .specificKnown => inferInstanceAs (Decidable (Dep T ∅ x))
  | .specificUnknown => inferInstanceAs (Decidable (_ ∧ _))
  | .nonSpecific => inferInstanceAs (Decidable (Var T {v} x))

/-- The atom a type requires, Table 14. -/
def DAType.Requires : DAType → Prop
  | .unmarked => True
  | .specific => Dep T {v} x
  | .nonSpecific => Var T {v} x
  | .epistemic => Var T ∅ x
  | .specificKnown => Dep T ∅ x
  | .skPlusNS => Dep T ∅ x ∧ Var T {v} x
  | .specificUnknown => Dep T {v} x ∧ Var T ∅ x

instance : (t : DAType) → Decidable (t.Requires T v x)
  | .unmarked => inferInstanceAs (Decidable True)
  | .specific => inferInstanceAs (Decidable (Dep T {v} x))
  | .nonSpecific => inferInstanceAs (Decidable (Var T {v} x))
  | .epistemic => inferInstanceAs (Decidable (Var T ∅ x))
  | .specificKnown => inferInstanceAs (Decidable (Dep T ∅ x))
  | .skPlusNS => inferInstanceAs (Decidable (_ ∧ _))
  | .specificUnknown => inferInstanceAs (Decidable (_ ∧ _))

omit [DecidableEq E] in
/-- The unattested type's requirement cannot be met: constancy across the team is constancy
within a world, which excludes variation there, footnote 16. -/
theorem not_requires_skPlusNS : ¬ DAType.skPlusNS.Requires T v x :=
  fun ⟨hdep, hvar⟩ ↦ (hdep.mono (Finset.empty_subset _)).not_var hvar

end Teams

/-- A type admits a use when every team on which the use holds meets the type's
requirement. -/
def Admits (t : DAType) (u : Use) : Prop :=
  ∀ {V E : Type} [DecidableEq E] (T : Finset (V → E)) (v x : V), u.Renders T v x → t.Requires T v x

/-- One world with one individual: the specific known use. -/
private def known : Finset (Fin 2 → Fin 2) := {fun _ ↦ 0}

/-- Two worlds, each with its own individual: the specific unknown use. -/
private def unknown : Finset (Fin 2 → Fin 2) := {fun _ ↦ 0, fun _ ↦ 1}

/-- One world with two individuals: the non-specific use. -/
private def open_ : Finset (Fin 2 → Fin 2) := {fun _ ↦ 0, fun k ↦ if k = 0 then 0 else 1}

/-- The requirements reproduce the profiles: an attested type admits exactly the uses Table 14
lists for it. -/
theorem admits_iff {t : DAType} (ht : t ≠ .skPlusNS) (u : Use) :
    Admits t u ↔ u ∈ t.profile := by
  cases t <;> cases u <;> first
    | exact absurd rfl ht
    | exact iff_of_true (fun _ _ _ _ ↦ trivial) (by decide)
    | exact iff_of_true (fun _ _ _ h ↦ h) (by decide)
    | exact iff_of_true (fun _ _ _ h ↦ h.1) (by decide)
    | exact iff_of_true (fun _ _ _ h ↦ h.2) (by decide)
    | exact iff_of_true (fun _ _ _ h ↦ h.mono (Finset.empty_subset _)) (by decide)
    | exact iff_of_true (fun _ _ _ h ↦ h.anti (Finset.empty_subset _)) (by decide)
    | exact iff_of_false (fun h ↦ absurd (h known 0 1 (by decide)) (by decide)) (by decide)
    | exact iff_of_false (fun h ↦ absurd (h unknown 0 1 (by decide)) (by decide)) (by decide)
    | exact iff_of_false (fun h ↦ absurd (h open_ 0 1 (by decide)) (by decide)) (by decide)

/-- The unattested type admits no use, not even the two it is built for. -/
theorem not_admits_skPlusNS (u : Use) : ¬ Admits .skPlusNS u := by
  cases u <;> first
    | exact fun h ↦ not_requires_skPlusNS _ _ _ (h known 0 1 (by decide))
    | exact fun h ↦ not_requires_skPlusNS _ _ _ (h unknown 0 1 (by decide))
    | exact fun h ↦ not_requires_skPlusNS _ _ _ (h open_ 0 1 (by decide))

/-! ### The types on the map -/

/-- The uses a region of the map covers. -/
def uses (s : Finset HaspelmathFunction) : Finset Use := Finset.univ.filter (·.haspelmath ∈ s)

@[simp]
theorem mem_uses {s : Finset HaspelmathFunction} {u : Use} : u ∈ uses s ↔ u.haspelmath ∈ s := by
  simp [uses]

/-- A series instantiates the type whose profile is exactly the uses it covers; by
`DAType.profile_injective` there is at most one. A series covering none of the three uses
instantiates no type. -/
def Instantiates (s : Series) (t : DAType) : Prop := uses s.functions = t.profile

instance (s : Series) (t : DAType) : Decidable (Instantiates s t) :=
  inferInstanceAs (Decidable (uses s.functions = t.profile))

/-- Coverage within a type's profile, as for a series whose paradigm mates take some of its
uses from it. -/
def ConsistentWith (s : Series) (t : DAType) : Prop := uses s.functions ⊆ t.profile

instance (s : Series) (t : DAType) : Decidable (ConsistentWith s t) :=
  inferInstanceAs (Decidable (uses s.functions ⊆ t.profile))

/-- Table 14's examples on the map: German *irgend-* is epistemic, Russian *koe-* specific
known, Russian *-nibud'* non-specific, and Kannada *-oo* specific unknown. -/
theorem examples :
    (∃ s ∈ Haspelmath1997.german,
        s.pronoun = German.Indefinites.irgendEntry ∧ Instantiates s .epistemic) ∧
      (∃ s ∈ Haspelmath1997.russian,
        s.pronoun = Russian.Indefinites.koeEntry ∧ Instantiates s .specificKnown) ∧
      (∃ s ∈ Haspelmath1997.russian,
        s.pronoun = Russian.Indefinites.nibudEntry ∧ Instantiates s .nonSpecific) ∧
      ∃ s ∈ Haspelmath1997.kannada,
        s.pronoun = Kannada.Indefinites.ooEntry ∧ Instantiates s .specificUnknown := by
  decide

end DeganoAloni2025
