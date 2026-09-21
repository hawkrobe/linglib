import Linglib.Logic.Team.Atoms
import Linglib.Studies.Haspelmath1997
import Mathlib.Basic.Nontrivial.Defs
import Mathlib.Order.Interval.Set.OrdConnected

/-!
# Degano and Aloni (2025): How to be (non-)specific?

This file formalizes the typology of marked indefinites of [degano-aloni-2025]. An indefinite
has three uses, specific known, specific unknown and non-specific, and a marked indefinite is
restricted to some of them: of the seven possible restrictions, six are attested and the one
covering the specific known and the non-specific use without the specific unknown is not. In
two-sorted team semantics a team of assignments to a world variable and an individual variable
is the speaker's information state, and the uses are constancy and variation conditions on the
individual variable: constancy across the team for specific known, constancy within a world
with variation across the team for specific unknown, and variation within a world for
non-specific. The three conditions partition the teams.

Each type requires a combination of atoms, and a team meets the requirement exactly when it
renders one of the uses the type is built for, so a type admits the uses of its profile and no
others. Five attested types require a single atom and the specific unknown type a conjunction of
two. The unattested type requires constancy across the team or variation within a world, two
atoms that exclude each other, and that disjunction is the one requirement that is not convex:
a team between two teams meeting it need not meet it. The single atoms are closed under
subteams or under superteams and their conjunction is an intersection of the two kinds, so the
attested requirements are all convex.

German *irgend-*, Russian *koe-* and *-nibud'*, Kannada *-oo*, Italian *qualche-* and Georgian
*-γac* instantiate the six attested types: the uses are three of the functions of
[haspelmath-1997]'s map, the non-specific use being the irrealis function, and a series covers
the uses whose functions lie in the region the book draws for it.

## Main results

* `Use.exists_renders`, `Use.renders_unique`: the three uses partition the teams.
* `IndefiniteType.requires_iff`: a requirement is the disjunction of the uses of the profile.
* `forall_renders_imp_requires_iff`: a use entails a requirement exactly when the profile
  lists it.
* `IndefiniteType.ordConnected_requires`, `IndefiniteType.not_ordConnected_skPlusNS`: the
  attested requirements are convex and the unattested one is not.

## TODO

The paper extends the system with negation and modality to derive the licensing of non-specific
indefinites and treats epistemic indefinites at length; neither is formalized here.

## References

* [degano-aloni-2025]
* [haspelmath-1997]
-/

namespace DeganoAloni2025

open Team Indefinite
open Haspelmath1997 (Series)

/-! ### Uses and types -/

/-- The three uses of an indefinite. -/
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

/-- The seven types of indefinite: the restriction a marked indefinite imposes on its uses, the
unmarked indefinite imposing none. -/
inductive IndefiniteType where
  | unmarked
  | specific
  | nonSpecific
  | epistemic
  | specificKnown
  | skPlusNS
  | specificUnknown
  deriving DecidableEq, Fintype, Repr

namespace IndefiniteType

/-- The uses a type is built for, the check marks of the table of marked indefinites. -/
def profile : IndefiniteType → Finset Use
  | .unmarked => {.specificKnown, .specificUnknown, .nonSpecific}
  | .specific => {.specificKnown, .specificUnknown}
  | .nonSpecific => {.nonSpecific}
  | .epistemic => {.specificUnknown, .nonSpecific}
  | .specificKnown => {.specificKnown}
  | .skPlusNS => {.specificKnown, .nonSpecific}
  | .specificUnknown => {.specificUnknown}

theorem profile_injective : Function.Injective profile := by decide

/-- The seven types are the seven non-empty sets of uses. -/
theorem exists_profile_eq {s : Finset Use} (hs : s.Nonempty) : ∃ t, profile t = s := by
  revert s; decide

end IndefiniteType

/-! ### Conditions on teams -/

section Teams

variable {V E : Type*} {T : Finset (V → E)} {v x : V} {u u' : Use} {t : IndefiniteType}

/-- The rendering of a use on a team, `v` the world variable and `x` the individual:
constancy, constancy within a world with variation across the team, and variation within a
world. -/
def Use.Renders (T : Finset (V → E)) (v x : V) : Use → Prop
  | .specificKnown => Dep T ∅ x
  | .specificUnknown => Dep T {v} x ∧ Var T ∅ x
  | .nonSpecific => Var T {v} x

/-- The atoms a type requires. The unattested type requires one of two atoms, a Boolean
disjunction. -/
def IndefiniteType.Requires (T : Finset (V → E)) (v x : V) : IndefiniteType → Prop
  | .unmarked => True
  | .specific => Dep T {v} x
  | .nonSpecific => Var T {v} x
  | .epistemic => Var T ∅ x
  | .specificKnown => Dep T ∅ x
  | .skPlusNS => Dep T ∅ x ∨ Var T {v} x
  | .specificUnknown => Dep T {v} x ∧ Var T ∅ x

/-- Constancy across the team is constancy within a world, which excludes variation there: the
two atoms of the unattested type cannot hold together. -/
theorem not_var_of_dep_empty (h : Dep T ∅ x) : ¬ Var T {v} x :=
  (h.mono (Finset.empty_subset _)).not_var

/-- Every team renders some use. -/
theorem Use.exists_renders (T : Finset (V → E)) (v x : V) : ∃ u : Use, u.Renders T v x := by
  by_cases hv : Dep T {v} x
  · by_cases hc : Dep T ∅ x
    · exact ⟨.specificKnown, hc⟩
    · exact ⟨.specificUnknown, hv, not_dep.1 hc⟩
  · exact ⟨.nonSpecific, not_dep.1 hv⟩

/-- No team renders two uses. -/
theorem Use.renders_unique (h : u.Renders T v x) (h' : u'.Renders T v x) : u = u' := by
  cases u <;> cases u' <;> first
    | rfl
    | exact absurd h'.2 h.not_var
    | exact absurd h.2 h'.not_var
    | exact absurd h' (not_var_of_dep_empty h)
    | exact absurd h (not_var_of_dep_empty h')
    | exact absurd h' h.1.not_var
    | exact absurd h h'.1.not_var

/-- A team meets a type's requirement exactly when it renders a use of the type's profile. For
the specific and the epistemic type this is the collapse of the disjunction of two adjacent
uses into a single atom. -/
theorem IndefiniteType.requires_iff :
    t.Requires T v x ↔ ∃ u ∈ t.profile, u.Renders T v x := by
  have h : Dep T ∅ x → Dep T {v} x := Dep.mono (Finset.empty_subset _)
  cases t <;>
    simp only [Requires, profile, Finset.mem_insert, Finset.mem_singleton, exists_eq_or_imp,
      exists_eq_left, Use.Renders, ← not_dep] <;>
    tauto

/-! ### Witnesses

Over a domain with two individuals `a` and `b` each use has a team: one assignment for the
specific known use, the two constant assignments for the specific unknown use, and a constant
assignment with its variant at the individual variable for the non-specific use. -/

section Witnesses

variable [DecidableEq (V → E)] {a b : E}

private theorem renders_unknown (hab : a ≠ b) :
    Use.specificUnknown.Renders ({fun _ ↦ a, fun _ ↦ b} : Finset (V → E)) v x := by
  refine ⟨dep_iff.2 ?_, fun _ ↦ a, by simp, fun _ ↦ b, by simp, by simp, hab⟩
  simp [hab, hab.symm]

private theorem renders_nonSpecific [DecidableEq V] (hab : a ≠ b) (hvx : v ≠ x) :
    Use.nonSpecific.Renders ({fun _ ↦ a, Function.update (fun _ ↦ a) x b} : Finset (V → E))
      v x :=
  ⟨fun _ ↦ a, by simp, Function.update (fun _ ↦ a) x b, by simp, by simp [hvx],
    by simpa using hab⟩

end Witnesses

/-- Each use has a team, given two individuals and distinct world and individual variables. -/
theorem Use.exists_team_renders [Nontrivial E] (hvx : v ≠ x) (u : Use) :
    ∃ T : Finset (V → E), u.Renders T v x := by
  classical
  obtain ⟨a, b, hab⟩ := exists_pair_ne E
  cases u
  · exact ⟨{fun _ ↦ a}, dep_singleton _⟩
  · exact ⟨_, renders_unknown hab⟩
  · exact ⟨_, renders_nonSpecific hab hvx⟩

/-- The requirements reproduce the profiles: a use entails a type's requirement exactly when
the type's profile lists it. -/
theorem forall_renders_imp_requires_iff [Nontrivial E] (hvx : v ≠ x) :
    (∀ T : Finset (V → E), u.Renders T v x → t.Requires T v x) ↔ u ∈ t.profile := by
  refine ⟨fun h ↦ ?_, fun hu T hT ↦ IndefiniteType.requires_iff.2 ⟨u, hu, hT⟩⟩
  obtain ⟨T, hT⟩ := u.exists_team_renders (E := E) hvx
  obtain ⟨u', hu', hT'⟩ := IndefiniteType.requires_iff.1 (h T hT)
  exact Use.renders_unique hT hT' ▸ hu'

/-! ### Convexity -/

/-- The attested requirements are convex: a single atom is closed under subteams or under
superteams, and the specific unknown type intersects one of each kind. -/
theorem IndefiniteType.ordConnected_requires (ht : t ≠ .skPlusNS) (v x : V) :
    {T : Finset (V → E) | t.Requires T v x}.OrdConnected := by
  cases t
  · exact Set.ordConnected_univ
  · exact (isLowerSet_dep _ _).ordConnected
  · exact (isUpperSet_var _ _).ordConnected
  · exact (isUpperSet_var _ _).ordConnected
  · exact (isLowerSet_dep _ _).ordConnected
  · exact absurd rfl ht
  · exact (isLowerSet_dep _ _).ordConnected.inter (isUpperSet_var _ _).ordConnected

/-- The unattested requirement is not convex: a specific known team lies below a specific
unknown team, which lies below a non-specific one. -/
theorem IndefiniteType.not_ordConnected_skPlusNS [Nontrivial E] (hvx : v ≠ x) :
    ¬ {T : Finset (V → E) | skPlusNS.Requires T v x}.OrdConnected := fun h ↦ by
  classical
  obtain ⟨a, b, hab⟩ := exists_pair_ne E
  have hmid : skPlusNS.Requires ({fun _ ↦ a, fun _ ↦ b} : Finset (V → E)) v x :=
    h.out (x := {fun _ ↦ a}) (.inl (dep_singleton _))
      (y := {fun _ ↦ a, fun _ ↦ b, Function.update (fun _ ↦ a) x b})
      (.inr ((renders_nonSpecific hab hvx).superset (by
        simp only [Finset.insert_subset_iff, Finset.mem_insert, Finset.mem_singleton,
          Finset.singleton_subset_iff, true_or, or_true, and_self])))
      ⟨by simp, Finset.insert_subset_insert _ (by simp)⟩
  obtain ⟨u, hu, hT⟩ := requires_iff.1 hmid
  exact absurd (Use.renders_unique (renders_unknown hab) hT ▸ hu) (by decide)

end Teams

/-! ### The types on the map -/

/-- The uses a region of the map covers. -/
def uses (s : Finset HaspelmathFunction) : Finset Use := Finset.univ.filter (·.haspelmath ∈ s)

@[simp]
theorem mem_uses {s : Finset HaspelmathFunction} {u : Use} : u ∈ uses s ↔ u.haspelmath ∈ s := by
  simp [uses]

/-- A series instantiates the type whose profile is exactly the uses it covers; by
`IndefiniteType.profile_injective` there is at most one. A series covering none of the three uses
instantiates no type. -/
def Instantiates (s : Series) (t : IndefiniteType) : Prop := uses s.functions = t.profile

instance (s : Series) (t : IndefiniteType) : Decidable (Instantiates s t) :=
  inferInstanceAs (Decidable (uses s.functions = t.profile))

/-- The paper's examples of the six attested types on the map: Italian *qualche-* is unmarked,
Georgian *-γac* specific, Russian *-nibud'* non-specific, German *irgend-* epistemic, Russian
*koe-* specific known, and Kannada *-oo* specific unknown. -/
theorem examples :
    (∃ s ∈ Haspelmath1997.italian, s.label = "qualche-" ∧ Instantiates s .unmarked) ∧
      (∃ s ∈ Haspelmath1997.georgian, s.label = "-γac" ∧ Instantiates s .specific) ∧
      (∃ s ∈ Haspelmath1997.russian,
        s.pronoun = Russian.Indefinites.nibudEntry ∧ Instantiates s .nonSpecific) ∧
      (∃ s ∈ Haspelmath1997.german,
        s.pronoun = German.Indefinites.irgendEntry ∧ Instantiates s .epistemic) ∧
      (∃ s ∈ Haspelmath1997.russian,
        s.pronoun = Russian.Indefinites.koeEntry ∧ Instantiates s .specificKnown) ∧
      ∃ s ∈ Haspelmath1997.kannada,
        s.pronoun = Kannada.Indefinites.ooEntry ∧ Instantiates s .specificUnknown := by
  decide

end DeganoAloni2025
