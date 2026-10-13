module

public import Linglib.Logic.Team.Atoms
public import Studies.Haspelmath1997
public import Mathlib.Basic.Nontrivial.Defs
public import Mathlib.Order.Interval.Set.OrdConnected

/-!
# Degano and Aloni (2025): How to be (non-)specific?

This file formalizes Degano and Aloni's typology of marked indefinites. An indefinite
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
attested requirements are all convex, the conjunction being closed under neither.

German *irgend-*, Russian *koe-* and *-nibud'*, Kannada *-oo*, Italian *qualche-* and Georgian
*-γac* instantiate the six attested types: the uses are the three specificity functions of
Haspelmath's map, the non-specific use being the irrealis function, and a series covers the uses
whose functions lie in the region the book draws for it.

## Main results

* `exists_renders`, `renders_unique`: the three uses partition the teams.
* `IndefiniteType.requires_iff`: a requirement is the disjunction of the uses of the profile.
* `IndefiniteType.ordConnected_requires_iff`: the attested requirements are convex and the
  unattested one is not.
* `connected_profile_iff`, `sample_instantiates_attested`: the convex types are the connected
  regions of the map, so no series of the sample instantiates the unattested type.

## TODO

The paper extends the system with negation and modality to derive the licensing of non-specific
indefinites and treats epistemic indefinites at length; neither is formalized here.

## References

* [degano-aloni-2025]
* [haspelmath-1997]
-/

@[expose] public section

namespace DeganoAloni2025

open Team Indefinite Haspelmath1997

/-! ### Uses and types -/

/-- The seven types of indefinite are the restrictions a marked indefinite can impose on its
uses, the unmarked indefinite imposing none. -/
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
def profile : IndefiniteType → Finset SpecificityFunction
  | .unmarked => {.specificKnown, .specificUnknown, .nonSpecific}
  | .specific => {.specificKnown, .specificUnknown}
  | .nonSpecific => {.nonSpecific}
  | .epistemic => {.specificUnknown, .nonSpecific}
  | .specificKnown => {.specificKnown}
  | .skPlusNS => {.specificKnown, .nonSpecific}
  | .specificUnknown => {.specificUnknown}

theorem profile_injective : Function.Injective profile := by decide

/-- The seven types are the seven non-empty sets of uses. -/
theorem exists_profile_eq {s : Finset SpecificityFunction} (hs : s.Nonempty) :
    ∃ t, profile t = s := by
  revert s; decide

theorem profile_nonempty (t : IndefiniteType) : t.profile.Nonempty := by
  cases t <;> decide

end IndefiniteType

/-! ### Conditions on teams -/

section Teams

variable {V E : Type*} {T : Finset (V → E)} {v x : V} {u u' : SpecificityFunction}
  {t : IndefiniteType}

/-- `Renders T v x u` says that the team `T` renders the use `u`, with `v` the world variable
and `x` the individual variable. The three uses are constancy, constancy within a world with
variation across the team, and variation within a world. -/
def Renders (T : Finset (V → E)) (v x : V) : SpecificityFunction → Prop
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

/-- Constancy across the team is constancy within a world, which excludes variation there, so
the two atoms of the unattested type cannot hold together. -/
theorem not_var_of_dep_empty (h : Dep T ∅ x) : ¬ Var T {v} x :=
  (h.mono (Finset.empty_subset _)).not_var

/-- Every team renders some use. -/
theorem exists_renders (T : Finset (V → E)) (v x : V) :
    ∃ u : SpecificityFunction, Renders T v x u := by
  by_cases hv : Dep T {v} x
  · by_cases hc : Dep T ∅ x
    · exact ⟨.specificKnown, hc⟩
    · exact ⟨.specificUnknown, hv, not_dep.1 hc⟩
  · exact ⟨.nonSpecific, not_dep.1 hv⟩

/-- No team renders two uses. -/
theorem renders_unique (h : Renders T v x u) (h' : Renders T v x u') : u = u' := by
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
    t.Requires T v x ↔ ∃ u ∈ t.profile, Renders T v x u := by
  have h : Dep T ∅ x → Dep T {v} x := Dep.mono (Finset.empty_subset _)
  cases t <;>
    simp only [Requires, profile, Finset.mem_insert, Finset.mem_singleton, exists_eq_or_imp,
      exists_eq_left, Renders, ← not_dep] <;>
    tauto

/-- On a team rendering a use, a type's requirement is met exactly when its profile lists the
use. -/
theorem IndefiniteType.requires_iff_mem_profile (hu : Renders T v x u) :
    t.Requires T v x ↔ u ∈ t.profile :=
  ⟨fun h ↦ let ⟨_, hu', hT⟩ := requires_iff.1 h; renders_unique hu hT ▸ hu',
    fun h ↦ requires_iff.2 ⟨u, h, hu⟩⟩

/-! ### Witnesses

Over a domain with two individuals `a` and `b` each use has a team: one assignment for the
specific known use, the two constant assignments for the specific unknown use, and those two
with a variant of the first at the individual variable for the non-specific use. -/

/-- A specific known team lies below a specific unknown team, which lies below a non-specific
one, given two individuals and distinct world and individual variables. -/
theorem exists_subset_renders [Nontrivial E] (hvx : v ≠ x) :
    ∃ T₁ T₂ T₃ : Finset (V → E), T₁ ⊆ T₂ ∧ T₂ ⊆ T₃ ∧ Renders T₁ v x .specificKnown ∧
      Renders T₂ v x .specificUnknown ∧ Renders T₃ v x .nonSpecific := by
  classical
  obtain ⟨a, b, hab⟩ := exists_pair_ne E
  refine ⟨{fun _ ↦ a}, {fun _ ↦ a, fun _ ↦ b},
    {fun _ ↦ a, fun _ ↦ b, Function.update (fun _ ↦ a) x b}, by simp,
    Finset.insert_subset_insert _ (by simp), dep_singleton _,
    ⟨dep_iff.2 ?_, var_iff.2 ⟨fun _ ↦ a, by simp, fun _ ↦ b, by simp, by simp, hab⟩⟩,
    var_iff.2 ⟨fun _ ↦ a, by simp, Function.update (fun _ ↦ a) x b, by simp, by simp [hvx],
      by simpa using hab⟩⟩
  simp [hab, hab.symm]

/-- Each use has a team, given two individuals and distinct world and individual variables. -/
theorem exists_team_renders [Nontrivial E] (hvx : v ≠ x) (u : SpecificityFunction) :
    ∃ T : Finset (V → E), Renders T v x u := by
  obtain ⟨T₁, T₂, T₃, -, -, h₁, h₂, h₃⟩ := exists_subset_renders (E := E) hvx
  cases u <;> exact ⟨_, ‹_›⟩

/-- A use entails a type's requirement exactly when the type's profile lists it, so the
requirements reproduce the profiles. -/
theorem forall_renders_imp_requires_iff [Nontrivial E] (hvx : v ≠ x) :
    (∀ T : Finset (V → E), Renders T v x u → t.Requires T v x) ↔ u ∈ t.profile :=
  ⟨fun h ↦ let ⟨T, hT⟩ := exists_team_renders (E := E) hvx u
    (IndefiniteType.requires_iff_mem_profile hT).1 (h T hT),
    fun hu _ hT ↦ (IndefiniteType.requires_iff_mem_profile hT).2 hu⟩

/-- One requirement entails another exactly when every use of the first type is a use of the
second, so semantic weakening is inclusion of profiles. -/
theorem forall_requires_imp_requires_iff [Nontrivial E] (hvx : v ≠ x) {t t' : IndefiniteType} :
    (∀ T : Finset (V → E), t.Requires T v x → t'.Requires T v x) ↔ t.profile ⊆ t'.profile := by
  refine ⟨fun h u hu ↦ ?_, fun h T ↦ ?_⟩
  · obtain ⟨T, hT⟩ := exists_team_renders (E := E) hvx u
    exact (IndefiniteType.requires_iff_mem_profile hT).1
      (h T ((IndefiniteType.requires_iff_mem_profile hT).2 hu))
  · simp only [IndefiniteType.requires_iff]
    exact fun ⟨u, hu, hT⟩ ↦ ⟨u, h hu, hT⟩

/-! ### Convexity -/

/-- The attested requirements are convex, since a single atom is closed under subteams or under
superteams and the specific unknown type intersects one of each kind. -/
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

/-- The unattested requirement is not convex, since a specific known team lies below a specific
unknown team, which lies below a non-specific one. -/
theorem IndefiniteType.not_ordConnected_skPlusNS [Nontrivial E] (hvx : v ≠ x) :
    ¬ {T : Finset (V → E) | skPlusNS.Requires T v x}.OrdConnected := fun h ↦ by
  obtain ⟨T₁, T₂, T₃, h₁₂, h₂₃, h₁, h₂, h₃⟩ := exists_subset_renders (E := E) hvx
  have hT₂ : skPlusNS.Requires T₂ v x := h.out (x := T₁) (.inl h₁) (y := T₃) (.inr h₃) ⟨h₁₂, h₂₃⟩
  exact absurd ((requires_iff_mem_profile h₂).1 hT₂) (by decide)

/-- Convexity separates the attested types from the unattested one. -/
theorem IndefiniteType.ordConnected_requires_iff [Nontrivial E] (hvx : v ≠ x) :
    {T : Finset (V → E) | t.Requires T v x}.OrdConnected ↔ t ≠ .skPlusNS :=
  ⟨by rintro h rfl; exact not_ordConnected_skPlusNS hvx h, fun ht ↦ ordConnected_requires ht v x⟩

/-! ### Monotonicity

A constancy atom is closed under subteams and a variation atom under superteams. The specific
unknown requirement, the conjunction of one of each, is convex and closed under neither. -/

theorem IndefiniteType.not_isLowerSet_specificUnknown [Nontrivial E] (hvx : v ≠ x) :
    ¬ IsLowerSet {T : Finset (V → E) | specificUnknown.Requires T v x} := fun h ↦ by
  obtain ⟨T₁, T₂, -, h₁₂, -, h₁, h₂, -⟩ := exists_subset_renders (E := E) hvx
  have hT₁ : specificUnknown.Requires T₁ v x := h h₁₂ h₂
  exact absurd ((requires_iff_mem_profile h₁).1 hT₁) (by decide)

theorem IndefiniteType.not_isUpperSet_specificUnknown [Nontrivial E] (hvx : v ≠ x) :
    ¬ IsUpperSet {T : Finset (V → E) | specificUnknown.Requires T v x} := fun h ↦ by
  obtain ⟨-, T₂, T₃, -, h₂₃, -, h₂, h₃⟩ := exists_subset_renders (E := E) hvx
  have hT₃ : specificUnknown.Requires T₃ v x := h h₂₃ h₂
  exact absurd ((requires_iff_mem_profile h₃).1 hT₃) (by decide)

end Teams

/-! ### The types on the map -/

/-- A series instantiates the type whose profile is exactly the uses it covers; by
`IndefiniteType.profile_injective` there is at most one. A series covering none of the three uses
instantiates no type. -/
def Instantiates (s : Series) (t : IndefiniteType) : Prop :=
  specificityFunctions s.functions = t.profile

instance (s : Series) (t : IndefiniteType) : Decidable (Instantiates s t) :=
  inferInstanceAs (Decidable (specificityFunctions s.functions = t.profile))

/-- The unattested profile skips the specific unknown function, which lies between the two it
covers, so no connected region of the map covers exactly its uses. -/
theorem specificityFunctions_ne_skPlusNS_profile {s : Finset HaspelmathFunction}
    (h : (implicationalMap.induce ↑s).Connected) :
    specificityFunctions s ≠ IndefiniteType.skPlusNS.profile := fun he ↦ by
  have hk : SpecificityFunction.specificKnown ∈ specificityFunctions s := he ▸ by decide
  have hn : SpecificityFunction.nonSpecific ∈ specificityFunctions s := he ▸ by decide
  have hu : SpecificityFunction.specificUnknown ∈ specificityFunctions s :=
    mem_specificityFunctions.2 (Haspelmath1997.specificUnknown_mem_of_irrealis_mem h
      (mem_specificityFunctions.1 hk) (mem_specificityFunctions.1 hn))
  exact absurd (he ▸ hu) (by decide)

/-- The map orders the uses as the meaning space does, in that a type's uses form a connected
region of the map exactly when the type is not the unattested one, which is when its requirement
is convex. -/
theorem connected_profile_iff {t : IndefiniteType} :
    (implicationalMap.induce ↑(t.profile.image SpecificityFunction.toFunction)).Connected ↔
      t ≠ .skPlusNS := by
  cases t <;> decide

/-- The unattested type is unattested in the sample, since every series covering one of the
three uses covers a connected region and so instantiates an attested type. -/
theorem sample_instantiates_attested :
    ∀ p ∈ Haspelmath1997.sample, ∀ s ∈ p, (specificityFunctions s.functions).Nonempty →
      ∃ t, t ≠ .skPlusNS ∧ Instantiates s t := fun p hp s hs hne ↦
  let ⟨t, ht⟩ := IndefiniteType.exists_profile_eq hne
  ⟨t, fun h ↦ specificityFunctions_ne_skPlusNS_profile
    (Haspelmath1997.sample_connected p hp s hs) (h ▸ ht.symm), ht.symm⟩

/-- The paper's examples instantiate the six attested types on the map, Italian *qualche-* the
unmarked one, Georgian *-γac* the specific, Russian *-nibud'* the non-specific, German *irgend-*
the epistemic, Russian *koe-* the specific known and Kannada *-oo* the specific unknown. -/
theorem examples :
    (∃ s ∈ Haspelmath1997.italian, s.label = "qualche-" ∧ Instantiates s .unmarked) ∧
      (∃ s ∈ Haspelmath1997.georgian, s.label = "-γac" ∧ Instantiates s .specific) ∧
      (∃ s ∈ Haspelmath1997.russian,
        s.pronoun = Russian.Indefinites.ktoNibud ∧ Instantiates s .nonSpecific) ∧
      (∃ s ∈ Haspelmath1997.german,
        s.pronoun = German.Indefinites.irgendEntry ∧ Instantiates s .epistemic) ∧
      (∃ s ∈ Haspelmath1997.russian,
        s.pronoun = Russian.Indefinites.koeKto ∧ Instantiates s .specificKnown) ∧
      ∃ s ∈ Haspelmath1997.kannada,
        s.pronoun = Kannada.Indefinites.ooEntry ∧ Instantiates s .specificUnknown := by
  decide

end DeganoAloni2025
