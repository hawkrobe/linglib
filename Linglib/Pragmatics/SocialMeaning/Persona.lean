module

public import Linglib.Pragmatics.SocialMeaning.Dimension
public import Linglib.Pragmatics.SocialMeaning.IndexicalField

/-!
# Personae and grounded fields

This file defines the personae and grounded indexical fields of [burnett-2019] and the
Eckert–Montague lift of a field to persona compatibility. A property space is a graph of
incompatibility on social properties, a persona is a maximal independent set of it, and a
grounded field indexes each variant to an independent set of properties. The lift sends a
variant to the personae compatible with it,
those with every property it indexes, or on the Montagovian-individual reading those sharing
some property with it, as an entity lifts to the generalized quantifier of the properties it
has. An association field over the dimensions of social evaluation grounds as the poles whose
polarity is the sign of the association.

## Main definitions

* `GroundedField`: an indexical field whose values are independent sets of an incompatibility
  graph.
* `GroundedField.Compatible`, `GroundedField.Meets`: a persona has every property a variant
  indexes, or shares one with it.
* `GroundedField.lift`, `GroundedField.liftMI`: the personae compatible with a variant on each
  reading.
* `Persona`: a maximal independent set of the incompatibility graph, and
  `GroundedField.personae`, the personae that meet a variant.
* `AssociationField.ground`: the grounded field of an association field over the dimensions.

## Main results

* `GroundedField.lift_subset_lift`, `GroundedField.liftMI_subset_liftMI`: the lift is antitone
  and the Montagovian-individual lift monotone in the indexed properties.

## References

* [burnett-2019]
* [eckert-2008]
-/

@[expose] public section

namespace SocialMeaning

/-- A grounded field indexes each variant to an independent set of the incompatibility graph
on properties. -/
structure GroundedField (Variant : Type*) {P : Type*} (G : SimpleGraph P) where
  /-- The properties each variant indexes. -/
  indexes : IndexicalField Variant P
  isIndepSet : ∀ v, G.IsIndepSet (indexes v : Set P)

namespace GroundedField

variable {Variant P : Type*} {G : SimpleGraph P} (F : GroundedField Variant G) (v : Variant)
  (π : Finset P) {v₁ v₂ : Variant}

/-- A persona is compatible with a variant when it has every property the variant indexes. -/
def Compatible : Prop := F.indexes v ⊆ π

/-- On the Montagovian-individual reading, a persona meets a variant when it shares a property
with it. -/
def Meets : Prop := ¬ Disjoint (F.indexes v) π

instance [DecidableEq P] : Decidable (F.Compatible v π) :=
  inferInstanceAs (Decidable (F.indexes v ⊆ π))

instance [DecidableEq P] : Decidable (F.Meets v π) :=
  inferInstanceAs (Decidable (¬ Disjoint _ _))

variable [Fintype P] [DecidableEq P] [DecidableRel G.Adj]

/-- The Eckert–Montague lift sends a variant to the personae compatible with it. -/
def lift : Finset (Finset P) := G.maximalIndepSets.filter (F.Compatible v)

/-- The Montagovian-individual lift sends a variant to the personae that meet it. -/
def liftMI : Finset (Finset P) := G.maximalIndepSets.filter (F.Meets v)

/-- The more a variant indexes, the fewer personae are compatible with it. -/
theorem lift_subset_lift (h : F.indexes v₁ ⊆ F.indexes v₂) : F.lift v₂ ⊆ F.lift v₁ :=
  Finset.monotone_filter_right _ λ _ _ hπ => h.trans hπ

/-- The more a variant indexes, the more personae meet it. -/
theorem liftMI_subset_liftMI (h : F.indexes v₁ ⊆ F.indexes v₂) : F.liftMI v₁ ⊆ F.liftMI v₂ :=
  Finset.monotone_filter_right _ λ _ _ hπ hd => hπ (hd.mono_left h)

end GroundedField

/-- A persona is a maximal independent set of the incompatibility graph, a maximal consistent
set of properties. -/
abbrev Persona {P : Type*} (G : SimpleGraph P) [Fintype P] [DecidableEq P] [DecidableRel G.Adj] :
    Type _ :=
  {π : Finset P // π ∈ G.maximalIndepSets}

/-- The personae that meet a variant. -/
def GroundedField.personae {Variant P : Type*} {G : SimpleGraph P} [Fintype P] [DecidableEq P]
    [DecidableRel G.Adj] (F : GroundedField Variant G) (v : Variant) : Finset (Persona G) :=
  Finset.univ.filter λ π => F.Meets v π.1

@[simp] theorem GroundedField.mem_personae {Variant P : Type*} {G : SimpleGraph P} [Fintype P]
    [DecidableEq P] [DecidableRel G.Adj] {F : GroundedField Variant G} {v : Variant}
    {π : Persona G} : π ∈ F.personae v ↔ F.Meets v π.1 := by
  simp [GroundedField.personae]

/-- An association field over the dimensions grounds as the poles whose polarity is the sign
of the variant's association with their dimension. -/
def AssociationField.ground {Variant R : Type*} [Zero R] [Preorder R] [DecidableLT R]
    (M : AssociationField Variant Dimension R) : GroundedField Variant Pole.incompatible where
  indexes v := Finset.univ.filter λ p => SignType.sign (M v p.dimension) = p.polarity
  isIndepSet v p hp q hq hne hadj := hne <| Pole.eq_iff.2 ⟨hadj.2, by
    rw [← (Finset.mem_filter.1 hp).2, ← (Finset.mem_filter.1 hq).2, hadj.2]⟩

@[simp] theorem AssociationField.mem_ground_indexes {Variant R : Type*} [Zero R] [Preorder R]
    [DecidableLT R] {M : AssociationField Variant Dimension R} {v : Variant} {p : Pole} :
    p ∈ M.ground.indexes v ↔ SignType.sign (M v p.dimension) = p.polarity := by
  simp [AssociationField.ground]

end SocialMeaning
