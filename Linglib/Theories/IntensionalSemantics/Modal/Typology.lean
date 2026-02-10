import Linglib.Core.ModalLogic
import Linglib.Theories.IntensionalSemantics.Modal.Kratzer

/-!
# Modal Semantic Universals

Formalizes the Independence of Force and Flavor (IFF) universal and the
Single Axis of Variability (SAV) universal from cross-linguistic modal typology.

## Key Definitions

* `satisfiesIFF`: A modal meaning ⟦m⟧ satisfies IFF iff ⟦m⟧ = fo(m) × fl(m)
* `satisfiesSAV`: A modal meaning satisfies SAV iff it varies on at most one axis
* `iffDegree`: Fraction of modals in a language satisfying IFF

## Key Theorems

* `sav_implies_iff`: SAV is strictly stronger than IFF
* `cartesianProduct_satisfies_iff`: Kratzer's independent parameterization → IFF

## References

* Nauze (2008). Modality in Typological Perspective.
* Steinert-Threlkeld, Imel, & Guo (2023). A Semantic Universal for Modal Language.
* Imel, Guo, & Steinert-Threlkeld (2026). An Efficient Communication Analysis of Modal Typology.
-/

namespace IntensionalSemantics.Modal.Typology

open Core.ModalLogic (ModalForce ModalFlavor ForceFlavor)

/-! ## Modal Meaning Projections -/

/-- The set of forces expressed by a modal meaning. -/
def forces (m : List ForceFlavor) : List ModalForce :=
  (m.map (·.force)).eraseDups

/-- The set of flavors expressed by a modal meaning. -/
def flavors (m : List ForceFlavor) : List ModalFlavor :=
  (m.map (·.flavor)).eraseDups

/-! ## Semantic Universals -/

/-- **Independence of Force and Flavor (IFF).**

A modal meaning satisfies IFF iff for any two pairs (fo₁, fl₁) and (fo₂, fl₂)
in the meaning, the pair (fo₁, fl₂) is also in the meaning.
Equivalently: ⟦m⟧ = fo(m) × fl(m) (Cartesian closure).

Alternative formulation: a modal m satisfies IFF just in case ⟦m⟧ = fo(m) × fl(m),
where × is the Cartesian product.

Steinert-Threlkeld, Imel, & Guo (2023). -/
def satisfiesIFF (m : List ForceFlavor) : Bool :=
  m.all fun ⟨fo₁, _⟩ =>
    m.all fun ⟨_, fl₂⟩ =>
      m.any fun ff => ff.force == fo₁ && ff.flavor == fl₂

/-- **Single Axis of Variability (SAV).**

A modal meaning satisfies SAV iff it exhibits variation along at most one axis
of the force-flavor space: either all pairs share the same force, or all pairs
share the same flavor.

[Alternative formulation: |fo(m)| = 1 or |fl(m)| = 1.]

Nauze (2008). -/
def satisfiesSAV (m : List ForceFlavor) : Bool :=
  m.all (fun ff₁ => m.all (fun ff₂ => ff₁.force == ff₂.force)) ||
  m.all (fun ff₁ => m.all (fun ff₂ => ff₁.flavor == ff₂.flavor))

/-! ## Relationship Between Universals -/

/-- SAV is strictly stronger than IFF: every SAV meaning is IFF.

**Proof sketch**: If all forces are equal to fo₀ (SAV left disjunct), then for any
(fo₁, fl₁) ∈ m and (_, fl₂) ∈ m, fo₁ = fo₀ and the pair (fo₂, fl₂) with
flavor fl₂ already has force fo₀ = fo₁, so (fo₁, fl₂) ∈ m.
Symmetric for the right disjunct. -/
theorem sav_implies_iff (m : List ForceFlavor) (h : satisfiesSAV m = true) :
    satisfiesIFF m = true := by
  unfold satisfiesSAV at h
  unfold satisfiesIFF
  simp only [Bool.or_eq_true] at h
  simp only [List.all_eq_true, List.any_eq_true, Bool.and_eq_true]
  intro ⟨fo₁, fl₁⟩ h₁ ⟨fo₂, fl₂⟩ h₂
  rcases h with hForce | hFlavor
  · -- All forces equal: fo₁ = fo₂, so witness is (fo₂, fl₂) itself
    have hfo : (fo₂ == fo₁) = true := by
      have h₂₁ := List.all_eq_true.mp (List.all_eq_true.mp hForce ⟨fo₂, fl₂⟩ h₂) ⟨fo₁, fl₁⟩ h₁
      simp only [BEq.beq] at h₂₁ ⊢
      exact h₂₁
    exact ⟨⟨fo₂, fl₂⟩, h₂, hfo, beq_self_eq_true fl₂⟩
  · -- All flavors equal: fl₁ = fl₂, so witness is (fo₁, fl₁) itself
    have hfl : (fl₁ == fl₂) = true := by
      have h₁₂ := List.all_eq_true.mp (List.all_eq_true.mp hFlavor ⟨fo₁, fl₁⟩ h₁) ⟨fo₂, fl₂⟩ h₂
      simp only [BEq.beq] at h₁₂ ⊢
      exact h₁₂
    exact ⟨⟨fo₁, fl₁⟩, h₁, beq_self_eq_true fo₁, hfl⟩

/-- IFF does NOT imply SAV: a meaning can vary on both axes while satisfying IFF.
    E.g., {(nec,e),(nec,d),(poss,e),(poss,d)} is IFF but not SAV. -/
theorem iff_not_implies_sav :
    ∃ m : List ForceFlavor,
      satisfiesIFF m = true ∧ satisfiesSAV m = false := by
  exact ⟨[⟨.necessity, .epistemic⟩, ⟨.necessity, .deontic⟩,
          ⟨.possibility, .epistemic⟩, ⟨.possibility, .deontic⟩],
         by native_decide, by native_decide⟩

/-! ## Cartesian Products in the Force-Flavor Space -/

/-- Local abbreviation for the Core infrastructure, for readability. -/
abbrev cartesianProduct := ForceFlavor.cartesianProduct

/-- Membership in a Cartesian product: `⟨fo, fl⟩ ∈ fos × fls` iff `fo ∈ fos ∧ fl ∈ fls`. -/
theorem mem_cartesianProduct (ff : ForceFlavor) (fos : List ModalForce)
    (fls : List ModalFlavor) :
    ff ∈ cartesianProduct fos fls ↔ ff.force ∈ fos ∧ ff.flavor ∈ fls := by
  unfold cartesianProduct ForceFlavor.cartesianProduct
  simp only [List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨fo, hfo, fl, hfl, rfl⟩; exact ⟨hfo, hfl⟩
  · rintro ⟨hfo, hfl⟩; exact ⟨ff.force, hfo, ff.flavor, hfl, rfl⟩

/-- Any Cartesian product of forces and flavors satisfies IFF.

    This is the formal content of Kratzer's (1981) insight that force
    (quantificational) and flavor (contextual) are **independent** parameters
    in the semantics of modals. -/
theorem cartesianProduct_satisfies_iff
    (fos : List ModalForce) (fls : List ModalFlavor) :
    satisfiesIFF (cartesianProduct fos fls) = true := by
  unfold satisfiesIFF cartesianProduct ForceFlavor.cartesianProduct
  simp only [List.all_eq_true, List.any_eq_true, Bool.and_eq_true]
  intro ⟨fo₁, _⟩ h₁ ⟨_, fl₂⟩ h₂
  simp only [List.mem_flatMap, List.mem_map, ForceFlavor.mk.injEq] at h₁ h₂
  obtain ⟨fo₁', hfo₁, fl₁', _, rfl, _⟩ := h₁
  obtain ⟨fo₂', _, fl₂', hfl₂, _, rfl⟩ := h₂
  exact ⟨⟨fo₁', fl₂'⟩,
         List.mem_flatMap.mpr ⟨fo₁', hfo₁, List.mem_map.mpr ⟨fl₂', hfl₂, rfl⟩⟩,
         beq_self_eq_true fo₁', beq_self_eq_true fl₂'⟩

/-- A Cartesian product with a singleton force axis satisfies SAV.
    Covers fixed-force Kratzer modals (e.g., English "must", "can"). -/
theorem cartesianProduct_singleton_force_satisfies_sav
    (fo : ModalForce) (fls : List ModalFlavor) :
    satisfiesSAV (cartesianProduct [fo] fls) = true := by
  unfold satisfiesSAV
  simp only [Bool.or_eq_true]
  left
  simp only [List.all_eq_true]
  intro ff₁ h₁ ff₂ h₂
  have hfo₁ : ff₁.force = fo :=
    ((mem_cartesianProduct ff₁ [fo] fls).mp h₁).1 |> List.mem_singleton.mp
  have hfo₂ : ff₂.force = fo :=
    ((mem_cartesianProduct ff₂ [fo] fls).mp h₂).1 |> List.mem_singleton.mp
  rw [hfo₁, hfo₂]
  exact beq_self_eq_true fo

/-- A Cartesian product with a singleton flavor axis satisfies SAV.
    Covers variable-force Kratzer modals (e.g., Gitksan ima'a). -/
theorem cartesianProduct_singleton_flavor_satisfies_sav
    (fos : List ModalForce) (fl : ModalFlavor) :
    satisfiesSAV (cartesianProduct fos [fl]) = true := by
  unfold satisfiesSAV
  simp only [Bool.or_eq_true]
  right
  simp only [List.all_eq_true]
  intro ff₁ h₁ ff₂ h₂
  have hfl₁ : ff₁.flavor = fl :=
    ((mem_cartesianProduct ff₁ fos [fl]).mp h₁).2 |> List.mem_singleton.mp
  have hfl₂ : ff₂.flavor = fl :=
    ((mem_cartesianProduct ff₂ fos [fl]).mp h₂).2 |> List.mem_singleton.mp
  rw [hfl₁, hfl₂]
  exact beq_self_eq_true fl

/-- Singleton meanings trivially satisfy IFF. -/
theorem singleton_satisfies_iff (ff : ForceFlavor) :
    satisfiesIFF [ff] = true := by
  unfold satisfiesIFF
  simp only [List.all_cons, List.all_nil, List.any_cons, List.any_nil,
    Bool.and_true, Bool.or_false]
  cases ff with | mk fo fl => cases fo <;> cases fl <;> decide

/-- Empty meanings trivially satisfy IFF. -/
theorem empty_satisfies_iff : satisfiesIFF [] = true := by
  unfold satisfiesIFF; simp [List.all_nil]

/-! ## Language-Level Measures -/

/-- A modal expression datum: a form paired with its meaning in the 2×3 space. -/
structure ModalExpression where
  form : String
  meaning : List ForceFlavor
  deriving Repr, BEq

/-- A language's modal inventory. -/
structure ModalInventory where
  language : String
  family : String
  source : String
  expressions : List ModalExpression
  deriving Repr

/-- Whether all modals in a language satisfy IFF. -/
def ModalInventory.allIFF (inv : ModalInventory) : Bool :=
  inv.expressions.all fun e => satisfiesIFF e.meaning

/-- Number of IFF-satisfying modals in a language. -/
def ModalInventory.iffCount (inv : ModalInventory) : Nat :=
  (inv.expressions.filter fun e => satisfiesIFF e.meaning).length

/-- Total number of modals in a language. -/
def ModalInventory.size (inv : ModalInventory) : Nat :=
  inv.expressions.length

/-- IFF degree: fraction of modals satisfying IFF (as a rational).
    This is the paper's "naturalness" measure. -/
def ModalInventory.iffDegreeNum (inv : ModalInventory) : Nat × Nat :=
  (inv.iffCount, inv.size)

/-- Whether a language has any synonymous modals (same meaning, different form). -/
def ModalInventory.hasSynonymy (inv : ModalInventory) : Bool :=
  inv.expressions.any fun e₁ =>
    inv.expressions.any fun e₂ =>
      e₁.form != e₂.form && e₁.meaning == e₂.meaning

/-! ## Fragment Integration -/

/-- Construct a modal inventory from fragment auxiliary entries.
    Filters to entries with non-empty modal meanings. -/
def ModalInventory.fromAuxEntries {α : Type}
    (language family source : String) (entries : List α)
    (form : α → String) (meaning : α → List ForceFlavor) : ModalInventory where
  language := language
  family := family
  source := source
  expressions := entries.filterMap fun e =>
    let m := meaning e
    if m.isEmpty then none else some ⟨form e, m⟩

/-! ## Kratzer-Typology Bridge

Connects Kratzer's parameterized modal semantics (conversational backgrounds,
ordering sources) to the typological force-flavor space. A Kratzerian modal
with fixed force and contextually variable flavors produces a meaning
`cartesianProduct [force] flavors`, which satisfies both IFF and SAV.
Variable-force modals (e.g., Gitksan ima'a) produce
`cartesianProduct forces [flavor]`, also satisfying both. -/

open IntensionalSemantics.Modal.Kratzer (KratzerParams)

/-- A flavor assignment maps each typological `ModalFlavor` to a
    Kratzer parameterization (modal base + ordering source). -/
structure FlavorAssignment where
  assign : ModalFlavor → KratzerParams

/-- Canonical assignment from the standard Kratzer flavor structures. -/
def canonicalAssignment
    (epist : IntensionalSemantics.Modal.Kratzer.EpistemicFlavor)
    (deont : IntensionalSemantics.Modal.Kratzer.DeonticFlavor)
    (teleo : IntensionalSemantics.Modal.Kratzer.TeleologicalFlavor) :
    FlavorAssignment where
  assign
    | .epistemic => epist.toKratzerParams
    | .deontic => deont.toKratzerParams
    | .circumstantial => teleo.toKratzerParams

end IntensionalSemantics.Modal.Typology
