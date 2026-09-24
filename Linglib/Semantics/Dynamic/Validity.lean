module

public import Linglib.Semantics.Dynamic.Update
public import Mathlib.Dynamics.FixedPoints.Defs
public import Mathlib.Order.BoundedOrder.Lattice
public import Mathlib.Tactic.TFAE

/-!
# Notions of validity in update semantics

An update system interprets each sentence as an operation on information states, and a state
accepts a sentence when updating it with the sentence changes nothing, that is, when the state is
a fixed point of the update. [veltman-1996] distinguishes three notions of validity. An argument
is valid₁ when updating the minimal state with the premises in order yields a state that accepts
the conclusion, valid₂ when this holds from every state, and valid₃ when every state that accepts
each premise accepts the conclusion.

An update is additive when it meets its input with the result of updating the minimal state, so
that a static content fixes its dynamic meaning. The additive updates are exactly those satisfying
Veltman's four constraints, Strengthening, Monotony, Idempotence and Persistence, and for additive
updates the three notions of validity coincide, each saying that the contents of the premises
jointly entail the content of the conclusion. In general they come apart. Validity₃ is monotone in
the premises and validity₂ is monotone on the left, while validity₁ is neither, but inserting a
conclusion that validity₁ has drawn into the premise sequence changes nothing, which gives
Sequential Monotony and Sequential Cut. On sets of possibilities the additive updates are the
classical ones of `Semantics/Dynamic/Update.lean`, the static updates with a content, and the
dynamic entailment that a satisfaction relation induces there is validity₂.

## Main definitions

* `DynamicSemantics.Valid₁`, `DynamicSemantics.Valid₂`, `DynamicSemantics.Valid₃`: the three
  notions of validity.
* `DynamicSemantics.IsAdditive`: the update meets its input with a fixed content.

## Main results

* `DynamicSemantics.isAdditive_iff`: additivity is Strengthening, Monotony, Idempotence and
  Persistence together.
* `DynamicSemantics.tfae_valid`: for additive updates the three notions of validity coincide.
* `DynamicSemantics.Valid₁.insert_iff`: Sequential Monotony and Sequential Cut.
* `DynamicSemantics.valid₁_append_self`: under Idempotence validity₁ is reflexive.
* `DynamicSemantics.isFixedPt_foldl_iff`: along updates that never add possibilities, a state
  accepts a text exactly when it accepts each of its sentences.
* `DynamicSemantics.CCP.isAdditive_iff_isClassical`: on sets of possibilities the additive
  updates are the classical ones.
* `DynamicSemantics.dynamicEntailsOf_iff_valid₂`: the dynamic entailment a satisfaction relation
  induces is validity₂.

## Implementation notes

States are ordered by inclusion, as for `DynamicSemantics.CCP` and `DynamicSemantics.ExpState`:
a more informed state lies lower, the minimal state is `⊤`, and Strengthening says that an update
never adds possibilities. Veltman orients the order the other way, with the minimal state `0` at
the bottom and the sum of two states their join, and the content is the same. Acceptance is
`Function.IsFixedPt`. A sentence is identified with its update and a text with the list of its
updates, applied from the left by `List.foldl`.

Read in the reversed order, the four constraints make an update a closure operator whose closed
elements form an upper set, and `isAdditive_iff` says that such an operator is `(· ⊔ c ⊥)`.

## References

* [F. Veltman, *Defaults in Update Semantics*][veltman-1996]
-/

@[expose] public section

namespace DynamicSemantics

open Function

variable {α : Type*}

/-! ### Validity -/

section Validity

variable (ψs : List (α → α)) (φ : α → α)

/-- An argument is *valid₁* when updating the minimal state with the premises in order yields a
state that accepts the conclusion. -/
def Valid₁ [Top α] : Prop := IsFixedPt φ (ψs.foldl (fun σ ψ ↦ ψ σ) ⊤)

/-- An argument is *valid₂* when updating any state with the premises in order yields a state that
accepts the conclusion. -/
def Valid₂ : Prop := ∀ σ, IsFixedPt φ (ψs.foldl (fun σ ψ ↦ ψ σ) σ)

/-- An argument is *valid₃* when every state that accepts each premise accepts the conclusion. -/
def Valid₃ : Prop := ∀ σ, (∀ ψ ∈ ψs, IsFixedPt ψ σ) → IsFixedPt φ σ

variable {ψs φ}

theorem Valid₂.valid₁ [Top α] (h : Valid₂ ψs φ) : Valid₁ ψs φ := h ⊤

/-- Validity₃ is monotone: adding premises preserves it. -/
theorem Valid₃.mono {χs : List (α → α)} (h : Valid₃ ψs φ) (hsub : ψs ⊆ χs) : Valid₃ χs φ :=
  fun σ hσ ↦ h σ fun ψ hψ ↦ hσ ψ (hsub hψ)

/-- Validity₂ is left monotone: adding premises in front preserves it. -/
theorem Valid₂.append_left (h : Valid₂ ψs φ) (χs : List (α → α)) : Valid₂ (χs ++ ψs) φ :=
  fun σ ↦ by rw [List.foldl_append]; exact h _

/-- Inserting a valid₁ conclusion right after its premises changes nothing. From right to left
this is Sequential Monotony, and from left to right Sequential Cut. -/
theorem Valid₁.insert_iff [Top α] (h : Valid₁ ψs φ) {θs : List (α → α)} {χ : α → α} :
    Valid₁ (ψs ++ φ :: θs) χ ↔ Valid₁ (ψs ++ θs) χ := by
  simp only [Valid₁, List.foldl_append, List.foldl_cons, h.eq]

/-- Under Idempotence validity₁ is reflexive: a sentence follows from any premises ending in it. -/
theorem valid₁_append_self [Top α] (hφ : ∀ σ, IsFixedPt φ (φ σ)) : Valid₁ (ψs ++ [φ]) φ := by
  simpa [Valid₁] using hφ _

end Validity

/-! ### Texts of eliminative updates -/

section Eliminative

variable [PartialOrder α] {ψs : List (α → α)}

private theorem foldl_le (h : ∀ ψ ∈ ψs, ∀ σ, ψ σ ≤ σ) (σ : α) :
    ψs.foldl (fun σ ψ ↦ ψ σ) σ ≤ σ := by
  induction ψs generalizing σ with
  | nil => exact le_rfl
  | cons ψ ψs ih =>
    exact (ih (fun χ hχ ↦ h χ (List.mem_cons_of_mem ψ hχ)) (ψ σ)).trans (h ψ (by simp) σ)

/-- Along updates that never add possibilities, a state accepts a text exactly when it accepts
each of its sentences. -/
theorem isFixedPt_foldl_iff (h : ∀ ψ ∈ ψs, ∀ σ, ψ σ ≤ σ) {σ : α} :
    IsFixedPt (fun σ ↦ ψs.foldl (fun σ ψ ↦ ψ σ) σ) σ ↔ ∀ ψ ∈ ψs, IsFixedPt ψ σ := by
  induction ψs with
  | nil => simp [IsFixedPt]
  | cons ψ ψs ih =>
    have h' : ∀ χ ∈ ψs, ∀ σ, χ σ ≤ σ := fun χ hχ ↦ h χ (List.mem_cons_of_mem ψ hχ)
    simp only [List.forall_mem_cons, ← ih h']
    refine ⟨fun hσ ↦ ?_, fun ⟨hψ, hσ⟩ ↦ by simpa [IsFixedPt, hψ.eq] using hσ⟩
    have hψ : IsFixedPt ψ σ :=
      le_antisymm (h ψ (by simp) σ) (hσ.symm.le.trans (foldl_le h' (ψ σ)))
    exact ⟨hψ, by simpa [IsFixedPt, hψ.eq] using hσ⟩

end Eliminative

/-! ### Additive updates -/

section Additive

variable [SemilatticeInf α] [OrderTop α] {f g φ : α → α} {ψs : List (α → α)} {σ : α}

/-- An update is *additive* when it meets its input with the update of the minimal state, so that
a static content determines it. -/
def IsAdditive (f : α → α) : Prop := ∀ σ, f σ = σ ⊓ f ⊤

theorem IsAdditive.le (hf : IsAdditive f) (σ : α) : f σ ≤ σ := (hf σ).trans_le inf_le_left

/-- A state accepts an additive update exactly when it lies below the update's content. -/
theorem IsAdditive.isFixedPt_iff (hf : IsAdditive f) : IsFixedPt f σ ↔ σ ≤ f ⊤ := by
  rw [IsFixedPt, hf σ, inf_eq_left]

theorem isAdditive_id : IsAdditive (id : α → α) := fun _ ↦ inf_top_eq _ |>.symm

theorem IsAdditive.comp (hg : IsAdditive g) (hf : IsAdditive f) : IsAdditive (g ∘ f) := fun σ ↦ by
  show g (f σ) = σ ⊓ g (f ⊤)
  rw [hg (f σ), hf σ, hg (f ⊤), inf_assoc]

/-- A text of additive updates is additive. -/
theorem isAdditive_foldl (h : ∀ ψ ∈ ψs, IsAdditive ψ) :
    IsAdditive fun σ ↦ ψs.foldl (fun σ ψ ↦ ψ σ) σ := by
  induction ψs with
  | nil => exact isAdditive_id
  | cons ψ ψs ih => exact (ih fun χ hχ ↦ h χ (List.mem_cons_of_mem ψ hχ)).comp (h ψ (by simp))

/-- An update is additive exactly when it satisfies Strengthening, never adding possibilities,
Monotony, Idempotence, and Persistence, the states that accept it being closed downward. -/
theorem isAdditive_iff : IsAdditive f ↔
    (∀ σ, f σ ≤ σ) ∧ Monotone f ∧ (∀ σ, IsFixedPt f (f σ)) ∧ IsLowerSet (fixedPoints f) := by
  refine ⟨fun h ↦ ⟨h.le, fun σ τ hστ ↦ ?_, fun σ ↦ ?_, fun σ τ hτσ hσ ↦ ?_⟩,
    fun ⟨hle, hmono, hidem, hpers⟩ σ ↦ ?_⟩
  · rw [h σ, h τ]; exact inf_le_inf_right _ hστ
  · rw [IsFixedPt, h (f σ), h σ, inf_assoc, inf_idem]
  · exact h.isFixedPt_iff.2 (hτσ.trans (h.isFixedPt_iff.1 hσ))
  · have hc : IsFixedPt f (σ ⊓ f ⊤) := hpers inf_le_right (hidem ⊤)
    exact le_antisymm (le_inf (hle σ) (hmono le_top)) (hc.eq.symm.trans_le (hmono inf_le_left))

/-- For additive updates the three notions of validity coincide. -/
theorem tfae_valid (hψs : ∀ ψ ∈ ψs, IsAdditive ψ) (hφ : IsAdditive φ) :
    [Valid₁ ψs φ, Valid₂ ψs φ, Valid₃ ψs φ].TFAE := by
  have hF := isAdditive_foldl hψs
  have hle : ∀ ψ ∈ ψs, ∀ σ, ψ σ ≤ σ := fun ψ hψ ↦ (hψs ψ hψ).le
  tfae_have 2 → 1 := Valid₂.valid₁
  tfae_have 1 → 2 := fun h σ ↦
    hφ.isFixedPt_iff.2 <| (hF σ).trans_le <| inf_le_right.trans (hφ.isFixedPt_iff.1 h)
  tfae_have 1 → 3 := fun h σ hσ ↦ hφ.isFixedPt_iff.2 <|
    (hF.isFixedPt_iff.1 ((isFixedPt_foldl_iff hle).2 hσ)).trans (hφ.isFixedPt_iff.1 h)
  tfae_have 3 → 1 := fun h ↦ h _ ((isFixedPt_foldl_iff hle).1 (hF.isFixedPt_iff.2 le_rfl))
  tfae_finish

end Additive

/-! ### Sets of possibilities -/

section CCP

variable {S : Type*} {u : CCP S}

/-- The static update with a content is additive. -/
theorem CCP.isAdditive_up (c : Set S) : IsAdditive (CCP.up c) := fun s ↦ by simp [CCP.up]

/-- On sets of possibilities the additive updates are the classical ones, eliminative and
distributive. -/
theorem CCP.isAdditive_iff_isClassical : IsAdditive u ↔ u.IsClassical := by
  rw [CCP.isClassical_iff_up_down_eq]
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ CCP.isAdditive_up _⟩
  rw [show u = CCP.up (u ⊤) from funext h, CCP.down_up]

/-- Dynamic entailment under a satisfaction relation is validity₂ of the induced updates. -/
theorem dynamicEntailsOf_iff_valid₂ {φ : Type*} (sat : S → φ → Prop) (ψ₁ ψ₂ : φ) :
    dynamicEntailsOf sat ψ₁ ψ₂ ↔ Valid₂ [CCP.updateFromSat sat ψ₁] (CCP.updateFromSat sat ψ₂) :=
  forall_congr' fun s ↦ support_iff_update_eq sat ψ₂ (CCP.updateFromSat sat ψ₁ s)

end CCP

end DynamicSemantics
