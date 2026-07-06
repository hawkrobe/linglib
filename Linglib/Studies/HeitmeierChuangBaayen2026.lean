import Linglib.Processing.Lexical.Discriminative.Coding
import Linglib.Processing.Lexical.Discriminative.Training
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Heitmeier, Chuang & Baayen (2026): linearity and regularity
[heitmeier-chuang-baayen-2026]

The relation between morphological regularity and linearity of the
form-meaning mapping (§16.6, Table 16.2), for paradigms with **imputed
additive semantics** — word meaning as stem vector plus exponent vector, the
book's regularisation of embeddings for "truly regular" systems.

* Linear maps satisfy **proportional analogy** by construction
  (`isAnalogicallyRegular_comp`): an exponent's form shift is
  stem-independent. Hence a table violating analogy (suppletion) has no
  linear interpolant over additive semantics
  (`not_exists_linear_of_not_regular`) — irregulars survive in a linear
  system only through word-specific, non-additive semantic vectors, which is
  how the book's linear models fit English past tense and Maltese plurals.
* When stem and exponent vectors are jointly independent the converse holds
  (`exists_linear_iff_isAnalogicallyRegular`): linear realisability *is*
  analogical regularity.
* Under ERM training on the paradigm (`paradigmExperience`), an irregular
  table forces positive loss for every linear map
  (`pos_weightedLoss_of_not_regular`).
-/

namespace HeitmeierChuangBaayen2026

open Processing.Lexical.Discriminative

variable {d n : ℕ} {Stem Cell : Type*}

/-- A paradigm's form table satisfies **proportional analogy** if the form
    contrast between two cells is the same for every stem
    (*cat : cats :: dog : dogs*). -/
def IsAnalogicallyRegular (f : Stem → Cell → FormVec n) : Prop :=
  ∀ st st' c c', f st c - f st c' = f st' c - f st' c'

variable (σ : Stem → MeaningVec d) (ε : Cell → MeaningVec d)

/-- Under additive semantics, the form shift a linear map assigns to an
    exponent is stem-independent. -/
theorem map_add_sub_map (G : MeaningVec d →ₗ[ℝ] FormVec n) (st : Stem)
    (c : Cell) : G (σ st + ε c) - G (σ st) = G (ε c) := by
  rw [map_add]
  abel

/-- Every linear map's paradigm table over additive semantics is
    analogically regular. -/
theorem isAnalogicallyRegular_comp (G : MeaningVec d →ₗ[ℝ] FormVec n) :
    IsAnalogicallyRegular fun st c => G (σ st + ε c) := fun st st' c c' => by
  simp only [map_add]
  abel

/-- A table violating proportional analogy has no linear interpolant over
    additive semantics. -/
theorem not_exists_linear_of_not_regular {f : Stem → Cell → FormVec n}
    (hf : ¬ IsAnalogicallyRegular f) :
    ¬ ∃ G : MeaningVec d →ₗ[ℝ] FormVec n, ∀ st c, G (σ st + ε c) = f st c := by
  rintro ⟨G, hG⟩
  exact hf (by simpa only [hG] using isAnalogicallyRegular_comp σ ε G)

/-- When stem and exponent vectors are jointly linearly independent, a
    paradigm table is linearly realisable **iff** it is analogically
    regular — over imputed additive semantics, linearity and regularity are
    the same constraint. -/
theorem exists_linear_iff_isAnalogicallyRegular [Nonempty Stem]
    [Nonempty Cell] (hind : LinearIndependent ℝ (Sum.elim σ ε))
    (f : Stem → Cell → FormVec n) :
    (∃ G : MeaningVec d →ₗ[ℝ] FormVec n, ∀ st c, G (σ st + ε c) = f st c)
      ↔ IsAnalogicallyRegular f := by
  constructor
  · rintro ⟨G, hG⟩
    simpa only [hG] using isAnalogicallyRegular_comp σ ε G
  · intro hreg
    obtain ⟨st₀⟩ := ‹Nonempty Stem›
    obtain ⟨c₀⟩ := ‹Nonempty Cell›
    obtain ⟨G, hG⟩ := LinearMap.exists_extend ((Module.Basis.span hind).constr ℝ
      (Sum.elim (fun st => f st c₀) fun c => f st₀ c - f st₀ c₀))
    have hb : ∀ x : Stem ⊕ Cell, G (Sum.elim σ ε x)
        = Sum.elim (fun st => f st c₀) (fun c => f st₀ c - f st₀ c₀) x := by
      intro x
      have h1 := LinearMap.congr_fun hG (Module.Basis.span hind x)
      rwa [LinearMap.comp_apply, Submodule.subtype_apply, Module.Basis.constr_basis,
           Module.Basis.span_apply] at h1
    refine ⟨G, fun st c => ?_⟩
    have hσ : G (σ st) = f st c₀ := hb (Sum.inl st)
    have hε : G (ε c) = f st₀ c - f st₀ c₀ := hb (Sum.inr c)
    rw [map_add, hσ, hε, ← hreg st st₀ c c₀]
    abel

/-- Proportional analogy is the vanishing of second differences — the same
    equation as the XOR obstruction of linear separability (§16.6's
    hub-and-neighbour classification example): a table realising XOR on a
    coordinate, `f ⊤ ⊤ = f ⊥ ⊥ ≠ f ⊤ ⊥ = f ⊥ ⊤`, violates analogy, so no
    linear map over additive semantics produces it. Analogy, linear
    separability, and absence of interaction terms are one constraint. -/
theorem not_isAnalogicallyRegular_of_xor {f : Bool → Bool → FormVec n}
    (hxor : f true true = f false false ∧ f true false = f false true)
    (hne : f true true ≠ f true false) :
    ¬ IsAnalogicallyRegular f := fun hreg => by
  have h := hreg true false true false
  rw [hxor.1, hxor.2] at h
  have h0 : f false false = f false true := by
    funext j
    have hj := congrFun h j
    simp only [Pi.sub_apply] at hj
    linarith
  exact hne ((hxor.1.trans h0).trans hxor.2.symm)

/-! ### The coding interface

The stem-exponent setting is the two-primitive case of the DLM coding
interface: a paradigm cell's primitives are its stem and cell tags, and
`embedSem` over `Sum.elim σ ε` is the imputed additive semantics. The
fourth proportional above is `embedSem_analogy` at the multiset relation
`{st, c} + {st', c'} = {st, c'} + {st', c}`. -/

instance : SemDecomposable (Stem × Cell) (Stem ⊕ Cell) :=
  ⟨fun p => {Sum.inl p.1, Sum.inr p.2}⟩

@[simp] theorem prims_pair (st : Stem) (c : Cell) :
    SemDecomposable.prims (Prim := Stem ⊕ Cell) (st, c)
      = {Sum.inl st, Sum.inr c} := rfl

theorem embedSem_sumElim (st : Stem) (c : Cell) :
    embedSem (Sum.elim σ ε) (st, c) = σ st + ε c := by
  simp [embedSem]

variable [Fintype Stem] [Fintype Cell]

/-- The paradigm as a training experience: imputed additive semantics as the
    meanings, the form table as the targets. -/
noncomputable def paradigmExperience (f : Stem → Cell → FormVec n) :
    TrainingExperience (Fintype.card (Stem × Cell)) n d where
  meanings i := σ ((Fintype.equivFin (Stem × Cell)).symm i).1
      + ε ((Fintype.equivFin (Stem × Cell)).symm i).2
  forms i := f ((Fintype.equivFin (Stem × Cell)).symm i).1
      ((Fintype.equivFin (Stem × Cell)).symm i).2

/-- Irregularity forces positive training loss: no linear map fits a
    suppletive paradigm exactly, so every ERM solution carries residual
    error — Table 16.2's irregular-linear cell runs on word-specific
    semantics, not on additive imputation. -/
theorem pos_weightedLoss_of_not_regular {f : Stem → Cell → FormVec n}
    (hf : ¬ IsAnalogicallyRegular f)
    {q : FrequencyVector (Fintype.card (Stem × Cell))} (hq : ∀ i, 0 < q i)
    (G : MeaningVec d →ₗ[ℝ] FormVec n) :
    0 < weightedLoss (paradigmExperience σ ε f) q G := by
  refine lt_of_le_of_ne
    (weightedLoss_nonneg _ _ _ fun i => (hq i).le) (Ne.symm fun h0 => ?_)
  have hint := (weightedLoss_eq_zero_iff _ _ _ hq).1 h0
  refine not_exists_linear_of_not_regular σ ε hf ⟨G, fun st c => ?_⟩
  have h := hint ((Fintype.equivFin (Stem × Cell)) (st, c))
  simpa [paradigmExperience] using h

end HeitmeierChuangBaayen2026
