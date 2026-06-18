import Linglib.Core.Logic.Orthologic
import Linglib.Core.Order.Orthoframe.Representation

/-!
# Frame semantics and completeness for orthologic

[holliday-mandelkern-2024] §4.1 — Goldblatt's compatibility-frame semantics for
orthologic and its completeness theorem (Theorem 4.19). A compatibility model is an
`Orthoframe` `F` with a valuation `V : Var → F.Reg` assigning each variable a regular
proposition. The support relation `s ⊩ φ` is defined recursively; the set of
supporters `{s | s ⊩ φ}` is exactly the extent of the algebraic value
`Formula.eval V φ` in the ortholattice `F.Reg` (`support_setOf_eq_extent`).

Soundness and completeness then reduce to the algebraic versions (Theorem 3.13): the
bridge turns frame consequence into the algebraic inequality in every frame algebra,
and the representation embedding (Theorem 4.13) places every ortholattice inside a
frame algebra via `represent`, so frame validity entails validity in all
ortholattices.

## Main results
* `Support`, `support_setOf_eq_extent` — the support relation and the bridge.
* `frame_sound`, `frame_complete`, `derivable_iff_frameConsequence` — Theorem 4.19.
-/

open Order Set Orthoframe

universe u

namespace Orthologic

variable {Var : Type u} {S : Type u}

/-! ### Support in a compatibility model -/

/-- The support relation `s ⊩ φ` of the compatibility model `(F, V)`
    ([holliday-mandelkern-2024] Def 4.16): `¬φ` is supported at `s` exactly when `s`
    is orthogonal to (incompatible with) every point supporting `φ`. -/
def Support (F : Orthoframe S) (V : Var → F.Reg) (s : S) : Formula Var → Prop
  | .top => True
  | .var p => s ∈ (V p).extent
  | .neg φ => ∀ t, Support F V t φ → F.ortho s t
  | .and φ ψ => Support F V s φ ∧ Support F V s ψ

/-- **The bridge**: the supporters of `φ` are exactly the extent of its algebraic
    value `Formula.eval V φ` in `F.Reg`. -/
theorem support_setOf_eq_extent (F : Orthoframe S) (V : Var → F.Reg) (φ : Formula Var) :
    {s | Support F V s φ} = (Formula.eval V φ).extent := by
  induction φ with
  | top =>
    ext s
    exact iff_of_true trivial (Set.mem_univ s)
  | var p => rfl
  | neg φ ih =>
    ext s
    simp only [Support, Set.mem_setOf_eq]
    rw [show Formula.eval V φ.neg = (Formula.eval V φ)ᶜ from rfl, Concept.extent_compl,
        ← Concept.upperPolar_extent, ← ih, mem_upperPolar_iff]
    constructor
    · intro h t ht; exact Std.Symm.symm _ _ (h t ht)
    · intro h t ht; exact Std.Symm.symm _ _ (h ht)
  | and φ ψ ihφ ihψ =>
    show {s | Support F V s φ ∧ Support F V s ψ}
        = (Formula.eval V φ ⊓ Formula.eval V ψ).extent
    rw [Concept.extent_inf, ← ihφ, ← ihψ]
    rfl

/-! ### Frame consequence, soundness, completeness -/

/-- Semantic consequence over compatibility frames ([holliday-mandelkern-2024]
    Def 4.18): in every model, every point supporting `φ` supports `ψ`. -/
def FrameConsequence (φ ψ : Formula Var) : Prop :=
  ∀ {S : Type u} (F : Orthoframe S) (V : Var → F.Reg) (s : S),
    Support F V s φ → Support F V s ψ

@[inherit_doc] scoped infix:50 " ⊨ᶠ " => FrameConsequence

/-- Frame consequence is the algebraic inequality holding in every frame algebra. -/
theorem frameConsequence_iff_eval {φ ψ : Formula Var} :
    (φ ⊨ᶠ ψ) ↔ ∀ {S : Type u} (F : Orthoframe S) (V : Var → F.Reg),
      Formula.eval V φ ≤ Formula.eval V ψ := by
  constructor
  · intro h S F V
    rw [← Concept.extent_subset_extent_iff, ← support_setOf_eq_extent F V φ,
        ← support_setOf_eq_extent F V ψ]
    exact fun s hs => h F V s hs
  · intro h S F V s hs
    have hsub := Concept.extent_subset_extent_iff.mpr (h F V)
    rw [← support_setOf_eq_extent F V φ, ← support_setOf_eq_extent F V ψ] at hsub
    exact hsub hs

/-- **Soundness over compatibility frames** ([holliday-mandelkern-2024] Thm 4.19). -/
theorem frame_sound {φ ψ : Formula Var} (h : φ ⊢ ψ) : φ ⊨ᶠ ψ :=
  frameConsequence_iff_eval.mpr fun _ V => sound h V

/-- `Formula.eval` commutes with the representation embedding `represent V₀`. -/
theorem eval_map {L : Type u} [OrthocomplementedLattice L] {V₀ : Set L}
    (hV : JoinDense V₀) (v : Var → L) (φ : Formula Var) :
    Formula.eval (fun p => represent V₀ (v p)) φ = represent V₀ (Formula.eval v φ) := by
  induction φ with
  | top => simp only [Formula.eval, represent_top hV]
  | var p => rfl
  | neg φ ih => simp only [Formula.eval, ih, represent_compl hV]
  | and φ ψ ihφ ihψ => simp only [Formula.eval, ihφ, ihψ, represent_inf hV]

/-- **Completeness over compatibility frames** ([holliday-mandelkern-2024] Thm 4.19):
    frame consequence implies derivability. Proved from algebraic completeness
    (Thm 3.13) by embedding every ortholattice into a frame algebra via `represent`
    over the join-dense `Set.univ` (Thm 4.13). -/
theorem frame_complete {φ ψ : Formula Var} (h : φ ⊨ᶠ ψ) : φ ⊢ ψ := by
  apply Orthologic.complete
  intro L _ v
  have hjd : JoinDense (Set.univ : Set L) := fun a => by
    have hset : {b : L | b ∈ Set.univ ∧ b ≤ a} = Set.Iic a := by ext b; simp
    rw [hset]; exact isLUB_Iic
  have hframe := frameConsequence_iff_eval.mp h (ofOrtholattice (Set.univ : Set L))
    fun p => represent Set.univ (v p)
  rw [eval_map hjd, eval_map hjd] at hframe
  exact (represent_le_iff hjd).mp hframe

/-- **Goldblatt's completeness theorem** ([holliday-mandelkern-2024] Theorem 4.19):
    `φ ⊢ ψ` iff `φ ⊨ᶠ ψ` — provability equals validity over all compatibility
    frames. -/
theorem derivable_iff_frameConsequence {φ ψ : Formula Var} :
    φ ⊢ ψ ↔ φ ⊨ᶠ ψ :=
  ⟨frame_sound, frame_complete⟩

end Orthologic
