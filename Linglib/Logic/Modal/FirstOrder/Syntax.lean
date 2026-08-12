import Mathlib.ModelTheory.Syntax

/-!
# The quantified modal language

`ModalFormula L α`: modal formulas over `L` with named free variables `α`,
in mathlib's `BoundedFormula` basis — atomic `equal`/`rel`, `falsum`,
`imp` — plus `□` and named universal quantification, with `∼`, `⊤`, `⊓`,
`⊔`, `ex`, and `diamond` derived exactly as for `BoundedFormula`.
`[UPSTREAM]` candidate for `Mathlib/ModelTheory`.
-/

namespace FirstOrder.Language

variable {L : Language} {α : Type*}

/-- Modal formulas over `L` with named free variables `α`: mathlib's
    `BoundedFormula` basis — atomic `equal`/`rel`, `falsum`, `imp` — plus
    `□` and named quantification; `∼`, `⊤`, `⊓`, `⊔`, `ex`, and `diamond` are
    derived exactly as for `BoundedFormula`. -/
inductive ModalFormula (L : Language) (α : Type*) where
  /-- The proposition that two terms are equal. -/
  | equal (t₁ t₂ : L.Term α) : ModalFormula L α
  /-- A relation symbol applied to terms. -/
  | rel {n : ℕ} (R : L.Relations n) (ts : Fin n → L.Term α) : ModalFormula L α
  /-- The contradiction. -/
  | falsum : ModalFormula L α
  /-- Implication. -/
  | imp (φ ψ : ModalFormula L α) : ModalFormula L α
  /-- Necessity. -/
  | box (φ : ModalFormula L α) : ModalFormula L α
  /-- Universal quantification of a named variable. -/
  | all (x : α) (φ : ModalFormula L α) : ModalFormula L α

namespace ModalFormula

instance : Inhabited (ModalFormula L α) := ⟨falsum⟩

instance : Bot (ModalFormula L α) := ⟨falsum⟩

/-- The negation of a modal formula. -/
@[match_pattern]
protected def not (φ : ModalFormula L α) : ModalFormula L α := φ.imp ⊥

instance : Top (ModalFormula L α) := ⟨ModalFormula.not ⊥⟩

instance : Min (ModalFormula L α) := ⟨fun φ ψ => (φ.imp ψ.not).not⟩

instance : Max (ModalFormula L α) := ⟨fun φ ψ => φ.not.imp ψ⟩

/-- Existential quantification of a named variable, derived: `∃x := ∼∀x∼`. -/
@[match_pattern]
protected def ex (x : α) (φ : ModalFormula L α) : ModalFormula L α :=
  (all x φ.not).not

/-- Possibility, derived: `◇φ := ∼□∼φ` — to `box` what `ex` is to `all`. -/
@[match_pattern]
def diamond (φ : ModalFormula L α) : ModalFormula L α := (box φ.not).not

end ModalFormula

/-- Applies a relation symbol to terms as a modal formula. -/
abbrev Relations.modalFormula {n : ℕ} (R : L.Relations n)
    (ts : Fin n → L.Term α) : ModalFormula L α :=
  ModalFormula.rel R ts

/-- Applies a unary relation symbol to a term as a modal formula. -/
abbrev Relations.modalFormula₁ (R : L.Relations 1) (t : L.Term α) :
    ModalFormula L α :=
  ModalFormula.rel R ![t]

end FirstOrder.Language
