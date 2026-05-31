import Linglib.Syntax.HPSG.Interpretation
import Mathlib.Data.Fintype.Basic

/-!
# RSRL descriptions
@cite{richter-2000}, @cite{richter-2024}

A native Lean rendering of the **description language** of RSRL — the formulae that state the
principles of an HPSG grammar (@cite{richter-2000}, Def. 54; satisfaction is Def. 58;
@cite{richter-2024}, Ch. 3 §2). This is the *relation-free, quantifier-free fragment*: sort
assignments and path equations closed under the classical connectives. Relational formulae,
component quantification, and chains (which make RSRL strictly richer than first-order logic)
are deferred.

## Main declarations

* `HPSG.RSRL.Desc` — descriptions: `sortAssign` (`τ ~ σ`), `pathEq` (`τ₁ ≈ τ₂`, token
  identity), and `neg`/`and`/`or`/`imp`.
* `HPSG.RSRL.Interpretation.satisfies` — the description-denotation: when a description is true
  of an entity `u` in an interpretation (@cite{richter-2000}, Def. 58; `Desc` syntax is
  Def. 54). Decidable on finite models, so worked examples reduce by `decide`.
* `HPSG.RSRL.Grammar` / `Interpretation.Models` — a grammar is a set (here `List`) of
  descriptions; an interpretation is a model iff every description holds of every entity.

## Implementation notes

* `pathEq` is **token identity** (@cite{richter-2024}, Ch. 3): two paths are equated iff both
  are defined and denote the *same* entity — reentrancy is ordinary `=` in the model.
* A grammar is a `List Desc` rather than `Set Desc` so that `Models` is decidable; the intended
  reading is still set-like (order and duplication are irrelevant).
-/

namespace HPSG.RSRL

universe u

/-- RSRL descriptions, relation-free quantifier-free fragment (@cite{richter-2000}, Def. 54). -/
inductive Desc {Srt : Type u} [PartialOrder Srt] (Sig : Signature Srt) where
  /-- Sort assignment `τ ~ σ`: the entity at path `p` has a sort at least as specific as `σ`. -/
  | sortAssign (p : Path Sig) (σ : Srt)
  /-- Path equation `τ₁ ≈ τ₂`: the entities at paths `p` and `q` are token-identical. -/
  | pathEq (p q : Path Sig)
  /-- Negation. -/
  | neg (d : Desc Sig)
  /-- Conjunction. -/
  | and (d e : Desc Sig)
  /-- Disjunction. -/
  | or (d e : Desc Sig)
  /-- Implication (classical; a non-antecedent entity satisfies it vacuously). -/
  | imp (d e : Desc Sig)

namespace Interpretation

variable {Srt : Type u} [PartialOrder Srt] {Sig : Signature Srt}

/-- When a description is true of entity `u` in interpretation `I` (@cite{richter-2000},
Def. 58). A path that is undefined makes an atomic description false. -/
def satisfies (I : Interpretation Sig) (u : I.U) : Desc Sig → Prop
  | .sortAssign p σ => match I.denot p u with
      | some v => I.S v ≤ σ
      | none => False
  | .pathEq p q => match I.denot p u, I.denot q u with
      | some a, some b => a = b
      | _, _ => False
  | .neg d => ¬ I.satisfies u d
  | .and d e => I.satisfies u d ∧ I.satisfies u e
  | .or d e => I.satisfies u d ∨ I.satisfies u e
  | .imp d e => I.satisfies u d → I.satisfies u e

instance decSatisfies (I : Interpretation Sig) [DecidableEq I.U] [DecidableLE Srt] (u : I.U) :
    (d : Desc Sig) → Decidable (I.satisfies u d)
  | .sortAssign p σ => by unfold satisfies; split <;> infer_instance
  | .pathEq p q => by unfold satisfies; split <;> infer_instance
  | .neg d => by unfold satisfies; haveI := decSatisfies I u d; infer_instance
  | .and d e => by
      unfold satisfies; haveI := decSatisfies I u d; haveI := decSatisfies I u e; infer_instance
  | .or d e => by
      unfold satisfies; haveI := decSatisfies I u d; haveI := decSatisfies I u e; infer_instance
  | .imp d e => by
      unfold satisfies; haveI := decSatisfies I u d; haveI := decSatisfies I u e; infer_instance

end Interpretation

/-- A **grammar** is a signature together with a set (here `List`) of descriptions, its
principles (@cite{richter-2000}). The signature is implicit in the `Desc`s' type. -/
abbrev Grammar {Srt : Type u} [PartialOrder Srt] (Sig : Signature Srt) := List (Desc Sig)

namespace Interpretation

variable {Srt : Type u} [PartialOrder Srt] {Sig : Signature Srt}

/-- An interpretation is a **model** of a grammar iff every principle holds of every entity in
all its components (@cite{richter-2000}; @cite{richter-2024}, Ch. 3: component-wise). -/
def Models (I : Interpretation Sig) (G : Grammar Sig) : Prop :=
  ∀ u : I.U, ∀ d ∈ G, I.satisfies u d

instance (I : Interpretation Sig) [Fintype I.U] [DecidableEq I.U] [DecidableLE Srt]
    (G : Grammar Sig) : Decidable (I.Models G) := by unfold Models; infer_instance

end Interpretation

/-- `IsSpecies` (i.e. `IsMin`) is decidable on a finite sort hierarchy. -/
instance instDecidableIsSpecies {Srt : Type u} [PartialOrder Srt] [Fintype Srt] [DecidableLE Srt]
    (σ : Srt) : Decidable (IsSpecies σ) :=
  inferInstanceAs (Decidable (∀ b, b ≤ σ → σ ≤ b))

/-- `WellTyped` is decidable on a finite interpretation. -/
instance instDecidableWellTyped {Srt : Type u} [PartialOrder Srt] [Fintype Srt] [DecidableLE Srt]
    {Sig : Signature Srt} (I : Interpretation Sig)
    [Fintype I.U] [DecidableEq I.U] [Fintype Sig.Attr] : Decidable I.WellTyped :=
  decidable_of_iff
    ((∀ u, IsSpecies (I.S u)) ∧
      (∀ (α : Sig.Attr) (u : I.U), (I.A α u).isSome = (Sig.approp (I.S u) α).isSome) ∧
      (∀ (α : Sig.Attr) (u v : I.U), I.A α u = some v → ∀ τ ∈ Sig.approp (I.S u) α, I.S v ≤ τ))
    ⟨fun ⟨a, b, c⟩ => ⟨a, b, c⟩, fun ⟨a, b, c⟩ => ⟨a, b, c⟩⟩

end HPSG.RSRL
