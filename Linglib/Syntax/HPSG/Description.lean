import Linglib.Syntax.HPSG.Interpretation
import Mathlib.Data.Fintype.Basic

/-!
# RSRL descriptions
[richter-2000], [richter-2024]

The **description language** of RSRL — the formulae stating an HPSG grammar's principles (Def.
54; satisfaction Def. 58). Includes relational formulae and **component quantification** (∃/∀
over the components of the described entity), the features making RSRL richer than FOL. Chains
(list-valued relation arguments, Def. 49–50) are deferred.

`ex`/`all` are bounded by `IsComponentOf` (reachability by attributes), decidable on finite
models, so `∃`-worked examples reduce by `decide`. `Models` evaluates the (variable-free)
principles under the assignment `fun _ => u`.
-/

namespace HPSG.RSRL

universe u

/-- RSRL descriptions over `Term`s ([richter-2000], Def. 54): atomic sort-assignments and
path-equations, relational formulae, the classical connectives, and component quantification. -/
inductive Desc {Srt : Type u} [PartialOrder Srt] (Sig : Signature Srt) where
  /-- Sort assignment `τ ~ σ`: the entity at `t` has a sort at least as specific as `σ`. -/
  | sortAssign (t : Term Sig) (σ : Srt)
  /-- Path equation `τ₁ ≈ τ₂`: the entities at `t₁` and `t₂` are token-identical. -/
  | pathEq (t₁ t₂ : Term Sig)
  /-- Relational formula `ρ(t₁,…,tₙ)`: the tuple of denoted terms stands in relation `ρ`. -/
  | rel (ρ : Sig.Rel) (ts : List (Term Sig))
  /-- Negation. -/
  | neg (d : Desc Sig)
  /-- Conjunction. -/
  | and (d e : Desc Sig)
  /-- Disjunction. -/
  | or (d e : Desc Sig)
  /-- Implication (classical; vacuously satisfied where the antecedent fails). -/
  | imp (d e : Desc Sig)
  /-- Existential component quantification: some component of the described entity. -/
  | ex (v : Nat) (d : Desc Sig)
  /-- Universal component quantification: every component of the described entity. -/
  | all (v : Nat) (d : Desc Sig)

namespace Interpretation

variable {Srt : Type u} [PartialOrder Srt] {Sig : Signature Srt}

/-- Satisfaction under a variable assignment ([richter-2000], Def. 58). `ex`/`all`
quantify over the **components** of `u` (`IsComponentOf`), RSRL's bounded quantification. An
undefined term makes an atomic description false. -/
def satisfies (I : Interpretation Sig) (ass : Nat → I.U) (u : I.U) : Desc Sig → Prop
  | .sortAssign t σ => match I.termDenot ass t u with
      | some v => I.S v ≤ σ
      | none => False
  | .pathEq t₁ t₂ => match I.termDenot ass t₁ u, I.termDenot ass t₂ u with
      | some a, some b => a = b
      | _, _ => False
  | .rel ρ ts => match ts.mapM (fun t => I.termDenot ass t u) with
      | some args => I.R ρ args
      | none => False
  | .neg d => ¬ I.satisfies ass u d
  | .and d e => I.satisfies ass u d ∧ I.satisfies ass u e
  | .or d e => I.satisfies ass u d ∨ I.satisfies ass u e
  | .imp d e => I.satisfies ass u d → I.satisfies ass u e
  | .ex v d => ∃ w, I.IsComponentOf u w ∧ I.satisfies (Function.update ass v w) u d
  | .all v d => ∀ w, I.IsComponentOf u w → I.satisfies (Function.update ass v w) u d

instance decSatisfies (I : Interpretation Sig) [Fintype I.U] [DecidableEq I.U] [DecidableLE Srt]
    [Fintype Sig.Attr] [∀ ρ, DecidablePred (I.R ρ)] (ass : Nat → I.U) (u : I.U) :
    (d : Desc Sig) → Decidable (I.satisfies ass u d)
  | .sortAssign t σ => by unfold satisfies; split <;> infer_instance
  | .pathEq t₁ t₂ => by unfold satisfies; split <;> infer_instance
  | .rel ρ ts => by unfold satisfies; split <;> infer_instance
  | .neg d => by unfold satisfies; haveI := decSatisfies I ass u d; infer_instance
  | .and d e => by
      unfold satisfies; haveI := decSatisfies I ass u d; haveI := decSatisfies I ass u e
      infer_instance
  | .or d e => by
      unfold satisfies; haveI := decSatisfies I ass u d; haveI := decSatisfies I ass u e
      infer_instance
  | .imp d e => by
      unfold satisfies; haveI := decSatisfies I ass u d; haveI := decSatisfies I ass u e
      infer_instance
  | .ex v d => by
      unfold satisfies
      haveI : ∀ w, Decidable (I.satisfies (Function.update ass v w) u d) :=
        fun w => decSatisfies I (Function.update ass v w) u d
      infer_instance
  | .all v d => by
      unfold satisfies
      haveI : ∀ w, Decidable (I.satisfies (Function.update ass v w) u d) :=
        fun w => decSatisfies I (Function.update ass v w) u d
      infer_instance

end Interpretation

/-- A **grammar** is a signature together with a set (here `List`) of descriptions, its
principles ([richter-2000]). -/
abbrev Grammar {Srt : Type u} [PartialOrder Srt] (Sig : Signature Srt) := List (Desc Sig)

namespace Interpretation

variable {Srt : Type u} [PartialOrder Srt] {Sig : Signature Srt}

/-- An interpretation is a **model** of a grammar iff every principle holds of every entity in
all its components ([richter-2000]). Principles are variable-free, so they are evaluated
under any assignment (here `fun _ => u`). -/
def Models (I : Interpretation Sig) (G : Grammar Sig) : Prop :=
  ∀ u : I.U, ∀ d ∈ G, I.satisfies (fun _ => u) u d

instance (I : Interpretation Sig) [Fintype I.U] [DecidableEq I.U] [DecidableLE Srt]
    [Fintype Sig.Attr] [∀ ρ, DecidablePred (I.R ρ)] (G : Grammar Sig) :
    Decidable (I.Models G) := by unfold Models; infer_instance

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
