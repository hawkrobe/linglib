import Linglib.Syntax.HPSG.Interpretation
import Mathlib.Data.Fintype.Basic

/-!
# RSRL descriptions
@cite{richter-2000}, @cite{richter-2024}

A native Lean rendering of the **description language** of RSRL — the formulae that state the
principles of an HPSG grammar (@cite{richter-2000}, Def. 54; satisfaction is Def. 58;
@cite{richter-2024}, Ch. 3 §2). This now includes **relational formulae** and **component
quantification** (∃/∀ over the components of the described entity), the features that make RSRL
strictly richer than first-order logic. Chains (list-valued *relation arguments*, Def. 49–50)
remain deferred.

## Main declarations

* `HPSG.RSRL.Desc` — descriptions over `Term`s (with variables): `sortAssign` (`τ ~ σ`),
  `pathEq` (`τ₁ ≈ τ₂`, token identity), `rel` (relational formula `ρ(τ₁,…)`), `neg`/`and`/
  `or`/`imp`, and `ex`/`all` (component quantification).
* `HPSG.RSRL.Interpretation.satisfies` — satisfaction under a variable assignment
  (@cite{richter-2000}, Def. 58). `ex`/`all` quantify over `IsComponentOf u` — RSRL's bounded
  (component) quantification, *not* the whole universe. Decidable on finite models.
* `HPSG.RSRL.Grammar` / `Interpretation.Models` — a grammar's principles; a model satisfies
  every (variable-free) principle of every entity.

## Implementation notes

* `ex`/`all` are **component-bounded** (`I.IsComponentOf u w`, i.e. `w` reachable from `u` by
  attributes). On finite models this is decidable (`Interpretation.lean`), so `∃`-quantified
  worked examples reduce by `decide`. Universal component quantification (`all`) is decidable
  too, but `decide` on it can be kernel-heavy; such principles are better checked structurally.
* `Models` evaluates principles under the assignment `fun _ => u`; grammar descriptions are
  variable-free (Def. 54), so the choice of assignment is irrelevant.
-/

namespace HPSG.RSRL

universe u

/-- RSRL descriptions over `Term`s (@cite{richter-2000}, Def. 54): atomic sort-assignments and
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

/-- Satisfaction under a variable assignment (@cite{richter-2000}, Def. 58). `ex`/`all`
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
principles (@cite{richter-2000}). -/
abbrev Grammar {Srt : Type u} [PartialOrder Srt] (Sig : Signature Srt) := List (Desc Sig)

namespace Interpretation

variable {Srt : Type u} [PartialOrder Srt] {Sig : Signature Srt}

/-- An interpretation is a **model** of a grammar iff every principle holds of every entity in
all its components (@cite{richter-2000}). Principles are variable-free, so they are evaluated
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
