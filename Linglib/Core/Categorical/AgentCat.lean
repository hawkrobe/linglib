import Mathlib.CategoryTheory.Category.Basic
import Linglib.Core.RationalAction

/-!
# Category of Rational Action Agents

Category of `RationalAction` agents (fixed `S`, `A` types) with
score-proportionality as morphisms.

If agent₂'s scores are `k` times agent₁'s scores (for `k > 0`), Luce
scale invariance (`RationalAction.scaleBy_policy`) guarantees identical
policies. This makes the category a groupoid: every morphism is invertible
(with inverse constant `1/k`).

The key downstream consumer is `RSA/Structural/ModelMorphism.lean`, where
proportional S1 scores imply identical L1 posteriors.
-/

namespace Core.Categorical

open Core

/-- Bundled rational action agent: an object in the agent category. -/
structure AgentObj (S : Type*) (A : Type*) [Fintype A] where
  /-- The underlying rational action agent. -/
  agent : RationalAction S A

variable {S : Type*} {A : Type*} [Fintype A]

/-- A morphism between agents: a score proportionality witness.

    `AgentMor ra₁ ra₂` asserts that ra₂'s scores are `k` times ra₁'s scores
    for some positive constant `k`. By Luce invariance, this guarantees that
    both agents have identical policies. -/
structure AgentMor (ra₁ ra₂ : AgentObj S A) where
  /-- The proportionality constant. -/
  k : ℝ
  /-- The constant is positive. -/
  k_pos : 0 < k
  /-- Scores are proportional: score₂(s,a) = k · score₁(s,a). -/
  proportional : ∀ s a, ra₂.agent.score s a = k * ra₁.agent.score s a

namespace AgentMor

@[ext]
theorem ext {ra₁ ra₂ : AgentObj S A} {m₁ m₂ : AgentMor ra₁ ra₂}
    (h : m₁.k = m₂.k) : m₁ = m₂ := by
  obtain ⟨k₁, _, _⟩ := m₁; obtain ⟨k₂, _, _⟩ := m₂; subst h; rfl

/-- Identity morphism: scores are `1 ×` themselves. -/
protected def id (ra : AgentObj S A) : AgentMor ra ra where
  k := 1
  k_pos := one_pos
  proportional _ _ := (one_mul _).symm

/-- Composition: if score₂ = k₁ · score₁ and score₃ = k₂ · score₂,
    then score₃ = (k₂ · k₁) · score₁. -/
protected def comp {ra₁ ra₂ ra₃ : AgentObj S A}
    (f : AgentMor ra₁ ra₂) (g : AgentMor ra₂ ra₃) : AgentMor ra₁ ra₃ where
  k := g.k * f.k
  k_pos := mul_pos g.k_pos f.k_pos
  proportional s a := by
    rw [g.proportional s a, f.proportional s a, mul_assoc]

/-- Inverse morphism: if score₂ = k · score₁, then score₁ = (1/k) · score₂. -/
protected noncomputable def inv {ra₁ ra₂ : AgentObj S A}
    (f : AgentMor ra₁ ra₂) : AgentMor ra₂ ra₁ where
  k := f.k⁻¹
  k_pos := inv_pos.mpr f.k_pos
  proportional s a := by
    have hk_ne : f.k ≠ 0 := ne_of_gt f.k_pos
    rw [f.proportional s a, inv_mul_cancel_left₀ hk_ne]

end AgentMor

instance : CategoryTheory.Category (AgentObj S A) where
  Hom := AgentMor
  id := AgentMor.id
  comp f g := AgentMor.comp f g
  id_comp f := AgentMor.ext (mul_one f.k)
  comp_id f := AgentMor.ext (one_mul f.k)
  assoc f g h := AgentMor.ext (mul_assoc h.k g.k f.k).symm

section PolicyPreservation

variable {ra₁ ra₂ : AgentObj S A}

/-- **Luce invariance**: a morphism preserves the policy.

    If scores are proportional, both agents assign the same probability
    to every action in every state. -/
theorem AgentMor.preserves_policy (m : AgentMor ra₁ ra₂) :
    ∀ s a, ra₁.agent.policy s a = ra₂.agent.policy s a :=
  fun s a => (RationalAction.policy_eq_of_proportional
    ra₁.agent ra₂.agent s m.k m.k_pos (m.proportional s) a).symm

/-- Composition of morphisms preserves policy preservation. -/
theorem AgentMor.comp_preserves_policy {ra₃ : AgentObj S A}
    (f : AgentMor ra₁ ra₂) (g : AgentMor ra₂ ra₃) :
    ∀ s a, ra₁.agent.policy s a = ra₃.agent.policy s a :=
  (AgentMor.comp f g).preserves_policy

end PolicyPreservation

end Core.Categorical
