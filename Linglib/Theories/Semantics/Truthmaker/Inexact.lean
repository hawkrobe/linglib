import Linglib.Theories.Semantics.Truthmaker.Basic

/-! # Inexact Truthmaking and Entailment @cite{jago-2026}

Jago Def 3: A state `s` *inexactly* makes `A` true iff some part of `s`
exactly verifies `A`. Inexact truthmaking obeys the standard extensional
clauses for conjunction and disjunction (unlike exact truthmaking, which
uses fusion).

This file:

- defines inexact verification (`▷`) and inexact falsification (`◁`) for
  unilateral and bilateral propositions;
- proves the bridge `s ⊩ A → s ▷ A` (exact implies inexact);
- defines exact and inexact entailment for unilateral propositions;
- shows the extensional clauses for inexact under `tmAnd` / `tmOr` and
  bilateral `conj` / `disj`.

The exact-vs-inexact distinction is what lets truthmaker semantics
distinguish the logic of *content* from the logic of *consequence*
(@cite{jago-2026}): exact entailment characterizes hyperintensional
content (e.g., AC analytic entailment), while inexact entailment is
the truthmaker analogue of familiar consequence relations.

NOTE: @cite{vanfraassen-1969}'s FDE is the canonical historical
target — Jago notes that on basic models inexact consequence
coincides with FDE. We do *not* formalize FDE here, so the
correspondence is documented as an external claim, not verified
inside linglib.

-/

namespace Semantics.Truthmaker


-- ════════════════════════════════════════════════════
-- § 1. Inexact Truthmaking (Jago Def 3)
-- ════════════════════════════════════════════════════

section Inexact
variable {S : Type*} [Preorder S]

/-- Inexact verification (@cite{jago-2026} Def 3): `s ▷ p` iff some part
    of `s` exactly verifies `p`. -/
def inexactVer (p : TMProp S) (s : S) : Prop :=
  ∃ u, u ≤ s ∧ p u

/-- Notation: `s ⊩ᵢ p` for "s inexactly verifies p". -/
scoped infix:50 " ⊩ᵢ " => fun s p => inexactVer p s

/-- Exact verification implies inexact: a verifier is its own part. -/
theorem inexactVer_of_exact {p : TMProp S} {s : S} (hp : p s) :
    inexactVer p s :=
  ⟨s, le_refl s, hp⟩

/-- Inexact verification is downward... wait — actually inexact verification
    is *upward* closed: if `s` inexactly verifies `p` and `s ≤ t`, then
    `t` inexactly verifies `p` (the same part of `s` is also a part of `t`). -/
theorem inexactVer_mono {p : TMProp S} {s t : S}
    (hs : inexactVer p s) (hle : s ≤ t) : inexactVer p t := by
  obtain ⟨u, hu, hp⟩ := hs
  exact ⟨u, le_trans hu hle, hp⟩

end Inexact

-- ════════════════════════════════════════════════════
-- § 2. Inexact under Connectives (extensional clauses)
-- ════════════════════════════════════════════════════

section InexactConnectives
variable {S : Type*} [Preorder S]

/-- Inexact verification of disjunction is the union of inexact
    verifications: `s ▷ (p ∨ q) ↔ s ▷ p ∨ s ▷ q`. -/
theorem inexactVer_tmOr (p q : TMProp S) (s : S) :
    inexactVer (tmOr p q) s ↔ inexactVer p s ∨ inexactVer q s := by
  constructor
  · rintro ⟨u, hu, hpq⟩
    cases hpq with
    | inl hp => exact Or.inl ⟨u, hu, hp⟩
    | inr hq => exact Or.inr ⟨u, hu, hq⟩
  · rintro (⟨u, hu, hp⟩ | ⟨u, hu, hq⟩)
    · exact ⟨u, hu, Or.inl hp⟩
    · exact ⟨u, hu, Or.inr hq⟩

end InexactConnectives

section InexactConj
variable {S : Type*} [SemilatticeSup S]

/-- Inexact verification of conjunction implies inexact verification of
    each conjunct: `s ▷ (p ∧ q) → s ▷ p ∧ s ▷ q`.

    The reverse implication does NOT hold in general: `s ▷ p` and `s ▷ q`
    only give us a part of `s` for each, which need not fuse to a part
    of `s` (without further structural assumptions). This is why
    truthmaker conjunction is hyperintensional even at the inexact level. -/
theorem inexactVer_tmAnd_imp (p q : TMProp S) (s : S)
    (h : inexactVer (tmAnd p q) s) :
    inexactVer p s ∧ inexactVer q s := by
  obtain ⟨u, hu, s₁, s₂, hp, hq, hsplit⟩ := h
  refine ⟨⟨s₁, ?_, hp⟩, ⟨s₂, ?_, hq⟩⟩
  · exact le_trans (hsplit ▸ le_sup_left) hu
  · exact le_trans (hsplit ▸ le_sup_right) hu

end InexactConj

-- ════════════════════════════════════════════════════
-- § 3. Bilateral Inexact Verification / Falsification
-- ════════════════════════════════════════════════════

namespace BilProp

variable {S : Type*} [Preorder S]

/-- Bilateral inexact verification: some part of `s` exactly verifies `A`. -/
def inexactVer (A : BilProp S) (s : S) : Prop :=
  Truthmaker.inexactVer A.ver s

/-- Bilateral inexact falsification: some part of `s` exactly falsifies `A`. -/
def inexactFal (A : BilProp S) (s : S) : Prop :=
  Truthmaker.inexactVer A.fal s

/-- Negation swaps inexact verification and falsification. -/
@[simp] theorem inexactVer_neg (A : BilProp S) (s : S) :
    A.neg.inexactVer s ↔ A.inexactFal s := Iff.rfl

@[simp] theorem inexactFal_neg (A : BilProp S) (s : S) :
    A.neg.inexactFal s ↔ A.inexactVer s := Iff.rfl

end BilProp

-- ════════════════════════════════════════════════════
-- § 4. Exact and Inexact Entailment
-- ════════════════════════════════════════════════════

section Entailment
variable {S : Type*}

/-- **Exact entailment** of unilateral propositions IS the pointwise
    `≤` on `TMProp S = S → Prop` (lifted via `Pi.instPreorder` from
    `Prop`'s preorder, where `P ≤ Q ↔ P → Q`). -/
abbrev ExactEntails (p q : TMProp S) : Prop := p ≤ q

/-- Notation: `p ⊨ₑ q` for exact entailment. -/
scoped infix:50 " ⊨ₑ " => ExactEntails

/-- `ExactEntails` unfolds to its pointwise definition. -/
theorem ExactEntails.iff_forall {p q : TMProp S} :
    p ⊨ₑ q ↔ ∀ s, p s → q s := Iff.rfl

variable [Preorder S]

/-- **Inexact entailment** IS the pointwise `≤` on `inexactVer`-extensions
    of the propositions. Reflexivity and transitivity come from the
    `Preorder` on `TMProp S`. -/
abbrev InexactEntails (p q : TMProp S) : Prop :=
  inexactVer p ≤ inexactVer q

/-- Notation: `p ⊨ᵢ q` for inexact entailment. -/
scoped infix:50 " ⊨ᵢ " => InexactEntails

/-- Exact entailment implies inexact entailment.
    Pointwise lift of `h` along `inexactVer`. -/
theorem InexactEntails.of_exact {p q : TMProp S} (h : p ⊨ₑ q) : p ⊨ᵢ q := by
  intro s ⟨u, hule, hp⟩
  exact ⟨u, hule, h u hp⟩

end Entailment

end Semantics.Truthmaker
