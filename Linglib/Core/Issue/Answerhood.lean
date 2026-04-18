import Linglib.Core.Issue.Basic

/-!
# Issue — mention-some / mention-all answerhood
@cite{ciardelli-groenendijk-roelofsen-2018} @cite{theiler-etal-2018}

The two basic answerhood predicates from the inquisitive-semantics
tradition. A **mention-all** answer settles every alternative; a
**mention-some** answer settles at least one without settling all. These
quantify over the alternatives `alt P` of an `Issue`; for the limit
case where alternatives don't exist
(@cite{ciardelli-groenendijk-roelofsen-2018} discusses this on infinite
worlds), both predicates degenerate to vacuous truth, which is the
intended classical convention.

For decidability sidecars (`Decidable (isMentionSomeAnswer P σ)`,
finset-view of `alt P` under finiteness), see future
`Core/Issue/Decidable.lean`.
-/

namespace Core

namespace Issue

universe u
variable {W : Type u}

/-- A state `σ` is a **mention-some** answer to `P`: it settles at least
    one alternative (`σ ⊆ p` for some `p ∈ alt P`) without settling all
    of them (some alternative is not contained in `σ`). -/
def isMentionSomeAnswer (P : Issue W) (σ : Set W) : Prop :=
  (∃ p ∈ alt P, σ ⊆ p) ∧ (∃ p ∈ alt P, ¬ σ ⊆ p)

/-- A state `σ` is a **mention-all** answer to `P`: it settles every
    alternative. -/
def isMentionAllAnswer (P : Issue W) (σ : Set W) : Prop :=
  ∀ p ∈ alt P, σ ⊆ p

/-- The only mention-all answer to `⊥` is the empty state. -/
@[simp] theorem isMentionAllAnswer_bot_iff {σ : Set W} :
    isMentionAllAnswer (⊥ : Issue W) σ ↔ σ = ∅ := by
  unfold isMentionAllAnswer
  simp only [alt_bot, Set.mem_singleton_iff, forall_eq, Set.subset_empty_iff]

/-- A mention-all answer to a declarative is precisely a substate of its
    informative content. -/
@[simp] theorem isMentionAllAnswer_declarative_iff {p σ : Set W} :
    isMentionAllAnswer (declarative p) σ ↔ σ ⊆ p := by
  unfold isMentionAllAnswer
  simp only [alt_declarative, Set.mem_singleton_iff, forall_eq]

end Issue

end Core
