import Linglib.Core.Question.Basic

/-!
# Question — mention-some / mention-all answerhood
@cite{ciardelli-groenendijk-roelofsen-2018} @cite{theiler-etal-2018}

The two basic answerhood predicates from the inquisitive-semantics
tradition. A **mention-all** answer settles every alternative; a
**mention-some** answer settles at least one without settling all. These
quantify over the alternatives `alt P` of an `Question`; for the limit
case where alternatives don't exist
(@cite{ciardelli-groenendijk-roelofsen-2018} discusses this on infinite
worlds), both predicates degenerate to vacuous truth, which is the
intended classical convention.

For decidability sidecars (`Decidable (isMentionSomeAnswer P σ)`,
finset-view of `alt P` under finiteness), see future
`Core/Question/Decidable.lean`.
-/

namespace Core

namespace Question

universe u
variable {W : Type u}

/-- A state `σ` is a **mention-some** answer to `P`: it settles at least
    one alternative (`σ ⊆ p` for some `p ∈ alt P`) without settling all
    of them (some alternative is not contained in `σ`). -/
def isMentionSomeAnswer (P : Question W) (σ : Set W) : Prop :=
  (∃ p ∈ alt P, σ ⊆ p) ∧ (∃ p ∈ alt P, ¬ σ ⊆ p)

/-- A state `σ` is a **mention-all** answer to `P`: it settles every
    alternative. -/
def isMentionAllAnswer (P : Question W) (σ : Set W) : Prop :=
  ∀ p ∈ alt P, σ ⊆ p

/-- The only mention-all answer to `⊥` is the empty state. -/
@[simp] theorem isMentionAllAnswer_bot_iff {σ : Set W} :
    isMentionAllAnswer (⊥ : Question W) σ ↔ σ = ∅ := by
  unfold isMentionAllAnswer
  simp only [alt_bot, Set.mem_singleton_iff, forall_eq, Set.subset_empty_iff]

/-- A mention-all answer to a declarative is precisely a substate of its
    informative content. -/
@[simp] theorem isMentionAllAnswer_declarative_iff {p σ : Set W} :
    isMentionAllAnswer (declarative p) σ ↔ σ ⊆ p := by
  unfold isMentionAllAnswer
  simp only [alt_declarative, Set.mem_singleton_iff, forall_eq]

/-! ### Partial answerhood (@cite{roberts-2012} Def. 3a) -/

/-- A state `σ` is a **partial answer** to `P`: it settles at least one
    alternative, either confirming it (`σ ⊆ p`) or ruling it out
    (`σ ⊆ pᶜ`).

    @cite{roberts-2012} Def. 3a: a partial answer contextually entails
    the evaluation — either true or false — of at least one element of
    `q-alt(q)`. The positive-only version misses negative partial
    answerhood, where `σ` rules out an alternative entirely. -/
def isPartialAnswer (P : Question W) (σ : Set W) : Prop :=
  ∃ p ∈ alt P, σ ⊆ p ∨ σ ⊆ pᶜ

/-- A move (an `Question` `R`) is **relevant** to `P` modulo a list of
    subquestions if some alternative of `R` is a partial answer to `P`
    or to one of the subquestions.

    @cite{roberts-2012} Def. 15 / @cite{ippolito-kiss-williams-2025}
    assumption iii (p. 225): "S is relevant to QUD if S is either a
    subquestion of QUD or an answer to a subquestion q of QUD." -/
def isMoveRelevant (R P : Question W) (subquestions : Set (Question W)) : Prop :=
  ∃ a ∈ alt R, isPartialAnswer P a ∨ ∃ Q ∈ subquestions, isPartialAnswer Q a

end Question

end Core
