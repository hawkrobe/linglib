import Linglib.Theories.Discourse.Centering.Transition

/-!
# Centering Theory — Rules 1 and 2
@cite{grosz-joshi-weinstein-1995} §3

The two normative rules of Centering Theory:

* **Rule 1** (pronominalization constraint): if any element of `Cf(U_n)`
  is realized by a pronoun in `U_{n+1}`, then `Cb(U_{n+1})` is realized
  by a pronoun also.

* **Rule 2** (transition preference): a *pair* of transitions is
  preferred over another when its constituent transitions have higher
  rank. The paper specifies the canonical case (CONT-CONT > RET-RET >
  SHIFT-SHIFT); the general pair preference uses sum-of-ranks.

Rule 1 takes the current utterance as a generic `[Realizes U E]
[Pronominalizes U E]` so it works on either `Utterance E R` or a
`DRSExpr` (via the DRT bridge).
-/

set_option autoImplicit false

namespace Discourse.Centering

variable {E R : Type}

-- ════════════════════════════════════════════════════
-- § 1. Rule 1
-- ════════════════════════════════════════════════════

/-- @cite{grosz-joshi-weinstein-1995} **Rule 1**: if any element of
    `Cf(U_n)` is realized by a pronoun in `U_{n+1}`, then `Cb(U_{n+1})`
    is realized by a pronoun also.

    Vacuously satisfied when no Cb exists. The constraint is
    *one-directional*: it says nothing about whether the Cb *must* be
    pronominalized when no other entity is — Rule 1 only constrains
    what happens when pronominalization is used at all. -/
def Rule1Holds [DecidableEq E] [CfRankerOf E R] {U : Type}
    [Realizes U E] [Pronominalizes U E]
    (prev : Utterance E R) (cur : U) : Prop :=
  match cb prev cur with
  | none => True
  | some curCb =>
    (∃ e ∈ prev.cf, pronominalizes cur e) → pronominalizes cur curCb

instance [DecidableEq E] [CfRankerOf E R] {U : Type}
    [Realizes U E] [Pronominalizes U E]
    (prev : Utterance E R) (cur : U) :
    Decidable (Rule1Holds prev cur) := by
  unfold Rule1Holds
  cases cb prev cur <;> infer_instance

-- ════════════════════════════════════════════════════
-- § 2. Rule 2 (pair preference)
-- ════════════════════════════════════════════════════

/-- @cite{grosz-joshi-weinstein-1995} **Rule 2** is stated at the
    *pair-of-transitions* level: a pair `(t₁, t₂)` is preferred over a
    pair `(s₁, s₂)` when its constituent transitions have higher rank.
    Implemented as sum-of-ranks (the discriminating measure consistent
    with the paper's stated CONT-CONT > RET-RET > SHIFT-SHIFT case;
    `min` is a coarser alternative). -/
def pairRank (t₁ t₂ : Transition) : Nat := t₁.rank + t₂.rank

theorem rule2_continuations_preferred_over_retentions :
    pairRank .continuation .continuation > pairRank .retaining .retaining := by decide

theorem rule2_retentions_preferred_over_shifts :
    pairRank .retaining .retaining > pairRank .shifting .shifting := by decide

theorem rule2_continuations_preferred_over_shifts :
    pairRank .continuation .continuation > pairRank .shifting .shifting := by decide

end Discourse.Centering
