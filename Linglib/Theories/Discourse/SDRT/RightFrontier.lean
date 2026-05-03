import Linglib.Theories.Discourse.SDRT.Defs

/-!
# Right Frontier Constraint

@cite{asher-lascarides-2003}, §4.7 Definition 14, p. 148.

The Right Frontier Constraint (RFC) — originally Polanyi 1985,
formalized in SDRT as `availableAttachmentPoints` — restricts where
new discourse units can attach in an SDRS. The set of available
attachment points consists of:

1. The label `α = LAST` (the most recent attachment)
2. Any label `γ` such that either
   (a) `iOutscopes(γ, α)` (γ outscopes α structurally), or
   (b) `R(γ, α)` is a conjunct in some constituent's content where
       `R` is a subordinating relation (Elaboration, Explanation)
3. The transitive closure of (1)+(2) under the `<` relation
   (where `α < γ` means γ is reachable from α via 2a or 2b)

In words (book p. 149): "the available nodes are the previous clause
α and any label γ that dominates α via a series of outscopings and/or
subordinating relations."

## Worked example (book p. 149)

Given the SDRS in Figure 4.5 (the John-evening-meal-cheese-salmon
discourse) with LAST = π₂, the available attachment sites are
{π₂, π₄, π₃, π₀}. Notably, π₁ is NOT available — its constituent
has been "closed off" by the Elaboration.

The substrate captures this via the `availableAttachmentPoints`
function below; consumers can decide-check the worked example by
constructing the SDRS literally and confirming the result.

## Why this matters

The RFC is the central structural constraint on anaphora resolution
in SDRT (book Ch. 4 Definition 15). A pronoun in the NEW unit β can
only be resolved to a discourse referent in a unit α that's available
at attachment time. Without the RFC, anaphora resolution would
overgenerate.
-/

namespace Discourse.SDRT

variable {L : Type*} {α : Type*} [DecidableEq L]

-- ════════════════════════════════════════════════════════════════
-- § 1. The single-step "<" relation (Def 14 conditions 2a + 2b)
-- ════════════════════════════════════════════════════════════════

/-- `dominatesOneStep s α' γ` (the book's `α < γ` notation,
    @cite{asher-lascarides-2003} Def 14 p. 148): γ dominates α' in
    one step, either via outscoping (condition 2a) or via a
    subordinating relation pointing into α' (condition 2b).

    Condition (2a): `iOutscopes(γ, α')` — γ outscopes α'.
    Condition (2b): there exists a container λ and a subordinating
    relation R such that `R(γ, α')` is a conjunct in `F(λ)`.
    In our `container`-tagged edges this is: there exists an edge
    `⟨_, γ, α', R⟩` with R subordinating. -/
def dominatesOneStep (s : SDRS L α) (α' γ : L) : Prop :=
  iOutscopes s γ α' ∨
  ∃ e ∈ s.edges, e.source = γ ∧ e.target = α' ∧
                 e.relation.isSubordinating

instance (s : SDRS L α) (α' γ : L) :
    Decidable (dominatesOneStep s α' γ) := by
  unfold dominatesOneStep
  exact instDecidableOr

-- ════════════════════════════════════════════════════════════════
-- § 2. Available attachment points (Def 14, transitively closed)
-- ════════════════════════════════════════════════════════════════

/-- `availableViaChain s α γ n` — γ dominates α via a chain of
    length ≤ n of `dominatesOneStep` steps. Bounded because the
    transitive closure on a finite SDRS terminates. -/
def availableViaChain (s : SDRS L α) (α' γ : L) : Nat → Prop
  | 0 => α' = γ
  | n + 1 => availableViaChain s α' γ n ∨
             ∃ δ ∈ s.labels, dominatesOneStep s α' δ ∧
                              availableViaChain s δ γ n

instance (s : SDRS L α) (α' γ : L) (n : Nat) :
    Decidable (availableViaChain s α' γ n) := by
  induction n generalizing α' with
  | zero => exact inferInstanceAs (Decidable (_ = _))
  | succ n ih =>
    unfold availableViaChain
    exact instDecidableOr

/-- `availableAttachmentPoints s` — the set of labels available for
    new attachment from `s.last`, as a `List L`
    (@cite{asher-lascarides-2003}, Def 14 p. 148).

    Implementation: starting from `s.last`, walk up the
    `dominatesOneStep` relation. The chain length is bounded by
    `s.labels.length` because the labels are finite and each step
    moves to a different label (well-foundedness from Def 13 L3'
    rules out cycles).

    Returns the labels γ such that `availableViaChain s s.last γ k`
    holds for some `k ≤ s.labels.length`. -/
def availableAttachmentPoints (s : SDRS L α) : List L :=
  s.labels.filter
    (fun γ => decide (availableViaChain s s.last γ s.labels.length))

-- ════════════════════════════════════════════════════════════════
-- § 3. Structural theorems
-- ════════════════════════════════════════════════════════════════

/-- LAST is always its own available attachment point (Def 14
    condition 1). Holds at chain length 0. -/
theorem last_self_available (s : SDRS L α) :
    availableViaChain s s.last s.last 0 := rfl

/-- The available-via-chain relation is monotone in the chain
    length: longer chains include shorter ones. -/
theorem availableViaChain_mono (s : SDRS L α) (α' γ : L) (n : Nat) :
    availableViaChain s α' γ n → availableViaChain s α' γ (n + 1) := by
  intro h
  unfold availableViaChain
  exact Or.inl h

/-- `α' < γ` (one-step domination) implies γ is available from α'
    at chain length 1. Headline corollary of Def 14 condition 2. -/
theorem oneStep_available (s : SDRS L α) (α' γ : L)
    (hγ : γ ∈ s.labels)
    (h : dominatesOneStep s α' γ) :
    availableViaChain s α' γ 1 := by
  unfold availableViaChain
  refine Or.inr ⟨γ, hγ, h, ?_⟩
  rfl

end Discourse.SDRT
