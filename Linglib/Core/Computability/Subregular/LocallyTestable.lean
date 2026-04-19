import Linglib.Core.Computability.Subregular.StrictlyLocal

/-!
# Locally Testable Languages (LT_k, LTT_{k,t})

A language `L` is **locally `k`-testable** when membership depends only on
which length-`k` factors occur in the boundary-augmented form of the input —
ignoring order and multiplicity @cite{rogers-pullum-2011} @cite{lambert-2022}.
The **threshold-testable** variant LTT_{k,t} relaxes "ignoring multiplicity"
to "saturating multiplicities at threshold `t`": LT counts only presence vs
absence (`t = 1`), LTT_{k,t} counts up to `t` and treats anything beyond as
"≥ t".

Both are *property-based* (extensional) classifications — there is no
canonical grammar, only an indistinguishability relation on strings:
`w₁ ~_LT w₂` iff their `k`-factor sets coincide. `L` is LT_k iff it is closed
under `~_LT`.

## Inclusions established here

- `isSLk_imp_isLTk`: every SL_k language is LT_k (Lambert §3.2). The SL test
  "every factor is permitted" depends only on the *set* of factors.

The dual inclusions (LT_k ⊆ LTT_{k,t}, the strict separations between SL/LT/
LTT, and the connection to TSL) are handled in `Hierarchy.lean`.
-/

namespace Core.Computability.Subregular

universe u

variable {α : Type u}

-- ============================================================================
-- § 1: Locally testable (LT_k)
-- ============================================================================

/-- The set of `k`-factors of the boundary-augmented form of `w`. The LT
    indistinguishability relation `w₁ ~_LT w₂` is exactly equality of
    `factorSet k w₁` and `factorSet k w₂`. -/
def factorSet (k : ℕ) (w : List α) : Set (Augmented α) :=
  {f | f ∈ kFactorsList k (boundary k w)}

/-- A language is **locally `k`-testable** iff strings with the same set of
    `k`-factors are either both in `L` or both out. -/
def IsLTk (k : ℕ) (L : Language α) : Prop :=
  ∀ w₁ w₂ : List α, factorSet k w₁ = factorSet k w₂ → (w₁ ∈ L ↔ w₂ ∈ L)

/-- **SL_k ⊆ LT_k**: every strictly-`k`-local language is locally
    `k`-testable. The SL test ("every factor is permitted") trivially
    depends only on the *set* of factors, not their order or multiplicity. -/
theorem isSLk_imp_isLTk {k : ℕ} {L : Language α} (h : IsSLk k L) :
    IsLTk k L := by
  obtain ⟨G, rfl⟩ := h
  intro w₁ w₂ heq
  have key : ∀ w, w ∈ G.lang ↔ ∀ f ∈ factorSet k w, f ∈ G.permitted := by
    intro w; rfl
  rw [key, key, heq]

-- ============================================================================
-- § 2: Locally threshold-testable (LTT_{k,t})
-- ============================================================================

variable [DecidableEq α]

/-- Saturated multiplicity: how many times factor `f` occurs in `w`'s
    boundary-augmented form, capped at threshold `t`. The cap is what
    makes LTT a *finite* test even on infinite-input families. -/
def factorCount (k t : ℕ) (f : Augmented α) (w : List α) : ℕ :=
  min t ((kFactorsList k (boundary k w)).count f)

/-- A language is **locally `(k,t)`-threshold-testable** iff strings with
    the same `t`-saturated factor counts agree on membership. Specializing
    to `t = 1` recovers `IsLTk` (presence vs absence of each factor). -/
def IsLTTk (k t : ℕ) (L : Language α) : Prop :=
  ∀ w₁ w₂ : List α,
    (∀ f, factorCount k t f w₁ = factorCount k t f w₂) → (w₁ ∈ L ↔ w₂ ∈ L)

end Core.Computability.Subregular
