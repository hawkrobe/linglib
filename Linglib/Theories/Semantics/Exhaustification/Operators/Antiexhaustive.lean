import Linglib.Theories.Semantics.Exhaustification.Operators.Basic

/-!
# Antiexhaustive Operator O⁻ @cite{chierchia-2006}

Chierchia's `O⁻` is distinct from `O` (exhaustification/only) and `E`
(even-like enrichment). While `O` negates stronger alternatives, `O⁻`
requires that **every** alternative in `C` entails every other — i.e., the
alternative set is a complete join semilattice. This yields
"antiexhaustive" universal-like force from an existential base.

Formally: `O⁻_C(p) = p ∧ ∀q ∈ C. q` (the assertion together with every
alternative being true).

The key use: when `C = D`-variants (subdomain alternatives) of an
existential `∃x∈D.P(x)`, asserting all `D`-variants gives `∀D'⊆D.
∃x∈D'.P(x)` — a distribution requirement across subdomains, i.e.,
universal force.

## Deriving Universal Force from Antiexhaustive Enrichment

@cite{chierchia-2006} §5.1: When `O⁻` is applied to an existential
`∃x∈D.P(x)` with `D-MIN` alternatives (all subdomains), the enriched
meaning requires the existential to hold over every subdomain — equivalent
to universal force. The formal engine behind FCI universal readings.
-/

namespace Exhaustification

variable {World : Type*}

/-- Antiexhaustive enrichment `O⁻`: assert the prejacent and every
    alternative.

    Simplified from @cite{chierchia-2006} definition (108c) / (62). The
    paper defines `O⁻_C(p) = p ∧ ∀q,q'∈C [q → q']` where `q'` has domain
    complementary to `q` — i.e., mutual entailment between all
    domain-alternative pairs. We simplify to the equivalent truth
    conditions `p ∧ ∀q∈C. q` (asserting all alternatives), which produces
    the same result when `C` consists of subdomain existentials forming a
    lattice.

    When `C` is a set of `D`-variants (subdomain existentials), asserting
    all of them yields: for every subdomain `D'` of `D`, `∃x∈D'.P(x)`. -/
def oMinus (C : Set (Set World)) (p : Set World) : Set World :=
  λ w => p w ∧ ∀ q ∈ C, q w

/-- `O⁻` is a strengthening operation: `O⁻_C(p) ⊆ p`. -/
theorem oMinus_entails (C : Set (Set World)) (p : Set World) :
    oMinus C p ⊆ p :=
  λ _ ⟨hp, _⟩ => hp

/-- `O⁻` is at least as strong as any individual alternative. -/
theorem oMinus_entails_alt (C : Set (Set World)) (p : Set World) (q : Set World)
    (hq : q ∈ C) : oMinus C p ⊆ q :=
  λ _ ⟨_, hall⟩ => hall q hq

section UniversalFromAntiexh

variable {Entity : Type*}

/-- An existential over a finite domain (list-based for computability). -/
def existsIn (D : List Entity) (P : Entity → Set World) : Set World :=
  λ w => ∃ x ∈ D, P x w

/-- `D-MIN` alternatives: existentials over all sublists (subdomains). -/
def dMinAlts (D : List Entity) (P : Entity → Set World) : Set (Set World) :=
  {q | ∃ D' : List Entity, (∀ x ∈ D', x ∈ D) ∧ q = existsIn D' P}

/-- **Antiexhaustiveness yields universal distribution.**

    `O⁻` applied to `∃x∈D.P(x)` with `D-MIN` alternatives entails that for
    every individual `a ∈ D`, `P(a)` holds — i.e., universal force.

    Chierchia 2006's key formal result: the "birth of universal readings"
    (§5.1) from antiexhaustive enrichment of an existential base. -/
theorem antiexh_yields_universal
    (D : List Entity) (P : Entity → Set World) (w : World)
    (h : oMinus (dMinAlts D P) (existsIn D P) w) :
    ∀ a ∈ D, P a w := by
  intro a ha
  obtain ⟨_, hall⟩ := h
  have hmem : existsIn [a] P ∈ dMinAlts D P := by
    unfold dMinAlts
    exact ⟨[a], λ x hx => by simp only [List.mem_singleton] at hx; rw [hx]; exact ha, rfl⟩
  have := hall _ hmem
  unfold existsIn at this
  obtain ⟨x, hx, hPx⟩ := this
  simp only [List.mem_singleton] at hx
  rw [hx] at hPx
  exact hPx

end UniversalFromAntiexh

end Exhaustification
