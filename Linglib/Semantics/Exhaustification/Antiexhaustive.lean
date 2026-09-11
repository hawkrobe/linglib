import Linglib.Semantics.Exhaustification.InnocentExclusion

/-!
# Antiexhaustive Operator O⁻ [chierchia-2006]

Chierchia's `O⁻` is distinct from `O` (exhaustification/only) and `E`
(even-like enrichment). While `O` negates stronger alternatives, `O⁻`
requires that **every** alternative in `C` entails every other — i.e., the
alternative set is a complete join semilattice. This yields
"antiexhaustive" universal-like force from an existential base.

Formally: `O⁻_C(p) = p ∧ ∀q ∈ C. q` (the assertion together with every
alternative being true).

The key use: when `C` is the set of D-variants of an existential
`∃x∈D.P(x)` over the subdomains that stand a chance, asserting all of them
gives `∀D'⊆D. ∃x∈D'.P(x)` — a distribution requirement across subdomains,
i.e., universal force over the possible witnesses.

## Deriving Universal Force from Antiexhaustive Enrichment

[chierchia-2006] §5.1: When `O⁻` is applied to an existential
`∃x∈D.P(x)` with `D-MIN` alternatives (the subdomains containing a possible
witness, (61b)), the enriched meaning requires the existential to hold over
every such subdomain — equivalent to universal force over the possible
witnesses in `D`, (63d). The formal engine behind FCI universal readings.

## Implementation notes

An alternative domain must contain a possible witness, (61b): without that
restriction the empty subdomain would be an alternative, its existential the
empty proposition, and `O⁻` contradictory everywhere.
-/

namespace Exhaustification

variable {World : Type*}

/-- Antiexhaustive enrichment `O⁻`: assert the prejacent and every
    alternative.

    Simplified from [chierchia-2006] definition (108c) / (62). The
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

/-- Under an antitone embedding, alternatives that each entail the prejacent are all
entailed by the embedded prejacent, so antiexhaustive enrichment is vacuous: the
free-choice implicature of an item under negation disappears, [chierchia-2006] (65)–(66). -/
theorem oMinus_image_antitone_eq {C : Set World → Set World} (hC : Antitone C)
    {A : Set (Set World)} {p : Set World} (hA : ∀ q ∈ A, q ⊆ p) :
    oMinus (C '' A) (C p) = C p :=
  Set.Subset.antisymm (oMinus_entails _ _)
    (λ _ hw => ⟨hw, by rintro _ ⟨q, hq, rfl⟩; exact hC (hA q hq) hw⟩)

section UniversalFromAntiexh

variable {Entity : Type*}

/-- An existential over a finite domain (list-based for computability). -/
def existsIn (D : List Entity) (P : Entity → Set World) : Set World :=
  λ w => ∃ x ∈ D, P x w

/-- A subdomain existential entails the existential over the whole domain. -/
theorem existsIn_subset (D : List Entity) (P : Entity → Set World) {D' : List Entity}
    (h : ∀ x ∈ D', x ∈ D) : existsIn D' P ⊆ existsIn D P := by
  rintro w ⟨x, hx, hPx⟩
  exact ⟨x, h x hx, hPx⟩

/-- The `D`-variants of a domain-dependent proposition, [chierchia-2006] (96): its values on the
subdomains of `D` that stand a chance, those containing a `possible` member, (61b). -/
def dVariants (F : List Entity → Set World) (D : List Entity) (possible : Entity → Prop) :
    Set (Set World) :=
  {q | ∃ D' : List Entity, (∀ x ∈ D', x ∈ D) ∧ (∃ x ∈ D', possible x) ∧ q = F D'}

/-- `D-MIN` alternatives: existentials over the subdomains with a possible witness. -/
def dMinAlts (D : List Entity) (P : Entity → Set World) : Set (Set World) :=
  dVariants (existsIn · P) D (λ x => ∃ v, P x v)

/-- **Antiexhaustiveness is universal force over the possible witnesses.**

    `O⁻` applied to `∃x∈D.P(x)` with `D-MIN` alternatives holds exactly when every
    possible witness in `D` is an actual one, [chierchia-2006] (63c)–(63d). -/
theorem oMinus_dMinAlts_iff (D : List Entity) (P : Entity → Set World) (w : World)
    (hD : ∃ a ∈ D, ∃ v, P a v) :
    oMinus (dMinAlts D P) (existsIn D P) w ↔ ∀ a ∈ D, (∃ v, P a v) → P a w := by
  constructor
  · rintro ⟨_, hall⟩ a ha hpos
    obtain ⟨x, hx, hPx⟩ :=
      hall _ ⟨[a], by simpa using ha, ⟨a, List.mem_singleton_self a, hpos⟩, rfl⟩
    obtain rfl := List.mem_singleton.1 hx
    exact hPx
  · intro h
    obtain ⟨a, ha, hpos⟩ := hD
    refine ⟨⟨a, ha, h a ha hpos⟩, ?_⟩
    rintro _ ⟨D', hD', ⟨b, hb, hbpos⟩, rfl⟩
    exact ⟨b, hb, h b (hD' b hb) hbpos⟩

/-- **Antiexhaustiveness yields universal distribution.**

    Chierchia 2006's key formal result: the "birth of universal readings"
    (§5.1) from antiexhaustive enrichment of an existential base. -/
theorem antiexh_yields_universal
    (D : List Entity) (P : Entity → Set World) (w : World)
    (h : oMinus (dMinAlts D P) (existsIn D P) w) :
    ∀ a ∈ D, (∃ v, P a v) → P a w := by
  rintro a ha hpos
  obtain ⟨x, hx, hPx⟩ :=
    h.2 _ ⟨[a], by simpa using ha, ⟨a, List.mem_singleton_self a, hpos⟩, rfl⟩
  obtain rfl := List.mem_singleton.1 hx
  exact hPx

end UniversalFromAntiexh

end Exhaustification
