import Linglib.Core.NestedRestriction
import Linglib.Core.Mereology
import Linglib.Core.Semantics.Presupposition

/-!
# Height as Domain Restriction in ASL
@cite{davidson-gagne-2022}

Davidson, K. & Gagné, D. (2022). "More is up" for domain restriction in ASL.
*Semantics & Pragmatics* 15, Article 1: 1–52.

## Core Idea

Vertical height in ASL signing space overtly marks quantifier domain
restriction — the contextual variable C that spoken languages leave covert.
Higher signing maps monotonically to mereologically larger domains. This
height enters the grammar via **pronominal elements** (IX-arc), not bare
nouns: pronouns, directional verbs (which incorporate pronouns), and
quantifiers (which take a pronominal restrictor via a partitive-like
structure).

## Architecture

`VerticalHeight` is a 3-level linear order (low < neutral < high) that
instantiates `Core.NestedRestriction`. This gives all monotonicity and
nesting theorems from `DomainRestriction.lean` for free.

The presuppositional denotations of IX-arc follow the phi-feature pattern
from `PhiFeatures.lean`: height marking is a presuppositional partial
identity function on plural individuals, analogous to gender on personal
pronouns or proximal/distal on demonstratives.

## Key Denotations

- ⟦arc⟧ = λx: ¬atomic(x). x — plural pronoun presupposes non-atomicity
- ⟦neutral⟧ = λx: ∀y(y ≤ x → y ∈ Cₑ). x — all parts in context
- ⟦domain-k⟧ = ⟦high⟧ = λx: Cₑ ⊂ {y : y ≤ x}. x — context is proper subpart
-/

set_option autoImplicit false

namespace Fragments.ASL.Height

open Core.Presupposition (PrProp)

-- ════════════════════════════════════════════════════════════════
-- § 1. Vertical Height Scale
-- ════════════════════════════════════════════════════════════════

/-- Vertical height in ASL signing space.

    @cite{davidson-gagne-2022} establish empirically that at least three
    height levels are semantically distinguished (ex. 15–16, 34): neutral
    signing height (default contextual domain), a mid level (superset of
    the default), and a high level (further superset). The contrast between
    (15) and (16) demonstrates that heights are relative, not absolute —
    a 3-level system can be compressed to 2 levels when the context provides
    only two relevant domains.

    low < neutral < high, with higher = wider domain. -/
inductive VerticalHeight where
  | low
  | neutral
  | high
  deriving DecidableEq, Repr, Inhabited

instance : Fintype VerticalHeight where
  elems := {.low, .neutral, .high}
  complete := λ x => by cases x <;> simp

/-- Rank embedding for the linear order on VerticalHeight. -/
def VerticalHeight.toFin : VerticalHeight → Fin 3
  | .low => 0
  | .neutral => 1
  | .high => 2

private theorem VerticalHeight.toFin_injective : Function.Injective VerticalHeight.toFin := by
  intro a b h; cases a <;> cases b <;> simp_all [toFin]

/-- low < neutral < high. -/
instance : LinearOrder VerticalHeight :=
  LinearOrder.lift' VerticalHeight.toFin VerticalHeight.toFin_injective

instance : OrderTop VerticalHeight where
  top := .high
  le_top a := by cases a <;> decide

instance : OrderBot VerticalHeight where
  bot := .low
  bot_le a := by cases a <;> decide

-- ════════════════════════════════════════════════════════════════
-- § 2. Height-Indexed Domain Restriction
-- ════════════════════════════════════════════════════════════════

/-- Height-indexed domain restrictor for ASL signing space.

    A `HeightDDRP E` is a `NestedRestriction` parameterized by `VerticalHeight`:
    each height level maps to a domain predicate, with higher height giving a
    superset. This is the third instance of `NestedRestriction` in linglib,
    alongside `SpatialScale` (@cite{ritchie-schiller-2024}) and `TwoLevel`
    (comparison class inference, @cite{tessler-goodman-2022}).

    All nesting and monotonicity theorems from `NestedRestriction` —
    `forall_nesting`, `exists_nesting`, and the derived `DDRP.every_nesting`,
    `DDRP.some_nesting`, `DDRP.no_nesting` — apply automatically. -/
abbrev HeightDDRP (E : Type*) := Core.NestedRestriction VerticalHeight E

/-- Construct a height-indexed DDRP from a height assignment function.

    Parallels `sceneToDDRP` in @cite{ritchie-schiller-2024}: given a
    function assigning entities to their minimum visible height level,
    builds the nested domain restrictor where `region h` contains all
    entities visible at height ≤ h. -/
def heightToDDRP {E : Type*} (zone : E → VerticalHeight) : HeightDDRP E where
  region h := λ e => zone e ≤ h
  monotone {h₁ h₂} hle _ hr := by exact le_trans hr hle
  top_total e := by show zone e ≤ ⊤; exact le_top

-- ════════════════════════════════════════════════════════════════
-- § 3. Presuppositional Denotations
-- ════════════════════════════════════════════════════════════════

/-- ⟦arc⟧ presupposition: the plural pronoun IX-arc presupposes that its
    referent is non-atomic (a plural individual).

    ⟦arc⟧ = λx: ¬Atom(x). x

    This uses `Mereology.Atom` from `Core/Mereology.lean`. The at-issue
    content is the identity — arc contributes only a presupposition, not
    assertoric content. -/
def arcPresup (E : Type*) [PartialOrder E] : PrProp E where
  presup := λ x => ¬ Mereology.Atom x
  assertion := λ _ => True

/-- Height-dependent domain presupposition.

    - ⟦high⟧ = ⟦domain-k⟧: Cₑ ⊂ {y : y ≤ x} — context is a proper
      subpart, i.e., the domain widens beyond the contextual default.
      @cite{davidson-gagne-2022} eq. (44).

    - ⟦neutral⟧: ∀y(y ≤ x → y ∈ Cₑ) — all parts are in the contextual
      domain. This is the unmarked default.

    - ⟦low⟧: Mereology.Atom x — the referent is atomic (a singleton).
      @cite{davidson-gagne-2022} (p. 39) report that SOME-low yields
      specific indefinite readings ("someone — and maybe you — know who"),
      consistent with @cite{schwarzschild-2002}'s view of specificity as
      extreme domain restriction. The presupposition is maximally
      restrictive: the domain collapses to a single individual. -/
def domainPresup {E : Type*} [PartialOrder E] (C : E → Prop) :
    VerticalHeight → PrProp E
  | .high => { presup := λ x => (∀ y, C y → y ≤ x) ∧ ∃ y, y ≤ x ∧ ¬ C y
               assertion := λ _ => True }
  | .neutral => { presup := λ x => ∀ y, y ≤ x → C y
                  assertion := λ _ => True }
  | .low => { presup := λ x => Mereology.Atom x
              assertion := λ _ => True }

/-- Full IX-arc-height denotation: conjunction of the arc (non-atomicity)
    and domain (height-dependent containment) presuppositions.

    ⟦[IX_i]-arc-height⟧ = ιz: ¬Atom(z) ∧ domainPresup(height). (z = g(i)) -/
def ixArcHeightPresup {E : Type*} [PartialOrder E] (C : E → Prop)
    (h : VerticalHeight) : PrProp E where
  presup := λ x => (arcPresup E).presup x ∧ (domainPresup C h).presup x
  assertion := λ _ => True

-- ════════════════════════════════════════════════════════════════
-- § 4. Height Nesting (Structural)
-- ════════════════════════════════════════════════════════════════

/-- The high presupposition entails the neutral presupposition is false:
    if Cₑ is a proper subpart of {y : y ≤ x}, then NOT all parts of x
    are in Cₑ. These are complementary conditions on the same domain. -/
theorem high_incompatible_with_neutral {E : Type*} [PartialOrder E]
    {C : E → Prop} {x : E}
    (hHigh : (domainPresup C .high).presup x) :
    ¬ (domainPresup C .neutral).presup x := by
  intro hNeut
  obtain ⟨y, hle, hnC⟩ := hHigh.2
  exact hnC (hNeut y hle)

/-- IX-arc-low is presuppositionally contradictory: arc requires
    non-atomicity (¬Atom), while low requires atomicity (Atom).
    This correctly predicts that the *plural* pronoun IX-arc cannot
    take low height — only singular IX can be specific/low.
    @cite{davidson-gagne-2022} (p. 39): the specific indefinite reading
    with low height uses SOME (an existential quantifier), not IX-arc
    (the plural pronoun). -/
theorem arc_low_contradictory {E : Type*} [PartialOrder E]
    {C : E → Prop} {x : E} :
    ¬ (ixArcHeightPresup C .low).presup x := by
  intro ⟨hArc, hLow⟩
  exact hArc hLow

-- ════════════════════════════════════════════════════════════════
-- § 5. Partitive ⟦of⟧ Composition (§5.3, eqs. 50–51)
-- ════════════════════════════════════════════════════════════════

/-! @cite{davidson-gagne-2022} §5.3 derives quantifier truth conditions
    step-by-step through the partitive type function ⟦of⟧ = λxλy. y ≤ x
    (Ladusaw 1982). The pronoun IX-arc denotes a discourse referent z
    (the maximal plural individual), and ⟦of⟧ maps z to `Set.Iic z` —
    the principal down-set, i.e., the set of z's mereological parts.
    This set becomes the semantic restrictor of FS-ALL via the generalized
    quantifier structure.

    The composition:
    1. ⟦IX-arc-h⟧ = ιz : presup(h). z = g(i) — pronoun with presuppositions
    2. ⟦of⟧ z = `Set.Iic z` = {y | y ≤ z} — parts of z
    3. ⟦FS-ALL⟧(`Set.Iic z`)(Q) = ∀x ∈ Set.Iic z, Q x

    The height presuppositions constrain `Set.Iic z` relative to C:
    - neutral: `Set.Iic z ⊆ C` (default domain)
    - high: `C ⊆ Set.Iic z` with `¬(Set.Iic z ⊆ C)` (expanded domain)

    The proofs below are definitionally trivial — the presuppositions
    encode exactly the `Set.Iic` containment relations. This is the
    design payoff: `domainPresup` and `Set.Iic` are structurally
    aligned by construction, not by accident.

    `Set.Iic` is Mathlib's principal down-set, also used as
    `Mereotopology.parts` in `Core/Mereotopology.lean`. Key lemmas
    from Mathlib that apply directly:
    - `Set.Iic_subset_Iic`: `Set.Iic a ⊆ Set.Iic b ↔ a ≤ b`
    - `Set.Iic_top`: `Set.Iic ⊤ = Set.univ`
    - `Set.mem_Iic`: `x ∈ Set.Iic b ↔ x ≤ b` -/

/-- Under the neutral presupposition (∀y, y ≤ z → C y), the partitive
    domain `Set.Iic z` is contained in C.

    This IS the neutral presupposition — `domainPresup .neutral` encodes
    exactly `Set.Iic z ⊆ C`. The proof is `id`.

    @cite{davidson-gagne-2022} eq. (50c): ⟦(of) IX-arc-neutral⟧ = λy. y ∈ Cₑ. -/
theorem partitive_neutral_subset {E : Type*} [PartialOrder E]
    {C : Set E} {z : E}
    (hNeut : (domainPresup C .neutral).presup z) :
    Set.Iic z ⊆ C :=
  hNeut

/-- Under the high presupposition, C is a proper subset of `Set.Iic z`:
    all of C is among the parts of z, but z has parts outside C.

    This IS the high presupposition — `domainPresup .high` encodes
    exactly `C ⊆ Set.Iic z` with a witness outside C. The proof is `id`.

    @cite{davidson-gagne-2022} eq. (51c): ⟦(of) IX-arc-high⟧ = λy. y ∈ C',
    where C ⊂ C'. -/
theorem partitive_high_superset {E : Type*} [PartialOrder E]
    {C : Set E} {z : E}
    (hHigh : (domainPresup C .high).presup z) :
    C ⊆ Set.Iic z ∧ ∃ y ∈ Set.Iic z, ¬ C y :=
  hHigh

/-- The partitive domain `Set.Iic z` aligns with a `HeightDDRP` region
    when the discourse referent z's mereological parts are exactly the
    entities visible at height h. This bridges the two construction paths:

    - **DDRP path**: `heightToDDRP zone` → `region h` → quantifier restrictor
    - **Partitive path**: `IX-arc-h` → `Set.Iic z` → `∀x ≤ z, Q x`

    The alignment condition `align` is satisfied when z is the maximal
    group entity at height h — the entity whose parts are exactly the
    individuals in the DDRP region. When this holds, the DDRP-based
    computation is a correct implementation of the compositional derivation. -/
theorem partitive_ddrp_equiv {E : Type*} [PartialOrder E]
    (ddrp : HeightDDRP E) (h : VerticalHeight) (z : E)
    (align : ∀ e, e ∈ ddrp.region h ↔ e ≤ z) :
    ∀ e, e ∈ Set.Iic z ↔ e ∈ ddrp.region h :=
  λ e => (align e).symm

end Fragments.ASL.Height
