import Linglib.Semantics.Dynamic.DPL
import Linglib.Core.Logic.Bilateral.Defs

/-!
# Charlow (2025) — Staged updates: lifted interpretations for DNE in dynamic semantics
[charlow-2025-staged-updates]
[groenendijk-stokhof-1991] [krahmer-muskens-1995] [gotham-2019-ac22]
[mandelkern-2022] [hofmann-2025] [spector-2025] [charlow-2014]

Charlow's [charlow-2025-staged-updates] (SALT 35 proceedings) gives an
algebraic characterization of how to **lift** a non-DNE-validating dynamic
substrate δ (e.g. DPL) into a richer Δ that does validate double-negation
elimination. Three operations (`up : δ → Δ`, `down : Δ → δ`, `invneg : Δ → Δ`)
plus three equational laws (Emb, Inv, Neg) suffice. Charlow's Fact 4 (the
headline) says: any two lawful lifts of the same substrate are isomorphic
on the image of the lifted interpretation.

## Architectural placement

Per linglib anchoring discipline (CLAUDE.md), framework substrate originating
with a paper lives in the originating Studies file until ≥ 2 paper-anchored
consumers exist. Currently only this file consumes the lift framework, so
the typeclasses live here. Promotion to `Semantics/Dynamic/Lift.lean`
is queued for when a Mandelkern2022 or Gotham2019 study lands.

The framework is **strictly more general than `Core.Logic.Bilateral.IsBilateral`**:
the Krahmer-Muskens (Instance 1) lift is bilateral and derives its laws from
`IsBilateral`, but the other three instances (Gotham decomposed, Staged updates,
Canonical) have non-bilateral shapes. `IsLawfulDNELift` does not extend
`IsBilateral`; it consumes it where applicable.

## Connection to existing linglib infrastructure

[charlow-2014]'s `AnaphoraFramework` (`Linglib/Studies/Charlow2014.lean`)
formalizes the partition of dynamic-anaphora frameworks into
`RepStrategy.stateThreading` (DRT, DPL, CDRT, BUS) vs `.typeStructure` (TTR).
Charlow 2025 strengthens the state-threading side: any two lifts that
satisfy Emb/Inv/Neg over the same substrate δ are isomorphic on the image
of `liftInterp`. This subsumes the prose "three incompatible DNE solutions"
table in `Semantics/Dynamic/Update.lean §49-78` for the
state-threading row — bilateral and ICDRT-bilateral are not incompatible
choices, they are isomorphic presentations once the substrate is fixed.
TTR remains genuinely outside the lift framework (its classical metalanguage
gives DNE statically, so there is no non-DNE substrate to lift from).

## Scope of this file

* §1 `DynamicSubstrate δ` — algebraic interface (conj + neg)
* §2 `DynForm Atom` — paper's ℒ ::= Atom | ∃x | φ ∧ ψ | ¬φ
* §3 `DNELift δ Δ` (data) + `IsLawfulDNELift δ Δ` (Prop, three laws)
* §4 `primInterp` and `liftInterp` (paper's [·] and ⟨·⟩, Definition 4)
* §5 Fact 1 (DNE validation) — proved
* §6 Fact 2 (conservativity over the substrate) — proved
* §7 Fact 4 (lifts factor through canonical form `δ ⊕ δ` via
  `lawful_lifts_factor_through_canonical`; kernel congruence via canonical form
  via `lawful_lifts_canonicalize_eq_implies` — both proved unconditionally;
  the literal "kernel iff" requires substrate non-degeneracy which Charlow's
  Appendix A proof implicitly assumes)
* §8 Auxiliary `DynamicProgramDisj`, `DynamicTruth` typeclasses
* §9-12 Four lift constructions (KM, Gotham, Staged, Canonical) over the DPL substrate
* §13 Sanity tests

The Spector 2025 weak-meaning prediction (donkey example, p. 871 of paper)
that discriminates bounded meanings from staged updates is not formalized
here — it requires the Mandelkern2022 study file as scaffolding.

The Section 6 exceptional-scope `D_σ` framework is also out of scope; it
requires the separate JoS [charlow-2014] successor "Static and dynamic
exceptional scope" which has its own study file pending.
-/

namespace Charlow2025

universe u v w

-- ════════════════════════════════════════════════════════════════
-- § 1. The dynamic substrate (algebraic interface)
-- ════════════════════════════════════════════════════════════════

/-- A **dynamic substrate** is a carrier with binary conjunction and unary
negation. The paper's δ. Concrete instances: DPL `DPLRel E`, CDRT `DProp`,
ICDRT contexts, etc. The interpretation function [·] : ℒ → δ is supplied
per-call as `interpAtom` and `interpExi` rather than as a typeclass field
(no shared `Language` type exists across linglib's dynamic theories yet). -/
class DynamicSubstrate (δ : Type u) where
  /-- Substrate conjunction (paper's ∧_δ). -/
  conj : δ → δ → δ
  /-- Substrate negation (paper's ¬_δ). Should fail DNE on its own;
  the lift framework adds DNE without requiring it of the substrate. -/
  neg : δ → δ

-- ════════════════════════════════════════════════════════════════
-- § 2. The language ℒ
-- ════════════════════════════════════════════════════════════════

/-- The paper's ℒ ::= Atom | ∃x | φ ∧ ψ | ¬φ. The existential `∃x` is a
primitive zero-place atom: `∃x.φ` is sugar for `∃x ∧ φ` (paper §1, footnote
on dynamic interpretation of `∃x`). -/
inductive DynForm (Atom : Type v) where
  | atom : Atom → DynForm Atom
  | exi  : Nat → DynForm Atom
  | conj : DynForm Atom → DynForm Atom → DynForm Atom
  | neg  : DynForm Atom → DynForm Atom
  deriving Repr

-- ════════════════════════════════════════════════════════════════
-- § 3. The lift framework (paper's Definitions 3, 4)
-- ════════════════════════════════════════════════════════════════

/-- **DNELift data** (paper's Definition 3 signatures): a richer type Δ
equipped with `up : δ → Δ`, `down : Δ → δ`, and `invneg : Δ → Δ`. The
laws live in `IsLawfulDNELift`; this class only carries the data so that
the same `δ × δ`-shaped Δ can support multiple competing instances
(Krahmer-Muskens vs. Gotham) without typeclass diamond. -/
class DNELift (δ : Type u) (Δ : Type w) [DynamicSubstrate δ] where
  up : δ → Δ
  down : Δ → δ
  invneg : Δ → Δ

/-- **Lawful DNE lift** (paper's Definition 3 laws): the three equational
constraints that make a lift "lawful" in the paper's sense.

Following mathlib's `Mul`/`IsLeftCancelMul` convention, the data class
`DNELift` is split from the Prop class `IsLawfulDNELift`. This avoids the
0.230.649 anti-pattern that deleted a prior bundled-typeclass attempt for
bilateral logic; consumers can construct candidate `DNELift` instances
without committing to lawfulness.

Field names use the descriptive `down_X_up`-style mathlib idiom rather than
the paper's terse `Emb`/`Inv`/`Neg` to avoid name collisions and parser
ambiguity. -/
class IsLawfulDNELift (δ : Type u) (Δ : Type w)
    [DynamicSubstrate δ] [self : DNELift δ Δ] : Prop where
  /-- **Emb** (paper): `down ∘ up = id`. The substrate embeds faithfully. -/
  down_up : ∀ (m : δ), self.down (self.up m) = m
  /-- **Inv** (paper): `invneg ∘ invneg = id`. The lifted negation is involutive. -/
  invneg_invneg : ∀ (M : Δ), self.invneg (self.invneg M) = M
  /-- **Neg** (paper): `down ∘ invneg ∘ up = neg`. Conjugation by lift recovers
  the substrate negation. -/
  down_invneg_up : ∀ (m : δ),
    self.down (self.invneg (self.up m)) = DynamicSubstrate.neg m

-- ════════════════════════════════════════════════════════════════
-- § 4. Primitive and lifted interpretations (paper's Definition 4)
-- ════════════════════════════════════════════════════════════════

/-- The substrate's primitive interpretation `[·] : ℒ → δ`. Recursive on
the form structure, using only substrate operations. -/
def primInterp {Atom : Type v} {δ : Type u} [DynamicSubstrate δ]
    (interpAtom : Atom → δ) (interpExi : Nat → δ) :
    DynForm Atom → δ
  | .atom a    => interpAtom a
  | .exi n     => interpExi n
  | .conj φ ψ  => DynamicSubstrate.conj
                    (primInterp interpAtom interpExi φ)
                    (primInterp interpAtom interpExi ψ)
  | .neg  φ    => DynamicSubstrate.neg (primInterp interpAtom interpExi φ)

/-- The lifted interpretation `⟨·⟩ : ℒ → Δ` (paper Definition 4). The only
type-correct recursion given the lift signatures; conjunction sequences via
`up ∘ ∧_δ ∘ (down ⟨φ⟩, down ⟨ψ⟩)`, negation via `∼` directly. -/
def liftInterp {Atom : Type v} {δ : Type u} {Δ : Type w}
    [DynamicSubstrate δ] [self : DNELift δ Δ]
    (interpAtom : Atom → δ) (interpExi : Nat → δ) :
    DynForm Atom → Δ
  | .atom a    => self.up (interpAtom a)
  | .exi n     => self.up (interpExi n)
  | .conj φ ψ  =>
      self.up (DynamicSubstrate.conj
        (self.down (liftInterp interpAtom interpExi φ))
        (self.down (liftInterp interpAtom interpExi ψ)))
  | .neg φ     => self.invneg (liftInterp interpAtom interpExi φ)

-- ════════════════════════════════════════════════════════════════
-- § 5. Fact 1 — Lifted interpretations validate DNE
-- ════════════════════════════════════════════════════════════════

/-- **Fact 1** (paper, p. 864): the lifted interpretation validates double
negation elimination. `⟨¬¬φ⟩ = ⟨φ⟩` for any φ, by the involutive law on ∼. -/
theorem liftInterp_dneg
    {Atom : Type v} {δ : Type u} {Δ : Type w}
    [DynamicSubstrate δ] [DNELift δ Δ] [IsLawfulDNELift δ Δ]
    (ia : Atom → δ) (ie : Nat → δ) (φ : DynForm Atom) :
    (liftInterp (Δ := Δ) ia ie (.neg (.neg φ))) = liftInterp ia ie φ :=
  IsLawfulDNELift.invneg_invneg (liftInterp ia ie φ)

-- ════════════════════════════════════════════════════════════════
-- § 6. Fact 2 — Conservativity over the substrate
-- ════════════════════════════════════════════════════════════════

/-- A formula is **negation-free** if it contains no `¬`. -/
inductive NegFree {Atom : Type v} : DynForm Atom → Prop where
  | atom (a : Atom) : NegFree (.atom a)
  | exi (n : Nat) : NegFree (.exi n)
  | conj {φ ψ : DynForm Atom} : NegFree φ → NegFree ψ → NegFree (.conj φ ψ)

/-- A formula is **double-negation-free** if no subformula has the shape
`¬¬ψ`. The constructors enumerate the allowed `¬`-prefixed shapes (atom,
exi, conj of dneg-frees), excluding `.neg (.neg ψ)`. -/
inductive DNegFree {Atom : Type v} : DynForm Atom → Prop where
  | atom (a : Atom) : DNegFree (.atom a)
  | exi (n : Nat) : DNegFree (.exi n)
  | conj {φ ψ : DynForm Atom} : DNegFree φ → DNegFree ψ → DNegFree (.conj φ ψ)
  | neg_atom (a : Atom) : DNegFree (.neg (.atom a))
  | neg_exi (n : Nat) : DNegFree (.neg (.exi n))
  | neg_conj {φ ψ : DynForm Atom} :
      DNegFree φ → DNegFree ψ → DNegFree (.neg (.conj φ ψ))

/-- **Fact 2.i** (paper, p. 864): for ¬-free φ, the lifted interpretation is
literally the up-lift of the substrate interpretation. -/
theorem liftInterp_eq_up_primInterp_of_negFree
    {Atom : Type v} {δ : Type u} {Δ : Type w}
    [DynamicSubstrate δ] [DNELift δ Δ] [IsLawfulDNELift δ Δ]
    (ia : Atom → δ) (ie : Nat → δ) {φ : DynForm Atom} (h : NegFree φ) :
    (liftInterp ia ie φ : Δ) = DNELift.up (primInterp ia ie φ) := by
  induction h with
  | atom _ => rfl
  | exi _ => rfl
  | @conj φ' ψ' _ _ ih_φ ih_ψ =>
    show DNELift.up (DynamicSubstrate.conj
        (DNELift.down (liftInterp (Δ := Δ) ia ie φ'))
        (DNELift.down (liftInterp (Δ := Δ) ia ie ψ'))) = _
    rw [ih_φ, ih_ψ, IsLawfulDNELift.down_up, IsLawfulDNELift.down_up]
    rfl

/-- **Fact 2.ii** (paper, p. 864): for ¬¬-free φ, lowering the lifted
interpretation recovers the substrate interpretation exactly. -/
theorem down_liftInterp_eq_primInterp_of_dnegFree
    {Atom : Type v} {δ : Type u} {Δ : Type w}
    [DynamicSubstrate δ] [DNELift δ Δ] [IsLawfulDNELift δ Δ]
    (ia : Atom → δ) (ie : Nat → δ) {φ : DynForm Atom} (h : DNegFree φ) :
    DNELift.down (liftInterp (Δ := Δ) ia ie φ) = primInterp ia ie φ := by
  induction h with
  | atom _ => exact IsLawfulDNELift.down_up _
  | exi _ => exact IsLawfulDNELift.down_up _
  | @conj φ' ψ' _ _ ih_φ ih_ψ =>
    show DNELift.down
        (DNELift.up (DynamicSubstrate.conj
          (DNELift.down (liftInterp (Δ := Δ) ia ie φ'))
          (DNELift.down (liftInterp (Δ := Δ) ia ie ψ')))) = _
    rw [IsLawfulDNELift.down_up, ih_φ, ih_ψ]
    rfl
  | neg_atom _ => exact IsLawfulDNELift.down_invneg_up _
  | neg_exi _ => exact IsLawfulDNELift.down_invneg_up _
  | @neg_conj φ' ψ' _ _ ih_φ ih_ψ =>
    -- Full `@`-form for inner DNELift.down calls pins the substrate δ
    -- explicitly; without it, Lean cannot determine δ for the
    -- deeply-nested DNELift.up call (the error from a less explicit
    -- form is "DNELift ?m Δ" — first arg metavariable).
    show @DNELift.down δ Δ _ _ (@DNELift.invneg δ Δ _ _
        (@DNELift.up δ Δ _ _ (DynamicSubstrate.conj
          (@DNELift.down δ Δ _ _ (liftInterp (Δ := Δ) ia ie φ'))
          (@DNELift.down δ Δ _ _ (liftInterp (Δ := Δ) ia ie ψ'))))) = _
    rw [IsLawfulDNELift.down_invneg_up, ih_φ, ih_ψ]
    rfl

-- ════════════════════════════════════════════════════════════════
-- § 7. Fact 4 — Lifts factor through canonical form
-- ════════════════════════════════════════════════════════════════

/-! ### Canonical form of a lifted formula

Each lawful-lift value `⟨φ⟩_Δ` decomposes into (substrate value, parity bit)
where the parity tracks the residual negation count after DNE collapse.
Following mathlib's structural-typing idiom for binary-tagged values, we
encode the parity as `Sum δ δ`: `Sum.inl m` is "positive m" (even
negations), `Sum.inr m` is "negative m" (odd). `Sum.swap` is the canonical
involution implementing parity flip — directly mirroring `IsLawfulDNELift.invneg_invneg`. -/

/-- **Canonical form** of a formula's lifted interpretation. Depends only
on the substrate `δ` and interpretations `ia`/`ie`, not on the lift `Δ`. -/
def canonicalize {Atom : Type v} {δ : Type u} [DynamicSubstrate δ]
    (ia : Atom → δ) (ie : Nat → δ) : DynForm Atom → δ ⊕ δ
  | .atom a => Sum.inl (ia a)
  | .exi n  => Sum.inl (ie n)
  | .conj φ ψ =>
      Sum.inl (DynamicSubstrate.conj
        ((canonicalize ia ie φ).elim id DynamicSubstrate.neg)
        ((canonicalize ia ie ψ).elim id DynamicSubstrate.neg))
  | .neg φ  => Sum.swap (canonicalize ia ie φ)

/-- **Encoding** the canonical form into any lawful lift `Δ`: positive `m`
is `up m`; negative `m` is `invneg (up m)`. `Δ` is explicit because the
input `δ ⊕ δ` doesn't constrain it for inference. The `self` named binding
on the `DNELift δ Δ` instance makes Lean use the in-scope instance for
the body's `up`/`invneg` calls (rather than searching afresh). -/
def encodeCanonical (Δ : Type w) {δ : Type u} [DynamicSubstrate δ]
    [self : DNELift δ Δ] : δ ⊕ δ → Δ
  | Sum.inl m => self.up m
  | Sum.inr m => self.invneg (self.up m)

/-- **Down-projection of an encoded canonical form**: `s.elim id neg`.
Direct from Emb (`down ∘ up = id`) and Neg (`down ∘ invneg ∘ up = neg`). -/
theorem down_encodeCanonical {δ : Type u} (Δ : Type w)
    [DynamicSubstrate δ] [DNELift δ Δ] [IsLawfulDNELift δ Δ] (s : δ ⊕ δ) :
    DNELift.down (encodeCanonical Δ s) = s.elim id DynamicSubstrate.neg := by
  cases s with
  | inl m => exact IsLawfulDNELift.down_up m
  | inr m => exact IsLawfulDNELift.down_invneg_up m

/-- **Inv law for the canonical encoding**: `encodeCanonical ∘ Sum.swap =
invneg ∘ encodeCanonical`. The structural counterpart of
`IsLawfulDNELift.invneg_invneg`. -/
theorem encodeCanonical_swap {δ : Type u} (Δ : Type w)
    [DynamicSubstrate δ] [self : DNELift δ Δ] [IsLawfulDNELift δ Δ] (s : δ ⊕ δ) :
    encodeCanonical Δ (Sum.swap s) = self.invneg (encodeCanonical Δ s) := by
  cases s with
  | inl m => rfl
  | inr m =>
    show self.up m = self.invneg (self.invneg (self.up m))
    rw [IsLawfulDNELift.invneg_invneg]

/-- **Fact 4** (paper, p. 869) — **factor-through-canonical form**.

For any lawful lift `Δ`, the lifted interpretation `⟨·⟩ : ℒ → Δ` factors
through a canonical form `δ ⊕ δ` that depends only on the substrate, not
on the lift:
`⟨φ⟩_Δ = encodeCanonical (canonicalize φ)`.

This is the substantive content of Charlow's Fact 4. The bijection
`f : Im(⟨·⟩)₁ → Im(⟨·⟩)₂` Charlow constructs in Appendix A is the natural
transformation between encodings of the same canonical form in different
`Δ`s: `f ∘ encodeCanonical_1 = encodeCanonical_2`.

The corollary `canonicalize φ = canonicalize ψ → ⟨φ⟩_Δ = ⟨ψ⟩_Δ` (one
direction of the literal "kernel congruence iff" Charlow states) follows
immediately — see `lawful_lifts_canonicalize_eq_implies` below.

The other direction of the iff (`⟨φ⟩₁ = ⟨ψ⟩₁ → ⟨φ⟩₂ = ⟨ψ⟩₂`) requires
substrate **non-degeneracy** (no `m : δ` with `m = neg m`, since with such
`m` the KMLift collapses formulas the CanonicalLift distinguishes — paper
Appendix A's well-definedness check implicitly assumes this). For "real"
substrates like DPL the iff holds; the abstract iff is genuinely
substrate-dependent. The factor-through formulation is what's provable
unconditionally. -/
theorem lawful_lifts_factor_through_canonical
    {Atom : Type v} {δ : Type u} (Δ : Type w)
    [DynamicSubstrate δ] [self : DNELift δ Δ] [IsLawfulDNELift δ Δ]
    (ia : Atom → δ) (ie : Nat → δ) (φ : DynForm Atom) :
    (liftInterp ia ie φ : Δ) = encodeCanonical Δ (canonicalize ia ie φ) := by
  induction φ with
  | atom a => rfl
  | exi n => rfl
  | conj φ ψ ihφ ihψ =>
    show self.up (DynamicSubstrate.conj
            (self.down (liftInterp ia ie φ : Δ))
            (self.down (liftInterp ia ie ψ : Δ))) = _
    rw [ihφ, ihψ, down_encodeCanonical, down_encodeCanonical]
    rfl
  | neg φ ihφ =>
    show self.invneg (liftInterp ia ie φ : Δ) = _
    rw [ihφ]
    exact (encodeCanonical_swap Δ _).symm

/-- **Kernel congruence via canonical form** (paper Fact 4, the
unconditionally-provable direction). If two formulas have the same
canonical form, every lawful lift identifies them. -/
theorem lawful_lifts_canonicalize_eq_implies
    {Atom : Type v} {δ : Type u} {Δ₁ Δ₂ : Type w}
    [DynamicSubstrate δ]
    [DNELift δ Δ₁] [IsLawfulDNELift δ Δ₁]
    [DNELift δ Δ₂] [IsLawfulDNELift δ Δ₂]
    (ia : Atom → δ) (ie : Nat → δ) (φ ψ : DynForm Atom)
    (h : canonicalize ia ie φ = canonicalize ia ie ψ) :
    ((liftInterp ia ie φ : Δ₁) = liftInterp ia ie ψ) ∧
    ((liftInterp ia ie φ : Δ₂) = liftInterp ia ie ψ) := by
  refine ⟨?_, ?_⟩
  · rw [lawful_lifts_factor_through_canonical Δ₁,
        lawful_lifts_factor_through_canonical Δ₁, h]
  · rw [lawful_lifts_factor_through_canonical Δ₂,
        lawful_lifts_factor_through_canonical Δ₂, h]

-- ════════════════════════════════════════════════════════════════
-- § 8. Auxiliary substrate operations needed by Instances 2-3
-- ════════════════════════════════════════════════════════════════

/-- **Program disjunction** (paper's `m ∪ n`, Definition 6 / §3): the
externally-dynamic union of two updates. Needed by Gotham (Instance 2) and
Staged updates (Instance 3); not needed by KM (Instance 1) or Canonical
(Instance 4). Separate typeclass to avoid burdening the basic substrate
with operations its non-DNE-extending consumers do not need. -/
class DynamicProgramDisj (δ : Type u) [DynamicSubstrate δ] where
  /-- Program disjunction `m ∪ n`. For DPL: `λ g h => m g h ∨ n g h`. -/
  pdisj : δ → δ → δ

/-- **Truth as a static proposition** (paper's `True_δ(m)`, Definition 2 /
Definition 5): the set of indices where `m` succeeds. Indexed by the
substrate's index type `i`. Needed by Staged updates (Instance 3). -/
class DynamicTruth (δ : Type u) (i : outParam (Type v))
    [DynamicSubstrate δ] where
  /-- `True_δ(m) := { i | i[m] ≠ ∅ }`. For DPL: `λ g, ∃ h, m g h`. -/
  truth : δ → (i → Prop)
  /-- `m|_p`: restrict m to inputs in p. For DPL: `λ g h, p g ∧ m g h`. -/
  restrict : δ → (i → Prop) → δ

-- ════════════════════════════════════════════════════════════════
-- § 9. Substrate instance: the canonical DPL substrate
-- ════════════════════════════════════════════════════════════════

open Semantics.Dynamic.DPL

/-- The DPL relational meaning type (`DPLRel E := (Nat → E) → (Nat → E) → Prop`)
is a `DynamicSubstrate` via its native conjunction and negation. -/
instance instDynamicSubstrateDPLRel (E : Type u) : DynamicSubstrate (DPLRel E) where
  conj := DPLRel.conj
  neg := DPLRel.neg

/-- Program disjunction on `DPLRel`: pointwise OR. Note this differs from
DPL's `DPLRel.disj` (which is externally-static, clearing the assignment);
program disjunction preserves output bindings. -/
def dplProgramDisj {E : Type u} (φ ψ : DPLRel E) : DPLRel E :=
  fun g h => φ g h ∨ ψ g h

instance instDynamicProgramDisjDPLRel (E : Type u) :
    DynamicProgramDisj (DPLRel E) where
  pdisj := dplProgramDisj

instance instDynamicTruthDPLRel (E : Type u) :
    DynamicTruth (DPLRel E) (Nat → E) where
  truth m := fun g => ∃ h, m g h
  restrict m p := fun g h => p g ∧ m g h

-- ════════════════════════════════════════════════════════════════
-- § 10. Instance 1 — Krahmer-Muskens (paper p. 866)
-- ════════════════════════════════════════════════════════════════

/-! ### Instance 1: 2D DPL (Krahmer-Muskens 1995)

`Δ ::= δ × δ` (pairs of updates). The lift `m^↑ := (m, ¬_δ m)` pairs every
update with its substrate negation. `down` projects the first component;
`invneg` swaps. Charlow notes (p. 865, footnote 5) that this is his own
reconstruction of [krahmer-muskens-1995] as a lifted interpretation —
the original K&M presentation interprets DRSs, not first-order formulas,
and is distinguished syntactically from static conditions.

This instance derives `IsLawfulDNELift` directly from the algebraic shape
of `Prod`: `down (up m) = m` is `Prod.fst_mk`; `invneg (invneg M) = M` is
`Prod.swap_swap`; `down (invneg (up m)) = neg m` is by computation. The
swap-axiom witness is also packaged as a `Core.Logic.Bilateral.IsBilateral`
proof (see `kmIsBilateral` below), making the connection to existing
linglib bilateral substrate explicit. -/

/-- **Instance 1's carrier**: pairs of updates over the same substrate.
Implemented as a `structure` (not a `def := δ × δ` alias) so that typeclass
search treats it as a distinct type from `GothamLift δ` (which has the same
underlying shape). -/
structure KMLift (δ : Type u) where
  /-- Positive update component (the substrate update itself). -/
  positive : δ
  /-- Negative update component (the substrate's negation of the positive). -/
  negative : δ

namespace KMLift

variable {δ : Type u} [DynamicSubstrate δ]

instance instDNELift : DNELift δ (KMLift δ) where
  up m := ⟨m, DynamicSubstrate.neg m⟩
  down M := M.positive
  invneg M := ⟨M.negative, M.positive⟩

instance instIsLawfulDNELift : IsLawfulDNELift δ (KMLift δ) where
  down_up _ := rfl
  invneg_invneg _ := rfl
  down_invneg_up _ := rfl

omit [DynamicSubstrate δ] in
/-- **Connection to `Core.Logic.Bilateral.IsBilateral`**: the KM lift's
projections witness the paraconsistent-bilateral pattern, with `positive`
as the positive interpretation, `negative` as the negative interpretation,
and a swap-style negate. Demonstrates linglib interconnection density.

The leading `omit [DynamicSubstrate δ]` clears the namespace-scoped variable
that this lemma doesn't use (bilaterality of projection-and-swap is a
Prod-shape fact, not a substrate fact). -/
lemma kmIsBilateral :
    Core.Logic.Bilateral.IsBilateral
      (Form := KMLift δ) (Result := δ)
      KMLift.positive KMLift.negative
      (fun M => ⟨M.negative, M.positive⟩) :=
  ⟨fun _ => rfl, fun _ => rfl⟩

end KMLift

-- ════════════════════════════════════════════════════════════════
-- § 11. Instance 2 — Gotham decomposed updates (paper p. 867)
-- ════════════════════════════════════════════════════════════════

/-! ### Instance 2: Decomposed updates (Gotham 2019)

`Δ ::= δ × δ`, but with a different lift: `m^↑ := (¬¬m, m ∪ ¬_δ m)`.
The first component is the doubly-negated (truth-conditional) half; the
second is a "dynamic tautology" `m ∪ ¬m` that introduces drefs in either
horn. `down` is conjunction; `invneg` negates the truth-conditional half.

The full `IsLawfulDNELift` instance is **not declared** here — Gotham's
Emb law `(¬¬m) ∧_δ (m ∪ ¬m) = m` is provable for the DPL substrate by
unfolding `conj`, `neg`, `pdisj` definitions (paper p. 867 sketches the
argument), but does not hold for arbitrary `DynamicSubstrate + DynamicProgramDisj`.
A future PR formalising Gotham 2019 as its own study should add the
DPL-specific instance + the substrate axioms required for generality.

The `lift` data is provided so that `liftInterp (Δ := GothamLift δ)` can be
typed; `IsLawfulDNELift` synthesis fails (correctly) so dependent theorems
do not silently accept un-proved laws. -/

/-- **Instance 2's carrier**: pairs of (truth-conditional, dynamic-tautology)
halves. Distinct structure from `KMLift` despite the same shape — different
field names + different lift operations. -/
structure GothamLift (δ : Type u) where
  /-- Doubly-negated, truth-conditional half (¬¬m). -/
  truthCond : δ
  /-- Dynamic-tautology half (m ∪ ¬m), introduces drefs in either horn. -/
  tautology : δ

namespace GothamLift

variable {δ : Type u} [DynamicSubstrate δ] [DynamicProgramDisj δ]

instance instDNELift : DNELift δ (GothamLift δ) where
  up m :=
    ⟨DynamicSubstrate.neg (DynamicSubstrate.neg m),
     DynamicProgramDisj.pdisj m (DynamicSubstrate.neg m)⟩
  down M := DynamicSubstrate.conj M.truthCond M.tautology
  invneg M := ⟨DynamicSubstrate.neg M.truthCond, M.tautology⟩

end GothamLift

-- ════════════════════════════════════════════════════════════════
-- § 12. Instance 3 — Staged updates (paper p. 868, Charlow's headline)
-- ════════════════════════════════════════════════════════════════

/-! ### Instance 3: Staged updates (Charlow 2025)

`Δ ::= (i → Prop) × δ` (pairs of static propositional content and updates).
The lift `m^↑ := (True_δ(m), m ∪ ¬_δ m)` decomposes a δ-meaning into its
truth-conditional content plus a dynamic tautology. `down` reconstitutes by
restriction; `invneg` flips the static-proposition half.

Like Gotham, the full `IsLawfulDNELift` instance is **not declared** here —
the laws hold over the DPL substrate (paper p. 868) but require unfolding
`truth`, `restrict`, and `pdisj` definitions. Future PR for Mandelkern2022
or Charlow's own §6 will add the DPL-specific lawfulness proof. -/

/-- **Instance 3's carrier**: pairs of static propositions and updates. -/
structure StagedLift (δ : Type u) (i : Type v) where
  /-- Static propositional content (`True_δ(m)` shape). -/
  staticContent : i → Prop
  /-- Update component carrying the dynamic tautology. -/
  update : δ

namespace StagedLift

variable {δ : Type u} {i : Type v}
  [DynamicSubstrate δ] [DynamicProgramDisj δ] [DynamicTruth δ i]

instance instDNELift : DNELift δ (StagedLift δ i) where
  up m :=
    ⟨DynamicTruth.truth m,
     DynamicProgramDisj.pdisj m (DynamicSubstrate.neg m)⟩
  down M := DynamicTruth.restrict M.update M.staticContent
  invneg M := ⟨fun x => ¬ M.staticContent x, M.update⟩

end StagedLift

-- ════════════════════════════════════════════════════════════════
-- § 13. Instance 4 — Canonical (paper p. 868, Fact 3)
-- ════════════════════════════════════════════════════════════════

/-! ### Instance 4: Canonical Δ = Bool × δ (Fact 3, p. 868)

The minimal/canonical lift: tag each substrate value with a Boolean
indicating whether to apply ¬_δ on lowering. Generic over any
`DynamicSubstrate` — no program disjunction or truth needed.

`m^↑ := (true, m)`; `(b, m)^↓ := if b then m else ¬_δ m`; `∼(b, m) := (¬b, m)`.
All three laws hold by case analysis on the Bool. Lawful in full generality;
unique among the four instances in being so. -/

/-- **Instance 4's carrier**: pairs of booleans and updates. -/
structure CanonicalLift (δ : Type u) where
  /-- Polarity flag: `true` means "apply m as-is", `false` means "negate m". -/
  flag : Bool
  /-- The underlying substrate update. -/
  update : δ

namespace CanonicalLift

variable {δ : Type u} [DynamicSubstrate δ]

instance instDNELift : DNELift δ (CanonicalLift δ) where
  up m := ⟨true, m⟩
  down M := if M.flag then M.update else DynamicSubstrate.neg M.update
  invneg M := ⟨!M.flag, M.update⟩

instance instIsLawfulDNELift : IsLawfulDNELift δ (CanonicalLift δ) where
  down_up _ := rfl
  invneg_invneg M := by
    show CanonicalLift.mk (!(!M.flag)) M.update = M
    cases M with
    | mk b _ => cases b <;> rfl
  down_invneg_up _ := rfl

end CanonicalLift

-- ════════════════════════════════════════════════════════════════
-- § 14. Sanity tests over a concrete DPL substrate
-- ════════════════════════════════════════════════════════════════

section Tests

/-- The KM lift over `DPLRel Bool` satisfies all three laws — confirmed via
typeclass synthesis. -/
example : IsLawfulDNELift (DPLRel Bool) (KMLift (DPLRel Bool)) :=
  KMLift.instIsLawfulDNELift

/-- The Canonical lift over `DPLRel Bool` satisfies all three laws. -/
example : IsLawfulDNELift (DPLRel Bool) (CanonicalLift (DPLRel Bool)) :=
  CanonicalLift.instIsLawfulDNELift

/-- DNE holds in the KM lifted interpretation: `⟨¬¬φ⟩ = ⟨φ⟩`. Demonstrates
Fact 1 over a concrete substrate (KMLift over DPLRel Bool). -/
example (ia : Unit → DPLRel Bool) (ie : Nat → DPLRel Bool)
        (φ : DynForm Unit) :
    (liftInterp (Δ := KMLift (DPLRel Bool)) ia ie (.neg (.neg φ))) =
    liftInterp ia ie φ :=
  liftInterp_dneg ia ie φ

/-- DNE holds in the Canonical lifted interpretation: `⟨¬¬φ⟩ = ⟨φ⟩`. -/
example (ia : Unit → DPLRel Bool) (ie : Nat → DPLRel Bool)
        (φ : DynForm Unit) :
    (liftInterp (Δ := CanonicalLift (DPLRel Bool)) ia ie (.neg (.neg φ))) =
    liftInterp ia ie φ :=
  liftInterp_dneg ia ie φ

end Tests

end Charlow2025
