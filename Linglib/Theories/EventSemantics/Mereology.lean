/-
# Algebraic Event Mereology

Champollion (2017) *Parts of a Whole* algebraic mereology formalized over
Mathlib's `SemilatticeSup` (binary join = mereological sum ⊕) and
`PartialOrder` (part-of = ≤). Abstract definitions (CUM, DIV, QUA,
AlgClosure) are polymorphic over any semilattice, then specialized to events.

## Sections

1. Algebraic Closure (*P)
2. Higher-Order Properties: CUM, DIV, QUA, Atom
3. Key Theorems (CUM/DIV/QUA interactions)
4. Sum Homomorphism
5. Event CEM (Classical Extensional Mereology enrichment)
6. Lexical Cumulativity
7. Role Homomorphism (θ preserves ⊕)
8. τ Homomorphism (runtime preserves ⊕)
9. Bridges to existing types
10. Overlap and Extensive Measures (Krifka 1998 §2.2)
11. QMOD: Quantizing Modification (Krifka 1989)

## References

- Champollion, L. (2017). *Parts of a Whole: Distributivity as a Bridge
  Between Aspect and Measurement*. OUP.
- Bach, E. (1986). The algebra of events.
- Krifka, M. (1989). Nominal reference, temporal constitution and
  quantification in event semantics.
-/

import Mathlib.Data.Rat.Defs
import Mathlib.Order.Lattice
import Mathlib.Order.Basic
import Linglib.Theories.EventSemantics.Basic
import Linglib.Theories.TruthConditional.Verb.Aspect

namespace EventSemantics.Mereology

open EventSemantics
open TruthConditional.Core.Time
open TruthConditional.Verb.Aspect

-- ════════════════════════════════════════════════════
-- § 1. Algebraic Closure (*P)
-- ════════════════════════════════════════════════════

/-- Algebraic closure of a predicate P under join (⊔):
    *P is the smallest set containing P and closed under ⊔.
    Corresponds to Champollion (2017) Ch. 2, §2.3.4. -/
inductive AlgClosure {α : Type*} [SemilatticeSup α] (P : α → Prop) : α → Prop where
  /-- Base case: everything in P is in *P. -/
  | base {x : α} : P x → AlgClosure P x
  /-- Closure: if x, y ∈ *P then x ⊔ y ∈ *P. -/
  | sum {x y : α} : AlgClosure P x → AlgClosure P y → AlgClosure P (x ⊔ y)

-- ════════════════════════════════════════════════════
-- § 2. Higher-Order Mereological Properties
-- ════════════════════════════════════════════════════

/-- Cumulative reference (CUM): P is closed under join.
    Champollion (2017) §2.3.2: CUM(P) ⇔ ∀x,y. P(x) ∧ P(y) → P(x ⊕ y).
    Activities and states are canonically cumulative. -/
def CUM {α : Type*} [SemilatticeSup α] (P : α → Prop) : Prop :=
  ∀ (x y : α), P x → P y → P (x ⊔ y)

/-- Divisive reference (DIV): P is closed downward under ≤.
    Champollion (2017) §2.3.3: DIV(P) ⇔ ∀x,y. P(x) ∧ y ≤ x → P(y).
    This is the mereological analog of the subinterval property. -/
def DIV {α : Type*} [PartialOrder α] (P : α → Prop) : Prop :=
  ∀ (x y : α), P x → y ≤ x → P y

/-- Quantized reference (QUA): no proper part of a P-entity is also P.
    Champollion (2017) §2.3.5: QUA(P) ⇔ ∀x,y. P(x) ∧ y < x → ¬P(y).
    Telic predicates are canonically quantized. -/
def QUA {α : Type*} [PartialOrder α] (P : α → Prop) : Prop :=
  ∀ (x y : α), P x → y < x → ¬ P y

/-- Mereological atom: x has no proper part.
    Champollion (2017) §2.2: Atom(x) ⇔ ¬∃y. y < x.
    Defined without OrderBot since events lack a natural bottom element. -/
def Atom {α : Type*} [PartialOrder α] (x : α) : Prop :=
  ∀ (y : α), y ≤ x → y = x

-- ════════════════════════════════════════════════════
-- § 3. Key Theorems
-- ════════════════════════════════════════════════════

/-- *P is always cumulative (Champollion 2017, §2.3.4).
    This is the fundamental property of algebraic closure. -/
theorem algClosure_cum {α : Type*} [SemilatticeSup α]
    {P : α → Prop} : CUM (AlgClosure P) :=
  λ _ _ hx hy => AlgClosure.sum hx hy

/-- P ⊆ *P: algebraic closure extends the original predicate. -/
theorem subset_algClosure {α : Type*} [SemilatticeSup α]
    {P : α → Prop} {x : α} (h : P x) :
    AlgClosure P x :=
  AlgClosure.base h

/-- QUA predicates cannot be cumulative (for predicates with ≥ 2 elements).
    Champollion (2017) §2.3.5: QUA and CUM are incompatible for non-singletons. -/
theorem qua_cum_incompatible {α : Type*} [SemilatticeSup α]
    {P : α → Prop} (hQ : QUA P)
    {x y : α} (hx : P x) (hy : P y) (hne : x ≠ y) :
    ¬ CUM P := by
  intro hC
  have hxy := hC x y hx hy
  have hle : x ≤ x ⊔ y := le_sup_left
  by_cases heq : x = x ⊔ y
  · -- If x = x ⊔ y, then y ≤ x, and x ≤ y, so x = y
    have hle' : y ≤ x ⊔ y := le_sup_right
    rw [← heq] at hle'
    -- heq : x = x ⊔ y means y ≤ x
    have : y ≤ x := heq ▸ le_sup_right
    -- hle : x ≤ x ⊔ y = x, so x ≤ x (trivial), but also x ⊔ y = x means x ≤ y?
    -- Actually: sup_eq_left : x ⊔ y = x ↔ y ≤ x (wrong direction, need sup_eq_right)
    -- heq says x = x ⊔ y. We need to show x = y.
    -- We have y ≤ x from above. We also need x ≤ y.
    -- From hQ: QUA says P (x ⊔ y) ∧ x < (x ⊔ y) → ¬P x
    -- Since x = x ⊔ y, x is not strictly less than x ⊔ y.
    -- So y ≤ x. And similarly y = y ⊔ x...
    -- Simpler: since y ≤ x and y ≠ x, we have y < x.
    -- QUA gives: P x → y < x → ¬P y. But P y = hy. Contradiction.
    by_cases hyx : y = x
    · exact hne hyx.symm
    · have hlt : y < x := lt_of_le_of_ne this hyx
      exact hQ x y hx hlt hy
  · -- x < x ⊔ y, so QUA gives ¬P(x), contradiction
    have hlt : x < x ⊔ y := lt_of_le_of_ne hle heq
    exact hQ (x ⊔ y) x hxy hlt hx

/-- Atoms are trivially quantized: the singleton {x} is QUA when x is an atom. -/
theorem atom_qua {α : Type*} [PartialOrder α]
    {x : α} (hAtom : Atom x) : QUA (· = x) := by
  intro a b ha hlt hn
  subst ha; subst hn
  exact absurd (hAtom b (le_of_lt hlt)) (ne_of_lt hlt).symm

/-- DIV allows extracting parts: if P is DIV and P(z), then P(w) for any w ≤ z. -/
theorem div_closed_under_le {α : Type*} [PartialOrder α]
    {P : α → Prop}
    (hDiv : DIV P)
    {z : α} (hz : P z) {w : α} (hle : w ≤ z) :
    P w :=
  hDiv z w hz hle

-- ════════════════════════════════════════════════════
-- § 4. Sum Homomorphism
-- ════════════════════════════════════════════════════

/-- A sum homomorphism preserves the join operation.
    Champollion (2017) §2.5: thematic roles and τ are sum homomorphisms.
    f(x ⊕ y) = f(x) ⊕ f(y). -/
class IsSumHom {α β : Type*} [SemilatticeSup α] [SemilatticeSup β]
    (f : α → β) : Prop where
  /-- f preserves binary join. -/
  map_sup : ∀ (x y : α), f (x ⊔ y) = f x ⊔ f y

/-- Sum homomorphisms are order-preserving (monotone).
    If x ≤ y then f(x) ≤ f(y). -/
theorem IsSumHom.monotone {α β : Type*}
    [SemilatticeSup α] [SemilatticeSup β]
    {f : α → β} (hf : IsSumHom f) :
    Monotone f := by
  intro x y hle
  have : x ⊔ y = y := sup_eq_right.mpr hle
  calc f x ≤ f x ⊔ f y := le_sup_left
    _ = f (x ⊔ y) := (hf.map_sup x y).symm
    _ = f y := by rw [this]

/-- Sum homomorphisms preserve CUM: if P is CUM then P ∘ f⁻¹ is CUM.
    More precisely: if P is CUM then (fun x => P (f x)) is CUM. -/
theorem IsSumHom.cum_preimage {α β : Type*}
    [SemilatticeSup α] [SemilatticeSup β]
    {f : α → β} (hf : IsSumHom f)
    {P : β → Prop} (hCum : CUM P) :
    CUM (P ∘ f) := by
  intro x y hx hy
  simp only [Function.comp] at *
  rw [hf.map_sup]
  exact hCum _ _ hx hy

-- ════════════════════════════════════════════════════
-- § 5. Event CEM (Classical Extensional Mereology)
-- ════════════════════════════════════════════════════

/-- Classical Extensional Mereology for events: enriches `EventMereology`
    with binary sum (⊔) via `SemilatticeSup (Ev Time)`.
    Champollion (2017) Ch. 2: event domain forms a join semilattice. -/
class EventCEM (Time : Type*) [LinearOrder Time]
    extends EventMereology Time where
  /-- Events form a join semilattice (binary sum ⊕ exists). -/
  evSemilatticeSup : SemilatticeSup (Ev Time)
  /-- ≤ from SemilatticeSup agrees with partOf. -/
  le_eq_partOf : ∀ (e₁ e₂ : Ev Time),
    @LE.le (Ev Time) evSemilatticeSup.toLE e₁ e₂ ↔ partOf e₁ e₂
  /-- Intervals form a join semilattice (for τ homomorphism). -/
  intervalSemilatticeSup : SemilatticeSup (Interval Time)
  /-- τ is a sum homomorphism: τ(e₁ ⊕ e₂) = τ(e₁) ⊕ τ(e₂).
      Champollion (2017) §2.5.1. -/
  τ_hom : ∀ (e₁ e₂ : Ev Time),
    (@SemilatticeSup.sup _ evSemilatticeSup e₁ e₂).runtime =
     @SemilatticeSup.sup _ intervalSemilatticeSup e₁.runtime e₂.runtime

-- Provide the SemilatticeSup instance from EventCEM
noncomputable instance eventCEMSemilatticeSup (Time : Type*) [LinearOrder Time]
    [cem : EventCEM Time] : SemilatticeSup (Ev Time) :=
  cem.evSemilatticeSup

-- ════════════════════════════════════════════════════
-- § 6. Lexical Cumulativity
-- ════════════════════════════════════════════════════

/-- Lexical cumulativity for event predicates: the event-specific
    instantiation of CUM. A verb predicate V is lexically cumulative
    iff for any two V-events, their sum is also a V-event.
    Champollion (2017) §3.2: activities and states are lexically cumulative. -/
def LexCum (Time : Type*) [LinearOrder Time] [cem : EventCEM Time]
    (P : EvPred Time) : Prop :=
  ∀ (e₁ e₂ : Ev Time), P e₁ → P e₂ →
    P (@SemilatticeSup.sup _ cem.evSemilatticeSup e₁ e₂)

/-- LexCum is exactly CUM specialized to EvPred.
    This bridges the abstract and event-specific formulations. -/
theorem cum_iff_lexCum (Time : Type*) [LinearOrder Time] [cem : EventCEM Time]
    (P : EvPred Time) :
    @CUM _ cem.evSemilatticeSup P ↔ LexCum Time P := by
  constructor
  · intro h e₁ e₂ h₁ h₂; exact h e₁ e₂ h₁ h₂
  · intro h x y hx hy; exact h x y hx hy

-- ════════════════════════════════════════════════════
-- § 7. Role Homomorphism (θ preserves ⊕)
-- ════════════════════════════════════════════════════

/-- A thematic-role sum homomorphism: the function mapping each event
    to its θ-role filler preserves ⊕.
    Champollion (2017) §2.5.1 eq. 34–35: Agent(e₁ ⊕ e₂) = Agent(e₁) ⊕ Agent(e₂).

    This is stated as: given a function `θ : Ev Time → Entity` extracting
    the unique role-filler, θ is a sum homomorphism. -/
class RoleHom (Entity Time : Type*) [LinearOrder Time] [cem : EventCEM Time]
    [SemilatticeSup Entity] where
  /-- Agent extraction function (partial: only defined for events with agents). -/
  agentOf : Ev Time → Entity
  /-- Agent extraction preserves ⊕. -/
  agent_hom : @IsSumHom _ _ cem.evSemilatticeSup _ agentOf
  /-- Patient extraction function. -/
  patientOf : Ev Time → Entity
  /-- Patient extraction preserves ⊕. -/
  patient_hom : @IsSumHom _ _ cem.evSemilatticeSup _ patientOf
  /-- Theme extraction function. -/
  themeOf : Ev Time → Entity
  /-- Theme extraction preserves ⊕. -/
  theme_hom : @IsSumHom _ _ cem.evSemilatticeSup _ themeOf

-- ════════════════════════════════════════════════════
-- § 8. τ Homomorphism
-- ════════════════════════════════════════════════════

/-- τ is a sum homomorphism: follows directly from EventCEM.τ_hom.
    τ(e₁ ⊕ e₂) = τ(e₁) ⊕ τ(e₂).
    Champollion (2017) §2.5.1: the runtime function preserves sums. -/
theorem τ_is_sum_hom (Time : Type*) [LinearOrder Time] [cem : EventCEM Time] :
    ∀ (e₁ e₂ : Ev Time),
      (@SemilatticeSup.sup _ cem.evSemilatticeSup e₁ e₂).runtime =
      @SemilatticeSup.sup _ cem.intervalSemilatticeSup e₁.runtime e₂.runtime :=
  cem.τ_hom

-- ════════════════════════════════════════════════════
-- § 9. Bridges to Existing Types
-- ════════════════════════════════════════════════════

/-- Atelic Vendler classes yield predicates that are naturally cumulative
    (Champollion 2017, §3.2). States and activities have the subinterval
    property, which entails CUM for their event predicates. -/
theorem vendlerClass_atelic_implies_cum_intent
    (c : VendlerClass) (h : c.telicity = .atelic) :
    c = .state ∨ c = .activity := by
  cases c <;> simp [VendlerClass.telicity] at h <;> try exact Or.inl rfl
  · exact Or.inr rfl

/-- Telic Vendler classes yield predicates that are naturally quantized
    (Champollion 2017, §3.3). Achievements and accomplishments lack
    the subinterval property, corresponding to QUA. -/
theorem vendlerClass_telic_implies_qua_intent
    (c : VendlerClass) (h : c.telicity = .telic) :
    c = .achievement ∨ c = .accomplishment := by
  cases c <;> simp [VendlerClass.telicity] at h
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- CUM and QUA partition event predicates (for non-trivial predicates):
    a predicate with ≥ 2 distinct elements cannot be both CUM and QUA.
    Champollion (2017) §2.3.5. -/
theorem cum_qua_disjoint {α : Type*} [SemilatticeSup α]
    {P : α → Prop}
    (hne : ∃ (x y : α), P x ∧ P y ∧ x ≠ y) :
    ¬ (CUM P ∧ QUA P) := by
  intro ⟨hC, hQ⟩
  obtain ⟨x, y, hpx, hpy, hxy⟩ := hne
  exact qua_cum_incompatible hQ hpx hpy hxy hC

/-- AlgClosure preserves membership: if P x, then AlgClosure P x. -/
theorem algClosure_of_mem {α : Type*} [SemilatticeSup α]
    {P : α → Prop} {x : α} (h : P x) : AlgClosure P x :=
  AlgClosure.base h

/-- AlgClosure is monotone: P ⊆ Q implies *P ⊆ *Q. -/
theorem algClosure_mono {α : Type*} [SemilatticeSup α]
    {P Q : α → Prop} (h : ∀ (x : α), P x → Q x) :
    ∀ (x : α), AlgClosure P x → AlgClosure Q x := by
  intro x hx
  induction hx with
  | base hp => exact AlgClosure.base (h _ hp)
  | sum _ _ ih₁ ih₂ => exact AlgClosure.sum ih₁ ih₂

/-- AlgClosure is idempotent: *(∗P) = *P. -/
theorem algClosure_idempotent {α : Type*} [SemilatticeSup α]
    {P : α → Prop} :
    ∀ (x : α), AlgClosure (AlgClosure P) x → AlgClosure P x := by
  intro x hx
  induction hx with
  | base hp => exact hp
  | sum _ _ ih₁ ih₂ => exact AlgClosure.sum ih₁ ih₂

-- ════════════════════════════════════════════════════
-- § 10. Overlap and Extensive Measures (Krifka 1998 §2.2)
-- ════════════════════════════════════════════════════

/-- Mereological overlap: x and y share a common part.
    Krifka (1998) eq. (1e): O(x, y) ⇔ ∃z. z ≤ x ∧ z ≤ y. -/
def Overlap {γ : Type*} [PartialOrder γ] (x y : γ) : Prop :=
  ∃ z, z ≤ x ∧ z ≤ y

/-- Extensive measure function: additive over non-overlapping entities.
    Krifka (1998) §2.2, eq. (7): μ(x ⊕ y) = μ(x) + μ(y) when ¬O(x,y).
    Examples: weight, volume, number (cardinality). -/
class ExtMeasure (α : Type*) [SemilatticeSup α]
    (μ : α → ℚ) : Prop where
  /-- Additivity: μ is additive over non-overlapping entities. -/
  additive : ∀ (x y : α), ¬ Overlap x y → μ (x ⊔ y) = μ x + μ y
  /-- Positivity: every entity has positive measure. -/
  positive : ∀ (x : α), 0 < μ x
  /-- Strict monotonicity: proper parts have strictly smaller measure.
      In a CEM with complementation, this follows from additivity + positivity:
      y < x implies x = y ⊔ z with ¬O(y,z), so μ(x) = μ(y) + μ(z) > μ(y).
      We axiomatize it directly since `SemilatticeSup` lacks complementation. -/
  strict_mono : ∀ (x y : α), y < x → μ y < μ x

/-- Measure phrases create QUA predicates: {x : μ(x) = n} is QUA
    whenever μ is an extensive measure.
    Krifka (1998) §2.2: "two kilograms of flour" is QUA because
    no proper part of a 2kg entity also weighs 2kg. -/
theorem extMeasure_qua {α : Type*} [SemilatticeSup α]
    {μ : α → ℚ} [hμ : ExtMeasure α μ] (n : ℚ) (_hn : 0 < n) :
    QUA (fun x => μ x = n) := by
  intro x y hx hlt hy
  have hsm := hμ.strict_mono x y hlt
  rw [hy, hx] at hsm
  exact absurd hsm (Rat.not_lt.mpr Rat.le_refl)

-- ════════════════════════════════════════════════════
-- § 11. QMOD: Quantizing Modification (Krifka 1989)
-- ════════════════════════════════════════════════════

/-- Quantizing modification: intersect predicate R with a measure constraint.
    Krifka (1989): QMOD(R, μ, n) = λx. R(x) ∧ μ(x) = n.
    "three kilos of rice" = QMOD(rice, μ_kg, 3).
    This is the operation that turns a CUM mass noun into a QUA measure phrase. -/
def QMOD {α μTy : Type*} (R : α → Prop) (μ : α → μTy) (n : μTy) : α → Prop :=
  λ x => R x ∧ μ x = n

/-- QMOD(R, μ, n) ⊆ R: quantizing modification restricts the base predicate. -/
theorem qmod_sub {α μTy : Type*} {R : α → Prop} {μ : α → μTy} {n : μTy}
    {x : α} (h : QMOD R μ n x) : R x :=
  h.1

end EventSemantics.Mereology
