import Mathlib.Order.Lattice
import Mathlib.Order.Monotone.Defs
import Mathlib.Order.Sublattice
import Linglib.Core.Logic.NaturalLogic
import Linglib.Tactics.OntSort

/-!
# Generalized Quantifier Properties
@cite{barwise-cooper-1981} @cite{elliott-2025} @cite{keenan-stavi-1986} @cite{peters-westerstahl-2006} @cite{van-benthem-1984}

Model-agnostic properties of generalized quantifier denotations.

A GQ denotation is a function `(α → Bool) → (α → Bool) → Bool` mapping
a restrictor and a scope to a truth value. The properties defined here
(conservativity, monotonicity, duality, intersection condition, symmetry)
are purely logical — they hold at the `Bool`-function level and require
no model infrastructure.

The theory-specific module `Semantics.Lexical.Determiner.Quantifier` defines
concrete denotations (`every_sem`, `some_sem`, etc.) and proves they satisfy
these properties. `m.interpTy Ty.det` is definitionally `GQ m.Entity`, so
all definitions here apply directly.

## Organization

- **§1 Property definitions**: all predicates on GQs, grouped by source
- **§2 Operations**: duality, Boolean algebra, type shifts
- **§3 Mathlib bridge**: connection to `Monotone`/`Antitone`
- **§4–§8 Theorems**: duality, symmetry/strength, Boolean closure,
  type ⟨1⟩, van Benthem characterization
- **§5b Basic left monotonicity**: persistence decomposition (Prop 6),
  negation rotation (Prop 8), smooth→Mon↑ (Prop 9), symmetry (Prop 7)
- **§12 Conservative GQ lattice**: `ConsGQ α` bounded distributive lattice

-/

namespace Core.Quantification

/-- Generalized quantifier denotation: restrictor → scope → truth value. -/
@[ont_sort] abbrev GQ (α : Type*) := (α → Bool) → (α → Bool) → Bool

variable {α : Type*}

-- ============================================================================
-- §1 Property Definitions
-- ============================================================================

-- §1.1 @cite{barwise-cooper-1981} --

/--
Conservativity: `Q(A, B) = Q(A, A ∩ B)`.

Only the elements of B that are also in A matter for the quantifier's
truth value. Also called "lives on" (B&C) or "intersectivity". All simple (lexicalized) determiners
are conservative.
-/
def Conservative (q : GQ α) : Prop :=
  ∀ (R S : α → Bool), q R S = q R (λ x => R x && S x)

/--
Scope-upward-monotone: if B ⊆ B' and Q(A,B), then Q(A,B').

Equivalent to `∀ R, Monotone (q R)` under pointwise Bool ordering
(see `scopeUpMono_iff_monotone`). This connects to
`Semantics.Entailment.Polarity.IsUpwardEntailing = Monotone`.
-/
def ScopeUpwardMono (q : GQ α) : Prop :=
  ∀ (R S S' : α → Bool),
    (∀ x, S x = true → S' x = true) →
    q R S = true → q R S' = true

/--
Scope-downward-monotone: if B ⊆ B' and Q(A,B'), then Q(A,B).

Equivalent to `∀ R, Antitone (q R)` under pointwise Bool ordering
(see `scopeDownMono_iff_antitone`).
-/
def ScopeDownwardMono (q : GQ α) : Prop :=
  ∀ (R S S' : α → Bool),
    (∀ x, S x = true → S' x = true) →
    q R S' = true → q R S = true

/-- Intersection condition: Q(A,B) depends only on A∩B. B&C §4.8, p.189. -/
def IntersectionCondition (q : GQ α) : Prop :=
  ∀ (R S R' S' : α → Bool),
    (∀ x, (R x && S x) = (R' x && S' x)) →
    q R S = q R' S'

/-- Symmetric: Q(A,B) = Q(B,A). B&C p.210; equivalent to intersection condition by Theorem C5. -/
def QSymmetric (q : GQ α) : Prop :=
  ∀ (R S : α → Bool), q R S = q S R

/-- Restrictor-upward-monotone (persistent): if A ⊆ A' then Q(A,B) → Q(A',B).
    Linked to weak determiners and there-insertion. B&C §4.9, p.193. -/
def RestrictorUpwardMono (q : GQ α) : Prop :=
  ∀ (R R' S : α → Bool),
    (∀ x, R x = true → R' x = true) →
    q R S = true → q R' S = true

/-- Restrictor-downward-monotone (anti-persistent). -/
def RestrictorDownwardMono (q : GQ α) : Prop :=
  ∀ (R R' S : α → Bool),
    (∀ x, R x = true → R' x = true) →
    q R' S = true → q R S = true

/-- Positive strong: Q(A,A) for all A. P&W Ch.6: "every", "most", "the". -/
def PositiveStrong (q : GQ α) : Prop :=
  ∀ (R : α → Bool), q R R = true

/-- Negative strong: ¬Q(A,A) for all A. "Neither". -/
def NegativeStrong (q : GQ α) : Prop :=
  ∀ (R : α → Bool), q R R = false

-- §1.2 @cite{peters-westerstahl-2006} --

/-- Extension (EXT): Q(A,B) depends only on A and B, not on the ambient
    universe M. In model-theoretic GQ theory (where Q^M takes a universe),
    EXT must be stated as an additional axiom. For `GQ α`, EXT holds
    trivially since there is no universe parameter — it's a design theorem.

    Significance: EXT + CONS characterize "well-behaved" determiners. See `vanBenthem_cons_ext`.

    Reference: Peters & Westerståhl Ch.4 Def 4.1. -/
def Extension (_q : GQ α) : Prop := True

/-- Second conservativity: Q(A,B) = Q(A∩B, B). P&W Ch.6. -/
def CONS2 (q : GQ α) : Prop :=
  ∀ (R S : α → Bool), q R S = q (λ x => R x && S x) S

/-- Existential property: Q(A,B) = Q(A∩B, everything). P&W Ch.6.
    Characterizes determiners that are felicitous in there-sentences. -/
def Existential (q : GQ α) : Prop :=
  ∀ (R S : α → Bool), q R S = q (λ x => R x && S x) (λ _ => true)

/-- ↑_SE Mon (@cite{peters-westerstahl-2006} §5.5): Q(A,B) & A⊆A' & A\B=A'\B → Q(A',B).
    On the number triangle: if Q(k,m) then Q(k',m) for k' ≥ k.
    Enlarging A by adding elements of B preserves Q. -/
def UpSEMon (q : GQ α) : Prop :=
  ∀ (R S R' : α → Bool),
    (∀ x, R x = true → R' x = true) →
    (∀ x, R' x = true → S x = false → R x = true) →
    q R S = true → q R' S = true

/-- ↑_SW Mon (@cite{peters-westerstahl-2006} §5.5): Q(A,B) & A⊆A' & A∩B=A'∩B → Q(A',B).
    On the number triangle: if Q(k,m) then Q(k,m') for m' ≥ m.
    Enlarging A by adding elements outside B preserves Q.
    This is property (p) from P&W §5.2: half of the EXT condition. -/
def UpSWMon (q : GQ α) : Prop :=
  ∀ (R S R' : α → Bool),
    (∀ x, R x = true → R' x = true) →
    (∀ x, R' x = true → S x = true → R x = true) →
    q R S = true → q R' S = true

/-- ↓_NW Mon (@cite{peters-westerstahl-2006} §5.5): Q(A,B) & A'⊆A & A\B=A'\B → Q(A',B).
    On the number triangle: if Q(k,m) then Q(k',m) for k' ≤ k.
    Shrinking A by removing elements of B preserves Q. -/
def DownNWMon (q : GQ α) : Prop :=
  ∀ (R S R' : α → Bool),
    (∀ x, R' x = true → R x = true) →
    (∀ x, R x = true → S x = false → R' x = true) →
    q R S = true → q R' S = true

/-- ↓_NE Mon (@cite{peters-westerstahl-2006} §5.5): Q(A,B) & A'⊆A & A∩B=A'∩B → Q(A',B).
    On the number triangle: if Q(k,m) then Q(k,m') for m' ≤ m.
    Shrinking A by removing elements outside B preserves Q. -/
def DownNEMon (q : GQ α) : Prop :=
  ∀ (R S R' : α → Bool),
    (∀ x, R' x = true → R x = true) →
    (∀ x, R x = true → S x = true → R' x = true) →
    q R S = true → q R' S = true

/-- Smooth (@cite{peters-westerstahl-2006} §5.6): Q is ↓_NE Mon and ↑_SE Mon.
    Smooth quantifiers are Mon↑ (Prop 9). Under ISOM, smooth quantifiers
    have smooth monotonicity functions f where f(n) ≤ f(n+1) ≤ f(n)+1 (Prop 10).
    Most natural language Mon↑ determiners are smooth: all proportional
    quantifiers, "some", "all", "most", etc. -/
def Smooth (q : GQ α) : Prop := DownNEMon q ∧ UpSEMon q

/-- Co-smooth (@cite{peters-westerstahl-2006} §5.6): Q's inner negation is smooth.
    Equivalently, ↓_NW Mon and ↑_SW Mon. "no" and "fewer than half" are co-smooth. -/
def CoSmooth (q : GQ α) : Prop := DownNWMon q ∧ UpSWMon q

/-- Left anti-additive: Q(A∪B, C) ↔ Q(A,C) ∧ Q(B,C). P&W §5.9. -/
def LeftAntiAdditive (q : GQ α) : Prop :=
  ∀ (R R' S : α → Bool),
    q (λ x => R x || R' x) S = (q R S && q R' S)

/-- Right anti-additive: Q(A, B∪C) ↔ Q(A,B) ∧ Q(A,C). P&W §5.9. -/
def RightAntiAdditive (q : GQ α) : Prop :=
  ∀ (R S S' : α → Bool),
    q R (λ x => S x || S' x) = (q R S && q R S')

-- §1.3 @cite{van-benthem-1984}: Relational properties --

/-- Transitive: Q(A,B) ∧ Q(B,C) → Q(A,C). @cite{van-benthem-1984} §3.1.
    "all" is the prime transitive quantifier (inclusion is transitive). -/
def QTransitive (q : GQ α) : Prop :=
  ∀ (A B C : α → Bool), q A B = true → q B C = true → q A C = true

/-- Antisymmetric: Q(A,B) ∧ Q(B,A) → A = B (extensionally).
    @cite{van-benthem-1984} §3.1: "all" (inclusion) is antisymmetric. -/
def QAntisymmetric (q : GQ α) : Prop :=
  ∀ (A B : α → Bool), q A B = true → q B A = true → A = B

/-- Linear (connected): Q(A,B) ∨ Q(B,A) for all A, B.
    @cite{van-benthem-1984} §3.1: "not all" (non-inclusion) is linear. -/
def QLinear (q : GQ α) : Prop :=
  ∀ (A B : α → Bool), q A B = true ∨ q B A = true

/-- Quasi-reflexive: Q(A,B) → Q(A,A). @cite{van-benthem-1984} §3.1.
    "some" is quasi-reflexive: overlap implies non-emptiness. -/
def QuasiReflexive (q : GQ α) : Prop :=
  ∀ (A B : α → Bool), q A B = true → q A A = true

/-- Quasi-universal: Q(A,A) → Q(A,B) for all B. @cite{van-benthem-1984} §3.1.
    "no" is quasi-universal: if A∩A = ∅ then A∩B = ∅ for all B. -/
def QuasiUniversal (q : GQ α) : Prop :=
  ∀ (A B : α → Bool), q A A = true → q A B = true

/-- Almost-connected: Q(A,B) → Q(A,C) ∨ Q(C,B) for all C.
    @cite{van-benthem-1984} §3.1: equivalent to transitivity of ¬Q.
    "not all" is almost-connected. -/
def AlmostConnected (q : GQ α) : Prop :=
  ∀ (A B C : α → Bool), q A B = true → q A C = true ∨ q C B = true

/-- VAR (Variety): Q is non-trivial — it both accepts and rejects some pair.
    @cite{van-benthem-1984} §2: rules out degenerate quantifiers like "at least 2"
    on singleton domains. Used as hypothesis in most uniqueness theorems. -/
def Variety (q : GQ α) : Prop :=
  (∃ A B, q A B = true) ∧ (∃ A B, q A B = false)

/-- Double monotonicity type (@cite{van-benthem-1984} §4.2).
    The logical Square of Opposition maps to four double-monotonicity types:
    all = ↓MON↑, some = ↑MON↑, no = ↓MON↓, not all = ↑MON↓. -/
inductive DoubleMono where
  | upUp     -- ↑MON↑: restrictor-↑ + scope-↑ (some)
  | downUp   -- ↓MON↑: restrictor-↓ + scope-↑ (all)
  | upDown   -- ↑MON↓: restrictor-↑ + scope-↓ (not all)
  | downDown -- ↓MON↓: restrictor-↓ + scope-↓ (no)
  deriving DecidableEq, Repr, BEq

/-- Right continuity (CONT): if Q(A,B₁) and Q(A,B₂) hold and B₁ ⊆ B ⊆ B₂,
    then Q(A,B). @cite{van-benthem-1984} §4.3: all right-monotone quantifiers are
    continuous. "precisely one" is continuous but non-monotone. -/
def RightContinuous (q : GQ α) : Prop :=
  ∀ (A B B₁ B₂ : α → Bool),
    (∀ x, B₁ x = true → B x = true) →
    (∀ x, B x = true → B₂ x = true) →
    q A B₁ = true → q A B₂ = true → q A B = true

/-- Filtrating: Q(A,B) ∧ Q(A,C) → Q(A, B∩C).
    @cite{van-benthem-1984} Thm 4.4.2: "all" is the only filtrating quantifier
    (under VAR*). This is because filtrating ↔ filter (closure under ∩),
    and only the principal filter at A (= inclusion) satisfies CONSERV. -/
def Filtrating (q : GQ α) : Prop :=
  ∀ (A B C : α → Bool),
    q A B = true → q A C = true → q A (λ x => B x && C x) = true

-- §1.4 @cite{mostowski-1957} --

/-- QUANT (Isomorphism closure): Q is invariant under permutations of the
    domain. Model-agnostic version: Q(A,B) depends only on the pointwise
    Boolean pattern, not on which specific elements satisfy A and B.

    This is the type ⟨1,1⟩ (binary) generalization of @cite{mostowski-1957}'s
    permutation invariance. Mostowski's original condition applies to type ⟨1⟩
    (unary) quantifiers; the extension to binary determiners is due to
    @cite{van-benthem-1984} (building on Lindström 1966).

    The model-specific version in `Semantics.Lexical.Determiner.Quantifier.Quantity`
    uses cardinalities directly, which requires `FiniteModel`. This version
    captures the same intuition without model infrastructure.

    @cite{van-benthem-1984} §2: CONSERV + QUANT together reduce Q's behavior to
    pairs (a, b) where a = |A \ B| and b = |A ∩ B|. -/
def QuantityInvariant (q : GQ α) : Prop :=
  ∀ (A B A' B' : α → Bool) (f : α → α),
    Function.Bijective f →
    (∀ x, A (f x) = A' x) → (∀ x, B (f x) = B' x) →
    q A B = q A' B'

-- ============================================================================
-- §2 Operations
-- ============================================================================

-- §2.1 Duality (B&C §4.11) --

/-- Outer negation: `(~Q)(A,B) = ¬Q(A,B)` (B&C §4.11).
    Example: ~every = not-every ("Not every student passed"). -/
def outerNeg (q : GQ α) : GQ α :=
  λ R S => !q R S

/-- Inner negation: `(Q~)(A,B) = Q(A, ¬B)` (B&C §4.11).
    Example: every~ = every...not ("Every student didn't pass"). -/
def innerNeg (q : GQ α) : GQ α :=
  λ R S => q R (λ x => !S x)

/-- Dual: `Q̌ = ~(Q~) = ¬Q(A, ¬B)` (B&C §4.11).
    Example: every̌ = some, somě = every. -/
def dualQ (q : GQ α) : GQ α :=
  outerNeg (innerNeg q)

-- §2.2 Boolean algebra (K&S §2.3) --

/-- Meet of two GQ denotations: (f ∧ g)(A,B) = f(A,B) ∧ g(A,B).
    K&S (20): conjunction of dets, e.g., "both John's and Mary's".
    Also: "between n and m" = (at least n) ∧ (at most m). -/
def gqMeet (f g : GQ α) : GQ α :=
  λ R S => f R S && g R S

/-- Join of two GQ denotations: (f ∨ g)(A,B) = f(A,B) ∨ g(A,B).
    K&S (24): disjunction of dets, e.g., "either John's or Mary's". -/
def gqJoin (f g : GQ α) : GQ α :=
  λ R S => f R S || g R S

/-- Restriction of a GQ by a restricting function (adjective/relative clause).
    K&S (66): h_f(s) = h(f(s)). In our representation, the adjective
    narrows the restrictor: "tall student" = student ∧ tall. -/
def adjRestrict (q : GQ α) (adj : α → Bool) : GQ α :=
  λ R S => q (λ x => R x && adj x) S

-- §2.3 Type ⟨1⟩ shifts (P&W Ch.2-3) --

/-- NP denotation (type ⟨1⟩): a property of properties.
    This is the model-agnostic version of `Ty.ett` from TypeShifting.lean.
    P&W §2.1: an NP like "every student" denotes a set of sets. -/
abbrev NPQ (α : Type*) := (α → Bool) → Bool

/-- Restriction: given a GQ Q and restrictor A, produce the type ⟨1⟩
    quantifier Q^[A] (P&W §3.2.2). `restrict Q A B = Q A B`. -/
def restrict (q : GQ α) (A : α → Bool) : NPQ α := q A

/-- A type ⟨1⟩ quantifier Q "lives on" A iff Q(B) = Q(A ∩ B) for all B.
    P&W §3.2.2: the restricted quantifier depends only on elements of A. -/
def LivesOn (Q : NPQ α) (A : α → Bool) : Prop :=
  ∀ B, Q B = Q (λ x => A x && B x)

/-- Montagovian individual: the type ⟨1⟩ quantifier I_a = {X : a ∈ X}.
    P&W §3.2.3: an entity lifts to the principal ultrafilter it generates. -/
def individual (a : α) : NPQ α := λ P => P a

-- ============================================================================
-- §3 Mathlib Bridge
-- ============================================================================

theorem bool_le_iff_imp (a b : Bool) : a ≤ b ↔ (a = true → b = true) := by
  cases a <;> cases b <;> decide

/-- `ScopeUpwardMono q` is `∀ R, Monotone (q R)` under pointwise Bool ordering.
    This bridges GQ-level monotonicity to Mathlib's `Monotone`, which is
    what `Polarity.lean` uses (`IsUpwardEntailing = Monotone`). -/
theorem scopeUpMono_iff_monotone (q : GQ α) :
    ScopeUpwardMono q ↔ ∀ R, Monotone (q R) := by
  unfold ScopeUpwardMono Monotone
  constructor
  · intro h R S S' hle
    rw [bool_le_iff_imp]
    exact h R S S' (λ x => (bool_le_iff_imp (S x) (S' x)).mp (hle x))
  · intro h R S S' hSS'
    exact (bool_le_iff_imp (q R S) (q R S')).mp
      (h R (λ x => (bool_le_iff_imp (S x) (S' x)).mpr (hSS' x)))

/-- `ScopeDownwardMono q` is `∀ R, Antitone (q R)` under pointwise Bool ordering. -/
theorem scopeDownMono_iff_antitone (q : GQ α) :
    ScopeDownwardMono q ↔ ∀ R, Antitone (q R) := by
  unfold ScopeDownwardMono Antitone
  constructor
  · intro h R a b hab
    rw [bool_le_iff_imp]
    exact h R a b (λ x => (bool_le_iff_imp (a x) (b x)).mp (hab x))
  · intro h R S S' hSS'
    exact (bool_le_iff_imp (q R S') (q R S)).mp
      (h R (λ x => (bool_le_iff_imp (S x) (S' x)).mpr (hSS' x)))

-- ============================================================================
-- §4 Duality Theorems
-- ============================================================================

/-- Outer negation reverses scope monotonicity: mon↑ → mon↓. B&C Theorem C9. -/
theorem outerNeg_up_to_down (q : GQ α)
    (h : ScopeUpwardMono q) : ScopeDownwardMono (outerNeg q) := by
  intro R S S' hSS' hNeg
  simp only [outerNeg] at *
  cases hqRS : q R S
  · rfl
  · have := h R S S' hSS' hqRS; simp [this] at hNeg

/-- Outer negation reverses scope monotonicity: mon↓ → mon↑. B&C Theorem C9. -/
theorem outerNeg_down_to_up (q : GQ α)
    (h : ScopeDownwardMono q) : ScopeUpwardMono (outerNeg q) := by
  intro R S S' hSS' hNeg
  simp only [outerNeg] at *
  cases hqRS' : q R S'
  · rfl
  · have := h R S S' hSS' hqRS'; simp [this] at hNeg

/-- Inner negation reverses scope monotonicity: mon↑ → mon↓ (B&C §4.11). -/
theorem innerNeg_up_to_down (q : GQ α)
    (h : ScopeUpwardMono q) : ScopeDownwardMono (innerNeg q) := by
  intro R S S' hSS' hInner
  simp only [innerNeg] at *
  apply h R (λ x => !S' x) (λ x => !S x)
  · intro x hx; cases hS : S x <;> simp_all
  · exact hInner

/-- Inner negation reverses scope monotonicity: mon↓ → mon↑ (B&C §4.11).
    Mirrors `innerNeg_up_to_down`. Proof: contrapose S⊆S' to ¬S'⊆¬S. -/
theorem innerNeg_down_to_up (q : GQ α)
    (h : ScopeDownwardMono q) : ScopeUpwardMono (innerNeg q) := by
  intro R S S' hSS' hInner
  simp only [innerNeg] at *
  apply h R (λ x => !S' x) (λ x => !S x)
  · intro x hx; cases hS : S x
    · rfl
    · simp [hSS' x hS] at hx
  · exact hInner

/-- Outer negation reverses restrictor monotonicity: mon↑ → mon↓. -/
theorem outerNeg_restrictorUp_to_down (q : GQ α)
    (h : RestrictorUpwardMono q) : RestrictorDownwardMono (outerNeg q) := by
  intro R R' S hRR' hNeg
  simp only [outerNeg] at *
  cases hqRS : q R S
  · rfl
  · have := h R R' S hRR' hqRS; simp [this] at hNeg

/-- Outer negation reverses restrictor monotonicity: mon↓ → mon↑. -/
theorem outerNeg_restrictorDown_to_up (q : GQ α)
    (h : RestrictorDownwardMono q) : RestrictorUpwardMono (outerNeg q) := by
  intro R R' S hRR' hNeg
  simp only [outerNeg] at *
  cases hqR'S : q R' S
  · rfl
  · have := h R R' S hRR' hqR'S; simp [this] at hNeg

/-- Outer negation is involutive: ~~Q = Q. -/
theorem outerNeg_involution (q : GQ α) : outerNeg (outerNeg q) = q := by
  funext R S; simp [outerNeg, Bool.not_not]

/-- Inner negation is involutive: Q~~ = Q. -/
theorem innerNeg_involution (q : GQ α) : innerNeg (innerNeg q) = q := by
  funext R S; simp [innerNeg, Bool.not_not]

/-- Dual is involutive: Q̌̌ = Q. -/
theorem dualQ_involution (q : GQ α) : dualQ (dualQ q) = q := by
  funext R S; simp [dualQ, outerNeg, innerNeg, Bool.not_not]

-- §2.4 QuantityInvariant closure --

/-- Outer negation preserves QuantityInvariant: if Q is bijection-invariant,
    so is ~Q. -/
theorem quantityInvariant_outerNeg (q : GQ α)
    (h : QuantityInvariant q) : QuantityInvariant (outerNeg q) := by
  intro A B A' B' f hBij hA hB
  simp only [outerNeg]
  rw [h A B A' B' f hBij hA hB]

/-- Inner negation preserves QuantityInvariant: if Q is bijection-invariant,
    so is Q~. -/
theorem quantityInvariant_innerNeg (q : GQ α)
    (h : QuantityInvariant q) : QuantityInvariant (innerNeg q) := by
  intro A B A' B' f hBij hA hB
  simp only [innerNeg]
  exact h A (λ x => !B x) A' (λ x => !B' x) f hBij hA
    (λ x => by simp only [Function.comp]; rw [hB x])

/-- Dual preserves QuantityInvariant. -/
theorem quantityInvariant_dualQ (q : GQ α)
    (h : QuantityInvariant q) : QuantityInvariant (dualQ q) :=
  quantityInvariant_outerNeg _ (quantityInvariant_innerNeg _ h)

/-- Meet preserves QuantityInvariant. -/
theorem quantityInvariant_gqMeet (f g : GQ α)
    (hf : QuantityInvariant f) (hg : QuantityInvariant g) :
    QuantityInvariant (gqMeet f g) := by
  intro A B A' B' σ hBij hA hB
  simp only [gqMeet]
  rw [hf A B A' B' σ hBij hA hB, hg A B A' B' σ hBij hA hB]

/-- Conservative + intersection condition → symmetric (B&C Theorem C5).
    Proof: by conservativity Q(A,B) = Q(A, A∩B) and Q(B,A) = Q(B, B∩A);
    both have the same restrictor∩scope = A∩B, so intersection condition
    equates them. -/
theorem intersection_conservative_symmetric (q : GQ α)
    (hCons : Conservative q) (hInt : IntersectionCondition q) :
    QSymmetric q := by
  intro R S
  rw [hCons R S, hCons S R]
  apply hInt
  intro x; cases R x <;> cases S x <;> rfl

/-- Scope-downward monotonicity is equivalent to scope-upward monotonicity
    of the inner negation (co-property characterization, P&W §3.2.4). -/
theorem co_property_mono (q : GQ α) :
    ScopeDownwardMono q ↔ ScopeUpwardMono (innerNeg q) := by
  constructor
  · exact innerNeg_down_to_up q
  · intro h
    have h' := innerNeg_up_to_down (innerNeg q) h
    rw [innerNeg_involution] at h'
    exact h'

-- ============================================================================
-- §5 Conservativity, Symmetry, and Strength
-- ============================================================================

/-- Under conservativity, symmetric ↔ intersective (P&W Ch.6 Fact 1).
    This is the single most important bridge theorem — it explains why
    weak determiners allow there-insertion. -/
theorem conserv_symm_iff_int (q : GQ α) (hCons : Conservative q) :
    QSymmetric q ↔ IntersectionCondition q := by
  constructor
  · -- SYMM → INT: show Q(R,S) depends only on R∩S
    intro hSym R S R' S' hEq
    -- Step 1: Q(R,S) = Q(R, R∩S) by CONS
    -- Step 2: Q(R, R∩S) = Q(R∩S, R) by SYMM
    -- Step 3: Q(R∩S, R) = Q(R∩S, (R∩S)∩R) by CONS
    -- (R∩S)∩R = R∩S, so Q(R,S) = Q(R∩S, R∩S)
    -- Same for Q(R',S') = Q(R'∩S', R'∩S')
    -- By hEq, R∩S = R'∩S', so these are equal
    have step_RS : q R S = q (λ x => R x && S x) (λ x => R x && S x) := by
      calc q R S
          = q R (λ x => R x && S x) := hCons R S
        _ = q (λ x => R x && S x) R := hSym R (λ x => R x && S x)
        _ = q (λ x => R x && S x) (λ x => (R x && S x) && R x) :=
            hCons (λ x => R x && S x) R
        _ = q (λ x => R x && S x) (λ x => R x && S x) := by
            congr 1; funext x; cases R x <;> cases S x <;> rfl
    have step_R'S' : q R' S' = q (λ x => R' x && S' x) (λ x => R' x && S' x) := by
      calc q R' S'
          = q R' (λ x => R' x && S' x) := hCons R' S'
        _ = q (λ x => R' x && S' x) R' := hSym R' (λ x => R' x && S' x)
        _ = q (λ x => R' x && S' x) (λ x => (R' x && S' x) && R' x) :=
            hCons (λ x => R' x && S' x) R'
        _ = q (λ x => R' x && S' x) (λ x => R' x && S' x) := by
            congr 1; funext x; cases R' x <;> cases S' x <;> rfl
    rw [step_RS, step_R'S']
    have : (λ x => R x && S x) = (λ x => R' x && S' x) := funext hEq
    rw [this]
  · -- INT → SYMM (already proved)
    exact intersection_conservative_symmetric q hCons

/-- Non-trivial symmetric quantifiers are not positive strong
    (P&W Ch.6 Fact 7). -/
theorem symm_not_positive_strong (q : GQ α) (hCons : Conservative q)
    (hSym : QSymmetric q)
    (hNontrivF : ∃ R S, q R S = false) :
    ¬PositiveStrong q := by
  intro hPos
  obtain ⟨R', S', hF⟩ := hNontrivF
  -- From the SYMM→INT direction above, Q(R',S') = Q(R'∩S', R'∩S')
  have hInt := (conserv_symm_iff_int q hCons).mp hSym
  -- Q(R'∩S', R'∩S') = Q(R',S') since restrictor∩scope is the same
  have hSame : q (λ x => R' x && S' x) (λ x => R' x && S' x) = q R' S' := by
    apply hInt; intro x; cases R' x <;> cases S' x <;> rfl
  -- But PositiveStrong says Q(R'∩S', R'∩S') = true
  have hT := hPos (λ x => R' x && S' x)
  rw [hSame] at hT
  simp [hT] at hF

/-- Conservativity of a GQ is equivalent to its restricted quantifiers
    living on their restrictors (P&W §3.2.2). -/
theorem conservative_iff_livesOn (q : GQ α) :
    Conservative q ↔ ∀ A, LivesOn (restrict q A) A := by
  unfold Conservative LivesOn restrict
  constructor
  · intro h A B; exact h A B
  · intro h R S; exact h R S

/-- Every `GQ α` satisfies Extension: the representation is universe-free. -/
theorem extension_trivial (q : GQ α) : Extension q := trivial

/-- @cite{van-benthem-1984}: Under Extension (free for GQ α), Conservativity
    is equivalent to LivesOn — the restricted quantifier depends only on
    elements of its restrictor. This is the `CONS + EXT ↔ Rel(⟨1⟩)`
    characterization of "well-behaved" type ⟨1,1⟩ quantifiers.

    Our `conservative_iff_livesOn` doesn't need an EXT hypothesis because
    `GQ α` already bakes it. -/
theorem vanBenthem_cons_ext (q : GQ α) :
    Extension q → (Conservative q ↔ ∀ A, LivesOn (restrict q A) A) :=
  λ _ => conservative_iff_livesOn q

-- ============================================================================
-- §5b Basic Left Monotonicity and Smoothness (@cite{peters-westerstahl-2006} §5.5-5.6)
-- ============================================================================

-- Prop 6: Persistence decomposes into ↑_SW + ↑_SE

/-- Persistence → ↑_SE Mon (trivial: ↑_SE conditions are a special case of A⊆A'). -/
theorem restrictorUpMono_to_upSE (q : GQ α)
    (h : RestrictorUpwardMono q) : UpSEMon q :=
  λ R S R' hSub _ hQ => h R R' S hSub hQ

/-- Persistence → ↑_SW Mon (trivial: ↑_SW conditions are a special case of A⊆A'). -/
theorem restrictorUpMono_to_upSW (q : GQ α)
    (h : RestrictorUpwardMono q) : UpSWMon q :=
  λ R S R' hSub _ hQ => h R R' S hSub hQ

/-- ↑_SW Mon ∧ ↑_SE Mon → Persistence (@cite{peters-westerstahl-2006} Prop 6).

    Proof: extend A to A' in two steps via A'' = A ∪ (A'\B).
    Step 1: A⊆A'' with A∩B = A''∩B (new elements are outside B) — apply ↑_SW.
    Step 2: A''⊆A' with A''\B = A'\B (same elements outside B) — apply ↑_SE. -/
theorem upSW_upSE_to_restrictorUpMono (q : GQ α)
    (hSW : UpSWMon q) (hSE : UpSEMon q) : RestrictorUpwardMono q := by
  intro R R' S hSub hQ
  -- A'' = A ∪ (A'\B): elements of A, plus elements of A' that are not in B
  let R'' : α → Bool := λ x => R x || (R' x && !S x)
  -- Step 1: ↑_SW from R to R'' (A ⊆ A'' and A∩B = A''∩B)
  have step1 : q R'' S = true := by
    apply hSW R S R'' _ _ hQ
    · intro x hRx; simp [R'', hRx]
    · intro x hR''x hSx
      simp [R''] at hR''x
      cases hR''x with
      | inl h => exact h
      | inr h => simp [hSx] at h
  -- Step 2: ↑_SE from R'' to R' (A'' ⊆ A' and A''\B = A'\B)
  apply hSE R'' S R' _ _ step1
  · intro x hR''x
    simp [R''] at hR''x
    cases hR''x with
    | inl h => exact hSub x h
    | inr h => exact h.1
  · intro x hR'x hSnS
    simp [R'', hR'x, hSnS]

/-- Persistence ↔ ↑_SW Mon ∧ ↑_SE Mon (@cite{peters-westerstahl-2006} Prop 6). -/
theorem persistent_iff_upSW_and_upSE (q : GQ α) :
    RestrictorUpwardMono q ↔ UpSWMon q ∧ UpSEMon q :=
  ⟨λ h => ⟨restrictorUpMono_to_upSW q h, restrictorUpMono_to_upSE q h⟩,
   λ ⟨hSW, hSE⟩ => upSW_upSE_to_restrictorUpMono q hSW hSE⟩

-- Analogous decomposition for anti-persistence

/-- Anti-persistence → ↓_NW Mon. -/
theorem restrictorDownMono_to_downNW (q : GQ α)
    (h : RestrictorDownwardMono q) : DownNWMon q :=
  λ R S R' hSub _ hQ => h R' R S hSub hQ

/-- Anti-persistence → ↓_NE Mon. -/
theorem restrictorDownMono_to_downNE (q : GQ α)
    (h : RestrictorDownwardMono q) : DownNEMon q :=
  λ R S R' hSub _ hQ => h R' R S hSub hQ

/-- ↓_NW Mon ∧ ↓_NE Mon → Anti-persistence.

    Proof: shrink A to A' in two steps via A'' = A' ∪ (A∩B) ∩ something.
    More precisely, A'' = A ∩ (A' ∪ B). Then A' ⊆ A'' ⊆ A,
    A∩B = A''∩B (removing complement-of-(A'∪B) doesn't touch B-elements),
    and A'\B = A''\B (A'' outside B = A ∩ A' outside B = A' outside B).
    Step 1: ↓_NE from A to A''. Step 2: ↓_NW from A'' to A'. -/
theorem downNW_downNE_to_restrictorDownMono (q : GQ α)
    (hNW : DownNWMon q) (hNE : DownNEMon q) : RestrictorDownwardMono q := by
  -- RestrictorDownwardMono: R⊆R' → q R' S → q R S
  intro R R' S hSub hQ
  -- A'' = R ∪ (R'∩S): intermediate restrictor with R ⊆ A'' ⊆ R'
  let R'' : α → Bool := λ x => R x || (R' x && S x)
  -- Step 1: ↓_NE from R' to R'' (R''⊆R' and R'∩S = R''∩S)
  have step1 : q R'' S = true := by
    apply hNE R' S R'' _ _ hQ
    · intro x hR''x
      simp only [R'', Bool.or_eq_true, Bool.and_eq_true] at hR''x
      cases hR''x with
      | inl h => exact hSub x h
      | inr h => exact h.1
    · intro x hR'x hSx
      simp only [R'', Bool.or_eq_true, Bool.and_eq_true]
      exact Or.inr ⟨hR'x, hSx⟩
  -- Step 2: ↓_NW from R'' to R (R⊆R'' and R''\S = R\S)
  apply hNW R'' S R _ _ step1
  · intro x hRx
    simp only [R'', Bool.or_eq_true, Bool.and_eq_true]
    exact Or.inl hRx
  · intro x hR''x hSnS
    simp only [R'', Bool.or_eq_true, Bool.and_eq_true] at hR''x
    cases hR''x with
    | inl h => exact h
    | inr h => exact absurd h.2 (by simp [hSnS])

/-- Anti-persistence ↔ ↓_NW Mon ∧ ↓_NE Mon. -/
theorem anti_persistent_iff_downNW_and_downNE (q : GQ α) :
    RestrictorDownwardMono q ↔ DownNWMon q ∧ DownNEMon q :=
  ⟨λ h => ⟨restrictorDownMono_to_downNW q h, restrictorDownMono_to_downNE q h⟩,
   λ ⟨hNW, hNE⟩ => downNW_downNE_to_restrictorDownMono q hNW hNE⟩

-- Prop 8: Negation rotates basic monotonicities

/-- Outer negation reverses ↑_SE to ↓_NW (@cite{peters-westerstahl-2006} Prop 8a).
    Contrapositive: if Q(R',S)→Q(R,S) under ↑_SE conditions,
    then ¬Q(R,S)→¬Q(R',S), which is ↓_NW for ~Q. -/
theorem outerNeg_upSE_to_downNW (q : GQ α)
    (h : UpSEMon q) : DownNWMon (outerNeg q) := by
  intro R S R' hSub hDiff hQ
  simp only [outerNeg] at *
  cases hR'S : q R' S
  · simp
  · have := h R' S R hSub hDiff hR'S; simp [this] at hQ

/-- Outer negation reverses ↓_NW to ↑_SE. -/
theorem outerNeg_downNW_to_upSE (q : GQ α)
    (h : DownNWMon q) : UpSEMon (outerNeg q) := by
  intro R S R' hSub hDiff hQ
  simp only [outerNeg] at *
  cases hR'S : q R' S
  · simp
  · have := h R' S R hSub hDiff hR'S; simp [this] at hQ

/-- Outer negation reverses ↑_SW to ↓_NE. -/
theorem outerNeg_upSW_to_downNE (q : GQ α)
    (h : UpSWMon q) : DownNEMon (outerNeg q) := by
  intro R S R' hSub hDiff hQ
  simp only [outerNeg] at *
  cases hR'S : q R' S
  · simp
  · have := h R' S R hSub hDiff hR'S; simp [this] at hQ

/-- Outer negation reverses ↓_NE to ↑_SW. -/
theorem outerNeg_downNE_to_upSW (q : GQ α)
    (h : DownNEMon q) : UpSWMon (outerNeg q) := by
  intro R S R' hSub hDiff hQ
  simp only [outerNeg] at *
  cases hR'S : q R' S
  · simp
  · have := h R' S R hSub hDiff hR'S; simp [this] at hQ

/-- Inner negation switches ↓_NE ↔ ↓_NW (@cite{peters-westerstahl-2006} Prop 8b).

    Proof: if Q is ↓_NE Mon, then Q¬(A,B) = Q(A,¬B), A'⊆A, and
    A\B = A'\B means A∩(¬B) = A'∩(¬B), so ↓_NE Mon on Q gives Q(A',¬B) = Q¬(A',B).
    This is the ↓_NW condition for Q¬. -/
theorem innerNeg_downNE_to_downNW (q : GQ α)
    (h : DownNEMon q) : DownNWMon (innerNeg q) := by
  intro R S R' hSub hDiff hQ
  simp only [innerNeg] at *
  refine h R (fun x => !S x) R' hSub ?_ hQ
  intro x hRx hNS
  exact hDiff x hRx (by cases hS : S x <;> simp [hS] at hNS ⊢)

/-- Inner negation switches ↓_NW ↔ ↓_NE. -/
theorem innerNeg_downNW_to_downNE (q : GQ α)
    (h : DownNWMon q) : DownNEMon (innerNeg q) := by
  intro R S R' hSub hDiff hQ
  simp only [innerNeg] at *
  refine h R (fun x => !S x) R' hSub ?_ hQ
  intro x hRx hNS
  exact hDiff x hRx (by cases hS : S x <;> simp [hS] at hNS ⊢)

/-- Inner negation switches ↑_SE ↔ ↑_SW. -/
theorem innerNeg_upSE_to_upSW (q : GQ α)
    (h : UpSEMon q) : UpSWMon (innerNeg q) := by
  intro R S R' hSub hDiff hQ
  simp only [innerNeg] at *
  refine h R (fun x => !S x) R' hSub ?_ hQ
  intro x hR'x hNS
  exact hDiff x hR'x (by cases hS : S x <;> simp [hS] at hNS ⊢)

/-- Inner negation switches ↑_SW ↔ ↑_SE. -/
theorem innerNeg_upSW_to_upSE (q : GQ α)
    (h : UpSWMon q) : UpSEMon (innerNeg q) := by
  intro R S R' hSub hDiff hQ
  simp only [innerNeg] at *
  refine h R (fun x => !S x) R' hSub ?_ hQ
  intro x hR'x hNS
  exact hDiff x hR'x (by cases hS : S x <;> simp [hS] at hNS ⊢)

/-- Smooth ↔ outer negation is co-smooth (@cite{peters-westerstahl-2006} Prop 8a). -/
theorem smooth_iff_outerNeg_coSmooth (q : GQ α) :
    Smooth q ↔ CoSmooth (outerNeg q) :=
  ⟨λ ⟨hNE, hSE⟩ => ⟨outerNeg_upSE_to_downNW q hSE, outerNeg_downNE_to_upSW q hNE⟩,
   λ ⟨hNW, hSW⟩ => by
    rw [show q = outerNeg (outerNeg q) from (outerNeg_involution q).symm]
    exact ⟨outerNeg_upSW_to_downNE _ hSW, outerNeg_downNW_to_upSE _ hNW⟩⟩

/-- Smooth ↔ inner negation is co-smooth (@cite{peters-westerstahl-2006} Prop 8b). -/
theorem smooth_iff_innerNeg_coSmooth (q : GQ α) :
    Smooth q ↔ CoSmooth (innerNeg q) :=
  ⟨λ ⟨hNE, hSE⟩ => ⟨innerNeg_downNE_to_downNW q hNE, innerNeg_upSE_to_upSW q hSE⟩,
   λ ⟨hNW, hSW⟩ => by
    rw [show q = innerNeg (innerNeg q) from (innerNeg_involution q).symm]
    exact ⟨innerNeg_downNW_to_downNE _ hNW, innerNeg_upSW_to_upSE _ hSW⟩⟩

-- Prop 9: Smooth → Mon↑

/-- CONSERV ∧ Smooth → Mon↑ (@cite{peters-westerstahl-2006} Prop 9).

    Proof: Given Q(A,B) and B ⊆ B'. Let A' = A \ (B'\B). Then:
    - A'⊆A and A∩B=A'∩B (removing B'\B doesn't touch B since B∩(B'\B)=∅)
    → ↓_NE gives Q(A',B)
    - A'∩B = A'∩B' (any x∈A'∩B' must be in B, since elements of B'\B were removed)
    → CONSERV: Q(A',B) = Q(A',B')
    - A'⊆A and A'\B'=A\B' (A'\B' = A\(B'\B)\B' = A\B')
    → ↑_SE gives Q(A,B') -/
theorem smooth_conservative_scopeUpMono (q : GQ α)
    (hCons : Conservative q) (hSmooth : Smooth q) : ScopeUpwardMono q := by
  obtain ⟨hNE, hSE⟩ := hSmooth
  intro R S S' hSS' hQ
  -- A' = A \ (B'\B): keep elements of A that are either in B or not in B'
  let R' : α → Bool := λ x => R x && (S x || !S' x)
  -- Step 1: ↓_NE from (R,S) to (R',S) — A'⊆A and A∩B = A'∩B
  have hR'S : q R' S = true := by
    apply hNE R S R' _ _ hQ
    · intro x hR'x; simp [R'] at hR'x; exact hR'x.1
    · intro x hRx hSx; simp [R', hRx, hSx]
  -- Key: R'∩S = R'∩S' (elements of B'\B were removed from A')
  have key : (λ x => R' x && S' x) = (λ x => R' x && S x) := by
    funext x
    simp only [R']
    cases hRx : R x <;> simp
    cases hSx : S x <;> cases hS'x : S' x <;> simp
    exact absurd (hSS' x hSx) (by simp [hS'x])
  -- Step 2: CONSERV switches scope from S to S' — Q(R',S) = Q(R',S')
  have hR'S' : q R' S' = true := by
    rw [hCons R' S'] ; rw [key] ; rw [← hCons R' S] ; exact hR'S
  -- Step 3: ↑_SE from (R',S') to (R,S') — R'⊆R and R\S'=R'\S'
  apply hSE R' S' R _ _ hR'S'
  · intro x hR'x; simp [R'] at hR'x; exact hR'x.1
  · intro x hRx hS'nS
    simp only [R', Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true']
    exact ⟨hRx, Or.inr hS'nS⟩

-- Prop 7: Symmetry ↔ ↑_SW + ↓_NE (under CONSERV)

/-- CONSERV ∧ QSymmetric → ↑_SW Mon ∧ ↓_NE Mon (@cite{peters-westerstahl-2006} Prop 7).

    Under CONSERV, symmetry is equivalent to Q(A,B) ↔ Q(A∩B, A∩B).
    Both ↑_SW and ↓_NE preserve A∩B, so the truth value is unchanged. -/
theorem symmetric_to_upSW_downNE (q : GQ α)
    (hCons : Conservative q) (hSym : QSymmetric q) :
    UpSWMon q ∧ DownNEMon q := by
  -- Key helper: under CONSERV+symmetry, Q(A,B) = Q(A∩B, A∩B)
  have toIntersect : ∀ A B : α → Bool,
      q A B = q (λ x => A x && B x) (λ x => A x && B x) := by
    intro A B
    have h1 : q A B = q A (λ x => A x && B x) := hCons A B
    have h2 : q A (λ x => A x && B x) = q (λ x => A x && B x) A :=
      hSym A (λ x => A x && B x)
    have h3 : q (λ x => A x && B x) A =
        q (λ x => A x && B x) (λ x => (A x && B x) && A x) :=
      hCons (λ x => A x && B x) A
    have h4 : (λ x => (A x && B x) && A x) = (λ x => A x && B x) := by
      funext x; cases A x <;> cases B x <;> rfl
    rw [h1, h2, h3, h4]
  -- Both ↑_SW and ↓_NE preserve A∩B, so Q is invariant
  have intersect_eq (R S R' : α → Bool)
      (hFwd : ∀ x, R x = true → S x = true → R' x = true)
      (hBwd : ∀ x, R' x = true → S x = true → R x = true) :
      (λ x => R x && S x) = (λ x => R' x && S x) := by
    funext x; cases hSx : S x <;> simp
    cases hRx : R x <;> cases hR'x : R' x <;> simp
    · exact absurd (hBwd x hR'x hSx) (by simp [hRx])
    · exact absurd (hFwd x hRx hSx) (by simp [hR'x])
  constructor
  · -- ↑_SW: A⊆A', A∩B=A'∩B, Q(A,B) → Q(A',B)
    intro R S R' hSub hInt hQ
    rw [toIntersect R S] at hQ
    rw [intersect_eq R S R' (λ x hRx hSx => hSub x hRx) hInt] at hQ
    rw [← toIntersect R' S] at hQ
    exact hQ
  · -- ↓_NE: A'⊆A, A∩B=A'∩B, Q(A,B) → Q(A',B)
    intro R S R' hSub hInt hQ
    rw [toIntersect R S] at hQ
    rw [intersect_eq R S R' hInt (λ x hR'x hSx => hSub x hR'x)] at hQ
    rw [← toIntersect R' S] at hQ
    exact hQ

/-- ↑_SW Mon ∧ ↓_NE Mon → QSymmetric (under CONSERV).
    Converse of `symmetric_to_upSW_downNE`. Together they give
    @cite{peters-westerstahl-2006} Prop 7: a CONSERV quantifier is symmetric iff
    it satisfies ↑_SW Mon and ↓_NE Mon.

    Proof sketch: Given Q(A,B), extend A to A∪B via ↑_SW (intersection preserved),
    then shrink A∪B to B via ↓_NE (intersection preserved), yielding Q(B, A∩B).
    By CONSERV, Q(B, A∩B) = Q(B, B∩(A∩B)) = Q(B, A∩B).
    Symmetrically from Q(B,A) → Q(A,B). -/
theorem upSW_downNE_to_symmetric (q : GQ α)
    (hCons : Conservative q) (hUpSW : UpSWMon q) (hDownNE : DownNEMon q) :
    QSymmetric q := by
  intro A B
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hQ
    -- Step 1: Rewrite via CONSERV: Q(A,B) = Q(A, A∩B)
    rw [hCons A B] at hQ
    -- Step 2: Q(A, A∩B) → Q(A∪B, A∩B) via ↑_SW
    -- Conditions: A ⊆ A∪B ✓; (A∪B) ∩ (A∩B) ⊆ A (from A∩B ⊆ A) ✓
    have hABint : q (λ x => A x || B x) (λ x => A x && B x) = true := by
      apply hUpSW A (λ x => A x && B x) (λ x => A x || B x)
      · intro x hAx; simp [hAx]
      · intro x _ hIntx
        simp only [Bool.and_eq_true] at hIntx
        exact hIntx.1
      · exact hQ
    -- Step 3: Q(A∪B, A∩B) → Q(B, A∩B) via ↓_NE
    -- Conditions: B ⊆ A∪B ✓; (A∪B) ∩ (A∩B) ⊆ B (from A∩B ⊆ B) ✓
    have hBint : q B (λ x => A x && B x) = true := by
      apply hDownNE (λ x => A x || B x) (λ x => A x && B x) B
      · intro x hBx; simp [hBx]
      · intro x _ hIntx
        simp only [Bool.and_eq_true] at hIntx
        exact hIntx.2
      · exact hABint
    -- Step 4: Q(B, A∩B) = Q(B, A) by CONSERV (since B∩A = A∩B)
    rw [hCons B A]
    convert hBint using 2; funext x
    cases A x <;> cases B x <;> rfl
  · intro hQ
    -- Symmetric argument: Q(B,A) → Q(A,B) via same route with A↔B swapped
    rw [hCons B A] at hQ
    have hBAint : q (λ x => B x || A x) (λ x => B x && A x) = true := by
      apply hUpSW B (λ x => B x && A x) (λ x => B x || A x)
      · intro x hBx; simp [hBx]
      · intro x _ hIntx
        simp only [Bool.and_eq_true] at hIntx
        exact hIntx.1
      · exact hQ
    have hAint : q A (λ x => B x && A x) = true := by
      apply hDownNE (λ x => B x || A x) (λ x => B x && A x) A
      · intro x hAx; simp [hAx]
      · intro x _ hIntx
        simp only [Bool.and_eq_true] at hIntx
        exact hIntx.2
      · exact hBAint
    rw [hCons A B]
    convert hAint using 2; funext x
    cases A x <;> cases B x <;> rfl

/-- @cite{peters-westerstahl-2006} Prop 7: a CONSERV type ⟨1,1⟩ quantifier
    is symmetric iff it satisfies ↑_SW Mon and ↓_NE Mon. -/
theorem symmetric_iff_upSW_downNE (q : GQ α) (hCons : Conservative q) :
    QSymmetric q ↔ (UpSWMon q ∧ DownNEMon q) :=
  ⟨symmetric_to_upSW_downNE q hCons,
   λ ⟨h1, h2⟩ => upSW_downNE_to_symmetric q hCons h1 h2⟩

-- ============================================================================
-- §6 Boolean Closure (@cite{keenan-stavi-1986})
-- ============================================================================

/-- Conservativity is closed under complement (K&S §2.3, negation).
    If Q is conservative, then ~Q is conservative. -/
theorem conservative_outerNeg (q : GQ α) (h : Conservative q) :
    Conservative (outerNeg q) := by
  intro R S; simp only [outerNeg]; rw [h R S]

/-- Conservativity is closed under meet (K&S §2.3, conjunction).
    If Q₁ and Q₂ are conservative, then Q₁ ∧ Q₂ is conservative. -/
theorem conservative_gqMeet (f g : GQ α)
    (hf : Conservative f) (hg : Conservative g) :
    Conservative (gqMeet f g) := by
  intro R S; simp only [gqMeet]; rw [hf R S, hg R S]

/-- Conservativity is closed under join (K&S §2.3, disjunction).
    If Q₁ and Q₂ are conservative, then Q₁ ∨ Q₂ is conservative. -/
theorem conservative_gqJoin (f g : GQ α)
    (hf : Conservative f) (hg : Conservative g) :
    Conservative (gqJoin f g) := by
  intro R S; simp only [gqJoin]; rw [hf R S, hg R S]

/-- K&S (26): complement distributes over join via de Morgan.
    ~(f ∨ g) = ~f ∧ ~g. "neither...nor" = complement of "either...or". -/
theorem outerNeg_gqJoin (f g : GQ α) :
    outerNeg (gqJoin f g) = gqMeet (outerNeg f) (outerNeg g) := by
  funext R S; simp [outerNeg, gqJoin, gqMeet, Bool.not_or]

/-- K&S (26): complement distributes over meet via de Morgan.
    ~(f ∧ g) = ~f ∨ ~g. -/
theorem outerNeg_gqMeet (f g : GQ α) :
    outerNeg (gqMeet f g) = gqJoin (outerNeg f) (outerNeg g) := by
  funext R S; simp [outerNeg, gqMeet, gqJoin, Bool.not_and]

/-- K&S PROP 6: Meet (join) of scope-↑ functions is scope-↑. -/
theorem scopeUpMono_gqMeet (f g : GQ α)
    (hf : ScopeUpwardMono f) (hg : ScopeUpwardMono g) :
    ScopeUpwardMono (gqMeet f g) := by
  intro R S S' hSS' h
  simp only [gqMeet] at *
  cases hfRS : f R S <;> cases hgRS : g R S <;> simp_all
  exact ⟨hf R S S' hSS' hfRS, hg R S S' hSS' hgRS⟩

/-- K&S PROP 6: Meet (join) of scope-↓ functions is scope-↓. -/
theorem scopeDownMono_gqMeet (f g : GQ α)
    (hf : ScopeDownwardMono f) (hg : ScopeDownwardMono g) :
    ScopeDownwardMono (gqMeet f g) := by
  intro R S S' hSS' h
  simp only [gqMeet] at *
  cases hfRS' : f R S' <;> cases hgRS' : g R S' <;> simp_all
  exact ⟨hf R S S' hSS' hfRS', hg R S S' hSS' hgRS'⟩

/-- K&S PROP 6: Join of scope-↑ functions is scope-↑. -/
theorem scopeUpMono_gqJoin (f g : GQ α)
    (hf : ScopeUpwardMono f) (hg : ScopeUpwardMono g) :
    ScopeUpwardMono (gqJoin f g) := by
  intro R S S' hSS' h
  simp only [gqJoin] at *
  cases hfRS : f R S <;> simp_all
  · exact Or.inr (hg R S S' hSS' h)
  · exact Or.inl (hf R S S' hSS' hfRS)

/-- K&S PROP 3: Conservativity is preserved under adjectival restriction. -/
theorem conservative_adjRestrict (q : GQ α) (adj : α → Bool)
    (h : Conservative q) : Conservative (adjRestrict q adj) := by
  intro R S
  simp only [adjRestrict]
  rw [h (λ x => R x && adj x) S, h (λ x => R x && adj x) (λ x => R x && S x)]
  congr 1; funext x; cases R x <;> cases adj x <;> cases S x <;> rfl

/-- K&S PROP 5: Scope-upward monotonicity is preserved under adjectival restriction.
    If det is increasing, (det + AP) is increasing. -/
theorem scopeUpMono_adjRestrict (q : GQ α) (adj : α → Bool)
    (h : ScopeUpwardMono q) : ScopeUpwardMono (adjRestrict q adj) := by
  intro R S S' hSS' hAdj
  simp only [adjRestrict] at *
  exact h _ S S' hSS' hAdj

/-- K&S PROP 5: Scope-downward monotonicity is preserved under adjectival restriction.
    If det is decreasing, (det + AP) is decreasing — NPIs still licensed. -/
theorem scopeDownMono_adjRestrict (q : GQ α) (adj : α → Bool)
    (h : ScopeDownwardMono q) : ScopeDownwardMono (adjRestrict q adj) := by
  intro R S S' hSS' hAdj
  simp only [adjRestrict] at *
  exact h _ S S' hSS' hAdj

-- ============================================================================
-- §7 Type ⟨1⟩ Theorems (P&W Ch.2-3)
-- ============================================================================

/-- Montagovian individuals are upward closed (ultrafilter property):
    if P ⊆ P' and a ∈ P, then a ∈ P'. -/
theorem individual_upward_closed (a : α) (P P' : α → Bool)
    (h : ∀ x, P x = true → P' x = true) :
    individual a P = true → individual a P' = true := by
  simp only [individual]; exact h a

/-- Montagovian individuals are closed under intersection:
    if a ∈ P and a ∈ Q, then a ∈ P ∩ Q. -/
theorem individual_meet_closed (a : α) (P Q : α → Bool) :
    individual a P = true → individual a Q = true →
    individual a (λ x => P x && Q x) = true := by
  simp only [individual]; intro hP hQ; simp [hP, hQ]

-- ============================================================================
-- §8 @cite{van-benthem-1984} Characterization
-- ============================================================================

/-- @cite{van-benthem-1984} Theorem 3.1.1: Under conservativity, inclusion (⊆)
    is the only reflexive antisymmetric quantifier.

    This is the "Aristotle reversed" cornerstone: the inferential properties
    (reflexivity + antisymmetry) uniquely determine the quantifier "all".

    Proof: (→) By CONSERV, Q(A,B) = Q(A, A∩B). Reflexivity gives Q(A∩B, A∩B).
    CONSERV again gives Q(A∩B, A) = Q(A∩B, A∩B). Antisymmetry on Q(A, A∩B)
    and Q(A∩B, A) yields A = A∩B, i.e., A ⊆ B.
    (←) If A ⊆ B then A∩B = A, so Q(A,B) = Q(A,A) by CONSERV + reflexivity. -/
theorem vanBenthem_refl_antisym_is_inclusion (q : GQ α)
    (hCons : Conservative q) (hRefl : PositiveStrong q)
    (hAnti : QAntisymmetric q) :
    ∀ A B, q A B = true ↔ (∀ x, A x = true → B x = true) := by
  intro A B
  constructor
  · intro hQAB
    have h1 : q A (λ x => A x && B x) = true := by rw [← hCons]; exact hQAB
    have h2 : q (λ x => A x && B x) A = true := by
      rw [hCons (λ x => A x && B x) A]
      have : (λ x => (A x && B x) && A x) = (λ x => A x && B x) := by
        funext x; cases A x <;> cases B x <;> rfl
      rw [this]; exact hRefl _
    have hEq := hAnti A (λ x => A x && B x) h1 h2
    intro x hAx
    have := congr_fun hEq x; simp [hAx] at this; exact this
  · intro hSub
    rw [hCons A B]
    have : (λ x => A x && B x) = A := by
      funext x; cases hA : A x
      · rfl
      · simp [hSub x hA]
    rw [this]; exact hRefl A

/-- @cite{van-benthem-1984} Thm 4.1.1 (Zwarts): reflexive + transitive → MON↑.
    Under CONSERV, if Q is reflexive and transitive, Q is scope-upward-monotone.

    Proof: QAB and B ⊆ B' gives QBB' (CONSERV + reflexivity), then QAB'
    by transitivity. -/
theorem zwarts_refl_trans_scopeUp (q : GQ α)
    (hCons : Conservative q) (hRefl : PositiveStrong q)
    (hTrans : QTransitive q) : ScopeUpwardMono q := by
  intro R S S' hSS' hQRS
  have hQSS' : q S S' = true := by
    rw [hCons S S']
    have : (λ x => S x && S' x) = S := by
      funext x; cases hS : S x
      · rfl
      · simp; exact hSS' x hS
    rw [this]; exact hRefl S
  exact hTrans R S S' hQRS hQSS'

/-- @cite{van-benthem-1984} Thm 4.1.1 (Zwarts): reflexive + transitive → ↓MON.
    Under CONSERV, if Q is reflexive and transitive, Q is
    restrictor-downward-monotone (anti-persistent).

    Proof: QR'S and R ⊆ R' gives QRR' (CONSERV + reflexivity), then QRS
    by transitivity. -/
theorem zwarts_refl_trans_restrictorDown (q : GQ α)
    (hCons : Conservative q) (hRefl : PositiveStrong q)
    (hTrans : QTransitive q) : RestrictorDownwardMono q := by
  intro R R' S hRR' hQR'S
  have hQRR' : q R R' = true := by
    rw [hCons R R']
    have : (λ x => R x && R' x) = R := by
      funext x; cases hR : R x
      · rfl
      · simp; exact hRR' x hR
    rw [this]; exact hRefl R
  exact hTrans R R' S hQRR' hQR'S

/-- @cite{van-benthem-1984} Thm 4.1.3 (Zwarts): for symmetric quantifiers,
    scope-↑ implies quasi-reflexive, under CONSERV. -/
theorem zwarts_sym_scopeUp_quasiRefl (q : GQ α)
    (hCons : Conservative q) (_hSym : QSymmetric q)
    (hUp : ScopeUpwardMono q) : QuasiReflexive q := by
  intro A B hQAB
  have h1 : q A (λ x => A x && B x) = true := by rw [← hCons]; exact hQAB
  exact hUp A (λ x => A x && B x) A
    (fun x hx => by cases hA : A x <;> simp_all) h1

/-- @cite{van-benthem-1984} Thm 4.1.3 (Zwarts): for symmetric quantifiers,
    scope-↓ implies quasi-universal, under CONSERV. -/
theorem zwarts_sym_scopeDown_quasiUniv (q : GQ α)
    (hCons : Conservative q) (_hSym : QSymmetric q)
    (hDown : ScopeDownwardMono q) : QuasiUniversal q := by
  intro A B hQAA
  rw [hCons A B]
  exact hDown A (λ x => A x && B x) A
    (fun x hx => by cases hA : A x <;> simp_all) hQAA

/-- Right-monotone quantifiers are right-continuous (@cite{van-benthem-1984} §4.3). -/
theorem scopeUpMono_rightContinuous (q : GQ α)
    (h : ScopeUpwardMono q) : RightContinuous q := by
  intro A B B₁ _ hB₁B _ hQ1 _
  exact h A B₁ B hB₁B hQ1

/-- @cite{van-benthem-1984} Thm 4.1.2: irreflexive + almost-connected → MON↓.
    Proof by duality: Q irreflexive ↔ ¬Q reflexive, Q almost-connected ↔ ¬Q
    transitive. By Zwarts (4.1.1), ¬Q has MON↑. Outer negation reverses
    scope monotonicity: MON↑ of ¬Q gives MON↓ of Q. -/
theorem irrefl_almostConn_scopeDown (q : GQ α)
    (hCons : Conservative q)
    (hIrrefl : NegativeStrong q)
    (hAC : AlmostConnected q) : ScopeDownwardMono q := by
  have hRefl : PositiveStrong (outerNeg q) := λ R => by simp [outerNeg, hIrrefl R]
  have hTrans : QTransitive (outerNeg q) := by
    intro A B C hAB hBC
    simp only [outerNeg, Bool.not_eq_true'] at *
    by_contra h; rw [Bool.not_eq_false] at h
    cases hAC A C B h with
    | inl h => simp [h] at hAB
    | inr h => simp [h] at hBC
  have hUp := zwarts_refl_trans_scopeUp (outerNeg q)
    (conservative_outerNeg q hCons) hRefl hTrans
  rw [← outerNeg_involution q]
  exact outerNeg_up_to_down (outerNeg q) hUp

/-- @cite{van-benthem-1984} Thm 4.1.2: irreflexive + almost-connected → ↑MON.
    Proof: ¬Q has ↓MON (Zwarts). Contrapositive gives ↑MON for Q:
    ↓MON(¬Q) = (A⊆A' → ¬Q(A',B) → ¬Q(A,B)) = (A⊆A' → Q(A,B) → Q(A',B)) = ↑MON(Q). -/
theorem irrefl_almostConn_restrictorUp (q : GQ α)
    (hCons : Conservative q)
    (hIrrefl : NegativeStrong q)
    (hAC : AlmostConnected q) : RestrictorUpwardMono q := by
  have hRefl : PositiveStrong (outerNeg q) := λ R => by simp [outerNeg, hIrrefl R]
  have hTrans : QTransitive (outerNeg q) := by
    intro A B C hAB hBC
    simp only [outerNeg, Bool.not_eq_true'] at *
    by_contra h; rw [Bool.not_eq_false] at h
    cases hAC A C B h with
    | inl h => simp [h] at hAB
    | inr h => simp [h] at hBC
  have hDown := zwarts_refl_trans_restrictorDown (outerNeg q)
    (conservative_outerNeg q hCons) hRefl hTrans
  intro R R' S hRR' hQ
  by_contra h
  have hF : q R' S = false := by revert h; cases q R' S <;> simp
  have := hDown R R' S hRR' (by simp [outerNeg, hF])
  simp [outerNeg, hQ] at this

-- ============================================================================
-- §8b — "Aristotle Reversed": Square from Inferential Conditions
-- @cite{van-benthem-1984} §3.3
-- ============================================================================

/-- @cite{van-benthem-1984} Cor 3.3.2: Under conservativity, the ONLY
    symmetric quasi-reflexive quantifier is overlap (= "some").

    Proof: CONSERV + symmetric → intersective (`conserv_symm_iff_int`).
    So q(A,B) = q(A∩B, A∩B) =: f(A∩B).
    Quasi-reflexivity gives: f(C) → f(D) when C ⊆ D
    (set A=D, B=C; then q(D,C) = f(D∩C) = f(C), and QR gives q(D,D) = f(D)).
    VAR gives f(∅) = false (otherwise f ≡ true) and ∃C, f(C) = true.
    So f is an upward-closed non-trivial predicate on sets.

    (→) If q(A,B) = true, then f(A∩B) = true, so A∩B is non-empty.
    (←) If A∩B is non-empty, pick a ∈ A∩B. Then f({a}) must be true
    (otherwise f(C) = false for all singletons, and upward closure +
    A∩B ⊇ {a} gives f(A∩B) = true only if f({a}) = true — contradiction).
    that works across models of arbitrary size, ensuring q is non-trivial on singletons.
    Because `GQ α` is fixed-domain, we explicitly require a singleton witness
    (`hWitT`) and isomorphism invariance (`hIso`) to ensure all singletons behave identically. -/
theorem vanBenthem_symm_quasiRefl_is_overlap [Fintype α] [DecidableEq α] (q : GQ α)
    (hCons : Conservative q) (hSym : QSymmetric q)
    (hQR : QuasiReflexive q)
    (hWitT : ∃ x, q (λ y => y == x) (λ y => y == x) = true)
    (hWitF : ∃ A, q A A = false)
    (hIso : QuantityInvariant q) :
    ∀ A B, q A B = true ↔ (∃ x, A x = true ∧ B x = true) := by
  have hInt := (conserv_symm_iff_int q hCons).mp hSym
  have qAB_eq : ∀ A B, q A B = q (λ x => A x && B x) (λ x => A x && B x) := by
    intro A B
    have h1 := hInt A B (λ x => A x && B x) (λ x => A x && B x)
    exact h1 (λ x => by cases A x <;> cases B x <;> rfl)
  have upward : ∀ C D : α → Bool,
      (∀ x, C x = true → D x = true) → q C C = true → q D D = true := by
    intro C D hCD hCC
    have hDC : q D C = q C C := by
      apply hInt; intro x; cases hC : C x
      · simp
      · simp [hCD x hC]
    exact hQR D C (hDC ▸ hCC)
  obtain ⟨A₀, hA₀⟩ := hWitF
  have empty_false : q (λ _ => false) (λ _ => false) = false := by
    by_contra h
    rw [Bool.not_eq_false] at h
    have := upward (λ _ => false) A₀ (λ _ _ => by contradiction) h
    rw [hA₀] at this; exact absurd this (by decide)
  intro A B
  constructor
  · intro hAB
    rw [qAB_eq] at hAB
    by_contra h
    push_neg at h
    have : (λ x => A x && B x) = (λ _ => false) := by
      funext x
      cases hA : A x <;> cases hB : B x <;> simp
      exact absurd hB (h x hA)
    rw [this] at hAB
    rw [empty_false] at hAB; exact absurd hAB (by decide)
  · intro ⟨a, hAa, hBa⟩
    rw [qAB_eq]
    obtain ⟨x, hx⟩ := hWitT
    have h_single : q (λ y => y == a) (λ y => y == a) = true := by
      let f : α → α := Equiv.swap x a
      have hf_bij : Function.Bijective f := (Equiv.swap x a).bijective
      have hf_prop : ∀ y, (f y == a) = (y == x) := by
        intro y
        apply Bool.eq_iff_iff.mpr
        simp only [beq_iff_eq, f]
        constructor
        · intro hy
          have h1 : (Equiv.swap x a).symm a = y := by
            exact (Equiv.symm_apply_eq (Equiv.swap x a)).mpr hy.symm
          have h2 : (Equiv.swap x a).symm a = x := by
            exact Equiv.swap_apply_right x a
          rw [h2] at h1
          exact h1.symm
        · intro hy
          have hh : y = x := hy
          rw [hh]
          exact Equiv.swap_apply_left x a
      have h_eq : q (λ y => y == a) (λ y => y == a) = q (λ y => y == x) (λ y => y == x) := by
        apply hIso (λ y => y == a) (λ y => y == a) (λ y => y == x) (λ y => y == x) f hf_bij
        · intro y; exact hf_prop y
        · intro y; exact hf_prop y
      rw [h_eq]
      exact hx
    apply upward (λ y => y == a) (λ y => A y && B y)
    · intro y hy
      simp only [beq_iff_eq] at hy
      subst hy
      simp [hAa, hBa]
    · exact h_single

/-- @cite{van-benthem-1984} Cor 3.3.3: Under conservativity, the ONLY
    symmetric quasi-universal quantifier is disjointness (= "no").

    This follows from the overlap characterization via outer negation:
    no(A,B) = ¬some(A,B) = ¬(A∩B ≠ ∅) = (A∩B = ∅). -/
theorem vanBenthem_symm_quasiUniv_is_disjointness [Fintype α] [DecidableEq α] (q : GQ α)
    (hCons : Conservative q) (hSym : QSymmetric q)
    (hQU : QuasiUniversal q)
    (hWitF : ∃ x, q (λ y => y == x) (λ y => y == x) = false)
    (hWitT : ∃ A, q A A = true)
    (hIso : QuantityInvariant q) :
    ∀ A B, q A B = true ↔ (∀ x, ¬(A x = true ∧ B x = true)) := by
  have hInt := (conserv_symm_iff_int q hCons).mp hSym
  have qAB_eq : ∀ A B, q A B = q (λ x => A x && B x) (λ x => A x && B x) := by
    intro A B
    exact hInt A B _ _ (λ x => by cases A x <;> cases B x <;> rfl)
  have downward : ∀ C D : α → Bool,
      (∀ x, C x = true → D x = true) → q D D = true → q C C = true := by
    intro C D hCD hDD
    have h1 : q D C = true := hQU D C hDD
    have h2 : q C D = true := by rw [hSym]; exact h1
    have h3 : q C D = q C C := by
      rw [hCons C D]
      have : (λ x => C x && D x) = C := by
        funext x
        cases hC : C x
        · rfl
        · simp [hCD x hC]
      rw [this]
    rw [h3] at h2
    exact h2

  obtain ⟨A₀, hA₀⟩ := hWitT
  have empty_true : q (λ _ => false) (λ _ => false) = true := by
    exact downward (λ _ => false) A₀ (λ _ _ => by contradiction) hA₀

  intro A B
  constructor
  · intro hAB x ⟨hAx, hBx⟩
    rw [qAB_eq] at hAB
    obtain ⟨x₀, hx₀⟩ := hWitF
    have h_single_true : q (λ y => y == x) (λ y => y == x) = true := by
      exact downward (λ y => y == x) (λ y => A y && B y) (λ y hy => by simp only [beq_iff_eq] at hy; subst hy; simp [hAx, hBx]) hAB
    have h_single_false : q (λ y => y == x) (λ y => y == x) = false := by
      let f : α → α := Equiv.swap x₀ x
      have hf_bij : Function.Bijective f := (Equiv.swap x₀ x).bijective
      have hf_prop : ∀ y, (f y == x) = (y == x₀) := by
        intro y
        apply Bool.eq_iff_iff.mpr
        simp only [beq_iff_eq, f]
        constructor
        · intro hy
          have h1 : (Equiv.swap x₀ x).symm x = y := by
            exact (Equiv.symm_apply_eq (Equiv.swap x₀ x)).mpr hy.symm
          have h2 : (Equiv.swap x₀ x).symm x = x₀ := by
            exact Equiv.swap_apply_right x₀ x
          rw [h2] at h1
          exact h1.symm
        · intro hy
          have hh : y = x₀ := hy
          rw [hh]
          exact Equiv.swap_apply_left x₀ x
      have h_eq : q (λ y => y == x) (λ y => y == x) = q (λ y => y == x₀) (λ y => y == x₀) := by
        apply hIso (λ y => y == x) (λ y => y == x) (λ y => y == x₀) (λ y => y == x₀) f hf_bij
        · intro y; exact hf_prop y
        · intro y; exact hf_prop y
      rw [h_eq]
      exact hx₀
    rw [h_single_true] at h_single_false
    contradiction
  · intro hDisj
    rw [qAB_eq]
    have hEmpty : (λ x => A x && B x) = (λ _ => false) :=
      funext λ x => by
        cases hA : A x <;> cases hB : B x <;> simp
        exact absurd ⟨hA, hB⟩ (hDisj x)
    rw [hEmpty]
    exact empty_true

-- ============================================================================
-- §9 — Entailment Signature Bridge (@cite{icard-2012})
-- ============================================================================

open Core.NaturalLogic (EntailmentSig ContextPolarity)

/--
Map a pair of entailment signatures (restrictor, scope) to `DoubleMono`,
the @cite{van-benthem-1984} double monotonicity classification.

Returns `none` for signature pairs that don't correspond to a standard
generalized quantifier pattern.
-/
def EntailmentSig.pairToDoubleMono : EntailmentSig → EntailmentSig → Option DoubleMono
  -- some = (⊕, ⊕) → ↑MON↑
  | .additive, .additive => some .upUp
  -- every = (◇, ⊞) → ↓MON↑
  | .antiAdd, .mult => some .downUp
  -- not every = (⊕, ⊟) → ↑MON↓
  | .additive, .antiMult => some .upDown
  -- no = (◇, ◇) → ↓MON↓
  | .antiAdd, .antiAdd => some .downDown
  -- Other combinations: could extend, but these are the four standard ones
  | _, _ => none

-- DoubleMono bridge verification
#guard EntailmentSig.pairToDoubleMono .additive .additive == some .upUp
#guard EntailmentSig.pairToDoubleMono .antiAdd .mult == some .downUp
#guard EntailmentSig.pairToDoubleMono .additive .antiMult == some .upDown
#guard EntailmentSig.pairToDoubleMono .antiAdd .antiAdd == some .downDown

/-- "every" has signature (◇, ⊞) = (antiAdd in restrictor, mult in scope). -/
def everyEntailmentSig : EntailmentSig × EntailmentSig := (.antiAdd, .mult)

/-- "some" has signature (⊕, ⊕) = (additive in both arguments). -/
def someEntailmentSig : EntailmentSig × EntailmentSig := (.additive, .additive)

/-- "no" has signature (◇, ◇) = (antiAdd in both arguments). -/
def noEntailmentSig : EntailmentSig × EntailmentSig := (.antiAdd, .antiAdd)

/-- "not every" has signature (⊕, ⊟) = (additive in restrictor, antiMult in scope). -/
def notEveryEntailmentSig : EntailmentSig × EntailmentSig := (.additive, .antiMult)

-- Verify quantifier ↔ DoubleMono agreement
#guard EntailmentSig.pairToDoubleMono everyEntailmentSig.1 everyEntailmentSig.2 == some .downUp
#guard EntailmentSig.pairToDoubleMono someEntailmentSig.1 someEntailmentSig.2 == some .upUp
#guard EntailmentSig.pairToDoubleMono noEntailmentSig.1 noEntailmentSig.2 == some .downDown
#guard EntailmentSig.pairToDoubleMono notEveryEntailmentSig.1 notEveryEntailmentSig.2 == some .upDown

-- Verify quantifier ↔ ContextPolarity agreement for scope position
#guard EntailmentSig.toContextPolarity everyEntailmentSig.2 == .upward     -- every scope is UE
#guard EntailmentSig.toContextPolarity someEntailmentSig.2 == .upward      -- some scope is UE
#guard EntailmentSig.toContextPolarity noEntailmentSig.2 == .downward      -- no scope is DE
#guard EntailmentSig.toContextPolarity notEveryEntailmentSig.2 == .downward -- not-every scope is DE

-- Verify quantifier ↔ ContextPolarity agreement for restrictor position
#guard EntailmentSig.toContextPolarity everyEntailmentSig.1 == .downward   -- every restrictor is DE
#guard EntailmentSig.toContextPolarity someEntailmentSig.1 == .upward      -- some restrictor is UE
#guard EntailmentSig.toContextPolarity noEntailmentSig.1 == .downward      -- no restrictor is DE
#guard EntailmentSig.toContextPolarity notEveryEntailmentSig.1 == .upward  -- not-every restrictor is UE

-- ============================================================================
-- §10 Number-Tree Impossibility Theorems (@cite{van-benthem-1984} §3.2)
-- ============================================================================

/-- Number-tree representation of a conservative, quantity-invariant GQ.
    Under CONSERV + QUANT, a quantifier's truth value depends only on
    `a = |A ∩ B|` and `b = |A \ B|` (@cite{van-benthem-1984} §2, "tree of numbers").
    This is inherently cross-domain: any `(a, b)` pair is realizable in some
    universe of size ≥ a + b. -/
abbrev NumberTreeGQ := Nat → Nat → Bool

namespace NumberTreeGQ

/-- Variety for number-tree quantifiers: Q is non-trivial. -/
def Variety (q : NumberTreeGQ) : Prop :=
  (∃ a b, q a b = true) ∧ (∃ a b, q a b = false)

/-- @cite{van-benthem-1984} Thm 3.2.1: No asymmetric CONSERV+QUANT quantifiers exist.

    On the number tree, asymmetry means: for all `a b c`,
    `q(a, b) → ¬q(a, c)` — because `|A ∩ B| = a` and `|B \ A| = c` is free
    (any `c` is realizable in a large enough universe).

    Proof: Set `c = b`. Then `q(a, b) → ¬q(a, b)`, so `q` is identically
    false. Contradicts Variety. -/
theorem no_asymmetric (q : NumberTreeGQ) (hVar : q.Variety)
    (hAsym : ∀ a b c, q a b = true → q a c = false) : False := by
  obtain ⟨⟨a, b, hab⟩, _⟩ := hVar
  exact absurd hab (Bool.eq_false_iff.mp (hAsym a b b hab))

/-- @cite{van-benthem-1984} §3.2 consequence: No strict partial order quantifiers.

    On the number tree, irreflexivity is `∀ n, q(n, 0) = false` (since
    `Q(A,A)` has `|A ∩ A| = n`, `|A \ A| = 0`). Transitivity (with C = A
    in the 3-set diagram) gives: `q(a, b) ∧ q(a, c) → q(a+b, 0)`.

    Proof: From transitivity, `q(a, b) → q(a, c) → q(a+b, 0)`.
    From irreflexivity, `q(a+b, 0) = false`. So `q(a, b) → q(a, c) = false`
    — number-tree asymmetry. Apply `no_asymmetric`. -/
theorem no_strict_partial_order (q : NumberTreeGQ) (hVar : q.Variety)
    (hIrrefl : ∀ n, q n 0 = false)
    (hTrans : ∀ a b c, q a b = true → q a c = true → q (a + b) 0 = true) :
    False := by
  exact no_asymmetric q hVar (λ a b c hab => by
    by_contra h
    rw [Bool.not_eq_false] at h
    have := hTrans a b c hab h
    rw [hIrrefl] at this
    exact absurd this (by decide))

/-- @cite{van-benthem-1984} Thm 3.2.3: No Euclidean CONSERV+QUANT quantifiers exist.

    On the number tree (3-set Venn diagram with 7 free size parameters
    `p, q, r, s, t, u` plus one more), the Euclidean property becomes:
    `q(p+q_, r+s) ∧ q(p+r, q_+s) → q(p+t, q_+u)` for all `p q_ r s t u`.

    Proof (4 steps):
    1. From Variety witness `q(α, β) = true`, set `p=α, q_=0, r=0, s=β`:
       `q(α+t, u)` for all `t, u`. So `q(a, b) = true` for `a ≥ α`.
    2. If `α = 0`, step 1 gives `q ≡ true`, contradicting Variety.
       If `α > 0`: pair `q(α, 2α)` and `q(2α, α)` (both from step 1)
       with `p=0, q_=α, r=2α, s=0`: get `q(t, α+u)` for all `t, u`.
       Combined: `q(a, b) = true` when `a ≥ α` or `b ≥ α`.
    3. `q(0, α)` (from step 2) and `q(α, 0)` (from step 1) with
       `p=0, q_=0, r=α, s=0`: get `q(t, u)` for all `t, u`.
    4. Contradicts Variety. -/
theorem no_euclidean (q : NumberTreeGQ) (hVar : q.Variety)
    (hEuc : ∀ p q_ r s t u,
      q (p + q_) (r + s) = true → q (p + r) (q_ + s) = true →
      q (p + t) (q_ + u) = true) : False := by
  obtain ⟨⟨α, β, hαβ⟩, ⟨a₀, b₀, hFalse⟩⟩ := hVar
  -- Step 1: q(α + t, u) for all t, u
  -- Use hEuc with p=α, q_=0, r=0, s=β: q(α+0)(0+β) ∧ q(α+0)(0+β) → q(α+t)(0+u)
  have step1 : ∀ t u, q (α + t) u = true := by
    intro t u
    have := hEuc α 0 0 β t u (by rwa [Nat.add_zero, Nat.zero_add])
      (by rwa [Nat.add_zero, Nat.zero_add])
    simpa [Nat.zero_add] using this
  -- Step 3 (shortcut): q(α, 0) from step1 (t=0, u=0)
  have qα0 : q α 0 = true := step1 0 0
  -- If α = 0: step1 gives q(t, u) for all t, u → contradiction
  by_cases hα : α = 0
  · subst hα; simp only [Nat.zero_add] at step1; rw [step1] at hFalse; exact absurd hFalse (by decide)
  -- α > 0
  -- Step 2: q(t, α + u) for all t, u
  -- q(α, β) is our witness. Use step1 to get q at larger first args.
  -- q(2*α, α) from step1 (t = α, u = α)
  have q_2α_α : q (2 * α) α = true := by
    have := step1 α α; rwa [show α + α = 2 * α from by omega] at this
  -- q(α, 2*α) via step1: need q(α + t', 2*α) — take t' = 0
  have q_α_2α : q α (2 * α) = true := by
    have := step1 0 (2 * α); rwa [Nat.add_zero] at this
  -- Use hEuc with p=0, q_=α, r=2*α, s=0: q(0+α)(2α+0) ∧ q(0+2α)(α+0) → q(0+t)(α+u)
  have step2 : ∀ t u, q t (α + u) = true := by
    intro t u
    have := hEuc 0 α (2 * α) 0 t u
      (by rwa [Nat.zero_add, Nat.add_zero])
      (by rwa [Nat.zero_add, Nat.add_zero])
    simpa [Nat.zero_add] using this
  -- Step 3: q(0, α) from step2 (t=0, u=0)
  have q0α : q 0 α = true := by have := step2 0 0; rwa [Nat.add_zero] at this
  -- Use hEuc with p=0, q_=0, r=α, s=0: q(0+0)(α+0) ∧ q(0+α)(0+0) → q(0+t)(0+u)
  have step3 : ∀ t u, q t u = true := by
    intro t u
    have := hEuc 0 0 α 0 t u
      (by rwa [Nat.zero_add, Nat.add_zero])
      (by rwa [Nat.zero_add, Nat.add_zero])
    simpa [Nat.zero_add] using this
  -- Step 4: contradiction with Variety
  rw [step3] at hFalse; exact absurd hFalse (by decide)

-- §10b Number-tree representations of the Square of Opposition

/-- "all" on the number tree: Q(A,B) iff A ⊆ B iff |A\B| = 0. -/
def allNT : NumberTreeGQ := λ _ b => b == 0

/-- "some" on the number tree: Q(A,B) iff A∩B ≠ ∅ iff |A∩B| ≥ 1. -/
def someNT : NumberTreeGQ := λ a _ => decide (a ≥ 1)

/-- "no" on the number tree: Q(A,B) iff A∩B = ∅ iff |A∩B| = 0. -/
def noNT : NumberTreeGQ := λ a _ => a == 0

/-- "not all" on the number tree: Q(A,B) iff A ⊄ B iff |A\B| ≥ 1. -/
def notAllNT : NumberTreeGQ := λ _ b => decide (b ≥ 1)

-- §10c Additivity (@cite{van-benthem-1984} §5.2, p.460)

/-- Additive: (a,b) ∈ Q and (a',b') ∈ Q implies (a+a', b+b') ∈ Q.
    @cite{van-benthem-1984} p.460: all, some, no, not all are additive.
    Additivity means Q's truth set is closed under componentwise addition
    in the number tree. -/
def Additive (q : NumberTreeGQ) : Prop :=
  ∀ a b a' b', q a b = true → q a' b' = true → q (a + a') (b + b') = true

theorem allNT_additive : Additive allNT := by
  intro a b a' b' h1 h2
  simp only [allNT, beq_iff_eq] at *; omega

theorem someNT_additive : Additive someNT := by
  intro a b a' b' h1 h2
  simp only [someNT, decide_eq_true_eq] at *; omega

theorem noNT_additive : Additive noNT := by
  intro a b a' b' h1 h2
  simp only [noNT, beq_iff_eq] at *; omega

theorem notAllNT_additive : Additive notAllNT := by
  intro a b a' b' h1 h2
  simp only [notAllNT, decide_eq_true_eq] at *; omega

-- §10d Continuity, PLUS, UNIF (@cite{van-benthem-1984} §4.3, §7)

/-- Right continuity on the number tree (CONT): on each diagonal a+b = n,
    the true points form a contiguous interval.
    @cite{van-benthem-1984} §4.3: all right-monotone quantifiers are
    continuous. "precisely one" is continuous but non-monotone. -/
def RightCont (q : NumberTreeGQ) : Prop :=
  ∀ n a₁ a₂ a, a₁ ≤ a → a ≤ a₂ → a₂ ≤ n →
    q a₁ (n - a₁) = true → q a₂ (n - a₂) = true →
    q a (n - a) = true

/-- Left continuity on the number tree: on each diagonal, the false
    points (absence) also form a contiguous interval.
    @cite{van-benthem-1984} §4.3: equivalent to right continuity of ¬Q. -/
def LeftCont (q : NumberTreeGQ) : Prop :=
  ∀ n a₁ a₂ a, a₁ ≤ a → a ≤ a₂ → a₂ ≤ n →
    q a₁ (n - a₁) = false → q a₂ (n - a₂) = false →
    q a (n - a) = false

/-- PLUS (@cite{van-benthem-1984} §7): adding one individual to the
    situation cannot create a "dead end." Both presence and absence must
    be extensible in at least one direction.
    - For + positions: q(a+1,b) or q(a,b+1) is true.
    - For − positions: q(a+1,b) or q(a,b+1) is false. -/
def Plus (q : NumberTreeGQ) : Prop :=
  (∀ a b, q a b = true → q (a + 1) b = true ∨ q a (b + 1) = true) ∧
  (∀ a b, q a b = false → q (a + 1) b = false ∨ q a (b + 1) = false)

/-- UNIF (@cite{van-benthem-1984} §7): the addition experiment
    (a,b) → (a+1,b) and (a,b) → (a,b+1) always yields the same
    pattern for positions of the same truth value. The experiment
    result depends only on whether Q holds, not on *where* in the
    tree we are. -/
def Uniform (q : NumberTreeGQ) : Prop :=
  (∀ a₁ b₁ a₂ b₂, q a₁ b₁ = true → q a₂ b₂ = true →
    q (a₁ + 1) b₁ = q (a₂ + 1) b₂ ∧ q a₁ (b₁ + 1) = q a₂ (b₂ + 1)) ∧
  (∀ a₁ b₁ a₂ b₂, q a₁ b₁ = false → q a₂ b₂ = false →
    q (a₁ + 1) b₁ = q (a₂ + 1) b₂ ∧ q a₁ (b₁ + 1) = q a₂ (b₂ + 1))

-- Verification: the four basic quantifiers satisfy CONT, PLUS, UNIF

private theorem beq_zero_iff (n : Nat) : (n == 0) = true ↔ n = 0 := beq_iff_eq
private theorem beq_zero_false_iff (n : Nat) : (n == 0) = false ↔ n ≠ 0 := by
  cases n <;> simp

theorem allNT_rightCont : RightCont allNT := by
  intro n a₁ _ a ha₁ _ _ h1 _
  simp only [allNT, beq_zero_iff] at *; omega

theorem someNT_rightCont : RightCont someNT := by
  intro n a₁ _ a ha₁ _ _ h1 _
  simp only [someNT, decide_eq_true_eq] at *; omega

theorem noNT_rightCont : RightCont noNT := by
  intro n _ a₂ a _ ha₂ _ _ h2
  simp only [noNT, beq_zero_iff] at *; omega

theorem notAllNT_rightCont : RightCont notAllNT := by
  intro n a₁ _ a ha₁ ha₂ ha₂n h1 _
  simp only [notAllNT, decide_eq_true_eq] at *; omega

theorem allNT_plus : Plus allNT := by
  unfold Plus allNT
  exact ⟨λ _ _ h => Or.inl h,
         λ _ b h => Or.inr (by cases b <;> simp_all)⟩

theorem someNT_plus : Plus someNT := by
  unfold Plus someNT
  constructor
  · intro a _ h; left; simp only [decide_eq_true_eq] at *; omega
  · intro a _ h; right; simp only [decide_eq_false_iff_not, not_le] at *; omega

theorem noNT_plus : Plus noNT := by
  unfold Plus noNT
  exact ⟨λ _ _ h => Or.inr (by simp only [beq_zero_iff] at h; subst h; simp),
         λ _ _ _ => Or.inl (by simp)⟩

theorem notAllNT_plus : Plus notAllNT := by
  unfold Plus notAllNT
  constructor
  · intro _ b h; left; simp only [decide_eq_true_eq] at *; omega
  · intro _ b h; left; simp only [decide_eq_false_iff_not, not_le] at *; omega

theorem allNT_uniform : Uniform allNT := by
  unfold Uniform allNT
  constructor
  · intro _ b₁ _ b₂ h1 h2
    simp only [beq_zero_iff] at h1 h2; subst h1; subst h2; simp
  · intro _ b₁ _ b₂ h1 h2
    simp only [beq_zero_false_iff] at h1 h2
    exact ⟨by rw [beq_false_of_ne h1, beq_false_of_ne h2],
           by rw [beq_false_of_ne (Nat.succ_ne_zero b₁), beq_false_of_ne (Nat.succ_ne_zero b₂)]⟩

theorem someNT_uniform : Uniform someNT := by
  unfold Uniform someNT
  constructor
  · intro a₁ _ a₂ _ h1 h2
    simp only [decide_eq_true_eq] at h1 h2
    constructor <;> simp only [decide_eq_decide] <;> constructor <;> intro <;> omega
  · intro a₁ _ a₂ _ h1 h2
    simp only [decide_eq_false_iff_not, not_le] at h1 h2
    constructor <;> simp only [decide_eq_decide] <;> constructor <;> intro <;> omega

theorem noNT_uniform : Uniform noNT := by
  unfold Uniform noNT
  constructor
  · intro a₁ _ a₂ _ h1 h2
    simp only [beq_zero_iff] at h1 h2; subst h1; subst h2; simp
  · intro a₁ _ a₂ _ h1 h2
    simp only [beq_zero_false_iff] at h1 h2
    exact ⟨by rw [beq_false_of_ne (Nat.succ_ne_zero a₁), beq_false_of_ne (Nat.succ_ne_zero a₂)],
           by rw [beq_false_of_ne h1, beq_false_of_ne h2]⟩

theorem notAllNT_uniform : Uniform notAllNT := by
  unfold Uniform notAllNT
  constructor
  · intro _ b₁ _ b₂ h1 h2
    simp only [decide_eq_true_eq] at h1 h2
    constructor <;> simp only [decide_eq_decide] <;> constructor <;> intro <;> omega
  · intro _ b₁ _ b₂ h1 h2
    simp only [decide_eq_false_iff_not, not_le] at h1 h2
    constructor <;> simp only [decide_eq_decide] <;> constructor <;> intro <;> omega

-- §10e @cite{van-benthem-1984} Theorem 7.1: Square of Opposition uniqueness

/-- The six postulates that @cite{van-benthem-1984} §7 uses to characterize
    the Square of Opposition. -/
structure SixPostulates (q : NumberTreeGQ) : Prop where
  variety : q.Variety
  cont    : q.RightCont
  lcont   : q.LeftCont
  plus    : q.Plus
  uniform : q.Uniform

/-- @cite{van-benthem-1984} Thm 7.1: On the finite sets, the only
    CONSERV+QUANT quantifiers satisfying VAR, CONT, PLUS, and UNIF are
    precisely the four corners of the logical Square of Opposition:
    **all**, **some**, **no**, and **not all**.

    Proof: case analysis on the number tree. At each level, PLUS
    constrains branching, UNIF forces the experiment pattern to be
    uniform, and CONT (right + left) prevents gaps. Together these
    leave exactly four degree-of-freedom choices, each producing
    one quantifier. See @cite{van-benthem-1984} §7 for the
    combinatorial argument. -/
theorem square_uniqueness (q : NumberTreeGQ) (h : SixPostulates q) :
    q = allNT ∨ q = someNT ∨ q = noNT ∨ q = notAllNT := by
  -- The proof proceeds by case analysis on q(0,0) and the
  -- UNIF experiment patterns. Each branch is forced to one of
  -- the four quantifiers by CONT + PLUS + UNIF + VAR.
  sorry

end NumberTreeGQ

-- ============================================================================
-- §10f GQ → NumberTreeGQ Bridge
-- ============================================================================

section NumberTreeBridge
open Classical

/-- Extract the number-tree representation of a CONSERV+QUANT quantifier.
    Under conservativity and quantity-invariance, Q(A,B) depends only on
    `|A ∩ B|` and `|A \ B|`. This definition picks a canonical witness
    pair for each (a,b) coordinate.

    For (a,b) realizable in the domain (a + b ≤ |α|), the value is
    determined by any witness; for unrealizable pairs, we default to false. -/
noncomputable def toNumberTree [Fintype α] (q : GQ α) : NumberTreeGQ :=
  λ a b =>
    if h : ∃ (A B : α → Bool),
      (Finset.univ.filter (λ x => A x && B x)).card = a ∧
      (Finset.univ.filter (λ x => A x && !(B x))).card = b
    then q h.choose h.choose_spec.choose
    else false

/-- The number-tree representation faithfully reflects the GQ on
    realizable coordinates: for any A, B, the GQ's truth value equals
    the number-tree value at (|A∩B|, |A\B|).

    Requires `QuantityInvariant` so that the choice of witness doesn't
    matter — any pair with the same cell cardinalities gives the same
    truth value.

    TODO: the proof requires constructing a cell-preserving bijection
    from matching cardinalities. The machinery exists in
    `Semantics.Lexical.Determiner.Quantifier.build_bijection` but
    uses `FiniteModel` rather than `Fintype`. -/
theorem toNumberTree_spec [Fintype α] [DecidableEq α] (q : GQ α)
    (_hCons : Conservative q) (_hQ : QuantityInvariant q) :
    ∀ (A B : α → Bool),
      q A B = toNumberTree q
        (Finset.univ.filter (λ x => A x && B x)).card
        (Finset.univ.filter (λ x => A x && !(B x))).card := by
  sorry

end NumberTreeBridge

-- ============================================================================
-- §11 Counting Quantifiers (@cite{van-benthem-1984} §5.4)
-- ============================================================================

/-- @cite{van-benthem-1984} Thm 5.4: On a finite set with n individuals, there are
    exactly 2^((n+1)(n+2)/2) conservative quantifiers (satisfying QUANT).
    The tree of numbers has (n+1)(n+2)/2 points at levels a + b ≤ n. -/
def conservativeQuantifierCount (n : Nat) : Nat :=
  2 ^ ((n + 1) * (n + 2) / 2)

#guard conservativeQuantifierCount 0 == 2
#guard conservativeQuantifierCount 1 == 8
#guard conservativeQuantifierCount 2 == 64
#guard conservativeQuantifierCount 3 == 1024
#guard conservativeQuantifierCount 4 == 32768

-- ============================================================================
-- §12 — Conservative GQ Lattice (@cite{elliott-2025})
-- ============================================================================

/-- Conservative GQs form a sublattice of `GQ α`. The `DistribLattice`
    on `GQ α` is inherited from Mathlib's Pi instances (`Bool` is a
    `DistribLattice`, and `(α → Bool) → (α → Bool) → Bool` lifts
    pointwise). Closure under `⊔`/`⊓` follows from
    `conservative_gqJoin`/`conservative_gqMeet` (§8).

    Reference: Elliott, P. (2025). Determiners as predicates. SALT 35. -/
def conservativeSublattice : Sublattice (GQ α) where
  carrier := { q | Conservative q }
  supClosed' q₁ hq₁ q₂ hq₂ := conservative_gqJoin q₁ q₂ hq₁ hq₂
  infClosed' q₁ hq₁ q₂ hq₂ := conservative_gqMeet q₁ q₂ hq₁ hq₂

/-- Conservative GQs: the subtype of `GQ α` satisfying conservativity.
    Forms a bounded distributive lattice under pointwise Boolean operations. Meet is `∧`, join is `∨`, the order is
    pointwise implication. The Birkhoff representation theorem applied to
    this lattice yields polarized individuals as join-irreducible elements.

    The `DistribLattice` instance is inherited from `GQ α` via
    `Sublattice.instDistribLatticeCoe` — no manual axiom proofs needed. -/
abbrev ConsGQ (α : Type*) := conservativeSublattice (α := α)

namespace ConsGQ

variable {α : Type*}

-- Lattice operations agree with gqJoin/gqMeet (definitional)

/-- The join of conservative GQs agrees with `gqJoin`. -/
theorem sup_eq_gqJoin (q₁ q₂ : ConsGQ α) : (q₁ ⊔ q₂).1 = gqJoin q₁.1 q₂.1 := rfl

/-- The meet of conservative GQs agrees with `gqMeet`. -/
theorem inf_eq_gqMeet (q₁ q₂ : ConsGQ α) : (q₁ ⊓ q₂).1 = gqMeet q₁.1 q₂.1 := rfl

-- Bounds

instance : Bot (ConsGQ α) := ⟨⟨⊥, λ _ _ => rfl⟩⟩
instance : Top (ConsGQ α) := ⟨⟨⊤, λ _ _ => rfl⟩⟩

instance : OrderBot (ConsGQ α) where
  bot_le q := show ⊥ ≤ q.1 from bot_le

instance : OrderTop (ConsGQ α) where
  le_top q := show q.1 ≤ ⊤ from le_top

-- Simp API for downstream use

@[simp] theorem sup_val (q₁ q₂ : ConsGQ α) (R S : α → Bool) :
    (q₁ ⊔ q₂).1 R S = (q₁.1 R S || q₂.1 R S) := rfl

@[simp] theorem inf_val (q₁ q₂ : ConsGQ α) (R S : α → Bool) :
    (q₁ ⊓ q₂).1 R S = (q₁.1 R S && q₂.1 R S) := rfl

@[simp] theorem top_val (R S : α → Bool) : (⊤ : ConsGQ α).1 R S = true := rfl

@[simp] theorem bot_val (R S : α → Bool) : (⊥ : ConsGQ α).1 R S = false := rfl

end ConsGQ

end Core.Quantification
