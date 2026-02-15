import Mathlib.Order.Lattice
import Mathlib.Order.Monotone.Defs
import Linglib.Core.NaturalLogic

/-!
# Generalized Quantifier Properties

Model-agnostic properties of generalized quantifier denotations.

A GQ denotation is a function `(α → Bool) → (α → Bool) → Bool` mapping
a restrictor and a scope to a truth value. The properties defined here
(conservativity, monotonicity, duality, intersection condition, symmetry)
are purely logical — they hold at the `Bool`-function level and require
no model infrastructure.

The theory-specific module `TruthConditional.Determiner.Quantifier` defines
concrete denotations (`every_sem`, `some_sem`, etc.) and proves they satisfy
these properties. `m.interpTy Ty.det` is definitionally `GQ m.Entity`, so
all definitions here apply directly.

## Organization

- **§1 Property definitions**: all predicates on GQs, grouped by source
- **§2 Operations**: duality, Boolean algebra, type shifts
- **§3 Mathlib bridge**: connection to `Monotone`/`Antitone`
- **§4–§8 Theorems**: duality, symmetry/strength, Boolean closure,
  type ⟨1⟩, van Benthem characterization

## References

- Barwise, J. & Cooper, R. (1981). Generalized Quantifiers and Natural Language.
- van Benthem, J. (1984). Questions About Quantifiers. J. Symbolic Logic 49(2).
- Keenan, E. & Stavi, J. (1986). A Semantic Characterization of Natural Language Determiners.
- Peters, S. & Westerståhl, D. (2006). Quantifiers in Language and Logic.
-/

namespace Core.Quantification

/-- Generalized quantifier denotation: restrictor → scope → truth value. -/
abbrev GQ (α : Type*) := (α → Bool) → (α → Bool) → Bool

variable {α : Type*}

-- ============================================================================
-- §1 Property Definitions
-- ============================================================================

-- §1.1 Barwise & Cooper (1981) --

/--
Conservativity (Barwise & Cooper 1981): `Q(A, B) = Q(A, A ∩ B)`.

Only the elements of B that are also in A matter for the quantifier's
truth value. Also called "lives on" (B&C) or "intersectivity"
(Higginbotham & May 1981). All simple (lexicalized) determiners
are conservative.
-/
def Conservative (q : GQ α) : Prop :=
  ∀ (R S : α → Bool), q R S = q R (λ x => R x && S x)

/--
Scope-upward-monotone: if B ⊆ B' and Q(A,B), then Q(A,B').

Equivalent to `∀ R, Monotone (q R)` under pointwise Bool ordering
(see `scopeUpMono_iff_monotone`). This connects to
`TruthConditional.Core.Polarity.IsUpwardEntailing = Monotone`.
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

/-- Intersection condition (B&C Def 27): Q(A,B) depends only on A∩B. -/
def IntersectionCondition (q : GQ α) : Prop :=
  ∀ (R S R' S' : α → Bool),
    (∀ x, (R x && S x) = (R' x && S' x)) →
    q R S = q R' S'

/-- Symmetric: Q(A,B) = Q(B,A) (B&C Theorem C5). -/
def QSymmetric (q : GQ α) : Prop :=
  ∀ (R S : α → Bool), q R S = q S R

/-- Restrictor-upward-monotone (persistent): if A ⊆ A' then Q(A,B) → Q(A',B).
    B&C §4.9: linked to weak determiners and there-insertion. -/
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

-- §1.2 Peters & Westerståhl (2006) --

/-- Extension (EXT): Q(A,B) depends only on A and B, not on the ambient
    universe M. In model-theoretic GQ theory (where Q^M takes a universe),
    EXT must be stated as an additional axiom. For `GQ α`, EXT holds
    trivially since there is no universe parameter — it's a design theorem.

    Significance: EXT + CONS characterize "well-behaved" determiners
    (van Benthem 1984). See `vanBenthem_cons_ext`.

    Reference: Peters & Westerståhl Ch.4 Def 4.1. -/
def Extension (_q : GQ α) : Prop := True

/-- Second conservativity: Q(A,B) = Q(A∩B, B). P&W Ch.6. -/
def CONS2 (q : GQ α) : Prop :=
  ∀ (R S : α → Bool), q R S = q (λ x => R x && S x) S

/-- Existential property: Q(A,B) = Q(A∩B, everything). P&W Ch.6.
    Characterizes determiners that are felicitous in there-sentences. -/
def Existential (q : GQ α) : Prop :=
  ∀ (R S : α → Bool), q R S = q (λ x => R x && S x) (λ _ => true)

/-- Left anti-additive: Q(A∪B, C) ↔ Q(A,C) ∧ Q(B,C). P&W §5.9. -/
def LeftAntiAdditive (q : GQ α) : Prop :=
  ∀ (R R' S : α → Bool),
    q (λ x => R x || R' x) S = (q R S && q R' S)

/-- Right anti-additive: Q(A, B∪C) ↔ Q(A,B) ∧ Q(A,C). P&W §5.9. -/
def RightAntiAdditive (q : GQ α) : Prop :=
  ∀ (R S S' : α → Bool),
    q R (λ x => S x || S' x) = (q R S && q R S')

-- §1.3 Van Benthem (1984): Relational properties --

/-- Transitive: Q(A,B) ∧ Q(B,C) → Q(A,C). Van Benthem 1984 §3.1.
    "all" is the prime transitive quantifier (inclusion is transitive). -/
def QTransitive (q : GQ α) : Prop :=
  ∀ (A B C : α → Bool), q A B = true → q B C = true → q A C = true

/-- Antisymmetric: Q(A,B) ∧ Q(B,A) → A = B (extensionally).
    Van Benthem 1984 §3.1: "all" (inclusion) is antisymmetric. -/
def QAntisymmetric (q : GQ α) : Prop :=
  ∀ (A B : α → Bool), q A B = true → q B A = true → A = B

/-- Linear (connected): Q(A,B) ∨ Q(B,A) for all A, B.
    Van Benthem 1984 §3.1: "not all" (non-inclusion) is linear. -/
def QLinear (q : GQ α) : Prop :=
  ∀ (A B : α → Bool), q A B = true ∨ q B A = true

/-- Quasi-reflexive: Q(A,B) → Q(A,A). Van Benthem 1984 §3.1.
    "some" is quasi-reflexive: overlap implies non-emptiness. -/
def QuasiReflexive (q : GQ α) : Prop :=
  ∀ (A B : α → Bool), q A B = true → q A A = true

/-- Quasi-universal: Q(A,A) → Q(A,B) for all B. Van Benthem 1984 §3.1.
    "no" is quasi-universal: if A∩A = ∅ then A∩B = ∅ for all B. -/
def QuasiUniversal (q : GQ α) : Prop :=
  ∀ (A B : α → Bool), q A A = true → q A B = true

/-- Almost-connected: Q(A,B) → Q(A,C) ∨ Q(C,B) for all C.
    Van Benthem 1984 §3.1: equivalent to transitivity of ¬Q.
    "not all" is almost-connected. -/
def AlmostConnected (q : GQ α) : Prop :=
  ∀ (A B C : α → Bool), q A B = true → q A C = true ∨ q C B = true

/-- VAR (Variety): Q is non-trivial — it both accepts and rejects some pair.
    Van Benthem 1984 §2: rules out degenerate quantifiers like "at least 2"
    on singleton domains. Used as hypothesis in most uniqueness theorems. -/
def Variety (q : GQ α) : Prop :=
  (∃ A B, q A B = true) ∧ (∃ A B, q A B = false)

/-- Double monotonicity type (van Benthem 1984 §4.2).
    The logical Square of Opposition maps to four double-monotonicity types:
    all = ↓MON↑, some = ↑MON↑, no = ↓MON↓, not all = ↑MON↓. -/
inductive DoubleMono where
  | upUp     -- ↑MON↑: restrictor-↑ + scope-↑ (some)
  | downUp   -- ↓MON↑: restrictor-↓ + scope-↑ (all)
  | upDown   -- ↑MON↓: restrictor-↑ + scope-↓ (not all)
  | downDown -- ↓MON↓: restrictor-↓ + scope-↓ (no)
  deriving DecidableEq, Repr, BEq

/-- Right continuity (CONT): if Q(A,B₁) and Q(A,B₂) hold and B₁ ⊆ B ⊆ B₂,
    then Q(A,B). Van Benthem 1984 §4.3: all right-monotone quantifiers are
    continuous. "precisely one" is continuous but non-monotone. -/
def RightContinuous (q : GQ α) : Prop :=
  ∀ (A B B₁ B₂ : α → Bool),
    (∀ x, B₁ x = true → B x = true) →
    (∀ x, B x = true → B₂ x = true) →
    q A B₁ = true → q A B₂ = true → q A B = true

/-- Filtrating: Q(A,B) ∧ Q(A,C) → Q(A, B∩C).
    Van Benthem 1984 Thm 4.4.2: "all" is the only filtrating quantifier
    (under VAR*). This is because filtrating ↔ filter (closure under ∩),
    and only the principal filter at A (= inclusion) satisfies CONSERV. -/
def Filtrating (q : GQ α) : Prop :=
  ∀ (A B C : α → Bool),
    q A B = true → q A C = true → q A (λ x => B x && C x) = true

-- §1.4 Mostowski (1957) --

/-- QUANT (Isomorphism closure): Q is invariant under permutations of the
    domain. Model-agnostic version: Q(A,B) depends only on the pointwise
    Boolean pattern, not on which specific elements satisfy A and B.
    This is the model-agnostic formulation of Mostowski (1957).

    The model-specific version in `TruthConditional.Determiner.Quantifier.Quantity`
    uses cardinalities directly, which requires `FiniteModel`. This version
    captures the same intuition without model infrastructure.

    Van Benthem 1984 §2: CONSERV + QUANT together reduce Q's behavior to
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

/-- Outer negation reverses scope monotonicity: mon↑ → mon↓ (B&C C9). -/
theorem outerNeg_up_to_down (q : GQ α)
    (h : ScopeUpwardMono q) : ScopeDownwardMono (outerNeg q) := by
  intro R S S' hSS' hNeg
  simp only [outerNeg] at *
  cases hqRS : q R S
  · rfl
  · have := h R S S' hSS' hqRS; simp [this] at hNeg

/-- Outer negation reverses scope monotonicity: mon↓ → mon↑ (B&C C9). -/
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

/-- Van Benthem (1984): Under Extension (free for GQ α), Conservativity
    is equivalent to LivesOn — the restricted quantifier depends only on
    elements of its restrictor. This is the `CONS + EXT ↔ Rel(⟨1⟩)`
    characterization of "well-behaved" type ⟨1,1⟩ quantifiers.

    Our `conservative_iff_livesOn` doesn't need an EXT hypothesis because
    `GQ α` already bakes it in. -/
theorem vanBenthem_cons_ext (q : GQ α) :
    Extension q → (Conservative q ↔ ∀ A, LivesOn (restrict q A) A) :=
  λ _ => conservative_iff_livesOn q

-- ============================================================================
-- §6 Boolean Closure (K&S 1986)
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
-- §8 Van Benthem (1984) Characterization
-- ============================================================================

/-- Van Benthem (1984) Theorem 3.1.1: Under conservativity, inclusion (⊆)
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

/-- Van Benthem 1984 Thm 4.1.1 (Zwarts): reflexive + transitive → MON↑.
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

/-- Van Benthem 1984 Thm 4.1.1 (Zwarts): reflexive + transitive → ↓MON.
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

/-- Van Benthem 1984 Thm 4.1.3 (Zwarts): for symmetric quantifiers,
    scope-↑ implies quasi-reflexive, under CONSERV. -/
theorem zwarts_sym_scopeUp_quasiRefl (q : GQ α)
    (hCons : Conservative q) (_hSym : QSymmetric q)
    (hUp : ScopeUpwardMono q) : QuasiReflexive q := by
  intro A B hQAB
  have h1 : q A (λ x => A x && B x) = true := by rw [← hCons]; exact hQAB
  exact hUp A (λ x => A x && B x) A
    (fun x hx => by cases hA : A x <;> simp_all) h1

/-- Van Benthem 1984 Thm 4.1.3 (Zwarts): for symmetric quantifiers,
    scope-↓ implies quasi-universal, under CONSERV. -/
theorem zwarts_sym_scopeDown_quasiUniv (q : GQ α)
    (hCons : Conservative q) (_hSym : QSymmetric q)
    (hDown : ScopeDownwardMono q) : QuasiUniversal q := by
  intro A B hQAA
  rw [hCons A B]
  exact hDown A (λ x => A x && B x) A
    (fun x hx => by cases hA : A x <;> simp_all) hQAA

/-- Right-monotone quantifiers are right-continuous (van Benthem 1984 §4.3). -/
theorem scopeUpMono_rightContinuous (q : GQ α)
    (h : ScopeUpwardMono q) : RightContinuous q := by
  intro A B B₁ _ hB₁B _ hQ1 _
  exact h A B₁ B hB₁B hQ1


-- ============================================================================
-- §9 — Entailment Signature Bridge (Icard 2012, Table p.720)
-- ============================================================================

open Core.NaturalLogic (EntailmentSig ContextPolarity)

/--
Map a pair of entailment signatures (restrictor, scope) to `DoubleMono`,
the van Benthem (1984) double monotonicity classification.

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

end Core.Quantification
