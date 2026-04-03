import Mathlib.Order.Lattice
import Mathlib.Order.Monotone.Defs
import Mathlib.Order.Sublattice
import Linglib.Core.Logic.NaturalLogic
import Linglib.Tactics.OntSort

/-!
# Generalized Quantifier Definitions
@cite{barwise-cooper-1981} @cite{keenan-stavi-1986} @cite{peters-westerstahl-2006} @cite{van-benthem-1984}

Model-agnostic property definitions, operations, and type shifts for
generalized quantifier denotations.

A GQ denotation is a function `(α → Bool) → (α → Bool) → Bool` mapping
a restrictor and a scope to a truth value. The properties defined here
(conservativity, monotonicity, duality, intersection condition, symmetry)
are purely logical — they hold at the `Bool`-function level and require
no model infrastructure.

The theory-specific module `Semantics.Lexical.Determiner.Quantifier` defines
concrete denotations (`every_sem`, `some_sem`, etc.) and proves they satisfy
these properties.

## Contents

- **§1 Property definitions**: all predicates on GQs, grouped by source
- **§2 Operations**: duality, Boolean algebra, type shifts
- **§3 Mathlib bridge**: connection to `Monotone`/`Antitone`
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

/-- Asymmetric: Q(A,B) → ¬Q(B,A). @cite{peters-westerstahl-2006} Ch 6.4.
    Strictly stronger than antisymmetric: antisymmetry allows Q(A,B) ∧ Q(B,A)
    when A = B; asymmetry forbids it entirely. Under CONSERV + ISOM, no
    non-trivial quantifier is asymmetric (P&W Ch 6.4). -/
def QAsymmetric (q : GQ α) : Prop :=
  ∀ (A B : α → Bool), q A B = true → q B A = false

/-- Reflexive (relational vocabulary): Q(A,A) for all A.
    Definitionally equal to `PositiveStrong`; included for relational vocabulary
    alignment with @cite{peters-westerstahl-2006} Ch 6.4 and @cite{van-benthem-1984}. -/
abbrev QReflexive (q : GQ α) : Prop := PositiveStrong q

/-- Irreflexive (relational vocabulary): Q(A,A) = false for all A.
    Definitionally equal to `NegativeStrong`; included for relational vocabulary
    alignment with @cite{peters-westerstahl-2006} Ch 6.4. -/
abbrev QIrreflexive (q : GQ α) : Prop := NegativeStrong q

/-- Circular: Q(A,B) ∧ Q(B,C) → Q(C,A). @cite{peters-westerstahl-2006} Ch 6.4.
    No natural language quantifier is non-trivially circular (under CONSERV + ISOM).
    Together with transitivity, circularity forces quasi-reflexivity. -/
def QCircular (q : GQ α) : Prop :=
  ∀ (A B C : α → Bool), q A B = true → q B C = true → q C A = true

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

-- §1.5 Monotonicity Universals (@cite{peters-westerstahl-2006} Ch 5.8) --

/-- MU1: All simple (lexicalized) determiners are monotone in scope.
    @cite{peters-westerstahl-2006} §5.8 Universal 1. -/
def MU1 (q : GQ α) : Prop := ScopeUpwardMono q ∨ ScopeDownwardMono q

/-- MU2: All simple determiners are monotone in at least one restrictor direction.
    @cite{peters-westerstahl-2006} §5.8 Universal 2. -/
def MU2 (q : GQ α) : Prop := RestrictorUpwardMono q ∨ RestrictorDownwardMono q

/-- MU3: All simple Mon↑ determiners are smooth.
    @cite{peters-westerstahl-2006} §5.8 Universal 3. -/
def MU3 (q : GQ α) : Prop := ScopeUpwardMono q → Smooth q

/-- MU4: All simple Mon↓ determiners are co-smooth.
    @cite{peters-westerstahl-2006} §5.8 Universal 4. -/
def MU4 (q : GQ α) : Prop := ScopeDownwardMono q → CoSmooth q

-- §1.6 @cite{mostowski-1957} --

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

end Core.Quantification
