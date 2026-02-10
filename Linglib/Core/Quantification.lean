import Mathlib.Order.Lattice
import Mathlib.Order.Monotone.Defs

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

## Main definitions

- `GQ α`: type abbreviation for `(α → Bool) → (α → Bool) → Bool`
- `Conservative`, `ScopeUpwardMono`, `ScopeDownwardMono`: B&C universals
- `Extension`: domain-independence (P&W Ch.4); trivially satisfied by `GQ α`
- `IntersectionCondition`, `QSymmetric`: B&C §4.3–4.8
- `RestrictorUpwardMono`, `RestrictorDownwardMono`: persistence
- `outerNeg`, `innerNeg`, `dualQ`: B&C §4.11 duality operations

## References

- Barwise, J. & Cooper, R. (1981). Generalized Quantifiers and Natural Language.
- Keenan, E. & Stavi, J. (1986). A Semantic Characterization of Natural Language Determiners.
-/

namespace Core.Quantification

/-- Generalized quantifier denotation: restrictor → scope → truth value. -/
abbrev GQ (α : Type*) := (α → Bool) → (α → Bool) → Bool

-- ============================================================================
-- Properties
-- ============================================================================

variable {α : Type*}

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

-- ============================================================================
-- Bridge to Mathlib Monotone/Antitone
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
-- Duality Operations (B&C §4.11)
-- ============================================================================

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

-- ============================================================================
-- Duality Theorems
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

-- ============================================================================
-- Missing duality theorem (gap F)
-- ============================================================================

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

-- ============================================================================
-- Involution theorems (P&W §1.1.1: square closure)
-- ============================================================================

/-- Outer negation is involutive: ~~Q = Q. -/
theorem outerNeg_involution (q : GQ α) : outerNeg (outerNeg q) = q := by
  funext R S; simp [outerNeg, Bool.not_not]

/-- Inner negation is involutive: Q~~ = Q. -/
theorem innerNeg_involution (q : GQ α) : innerNeg (innerNeg q) = q := by
  funext R S; simp [innerNeg, Bool.not_not]

/-- Dual is involutive: Q̌̌ = Q. -/
theorem dualQ_involution (q : GQ α) : dualQ (dualQ q) = q := by
  funext R S; simp [dualQ, outerNeg, innerNeg, Bool.not_not]

-- ============================================================================
-- Restrictor duality (gap F)
-- ============================================================================

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

-- ============================================================================
-- Type ⟨1⟩ quantifiers (P&W Ch.2-3)
-- ============================================================================

/-- NP denotation (type ⟨1⟩): a property of properties.
    This is the model-agnostic version of `Ty.ett` from TypeShifting.lean.
    P&W §2.1: an NP like "every student" denotes a set of sets. -/
abbrev NPQ (α : Type*) := (α → Bool) → Bool

/-- Restriction: given a GQ Q and restrictor A, produce the type ⟨1⟩
    quantifier Q^[A] (P&W §3.2.2). `restrict Q A B = Q A B`. -/
def restrict (q : GQ α) (A : α → Bool) : NPQ α := q A

-- ============================================================================
-- LivesOn + conservative bridge (P&W §3.2.2)
-- ============================================================================

/-- A type ⟨1⟩ quantifier Q "lives on" A iff Q(B) = Q(A ∩ B) for all B.
    P&W §3.2.2: the restricted quantifier depends only on elements of A. -/
def LivesOn (Q : NPQ α) (A : α → Bool) : Prop :=
  ∀ B, Q B = Q (λ x => A x && B x)

/-- Conservativity of a GQ is equivalent to its restricted quantifiers
    living on their restrictors (P&W §3.2.2). -/
theorem conservative_iff_livesOn (q : GQ α) :
    Conservative q ↔ ∀ A, LivesOn (restrict q A) A := by
  unfold Conservative LivesOn restrict
  constructor
  · intro h A B; exact h A B
  · intro h R S; exact h R S

-- ============================================================================
-- Montagovian individuals (P&W §3.2.3-4)
-- ============================================================================

/-- Montagovian individual: the type ⟨1⟩ quantifier I_a = {X : a ∈ X}.
    P&W §3.2.3: an entity lifts to the principal ultrafilter it generates. -/
def individual (a : α) : NPQ α := λ P => P a

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
-- Co-property monotonicity (P&W §3.2.4)
-- ============================================================================

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
-- Second conservativity + Existential (P&W Ch.6 Fact 5)
-- ============================================================================

/-- Second conservativity: Q(A,B) = Q(A∩B, B). P&W Ch.6. -/
def CONS2 (q : GQ α) : Prop :=
  ∀ (R S : α → Bool), q R S = q (λ x => R x && S x) S

/-- Existential property: Q(A,B) = Q(A∩B, everything). P&W Ch.6.
    Characterizes determiners that are felicitous in there-sentences. -/
def Existential (q : GQ α) : Prop :=
  ∀ (R S : α → Bool), q R S = q (λ x => R x && S x) (λ _ => true)

-- ============================================================================
-- CONSERV → (SYMM ↔ INT) (P&W Ch.6 Fact 1)
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

-- ============================================================================
-- Positive/Negative strong (B&C 1981, P&W Ch.6)
-- ============================================================================

/-- Positive strong: Q(A,A) for all A. P&W Ch.6: "every", "most", "the". -/
def PositiveStrong (q : GQ α) : Prop :=
  ∀ (R : α → Bool), q R R = true

/-- Negative strong: ¬Q(A,A) for all A. "Neither". -/
def NegativeStrong (q : GQ α) : Prop :=
  ∀ (R : α → Bool), q R R = false

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

-- ============================================================================
-- Left/Right anti-additivity for GQ (P&W Ch.5 §5.9)
-- ============================================================================

/-- Left anti-additive: Q(A∪B, C) ↔ Q(A,C) ∧ Q(B,C). P&W §5.9. -/
def LeftAntiAdditive (q : GQ α) : Prop :=
  ∀ (R R' S : α → Bool),
    q (λ x => R x || R' x) S = (q R S && q R' S)

/-- Right anti-additive: Q(A, B∪C) ↔ Q(A,B) ∧ Q(A,C). P&W §5.9. -/
def RightAntiAdditive (q : GQ α) : Prop :=
  ∀ (R S S' : α → Bool),
    q R (λ x => S x || S' x) = (q R S && q R S')

-- ============================================================================
-- Extension (P&W Ch.4 Def 4.1)
-- ============================================================================

/-- Extension (EXT): Q(A,B) depends only on A and B, not on the ambient
    universe M. In model-theoretic GQ theory (where Q^M takes a universe),
    EXT must be stated as an additional axiom. For `GQ α`, EXT holds
    trivially since there is no universe parameter — it's a design theorem.

    Significance: EXT + CONS characterize "well-behaved" determiners
    (van Benthem 1984). See `vanBenthem_cons_ext`.

    Reference: Peters & Westerståhl Ch.4 Def 4.1. -/
def Extension (_q : GQ α) : Prop := True

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
-- Boolean operations on GQ (K&S §2.3: D_Det closure)
-- ============================================================================

/-- Meet of two GQ denotations: (f ∧ g)(A,B) = f(A,B) ∧ g(A,B).
    K&S (20): conjunction of dets, e.g., "both John's and Mary's".
    Also: "between n and m" = (at least n) ∧ (at most m). -/
def gqMeet (f g : GQ α) : GQ α :=
  λ R S => f R S && g R S

/-- Join of two GQ denotations: (f ∨ g)(A,B) = f(A,B) ∨ g(A,B).
    K&S (24): disjunction of dets, e.g., "either John's or Mary's". -/
def gqJoin (f g : GQ α) : GQ α :=
  λ R S => f R S || g R S

-- ============================================================================
-- Boolean closure of conservativity (K&S PROP 1)
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

-- ============================================================================
-- De Morgan laws on GQ (K&S equation 26)
-- ============================================================================

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

-- ============================================================================
-- Monotonicity closure under boolean operations (K&S PROP 6)
-- ============================================================================

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

-- ============================================================================
-- Adjectival restriction (K&S PROP 3, 5)
-- ============================================================================

/-- Restriction of a GQ by a restricting function (adjective/relative clause).
    K&S (66): h_f(s) = h(f(s)). In our representation, the adjective
    narrows the restrictor: "tall student" = student ∧ tall. -/
def adjRestrict (q : GQ α) (adj : α → Bool) : GQ α :=
  λ R S => q (λ x => R x && adj x) S

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

end Core.Quantification
