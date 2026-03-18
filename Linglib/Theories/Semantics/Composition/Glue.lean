import Linglib.Theories.Semantics.Montague.Types
import Linglib.Theories.Semantics.Composition.Scope
import Linglib.Theories.Semantics.Lexical.Determiner.Quantifier
import Linglib.Theories.Semantics.Composition.Tree
import Linglib.Theories.Semantics.Montague.Variables

/-!
# Glue Semantics
@cite{asudeh-2022}

Glue Semantics is a composition framework where meanings are assembled
via proof search in the implicational fragment of linear logic (⊸).
Meaning constructors are pairs M : G, where M is a lambda term and G is
a linear logic formula. Composition corresponds to ⊸-elimination
(functional application) and ⊸-introduction (lambda abstraction) via
the Curry-Howard isomorphism.

## Key properties (@cite{asudeh-2022}, §1)

1. **Resource-sensitive composition**: Each premise is used exactly once
   (no weakening, no contraction). This subsumes the Theta Criterion,
   Projection Principle, Full Interpretation, Completeness/Coherence,
   No Vacuous Quantification, and the Inclusiveness Condition as
   instances of a single logical principle.
2. **Flexible composition**: The logic is commutative — word order
   doesn't determine composition order.
3. **Autonomy of syntax**: Structural syntax and the logical syntax of
   composition are separate levels.
4. **Syntax/semantics non-isomorphism**: One word may contribute
   multiple or zero meaning constructors.

## Scope ambiguity

"Everybody loves somebody" (@cite{asudeh-2022}, §4.2) yields two
scope readings. Each reading corresponds to a different instantiation
of the second-order ∀ in the quantifier types, producing a different
premise multiset. Each multiset has exactly one normal-form proof.

## Integration with linglib

This module connects Glue to:
- `ScopeConfig` from `Montague/Scope.lean`
- `interp`-based QR composition from `Composition/Tree.lean`
- `QuantifierComposition.lean` for the same scope example via H&K

The bridge theorem `glue_qr_agree` proves that Glue proof search and
QR tree interpretation yield the same truth values on the canonical
scope example.
-/

namespace Semantics.Composition.Glue

open Semantics.Montague
open Semantics.Lexical.Determiner.Quantifier

-- ════════════════════════════════════════════════════════════════════
-- § Glue Logic: Implicational Fragment of Linear Logic
-- ════════════════════════════════════════════════════════════════════

/-- Glue types: the implicational fragment of linear logic.

    Atomic types are parameterized by strings corresponding to
    s-structure nodes (e.g. `"e"` for the subject's semantic
    contribution, `"l"` for the clause). The linear implication
    `A ⊸ B` corresponds to `lolli A B`. -/
inductive GlueTy where
  | atom : String → GlueTy
  | lolli : GlueTy → GlueTy → GlueTy
  deriving DecidableEq, Repr

infixr:25 " ⊸ " => GlueTy.lolli

/-- A meaning constructor: a meaning term M paired with a Glue type G.
    Written `M : G` in the Glue literature (@cite{asudeh-2022}, §2). -/
structure MeaningConstructor (α : Type) where
  meaning : α
  glue : GlueTy
  deriving Repr

-- ════════════════════════════════════════════════════════════════════
-- § Proof Terms (Curry-Howard for ⊸)
-- ════════════════════════════════════════════════════════════════════

/-- Proof terms for the implicational fragment of linear logic.

    By Curry-Howard, these are simply-typed linear lambda terms:
    - `ax n` : use the term at context index n (premise or hypothesis)
    - `lolliE f a` : ⊸-elimination = functional application
    - `lolliI hypTy body` : ⊸-introduction = lambda abstraction.
      Extends the context with `hypTy`; the hypothesis is accessed
      in `body` via its new index (`ctx.length`). -/
inductive GlueProof : Type where
  | ax : Nat → GlueProof
  | lolliE : GlueProof → GlueProof → GlueProof
  | lolliI : GlueTy → GlueProof → GlueProof
  deriving Repr, DecidableEq

-- ════════════════════════════════════════════════════════════════════
-- § Type Checking
-- ════════════════════════════════════════════════════════════════════

/-- Type-check a proof against a context (premises ++ hypotheses).
    `lolliI` extends the context by appending the hypothesis type;
    the hypothesis is accessed in the body at index `ctx.length`.
    Returns the conclusion type if well-typed. -/
def GlueProof.check (ctx : List GlueTy) : GlueProof → Option GlueTy
  | .ax n => ctx[n]?
  | .lolliE f a => do
    let fTy ← f.check ctx
    let aTy ← a.check ctx
    match fTy with
    | .lolli dom cod =>
      if dom = aTy then some cod else none
    | _ => none
  | .lolliI hypTy body => do
    let bodyTy ← body.check (ctx ++ [hypTy])
    some (hypTy ⊸ bodyTy)

/-- Indices of *premises* (from the original context) used by a proof.
    Hypothesis indices (≥ numPremises) are excluded. -/
def GlueProof.usedPremises (numPremises : Nat) : GlueProof → List Nat
  | .ax n => if n < numPremises then [n] else []
  | .lolliE f a => f.usedPremises numPremises ++ a.usedPremises numPremises
  | .lolliI _ body => body.usedPremises numPremises

/-- A proof is resource-correct if every premise is used exactly once. -/
def GlueProof.isResourceCorrect (numPremises : Nat) (p : GlueProof)
    : Bool :=
  (p.usedPremises numPremises).mergeSort (· ≤ ·) == List.range numPremises

-- ════════════════════════════════════════════════════════════════════
-- § Substructural Logic Hierarchy (@cite{asudeh-2022}, §3)
-- ════════════════════════════════════════════════════════════════════

/-! ### The logic landscape

@cite{asudeh-2022} (§3) situates linear logic in a hierarchy of
substructural logics (Figure 1). Logics are characterized by which
structural rules they admit:

- **Weakening**: A premise can be freely added (Γ⊢B → Γ,A⊢B)
- **Contraction**: A duplicate premise can be freely discarded (Γ,A,A⊢B → Γ,A⊢B)
- **Commutativity**: Premises can be freely reordered (Γ,A,B⊢C → Γ,B,A⊢C)

Lambek logic L has none of these. Linear logic adds commutativity.
Relevance logic adds contraction. Affine/BCK logic adds weakening.
Intuitionistic logic has all three.

Semantics is best modeled by a commutative resource logic: composition
is order-independent (Klein & Sag 1985: types, not order, determine
composition) but resource-sensitive (each meaning used exactly once).
-/

/-- Structural rules that characterize logics in the substructural
    hierarchy. -/
inductive StructuralRule where
  | weakening      -- A premise can be freely added
  | contraction    -- A duplicate premise can be freely discarded
  | commutativity  -- Premises can be freely reordered
  deriving DecidableEq, Repr

/-- Substructural logics, ordered by which structural rules they admit
    (@cite{asudeh-2022}, §3, Figure 1). -/
inductive SubstructuralLogic where
  | lambekL        -- No structural rules (noncommutative resource logic)
  | linearLogic    -- + commutativity (commutative resource logic = Glue)
  | relevance      -- + commutativity + contraction
  | affineBCK      -- + commutativity + weakening
  | intuitionistic -- + all three structural rules
  deriving DecidableEq, Repr

def SubstructuralLogic.admitsRule : SubstructuralLogic → StructuralRule → Bool
  | .lambekL,        _ => false
  | .linearLogic,    .commutativity => true
  | .linearLogic,    _ => false
  | .relevance,      .weakening => false
  | .relevance,      _ => true
  | .affineBCK,      .contraction => false
  | .affineBCK,      _ => true
  | .intuitionistic, _ => true

def SubstructuralLogic.isResourceSensitive : SubstructuralLogic → Bool
  | .lambekL => true
  | .linearLogic => true
  | _ => false

/-- The Glue logic is linear logic. -/
def glueLogic : SubstructuralLogic := .linearLogic

theorem glue_is_commutative :
    glueLogic.admitsRule .commutativity = true := rfl

theorem glue_no_weakening :
    glueLogic.admitsRule .weakening = false := rfl

theorem glue_no_contraction :
    glueLogic.admitsRule .contraction = false := rfl

theorem glue_is_resource_sensitive :
    glueLogic.isResourceSensitive = true := rfl

-- ════════════════════════════════════════════════════════════════════
-- § "Alex likes Blake" — Basic Glue Composition
-- ════════════════════════════════════════════════════════════════════

/-! ### Simple transitive composition (@cite{asudeh-2022}, §2)

The simplest Glue derivation: a transitive verb with two arguments.
Given meaning constructors:
```
likes : λy.λx.like(y)(x) : b ⊸ a ⊸ l
alex  : alex              : a
blake : blake              : b
```

The unique normal-form proof applies likes to blake, then to alex:
```
likes : b⊸a⊸l    blake : b
────────────────────────── ⊸ε
   like(blake) : a⊸l      alex : a
   ────────────────────────────── ⊸ε
        like(blake)(alex) : l
```
-/

section AlexLikesBlake

def a_ := GlueTy.atom "a"  -- subject (alex)
def b_ := GlueTy.atom "b"  -- object (blake)
def l_ := GlueTy.atom "l"  -- clause type

/-- Premises for "Alex likes Blake". -/
def alexLikesBlakePremises : List GlueTy :=
  [ b_ ⊸ a_ ⊸ l_   -- 0: likes
  , a_               -- 1: alex
  , b_               -- 2: blake
  ]

/-- Proof: apply likes to blake, then to alex. -/
def alexLikesBlakeProof : GlueProof :=
  .lolliE (.lolliE (.ax 0) (.ax 2)) (.ax 1)

theorem alex_likes_blake_typechecks :
    alexLikesBlakeProof.check alexLikesBlakePremises = some l_ := by
  native_decide

theorem alex_likes_blake_resource_correct :
    alexLikesBlakeProof.isResourceCorrect 3 = true := by native_decide

/-- Argument reordering: the same proof works regardless of premise order,
    because the Glue logic is commutative (@cite{asudeh-2022}, §2). -/
def alexLikesBlakeReordered : List GlueTy :=
  [ a_               -- 0: alex (moved first)
  , b_               -- 1: blake
  , b_ ⊸ a_ ⊸ l_   -- 2: likes (moved last)
  ]

def alexLikesBlakeReorderedProof : GlueProof :=
  .lolliE (.lolliE (.ax 2) (.ax 1)) (.ax 0)

theorem reordered_typechecks :
    alexLikesBlakeReorderedProof.check alexLikesBlakeReordered = some l_ := by
  native_decide

theorem reordered_resource_correct :
    alexLikesBlakeReorderedProof.isResourceCorrect 3 = true := by
  native_decide

end AlexLikesBlake

-- ════════════════════════════════════════════════════════════════════
-- § "Everybody loves somebody" — The Canonical Scope Example
-- ════════════════════════════════════════════════════════════════════

/-! ### Meaning constructors (@cite{asudeh-2022}, §4.2)

Lexical entries (before instantiation):
```
love    : λy.λx.love(y)(x)     : (↑ OBJ)σ ⊸ (↑ SUBJ)σ ⊸ ↑σ
every   : λQ.every(person, Q)  : ∀S.(e ⊸ S) → S
some    : λQ.some(person, Q)   : ∀S.(s ⊸ S) → S
```

The ∀ quantifier in the Glue logic ranges over Glue types. Different
instantiations of S yield different premise contexts, and each context
has exactly one normal-form proof.

**Surface scope (∀>∃)**: every instantiated with S=l, some with S=e⊸l.
**Inverse scope (∃>∀)**: some instantiated with S=l, every with S=s⊸l.
-/

section EveryLovesSome

-- Reuse l_ from AlexLikesBlake; define additional atomic types
-- for the quantifier scope example
def e_ := GlueTy.atom "e"  -- subject position
def s_ := GlueTy.atom "s"  -- object position

-- Surface scope (∀>∃) premises
def surfacePremises : List GlueTy :=
  [ s_ ⊸ e_ ⊸ l_                        -- 0: love
  , (s_ ⊸ e_ ⊸ l_) ⊸ (e_ ⊸ l_)        -- 1: some (S = e ⊸ l)
  , (e_ ⊸ l_) ⊸ l_                      -- 2: every (S = l)
  ]

-- Inverse scope (∃>∀) premises
def inversePremises : List GlueTy :=
  [ s_ ⊸ e_ ⊸ l_                        -- 0: love
  , (e_ ⊸ s_ ⊸ l_) ⊸ (s_ ⊸ l_)        -- 1: every (S = s ⊸ l)
  , (s_ ⊸ l_) ⊸ l_                      -- 2: some (S = l)
  ]

/-- Surface scope proof: every(some(love)) : l

    Proof structure (cf. @cite{asudeh-2022}, Figure 4):
    1. Apply some(S=e⊸l) to love → e ⊸ l
    2. Apply every(S=l) to result → l -/
def surfaceProof : GlueProof :=
  .lolliE (.ax 2) (.lolliE (.ax 1) (.ax 0))

/-- Inverse scope proof: some(every(λv.λu.love(u)(v))) : l

    Proof structure (cf. @cite{asudeh-2022}, Figure 5):
    1. Assume [v:e]³, [u:s]⁴
    2. Apply love to u (s-arg) then to v (e-arg) → l
    3. Abstract over u → s⊸l, then over v → e⊸s⊸l
    4. Apply every(S=s⊸l) → s⊸l
    5. Apply some(S=l) → l -/
def inverseProof : GlueProof :=
  .lolliE (.ax 2)
    (.lolliE (.ax 1)
      (.lolliI e_
        (.lolliI s_
          (.lolliE (.lolliE (.ax 0) (.ax 4)) (.ax 3)))))

/-- Surface proof type-checks to l. -/
theorem surface_typechecks :
    surfaceProof.check surfacePremises = some l_ := by native_decide

/-- Inverse proof type-checks to l. -/
theorem inverse_typechecks :
    inverseProof.check inversePremises = some l_ := by native_decide

/-- Surface proof uses each premise exactly once. -/
theorem surface_resource_correct :
    surfaceProof.isResourceCorrect 3 = true := by native_decide

/-- Inverse proof uses each premise exactly once. -/
theorem inverse_resource_correct :
    inverseProof.isResourceCorrect 3 = true := by native_decide

end EveryLovesSome

-- ════════════════════════════════════════════════════════════════════
-- § Semantic Evaluation: Connecting Proofs to Truth Conditions
-- ════════════════════════════════════════════════════════════════════

/-! The Glue logic tells us *how* to compose meanings but not *what*
    the meanings are. The meaning terms are ordinary Montague-style
    denotations. We connect Glue proofs to truth conditions by
    evaluating them over the same `toyModel` used by
    `QuantifierComposition.lean`.

    The toy model has no `love` predicate, so we use `sees_sem` as
    the transitive relation. The logical structure is identical.

    Surface scope: every(person, λx. some(person, λy. sees(y)(x)))
    Inverse scope: some(person, λy. every(person, λx. sees(y)(x)))
-/

open ToyLexicon

def glue_surface_meaning : Bool :=
  every_sem toyModel person_sem
    (λ x => some_sem toyModel person_sem (λ y => sees_sem y x))

def glue_inverse_meaning : Bool :=
  some_sem toyModel person_sem
    (λ y => every_sem toyModel person_sem (λ x => sees_sem y x))

/-- The two Glue readings differ (genuine ambiguity). -/
theorem glue_readings_differ :
    glue_surface_meaning ≠ glue_inverse_meaning := by native_decide

/-- Surface scope is true in the toy model
    (each person sees some person). -/
theorem glue_surface_true : glue_surface_meaning = true := by
  native_decide

/-- Inverse scope is false in the toy model
    (no single person is seen by everyone). -/
theorem glue_inverse_false : glue_inverse_meaning = false := by
  native_decide

-- ════════════════════════════════════════════════════════════════════
-- § Bridge: Glue ↔ QR Scope Readings
-- ════════════════════════════════════════════════════════════════════

/-! Both Glue and QR are extensionally equivalent on the canonical
    scope example: both yield exactly {∀>∃, ∃>∀} with the same
    truth values. The QR side is computed via `interp` from
    `Composition/Tree.lean`, connecting Glue to the H&K composition
    engine. -/

open Semantics.Scope
open Core.Tree
open Semantics.Composition.Tree
open Semantics.Montague.Variables

/-- Lexicon for the QR bridge (matching QuantifierComposition). -/
private def bridgeLex : Lexicon toyModel := λ word =>
  match word with
  | "every" => some ⟨Ty.det, every_sem toyModel⟩
  | "some" => some ⟨Ty.det, some_sem toyModel⟩
  | "person" => some ⟨.e ⇒ .t, person_sem⟩
  | "sees" => some ⟨.e ⇒ .e ⇒ .t, ToyLexicon.sees_sem⟩
  | _ => none

private def g₀ : Assignment toyModel := λ _ => .john

/-- Surface scope QR tree (∀>∃):
    `[S [DP every person] [1 [S [DP some person] [2 [S t₁ [VP sees t₂]]]]]]` -/
private def qr_surface : Tree Unit String :=
  .bin
    (.bin (.leaf "every") (.leaf "person"))
    (.binder 1
      (.bin
        (.bin (.leaf "some") (.leaf "person"))
        (.binder 2
          (.bin (.tr 1) (.bin (.leaf "sees") (.tr 2))))))

/-- Inverse scope QR tree (∃>∀):
    `[S [DP some person] [2 [S [DP every person] [1 [S t₁ [VP sees t₂]]]]]]` -/
private def qr_inverse : Tree Unit String :=
  .bin
    (.bin (.leaf "some") (.leaf "person"))
    (.binder 2
      (.bin
        (.bin (.leaf "every") (.leaf "person"))
        (.binder 1
          (.bin (.tr 1) (.bin (.leaf "sees") (.tr 2))))))

/-- Map ScopeConfig to truth values via Glue evaluation. -/
def glueReading : ScopeConfig → Bool
  | .surface => glue_surface_meaning
  | .inverse => glue_inverse_meaning

/-- Map ScopeConfig to truth values via QR tree interpretation
    (@cite{heim-kratzer-1998} Ch. 5). -/
def qrReading : ScopeConfig → Option Bool
  | .surface => evalTree bridgeLex g₀ qr_surface
  | .inverse => evalTree bridgeLex g₀ qr_inverse

/-- QR surface scope tree produces the same truth value as Glue. -/
theorem qr_surface_agrees :
    qrReading .surface = some glue_surface_meaning := by native_decide

/-- QR inverse scope tree produces the same truth value as Glue. -/
theorem qr_inverse_agrees :
    qrReading .inverse = some glue_inverse_meaning := by native_decide

/-- Glue and QR yield identical truth values for both scope readings.

    Two fundamentally different composition mechanisms — proof search
    in linear logic (Glue, @cite{asudeh-2022}) vs. covert movement
    with Predicate Abstraction (QR, @cite{heim-kratzer-1998}) — produce
    the same semantic results. -/
theorem glue_qr_agree :
    ∀ s : ScopeConfig, qrReading s = some (glueReading s) := by
  intro s; cases s
  · exact qr_surface_agrees
  · exact qr_inverse_agrees

-- ════════════════════════════════════════════════════════════════════
-- § Resource Sensitivity as a Unifying Principle
-- ════════════════════════════════════════════════════════════════════

/-! @cite{asudeh-2022} (§3) argues that linear logic resource
    sensitivity subsumes several well-formedness conditions from
    different frameworks. These are all instances of: in a valid
    linear logic proof, each premise is used exactly once. -/

inductive ResourceCondition where
  | completenessCoherence   -- @cite{kaplan-bresnan-1982}: all and only GFs
  | thetaCriterion          -- @cite{chomsky-1981}: each arg ↔ one θ-role
  | projectionPrinciple     -- @cite{chomsky-1981}: lexical requirements projected
  | noVacuousQuantification -- every binder binds something
  | fullInterpretation      -- @cite{chomsky-1982}: every LF element licensed
  | inclusivenessCondition  -- @cite{chomsky-1995}: no new objects in derivation
  deriving DecidableEq, Repr

/-- Resource sensitivity = no weakening + no contraction.
    No weakening means every premise must be consumed (captures
    fullInterpretation, inclusivenessCondition).
    No contraction means each premise consumed at most once (captures
    thetaCriterion, noVacuousQuantification). Together they enforce
    completenessCoherence and projectionPrinciple. -/
def ResourceCondition.fromNoWeakening : List ResourceCondition :=
  [.fullInterpretation, .inclusivenessCondition, .completenessCoherence]

def ResourceCondition.fromNoContraction : List ResourceCondition :=
  [.thetaCriterion, .noVacuousQuantification, .projectionPrinciple]

-- ════════════════════════════════════════════════════════════════════
-- § Three Kinds of Composition Theory
-- ════════════════════════════════════════════════════════════════════

/-! @cite{asudeh-2022} (§4) distinguishes three approaches to the
    syntax-semantics interface:

    1. **Interpretive** (H&K/QR): Syntax produces LF, which is
       directly interpreted. Scope ambiguity requires a syntactic
       operation (QR/covert movement) — two distinct LF trees.
    2. **Parallel** (CG/CCG): Syntax and semantics computed in
       lockstep. Scope ambiguity requires type-shifting operations
       and corresponding categorial modifications.
    3. **Glue** (separable logic): Syntax produces meaning
       constructors; composition is proof search. Scope ambiguity
       arises from multiple ∀-instantiations — no syntactic ambiguity
       or type-shifting needed.

    linglib formalizes all three: H&K in `Composition/Tree.lean`,
    CCG in `CCG/Interface.lean`, Glue here. -/

inductive CompositionApproach where
  | interpretive   -- H&K: syntax → LF → interpretation
  | parallel       -- CG/CCG: syntax ∥ semantics
  | glueSeparable  -- Glue: syntax → premises → proof search
  deriving DecidableEq, Repr

/-- How each approach handles scope ambiguity. -/
inductive ScopeAmbiguityMechanism where
  | covertMovement   -- QR: syntactic operation producing distinct LFs
  | typeShifting      -- CG/CCG: type-raising / scope-shifting
  | proofSearch       -- Glue: multiple ∀-instantiations → multiple proofs
  deriving DecidableEq, Repr

def CompositionApproach.scopeMechanism : CompositionApproach → ScopeAmbiguityMechanism
  | .interpretive => .covertMovement
  | .parallel => .typeShifting
  | .glueSeparable => .proofSearch

/-- Glue is the only approach that derives scope ambiguity from
    proof search rather than syntactic or type-theoretic operations. -/
theorem glue_scope_via_proof_search :
    CompositionApproach.glueSeparable.scopeMechanism = .proofSearch := rfl

/-- In Glue, the structural syntax need not be ambiguous to derive
    scope ambiguity — the ambiguity is in the proof space. -/
def requiresSyntacticOperation : CompositionApproach → Bool
  | .interpretive => true    -- QR = covert movement
  | .parallel => false       -- type-shifting is semantic, not syntactic
  | .glueSeparable => false  -- proof search is semantic, not syntactic

theorem glue_no_syntactic_operation :
    requiresSyntacticOperation .glueSeparable = false := rfl

theorem interpretive_requires_syntactic_operation :
    requiresSyntacticOperation .interpretive = true := rfl

end Semantics.Composition.Glue
