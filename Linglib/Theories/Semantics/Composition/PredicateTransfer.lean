import Linglib.Theories.Semantics.Lexical.CovertQuantifier

/-!
# Predicate Transfer, SHIFT, and Habitual Type-Shifting

@cite{cohen-2013} @cite{nunberg-1995}

Two reinterpretation mechanisms that introduce covert quantifiers into
logical form, with different consequences for scope:

1. **Predicate Transfer** (T_g, @cite{nunberg-1995}): pragmatically triggered
   when direct kind predication is anomalous. Can apply at any level of
   semantic composition → produces scope ambiguities, except in opaque
   contexts (which block transfer because it requires the intension of
   the property, not just its extension).

2. **Habitual type-shift** (γ, @cite{cohen-2013}): semantically triggered
   by type mismatch between eventive predicates (which require intervals)
   and present tense (which provides a moment). Applies locally at the
   mismatch site → narrow scope only.

The key insight: while both produce the same quantifier (GEN), the
*mechanism* that introduces it determines its scope behavior.

## Why type-shifts are local (§13.3.1)

@cite{cohen-2013} inherits the Partee-Rooth SHIFT operator to argue that
type-shifting cannot commute with negation: ¬SHIFT(V) ≠ SHIFT(¬V). This
non-commutativity proves that the shift must apply *before* other operators
— i.e., locally. The same reasoning applies to γ.

See `Phenomena/Generics/Studies/Cohen2013.lean` for the empirical
predictions and verification.
-/

namespace Semantics.Composition.PredicateTransfer

-- ============================================================================
-- Predicate Transfer (Nunberg 1995)
-- ============================================================================

/-- Predicate Transfer for generics: T_g transforms a kind-level predicate
    into a quantified predicate over instances of the kind.

    T_g(P) = λx. gen_y[C(y,x)][P(y)]

    where C(y,x) means y is an instance of kind x.  Following
    @cite{chierchia-1998}, kinds are the denotations of bare plurals
    via the ∩ (down) operator: ∩storks, ∩pandas, etc.

    - `gen`: the generic quantifier (restrictor → scope → Bool)
    - `instanceOf y x`: y is an instance of kind x (Chierchia's ∪ applied
      to x would give the set of instances; C is its characteristic function)
    - `P`: the predicate to transfer (e.g., "eat bamboo shoots")

    When the initial logical form P(∩pandas) is pragmatically anomalous
    (kinds don't eat bamboo — individuals do), Predicate Transfer applies,
    yielding gen_y[C(y, ∩pandas)][P(y)]. -/
def transferGen {Kind Ind : Type}
    (gen : (Ind → Bool) → (Ind → Bool) → Bool)
    (instanceOf : Ind → Kind → Bool)
    (P : Ind → Bool) : Kind → Bool :=
  fun x => gen (fun y => instanceOf y x) P

-- ============================================================================
-- Partee-Rooth SHIFT (§13.3.1)
-- ============================================================================

/-- Partee-Rooth SHIFT: lift an extensional transitive verb to take
    a generalized quantifier as its object argument.

    SHIFT(V) = λQ.λx.Q(λy.V(x,y))

    @cite{partee-rooth-1983} propose this to resolve the type mismatch
    when extensional verbs (type e → e → t) are conjoined with intensional
    verbs (type (et → t) → e → t): "John needed and bought a new coat."

    @cite{cohen-2013} uses SHIFT to argue that type-shifting must be LOCAL:
    since ¬SHIFT(V) ≠ SHIFT(¬V), the shift must apply before negation.
    See `shift_neg_noncommutative`. -/
def SHIFT {E : Type} (V : E → E → Bool) : ((E → Bool) → Bool) → E → Bool :=
  fun Q x => Q (fun y => V x y)

/-- SHIFT does not commute with negation.

    - ¬SHIFT(V)(Q)(x) = ¬Q(λy.V(x,y))
    - SHIFT(¬V)(Q)(x) = Q(λy.¬V(x,y))

    For Q = ∃: ¬∃y.V(x,y) vs ∃y.¬V(x,y) — these are ∀y.¬V vs ∃y.¬V.

    This is the reason type-shifting is LOCAL (@cite{cohen-2013} §13.3.1):
    the shift must apply to the verb BEFORE negation. If shifting were
    global (post-negation), we would get the SHIFT(¬V) reading, which is
    empirically unavailable for "John needed but didn't buy a new coat."
    This argument carries over to γ: since γ is a type-shift, it too
    must apply locally. -/
theorem shift_neg_noncommutative :
    ∃ (V : Bool → Bool → Bool) (Q : (Bool → Bool) → Bool) (x : Bool),
    !(SHIFT V Q x) ≠ SHIFT (fun a b => !(V a b)) Q x :=
  -- V = projection on object: V(x,y) = y
  -- Q = existential: Q(P) = P(true) ∨ P(false)
  -- x = true
  -- LHS: !(Q(λy.y)) = !(true ∨ false) = false
  -- RHS: Q(λy.¬y) = (false ∨ true) = true
  ⟨fun _ y => y, fun P => P true || P false, true, by native_decide⟩

-- ============================================================================
-- Habitual Type-Shift (γ)
-- ============================================================================

/-- γ: type-shifting operator that turns an eventive predicate
    (property of intervals) into a stative one (property of moments).

    γP = λt. gen_e[e ≤ int(t)][P(e)]

    - `gen`: the generic quantifier
    - `containedIn e t`: interval e is contained in int(t), the
      relevant interval surrounding moment t
    - `P`: eventive predicate (e.g., λe. smoke(mary, e))

    Triggered by type mismatch: an eventive verb requires an interval
    argument, but present tense provides a moment. The mismatch forces
    γ to apply at the verb level — locally, before composition with
    the object. This locality is why habituals take narrow scope.

    Like SHIFT, γ does not commute with other operators (see
    `shift_neg_noncommutative`): γ(λe.∃x(P(x,e))) ≠ ∃x(γ(λe.P(x,e))),
    so the scope of the existential relative to gen depends on where
    γ fires. Since it fires locally (at the type mismatch), the
    existential always scopes over gen. -/
def gamma {Interval Moment : Type}
    (gen : (Interval → Bool) → (Interval → Bool) → Bool)
    (containedIn : Interval → Moment → Bool)
    (P : Interval → Bool) : Moment → Bool :=
  fun t => gen (fun e => containedIn e t) P

-- ============================================================================
-- Quantifier Source
-- ============================================================================

/-- The mechanism by which a covert quantifier is introduced into logical form.
    Determines scope behavior (@cite{cohen-2013} §13.4). -/
inductive QuantifierSource where
  /-- Pragmatic; can apply at any level of semantic composition -/
  | predicateTransfer
  /-- Semantic; applies locally at the type-mismatch site -/
  | typeShift
  /-- Phonologically realized (always, usually, often, etc.) -/
  | overt
  deriving DecidableEq, BEq, Repr

/-- Type-shifted elements take narrow scope only (local application).
    Predicate Transfer and overt quantifiers can take wide scope
    (application at any composition level). -/
def QuantifierSource.canTakeWideScope : QuantifierSource → Bool
  | .predicateTransfer => true
  | .typeShift => false
  | .overt => true

/-- Predicate Transfer cannot scope out of opaque (intensional) contexts.
    It requires the intension of the property, which is not available
    outside the scope of an attitude verb.

    Overt quantifiers can scope out of opaque contexts (de re readings).
    Type-shifted elements cannot either (they're already local). -/
def QuantifierSource.canScopeOutOfOpaque : QuantifierSource → Bool
  | .predicateTransfer => false
  | .typeShift => false
  | .overt => true

/-- Strict scope-freedom ordering: overt > predicateTransfer > typeShift. -/
theorem scope_freedom_ordering :
    (QuantifierSource.overt.canTakeWideScope = true ∧
     QuantifierSource.overt.canScopeOutOfOpaque = true) ∧
    (QuantifierSource.predicateTransfer.canTakeWideScope = true ∧
     QuantifierSource.predicateTransfer.canScopeOutOfOpaque = false) ∧
    (QuantifierSource.typeShift.canTakeWideScope = false ∧
     QuantifierSource.typeShift.canScopeOutOfOpaque = false) :=
  ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

end Semantics.Composition.PredicateTransfer
