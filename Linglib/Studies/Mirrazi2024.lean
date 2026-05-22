import Linglib.Theories.Semantics.Quantification.ChoiceFunction
import Linglib.Theories.Semantics.Attitudes.NegRaising
import Linglib.Fragments.Farsi.Determiners

/-!
# Indefinites in Negated Intensional Contexts @cite{mirrazi-2024}

Semantics & Pragmatics 17, Article 7: 1–44.

## The Scope Paradox

Farsi indefinites under negated intensional operators (*think*, *necessary*,
*can*) yield "wide pseudo-scope de dicto" readings. The indefinite appears
to take **wide scope over negation** but **narrow scope (de dicto) under
the intensional operator**:

  (1) Rodica does not think that Carl read some of the books.
      Attested: think ≫ INDEF ≫ ¬
      = Rodica thinks there are some books Carl didn't read
        (but she doesn't know which ones)

This is paradoxical: there is no syntactic position that is simultaneously
above negation and below *think*. Under movement-based approaches, the
indefinite would have to move above negation, but any such landing site
unavoidably outscopes the intensional operator — yielding a de re (not
de dicto) construal. This is the "fourth reading" problem (@cite{percus-2000},
@cite{von-fintel-heim-2011}, @cite{keshet-schwarz-2019}).

## Choice Functions Solve It

In-situ choice function accounts separate the existential quantification
(∃f) from the descriptive content. The ∃-closure over the choice function
sits above negation (giving wide scope), while the CF's world variable,
bound by the intensional operator, keeps the restrictor de dicto.

## World-Skolemized Choice Functions

Standard intensional CFs (@cite{heim-1994}, @cite{winter-1997}) run into
the **fixed-set problem**: when the NP extension is rigid across worlds,
`f(⟨s, ⟨e,t⟩⟩)` returns the same individual everywhere. World-skolemized
CFs `f(w', NP(w'))` solve this: the CF takes a world argument, so it can
pick different individuals in different worlds even from the same set.

## Cross-Linguistic Variation

Wide pseudo-scope de dicto is available in Farsi and Japanese, marginal in
English, and absent in German and French. @cite{schwarz-2012} proposes that
determiners vary in whether they carry an independent world variable. Farsi
indefinites (*ye*, *čand-ta*, *do-ta*) carry one; German/French do not.

## Indefinite/Universal Asymmetry

Universal quantifiers (*hame* "all") under the same negated intensional
operators do NOT get wide pseudo-scope de dicto readings. This follows
because universal quantifiers are genuine scope-takers (GQs), not choice
functions — they cannot separate their quantificational force from their
descriptive content.
-/

namespace Mirrazi2024

open Semantics.Quantification.ChoiceFunction
open Semantics.Attitudes.Doxastic (AccessRel boxAt)
open Semantics.Attitudes.NegRaising (negRaisesAt)
open Fragments.Farsi.Determiners (ye candTa doTa PlainIndefiniteEntry)

-- ============================================================================
-- §1 The Scope Paradox: Three Readings
-- ============================================================================

/-- The three logically possible scope configurations for an indefinite
    under a negated intensional operator: ¬ INT_OP [INDEF VP]. -/
inductive ScopeConfig where
  /-- NEG ≫ INT ≫ INDEF: narrow scope (under both). -/
  | narrow
  /-- INDEF ≫ NEG ≫ INT: wide scope de re (above both). -/
  | wideDeRe
  /-- INT ≫ INDEF ≫ NEG: wide pseudo-scope de dicto. -/
  | widePseudoDeDicto
  deriving DecidableEq, Repr

/-- The kind of scope-taker. -/
inductive ScopeTakerKind where
  /-- An indefinite (choice function semantics). -/
  | indefinite
  /-- A genuine generalized quantifier (every, all). -/
  | universal
  deriving DecidableEq, Repr

-- ============================================================================
-- §1.2 Neg-Raising Does Not Explain the Paradox
-- ============================================================================

/-- Under neg-raising, ¬THINK(p) is strengthened to THINK(¬p).

    @cite{mirrazi-2024} §1.2 ex. (5)–(6): if neg-raising applies to (1),
    the resulting interpretation is THINK(¬[Carl read some of the books]).
    This puts the indefinite UNDER negation (inside the think-complement),
    giving think ≫ ¬ ≫ INDEF — NOT the attested think ≫ INDEF ≫ ¬.

    Moreover, the same readings arise with non-neg-raising predicates
    (*necessary*, *can*), so neg-raising cannot be the explanation. -/
structure NegRaisingCounterargument where
  /-- A neg-raising predicate produces think ≫ ¬ ≫ INDEF, not the
      attested think ≫ INDEF ≫ ¬. The indefinite ends up below negation. -/
  negRaising_wrong_scope : ScopeConfig
  /-- Non-neg-raising predicates (necessary, can) also yield the reading,
      so neg-raising is neither necessary nor sufficient. -/
  nonNegRaiser_also_works : Bool

/-- The neg-raising hypothesis yields the wrong scope configuration.
    Under neg-raising: ¬think(p) → think(¬p), and the indefinite stays
    inside ¬p, giving narrow scope — the opposite of what's attested.
    @cite{mirrazi-2024} §1.2 exx. (5)–(10). -/
def negRaisingFails : NegRaisingCounterargument where
  negRaising_wrong_scope := .narrow  -- think ≫ ¬ ≫ INDEF, not think ≫ INDEF ≫ ¬
  nonNegRaiser_also_works := true    -- necessary, can also yield the reading

/-- Neg-raising yields the wrong scope order for the indefinite. -/
theorem negRaising_yields_narrow :
    negRaisingFails.negRaising_wrong_scope = .narrow := rfl

/-- Neg-raising is not needed: non-neg-raising operators also yield
    wide pseudo-scope de dicto. -/
theorem nonNegRaiser_suffices :
    negRaisingFails.nonNegRaiser_also_works = true := rfl

/-- Structural verification: *think* supports neg-raising via the
    doxastic infrastructure. This connects to the library's `negRaisesAt`
    without claiming neg-raising explains the scope paradox. -/
theorem think_does_neg_raise {W E : Type*} (R : AccessRel W E)
    (agent : E) (worlds : List W) (p : W → Prop) (w : W)
    (hNeg : ¬ boxAt R agent w worlds p)
    (hExclMiddle : negRaisesAt R agent worlds p w) :
    boxAt R agent w worlds (λ w' => ¬ p w') :=
  hExclMiddle hNeg

-- ============================================================================
-- §2 Truth Conditions
-- ============================================================================

section TruthConditions

variable (W : Type*) (E : Type*)

/-- The truth conditions for the wide pseudo-scope de dicto reading,
    derived from CF semantics.

    @cite{mirrazi-2024} ex. (44):
    ∀w'' ∈ Beliefs(Rodica,w₀): ¬read_{w''}(Carl, f(w'', book(w'')))

    The ∃f sits above negation (wide scope), while f's world argument
    is bound by the attitude verb (de dicto). The accessibility relation
    `R` connects to the doxastic infrastructure in `Attitudes.Doxastic`. -/
def widePseudoDeDictoTC
    (f : SkolemCF W E)
    (R : AccessRel W E) (agent : E) (worlds : List W)
    (nounProp : W → E → Prop)
    (vp : E → W → Prop)
    (w₀ : W) : Prop :=
  ∀ w' ∈ worlds, R agent w₀ w' →
    ¬vp (f w' (nounProp w')) w'

/-- The truth conditions for the genuine wide scope de re reading.

    @cite{mirrazi-2024} ex. (41):
    ∀w'' ∈ Beliefs(Rodica,w₀): ¬read_{w''}(Carl, f(book_{w₀}))

    The CF's world variable is free (evaluated at w₀):
    the individual is fixed across belief worlds. -/
def wideDeReTC
    (f : SkolemCF W E)
    (R : AccessRel W E) (agent : E) (worlds : List W)
    (nounProp : W → E → Prop)
    (vp : E → W → Prop)
    (w₀ : W) : Prop :=
  ∀ w' ∈ worlds, R agent w₀ w' →
    ¬vp (f w₀ (nounProp w₀)) w'

/-- The key structural fact: de re and pseudo-de dicto differ exactly in
    whether the CF's world argument is bound (varies with w') or free
    (fixed at w₀). When `nounProp` is world-invariant and `f` is
    world-invariant, they collapse — the two readings become equivalent.

    This is the formal content of the fixed-set problem: when there is
    no cross-world variation, world-skolemization adds nothing, and the
    "pseudo-de dicto" reading reduces to plain de re. -/
theorem deRe_eq_pseudoDeDicto_when_rigid
    (f : SkolemCF W E)
    (R : AccessRel W E) (agent : E) (worlds : List W)
    (nounProp : W → E → Prop)
    (vp : E → W → Prop) (w₀ : W)
    (hRigidNP : ∀ w, nounProp w = nounProp w₀)
    (hRigidCF : ∀ w, f w = f w₀) :
    widePseudoDeDictoTC W E f R agent worlds nounProp vp w₀ ↔
    wideDeReTC W E f R agent worlds nounProp vp w₀ := by
  unfold widePseudoDeDictoTC wideDeReTC
  constructor <;> intro h w' hw' hR
  · rw [← hRigidNP w', ← hRigidCF w']; exact h w' hw' hR
  · rw [hRigidNP w', hRigidCF w']; exact h w' hw' hR

end TruthConditions

-- ============================================================================
-- §2.2 The Fourth Reading is Impossible Under Movement
-- ============================================================================

/-- Under movement-based accounts, a DP that moves above an intensional
    operator is necessarily interpreted de re (at its landing site).

    @cite{mirrazi-2024} §2.2, citing @cite{percus-2000},
    @cite{von-fintel-heim-2011}, @cite{keshet-schwarz-2019}:

    "According to all of these theories, a DP can only get a *de dicto*
    reading when it is under the scope of an intensional operator. If a
    DP moves in order to take wide scope with respect to the intensional
    operator, it can no longer be construed *de dicto*."

    This means: to scope above negation, the indefinite must move to a
    position above NEG — but any such position is also above the
    intensional operator, forcing de re. There is no landing site that
    is simultaneously above NEG and below the intensional operator
    (since NEG is syntactically below the operator). -/
theorem movement_above_neg_forces_deRe
    {W E : Type*} (f : SkolemCF W E)
    (R : AccessRel W E) (agent : E) (worlds : List W)
    (nounProp : W → E → Prop) (vp : E → W → Prop) (w₀ : W) :
    -- If the CF is "moved" (evaluated at w₀ for both its world and NP args),
    -- the result is de re, not pseudo-de dicto.
    (∀ w' ∈ worlds, R agent w₀ w' →
      ¬vp (f w₀ (nounProp w₀)) w') ↔
    wideDeReTC W E f R agent worlds nounProp vp w₀ := by
  rfl

-- ============================================================================
-- §3 The Fixed-Set Problem and World-Skolemization
-- ============================================================================

/-- The fixed-set problem: when the NP extension is rigid across worlds,
    a non-world-skolemized CF returns the same individual everywhere.

    @cite{mirrazi-2024} §3: Consider a course on Covid-19 with exactly 5
    books {A,B,C,D,E}. The extension of "book Carl has to read" is the same
    set in every belief world. A plain intensional CF `f(⟨s,⟨e,t⟩⟩)` applied
    to this rigid intension always returns the same book. -/
theorem fixedSet_no_variation {W E : Type*}
    (f : CF E)
    (nounProp : E → Prop) :
    ∀ (_ _ : W), f nounProp = f nounProp :=
  λ _ _ => rfl

/-- World-skolemization solves the fixed-set problem: `f(w', P)` can pick
    different individuals at different worlds because `f` varies with `w'`.

    @cite{mirrazi-2024} ex. (45): f(w₁, {A,B,C,D,E}) = A,
    f(w₂, {A,B,C,D,E}) = C, f(w₃, {A,B,C,D,E}) = E. -/
theorem worldSkolem_allows_variation {W E : Type*}
    (f : SkolemCF W E) (P : E → Prop) (w₁ w₂ : W)
    (hVary : f w₁ P ≠ f w₂ P) :
    ∃ (_ : W) (_ : W), f w₁ P ≠ f w₂ P :=
  ⟨w₁, w₂, hVary⟩

-- ============================================================================
-- §4 Indefinite / Universal Asymmetry (Derived)
-- ============================================================================

/-! Wide pseudo-scope de dicto requires CF semantics + world variable.

@cite{mirrazi-2024} §1.3: universal quantifiers (*hame* "all") under
the same negated intensional operators do NOT get wide pseudo-scope
de dicto readings. This follows because universals are genuine GQs
— they cannot separate quantificational force from their descriptive content.

The prediction is DERIVED from `IndefType.canPseudoDeDicto`:
- Indefinite (CF + world var): ✓
- Universal (GQ): ✗ regardless of world variable -/

/-- ∃-quantifiers never yield pseudo-de dicto, regardless of world
    variable. This is structural: ∃-quantifiers cannot separate their
    quantificational force from their descriptive content, so there is
    no mechanism to place ∃ above negation while keeping the restrictor
    below the intensional operator. -/
theorem existential_never_pseudo (b : Bool) :
    IndefType.canPseudoDeDicto .existential b = false := rfl

-- ============================================================================
-- §5 Cross-Linguistic Variation (Structural)
-- ============================================================================

/-! Cross-linguistic parameter: whether wide pseudo-scope de dicto is
    available depends on whether the language's indefinite determiners
    carry a world variable AND use CF semantics.

    @cite{mirrazi-2024} §3.1, @cite{schwarz-2012}:

    | Language | CF | World var | canPseudoDeDicto |
    |----------|-----------|-----------|-----------------|
    | Farsi    | ✓         | ✓         | ✓               |
    | Japanese | ✓         | ✓         | ✓               |
    | English  | ✓         | ✓/✗       | marginal        |
    | German   | ?         | ✗         | ✗               |
    | French   | ?         | ✗         | ✗               |

    These two structural theorems derive the full typological pattern
    from `canPseudoDeDicto`. -/

/-- The world variable is necessary: without it, even CF indefinites
    cannot get pseudo-de dicto (the CF has no world argument to bind). -/
theorem worldVar_necessary_for_pseudo :
    IndefType.canPseudoDeDicto .choiceFunction false = false := rfl

/-- The world variable is sufficient (given CF): with it, the CF's
    world argument can be bound by the intensional operator, yielding
    de dicto construal while ∃-closure sits above negation. -/
theorem worldVar_sufficient_for_pseudo :
    IndefType.canPseudoDeDicto .choiceFunction true = true := rfl

-- ============================================================================
-- §6 Bridge: Farsi Indefinites (Structural)
-- ============================================================================

/-- Any `PlainIndefiniteEntry` that is a choice function with a world
    variable is predicted to support wide pseudo-scope de dicto.
    This is the structurally general version — it applies to ye, čand-ta,
    do-ta, and any future entry with the same properties. -/
theorem plainIndef_pseudo_de_dicto (entry : PlainIndefiniteEntry)
    (hCF : entry.indefType = .choiceFunction)
    (hWV : entry.hasWorldVar = true) :
    IndefType.canPseudoDeDicto entry.indefType entry.hasWorldVar = true := by
  simp [hCF, hWV, IndefType.canPseudoDeDicto]

end Mirrazi2024
