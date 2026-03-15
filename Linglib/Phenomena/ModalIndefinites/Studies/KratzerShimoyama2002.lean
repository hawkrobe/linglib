import Linglib.Theories.Semantics.Composition.SetMonad
import Linglib.Theories.Semantics.Exhaustification.FreeChoice
import Linglib.Fragments.Japanese.Determiners
import Linglib.Fragments.German.ModalIndefinites
import Linglib.Fragments.Latvian.IndeterminatePronouns

/-!
# Kratzer & Shimoyama (2002): Indeterminate Pronouns
@cite{kratzer-shimoyama-2002}

"Indeterminate Pronouns: The View from Japanese." In C. Lee et al. (eds.),
*Contrastiveness in Information Structure, Alternatives and Scalar
Implicatures*, Studies in Natural Language and Linguistic Theory 91, 123-143.

## Core Thesis

Hamblin alternative semantics, originally designed for questions, is the
right architecture for **all quantification**. Indeterminate pronouns
(Japanese *dare*, *nani*, *doko*...) denote sets of individual alternatives
that expand pointwise via functional application until caught by an
operator (∃, ∀, Neg, Q). Quantification is operator selection, not DP
movement.

## Formalized Contributions

1. **Hamblin operators** (§2): The four sentential operators over
   propositional alternative sets.
2. **Pointwise FA = Set applicative** (§3): K&S's Hamblin FA is exactly
   the set applicative from @cite{charlow-2020}, already formalized in
   `Applicative.lean`.
3. **GQ as special case** (§2): Determiner quantification falls out
   when alternatives are individuals — `[∃]({P(x) : x ∈ A}) ↔ ∃x∈A, P(x)`.
4. **Singleton collapse**: When alternatives are a singleton (ordinary
   semantics), Hamblin modals reduce to standard Kripke modals.
5. **Modal–indefinite interaction** (§7): Possibility/necessity modals
   are sensitive to Hamblin alternatives in their scope.
6. **Distribution requirement as implicature** (§6, §8): The free choice
   effect is derived via Gricean reasoning, not semantic entailment.
7. **End-to-end FC derivation**: Hamblin T-content + implicature = FC.
8. **Selectivity** (§9): Non-selective (Japanese) vs. selective
   (Indo-European) indeterminate systems, with Beck effect data.
9. **Cross-linguistic paradigm** (§1): Latvian indeterminate series.

## Integration Points

- §3 Hamblin FA bridges to `setAp` (`Composition/Applicative.lean`)
- Singleton collapse bridges Hamblin modals to Kripke semantics
- §8 free choice bridges to `free_choice_forward`
  (`Exhaustification/FreeChoice.lean`)
- Fragment data bridges to `Japanese/Determiners.lean`,
  `German/ModalIndefinites.lean`, and `Latvian/IndeterminatePronouns.lean`
-/

set_option autoImplicit false

namespace Phenomena.ModalIndefinites.Studies.KratzerShimoyama2002

open Semantics.Composition.SetMonad (eta)
open Semantics.Composition.Applicative (setAp)

-- ════════════════════════════════════════════════════════════════
-- Part I: Hamblin Alternative Semantics Generalized (§2-3)
-- ════════════════════════════════════════════════════════════════

/-!
## §2-3: Hamblin Interpretation System

In a Hamblin semantics, **all expressions denote sets of alternatives**.
Most lexical items denote singleton sets; indeterminate pronouns denote
sets of individuals. Composition is pointwise functional application.
-/

/-- A Hamblin denotation is a set of alternatives of type α.
    This is exactly the carrier of @cite{charlow-2020}'s set monad. -/
abbrev HamblinDen (α : Type) := α → Prop

/-- Hamblin Functional Application (§3): pointwise application of a set
    of functions to a set of arguments.

    `⟦α⟧ = {a ∈ Dσ : ∃b ∈ ⟦β⟧ ∃c ∈ ⟦γ⟧, a = c(b)}` -/
def hamblinFA {A B : Type} (funSet : HamblinDen (A → B)) (argSet : HamblinDen A) : HamblinDen B :=
  fun b => ∃ f, funSet f ∧ ∃ x, argSet x ∧ f x = b

/-- **Bridge**: Hamblin FA = the set applicative from `Applicative.lean`. -/
theorem hamblinFA_eq_setAp {A B : Type} (m : HamblinDen (A → B)) (n : HamblinDen A) :
    hamblinFA m n = setAp m n := rfl


-- ════════════════════════════════════════════════════════════════
-- §2: The Four Sentential Operators
-- ════════════════════════════════════════════════════════════════

/-!
## §2: Sentential Operators over Propositional Alternatives

The alternatives created by indeterminate phrases expand until caught
by an operator. Where A is a set of propositions (p. 126-127):

- `[∃](A)` — true iff some proposition in A is true
- `[∀](A)` — true iff every proposition in A is true
- `[Neg](A)` — true iff no proposition in A is true
- `[Q](A)` — A itself (the Hamblin question denotation)
-/

section Operators

variable {W : Type}

/-- `[∃](A)`: existential closure over propositional alternatives. -/
def opExists (A : HamblinDen (W → Prop)) : W → Prop :=
  fun w => ∃ p, A p ∧ p w

/-- `[∀](A)`: universal closure over propositional alternatives. -/
def opForall (A : HamblinDen (W → Prop)) : W → Prop :=
  fun w => ∀ p, A p → p w

/-- `[Neg](A)`: negative closure over propositional alternatives. -/
def opNeg (A : HamblinDen (W → Prop)) : W → Prop :=
  fun w => ∀ p, A p → ¬p w

/-- `[Q](A)`: question operator — identity on propositional alternatives. -/
def opQ (A : HamblinDen (W → Prop)) : HamblinDen (W → Prop) := A

/-- Neg is the pointwise negation of ∃: `[Neg](A)(w) ↔ ¬[∃](A)(w)`. -/
theorem opNeg_iff_not_opExists (A : HamblinDen (W → Prop)) (w : W) :
    opNeg A w ↔ ¬opExists A w := by
  constructor
  · intro hneg ⟨p, hA, hp⟩; exact hneg p hA hp
  · intro hne p hA hp; exact hne ⟨p, hA, hp⟩

/-- ∀ entails ∃ on non-empty alternative sets. -/
theorem opForall_entails_opExists (A : HamblinDen (W → Prop))
    (hne : ∃ p, A p) (w : W) (h : opForall A w) : opExists A w := by
  obtain ⟨p, hp⟩ := hne
  exact ⟨p, hp, h p hp⟩

/-- Map from operator tags to their semantic implementations. -/
inductive QuantOperator where
  | exists_   -- [∃]: existential closure
  | forall_   -- [∀]: universal closure
  | neg       -- [Neg]: negative closure
  | question  -- [Q]: question formation
  deriving DecidableEq, BEq, Repr

/-- Semantic interpretation of a propositional quantificational operator.
    Returns `none` for `.question`, which produces an alternative set rather
    than a proposition. -/
def QuantOperator.applyProp (op : QuantOperator) (A : HamblinDen (W → Prop)) : Option (W → Prop) :=
  match op with
  | .exists_  => some (opExists A)
  | .forall_  => some (opForall A)
  | .neg      => some (opNeg A)
  | .question => none

/-- The question operator returns the alternative set unchanged:
    `[Q](A) = A`. This is distinct from the propositional operators
    because it does not collapse alternatives to a truth value. -/
theorem question_returns_alternatives (A : HamblinDen (W → Prop)) :
    QuantOperator.applyProp .question A = none ∧ opQ A = A :=
  ⟨rfl, rfl⟩

/-- **Determiner quantification as special case** (p. 126):
    "Determiner quantification falls out as a special case, the case where
    the alternatives are individuals."

    When an indeterminate denotes a set of individuals A and a predicate
    lifts each individual to a proposition, sentential `[∃]` over the
    resulting propositional alternatives equals the standard GQ existential:
    `[∃]({P(x) : x ∈ A})(w) ↔ ∃ x ∈ A, P(x)(w)`. -/
theorem opExists_gq_special_case {E W : Type}
    (A : HamblinDen E) (P : E → W → Prop) (w : W) :
    opExists (fun p => ∃ x, A x ∧ p = P x) w ↔ ∃ x, A x ∧ P x w := by
  constructor
  · rintro ⟨_, ⟨x, hA, rfl⟩, hp⟩; exact ⟨x, hA, hp⟩
  · rintro ⟨x, hA, hp⟩; exact ⟨P x, ⟨x, hA, rfl⟩, hp⟩

/-- Universal counterpart: `[∀]` over individual alternatives = standard ∀.
    `[∀]({P(x) : x ∈ A})(w) ↔ ∀ x ∈ A, P(x)(w)`. -/
theorem opForall_gq_special_case {E W : Type}
    (A : HamblinDen E) (P : E → W → Prop) (w : W) :
    opForall (fun p => ∃ x, A x ∧ p = P x) w ↔ ∀ x, A x → P x w := by
  constructor
  · intro h x hA; exact h (P x) ⟨x, hA, rfl⟩
  · rintro h _ ⟨x, hA, rfl⟩; exact h x hA

end Operators


-- ════════════════════════════════════════════════════════════════
-- Part II: Indeterminate Pronoun Derivations (§2)
-- ════════════════════════════════════════════════════════════════

/-!
## Compositional Derivation of *dare(-ga) nemutta*

Japanese indeterminate pronouns denote sets of individuals. Composed
with a predicate via pointwise FA, they produce propositional alternative
sets. An operator then closes the set (p. 126):

- `⟦dare⟧^{w,g}    = {x: human(x)(w)}`
- `⟦nemutta⟧^{w,g}  = {λxλw'. slept(x)(w')}` (singleton)
- `⟦dare nemutta⟧^{w,g} = {p: ∃x[human(x)(w) & p = λw'. slept(x)(w')]}`

We simplify by working extensionally (dropping the world parameter on
the restrictor), which is faithful for the core point that operator
selection = quantification.
-/

section Derivation

inductive Person where | a | b | c
  deriving DecidableEq, BEq, Repr

/-- `⟦dare⟧` = the set of all humans (extensional simplification). -/
def dare : HamblinDen Person := fun _ => True

/-- `⟦nemutta⟧` = singleton set containing the sleep predicate. -/
def sleptPred (slept : Person → Prop) : HamblinDen (Person → Prop) :=
  eta slept

/-- `⟦dare nemutta⟧` = {slept(a), slept(b), slept(c)} via Hamblin FA. -/
def dareNemutta (slept : Person → Prop) : HamblinDen Prop :=
  hamblinFA (sleptPred slept) dare

/-- dare-ka nemutta = [∃]({slept(a), slept(b), slept(c)}) = ∃x.slept(x) -/
theorem dare_ka_derivation (slept : Person → Prop) :
    (∃ p, dareNemutta slept p ∧ p) ↔ (∃ x : Person, slept x) := by
  constructor
  · rintro ⟨_, ⟨f, rfl, x, _, rfl⟩, hp⟩; exact ⟨x, hp⟩
  · rintro ⟨x, hx⟩; exact ⟨slept x, ⟨slept, rfl, x, trivial, rfl⟩, hx⟩

/-- dare-mo nemutta = [∀]({slept(a), slept(b), slept(c)}) = ∀x.slept(x) -/
theorem dare_mo_derivation (slept : Person → Prop) :
    (∀ p, dareNemutta slept p → p) ↔ (∀ x : Person, slept x) := by
  constructor
  · intro h x; exact h (slept x) ⟨slept, rfl, x, trivial, rfl⟩
  · rintro h _ ⟨f, rfl, x, _, rfl⟩; exact h x

end Derivation


-- ════════════════════════════════════════════════════════════════
-- Part III: Modal–Indefinite Interaction (§7)
-- ════════════════════════════════════════════════════════════════

/-!
## §7: Modals over Hamblin Alternative Sets

The key insight: modals can be sensitive to the propositional alternatives
introduced by indeterminate phrases in their scope (p. 132-133).

Possibility/necessity modals over an alternative set A:

```
⟦kann α⟧(w) = ∃w'[R(w,w') ∧ ∃p[p ∈ A ∧ p(w')]]
⟦muss α⟧(w) = ∀w'[R(w,w') → ∃p[p ∈ A ∧ p(w')]]
```

The **distribution requirement** (to be derived as implicature in §8):

`∀p[p ∈ A → ∃w'[R(w,w') ∧ p(w')]]`

distributes alternatives over accessible worlds.

Note: We use `Prop`-valued accessibility here (rather than the `Bool`-valued
`Core.ModalLogic.AccessRel`) to stay in `Prop` throughout the Hamblin
semantics. The singleton collapse theorem below shows these Hamblin modals
reduce to standard Kripke modals when the alternative set is a singleton.
-/

section ModalInteraction

variable {W : Type}

/-- Prop-valued accessibility relation for Hamblin modal semantics.
    Named distinctly from `Core.ModalLogic.AccessRel` (which is Bool-valued)
    to avoid shadowing. -/
abbrev HamblinAccessRel (W : Type) := W → W → Prop

/-- Possibility modal over Hamblin alternatives (§7, p. 133):
    True at w iff some accessible world satisfies some alternative. -/
def hamblinPoss (R : HamblinAccessRel W) (A : HamblinDen (W → Prop)) (w : W) : Prop :=
  ∃ w', R w w' ∧ ∃ p, A p ∧ p w'

/-- Necessity modal over Hamblin alternatives (§7, p. 133):
    True at w iff every accessible world satisfies some alternative. -/
def hamblinNec (R : HamblinAccessRel W) (A : HamblinDen (W → Prop)) (w : W) : Prop :=
  ∀ w', R w w' → ∃ p, A p ∧ p w'

/-- The distribution requirement (§7, p. 133): for every alternative p in A,
    there exists an accessible world where p is true. -/
def distribReq (R : HamblinAccessRel W) (A : HamblinDen (W → Prop)) (w : W) : Prop :=
  ∀ p, A p → ∃ w', R w w' ∧ p w'

/-- **Singleton collapse**: when the alternative set is a singleton {p},
    Hamblin possibility reduces to standard Kripke possibility.
    This is the paper's core architectural claim: ordinary semantics
    is the special case where all denotations are singletons. -/
theorem hamblinPoss_singleton (R : HamblinAccessRel W) (p : W → Prop) (w : W) :
    hamblinPoss R (eta p) w ↔ ∃ w', R w w' ∧ p w' := by
  constructor
  · rintro ⟨w', hw', q, rfl, hq⟩; exact ⟨w', hw', hq⟩
  · rintro ⟨w', hw', hp⟩; exact ⟨w', hw', p, rfl, hp⟩

/-- **Singleton collapse for necessity**: when alternatives are a singleton,
    Hamblin necessity reduces to standard Kripke necessity. -/
theorem hamblinNec_singleton (R : HamblinAccessRel W) (p : W → Prop) (w : W) :
    hamblinNec R (eta p) w ↔ ∀ w', R w w' → p w' := by
  constructor
  · intro h w' hw'; obtain ⟨_, rfl, hq⟩ := h w' hw'; exact hq
  · intro h w' hw'; exact ⟨p, rfl, h w' hw'⟩

/-- Necessity entails possibility (when some accessible world exists). -/
theorem hamblinNec_entails_hamblinPoss (R : HamblinAccessRel W) (A : HamblinDen (W → Prop))
    (w : W) (h : hamblinNec R A w) (hacc : ∃ w', R w w') : hamblinPoss R A w := by
  obtain ⟨w', hw'⟩ := hacc
  obtain ⟨p, hA, hp⟩ := h w' hw'
  exact ⟨w', hw', p, hA, hp⟩

/-- The distribution requirement is NOT entailed by necessity (§6, p. 131).
    Necessity only requires *some* alternative per world, not that *every*
    alternative is witnessed. The distribution requirement is an implicature.

    Countermodel: R reflexive-only, A = {p₁, p₂} where p₁ holds at true,
    p₂ holds at false. From w = true, only true is accessible: necessity
    holds (p₁ witnesses true) but distribution fails (p₂ is unwitnessed). -/
theorem distrib_not_entailed_by_nec :
    ∃ (R : HamblinAccessRel Bool) (A : HamblinDen (Bool → Prop)) (w : Bool),
      hamblinNec R A w ∧ ¬distribReq R A w := by
  let R : HamblinAccessRel Bool := fun w w' => w = w'
  let p₁ : Bool → Prop := fun w => w = true
  let p₂ : Bool → Prop := fun w => w = false
  let A : HamblinDen (Bool → Prop) := fun p => p = p₁ ∨ p = p₂
  refine ⟨R, A, true, ?_, ?_⟩
  · intro w' hw'
    subst hw'
    exact ⟨p₁, Or.inl rfl, rfl⟩
  · intro hdist
    obtain ⟨w', hw', hp₂⟩ := hdist p₂ (Or.inr rfl)
    subst hw'
    exact absurd hp₂ (by decide)

end ModalInteraction


-- ════════════════════════════════════════════════════════════════
-- Part IV: Domain Widening (§7)
-- ════════════════════════════════════════════════════════════════

/-!
## §7: Domain Widening

*ein Mann* denotes a contextually restricted **subset** of men
(Schwarzschild 2000: singleton indefinites). *irgendein Mann*
widens to the **full set** (p. 132).

This is the same mechanism as contextual domain restriction in
`DomainRestriction.lean`: *ein* selects from a contextually restricted
domain C ∩ P, while *irgend-* removes the restriction.
-/

section DomainWidening

variable {E : Type}

/-- A simple indefinite selects from a contextually restricted subset. -/
def simpleIndef (D : Set E) (P : E → Prop) : Set E :=
  {x | x ∈ D ∧ P x}

/-- An *irgend-* indefinite widens to the full predicate extension. -/
def irgendIndef (P : E → Prop) : Set E :=
  {x | P x}

/-- Widening weakens existentials: restricted entails widened. -/
theorem simple_entails_widened (D : Set E) (P Q : E → Prop) :
    (∃ x ∈ simpleIndef D P, Q x) → (∃ x ∈ irgendIndef P, Q x) := by
  rintro ⟨x, ⟨_, hP⟩, hQ⟩
  exact ⟨x, hP, hQ⟩

end DomainWidening


-- ════════════════════════════════════════════════════════════════
-- Part V: Distribution Requirement as Implicature (§6, §8)
-- ════════════════════════════════════════════════════════════════

/-!
## §6 & §8: Pragmatic Derivation of the Free Choice Implicature

§6 establishes that the distribution requirement is a conversational
implicature: cancelable (ex. 11), disappears in DE contexts (ex. 12, 14).

§8 derives it via Gricean reasoning about *why the speaker widened*.
Widening could serve: (a) strengthening, (b) avoiding a false claim,
(c) avoiding a false exhaustivity inference (p. 134).

Three cases over alternatives {A, B}:

### (16) Possibility: *Du kannst dir irgendeins leihen*
- T-content: ◇(A ∨ B)
- Implicature: ◇A ↔ ◇B
- Total: ◇A ∧ ◇B

### (17) Necessity: *Du musst dir irgendeins leihen*
- T-content: □(A ∨ B)
- Implicature: □A ↔ □B
- Total: □(A ∨ B) ∧ ◇A ∧ ◇B

### (18) Negated possibility: *auf keinen Fall*
- T-content: ¬◇(A ∨ B)
- No implicature: canceled (widening adds nothing in DE context)
-/

section DistributionRequirement

variable {W : Type}

/-- **(16) Possibility: T-content + implicature → FC.**
    ◇(A ∨ B) with ◇A ↔ ◇B yields ◇A ∧ ◇B. -/
theorem fc_possibility (pA pB : Prop)
    (h_tcontent : pA ∨ pB)
    (h_implic : pA ↔ pB) : pA ∧ pB := by
  cases h_tcontent with
  | inl ha => exact ⟨ha, h_implic.mp ha⟩
  | inr hb => exact ⟨h_implic.mpr hb, hb⟩

/-- **(17) Necessity total meaning (p. 135).**
    □(A∨B) → ◇(A∨B) → ◇A ∨ ◇B, combined with ◇A↔◇B, gives
    □(A∨B) ∧ ◇A ∧ ◇B. -/
theorem fc_necessity_total (nAB : Prop) (pA pB : Prop)
    (h_nAB : nAB)
    (h_nec_to_poss : nAB → pA ∨ pB)
    (h_poss_implic : pA ↔ pB) :
    nAB ∧ pA ∧ pB :=
  ⟨h_nAB, fc_possibility pA pB (h_nec_to_poss h_nAB) h_poss_implic⟩

/-- **(18) Negated possibility: implicature canceled.**
    ¬◇(A ∨ B) implies ¬◇A ∧ ¬◇B. Widening adds nothing. -/
theorem fc_negated_no_implicature
    (pA pB : Prop)
    (h_neg : ¬(pA ∨ pB)) : ¬pA ∧ ¬pB :=
  ⟨fun ha => h_neg (Or.inl ha), fun hb => h_neg (Or.inr hb)⟩

/-- **End-to-end FC derivation for (16)**: Given two propositional
    alternatives under a possibility modal, the T-content is exactly
    `hamblinPoss`, and applying the biconditional implicature yields FC.

    This connects the modal semantics (§7) to the pragmatic derivation
    (§8) in a single theorem. -/
theorem fc_end_to_end_possibility (R : HamblinAccessRel W) (p q : W → Prop)
    (w : W)
    (h_tcontent : hamblinPoss R (fun r => r = p ∨ r = q) w)
    (h_implic : (∃ w', R w w' ∧ p w') ↔ (∃ w', R w w' ∧ q w')) :
    (∃ w', R w w' ∧ p w') ∧ (∃ w', R w w' ∧ q w') := by
  have h_disj : (∃ w', R w w' ∧ p w') ∨ (∃ w', R w w' ∧ q w') := by
    obtain ⟨w', hw', r, hr, hrw⟩ := h_tcontent
    cases hr with
    | inl h => exact Or.inl ⟨w', hw', h ▸ hrw⟩
    | inr h => exact Or.inr ⟨w', hw', h ▸ hrw⟩
  exact fc_possibility _ _ h_disj h_implic

/-- **Bridge to @cite{chierchia-2013}.**
    K&S's pragmatic derivation (Gricean reasoning) and Chierchia's
    grammatical derivation (double exhaustification) both yield
    ◇A ∧ ◇B. Different mechanisms, same empirical prediction. -/
theorem pragmatic_agrees_with_grammatical
    (a : Exhaustification.FreeChoice.FCAltSet W)
    (h : a.exh2) :
    a.freeChoice :=
  Exhaustification.FreeChoice.free_choice_forward a h

end DistributionRequirement


-- ════════════════════════════════════════════════════════════════
-- Part VI: Selectivity & Intervention (§9)
-- ════════════════════════════════════════════════════════════════

/-!
## §9: Non-Selective vs. Selective Indeterminate Systems

Japanese: **non-selective** — same base (*dare*) + different particles
(ka → ∃, mo → ∀, demo → FC). Base does not change shape.

Indo-European: **selective** — *irgendein* associates only with [∃],
not [∀], [Neg], or [Q]. Explained via uninterpretable features (p. 138):
selective indeterminates carry uninterpretable [∃] that must be checked
against an interpretable counterpart via feature movement.

### Beck Effects (§9, p. 139)

When feature movement of uninterpretable [∃] is blocked by an
intervening scope-bearing element, ungrammaticality results:

- (23a) *Was hat sie **nicht** WEM gezeigt? — blocked by *nicht* ([Neg])
- (23b) *Was hat sie **nie** WEM gezeigt? — blocked by *nie*
- (23c) *Was hat **niemand** WEM gezeigt? — blocked by *niemand*
- (23d) *Was hat **fast jeder** WEM gezeigt? — blocked by *fast jeder*
- (23e) *Was hat **(irgend)jemand** WEM gezeigt? — blocked by *jemand*
- (23f) Was hat **der Hans** WEM gezeigt? — OK (definite: no scope feature)
- (23g) Was hat sie **damals** WEM gezeigt? — OK (adverb: no scope feature)
-/

/-- An indeterminate pronoun paradigm: which operators it associates with,
    and whether its morphology changes per operator. -/
structure IndeterminateParadigm where
  language : String
  base : String
  associatesWith : List QuantOperator
  morphologicallyMarked : Bool
  deriving Repr

def IndeterminateParadigm.isNonSelective (p : IndeterminateParadigm) : Bool :=
  p.associatesWith.length ≥ 3

def IndeterminateParadigm.isSelective (p : IndeterminateParadigm) : Bool :=
  p.associatesWith.length ≤ 2

/-- Japanese *dare*: non-selective. Associates with all four operators
    via different particles. Base form does not change. -/
def japaneseParadigm : IndeterminateParadigm where
  language := "Japanese"
  base := "dare"
  associatesWith := [.exists_, .forall_, .neg, .question]
  morphologicallyMarked := false

theorem japanese_non_selective : japaneseParadigm.isNonSelective = true := by native_decide

/-- German *irgend-*: selective. Associates only with [∃] (§9, p. 137).
    Cannot associate with [∀] (ex. 20c), [Neg] (ex. 21), or [Q]. -/
def germanParadigm : IndeterminateParadigm where
  language := "German"
  base := "irgend-"
  associatesWith := [.exists_]
  morphologicallyMarked := true

theorem german_selective : germanParadigm.isSelective = true := by native_decide

-- Beck effect intervention data (§9, p. 139, examples 23a-g)

/-- An intervention datum: an element between a wh-phrase and its
    in-situ associate, and whether the result is grammatical. -/
structure InterventionDatum where
  intervener : String
  gloss : String
  grammatical : Bool
  isScopeBearing : Bool
  deriving Repr, BEq

/-- Beck effect paradigm (examples 23a-g): scope-bearing elements
    block feature movement of [∃]/[Q]; non-scope-bearing elements don't.

    Pattern: `*Was hat sie [INTERVENER] WEM gezeigt?` -/
def beckParadigm : List InterventionDatum :=
  [ ⟨"nicht",           "not",             false, true⟩    -- (23a) Neg
  , ⟨"nie",             "never",           false, true⟩    -- (23b) Neg
  , ⟨"niemand",         "nobody",          false, true⟩    -- (23c) ∃+Neg
  , ⟨"fast jeder",      "almost everyone", false, true⟩    -- (23d) ∀
  , ⟨"(irgend)jemand",  "somebody",        false, true⟩    -- (23e) ∃
  , ⟨"der Hans",        "Hans (definite)",  true, false⟩   -- (23f) no scope feature
  , ⟨"damals",          "then (adverb)",    true, false⟩ ] -- (23g) no scope feature

/-- Scope-bearing elements block; non-scope-bearing elements don't. -/
theorem beck_scope_bearing_block :
    (beckParadigm.filter (·.grammatical == false)).length = 5 ∧
    (beckParadigm.filter (·.grammatical == true)).length = 2 := by
  native_decide

/-- The generalization: scope-bearing = ungrammatical, non-scope-bearing = OK. -/
theorem beck_generalization :
    beckParadigm.all (fun d => d.isScopeBearing == !d.grammatical) = true := by
  native_decide


-- ════════════════════════════════════════════════════════════════
-- Bridge to Fragment Entries
-- ════════════════════════════════════════════════════════════════

open Fragments.Japanese.Determiners (dare_ka dare_mo)
open Fragments.German.ModalIndefinites (irgendeinEntry)

/-- Same base (*dare*), different force via particle alternation. -/
theorem same_base_different_force :
    dare_ka.indeterminate = dare_mo.indeterminate ∧
    dare_ka.qforce ≠ dare_mo.qforce := by
  exact ⟨rfl, by decide⟩

/-- dare-ka is existential; paradigm predicts ∃ association. -/
theorem dare_ka_existential_from_paradigm :
    dare_ka.qforce = .existential ∧
    japaneseParadigm.associatesWith.contains .exists_ = true :=
  ⟨rfl, by native_decide⟩

/-- dare-mo is universal; paradigm predicts ∀ association. -/
theorem dare_mo_universal_from_paradigm :
    dare_mo.qforce = .universal ∧
    japaneseParadigm.associatesWith.contains .forall_ = true :=
  ⟨rfl, by native_decide⟩

/-- *irgendein* is existential-only + not-at-issue (domain widening). -/
theorem irgendein_existential_only :
    germanParadigm.associatesWith = [.exists_] ∧
    irgendeinEntry.status = .notAtIssue :=
  ⟨rfl, rfl⟩


-- ════════════════════════════════════════════════════════════════
-- Part VII: Cross-Linguistic Indeterminate Typology (§1)
-- ════════════════════════════════════════════════════════════════

/-!
## §1: Indeterminate Pronoun Paradigms Cross-Linguistically

@cite{haspelmath-1997} (p. 277, diacritics omitted). The Latvian
paradigm illustrates a selective system: each operator association is
morphologically marked by a distinct prefix (kaut- existential,
ne- under direct negation, jeb- indirect negation/comparatives/FC).

Latvian paradigm data imported from `Fragments/Latvian/IndeterminatePronouns.lean`.
-/

open Fragments.Latvian.IndeterminatePronouns (paradigm)

/-- Latvian is morphologically marked (selective); Japanese is not. -/
theorem selective_contrast :
    paradigm.length = 6 ∧ japaneseParadigm.morphologicallyMarked = false :=
  ⟨rfl, rfl⟩


end Phenomena.ModalIndefinites.Studies.KratzerShimoyama2002
