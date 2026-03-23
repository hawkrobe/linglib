import Linglib.Core.Semantics.Presupposition
import Linglib.Core.Logic.ThreeValuedLogic
import Linglib.Core.Semantics.CommonGround
import Linglib.Theories.Semantics.Presupposition.Accommodation
import Linglib.Theories.Semantics.Presupposition.LocalContext
import Linglib.Theories.Semantics.Dynamic.ABLE.Basic

/-!
# Beaver (2001) @cite{beaver-2001}

Presupposition and Assertion in Dynamic Semantics: A Critical Review of
Linguistic Theories of Presupposition. CSLI Publications.

## Overview

Beaver's monograph compares four families of presupposition theory in Part I,
then develops his own dynamic theory (PUL) in Part II:

**Part I: A Critical Review (Chs. 1-5)**
1. **Ch. 1**: Introduction — presupposition identification, basic data
2. **Ch. 2 Multivalence**: Strong Kleene, Weak Kleene, Middle Kleene (§1-2)
3. **Ch. 3 Cancellation and filtering**: Karttunen's heritage functions,
   Heim's CCP, the convergence of heritage/filtering/CCP (§3)
4. **Ch. 4 Common ground**: Stalnaker's context sets, File Change Semantics,
   DPL — all compute from `PrProp.presup` and `PrProp.assertion` (§4)
5. **Ch. 5 Accommodation**: Lewis 1979, van der Sandt 1992, Heim's
   global-preference synthesis, conditional presuppositions (§5-6)

**Part II: A Dynamic Theory (Chs. 6-10)**
6. **Ch. 6 PUL**: Presuppositional Update Logic — Beaver's formalism (§7)
7. **Ch. 7 ABLE**: "A Bit Like English" — fragment mapping English to PUL
8. **Ch. 8 Quantification**: Presupposition projection under quantifiers
9. **Ch. 9 Accommodation in ABLE**: Accommodation within PUL
10. **Ch. 10 Conclusion**: Summary and open problems

## Structural Connection to PrProp

The central insight formalized here: Karttunen's heritage functions, Heim's
filtering connectives, and CCP-based local contexts all compute projection
from the same source — **PrProp.presup**.

- Heritage function for `p → q` = `(impFilter p q).presup` (by construction)
- Local context for q in `p → q` = `{ w ∈ c | p.assertion w }` (from PrProp)
- Accommodation operates on `p.presup` directly

`PrProp` IS the two-dimensional representation of @cite{karttunen-peters-1979}:
`.presup` = their P-function, `.assertion` = their A-function. The filtering
connectives resolve the "binding problem" (variables not linked between
dimensions) by computing compound presuppositions from BOTH `.presup` and
`.assertion` fields of the same `PrProp W` — the shared type parameter `W`
ensures variables range over the same domain.

No separate heritage type is needed. Filtering connectives ARE heritage
functions — the `.presup` field of a filtering connective IS the heritage
function output.

## Formalization Coverage

This file formalizes key results from Chs. 2-7. The ABLE fragment (Ch. 7)
is formalized in `Theories.Semantics.Dynamic.ABLE.Basic` and demonstrated
here via worked examples (§8). Quantifier projection (Ch. 8) and ABLE
accommodation (Ch. 9) are not yet formalized. Quantifier projection is
partially addressed by the `QuantifierProjection` type in
`PresuppositionPolarity.lean`.
-/

namespace Phenomena.Presupposition.Studies.Beaver2001

open Core.Presupposition
open Core.Proposition
open Core.Duality
open Core.CommonGround

variable {W : Type*}

-- ══════════════════════════════════════════════════════════
-- § 1. The Symmetry Problem and Fact 2.1
-- (@cite{beaver-2001} Ch. 2)
-- ══════════════════════════════════════════════════════════

/-! ### SK vs MK: Symmetry and Presupposition Projection

Strong Kleene disjunction is symmetric: `join a b = join b a`.
Middle Kleene disjunction is NOT: `joinMiddle a b ≠ joinMiddle b a` in general.
Natural language disjunction appears to be symmetric for presupposition
projection, which favors the SK/heritage prediction over CCP.

### Fact 2.1: SK Projection Predictions

@cite{beaver-2001} Fact 2.1 gives the SK projection predictions for all
binary connectives. The hallmark of SK is **uniformity**: every binary
connective (∧, ∨, →) predicts the same presupposition — π(φ) ∧ π(ψ) —
and **symmetry**: swapping φ and ψ does not change the projection.

This uniformity is empirically too strong: "if p then q" presupposes
π(p) ∧ (A(p) → π(q)), not π(p) ∧ π(q). The filtering connectives
(`PrProp.impFilter`, etc.) capture this asymmetry. -/

/-- SK disjunction is symmetric for presupposition projection.
    @cite{beaver-2001} Ch. 2: the correct empirical prediction. -/
theorem sk_disjunction_symmetric (a b : Truth3) :
    Truth3.join a b = Truth3.join b a := by
  cases a <;> cases b <;> rfl

/-- MK disjunction is NOT symmetric.
    @cite{beaver-2001} Ch. 2: MK captures left-to-right processing
    but overpredicts asymmetry for disjunction. -/
theorem mk_disjunction_asymmetric :
    ∃ a b : Truth3, Truth3.joinMiddle a b ≠ Truth3.joinMiddle b a :=
  ⟨.true, .indet, by simp [Truth3.joinMiddle, Truth3.join]⟩

/-- Fact 2.1, negation: SK negation preserves presupposition.
    The presupposition of ¬φ is exactly π(φ). -/
theorem sk_neg_presup (p : PrProp W) :
    (PrProp.neg p).presup = p.presup := rfl

/-- Fact 2.1, uniformity: all SK binary connectives produce the
    SAME presupposition — π(φ) ∧ π(ψ) — regardless of the connective.
    This is the hallmark of the SK approach: conjunction, disjunction,
    and implication are indistinguishable from the presupposition's
    perspective. -/
theorem sk_binary_presup_uniform (p q : PrProp W) :
    (PrProp.and p q).presup = (PrProp.or p q).presup ∧
    (PrProp.or p q).presup = (PrProp.imp p q).presup := ⟨rfl, rfl⟩

/-- Fact 2.1, symmetry: SK binary presuppositions are symmetric.
    Swapping φ and ψ does not change the presupposition. -/
theorem sk_presup_symmetric (p q : PrProp W) :
    (PrProp.and p q).presup = (PrProp.and q p).presup := by
  funext w; simp only [PrProp.and]
  cases p.presup w <;> cases q.presup w <;> rfl

/-- Filtering presuppositions are NOT symmetric: there exist p, q where
    swapping the operands changes the presupposition. This is the empirically
    correct prediction — "if p then q" and "if q then p" have different
    presuppositions. -/
theorem filtering_presup_not_symmetric :
    ∃ (p q : PrProp Bool),
      (PrProp.andFilter p q).presup ≠ (PrProp.andFilter q p).presup := by
  refine ⟨⟨λ _ => true, λ b => b⟩, ⟨λ _ => false, λ _ => true⟩, ?_⟩
  intro h; exact absurd (congr_fun h false) (by decide)

-- ══════════════════════════════════════════════════════════
-- § 2. PrProp as Two-Dimensional Representation
-- (@cite{beaver-2001} Ch. 2, §2.2; @cite{karttunen-peters-1979})
-- ══════════════════════════════════════════════════════════

/-! ### The Two-Dimensional Approach

@cite{karttunen-peters-1979} proposed parallel translation functions A(·)
and P(·) that compute assertion and presupposition separately. This is
structurally identical to `PrProp`:

- `PrProp.assertion` = A(·) (assertion translation)
- `PrProp.presup` = P(·) (presupposition translation)

The **binding problem** (@cite{beaver-2001} Ch. 2): in Karttunen & Peters'
system, quantifier variables in the assertion dimension are not linked to
variables in the presupposition dimension. For example, in "Every student
stopped smoking", the student bound by "every" in the assertion should be
the same student bound in the presupposition — but the two translation
functions compute independently.

**PrProp resolves this by construction**: both `.presup` and `.assertion`
are functions from the SAME type `W`. When `W` includes variable
assignments (as in `W = World × Assignment`), the binding is shared. The
filtering connectives explicitly reference both fields of a single PrProp,
ensuring the variables agree across dimensions. -/

/-- Filtering connectives reference BOTH `.presup` and `.assertion`,
    resolving the binding problem. The presupposition of `impFilter p q`
    depends on `p.assertion` (assertion of the antecedent) — linking
    the two dimensions. -/
theorem filtering_links_dimensions (p q : PrProp W) (w : W) :
    (PrProp.impFilter p q).presup w =
    (p.presup w && ((p.assertion w).not || q.presup w)) := rfl

/-- SK connectives do NOT link dimensions: they reference only `.presup`,
    ignoring `.assertion`. This means they cannot capture filtering. -/
theorem sk_ignores_assertion (p q : PrProp W) (w : W) :
    (PrProp.and p q).presup w = (p.presup w && q.presup w) := rfl

-- ══════════════════════════════════════════════════════════
-- § 3. Heritage = Filtering (by construction)
-- (@cite{beaver-2001} Ch. 3)
-- ══════════════════════════════════════════════════════════

/-! Karttunen's heritage function for a connective is the presupposition
that the compound inherits from its parts. For filtering connectives,
this IS the `.presup` field — no separate heritage type needed.

The convergence of heritage, filtering, and CCP is @cite{beaver-2001}'s
central result for Chs. 2-4. We show it holds by construction: all three
read from the same `PrProp.presup` and `PrProp.assertion` fields. -/

/-- Heritage function for conditionals IS `.presup` of `impFilter`.
    @cite{beaver-2001} Ch. 3: heritage, filtering, and CCP agree. -/
example (p q : PrProp W) : (PrProp.impFilter p q).presup =
    (λ w => p.presup w && ((p.assertion w).not || q.presup w)) := rfl

/-- Heritage function for conjunction IS `.presup` of `andFilter`. -/
example (p q : PrProp W) : (PrProp.andFilter p q).presup =
    (λ w => p.presup w && ((p.assertion w).not || q.presup w)) := rfl

/-- Heritage function for disjunction IS `.presup` of `orFilter` (symmetric). -/
example (p q : PrProp W) : (PrProp.orFilter p q).presup =
    (λ w => ((p.assertion w).not || q.presup w) &&
            ((q.assertion w).not || p.presup w) &&
            (p.presup w || q.presup w)) := rfl

/-- Filtering vs SK: filtering conjunction is strictly weaker than SK
    conjunction in its presupposition requirements. When p's assertion
    entails q's presupposition, filtering drops q's presupposition
    entirely — SK never does. -/
theorem filtering_weaker_than_sk (p q : PrProp W)
    (h : ∀ w, p.assertion w = true → q.presup w = true) :
    (PrProp.andFilter p q).presup = p.presup := by
  funext w; simp only [PrProp.andFilter]
  cases hp : p.presup w
  · rfl
  · cases ha : p.assertion w
    · rfl
    · simp [h w ha]

-- ══════════════════════════════════════════════════════════
-- § 4. Static ↔ Dynamic Agreement
-- (@cite{beaver-2001} Chs. 3-4)
-- ══════════════════════════════════════════════════════════

/-! The static filtering connectives and the dynamic CCP approach
agree for conditionals. Both compute projection from PrProp.presup
and PrProp.assertion — when the context entails p's presupposition,
filtering holds iff the local context (from p.assertion) entails
q's presupposition (from q.presup).

### Connection to Common Ground and File Change Semantics

@cite{beaver-2001} Ch. 4 discusses @cite{stalnaker-1974}'s common ground
and @cite{heim-1983}'s File Change Semantics in detail. The `ContextSet W`
type used here IS the context set from `Core.Semantics.CommonGround`.
`ContextSet.update` IS Heim's FCS update: intersect the context set with a
proposition, keeping only worlds where the proposition holds.

The local context at position q in `p → q` is
`ContextSet.update c p.assertion` — exactly
`Semantics.Presupposition.LocalContext.localCtxConsequent`. -/

/-- File Change Semantics update (@cite{heim-1983}) IS `ContextSet.update`.
    The context set c updated with proposition p keeps only worlds where
    p holds. This is the foundation of CCP/dynamic semantics (Ch. 4). -/
example (c : ContextSet W) (p : BProp W) :
    ContextSet.update c p = λ w => c w ∧ p w = true := rfl

/-- Static filtering = dynamic local context for conditionals.
    Both derive from PrProp fields: `.presup` and `.assertion`.
    This is the cornerstone theorem connecting three approaches:
    1. Static filtering (@cite{karttunen-1973})
    2. Heim's CCP / File Change Semantics (@cite{heim-1983})
    3. Local contexts (@cite{schlenker-2009}) -/
theorem static_dynamic_agreement (c : ContextSet W)
    (p q : PrProp W) :
    (∀ w, c w → (PrProp.impFilter p q).presup w = true) ↔
    (∀ w, c w → p.presup w = true ∧
                (p.assertion w = true → q.presup w = true)) :=
  Semantics.Presupposition.LocalContext.local_context_matches_impFilter c p q

-- ══════════════════════════════════════════════════════════
-- § 5. Accommodation and Cancellation
-- (@cite{beaver-2001} Ch. 5)
-- ══════════════════════════════════════════════════════════

/-! Heim's observation: global accommodation preference ≈ Gazdar cancellation.
Accommodation operates on `p.presup` directly — the structural connection
to PrProp is by construction. -/

open Semantics.Presupposition.Accommodation

/-- Heim's synthesis: global preference selects global when consistent.
    Accommodation input is `p.presup` — structurally connected to PrProp. -/
theorem heim_synthesis_projection (c : ContextSet W)
    (p : PrProp W)
    (h : ContextSet.nonEmpty
           (globalAccommodate c p.presup)) :
    heimSelect c p.presup = .global :=
  heim_projection_when_consistent c p.presup h

/-- Heim's synthesis: global preference selects local when inconsistent.
    This matches Gazdar's cancellation prediction. -/
theorem heim_synthesis_cancellation (c : ContextSet W)
    (p : PrProp W)
    (h : ¬ContextSet.nonEmpty
           (globalAccommodate c p.presup)) :
    heimSelect c p.presup = .local :=
  heim_cancellation_equivalence c p.presup h

-- ══════════════════════════════════════════════════════════
-- § 6. Conditional Presuppositions
-- (@cite{beaver-2001} Ch. 5)
-- ══════════════════════════════════════════════════════════

/-! @cite{beaver-2001} argues that presuppositions can themselves be
conditional. The Spaceman Spiff example:

  "If Spaceman Spiff lands on Planet X, he will be bothered by the
  fact that his weight is greater than it would be on Earth."

The presupposition (Spiff's weight > Earth weight) is not an unconditional
global presupposition — it is conditional on the antecedent. Neither
filtering nor CCP can systematically produce conditional presuppositions. -/

inductive SpiffWorld where
  | onEarth | onPlanetX_heavy | onPlanetX_light | inSpace
  deriving DecidableEq, Repr, Inhabited

/-- "Spiff lands on Planet X" — no presupposition. -/
def spiffLands : PrProp SpiffWorld where
  presup := λ _ => true
  assertion := λ w => match w with
    | .onPlanetX_heavy | .onPlanetX_light => true
    | _ => false

/-- "Spiff's weight is greater than on Earth" — presupposes being
    somewhere with weight (not in space). -/
def weightGreater : PrProp SpiffWorld where
  presup := λ w => match w with
    | .inSpace => false
    | _ => true
  assertion := λ w => match w with
    | .onPlanetX_heavy => true
    | _ => false

/-- Filtering correctly predicts: the antecedent filters the
    consequent's presupposition. -/
theorem spiff_conditional_filters :
    ∀ w, spiffLands.presup w = true →
    (spiffLands.assertion w = true → weightGreater.presup w = true) := by
  intro w _ ha
  cases w <;> simp_all [spiffLands, weightGreater]

/-- The actual presupposition people infer is CONDITIONAL:
    "IF Spiff lands on Planet X, his weight > Earth weight."
    This is stronger than what filtering predicts. -/
def conditionalPresup : BProp SpiffWorld :=
  λ w => match w with
    | .onPlanetX_heavy => true
    | .onPlanetX_light => false
    | _ => true

/-- The conditional presupposition is NOT equivalent to the filtering
    prediction. Filtering predicts weight-is-defined; the conditional
    presupposition additionally requires weight > Earth. -/
theorem conditional_presup_stronger_than_filtering :
    ∃ w, (PrProp.impFilter spiffLands weightGreater).presup w = true ∧
         conditionalPresup w = false := by
  exact ⟨.onPlanetX_light, by simp [PrProp.impFilter, spiffLands, weightGreater],
         by simp [conditionalPresup]⟩

-- ══════════════════════════════════════════════════════════
-- § 7. PUL: Presuppositional Update Logic
-- (@cite{beaver-2001} Ch. 6)
-- ══════════════════════════════════════════════════════════

/-! ### Beaver's Dynamic Theory

PUL is Beaver's own formal system from Part II. It combines partial
semantics with dynamic update: presuppositions cause undefinedness of
context updates. The core operations map to `ContextSet` operations:

- **Atomic update** σ[p] = σ ∩ {w | p(w)} = `ContextSet.update σ p`
- **Negation** σ[-φ] = σ \ σ[φ] (set complement within input)
- **Conjunction** σ[φ ∧ ψ] = σ[φ][ψ] (sequential update)
- **Conditional** σ[φ → ψ] = σ \ (σ[φ] \ σ[φ][ψ]) (residual)

PUL conjunction is exactly CCP sequential composition
(`CCP.seq` from `Theories.Semantics.Dynamic.Core.CCP`).
PUL negation differs from CCP's test-based negation:
PUL computes the complement within the input state, while CCP
negation passes or fails the entire state.

### Partiality

In Beaver's book, PUL updates are PARTIAL — presupposition failure
causes the update to be undefined. Here we define the total operations
(the defined cases). The presupposition check is modeled separately
through `PrProp.presup`: a PUL update from a PrProp sentence p is
defined at context σ iff `∀ w, σ w → p.presup w = true`. -/

/-- PUL atomic update: intersect context with proposition.
    @cite{beaver-2001} Ch. 6. Equivalent to `ContextSet.update`. -/
def pulUpdate (p : BProp W) (σ : ContextSet W) : ContextSet W :=
  ContextSet.update σ p

/-- PUL negation: complement within the input state.
    σ[-φ] = σ \ σ[φ]. Note: this differs from CCP.neg, which is
    test-based (pass/fail). PUL negation selects worlds where φ
    does NOT hold. -/
def pulNeg (φ : ContextSet W → ContextSet W) (σ : ContextSet W) : ContextSet W :=
  λ w => σ w ∧ ¬ (φ σ) w

/-- PUL conjunction: sequential update.
    σ[φ ∧ ψ] = σ[φ][ψ]. This is CCP.seq by construction. -/
def pulConj (φ ψ : ContextSet W → ContextSet W) : ContextSet W → ContextSet W :=
  ψ ∘ φ

/-- PUL conditional: residual.
    σ[φ → ψ] = σ \ (σ[φ] \ σ[φ][ψ]).
    Worlds in σ that survive are those where: if φ holds, then ψ
    holds in the φ-updated context. -/
def pulImpl (φ ψ : ContextSet W → ContextSet W) (σ : ContextSet W) : ContextSet W :=
  λ w => σ w ∧ ¬ ((φ σ) w ∧ ¬ (ψ (φ σ)) w)

/-- PUL atomic update is `ContextSet.update` (by construction). -/
theorem pulUpdate_eq (p : BProp W) (σ : ContextSet W) :
    pulUpdate p σ = ContextSet.update σ p := rfl

/-- PUL negation is eliminative: it only removes worlds. -/
theorem pulNeg_eliminative (φ : ContextSet W → ContextSet W)
    (σ : ContextSet W) (w : W) :
    pulNeg φ σ w → σ w := And.left

/-- PUL conjunction of atomic updates equals iterated context update. -/
theorem pulConj_update (p q : BProp W) (σ : ContextSet W) :
    pulConj (pulUpdate p) (pulUpdate q) σ =
    ContextSet.update (ContextSet.update σ p) q := rfl

/-- PUL conditional on atomic propositions: a world survives iff
    it is in σ and the material conditional holds.
    When φ = pulUpdate p and ψ = pulUpdate q, the conditional
    simplifies to the classical material conditional on the
    proposition values. -/
theorem pulImpl_atomic (p q : BProp W) (σ : ContextSet W) (w : W) :
    pulImpl (pulUpdate p) (pulUpdate q) σ w ↔
    σ w ∧ (p w = true → q w = true) := by
  simp only [pulImpl, pulUpdate, ContextSet.update]
  constructor
  · intro ⟨hσ, hcond⟩
    refine ⟨hσ, fun hp => ?_⟩
    by_contra hq
    exact hcond ⟨⟨hσ, hp⟩, fun ⟨_, hq'⟩ => hq hq'⟩
  · intro ⟨hσ, himp⟩
    refine ⟨hσ, fun ⟨⟨_, hp⟩, hn⟩ => ?_⟩
    exact hn ⟨⟨hσ, hp⟩, himp hp⟩

-- ══════════════════════════════════════════════════════════
-- § 8. ABLE Worked Examples
-- (@cite{beaver-2001} Chs. 7-8)
-- ══════════════════════════════════════════════════════════

/-! ### ABLE Fragment Demonstrations

The ABLE formalization in `Theories.Semantics.Dynamic.ABLE.Basic` provides
the `Formula` type and its evaluation semantics. Here we instantiate it
with the Spaceman Spiff scenario from §6 to demonstrate projection through
negation and conditionals.

Key correspondences to PUL:
- `Formula.presup` (∂) = `CCP.must` — full support test (D59)
- `Formula.and` = `CCP.seq` — sequential composition
- `Formula.might` = `CCP.might` — compatibility test
- `Formula.not` ≠ `CCP.neg` — PUL negation is set complement, not pass/fail

### Structural Admittance (D54)

Admittance is the mechanism by which presuppositions project. A context σ
*admits* a formula φ iff every subformula's presupposition is satisfied at
its local context (the context that results from processing prior material).
This is why presupposition projection is asymmetric for conjunction:
in `φ AND ψ`, σ must admit φ, and σ[φ] must admit ψ — so ψ's presupposition
can be "filtered" by φ's content. -/

open Semantics.Dynamic.ABLE (Formula)

section ABLEExamples

/-- Represent the Spiff scenario as a set-based info state.
    Each element of the set is a possible world. -/
def spiffState : Set SpiffWorld :=
  {.onEarth, .onPlanetX_heavy, .onPlanetX_light, .inSpace}

/-- ABLE formula: "Spiff lands on Planet X" (no presupposition). -/
def ableLands : Formula SpiffWorld :=
  .pred (λ w => match w with
    | .onPlanetX_heavy | .onPlanetX_light => True
    | _ => False)

/-- ABLE formula: "Spiff's weight > Earth weight"
    with presupposition ∂(has-weight). -/
def ableWeightGreater : Formula SpiffWorld :=
  .and
    (.presup (.pred (λ w => match w with | .inSpace => False | _ => True)))
    (.pred (λ w => match w with | .onPlanetX_heavy => True | _ => False))

/-- Admitting "weight > Earth" requires the context to entail has-weight.
    The full info state does NOT admit it (space is included). -/
theorem spiff_full_state_rejects_weight :
    ¬ableWeightGreater.pulAdmits spiffState := by
  intro ⟨h, _⟩
  simp only [Formula.pulAdmits, Formula.eval] at h
  have : SpiffWorld.inSpace ∈ ({ p : SpiffWorld | p ∈ spiffState ∧
    match p with | .inSpace => False | _ => True }) := by
    rw [h]; exact Or.inr (Or.inr (Or.inr (Set.mem_singleton_iff.mpr rfl)))
  exact this.2

/-- After learning "Spiff lands on Planet X", the state admits "weight > Earth".
    This is Fact 8.3: the conditional presupposition is satisfied. -/
theorem spiff_lands_then_weight_admits :
    ableWeightGreater.pulAdmits (ableLands.eval spiffState) := by
  constructor
  · -- ∂(has-weight) is satisfied after landing
    simp only [Formula.eval, Formula.pulAdmits]
    ext w; simp only [Set.mem_setOf_eq]
    constructor
    · intro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2⟩
    · intro ⟨h1, h2⟩
      refine ⟨⟨h1, h2⟩, ?_⟩
      cases w <;> simp_all [spiffState]
  · trivial

end ABLEExamples

end Phenomena.Presupposition.Studies.Beaver2001
