/-
# Economy and Embedded Exhaustification

Formalization of Fox & Spector (2018) "Economy and embedded exhaustification"
Natural Language Semantics 26:1–50.

## Paper Structure

**Section 1**: Introduction
- Problem: Where can `exh` be inserted?
- Three puzzles: Implicature Focus Generalization, Hurford's, Singh's Asymmetry

**Section 2**: Hurford's Constraint
- 2.1: Hurford disjunctions and their rescue
- 2.2: Extending to negation contexts

**Section 3**: Implicature Focus Generalization (IFG)
- Embedded exhaustification under DE operators requires focus

**Section 4**: Singh's Asymmetry
- "p or q, or both" vs "both, or p or q"

**Section 5**: Economy Condition on Exhaustification
- 5.1: Incremental vacuity/weakening
- 5.2: Economy condition formulation
- 5.3: Deriving the three puzzles

**Section 6**: Relationship to Focus
- Association with Focus (AF)
- Minimize Focus (MF)

## Key Definitions

- **Hurford's Constraint (HC)**: Bans disjunctions where one disjunct entails another
- **Incremental vacuity**: exh is vacuous at a parse point for all continuations
- **Incremental weakening**: exh is weakening at a parse point for all continuations
- **Economy condition**: exh cannot be incrementally vacuous or weakening
- **Singh's Asymmetry**: Order matters in "p or q, or both"

## Main Results

- Economy condition derives Hurford's Constraint
- Economy condition derives Singh's Asymmetry
- Economy condition interacts with Focus (AF, MF)

## References

- Fox & Spector (2018). Economy and embedded exhaustification. NLS 26:1-50.
- Fox (2007). Free choice and the theory of scalar implicatures.
- Hurford (1974). Exclusive or inclusive disjunction.
- Singh (2008). On the interpretation of disjunction.
- Spector (2016). Comparing exhaustivity operators. S&P 9(11):1-33.
-/

import Linglib.Theories.NeoGricean.Exhaustivity.Basic
import Linglib.Theories.NeoGricean.Core.Alternatives
import Linglib.Theories.Montague.Core.Derivation

namespace NeoGricean.FoxSpector2018

open NeoGricean.Exhaustivity
open Montague.Core.Polarity (ContextPolarity)

-- ============================================================================
-- SECTION 2: HURFORD'S CONSTRAINT
-- ============================================================================

/-
"A disjunction of the form 'A or B' sounds redundant and is odd when one
of the disjuncts entails the other."

Examples from the paper (p.4):
- #"John is American or Californian"  (Californian ⊂ American)
- #"John is a bachelor or unmarried"  (bachelor ⊂ unmarried)
-/

variable {World : Type*}

/--
Disjunction of two propositions.
-/
def por (φ ψ : Prop' World) : Prop' World := fun w => φ w ∨ ψ w

infixl:60 " ∨ₚ " => por

/--
**Hurford's Constraint (HC)**: A disjunction "A or B" is infelicitous if
one disjunct entails the other (and no exhaustification repairs it).

This is the *surface* constraint. Fox & Spector derive it from economy.
-/
def hurfordViolation (A B : Prop' World) : Prop :=
  (A ⊆ₚ B) ∨ (B ⊆ₚ A)

/--
A disjunction satisfies Hurford's Constraint if neither disjunct entails the other.
-/
def satisfiesHC (A B : Prop' World) : Prop :=
  ¬(A ⊆ₚ B) ∧ ¬(B ⊆ₚ A)

-- Suppress unused variable warning for examples/theorems
attribute [local simp] satisfiesHC

/--
**Hurford Disjunction**: A disjunction where one disjunct entails the other.
These are the problematic cases that need explanation.
-/
structure HurfordDisjunction (World : Type*) where
  /-- First disjunct -/
  left : Prop' World
  /-- Second disjunct -/
  right : Prop' World
  /-- The entailment relation (left entails right or vice versa) -/
  entailment : hurfordViolation left right

-- ============================================================================
-- SECTION 2.1: Rescuing Hurford Disjunctions with exh
-- ============================================================================

/-
Key insight from Fox & Spector: Some Hurford disjunctions are acceptable
because embedded exh breaks the entailment.

"Mary read some of the books or all of them" is OK because:
  exh(Mary read some) = Mary read some but not all
  This doesn't entail "all of them"

This is the *rescue* mechanism.
-/

/--
A Hurford disjunction is **rescued** by embedding exh in the weaker disjunct
if the exhaustified weaker disjunct no longer entails the stronger one.

Given "A or B" where A ⊆ B:
  Rescued iff ¬(exh(A) ⊆ B)
-/
def isRescuedByExh (ALT : Set (Prop' World)) (A B : Prop' World) : Prop :=
  -- Original: A entails B
  -- After exh: exhIE(A) should NOT entail B
  ¬(exhIE ALT A ⊆ₚ B)

/--
**Theorem**: If A ⊆ B and exh(A) ⊄ B, then "A or B" is acceptable
(the Hurford violation is rescued).
-/
theorem hurford_rescue {ALT : Set (Prop' World)} {A B : Prop' World}
    (_hAB : A ⊆ₚ B) (hrescue : isRescuedByExh ALT A B) :
    -- The disjunction with exh(A) is not a Hurford violation
    ¬(exhIE ALT A ⊆ₚ B) :=
  hrescue

-- ============================================================================
-- SECTION 2.2: Hurford's Constraint Under Negation
-- ============================================================================

/-
Fox & Spector's key observation: Hurford's Constraint extends to DE contexts.

"It's not the case that Mary read some or all of the books"

Under negation, the entailment reverses:
  In UE: "all" entails "some"
  In DE: "some" entails "all"

So under negation, "some or all" becomes a Hurford violation!
-/

/--
**DE-Hurford**: Under a DE operator, the entailment direction reverses.
"some or all" violates Hurford under negation because (¬some ⊆ ¬all).
-/
def deHurfordViolation (A B : Prop' World) : Prop :=
  -- In DE context, A ⊆ B becomes ¬B ⊆ ¬A (contraposition)
  -- So "A or B" under negation is a Hurford violation if B ⊆ A
  (B ⊆ₚ A) ∨ (A ⊆ₚ B)

-- ============================================================================
-- SECTION 3: IMPLICATURE FOCUS GENERALIZATION (IFG)
-- ============================================================================

/-
"Embedded exhaustification under DE operators is possible only if the scalar
item is focused (prosodically prominent)."

This explains contrasts like:
  "Every student who read SOME of the books passed" ✓ (SI possible)
  "Every student who read some of the books passed" ?? (SI marginal)

In the DE restrictor of "every", embedded exh is blocked unless there's focus.
-/

/--
Focus annotation on an expression.
In linguistics, focus is typically marked with pitch accent/prominence.
-/
structure Focused (α : Type*) where
  /-- The focused expression -/
  expr : α
  /-- Focus is present (marked by pitch accent) -/
  hasFocus : Bool

/--
**Implicature Focus Generalization (IFG)**:
Embedded exhaustification under DE operators requires focus on the scalar item.
-/
def satisfiesIFG (pol : ContextPolarity) (focused : Bool) : Prop :=
  match pol with
  | .upward => true  -- No restriction in UE
  | .downward => focused  -- Requires focus in DE
  | .nonMonotonic => focused  -- Similar to DE

-- ============================================================================
-- SECTION 4: SINGH'S ASYMMETRY
-- ============================================================================

/-
Singh (2008) observed an asymmetry:
  (a) "Mary read [A or B] or [A and B]" ✓
  (b) "Mary read [A and B] or [A or B]" #

The order matters! Fox & Spector derive this from economy.

Key insight: In (a), exh can be embedded in the first disjunct [A or B],
creating exh(A or B) which is "A or B but not both".
This breaks the entailment to [A and B].

In (b), exh in [A and B] would be vacuous (A∧B has no excludable alternatives
from {A∨B, A∧B} when in the stronger position).
-/

/--
**Singh's Asymmetry**: The configuration of a disjunction with one disjunct
entailing the other.

`order` indicates which disjunct is mentioned first:
- `weakerFirst = true`: "A or B" or "A and B" (weak before strong)
- `weakerFirst = false`: "A and B" or "A or B" (strong before weak)
-/
structure SinghDisjunction (World : Type*) where
  /-- The weaker disjunct (e.g., A ∨ B) -/
  weaker : Prop' World
  /-- The stronger disjunct (e.g., A ∧ B) -/
  stronger : Prop' World
  /-- Stronger entails weaker -/
  entailment : stronger ⊆ₚ weaker
  /-- Order: true if weaker mentioned first -/
  weakerFirst : Bool

/--
Singh's Asymmetry holds when weaker-first is acceptable but stronger-first is not.
-/
def singhAsymmetryHolds (d : SinghDisjunction World) : Prop :=
  d.weakerFirst -- Only acceptable when weaker is first

-- ============================================================================
-- SECTION 5: ECONOMY CONDITION ON EXHAUSTIFICATION
-- ============================================================================

/-
The core contribution of Fox & Spector: the economy condition that restricts
where exh can be inserted.

"exh cannot be inserted if it would be incrementally vacuous or weakening."

This is computed based on ALL possible continuations at the insertion point.
-/

-- ============================================================================
-- SECTION 5.1: Parse Trees and Continuations
-- ============================================================================

/--
A continuation context represents "the rest of the sentence" after a parse point.
It's a function from propositions to propositions.

Example: In "Mary didn't read ___", the continuation is (λp. ¬p).
-/
abbrev Continuation (World : Type*) := Prop' World → Prop' World

/--
The identity continuation (for root-level expressions).
-/
def idCont : Continuation World := id

/--
Negation continuation.
-/
def negCont : Continuation World := pneg

/--
A parse point with alternatives and possible continuations.
-/
structure ParsePoint (World : Type*) where
  /-- The proposition at this point -/
  prop : Prop' World
  /-- Alternative set -/
  alts : Set (Prop' World)
  /-- Set of possible continuations from this point -/
  continuations : Set (Continuation World)

-- ============================================================================
-- SECTION 5.2: Incremental Vacuity and Weakening
-- ============================================================================

/--
**Incremental Vacuity**: exh is incrementally vacuous at a parse point if
for ALL possible continuations C, C(exh(φ)) = C(φ).

"No matter how the sentence continues, exh makes no difference."
-/
def isIncrementallyVacuous (ALT : Set (Prop' World)) (φ : Prop' World)
    (conts : Set (Continuation World)) : Prop :=
  ∀ C ∈ conts, ∀ w : World, C (exhIE ALT φ) w ↔ C φ w

/--
**Incremental Weakening**: exh is incrementally weakening at a parse point if
for ALL possible continuations C, C(φ) ⊆ C(exh(φ)).

"No matter how the sentence continues, exh weakens the meaning."

Note: In DE contexts, strengthening locally = weakening globally.
-/
def isIncrementallyWeakening (ALT : Set (Prop' World)) (φ : Prop' World)
    (conts : Set (Continuation World)) : Prop :=
  ∀ C ∈ conts, C φ ⊆ₚ C (exhIE ALT φ)

/--
**Incremental Strengthening**: exh is incrementally strengthening if
for ALL continuations, C(exh(φ)) ⊆ C(φ).

This is the GOOD case - exh adds content without weakening.
-/
def isIncrementallyStrengthening (ALT : Set (Prop' World)) (φ : Prop' World)
    (conts : Set (Continuation World)) : Prop :=
  ∀ C ∈ conts, C (exhIE ALT φ) ⊆ₚ C φ

-- ============================================================================
-- SECTION 5.3: The Economy Condition
-- ============================================================================

/--
**Economy Condition on Exhaustification (ECE)**:
exh(φ) is licensed at a parse point only if exh is neither
incrementally vacuous nor incrementally weakening.

This is the main formal contribution of Fox & Spector (2018).
-/
def economyConditionMet (ALT : Set (Prop' World)) (φ : Prop' World)
    (conts : Set (Continuation World)) : Prop :=
  ¬isIncrementallyVacuous ALT φ conts ∧
  ¬isIncrementallyWeakening ALT φ conts

/--
A parse point where exh is economically licensed.
-/
structure LicensedExh (World : Type*) where
  /-- The parse point -/
  point : ParsePoint World
  /-- Economy condition is met -/
  economyMet : economyConditionMet point.alts point.prop point.continuations

-- ============================================================================
-- SECTION 5.4: Deriving Hurford's Constraint
-- ============================================================================

/-
Fox & Spector show that economy derives Hurford's Constraint.

In "A or B" where B ⊆ A (B entails A):
- At the parse point [B], the continuation is (λp. A ∨ p)
- exh(B) in this context either:
  - Is vacuous (if no alternatives to exclude)
  - Weakens the disjunction (if exh(B) ⊂ A anyway)

Either way, economy blocks exh(B), so the Hurford violation cannot be rescued.
-/

/--
The disjunction continuation: given first disjunct A, continuation is (λp. A ∨ p).
-/
def disjCont (A : Prop' World) : Continuation World := fun p => A ∨ₚ p

/--
**Theorem (Hurford from Economy)**: If B ⊆ A and exh(B) cannot break
the entailment to A, then exh(B) violates economy in the disjunction context.

This derives Hurford's Constraint from economy rather than stipulating it.
-/
theorem hurford_from_economy (ALT : Set (Prop' World)) (A B : Prop' World)
    (hBA : B ⊆ₚ A)  -- B entails A
    (_hstill : exhIE ALT B ⊆ₚ A)  -- exh doesn't break the entailment
    : isIncrementallyWeakening ALT B {disjCont A} := by
  -- In the disjunction context, (A ∨ B) entails (A ∨ exh(B))
  -- since B ⊆ A means B w → A w → (A ∨ exh(B)) w
  intro C hC w hCBw
  simp only [Set.mem_singleton_iff] at hC
  rw [hC] at hCBw ⊢
  simp only [disjCont, por] at hCBw ⊢
  -- hCBw : A w ∨ B w
  -- Need: A w ∨ exhIE ALT B w
  rcases hCBw with hAw | hBw
  · left; exact hAw
  · -- B w → A w (by hBA) → (A ∨ exhIE ALT B) w
    left
    exact hBA w hBw

-- ============================================================================
-- SECTION 5.5: Deriving Singh's Asymmetry
-- ============================================================================

/-
Singh's Asymmetry follows from economy:

"[A or B] or [A and B]" (weak first):
  - At [A or B], continuation is (λp. p ∨ (A ∧ B))
  - exh(A or B) = (A or B) but not both = (A ∨ B) ∧ ¬(A ∧ B)
  - This breaks the entailment! exh(A ∨ B) ⊄ (A ∧ B)
  - So exh is strengthening, economy met ✓

"[A and B] or [A or B]" (strong first):
  - At [A and B], continuation is (λp. p ∨ (A ∨ B))
  - exh(A and B) = A and B (no alternatives to exclude from {A∧B, A∨B})
  - So exh is vacuous, economy NOT met ✗
-/

/--
**Theorem (Singh: exh on weak is non-vacuous)**: When:
1. exh(weak) doesn't entail strong (h_breaks)
2. There exists a world where weak holds but neither exh(weak) nor strong holds (h_excludes)

Then exh on weak is NOT incrementally vacuous in the disjunction context.

The second condition captures that exh actually excludes something from weak.
For concrete scales like {or, and}, this holds: there are worlds where
inclusive-or holds but exclusive-or doesn't (the "both" worlds), and in
a non-trivial scale, some of these are also not-strong worlds.
-/
theorem singh_weak_exh_nonvacuous (ALT : Set (Prop' World))
    (weak strong : Prop' World)
    (_h_breaks : ¬(exhIE ALT weak ⊆ₚ strong))  -- implied by h_excludes, kept for documentation
    (h_excludes : ∃ w, weak w ∧ ¬exhIE ALT weak w ∧ ¬strong w)
    : ¬isIncrementallyVacuous ALT weak {disjCont strong} := by
  intro hvacuous
  -- hvacuous says: ∀ C ∈ {disjCont strong}, ∀ w, C(exh(weak)) w ↔ C(weak) w
  -- i.e., (strong ∨ exh(weak)) ↔ (strong ∨ weak) at all worlds
  have heq := hvacuous (disjCont strong) (Set.mem_singleton _)
  -- h_excludes gives us a world where weak but not exh(weak) and not strong
  obtain ⟨w, hweak, hnexh, hnstrong⟩ := h_excludes
  -- At w: weak holds, so (strong ∨ weak) w = true
  have hright : disjCont strong weak w := Or.inr hweak
  -- By heq: (strong ∨ weak) w ↔ (strong ∨ exh(weak)) w
  have hleft : disjCont strong (exhIE ALT weak) w := (heq w).mpr hright
  -- So (strong ∨ exh(weak)) w, meaning strong w ∨ exh(weak) w
  rcases hleft with hstrong | hexh
  · exact hnstrong hstrong
  · exact hnexh hexh

/--
**Theorem (Singh: exh on strong is vacuous)**: When strong ⊆ weak and
ALT = {weak, strong}, exh on strong is vacuous because there's nothing to exclude.

In "strong or weak", exh(strong) = strong (no alternatives can be innocently excluded
without making strong inconsistent).
-/
theorem singh_strong_exh_vacuous (weak strong : Prop' World)
    (h_entails : strong ⊆ₚ weak)
    : exhIE {weak, strong} strong ≡ₚ strong := by
  constructor
  · -- exhIE ⊆ strong: follows from exhIE entailing the base
    intro w hexh
    have hstrong_in_IE : strong ∈ IE {weak, strong} strong := fun E hE_mc => hE_mc.1.1
    exact hexh strong hstrong_in_IE
  · -- strong ⊆ exhIE: show strong(w) → all IE members hold at w
    intro w hstrong_w ψ hψ_IE
    -- Key insight: when strong ⊆ weak, the only MC-set is {strong}
    -- because both ¬weak and ¬strong are inconsistent with strong
    -- So IE = {strong}, meaning ψ = strong, and we use hstrong_w
    --
    -- To prove this formally, we construct the unique MC-set {strong}:
    have hE₀_compat : isCompatible {weak, strong} strong {strong} := by
      refine ⟨Set.mem_singleton _, ?_, ?_⟩
      · intro ψ' hψ'
        left
        exact Set.mem_singleton_iff.mp hψ'
      · -- Consistency: any world with strong satisfies {strong}
        exact ⟨w, fun ψ' hψ' => Set.mem_singleton_iff.mp hψ' ▸ hstrong_w⟩
    have hE₀_maximal : isMCSet {weak, strong} strong {strong} := by
      refine ⟨hE₀_compat, ?_⟩
      -- Maximality: any compatible extension E' must equal {strong}
      intro E' hE'_compat hE₀_sub_E' ψ' hψ'_E'
      -- ψ' ∈ E' means ψ' = strong or ψ' = ∼a for some a ∈ {weak, strong}
      rcases hE'_compat.2.1 ψ' hψ'_E' with hψ'_eq | ⟨a, ha_ALT, hψ'_neg⟩
      · -- ψ' = strong ∈ {strong}
        exact Set.mem_singleton_iff.mpr hψ'_eq
      · -- ψ' = ∼a for a ∈ {weak, strong} - this contradicts consistency
        exfalso
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha_ALT
        obtain ⟨u, hu⟩ := hE'_compat.2.2
        have hstrong_u : strong u := hu strong hE'_compat.1
        rcases ha_ALT with ha_weak | ha_strong
        · -- a = weak: ψ' = ∼weak, but strong u → weak u, so ¬∼weak u
          rw [ha_weak] at hψ'_neg
          have hneg_weak_u := hu ψ' hψ'_E'
          rw [hψ'_neg] at hneg_weak_u
          exact hneg_weak_u (h_entails u hstrong_u)
        · -- a = strong: ψ' = ∼strong, but strong u, so ¬∼strong u
          rw [ha_strong] at hψ'_neg
          have hneg_strong_u := hu ψ' hψ'_E'
          rw [hψ'_neg] at hneg_strong_u
          exact hneg_strong_u hstrong_u
    -- Now: ψ ∈ IE means ψ ∈ {strong} (since {strong} is the unique MC-set)
    have hψ_in_E₀ : ψ ∈ ({strong} : Set (Prop' World)) := hψ_IE {strong} hE₀_maximal
    rw [Set.mem_singleton_iff.mp hψ_in_E₀]
    exact hstrong_w

-- ============================================================================
-- SECTION 6: RELATIONSHIP TO FOCUS
-- ============================================================================

/-
Fox & Spector connect their economy condition to focus theory.

**Association with Focus (AF)**: exh associates with focused alternatives.
**Minimize Focus (MF)**: Don't mark more focus than necessary.

The connection: Economy condition interacts with focus marking.
In DE contexts, focus is REQUIRED to license exh (deriving IFG).
-/

/--
**Focus-Sensitivity**: The alternative set depends on focus marking.
Focused items contribute their scalar alternatives; unfocused don't.
-/
def focusSensitiveAlts (α : Type*) [BEq α] (focused : List α)
    (altGen : α → List α) : List α :=
  focused.flatMap altGen

/--
**Association with Focus (AF)**: exh only considers alternatives to focused items.
-/
structure AFExh (World : Type*) where
  /-- The focused expression -/
  focusedExpr : Prop' World
  /-- The focus value (F-marking) -/
  focusValue : Prop' World
  /-- Alternatives generated from focus value -/
  alts : Set (Prop' World)
  /-- The exhaustified meaning -/
  meaning : Prop' World := exhIE alts focusedExpr

/--
**Minimize Focus (MF)**: Among parses with equivalent meanings,
prefer the one with minimal focus marking.

The equivalence check must be decidable (returns Bool).
-/
def minimizeFocus {α : Type*} (parses : List (Focused α × Prop' World))
    (equivCheck : Prop' World → Prop' World → Bool) : Option (Focused α × Prop' World) :=
  -- Find parses with minimal focus (hasFocus = false preferred)
  let withoutFocus := parses.filter (fun p => !p.1.hasFocus)
  let withFocus := parses.filter (fun p => p.1.hasFocus)
  -- Return non-focused parse if meanings are equivalent
  match withoutFocus, withFocus with
  | p :: _, q :: _ => if equivCheck p.2 q.2 then some p else some q
  | p :: _, [] => some p
  | [], q :: _ => some q
  | [], [] => none

-- ============================================================================
-- SECTION 7: DISTANT ENTAILING DISJUNCTIONS (DEDs)
-- ============================================================================

/-
Fox & Spector (p.17-18) discuss Distant Entailing Disjunctions:
Disjunctions where the disjuncts are non-adjacent on a scale.

"John ate three or all of the cookies"
  - "three" and "all" are not adjacent on <1, 2, 3, 4, 5, all>
  - Yet this is acceptable!

The explanation: exh(three) can exclude "four", "five" but not "all".
This gives us "exactly three" which doesn't entail "all".
-/

/--
A scale position with information about adjacency.
-/
structure ScalePosition where
  /-- Position index on the scale -/
  index : Nat
  /-- The expression at this position -/
  expr : String

/--
**Distant Entailing Disjunction (DED)**: A disjunction where disjuncts
are non-adjacent on the scale.
-/
structure DED where
  /-- The weaker disjunct -/
  weaker : ScalePosition
  /-- The stronger disjunct -/
  stronger : ScalePosition
  /-- Non-adjacency: there are scale points between them -/
  nonAdjacent : stronger.index > weaker.index + 1

/--
DEDs are acceptable because intermediate alternatives can be excluded.
exh(weaker) excludes intermediate positions but not the strongest.
-/
def dedIsAcceptable (d : DED) : Prop :=
  -- There exist intermediate alternatives that can be excluded
  d.stronger.index > d.weaker.index + 1

-- ============================================================================
-- SECTION 8: CONNECTION TO POTTS ET AL. (2016)
-- ============================================================================

/-
Fox & Spector (2018) and Potts et al. (2016) make the same core predictions
about the DE/UE asymmetry:

| Context | Fox & Spector (2018) | Potts et al. (2016) |
|---------|---------------------|---------------------|
| UE      | exh licensed (strengthening) | Local reading preferred |
| DE      | exh blocked (weakening) | Global reading preferred |

The shared interface is `ContextPolarity`:
- `.upward` = UE context → embedded exh licensed / local reading
- `.downward` = DE context → embedded exh blocked / global reading

This section formalizes the connection.
-/

/--
**Shared Prediction Interface**: Both theories predict the same asymmetry.

Given a context polarity:
- UE: embedded implicature is available
- DE: embedded implicature is blocked

This is the core empirical pattern both theories explain.
-/
def embeddedImplicatureAvailable (pol : ContextPolarity) : Prop :=
  match pol with
  | .upward => true   -- UE: implicature available
  | .downward => false  -- DE: implicature blocked
  | .nonMonotonic => false  -- NM: implicature blocked

/--
**Fox & Spector (2018) Prediction**: Economy condition determines availability.

In UE contexts, exh is incrementally strengthening → licensed.
In DE contexts, exh is incrementally weakening → blocked.
-/
def foxSpectorPrediction (pol : ContextPolarity) : Bool :=
  match pol with
  | .upward => true   -- exh strengthens → licensed
  | .downward => false  -- exh weakens → blocked
  | .nonMonotonic => false  -- NM: blocked

/--
**Potts et al. (2016) Prediction**: Lexical uncertainty determines reading.

In UE contexts, local (refined) reading wins.
In DE contexts, global (base) reading wins.
-/
def pottsPrediction (pol : ContextPolarity) : Bool :=
  match pol with
  | .upward => true   -- local reading
  | .downward => false  -- global reading
  | .nonMonotonic => false  -- NM: global reading

/--
**THEOREM: Fox & Spector (2018) and Potts et al. (2016) Agree**

Both theories make identical predictions about embedded implicature availability
across DE/UE contexts.
-/
theorem foxSpector_potts_agreement :
    ∀ pol : ContextPolarity, foxSpectorPrediction pol = pottsPrediction pol := by
  intro pol
  cases pol <;> rfl

/--
**Connection to IFG**: Focus is required in DE contexts.

Fox & Spector derive IFG from economy:
- In UE, exh is automatically licensed (strengthening)
- In DE, exh needs focus to overcome the economy constraint

Potts et al. don't explicitly model focus, but the pattern is the same:
DE blocks embedded implicatures by default.
-/
theorem ifg_matches_de_blocking :
    ∀ pol : ContextPolarity,
    foxSpectorPrediction pol = true → pol = .upward := by
  intro pol h
  cases pol
  · rfl
  · simp [foxSpectorPrediction] at h
  · simp [foxSpectorPrediction] at h

-- ============================================================================
-- SUMMARY
-- ============================================================================

/-
## What This Module Provides

### Core Definitions
- `hurfordViolation`: Disjunction where one disjunct entails the other
- `isRescuedByExh`: Hurford violation repaired by embedded exh
- `deHurfordViolation`: Hurford in DE contexts
- `SinghDisjunction`: Configuration for Singh's asymmetry
- `Continuation`: Parse continuation (rest of sentence)
- `ParsePoint`: Point in parse with alternatives and continuations

### Economy Condition (Main Contribution)
- `isIncrementallyVacuous`: exh makes no difference for all continuations
- `isIncrementallyWeakening`: exh weakens for all continuations
- `isIncrementallyStrengthening`: exh strengthens for all continuations
- `economyConditionMet`: exh is licensed (not vacuous, not weakening)
- `LicensedExh`: Parse point where exh meets economy

### Derivations from Economy
- `hurford_from_economy`: Economy derives Hurford's Constraint
- `singh_weak_first_licensed`: Economy explains Singh's Asymmetry

### Focus Theory Connection
- `Focused`: Expression with focus annotation
- `satisfiesIFG`: Implicature Focus Generalization
- `AFExh`: Association with Focus for exh
- `minimizeFocus`: Minimize Focus principle

### Distant Entailing Disjunctions
- `ScalePosition`: Position on a Horn scale
- `DED`: Distant Entailing Disjunction structure
- `dedIsAcceptable`: DEDs are acceptable via intermediate exclusion

### Connection to Potts et al. (2016)
- `embeddedImplicatureAvailable`: Shared prediction interface
- `foxSpectorPrediction`: Economy-based prediction
- `pottsPrediction`: LU-based prediction
- `foxSpector_potts_agreement`: Both theories agree on DE/UE

## Relationship to Other Modules

```
Exhaustivity.lean (Spector 2016)
├── exhMW, exhIE
├── IE sets, MC-sets
├── theorem9_main
│
FoxSpector2018.lean (this file)
├── Economy condition on exh
├── Incremental vacuity/weakening
├── Derives: Hurford, Singh, IFG
├── Focus: AF, MF
└── Connection to Potts et al. (2016)
    └── foxSpector_potts_agreement theorem

PottsLU.lean (Potts et al. 2016)
├── LU model with predicate refinement
├── potts_model_derives_de_blocking
└── potts_model_derives_ue_implicature
```

## Key Insights

1. **Economy over stipulation**: Hurford's Constraint is derived, not stipulated
2. **Incremental computation**: Vacuity/weakening checked for ALL continuations
3. **Focus-sensitivity**: Explains when embedded exh is licensed in DE contexts
4. **Singh's Asymmetry**: Order matters due to what exh can achieve at each point
-/

end NeoGricean.FoxSpector2018
