import Linglib.Theories.Semantics.Dynamic.IntensionalCDRT.Operators

/-!
# Hofmann (2025): Anaphoric Accessibility with Flat Update

@cite{hofmann-2025}

Formalizes the core empirical and theoretical contributions of
@cite{hofmann-2025}'s unified account of anaphoric accessibility.

## Core Claim

Anaphoric accessibility is governed by **veridicality** — speaker
commitments about discourse referents — not by structural scope.
Indefinites under nonveridical operators introduce drefs globally
(flat update), and constraints on anaphora emerge from two principles:

1. **Local contextual entailment**: a dref's referent must exist
   throughout the pronoun's local context.
2. **Discourse consistency**: the speaker's commitment set must remain
   non-empty after the update.

## Phenomena Unified

The paper provides a single analysis for four previously disparate
patterns of anaphora to negated antecedents:

- **Double negation** (@cite{krahmer-muskens-1995}): "It's not the case
  that there isn't a bathroom. It's upstairs."
- **Bathroom disjunctions** (@cite{roberts-1989}): "Either there isn't
  a bathroom, or it's upstairs."
- **Disagreement** (@cite{hofmann-2019}): A: "There isn't a bathroom."
  B: "It's upstairs."
- **Modal subordination** (@cite{frank-1996}, @cite{roberts-1989}):
  "There isn't a bathroom. It would be upstairs."

## Theoretical Framework

The analysis is implemented in Intensional CDRT (ICDRT), extending
@cite{muskens-1996}'s Compositional DRT with intensionality and
propositional drefs, following @cite{stone-1999} and
@cite{brasoveanu-2006}'s flat-update approach.

## Structure of this file

1. **Empirical data** (§1): AccessDatum entries with felicity judgments
2. **Concrete model M₁** (§2): The 4-world model from the paper
3. **End-to-end derivations** (§3): Accessibility derived from ICDRT operators
4. **Accessibility predictions** (§4): The classification, verified against derivations
-/

namespace Phenomena.Anaphora.Studies.Hofmann2025

open Semantics.Dynamic.Core
open Semantics.Dynamic.IntensionalCDRT


-- ════════════════════════════════════════════════════════════════
-- § 1. Empirical Data
-- ════════════════════════════════════════════════════════════════

/-- Epistemic status of a discourse referent relative to a speaker. -/
inductive DrefStatus where
  | veridical | hypothetical | counterfactual
  deriving DecidableEq, Repr

/-- Veridicality of the anaphor's embedding context. -/
inductive AnaphorContext where
  | veridical | nonveridical
  deriving DecidableEq, Repr

/-- An empirical datum on anaphoric accessibility. -/
structure AccessDatum where
  label : String
  antecedentSentence : String
  anaphorSentence : String
  antecedentStatus : DrefStatus
  anaphorCtx : AnaphorContext
  felicitous : Bool
  source : String
  deriving Repr

-- § 1.1 Basic contrast

/-- (1a): "Mary owns a car. It is red." @cite{hofmann-2025} -/
def veridicalBasic : AccessDatum where
  label := "veridical-basic"
  antecedentSentence := "Mary owns a car."
  anaphorSentence := "It is red."
  antecedentStatus := .veridical
  anaphorCtx := .veridical
  felicitous := true
  source := "Hofmann 2025: (1a)"

/-- (1b): "Mary doesn't own a car. #It is red." @cite{hofmann-2025} -/
def negatedBasic : AccessDatum where
  label := "negated-basic"
  antecedentSentence := "Mary doesn't own a car."
  anaphorSentence := "#It is red."
  antecedentStatus := .counterfactual
  anaphorCtx := .veridical
  felicitous := false
  source := "Hofmann 2025: (1b)"

-- § 1.2 Four counterexamples to nested update

/-- (2a)/(42a): Double negation. @cite{krahmer-muskens-1995} -/
def doubleNegation : AccessDatum where
  label := "double-negation"
  antecedentSentence := "It's not true that there isn't a bathroom."
  anaphorSentence := "It is upstairs."
  antecedentStatus := .veridical
  anaphorCtx := .veridical
  felicitous := true
  source := "Krahmer & Muskens 1995: (5)"

/-- (2b)/(42b): Bathroom disjunction. @cite{roberts-1989} -/
def bathroomDisjunction : AccessDatum where
  label := "bathroom-disjunction"
  antecedentSentence := "Either there isn't a bathroom in this house"
  anaphorSentence := "or it's in a funny place."
  antecedentStatus := .counterfactual
  anaphorCtx := .nonveridical
  felicitous := true
  source := "Roberts 1989: (12)"

/-- (2c)/(42c): Disagreement. @cite{hofmann-2019} -/
def disagreement : AccessDatum where
  label := "disagreement"
  antecedentSentence := "A: There isn't a bathroom in this house."
  anaphorSentence := "B: (What are you talking about?) It is just in a weird place."
  antecedentStatus := .counterfactual
  anaphorCtx := .nonveridical
  felicitous := true
  source := "Hofmann 2019: (2d)"

/-- (2d)/(42d): Modal subordination. @cite{frank-1996} -/
def modalSubordination : AccessDatum where
  label := "modal-subordination"
  antecedentSentence := "Fred didn't buy a microwave oven."
  anaphorSentence := "He wouldn't know what to do with it."
  antecedentStatus := .counterfactual
  anaphorCtx := .nonveridical
  felicitous := true
  source := "Frank 1996: (8a)"

-- § 1.3 Veridical under negation

/-- (5a): Negated factive. @cite{karttunen-1976} -/
def negatedFactive : AccessDatum where
  label := "negated-factive"
  antecedentSentence := "Bill didn't realize that he had a dime."
  anaphorSentence := "It was in his pocket."
  antecedentStatus := .veridical
  anaphorCtx := .veridical
  felicitous := true
  source := "Karttunen 1976: (16)"

/-- (5b): Negative implicative. @cite{karttunen-1976} -/
def negativeImplicative : AccessDatum where
  label := "negative-implicative"
  antecedentSentence := "John forgot not to bring an umbrella."
  anaphorSentence := "...but we had no room for it."
  antecedentStatus := .veridical
  anaphorCtx := .veridical
  felicitous := true
  source := "Karttunen 1976: (14b)"

-- § 1.4 Anaphor context matters

def counterfactualVeridical : AccessDatum where
  label := "counterfactual-veridical"
  antecedentSentence := "Mary doesn't own a car."
  anaphorSentence := "#It is parked outside."
  antecedentStatus := .counterfactual
  anaphorCtx := .veridical
  felicitous := false
  source := "Hofmann 2025: (6a)"

def counterfactualModal : AccessDatum where
  label := "counterfactual-modal"
  antecedentSentence := "Mary doesn't own a car."
  anaphorSentence := "It would be parked outside."
  antecedentStatus := .counterfactual
  anaphorCtx := .nonveridical
  felicitous := true
  source := "Hofmann 2025: (6b)"

def counterfactualConcessive : AccessDatum where
  label := "counterfactual-concessive"
  antecedentSentence := "Mary doesn't own a car."
  anaphorSentence := "...even though Cole said that it's red."
  antecedentStatus := .counterfactual
  anaphorCtx := .nonveridical
  felicitous := true
  source := "Hofmann 2025: (6c)"

-- § 1.5 Modal subordination variants

def wolfIndicative : AccessDatum where
  label := "wolf-indicative"
  antecedentSentence := "A wolf might walk in."
  anaphorSentence := "#It is gray."
  antecedentStatus := .hypothetical
  anaphorCtx := .veridical
  felicitous := false
  source := "Roberts 1989: (11)"

def wolfWould : AccessDatum where
  label := "wolf-would"
  antecedentSentence := "A wolf might walk in."
  anaphorSentence := "It would eat you first."
  antecedentStatus := .hypothetical
  anaphorCtx := .nonveridical
  felicitous := true
  source := "Roberts 1989: (11)"

-- § 1.6 Infelicitous contrasts

def negationBlocks : AccessDatum where
  label := "negation-blocks"
  antecedentSentence := "There isn't a bathroom."
  anaphorSentence := "#It is upstairs."
  antecedentStatus := .counterfactual
  anaphorCtx := .veridical
  felicitous := false
  source := "Karttunen 1976"

def conjunctionBlocks : AccessDatum where
  label := "conjunction-blocks"
  antecedentSentence := "There's no bathroom"
  anaphorSentence := "and it's upstairs."
  antecedentStatus := .counterfactual
  anaphorCtx := .veridical
  felicitous := false
  source := "Contrast case"

def wrongOrderBathroom : AccessDatum where
  label := "wrong-order-bathroom"
  antecedentSentence := "Either it's upstairs"
  anaphorSentence := "or there's no bathroom."
  antecedentStatus := .counterfactual
  anaphorCtx := .veridical
  felicitous := false
  source := "Evans 1977, noted in Hofmann 2025"


-- ════════════════════════════════════════════════════════════════
-- § 2. Concrete Model M₁ (§3.3.2)
-- ════════════════════════════════════════════════════════════════

/-! ## Model M₁

The paper works through all derivations on a concrete model M₁ with
four possible worlds and a single bathroom entity b.

- `w_bu`: bathroom exists AND is upstairs
- `w_b`:  bathroom exists, NOT upstairs
- `w_u`:  no bathroom, but "upstairs" is true (vacuously; no entity)
- `w_0`:  no bathroom, "upstairs" is false

Entities: `{b}` (the bathroom). The universal falsifier ⋆ is modeled
by `Entity.star`.
-/

/-- Possible worlds in model M₁. -/
inductive BWorld where
  | w_bu | w_b | w_u | w_0
  deriving DecidableEq, Repr

/-- Entities in model M₁ (just the bathroom b). -/
inductive BEnt where
  | b
  deriving DecidableEq, Repr

open BWorld BEnt

/-- b is a bathroom in w_bu and w_b. -/
def isBathroom : BEnt → BWorld → Prop
  | .b, .w_bu => True | .b, .w_b => True | _, _ => False

/-- b is upstairs in w_bu and w_u. -/
def isUpstairs : BEnt → BWorld → Prop
  | .b, .w_bu => True | .b, .w_u => True | _, _ => False

-- Named variables

def p1 : PVar := ⟨0⟩       -- φ₁: matrix assertion content
def p2 : PVar := ⟨1⟩       -- φ₂: negated/embedded content
def p3 : PVar := ⟨2⟩       -- φ₃: anaphor's assertion / inner content
def p4 : PVar := ⟨3⟩       -- φ₄: disjunction's negative prejacent
def pDC_S : PVar := ⟨10⟩   -- φ_{DC_S}: speaker S's commitment set
def pDC_A : PVar := ⟨11⟩   -- φ_{DC_A}: speaker A (disagreement)
def pDC_B : PVar := ⟨12⟩   -- φ_{DC_B}: speaker B (disagreement)
def v1 : IVar := ⟨0⟩       -- v₁: individual dref for indefinite

/-- Individual dref assignment for the bathroom model: v₁ maps to b in
    bathroom worlds (w_bu, w_b), ⋆ elsewhere. All other variables map to ⋆. -/
def indivBathroom : IVar → BWorld → Entity BEnt
  | ⟨0⟩, .w_bu => .some .b
  | ⟨0⟩, .w_b  => .some .b
  | _, _        => .star


-- ════════════════════════════════════════════════════════════════
-- § 3. End-to-end Derivations
-- ════════════════════════════════════════════════════════════════

/-! ## Derivations from ICDRT operators

Each derivation constructs the output assignment j from the paper's
figures, defines the ICDRT update as a static relation (Definition 17),
then proves the accessibility prediction follows from Definition 38:
local contextual entailment + discourse consistency.
-/

-- ────────────────────────────────────────────────────────────────
-- § 3.1 Veridical antecedent + veridical anaphor (§3.3)
-- ────────────────────────────────────────────────────────────────

/-! ### "There is a bathroom. It is upstairs." (§3.3, Figures 5–6)

After (19a) + (30):
- φ₁(j) = φ_{DC_S}(j) = {w_bu, w_b}
- φ₃(j) = {w_bu}
- v maps w_bu → b, w_b → b, else ⋆
- v is veridical, discourse consistent, v entailed in φ₃
-/

/-- Output assignment after "There is a bathroom. It is upstairs." (Figure 6) -/
def j_veridical : ICDRTAssignment BWorld BEnt where
  prop | ⟨10⟩ => {w_bu, w_b}  -- pDC_S
       | ⟨0⟩  => {w_bu, w_b}  -- p1
       | ⟨2⟩  => {w_bu}        -- p3
       | _    => Set.univ
  indiv := indivBathroom

/-- The update (19a): `[φ₁, φ₁ : v | φ_{DC_S} ∈ φ₁, bathroom_{φ₁}(v)]` -/
def update_19a : ICDRTUpdate BWorld BEnt := λ i j =>
  multiVarUp [p1] [v1] i j ∧
  (∀ w, w ∈ j.prop p1 ↔ j.indiv v1 w ≠ .star) ∧
  decCondition pDC_S p1 j ∧
  dynPred isBathroom p1 v1 j

/-- The update (30): `[φ₃ | φ_{DC_S} ∈ φ₃, upstairs_{φ₃}(v)]` -/
def update_30 : ICDRTUpdate BWorld BEnt := λ i j =>
  multiVarUp [p3] [] i j ∧
  decCondition pDC_S p3 j ∧
  dynPred isUpstairs p3 v1 j

/-- v₁ is veridical at j_veridical: exists in all φ_{DC_S}-worlds. -/
theorem veridical_v_is_veridical :
    veridicalIndiv pDC_S v1 j_veridical := by
  intro w hw; cases w <;> simp_all [j_veridical, pDC_S, v1, indivBathroom]

/-- Discourse is consistent at j_veridical. -/
theorem veridical_consistent :
    (j_veridical.prop pDC_S).Nonempty :=
  ⟨w_bu, Or.inl rfl⟩

/-- v₁ is locally entailed in φ₃ at j_veridical. -/
theorem veridical_entailed_in_p3 :
    localEntailment p3 v1 j_veridical := by
  intro w hw; cases w <;> simp_all [j_veridical, p3, v1, indivBathroom]

/-- **Veridical anaphor is accessible** (Definition 38). -/
theorem veridical_anaphor_accessible :
    accessible p3 v1 pDC_S j_veridical :=
  ⟨veridical_entailed_in_p3, veridical_consistent⟩


-- ────────────────────────────────────────────────────────────────
-- § 3.2 Counterfactual antecedent + veridical anaphor fails (§3.4)
-- ────────────────────────────────────────────────────────────────

/-! ### "There isn't a bathroom. #It is upstairs." (§3.4, Figure 7)

After (19b):
- φ₂(j) = {w_bu, w_b}, φ₁(j) = {w_u, w_0} = φ̄₂
- φ_{DC_S}(j) = {w_u, w_0} ⊆ φ₁
- v maps w_bu → b, w_b → b, else ⋆
- v is counterfactual (⋆ in all DC worlds)

Attempting (30) requires φ₃ ⊆ φ₂ (subset requirement) AND
φ_{DC_S} ⊆ φ₃ (DEC). But φ_{DC_S} ∩ φ₂ = ∅ → contradiction.
-/

/-- Output assignment after "There isn't a bathroom" (Figure 7). -/
def j_counterfactual : ICDRTAssignment BWorld BEnt where
  prop | ⟨10⟩ => {w_u, w_0}     -- pDC_S
       | ⟨0⟩  => {w_u, w_0}     -- p1
       | ⟨1⟩  => {w_bu, w_b}    -- p2
       | _    => Set.univ
  indiv := indivBathroom

/-- v₁ is counterfactual at j_counterfactual. -/
theorem counterfactual_v_is_cf :
    counterfactualIndiv pDC_S v1 j_counterfactual := by
  intro w hw; cases w <;> simp_all [j_counterfactual, pDC_S, v1, indivBathroom]

/-- φ₁ is the complement of φ₂ at j_counterfactual (NOT condition). -/
theorem counterfactual_complement :
    isComplement p1 p2 j_counterfactual := by
  ext w; cases w <;> simp [j_counterfactual, p1, p2]

/-- **Veridical anaphor fails**: no consistent, locally-entailing
    extension of j_counterfactual with φ₃ exists.

    Any j extending j_counterfactual that satisfies both
    φ_{DC_S} ⊆ φ₃ (DEC) and φ₃ ⊆ φ₂ (subset requirement)
    must have φ_{DC_S} ⊆ φ₂, but φ_{DC_S} ∩ φ₂ = ∅. -/
theorem counterfactual_veridical_impossible
    (j : ICDRTAssignment BWorld BEnt)
    (h_extends : ∀ p, p ≠ p3 → j.prop p = j_counterfactual.prop p)
    (_h_indiv : j.indiv = j_counterfactual.indiv)
    (h_dec : decCondition pDC_S p3 j)
    (h_subset : subsetReq p3 p2 j)
    (_h_entailed : localEntailment p3 v1 j) :
    ¬(j.prop pDC_S).Nonempty := by
  intro ⟨w, hw⟩
  have hDC := h_extends pDC_S (by decide)
  have hp2 := h_extends p2 (by decide)
  have hw3 := h_dec hw
  have hw2 := h_subset hw3
  rw [hp2] at hw2; rw [hDC] at hw
  cases w <;> simp_all [j_counterfactual, pDC_S, p2]


-- ────────────────────────────────────────────────────────────────
-- § 3.3 Double negation (§4.1)
-- ────────────────────────────────────────────────────────────────

/-! ### "It's not the case that there isn't a bathroom." (§4.1, Figure 8)

DRS (43): `DEC_S(NOT(NOT(there is [a bathroom]^v)))`

Double complementation: φ₁ ≡ φ̄₂, φ₂ ≡ φ̄₃ ⟹ φ₁ = φ₃.
The dref v is introduced relative to φ₃ = φ₁ = {w_bu, w_b}.
Since φ_{DC_S} ⊆ φ₁ = φ₃, v is veridical.
-/

/-- Output after double negation (Figure 8). -/
def j_double_neg : ICDRTAssignment BWorld BEnt where
  prop | ⟨10⟩ => {w_bu, w_b}    -- pDC_S
       | ⟨0⟩  => {w_bu, w_b}    -- p1
       | ⟨1⟩  => {w_u, w_0}     -- p2
       | ⟨2⟩  => {w_bu, w_b}    -- p3
       | _    => Set.univ
  indiv := indivBathroom

/-- φ₁ = φ₃ via double complementation: the key structural result. -/
theorem double_neg_phi1_eq_phi3 :
    j_double_neg.prop p1 = j_double_neg.prop p3 := rfl

/-- NOT conditions hold: φ₁ ≡ φ̄₂ and φ₂ ≡ φ̄₃. -/
theorem double_neg_complement_conditions :
    isComplement p1 p2 j_double_neg ∧ isComplement p2 p3 j_double_neg := by
  constructor <;> ext w <;> cases w <;> simp [j_double_neg, p1, p2, p3]

/-- v₁ is veridical after double negation. -/
theorem double_neg_v_veridical :
    veridicalIndiv pDC_S v1 j_double_neg := by
  intro w hw; cases w <;> simp_all [j_double_neg, pDC_S, v1, indivBathroom]

/-- **Double negation: anaphora accessible.** -/
theorem double_neg_accessible :
    accessible p3 v1 pDC_S j_double_neg :=
  ⟨by intro w hw; cases w <;> simp_all [j_double_neg, p3, v1, indivBathroom],
   ⟨w_bu, Or.inl rfl⟩⟩


-- ────────────────────────────────────────────────────────────────
-- § 3.4 Bathroom disjunction (§4.2)
-- ────────────────────────────────────────────────────────────────

/-! ### "Either there isn't a bathroom, or it's upstairs." (§4.2, Figure 9)

DRS (44): φ₁ ≡ φ₂ ∪ φ₃ (disjunction). The second disjunct φ₃ = {w_bu}
is the local context for the pronoun. v exists in φ₃ (v(w_bu) = b ≠ ⋆).
Disjunction does NOT require overlap between disjunct propositions,
so φ₃ ⊆ φ₄ (bathroom worlds) is compatible with φ₂ (no-bathroom worlds)
being disjoint from φ₃.
-/

/-- Output after bathroom disjunction (Figure 9). -/
def j_bathroom_disj : ICDRTAssignment BWorld BEnt where
  prop | ⟨10⟩ => {w_bu, w_u, w_0}  -- pDC_S
       | ⟨0⟩  => {w_bu, w_u, w_0}  -- p1
       | ⟨1⟩  => {w_u, w_0}        -- p2
       | ⟨2⟩  => {w_bu}             -- p3
       | ⟨3⟩  => {w_bu, w_b}       -- p4
       | _    => Set.univ
  indiv := indivBathroom

/-- φ₁ = φ₂ ∪ φ₃ (disjunction condition). -/
theorem bathroom_disj_union :
    j_bathroom_disj.prop p1 = j_bathroom_disj.prop p2 ∪ j_bathroom_disj.prop p3 := by
  ext w; cases w <;> simp [j_bathroom_disj, p1, p2, p3]

/-- φ₂ = φ̄₄ (negation in first disjunct). -/
theorem bathroom_disj_complement :
    isComplement p2 p4 j_bathroom_disj := by
  ext w; cases w <;> simp [j_bathroom_disj, p2, p4]

/-- **Bathroom disjunction: anaphora accessible.**
    v₁ is locally entailed in φ₃ = {w_bu} and discourse is consistent. -/
theorem bathroom_disj_accessible :
    accessible p3 v1 pDC_S j_bathroom_disj :=
  ⟨by intro w hw; cases w <;> simp_all [j_bathroom_disj, p3, v1, indivBathroom],
   ⟨w_bu, Or.inl rfl⟩⟩


-- ────────────────────────────────────────────────────────────────
-- § 3.5 Disagreement (§4.3)
-- ────────────────────────────────────────────────────────────────

/-! ### A: "There isn't a bathroom." B: "It is upstairs." (§4.3, Figure 10)

This is the critical case that bilateral accounts (DN-DRT/BUS) CANNOT
handle (§5.1.1). ICDRT handles it because different speakers have
separate commitment sets.

(47) A's assertion: constrains φ_{DC_A}, introduces v counterfactually.
(48) B's assertion: constrains φ_{DC_B}, v is locally entailed in φ₃.
Both commitment sets nonempty → discourse consistent despite contradiction.
-/

/-- Output after disagreement (Figure 10). -/
def j_disagreement : ICDRTAssignment BWorld BEnt where
  prop | ⟨11⟩ => {w_u, w_0}     -- pDC_A
       | ⟨12⟩ => {w_bu}          -- pDC_B
       | ⟨0⟩  => {w_u, w_0}     -- p1
       | ⟨1⟩  => {w_bu, w_b}    -- p2
       | ⟨2⟩  => {w_bu}          -- p3
       | _    => Set.univ
  indiv := indivBathroom

/-- v₁ is counterfactual for A. -/
theorem disagreement_v_cf_for_A :
    counterfactualIndiv pDC_A v1 j_disagreement := by
  intro w hw; cases w <;> simp_all [j_disagreement, pDC_A, v1, indivBathroom]

/-- v₁ is veridical for B. -/
theorem disagreement_v_veridical_for_B :
    veridicalIndiv pDC_B v1 j_disagreement := by
  intro w hw; cases w <;> simp_all [j_disagreement, pDC_B, v1, indivBathroom]

/-- Both commitment sets are nonempty → discourse is consistent. -/
theorem disagreement_consistent :
    (j_disagreement.prop pDC_A).Nonempty ∧
    (j_disagreement.prop pDC_B).Nonempty :=
  ⟨⟨w_u, Or.inl rfl⟩, ⟨w_bu, rfl⟩⟩

/-- **Disagreement: anaphora accessible for B.**
    Impossible in bilateral accounts (§5.1.1) — they require a single
    negation swap, but here A and B have contradictory commitments. -/
theorem disagreement_accessible :
    accessible p3 v1 pDC_B j_disagreement :=
  ⟨by intro w hw; cases w <;> simp_all [j_disagreement, p3, v1, indivBathroom],
   ⟨w_bu, rfl⟩⟩


-- ────────────────────────────────────────────────────────────────
-- § 3.6 Modal subordination (§4.4)
-- ────────────────────────────────────────────────────────────────

/-! ### "There isn't a bathroom. Sue believes it's upstairs." (§4.4)

(51a): DEC_S(NOT(there is [a bathroom]^v))  — v counterfactual for S
(51b): DEC_S(Sue believes(it_v is upstairs)) — believe provides
        nonveridical local context φ₄ for the pronoun.

v is locally entailed in φ₄ ⊆ φ₂ (bathroom-worlds), which need not
overlap with φ_{DC_S}. Discourse consistent: φ_{DC_S} ≠ ∅.

**Simplification note**: The paper's §4.4 uses a richer model M₃ with
8 worlds, entities `{b, sue, S, ⋆}`, and a `believe` predicate
(Definition 50). We simplify to the 4-world M₁ model where the
attitude's embedded content φ₄ = {w_bu} is stipulated directly
rather than derived from Sue's doxastic state. This suffices to
verify the accessibility prediction (which depends only on φ₄ ⊆ φ₂
and DC consistency, not on how φ₄ is computed). A faithful M₃ model
would require adding `BWSue` (8 worlds), a `believe` relation, and
deriving φ₄ from `DOX(sue, φ₃)`.
-/

/-- Propositional variable for the attitude's embedded content. -/
def p4_modal : PVar := ⟨4⟩

/-- Output after "There isn't a bathroom. Sue believes it's upstairs." -/
def j_modal_sub : ICDRTAssignment BWorld BEnt where
  prop | ⟨10⟩ => {w_u, w_0}     -- pDC_S
       | ⟨0⟩  => {w_u, w_0}     -- p1
       | ⟨1⟩  => {w_bu, w_b}    -- p2
       | ⟨2⟩  => {w_u, w_0}     -- p3
       | ⟨4⟩  => {w_bu}          -- p4_modal
       | _    => Set.univ
  indiv := indivBathroom

/-- v₁ is counterfactual for the speaker. -/
theorem modal_sub_v_cf :
    counterfactualIndiv pDC_S v1 j_modal_sub := by
  intro w hw; cases w <;> simp_all [j_modal_sub, pDC_S, v1, indivBathroom]

/-- v₁ is locally entailed in the nonveridical context φ₄. -/
theorem modal_sub_entailed :
    localEntailment p4_modal v1 j_modal_sub := by
  intro w hw; cases w <;> simp_all [j_modal_sub, p4_modal, v1, indivBathroom]

/-- **Modal subordination: anaphora accessible in nonveridical context.**
    The pronoun resolves in Sue's doxastic state, not the speaker's
    commitment set. -/
theorem modal_sub_accessible :
    accessible p4_modal v1 pDC_S j_modal_sub :=
  ⟨modal_sub_entailed, ⟨w_u, Or.inl rfl⟩⟩


-- ════════════════════════════════════════════════════════════════
-- § 4. Accessibility Predictions (Derived)
-- ════════════════════════════════════════════════════════════════

/-! ## Accessibility generalization (7)

The paper's core empirical generalization (@cite{hofmann-2025}, (7)):

> A dref is accessible iff it is veridical OR the anaphor occurs in
> a nonveridical context.

This is encoded directly as `accessiblePred` and verified against each
phenomenon via ICDRT derivations with zero sorry:

- **Veridical** → accessible: `veridical_anaphor_accessible` (§3.1)
- **Counterfactual + veridical** → inaccessible: `counterfactual_veridical_impossible` (§3.2)
- **Double negation** → restores veridicality: `double_neg_accessible` (§3.3)
- **Counterfactual + nonveridical** → accessible: `bathroom_disj_accessible` (§3.4),
  `disagreement_accessible` (§3.5), `modal_sub_accessible` (§3.6)
-/

/-- The accessibility generalization (@cite{hofmann-2025}, (7)):
    accessible iff veridical OR nonveridical anaphor context. -/
def accessiblePred (status : DrefStatus) (ctx : AnaphorContext) : Bool :=
  match status, ctx with
  | .veridical,      _              => true
  | .hypothetical,    .nonveridical  => true
  | .counterfactual,  .nonveridical  => true
  | .hypothetical,    .veridical     => false
  | .counterfactual,  .veridical     => false


-- ════════════════════════════════════════════════════════════════
-- § 5. Per-datum Verification
-- ════════════════════════════════════════════════════════════════

theorem veridicalBasic_correct :
    accessiblePred veridicalBasic.antecedentStatus veridicalBasic.anaphorCtx
    = veridicalBasic.felicitous := rfl
theorem negatedBasic_correct :
    accessiblePred negatedBasic.antecedentStatus negatedBasic.anaphorCtx
    = negatedBasic.felicitous := rfl
theorem doubleNegation_correct :
    accessiblePred doubleNegation.antecedentStatus doubleNegation.anaphorCtx
    = doubleNegation.felicitous := rfl
theorem bathroomDisjunction_correct :
    accessiblePred bathroomDisjunction.antecedentStatus bathroomDisjunction.anaphorCtx
    = bathroomDisjunction.felicitous := rfl
theorem disagreement_correct :
    accessiblePred disagreement.antecedentStatus disagreement.anaphorCtx
    = disagreement.felicitous := rfl
theorem modalSubordination_correct :
    accessiblePred modalSubordination.antecedentStatus modalSubordination.anaphorCtx
    = modalSubordination.felicitous := rfl
theorem negatedFactive_correct :
    accessiblePred negatedFactive.antecedentStatus negatedFactive.anaphorCtx
    = negatedFactive.felicitous := rfl
theorem negativeImplicative_correct :
    accessiblePred negativeImplicative.antecedentStatus negativeImplicative.anaphorCtx
    = negativeImplicative.felicitous := rfl
theorem counterfactualVeridical_correct :
    accessiblePred counterfactualVeridical.antecedentStatus counterfactualVeridical.anaphorCtx
    = counterfactualVeridical.felicitous := rfl
theorem counterfactualModal_correct :
    accessiblePred counterfactualModal.antecedentStatus counterfactualModal.anaphorCtx
    = counterfactualModal.felicitous := rfl
theorem counterfactualConcessive_correct :
    accessiblePred counterfactualConcessive.antecedentStatus counterfactualConcessive.anaphorCtx
    = counterfactualConcessive.felicitous := rfl
theorem wolfIndicative_correct :
    accessiblePred wolfIndicative.antecedentStatus wolfIndicative.anaphorCtx
    = wolfIndicative.felicitous := rfl
theorem wolfWould_correct :
    accessiblePred wolfWould.antecedentStatus wolfWould.anaphorCtx
    = wolfWould.felicitous := rfl
theorem negationBlocks_correct :
    accessiblePred negationBlocks.antecedentStatus negationBlocks.anaphorCtx
    = negationBlocks.felicitous := rfl
theorem conjunctionBlocks_correct :
    accessiblePred conjunctionBlocks.antecedentStatus conjunctionBlocks.anaphorCtx
    = conjunctionBlocks.felicitous := rfl
theorem wrongOrderBathroom_correct :
    accessiblePred wrongOrderBathroom.antecedentStatus wrongOrderBathroom.anaphorCtx
    = wrongOrderBathroom.felicitous := rfl

/-- All 16 data points match the accessibility prediction. -/
theorem all_data_correct :
    accessiblePred veridicalBasic.antecedentStatus veridicalBasic.anaphorCtx = veridicalBasic.felicitous ∧
    accessiblePred negatedBasic.antecedentStatus negatedBasic.anaphorCtx = negatedBasic.felicitous ∧
    accessiblePred doubleNegation.antecedentStatus doubleNegation.anaphorCtx = doubleNegation.felicitous ∧
    accessiblePred bathroomDisjunction.antecedentStatus bathroomDisjunction.anaphorCtx = bathroomDisjunction.felicitous ∧
    accessiblePred disagreement.antecedentStatus disagreement.anaphorCtx = disagreement.felicitous ∧
    accessiblePred modalSubordination.antecedentStatus modalSubordination.anaphorCtx = modalSubordination.felicitous ∧
    accessiblePred negatedFactive.antecedentStatus negatedFactive.anaphorCtx = negatedFactive.felicitous ∧
    accessiblePred negativeImplicative.antecedentStatus negativeImplicative.anaphorCtx = negativeImplicative.felicitous ∧
    accessiblePred counterfactualVeridical.antecedentStatus counterfactualVeridical.anaphorCtx = counterfactualVeridical.felicitous ∧
    accessiblePred counterfactualModal.antecedentStatus counterfactualModal.anaphorCtx = counterfactualModal.felicitous ∧
    accessiblePred counterfactualConcessive.antecedentStatus counterfactualConcessive.anaphorCtx = counterfactualConcessive.felicitous ∧
    accessiblePred wolfIndicative.antecedentStatus wolfIndicative.anaphorCtx = wolfIndicative.felicitous ∧
    accessiblePred wolfWould.antecedentStatus wolfWould.anaphorCtx = wolfWould.felicitous ∧
    accessiblePred negationBlocks.antecedentStatus negationBlocks.anaphorCtx = negationBlocks.felicitous ∧
    accessiblePred conjunctionBlocks.antecedentStatus conjunctionBlocks.anaphorCtx = conjunctionBlocks.felicitous ∧
    accessiblePred wrongOrderBathroom.antecedentStatus wrongOrderBathroom.anaphorCtx = wrongOrderBathroom.felicitous :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩


end Phenomena.Anaphora.Studies.Hofmann2025
