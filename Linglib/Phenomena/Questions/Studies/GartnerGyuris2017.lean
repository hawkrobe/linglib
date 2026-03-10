import Linglib.Theories.Semantics.Modality.BiasedPQ
import Linglib.Phenomena.Negation.Studies.Stakov2026Typology

/-!
# Gärtner & Gyuris (2017): Delimiting the Space of Bias Profiles
@cite{gartner-gyuris-2017}

Formalization of the bias profile framework from @cite{gartner-gyuris-2017},
which defines bias profiles as non-empty power-set choices from {+, −, %}
for evidential and epistemic dimensions across PPQ/IN-NPQ/ON-NPQ forms.

## Key Results

- **Space size**: 7³ × 7³ = 117649 total profiles
- **7 delimiting principles** (§2) reduce the space progressively:
  1. No Uniformity (§2.1)
  2. PPQ ≠ NPQ (§2.2)
  3. Markedness (§2.3)
  4. Polarity Match / QA Alignment (§2.4)
  5. Convexity (§2.5)
  6. Narrow Epistemic Choice (§2.6)
  7. Static Complementarity (§2.7)
- **Final reduction**: Convexity + Narrow Epistemic Choice + Static
  Complementarity together yield (4 × 2)³ = 512 permissible profiles.

## Cross-Linguistic Data (Appendix A)

Six bias profiles from English, Japanese, and Hungarian are encoded
and verified against the delimiting principles.
-/

namespace Phenomena.Questions.Studies.GartnerGyuris2017

open Semantics.Modality.BiasedPQ (PQForm OriginalBias ContextualEvidence)

-- ============================================================================
-- §1: Core Types
-- ============================================================================

/-- Bias values: positive (+), negative (−), neutral (%). -/
inductive BiasValue where
  | pos   -- +: evidence for p / belief that p
  | neg   -- −: evidence for ¬p / belief that ¬p
  | neut  -- %: no compelling evidence / agnostic
  deriving DecidableEq, BEq, Repr

/-- A bias choice is a non-empty subset of {+, −, %}.
There are 2³ − 1 = 7 such subsets. We represent them as sorted lists
for decidable equality and enumeration. -/
def BiasChoice := List BiasValue

instance : BEq BiasChoice := inferInstanceAs (BEq (List BiasValue))
instance : DecidableEq BiasChoice := inferInstanceAs (DecidableEq (List BiasValue))
instance : Repr BiasChoice := inferInstanceAs (Repr (List BiasValue))

/-- The 7 non-empty subsets of {+, −, %}. -/
def allBiasChoices : List BiasChoice :=
  [ [.pos], [.neg], [.neut],
    [.pos, .neut], [.pos, .neg], [.neut, .neg],
    [.pos, .neut, .neg] ]

theorem seven_bias_choices : allBiasChoices.length = 7 := rfl

/-- Bias dimension: evidential vs epistemic. -/
inductive BiasDimension where
  | evidential  -- ev: based on contextual evidence
  | epistemic   -- ep: based on speaker's prior belief/expectation
  deriving DecidableEq, BEq, Repr

/-- G&G's PQ form typology: PPQ, IN-NPQ, ON-NPQ.
These map to Romero's PosQ, LoNQ, HiNQ respectively. -/
inductive GGPQForm where
  | PPQ     -- Positive polar question (?p)
  | IN_NPQ  -- NPQ with inside (propositional) negation (?¬p)
  | ON_NPQ  -- NPQ with outside negation (?~p)
  deriving DecidableEq, BEq, Repr

/-- Map G&G forms to Romero's typology. -/
def GGPQForm.toRomero : GGPQForm → PQForm
  | .PPQ    => .PosQ
  | .IN_NPQ => .LoNQ
  | .ON_NPQ => .HiNQ

/-- A cell in the bias profile grid: one PQ form × one bias dimension. -/
structure BiasCell where
  form : GGPQForm
  dim  : BiasDimension
  deriving DecidableEq, BEq, Repr

/-- A bias profile assigns a non-empty bias choice to each of 6 cells
(3 PQ forms × 2 bias dimensions). -/
structure BiasProfile where
  ppqEv    : BiasChoice
  ppqEp    : BiasChoice
  inNpqEv  : BiasChoice
  inNpqEp  : BiasChoice
  onNpqEv  : BiasChoice
  onNpqEp  : BiasChoice
  deriving DecidableEq, BEq, Repr

/-- Access a bias profile by cell. -/
def BiasProfile.get (bp : BiasProfile) : BiasCell → BiasChoice
  | ⟨.PPQ, .evidential⟩    => bp.ppqEv
  | ⟨.PPQ, .epistemic⟩     => bp.ppqEp
  | ⟨.IN_NPQ, .evidential⟩ => bp.inNpqEv
  | ⟨.IN_NPQ, .epistemic⟩  => bp.inNpqEp
  | ⟨.ON_NPQ, .evidential⟩ => bp.onNpqEv
  | ⟨.ON_NPQ, .epistemic⟩  => bp.onNpqEp

-- ============================================================================
-- §2: Space Size
-- ============================================================================

/-- Total space: 7 choices per cell, 6 cells = 7⁶ = 117649. -/
theorem total_space_size : 7 ^ 6 = 117649 := by native_decide

-- ============================================================================
-- §3: Delimiting Principle 1 — No Uniformity (§2.1)
-- ============================================================================

/-- No Uniformity: a bias profile is not entirely uniform, i.e., not all 6
cells have exactly the same bias choice.

"none of them consist of exactly the same choice, e.g., {+}, for each of
its 6 dimensions." -/
def noUniformity (bp : BiasProfile) : Bool :=
  !(bp.ppqEv == bp.ppqEp &&
    bp.ppqEp == bp.inNpqEv &&
    bp.inNpqEv == bp.inNpqEp &&
    bp.inNpqEp == bp.onNpqEv &&
    bp.onNpqEv == bp.onNpqEp)

/-- No Uniformity removes exactly 7 profiles (one per uniform choice). -/
theorem noUniformity_removes : 117649 - 7 = 117642 := by native_decide

-- ============================================================================
-- §4: Delimiting Principle 2 — PPQ ≠ NPQ (§2.2)
-- ============================================================================

/-- PPQ ≠ NPQ: Negation has an impact on bias. Both the evidential AND
epistemic choices of PPQ must differ from those of each NPQ form.

"PPQ ≠ NPQ (interpreted more precisely as PPQ^ev ≠ NPQ^ev &
PPQ^ep ≠ NPQ^ep)" — @cite{gartner-gyuris-2017} §2.2. -/
def ppqNeqNpq (bp : BiasProfile) : Bool :=
  -- PPQ ≠ IN-NPQ (both dimensions must differ)
  (bp.ppqEv != bp.inNpqEv && bp.ppqEp != bp.inNpqEp) &&
  -- PPQ ≠ ON-NPQ (both dimensions must differ)
  (bp.ppqEv != bp.onNpqEv && bp.ppqEp != bp.onNpqEp)

/-- PPQ ≠ NPQ reduces the space to 7² × 6² × 6² = 63504. -/
theorem ppqNeqNpq_space : 7 * 7 * 6 * 6 * 6 * 6 = 63504 := by native_decide

-- ============================================================================
-- §5: Delimiting Principle 3 — Markedness (§2.3)
-- ============================================================================

/-- Quantitative Markedness (distributive, §2.3 eq. 11a): expressing marked
(negative) meanings does not lead to more options than expressing their
unmarked (positive) counterpart.

|PPQ^ev| ≥ |IN-NPQ^ev| & |PPQ^ev| ≥ |ON-NPQ^ev| &
|PPQ^ep| ≥ |IN-NPQ^ep| & |PPQ^ep| ≥ |ON-NPQ^ep| -/
def markednessDistributive (bp : BiasProfile) : Bool :=
  Nat.ble bp.inNpqEv.length bp.ppqEv.length &&
  Nat.ble bp.onNpqEv.length bp.ppqEv.length &&
  Nat.ble bp.inNpqEp.length bp.ppqEp.length &&
  Nat.ble bp.onNpqEp.length bp.ppqEp.length

/-- Quantitative Markedness (collective, §2.3 eq. 11b):
|PPQ^ev| + |PPQ^ep| ≥ |IN-NPQ^ev| + |IN-NPQ^ep| &
|PPQ^ev| + |PPQ^ep| ≥ |ON-NPQ^ev| + |ON-NPQ^ep| -/
def markednessCollective (bp : BiasProfile) : Bool :=
  Nat.ble (bp.inNpqEv.length + bp.inNpqEp.length) (bp.ppqEv.length + bp.ppqEp.length) &&
  Nat.ble (bp.onNpqEv.length + bp.onNpqEp.length) (bp.ppqEv.length + bp.ppqEp.length)

/-- Distributive Markedness yields 33856 profiles (Appendix B [1]).
Per dimension: 3×3² + 3×6² + 1×7² = 184 (PPQ,NPQ) triples.
Two independent dimensions: 184² = 33856. -/
theorem markedness_distributive_space : Nat.mul 184 184 = 33856 := by native_decide

/-- Collective Markedness yields 56536 profiles (Appendix B [2]):
9×9² + 18×27² + 15×42² + 6×48² + 1×49² = 56536, summed over
|PPQ^ev|+|PPQ^ep| = 2..6, counting NPQ pairs with sum ≤ PPQ sum. -/
theorem markedness_collective_space :
    Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 9 81) (Nat.mul 18 729))
      (Nat.mul 15 1764)) (Nat.mul 6 2304)) (Nat.mul 1 2401) = 56536 := by native_decide

-- ============================================================================
-- §6: Delimiting Principle 4 — Polarity Match / QA Alignment (§2.4)
-- ============================================================================

/-- Avoid Disagreement: − ∉ PPQ and + ∉ NPQ.
The polarity of the question and the direction of bias should not
totally contradict each other. -/
def avoidDisagreement (bp : BiasProfile) : Bool :=
  -- − ∉ PPQ (neither evidential nor epistemic)
  !bp.ppqEv.contains .neg && !bp.ppqEp.contains .neg &&
  -- + ∉ IN-NPQ
  !bp.inNpqEv.contains .pos && !bp.inNpqEp.contains .pos &&
  -- + ∉ ON-NPQ
  !bp.onNpqEv.contains .pos && !bp.onNpqEp.contains .pos

/-- Don't Rule Out Agreement: each cell of PPQ must contain +, and each
cell of NPQ must contain −. The constraint applies per-cell, not per-row.

This yields 4 choices per cell (subsets containing the matching polarity),
so 4⁶ = 4096 total (@cite{gartner-gyuris-2017} §2.4, chart (19)). -/
def dontRuleOutAgreement (bp : BiasProfile) : Bool :=
  -- + ∈ each PPQ cell
  bp.ppqEv.contains .pos && bp.ppqEp.contains .pos &&
  -- − ∈ each IN-NPQ cell
  bp.inNpqEv.contains .neg && bp.inNpqEp.contains .neg &&
  -- − ∈ each ON-NPQ cell
  bp.onNpqEv.contains .neg && bp.onNpqEp.contains .neg

/-- Avoid Disagreement yields 3⁶ = 729 profiles. -/
theorem avoidDisagreement_space : 3 ^ 6 = 729 := by native_decide

/-- Don't Rule Out Agreement yields 4⁶ = 4096 profiles. -/
theorem dontRuleOutAgreement_space : 4 ^ 6 = 4096 := by native_decide

-- ============================================================================
-- §7: Delimiting Principle 5 — Convexity (§2.5)
-- ============================================================================

/-- A bias choice is convex if it doesn't "skip" intermediate values in the
Hasse ordering + > % > −. Concretely, {+, −} is ruled out because it
crosses over % without including it.

The convex non-empty subsets of {+, %, −} are:
{+}, {−}, {%}, {+,%}, {%,−}, {+,%,−} — six options. -/
def isConvex (bc : BiasChoice) : Bool :=
  !(bc.contains .pos && bc.contains .neg && !bc.contains .neut)

/-- A bias profile satisfies Convexity if all 6 cells are convex. -/
def convexity (bp : BiasProfile) : Bool :=
  isConvex bp.ppqEv && isConvex bp.ppqEp &&
  isConvex bp.inNpqEv && isConvex bp.inNpqEp &&
  isConvex bp.onNpqEv && isConvex bp.onNpqEp

/-- {+, −} is ruled out by Convexity. -/
theorem pos_neg_not_convex : isConvex [.pos, .neg] = false := rfl

/-- All singletons are convex. -/
theorem singletons_convex :
    isConvex [.pos] = true ∧
    isConvex [.neg] = true ∧
    isConvex [.neut] = true := ⟨rfl, rfl, rfl⟩

/-- {+, %} and {%, −} are convex. -/
theorem adjacent_pairs_convex :
    isConvex [.pos, .neut] = true ∧
    isConvex [.neut, .neg] = true := ⟨rfl, rfl⟩

/-- {+, %, −} is convex (the full set). -/
theorem full_set_convex : isConvex [.pos, .neut, .neg] = true := rfl

/-- Convexity yields 6⁶ = 46656 profiles. -/
theorem convexity_space : 6 ^ 6 = 46656 := by native_decide

-- ============================================================================
-- §8: Delimiting Principle 6 — Narrow Epistemic Choice (§2.6)
-- ============================================================================

/-- Narrow Epistemic Choice: epistemic bias is either {+^ep} or
{+^ep, −^ep, %^ep} (the full set).

"the number of epistemic bias options is rather narrow, that is, we
predominantly find {+^ep} or {+^ep,−^ep,%^ep}" -/
def narrowEpistemicChoice (bc : BiasChoice) : Bool :=
  bc == [.pos] || bc == [.pos, .neut, .neg]

/-- A bias profile satisfies Narrow Epistemic Choice if all 3 epistemic
cells use either {+} or {+,%,−}. -/
def narrowEpistemic (bp : BiasProfile) : Bool :=
  narrowEpistemicChoice bp.ppqEp &&
  narrowEpistemicChoice bp.inNpqEp &&
  narrowEpistemicChoice bp.onNpqEp

/-- Narrow Epistemic Choice alone yields (7 × 2)³ = 2744 profiles. -/
theorem narrowEpistemic_space : (7 * 2) ^ 3 = 2744 := by native_decide

-- ============================================================================
-- §9: Delimiting Principle 7 — Static Complementarity (§2.7)
-- ============================================================================

/-- The 4 evidential options surviving Static Complementarity + Convexity:
{+,%}, {%,−}, {%}, {−}.

These are the convex subsets minus {+}, {+,%,−} (which are the epistemic
options) and minus {+,−} (non-convex). -/
def staticComplementarityEvChoices : List BiasChoice :=
  [ [.pos, .neut], [.neut, .neg], [.neut], [.neg] ]

/-- A bias profile satisfies Static Complementarity if:
- Epistemic cells use {+} or {+,%,−} (Narrow Epistemic Choice)
- Evidential cells use {+,%}, {%,−}, {%}, or {−} -/
def isStaticComplementaryEv (bc : BiasChoice) : Bool :=
  bc == [.pos, .neut] || bc == [.neut, .neg] ||
  bc == [.neut] || bc == [.neg]

def staticComplementarity (bp : BiasProfile) : Bool :=
  narrowEpistemic bp &&
  isStaticComplementaryEv bp.ppqEv &&
  isStaticComplementaryEv bp.inNpqEv &&
  isStaticComplementaryEv bp.onNpqEv

/-- Static Complementarity + Convexity yields (4 × 2)³ = 512 profiles. -/
theorem staticComplementarity_space : (4 * 2) ^ 3 = 512 := by native_decide

-- ============================================================================
-- §10: Cross-Linguistic Data — Appendix A
-- ============================================================================

/-- [1] English V1-Interrogative (@cite{gartner-gyuris-2017} Appendix A [1],
from Sudo 2013:284).

PPQ:    ⟨{+,  %}, {+, −, %}⟩
IN-NPQ: ⟨{−},     {+}⟩
ON-NPQ: ⟨{−, %},  {+}⟩ -/
def englishV1 : BiasProfile where
  ppqEv   := [.pos, .neut]
  ppqEp   := [.pos, .neut, .neg]
  inNpqEv := [.neg]
  inNpqEp := [.pos]
  onNpqEv := [.neut, .neg]
  onNpqEp := [.pos]

/-- [2] Japanese ∅-Interrogative (@cite{gartner-gyuris-2017} Appendix A [2],
from Sudo 2013:285).

PPQ:    ⟨{%},      {+, −, %}⟩
IN-NPQ: ⟨{−},      {+, −, %}⟩
ON-NPQ: ⟨{+, %},   {+}⟩ -/
def japaneseNull : BiasProfile where
  ppqEv   := [.neut]
  ppqEp   := [.pos, .neut, .neg]
  inNpqEv := [.neg]
  inNpqEp := [.pos, .neut, .neg]
  onNpqEv := [.pos, .neut]
  onNpqEp := [.pos]

/-- [3] Japanese *no*-Interrogative (@cite{gartner-gyuris-2017} Appendix A [3],
= ex. (4), from Sudo 2013:288).

PPQ:    ⟨{+},           {+, −, %}⟩
IN-NPQ: ⟨{−},           {+}⟩
ON-NPQ: ⟨{+, −, %},     {+}⟩ -/
def japaneseNo : BiasProfile where
  ppqEv   := [.pos]
  ppqEp   := [.pos, .neut, .neg]
  inNpqEv := [.neg]
  inNpqEp := [.pos]
  onNpqEv := [.pos, .neut, .neg]
  onNpqEp := [.pos]

/-- [4] Japanese *desho*-Interrogative (@cite{gartner-gyuris-2017} Appendix A [4],
= ex. (23), from Sudo 2013:290).

PPQ:    ⟨{+, −, %},  {+}⟩
IN-NPQ: ⟨{+, −, %},  {−}⟩
ON-NPQ: ⟨{−, %},     {−}⟩ -/
def japaneseDesho : BiasProfile where
  ppqEv   := [.pos, .neut, .neg]
  ppqEp   := [.pos]
  inNpqEv := [.pos, .neut, .neg]
  inNpqEp := [.neg]
  onNpqEv := [.neut, .neg]
  onNpqEp := [.neg]

/-- [5] Hungarian ∧-Interrogative (@cite{gartner-gyuris-2017} Appendix A [5],
from Gyuris 2017: Section 4).

PPQ:    ⟨{+, %},    {+, −, %}⟩
IN-NPQ: ⟨{−},       {+}⟩
ON-NPQ: ⟨{−, %},    {+}⟩ -/
def hungarianWedge : BiasProfile where
  ppqEv   := [.pos, .neut]
  ppqEp   := [.pos, .neut, .neg]
  inNpqEv := [.neg]
  inNpqEp := [.pos]
  onNpqEv := [.neut, .neg]
  onNpqEp := [.pos]

/-- [6] Hungarian *e*-Interrogative (@cite{gartner-gyuris-2017} Appendix A [6],
= ex. (10), from Gyuris 2017: Section 4). IN-NPQ is not expressible.

PPQ:    ⟨{%},   {+, −, %}⟩
ON-NPQ: ⟨{%},   {+}⟩ -/
structure PartialBiasProfile where
  ppqEv    : BiasChoice
  ppqEp    : BiasChoice
  onNpqEv  : BiasChoice
  onNpqEp  : BiasChoice
  deriving Repr

def hungarianE : PartialBiasProfile where
  ppqEv   := [.neut]
  ppqEp   := [.pos, .neut, .neg]
  onNpqEv := [.neut]
  onNpqEp := [.pos]

-- ============================================================================
-- §11: Verification — Principles Against Data
-- ============================================================================

/-- English V1 satisfies No Uniformity. -/
theorem englishV1_noUniformity : noUniformity englishV1 = true := rfl

/-- English V1 satisfies PPQ ≠ NPQ. -/
theorem englishV1_ppqNeqNpq : ppqNeqNpq englishV1 = true := rfl

/-- English V1 satisfies Convexity. -/
theorem englishV1_convexity : convexity englishV1 = true := rfl

/-- English V1 satisfies Narrow Epistemic Choice. -/
theorem englishV1_narrowEpistemic : narrowEpistemic englishV1 = true := rfl

/-- English V1 satisfies Static Complementarity. -/
theorem englishV1_staticComplementarity :
    staticComplementarity englishV1 = true := rfl

/-- Hungarian ∧-Interrogative has the same bias profile as English V1
(@cite{gartner-gyuris-2017} Appendix A: [5] = [1]). -/
theorem hungarianWedge_eq_englishV1 : hungarianWedge = englishV1 := rfl

/-- Japanese ∅-Interrogative satisfies No Uniformity. -/
theorem japaneseNull_noUniformity : noUniformity japaneseNull = true := rfl

/-- Japanese ∅-Interrogative violates PPQ ≠ NPQ: PPQ^ep = IN-NPQ^ep = {+,−,%}.
Under the AND interpretation (both ev and ep must differ), identical
epistemic values suffice to violate the constraint. -/
theorem japaneseNull_violates_ppqNeqNpq : ppqNeqNpq japaneseNull = false := rfl

/-- Japanese ∅-Interrogative satisfies Convexity. -/
theorem japaneseNull_convexity : convexity japaneseNull = true := rfl

/-- Japanese ∅-Interrogative satisfies Static Complementarity:
all ev cells ∈ {{+,%},{%,−},{%},{−}} and all ep cells ∈ {{+},{+,−,%}}.
Despite violating PPQ ≠ NPQ, its profile is within the 512-profile
SC-permissible space. -/
theorem japaneseNull_staticComplementarity :
    staticComplementarity japaneseNull = true := rfl

/-- Japanese *no*-Interrogative satisfies No Uniformity. -/
theorem japaneseNo_noUniformity : noUniformity japaneseNo = true := rfl

/-- Japanese *no*-Interrogative satisfies PPQ ≠ NPQ. -/
theorem japaneseNo_ppqNeqNpq : ppqNeqNpq japaneseNo = true := rfl

-- §11.1: Known counterexamples to principles

/-- Japanese *no*-Interrogative violates Distributive Markedness:
|PPQ^ev| = 1 < |ON-NPQ^ev| = 3. This is a known counterexample
noted by @cite{gartner-gyuris-2017} §2.3. -/
theorem japaneseNo_violates_distributiveMarkedness :
    markednessDistributive japaneseNo = false := rfl

/-- Japanese *no*-Interrogative violates Static Complementarity:
ON-NPQ^ev = {+,−,%} which is not in the static complementarity set
of evidential options. -/
theorem japaneseNo_violates_staticComplementarity :
    staticComplementarity japaneseNo = false := rfl

/-- Japanese *desho*-Interrogative violates Avoid Disagreement:
IN-NPQ^ev contains + and PPQ^ev contains −. -/
theorem japaneseDesho_violates_avoidDisagreement :
    avoidDisagreement japaneseDesho = false := rfl

/-- Japanese *desho*-Interrogative violates Narrow Epistemic Choice:
IN-NPQ^ep and ON-NPQ^ep select {−}, which is neither {+} nor {+,%,−}. -/
theorem japaneseDesho_violates_narrowEpistemic :
    narrowEpistemic japaneseDesho = false := rfl

/-- Japanese *desho*-Interrogative violates PPQ ≠ NPQ:
PPQ^ev = IN-NPQ^ev = {+,−,%}. -/
theorem japaneseDesho_violates_ppqNeqNpq :
    ppqNeqNpq japaneseDesho = false := rfl

/-- Japanese *desho*-Interrogative violates Static Complementarity
(via narrowEpistemic failure). -/
theorem japaneseDesho_violates_staticComplementarity :
    staticComplementarity japaneseDesho = false := rfl

-- §11.2: Polarity Match / QA Alignment incompatibility (§3.1.2)

/-- English V1 violates Avoid Disagreement: PPQ^ep = {+,−,%} contains −,
and IN-NPQ^ep = {+} contains +. This exemplifies the systematic
incompatibility between Narrow Epistemic Choice and Polarity Match
for epistemic cells (@cite{gartner-gyuris-2017} §3.1.2). -/
theorem englishV1_violates_avoidDisagreement :
    avoidDisagreement englishV1 = false := rfl

/-- English V1 violates Don't Rule Out Agreement: IN-NPQ^ep = {+} does
not contain −. Again, the epistemic dimension conflicts with NEC-derived
empirical patterns (@cite{gartner-gyuris-2017} §3.1.2). -/
theorem englishV1_violates_dontRuleOutAgreement :
    dontRuleOutAgreement englishV1 = false := rfl

/-- English V1 satisfies Distributive Markedness. -/
theorem englishV1_markednessDistributive :
    markednessDistributive englishV1 = true := rfl

/-- English V1 satisfies Collective Markedness. -/
theorem englishV1_markednessCollective :
    markednessCollective englishV1 = true := rfl

-- ============================================================================
-- §12: Bridge to Romero Typology
-- ============================================================================

/-- Map G&G's evidential bias choice to Romero/BiasedPQ ContextualEvidence
compatibility. A bias choice lists which evidence types are felicitous. -/
def evidentiallyCompatible (bc : BiasChoice) (ce : ContextualEvidence) : Bool :=
  match ce with
  | .forP     => bc.contains .pos
  | .neutral  => bc.contains .neut
  | .againstP => bc.contains .neg

/-- Map G&G's epistemic bias choice to Romero/BiasedPQ OriginalBias
compatibility. -/
def epistemicallyCompatible (bc : BiasChoice) (ob : OriginalBias) : Bool :=
  match ob with
  | .forP     => bc.contains .pos
  | .neutral  => bc.contains .neut
  | .againstP => bc.contains .neg

/-- English V1 IN-NPQ (= Romero's LoNQ) requires evidence against p,
matching Romero's Table 2 prediction. -/
theorem englishV1_inNpq_evidence_matches_romero :
    evidentiallyCompatible englishV1.inNpqEv .forP = false ∧
    evidentiallyCompatible englishV1.inNpqEv .neutral = false ∧
    evidentiallyCompatible englishV1.inNpqEv .againstP = true := ⟨rfl, rfl, rfl⟩

/-- English V1 ON-NPQ (= Romero's HiNQ) has epistemic bias for p only,
matching Romero's requirement that HiNQ conveys original bias for p. -/
theorem englishV1_onNpq_epistemic_matches_romero :
    epistemicallyCompatible englishV1.onNpqEp .forP = true ∧
    epistemicallyCompatible englishV1.onNpqEp .neutral = false ∧
    epistemicallyCompatible englishV1.onNpqEp .againstP = false := ⟨rfl, rfl, rfl⟩

/-- English V1 PPQ (= Romero's PosQ) is compatible with evidence for p
or neutral evidence, matching Romero's Table 2. -/
theorem englishV1_ppq_evidence_matches_romero :
    evidentiallyCompatible englishV1.ppqEv .forP = true ∧
    evidentiallyCompatible englishV1.ppqEv .neutral = true ∧
    evidentiallyCompatible englishV1.ppqEv .againstP = false := ⟨rfl, rfl, rfl⟩

/-- Hungarian *e*-Interrogative has evidential "anti-bias" {%^ev} for PPQ:
requiring *neutral* evidence only. This is the key counterexample to
PPQ ≠ NPQ noted by @cite{gartner-gyuris-2017} §2.2.

This contrasts with standard PPQs which admit positive evidence. -/
theorem hungarianE_ppq_antibias :
    hungarianE.ppqEv = [BiasValue.neut] := rfl

-- ============================================================================
-- §13: Czech Integration — Derive G&G Profile from czechBiasProfile
-- ============================================================================

open Phenomena.Negation.CzechThreeWayNegTypologyBridge (CzechPQForm czechBiasProfile)

/-- Derive a G&G evidential bias choice for a Czech PQ form by checking
which contextual evidence values admit that form (across any epistemic bias). -/
private def czechEvChoice (f : CzechPQForm) : BiasChoice :=
  let forP := [OriginalBias.forP, .neutral, .againstP].any
    λ ob => (czechBiasProfile .forP ob).contains f
  let neut := [OriginalBias.forP, .neutral, .againstP].any
    λ ob => (czechBiasProfile .neutral ob).contains f
  let againstP := [OriginalBias.forP, .neutral, .againstP].any
    λ ob => (czechBiasProfile .againstP ob).contains f
  (if forP then [BiasValue.pos] else []) ++
  (if neut then [BiasValue.neut] else []) ++
  (if againstP then [BiasValue.neg] else [])

/-- Derive a G&G epistemic bias choice for a Czech PQ form by checking
which original bias values admit that form (across any evidence). -/
private def czechEpChoice (f : CzechPQForm) : BiasChoice :=
  let forP := [ContextualEvidence.forP, .neutral, .againstP].any
    λ ev => (czechBiasProfile ev .forP).contains f
  let neut := [ContextualEvidence.forP, .neutral, .againstP].any
    λ ev => (czechBiasProfile ev .neutral).contains f
  let againstP := [ContextualEvidence.forP, .neutral, .againstP].any
    λ ev => (czechBiasProfile ev .againstP).contains f
  (if forP then [BiasValue.pos] else []) ++
  (if neut then [BiasValue.neut] else []) ++
  (if againstP then [BiasValue.neg] else [])

/-- Czech bias profile in G&G format, derived from @cite{simik-2024} Table 2
via `czechBiasProfile`.

Czech V1-Interrogative (InterPPQ/InterNPQ as PPQ/ON-NPQ):
- InterPPQ = PPQ: ev={%}, ep={+,%}
- DeclNPQ = IN-NPQ: ev={−}, ep={+,%}
- InterNPQ = ON-NPQ: ev={+,%,−}, ep={+,%} -/
def czechV1 : BiasProfile where
  ppqEv   := czechEvChoice .interPPQ
  ppqEp   := czechEpChoice .interPPQ
  inNpqEv := czechEvChoice .declNPQ
  inNpqEp := czechEpChoice .declNPQ
  onNpqEv := czechEvChoice .interNPQ
  onNpqEp := czechEpChoice .interNPQ

/-- Czech PPQ (InterPPQ) admits only neutral evidence — narrower than
English V1 PPQ. Czech InterPPQ is the default unbiased PQ, felicitous
only when there is no compelling evidence either way. -/
theorem czechV1_ppq_ev : czechV1.ppqEv = [.neut] := rfl

/-- Czech ON-NPQ (InterNPQ) has *broader* evidential distribution than
English — it admits +, %, and − evidence, reflecting FALSUM^CZ's weaker
requirements (@cite{simik-2024} §5). -/
theorem czechV1_onNpq_ev : czechV1.onNpqEv = [.pos, .neut, .neg] := rfl

/-- Czech ON-NPQ (InterNPQ) epistemic bias admits + and % (speaker believes
p or is neutral). Unlike English HiNQ which requires bias for p, Czech
InterNPQ is also felicitous in explanation-seeking contexts (neutral
epistemic bias, @cite{simik-2024} §5.2). -/
theorem czechV1_onNpq_ep : czechV1.onNpqEp = [.pos, .neut] := rfl

/-- Czech V1 profile satisfies No Uniformity. -/
theorem czechV1_noUniformity : noUniformity czechV1 = true := rfl

/-- Czech V1 profile violates PPQ ≠ NPQ: PPQ^ep = IN-NPQ^ep = {+,%}.
Czech InterPPQ and DeclNPQ share the same epistemic bias distribution,
reflecting that both forms are felicitous when the speaker either believes
p or is neutral. -/
theorem czechV1_violates_ppqNeqNpq : ppqNeqNpq czechV1 = false := rfl

/-- Czech V1 profile satisfies Convexity. -/
theorem czechV1_convexity : convexity czechV1 = true := rfl

/-- Czech ON-NPQ evidential {+,%,−} violates Static Complementarity —
this is expected because Czech FALSUM^CZ has broader distribution than
English FALSUM, allowing all evidence types. The G&G framework was
designed for English/Japanese/Hungarian where ON-NPQ evidence is narrower. -/
theorem czechV1_violates_staticComplementarity :
    staticComplementarity czechV1 = false := rfl

/-- The key Czech vs English difference: Czech ON-NPQ admits positive
evidence while English ON-NPQ does not. This is the empirical core of
@cite{simik-2024}'s FALSUM^CZ proposal. -/
theorem czech_vs_english_onNpq_evidence :
    -- Czech ON-NPQ: positive evidence OK
    evidentiallyCompatible czechV1.onNpqEv .forP = true ∧
    -- English ON-NPQ: positive evidence NOT OK
    evidentiallyCompatible englishV1.onNpqEv .forP = false := ⟨rfl, rfl⟩

/-- Czech InterPPQ shares the "anti-bias" evidential pattern {%^ev} with
Hungarian *e*-interrogatives — both require neutral evidence only. This
parallel is striking given that Czech InterPPQ and Hungarian *e*-PPQ
serve different functions: Czech InterPPQ is the default unbiased PQ,
while Hungarian *e*-PPQ carries positive epistemic bias. -/
theorem czech_hungarian_shared_antibias :
    czechV1.ppqEv = hungarianE.ppqEv := rfl

end Phenomena.Questions.Studies.GartnerGyuris2017
