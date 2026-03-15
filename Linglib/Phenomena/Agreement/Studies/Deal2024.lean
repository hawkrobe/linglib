import Linglib.Theories.Syntax.Minimalism.Core.PConstraint
import Linglib.Theories.Syntax.Minimalism.Core.CyclicAgree

/-!
# Interaction, Satisfaction, and the PCC @cite{deal-2024}

@cite{deal-2024} unifies the Person Case Constraint (PCC) typology under
a single Agree operation with two independently parameterized conditions:

- **Interaction (INT)**: what features the probe copies from a goal.
- **Satisfaction (SAT)**: what features halt the probe.

The probe encounters DO first ("DO preference"). If DO satisfies the
probe, it halts before reaching IO — creating a PCC violation when IO
requires licensing. If DO does not satisfy, the probe copies DO's
features and continues to IO. **Dynamic interaction** narrows the
probe's subsequent INT condition based on what was copied from DO.

## PCC Typology

Two parameters — satisfaction feature and dynamic interaction
configuration — derive five attested PCC varieties:

| SAT      | DynINT   | PCC type            | Licit |
|----------|----------|---------------------|-------|
| [PART]   | none     | Strong              | 3     |
| [SPKR]   | none     | Me-first            | 6     |
| none     | [PART]↑  | Weak                | 7     |
| [SPKR]   | [PART]↑  | Strictly descending | 5     |
| none     | none     | No PCC              | 9     |

## Bridge Results

This study file connects @cite{deal-2024}'s framework to both:

1. **@cite{pancheva-zubizarreta-2018}** (`PConstraint.lean`): exact match
   for Strong, Weak, and Me-first (all 9 cells); 7/9 match for Strictly
   Descending vs Ultra-strong (discrepancies on reflexive SAP combinations).
2. **@cite{bejar-rezac-2009}** (`CyclicAgree.lean`): probe satisfaction
   in Deal's sense corresponds to residue depletion in cyclic Agree —
   a DP satisfies SAT:[PART] iff it depletes the partial probe's residue.

-/

namespace Phenomena.Agreement.Studies.Deal2024

open Core.Prominence (PersonLevel)
open Minimalism (decomposePerson)
open Minimalism.PConstraint (pccLicit strongGrammar ultraStrongGrammar
  weakGrammar meFirstGrammar)
open Minimalism.CyclicAgree (activeResidue personSpec partialProbe)

-- ============================================================================
-- § 1: Person Features
-- ============================================================================

/-- Person features in @cite{deal-2024}'s geometry.

        [φ] → [PART] → [SPKR]
                     → [ADDR]

    Maps onto `DecomposedPerson`: [PART] = hasParticipant,
    [SPKR] = hasAuthor, [ADDR] = (person == .second). -/
inductive PersonFeature where
  | phi   -- [φ]: root feature, all DPs
  | part  -- [PART]: 1st and 2nd person
  | spkr  -- [SPKR]: 1st person only
  | addr  -- [ADDR]: 2nd person only
  deriving DecidableEq, BEq, Repr

/-- Does a DP of person level `p` bear feature `f`? -/
def dpBears (p : PersonLevel) (f : PersonFeature) : Bool :=
  match f with
  | .phi  => true
  | .part => (decomposePerson p).hasParticipant
  | .spkr => (decomposePerson p).hasAuthor
  | .addr => p == .second

-- ============================================================================
-- § 2: Feature Verification
-- ============================================================================

theorem first_bears :
    dpBears .first .phi = true ∧ dpBears .first .part = true ∧
    dpBears .first .spkr = true ∧ dpBears .first .addr = false := ⟨rfl, rfl, rfl, rfl⟩

theorem second_bears :
    dpBears .second .phi = true ∧ dpBears .second .part = true ∧
    dpBears .second .spkr = false ∧ dpBears .second .addr = true := ⟨rfl, rfl, rfl, rfl⟩

theorem third_bears :
    dpBears .third .phi = true ∧ dpBears .third .part = false ∧
    dpBears .third .spkr = false ∧ dpBears .third .addr = false := ⟨rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- § 3: Dynamic Interaction
-- ============================================================================

/-- Dynamic interaction configurations.

    After copying features from DO, the probe's subsequent INT condition
    may narrow. The `↑` notation indicates which features trigger narrowing.

    - `none_`: no dynamic narrowing
    - `part`: [PART]↑ — if DO bears [PART], INT narrows to [PART]
    - `spkr`: [SPKR]↑ — if DO bears [SPKR], INT narrows to [SPKR]
    - `partAndSpkr`: both [PART]↑ and [SPKR]↑ — [SPKR]↑ takes priority -/
inductive DynInteraction where
  | none_
  | part
  | spkr
  | partAndSpkr
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- § 4: DealGrammar
-- ============================================================================

/-- A grammar in @cite{deal-2024}'s framework.

    Two parameters determine the PCC type:
    - `satisfaction`: which feature, if present on DO, halts the probe.
      `none` means the probe is never satisfied by DO alone.
    - `dynInteraction`: which features trigger dynamic narrowing of the
      probe's INT condition after interacting with DO. -/
structure DealGrammar where
  satisfaction : Option PersonFeature
  dynInteraction : DynInteraction
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- § 5: Licitness
-- ============================================================================

/-- Is a clitic combination ⟨IO, DO⟩ licit under a Deal grammar?

    The probe encounters DO first ("DO preference"):

    1. If DO bears the SAT feature → probe satisfied → halts before IO →
       IO not licensed → **illicit**.
    2. Otherwise, the probe copies features from DO. Dynamic interaction
       may narrow the probe's subsequent INT condition.
    3. If narrowing occurred, IO must bear the narrowed feature to be
       visible to the probe. If IO is invisible → **illicit**.
    4. If no narrowing, IO is always visible → **licit**. -/
def isLicit (g : DealGrammar) (io do_ : PersonLevel) : Bool :=
  let doSatisfies := match g.satisfaction with
    | none => false
    | some f => dpBears do_ f
  if doSatisfies then false
  else
    let narrowedTo : Option PersonFeature := match g.dynInteraction with
      | .none_ => none
      | .part => if dpBears do_ .part then some .part else none
      | .spkr => if dpBears do_ .spkr then some .spkr else none
      | .partAndSpkr =>
          if dpBears do_ .spkr then some .spkr
          else if dpBears do_ .part then some .part
          else none
    match narrowedTo with
    | none => true
    | some f => dpBears io f

-- ============================================================================
-- § 6: Grammar Instances
-- ============================================================================

/-- **Strong PCC**: SAT:[PART], no dynamic interaction.
    DO bearing [PART] satisfies the probe → only 3P DOs survive. -/
def strong : DealGrammar := ⟨some .part, .none_⟩

/-- **Me-first PCC**: SAT:[SPKR], no dynamic interaction.
    Only 1P DOs satisfy the probe → only 1P DOs are banned. -/
def meFirst : DealGrammar := ⟨some .spkr, .none_⟩

/-- **Weak PCC**: no satisfaction, [PART]↑ dynamic interaction.
    The probe is never satisfied by DO, but copying [PART] from a SAP DO
    narrows the probe so it can only see [PART]-bearing IOs. -/
def weak : DealGrammar := ⟨none, .part⟩

/-- **Strictly descending PCC**: SAT:[SPKR], [PART]↑ dynamic interaction.
    1P DOs satisfy (banned); SAP DOs narrow the probe to require [PART]
    on IO. -/
def strictlyDescending : DealGrammar := ⟨some .spkr, .part⟩

/-- **No PCC**: no satisfaction, no dynamic interaction.
    The probe never halts at DO and never narrows. -/
def noPCC : DealGrammar := ⟨none, .none_⟩

-- ============================================================================
-- § 7: Verification — Strong PCC
-- ============================================================================

theorem strong_1_3 : isLicit strong .first .third = true := rfl
theorem strong_2_3 : isLicit strong .second .third = true := rfl
theorem strong_3_3 : isLicit strong .third .third = true := rfl
theorem strong_1_2 : isLicit strong .first .second = false := rfl
theorem strong_2_1 : isLicit strong .second .first = false := rfl
theorem strong_3_1 : isLicit strong .third .first = false := rfl
theorem strong_3_2 : isLicit strong .third .second = false := rfl
theorem strong_1_1 : isLicit strong .first .first = false := rfl
theorem strong_2_2 : isLicit strong .second .second = false := rfl

-- ============================================================================
-- § 8: Verification — Me-first PCC
-- ============================================================================

theorem mefirst_1_2 : isLicit meFirst .first .second = true := rfl
theorem mefirst_1_3 : isLicit meFirst .first .third = true := rfl
theorem mefirst_2_3 : isLicit meFirst .second .third = true := rfl
theorem mefirst_3_2 : isLicit meFirst .third .second = true := rfl
theorem mefirst_3_3 : isLicit meFirst .third .third = true := rfl
theorem mefirst_2_2 : isLicit meFirst .second .second = true := rfl
theorem mefirst_3_1 : isLicit meFirst .third .first = false := rfl
theorem mefirst_2_1 : isLicit meFirst .second .first = false := rfl
theorem mefirst_1_1 : isLicit meFirst .first .first = false := rfl

-- ============================================================================
-- § 9: Verification — Weak PCC
-- ============================================================================

theorem weak_1_3 : isLicit weak .first .third = true := rfl
theorem weak_2_3 : isLicit weak .second .third = true := rfl
theorem weak_3_3 : isLicit weak .third .third = true := rfl
theorem weak_1_2 : isLicit weak .first .second = true := rfl
theorem weak_2_1 : isLicit weak .second .first = true := rfl
theorem weak_1_1 : isLicit weak .first .first = true := rfl
theorem weak_2_2 : isLicit weak .second .second = true := rfl
theorem weak_3_1 : isLicit weak .third .first = false := rfl
theorem weak_3_2 : isLicit weak .third .second = false := rfl

-- ============================================================================
-- § 10: Verification — Strictly Descending PCC
-- ============================================================================

theorem sd_1_3 : isLicit strictlyDescending .first .third = true := rfl
theorem sd_2_3 : isLicit strictlyDescending .second .third = true := rfl
theorem sd_3_3 : isLicit strictlyDescending .third .third = true := rfl
/-- ⟨1,2⟩ is licit: 2P DO doesn't bear [SPKR] (no SAT); dynamic
    narrowing requires IO to bear [PART]; 1P bears [PART]. -/
theorem sd_1_2 : isLicit strictlyDescending .first .second = true := rfl
/-- ⟨2,2⟩ is licit: 2P DO lacks [SPKR]; narrowing requires [PART]
    on IO; 2P IO bears [PART]. -/
theorem sd_2_2 : isLicit strictlyDescending .second .second = true := rfl
theorem sd_2_1 : isLicit strictlyDescending .second .first = false := rfl
theorem sd_1_1 : isLicit strictlyDescending .first .first = false := rfl
theorem sd_3_1 : isLicit strictlyDescending .third .first = false := rfl
/-- ⟨3,2⟩ is illicit: 2P DO lacks [SPKR] but bears [PART]; narrowing
    requires [PART] on IO; 3P IO lacks [PART]. -/
theorem sd_3_2 : isLicit strictlyDescending .third .second = false := rfl

-- ============================================================================
-- § 11: Verification — No PCC
-- ============================================================================

theorem nopcc_all_licit (io do_ : PersonLevel) :
    isLicit noPCC io do_ = true := by
  cases io <;> cases do_ <;> rfl

-- ============================================================================
-- § 12: Licit Counts
-- ============================================================================

/-- Count licit combinations (out of 9 = 3×3). -/
def licitCount (g : DealGrammar) : Nat :=
  let ps : List PersonLevel := [.first, .second, .third]
  (ps.flatMap (λ io => ps.filter (λ do_ => isLicit g io do_))).length

theorem strong_licit_count : licitCount strong = 3 := by native_decide
theorem mefirst_licit_count : licitCount meFirst = 6 := by native_decide
theorem weak_licit_count : licitCount weak = 7 := by native_decide
theorem sd_licit_count : licitCount strictlyDescending = 5 := by native_decide
theorem nopcc_licit_count : licitCount noPCC = 9 := by native_decide

-- ============================================================================
-- § 13: Entailment Relations
-- ============================================================================

/-- Strong entails Me-first: anything licit under Strong is licit under
    Me-first. (Strong has SAT:[PART] ⊇ SAT:[SPKR].) -/
theorem strong_entails_mefirst (io do_ : PersonLevel) :
    isLicit strong io do_ = true → isLicit meFirst io do_ = true := by
  cases io <;> cases do_ <;> decide

/-- Strong entails Weak: anything licit under Strong is licit under Weak. -/
theorem strong_entails_weak (io do_ : PersonLevel) :
    isLicit strong io do_ = true → isLicit weak io do_ = true := by
  cases io <;> cases do_ <;> decide

-- ============================================================================
-- § 14: Bridge to PConstraint (@cite{pancheva-zubizarreta-2018})
-- ============================================================================

/-- Deal's Strong PCC matches P&Z's Strong PCC on all 9 cells. -/
theorem strong_matches_pz (io do_ : PersonLevel) :
    isLicit strong io do_ = pccLicit strongGrammar io do_ := by
  cases io <;> cases do_ <;> rfl

/-- Deal's Weak PCC matches P&Z's Weak PCC on all 9 cells. -/
theorem weak_matches_pz (io do_ : PersonLevel) :
    isLicit weak io do_ = pccLicit weakGrammar io do_ := by
  cases io <;> cases do_ <;> rfl

/-- Deal's Me-first PCC matches P&Z's Me-first PCC on all 9 cells. -/
theorem mefirst_matches_pz (io do_ : PersonLevel) :
    isLicit meFirst io do_ = pccLicit meFirstGrammar io do_ := by
  cases io <;> cases do_ <;> rfl

/-- Strictly descending agrees with ultra-strong on 7 of 9 cells.
    All non-reflexive-SAP combinations match. -/
theorem sd_matches_ultra_non_reflexive :
    isLicit strictlyDescending .first .second = pccLicit ultraStrongGrammar .first .second ∧
    isLicit strictlyDescending .first .third = pccLicit ultraStrongGrammar .first .third ∧
    isLicit strictlyDescending .second .first = pccLicit ultraStrongGrammar .second .first ∧
    isLicit strictlyDescending .second .third = pccLicit ultraStrongGrammar .second .third ∧
    isLicit strictlyDescending .third .first = pccLicit ultraStrongGrammar .third .first ∧
    isLicit strictlyDescending .third .second = pccLicit ultraStrongGrammar .third .second ∧
    isLicit strictlyDescending .third .third = pccLicit ultraStrongGrammar .third .third :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Strictly descending diverges from ultra-strong on ⟨1,1⟩:
    Deal bans it (1P DO satisfies SAT:[SPKR]), P&Z allows it
    (P-Primacy rescues: 1P IO is [+author]). -/
theorem sd_ultra_discrepancy_1_1 :
    isLicit strictlyDescending .first .first = false ∧
    pccLicit ultraStrongGrammar .first .first = true := ⟨rfl, rfl⟩

/-- Strictly descending diverges from ultra-strong on ⟨2,2⟩:
    Deal allows it (2P lacks [SPKR]; narrowing requires [PART];
    2P bears [PART]), P&Z bans it (P-Uniqueness violated, 2P
    lacks [+author] so no P-Primacy rescue). -/
theorem sd_ultra_discrepancy_2_2 :
    isLicit strictlyDescending .second .second = true ∧
    pccLicit ultraStrongGrammar .second .second = false := ⟨rfl, rfl⟩

-- ============================================================================
-- § 15: Bridge to CyclicAgree (@cite{bejar-rezac-2009})
-- ============================================================================

/-- Probe satisfaction in @cite{deal-2024}'s sense (SAT:[PART]) corresponds
    to residue depletion in @cite{bejar-rezac-2009}'s cyclic Agree.

    A DP fully checks the partial probe [uπ, uParticipant] iff it bears
    [PART]. In Deal's terms, such a DP satisfies a SAT:[PART] probe. In
    B&R's terms, it depletes the active residue to ∅.

    This bridges the two frameworks: "the probe is satisfied" (Deal) ↔
    "no active residue remains" (B&R). -/
theorem residue_empty_iff_bears_part (p : PersonLevel) :
    (activeResidue partialProbe (personSpec .standard p)).isEmpty =
    dpBears p .part := by
  cases p <;> native_decide

/-- The converse direction: a DP that does NOT bear [PART] leaves
    non-empty residue — the probe continues to the next cycle. -/
theorem residue_nonempty_iff_lacks_part (p : PersonLevel) :
    (!(activeResidue partialProbe (personSpec .standard p)).isEmpty) =
    !dpBears p .part := by
  cases p <;> native_decide

-- ============================================================================
-- § 16: Table (53) — SAT:[PART] Absorbs Dynamic Interaction
-- ============================================================================

/-- SAT:[PART] yields the Strong PCC regardless of dynamic interaction.

    This is the key insight of Table (53): when DO bears [PART], the probe
    is satisfied before any dynamic narrowing can take effect. Since [SPKR]
    and [ADDR] geometrically entail [PART], any DP that would trigger
    dynamic interaction via [SPKR]↑ or [PART]↑ also satisfies SAT:[PART].
    Therefore, dynamic interaction is irrelevant when SAT = [PART]. -/
theorem sat_part_absorbs_dynint (dyn : DynInteraction) (io do_ : PersonLevel) :
    isLicit ⟨some .part, dyn⟩ io do_ = isLicit strong io do_ := by
  cases dyn <;> cases io <;> cases do_ <;> rfl

-- ============================================================================
-- § 17: Extended Typology — [ADDR] Grammars (§6.1)
-- ============================================================================

/-- **You-first PCC** (predicted): SAT:[ADDR], no dynamic interaction.
    2P DOs satisfy the probe → ⟨IO, 2P DO⟩ is illicit.
    Predicted by @cite{deal-2024} §6.1 but not yet robustly attested. -/
def youFirst : DealGrammar := ⟨some .addr, .none_⟩

/-- **A-descending PCC** (predicted): SAT:[ADDR], [PART]↑ dynamic interaction.
    IO must outrank DO on the hierarchy 2 > 1 > 3.
    @cite{deal-2024} §6.1 notes hints of this pattern in Catalan and
    Italian speaker variation. -/
def aDescending : DealGrammar := ⟨some .addr, .part⟩

-- You-first: 2P DOs are banned; 1P and 3P DOs are free
theorem yf_1_3 : isLicit youFirst .first .third = true := rfl
theorem yf_2_3 : isLicit youFirst .second .third = true := rfl
theorem yf_3_3 : isLicit youFirst .third .third = true := rfl
theorem yf_2_1 : isLicit youFirst .second .first = true := rfl
theorem yf_1_1 : isLicit youFirst .first .first = true := rfl
theorem yf_3_1 : isLicit youFirst .third .first = true := rfl
theorem yf_1_2 : isLicit youFirst .first .second = false := rfl
theorem yf_3_2 : isLicit youFirst .third .second = false := rfl
theorem yf_2_2 : isLicit youFirst .second .second = false := rfl

-- A-descending: IO must outrank DO on 2 > 1 > 3
theorem ad_2_1 : isLicit aDescending .second .first = true := rfl
theorem ad_2_3 : isLicit aDescending .second .third = true := rfl
theorem ad_1_3 : isLicit aDescending .first .third = true := rfl
theorem ad_3_3 : isLicit aDescending .third .third = true := rfl
theorem ad_1_1 : isLicit aDescending .first .first = true := rfl
theorem ad_1_2 : isLicit aDescending .first .second = false := rfl
theorem ad_3_1 : isLicit aDescending .third .first = false := rfl
theorem ad_3_2 : isLicit aDescending .third .second = false := rfl
theorem ad_2_2 : isLicit aDescending .second .second = false := rfl

theorem yf_licit_count : licitCount youFirst = 6 := by native_decide
theorem ad_licit_count : licitCount aDescending = 5 := by native_decide

-- ============================================================================
-- § 18: Reverse PCC (§6.2)
-- ============================================================================

/-- Reverse PCC: the probe encounters IO before DO (IO preference).

    @cite{deal-2024} §6.2: in structures where IO moves to a position
    between v and DO, the probe encounters IO first. This reverses the
    PCC restriction — now IO features can satisfy/narrow the probe,
    and DO is the argument that may fail to be licensed.

    Attested in Shapsug Adyghe, varieties of Swiss German, Czech,
    and Slovenian. -/
def reverseLicit (g : DealGrammar) (io do_ : PersonLevel) : Bool :=
  isLicit g do_ io

/-- Reverse strictly descending PCC (Shapsug Adyghe): DO must outrank IO
    on the hierarchy 1 > 2 > 3 — the mirror image of forward SD. -/
def reverseSD : DealGrammar := strictlyDescending

theorem rsd_3_1_ok : reverseLicit reverseSD .third .first = true := rfl
theorem rsd_3_2_ok : reverseLicit reverseSD .third .second = true := rfl
theorem rsd_2_1_ok : reverseLicit reverseSD .second .first = true := rfl
theorem rsd_1_3_bad : reverseLicit reverseSD .first .third = false := rfl
theorem rsd_2_3_bad : reverseLicit reverseSD .second .third = false := rfl
theorem rsd_1_2_bad : reverseLicit reverseSD .first .second = false := rfl

-- ============================================================================
-- § 19: Characterization Theorems (Table (1), (2a-d))
-- ============================================================================

/-- Strong PCC (2a): DO must be 3P. Any IO is licit with a 3P DO;
    any SAP DO is illicit regardless of IO. -/
theorem strong_iff_3p_do (io do_ : PersonLevel) :
    isLicit strong io do_ = true ↔ do_ = .third := by
  cases io <;> cases do_ <;> simp [isLicit, strong, dpBears, decomposePerson]

/-- Weak PCC (2b): if IO is 3P, DO must be 3P. Equivalently: the only
    illicit cells are ⟨3P IO, SAP DO⟩. -/
theorem weak_illicit_iff (io do_ : PersonLevel) :
    isLicit weak io do_ = false ↔ io = .third ∧ do_.isSAP = true := by
  cases io <;> cases do_ <;> simp [isLicit, weak, dpBears, decomposePerson,
    PersonLevel.isSAP]

/-- Me-first PCC (2c): if 1P is present, it must be IO. Equivalently:
    DO cannot be 1P. -/
theorem mefirst_iff_not_1p_do (io do_ : PersonLevel) :
    isLicit meFirst io do_ = true ↔ dpBears do_ .spkr = false := by
  cases io <;> cases do_ <;> simp [isLicit, meFirst, dpBears, decomposePerson]

/-- Strictly descending PCC (2d): IO must outrank DO on 1 > 2 > 3.
    For the 6 non-diagonal cells, this is exactly the pattern.
    (Diagonal cells: ⟨3,3⟩ and ⟨2,2⟩ are licit; ⟨1,1⟩ is illicit
    because SAT:[SPKR] fires.) -/
theorem sd_off_diagonal_iff_outranks (io do_ : PersonLevel) (h : io ≠ do_) :
    isLicit strictlyDescending io do_ = true ↔ io.rank > do_.rank := by
  cases io <;> cases do_ <;> simp_all [isLicit, strictlyDescending, dpBears,
    decomposePerson, PersonLevel.rank]

-- ============================================================================
-- § 20: Additional Entailment
-- ============================================================================

/-- Strong entails strictly descending: anything licit under Strong
    is licit under SD. (Strong bans all SAP DOs; SD bans only 1P DOs
    and ⟨3P IO, SAP DO⟩.) -/
theorem strong_entails_sd (io do_ : PersonLevel) :
    isLicit strong io do_ = true → isLicit strictlyDescending io do_ = true := by
  cases io <;> cases do_ <;> decide

-- ============================================================================
-- § 21: Feature Geometry Grounding
-- ============================================================================

/-- `dpBears` is grounded in the shared feature geometry `decomposePerson`
    from PersonGeometry.lean. This makes the connection structural — Deal's
    person features are not independently stipulated but derived from the
    same privative geometry used by @cite{pancheva-zubizarreta-2018}'s
    `satisfiesProminence` and @cite{bejar-rezac-2009}'s `personSpec`. -/
theorem dpBears_grounded_in_decomposePerson (p : PersonLevel) :
    dpBears p .part = (decomposePerson p).hasParticipant ∧
    dpBears p .spkr = (decomposePerson p).hasAuthor := by
  cases p <;> exact ⟨rfl, rfl⟩

end Phenomena.Agreement.Studies.Deal2024
