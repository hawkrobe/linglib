import Linglib.Features.Person.PersonCaseConstraint
import Linglib.Syntax.Minimalist.Agree.Cyclic
import Linglib.Studies.CoonKeine2021

/-!
# Interaction, Satisfaction, and the PCC [deal-2024]

[deal-2024] unifies the Person Case Constraint (PCC) typology under
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

This study file connects [deal-2024]'s framework to both:

1. **[pancheva-zubizarreta-2018]** (`PConstraint.lean`): exact match
   for Strong, Weak, and Me-first (all 9 cells); 7/9 match for Strictly
   Descending vs Ultra-strong (discrepancies on reflexive SAP combinations).
2. **[bejar-rezac-2009]** (`CyclicAgree.lean`): probe satisfaction
   in Deal's sense corresponds to residue depletion in cyclic Agree —
   a DP satisfies SAT:[PART] iff it depletes the partial probe's residue.
3. **[coon-keine-2021]** (`Studies/CoonKeine2021.lean`): strong and
   weak coincide with gluttony cell-for-cell; Me-First diverges
   exactly at 1>1 (`mefirst_diverges_from_gluttony`).

The licitness function is *run*, not tabulated: `runProbe` walks the
goal sequence with interaction, satisfaction, and dynamic narrowing
as state transitions (`step`), with `step_int_mono` ("dynamic
interaction only narrows"), `probe_vis_antitone` (its `Probe`-level
form: the state-indexed probe family `ProbeState.probe` only sees
less over time), and `step_of_satisfied` (a satisfied probe is
inert) as the probe-state laws; `isLicit` and the (1)-table theorems
are derived from runs.

-/

namespace Deal2024

open Minimalist (decomposePerson)
open PCC (IsLicit strongGrammar ultraStrongGrammar
  weakGrammar meFirstGrammar)
open Minimalist.CyclicAgree (activeResidue personSpec partialProbe)

-- ============================================================================
-- § 1: Person Features
-- ============================================================================

/-- Person features in [deal-2024]'s geometry.

        [φ] → [PART] → [SPKR]
                     → [ADDR]

    Maps onto `DecomposedPerson`: [PART] = hasParticipant,
    [SPKR] = hasAuthor, [ADDR] = (person == .second). -/
inductive PersonFeature where
  | phi   -- [φ]: root feature, all DPs
  | part  -- [PART]: 1st and 2nd person
  | spkr  -- [SPKR]: 1st person only
  | addr  -- [ADDR]: 2nd person only
  deriving DecidableEq, Repr

/-- Does a DP of person level `p` bear feature `f`? -/
def dpBears (p : Person) (f : PersonFeature) : Bool :=
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
  deriving DecidableEq, Repr

-- ============================================================================
-- § 4: DealGrammar
-- ============================================================================

/-- A grammar in [deal-2024]'s framework.

    Two parameters determine the PCC type:
    - `satisfaction`: which feature, if present on DO, halts the probe.
      `none` means the probe is never satisfied by DO alone.
    - `dynInteraction`: which features trigger dynamic narrowing of the
      probe's INT condition after interacting with DO. -/
structure DealGrammar where
  satisfaction : Option PersonFeature
  dynInteraction : DynInteraction
  deriving DecidableEq, Repr

-- ============================================================================
-- § 5: Licitness
-- ============================================================================

/-- Downward closure of a person feature in the (7) geometry (same
    convention as `Segment.below`, `Phi/Articulation.lean`): the
    features that bearing this one entails. -/
def PersonFeature.below : PersonFeature → List PersonFeature
  | .phi => [.phi]
  | .part => [.phi, .part]
  | .spkr => [.phi, .part, .spkr]
  | .addr => [.phi, .part, .addr]

/-- The entailment order: `s ≤ t` iff bearing `t` entails bearing
    `s`; [φ] is bottom, [SPKR]/[ADDR] maximal. "More specific" =
    larger. -/
instance : PartialOrder PersonFeature where
  le s t := s ∈ t.below
  le_refl s := by cases s <;> decide
  le_trans s t u hst htu := by
    revert hst htu; cases s <;> cases t <;> cases u <;> decide
  le_antisymm s t hst hts := by
    revert hst hts; cases s <;> cases t <;> decide

instance : DecidableRel (α := PersonFeature) (· ≤ ·) := fun s t =>
  inferInstanceAs (Decidable (s ∈ t.below))

/-- The probe's state during its walk over the goal sequence
    (her (8), (44)–(47)): the current interaction condition, the
    satisfaction flag, and the positions of the goals interacted
    with. -/
structure ProbeState where
  int : PersonFeature
  satisfied : Bool
  agreed : List Nat
  deriving DecidableEq, Repr

/-- Initial state: [INT:φ], unsatisfied, nothing agreed. -/
def ProbeState.initial : ProbeState := ⟨.phi, false, []⟩

/-- The static `Probe` a state denotes: visibility = bearing the
    current INT condition. Deal's dynamic probe is a *state-indexed
    family* of static probes — `step`'s interaction check is
    literally `st.probe.vis`. -/
def ProbeState.probe (st : ProbeState) : Minimalist.Probe Person :=
  .ofVis (fun p => dpBears p st.int)

/-- The dynamic-interaction target a goal contributes (her §5):
    `[F]↑` narrows INT to [F] when the interacted goal bears [F];
    in the combined setting `[SPKR]↑` takes priority. -/
def narrowTarget (d : DynInteraction) (p : Person) : Option PersonFeature :=
  match d with
  | .none_ => none
  | .part => if dpBears p .part then some .part else none
  | .spkr => if dpBears p .spkr then some .spkr else none
  | .partAndSpkr =>
      if dpBears p .spkr then some .spkr
      else if dpBears p .part then some .part
      else none

/-- One step of the probe's walk: a satisfied probe is inert
    (her (8b)); otherwise a goal bearing the current INT is
    interacted with (its position recorded), satisfaction is checked
    against the goal, and dynamic interaction narrows INT (her
    (44)–(47)). The narrowing is guarded to be specificity-increasing
    — vacuously for every grammar of the paper, where a run has at
    most one narrowing target; the guard makes `step_int_mono` true
    by construction. -/
def step (g : DealGrammar) (st : ProbeState) (t : Person × Nat) : ProbeState :=
  if st.satisfied then st
  else if st.probe.vis t.1 then
    { int :=
        match narrowTarget g.dynInteraction t.1 with
        | some f => if st.int ≤ f then f else st.int
        | none => st.int
      satisfied :=
        match g.satisfaction with
        | some f => dpBears t.1 f
        | none => false
      agreed := st.agreed ++ [t.2] }
  else st

/-- Run the probe over a goal sequence, in interaction order. -/
def runProbe (g : DealGrammar) (goals : List Person) : ProbeState :=
  goals.zipIdx.foldl (step g) .initial

/-- "Dynamic interaction only narrows": along any run, the
    interaction condition only becomes more specific — the
    probe-state law that makes [deal-2024]'s INT a well-behaved
    object. -/
theorem step_int_mono (g : DealGrammar) (st : ProbeState)
    (t : Person × Nat) : st.int ≤ (step g st t).int := by
  unfold step
  split
  · exact le_refl _
  · split
    · simp only
      split
      · split
        · assumption
        · exact le_refl _
      · exact le_refl _
    · exact le_refl _

/-- Bearing a more specific feature entails bearing a less specific
    one — the (7) geometry, as monotonicity of `dpBears`. -/
theorem dpBears_antitone {f g : PersonFeature} (hfg : f ≤ g) (p : Person)
    (h : dpBears p g = true) : dpBears p f = true := by
  revert hfg h
  cases f <;> cases g <;> cases p <;> decide

/-- The state-indexed probe family only narrows: anything visible to
    a later state's probe was visible to an earlier state's —
    `step_int_mono` at the `Probe` level. -/
theorem probe_vis_antitone (g : DealGrammar) (st : ProbeState)
    (t : Person × Nat) (a : Person)
    (h : ((step g st t).probe).vis a = true) : st.probe.vis a = true :=
  dpBears_antitone (step_int_mono g st t) a h

/-- Narrowing the probe cannot gain a goal: if the later (narrower)
    state's probe still finds one, so did the earlier — the outcome-level
    form of "interaction only narrows", from the substrate's
    `Probe.outcome_valued_mono` fed by `probe_vis_antitone`. -/
theorem probe_outcome_antitone (g : DealGrammar) (st : ProbeState)
    (t : Person × Nat) (goals : List Person)
    (h : ((step g st t).probe).outcome goals = .valued) :
    st.probe.outcome goals = .valued :=
  Minimalist.Probe.outcome_valued_mono (fun a _ ha => probe_vis_antitone g st t a ha) h

/-- A satisfied probe is inert: satisfaction halts all further
    interaction (her (8b)). -/
theorem step_of_satisfied (g : DealGrammar) (st : ProbeState)
    (t : Person × Nat) (h : st.satisfied = true) : step g st t = st := by
  unfold step
  rw [if_pos h]

/-- Is a clitic combination ⟨IO, DO⟩ licit under a Deal grammar?
    Cliticization of both objects requires Agree with both (her §4),
    and the probe interacts with the DO first (DO preference, her
    (17), on either the high- or the low-probe structure): licit iff
    the run over ⟨DO, IO⟩ interacts with both goals. The PCC
    varieties are now *derived* by running the probe, not read off a
    table. -/
def isLicit (g : DealGrammar) (io do_ : Person) : Bool :=
  (runProbe g [do_, io]).agreed.length == 2

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

theorem nopcc_all_licit (io do_ : Person) :
    isLicit noPCC io do_ = true := by
  cases io <;> cases do_ <;> rfl

-- ============================================================================
-- § 12: Licit Counts
-- ============================================================================

/-- Count licit combinations (out of 9 = 3×3). -/
def licitCount (g : DealGrammar) : Nat :=
  let ps : List Person := [.first, .second, .third]
  (ps.flatMap (λ io => ps.filter (λ do_ => isLicit g io do_))).length

theorem strong_licit_count : licitCount strong = 3 := by decide
theorem mefirst_licit_count : licitCount meFirst = 6 := by decide
theorem weak_licit_count : licitCount weak = 7 := by decide
theorem sd_licit_count : licitCount strictlyDescending = 5 := by decide
theorem nopcc_licit_count : licitCount noPCC = 9 := by decide

-- ============================================================================
-- § 13: Entailment Relations
-- ============================================================================

/-- Strong entails Me-first: anything licit under Strong is licit under
    Me-first. (Strong has SAT:[PART] ⊇ SAT:[SPKR].) -/
theorem strong_entails_mefirst (io do_ : Person) :
    isLicit strong io do_ = true → isLicit meFirst io do_ = true := by
  cases io <;> cases do_ <;> decide

/-- Strong entails Weak: anything licit under Strong is licit under Weak. -/
theorem strong_entails_weak (io do_ : Person) :
    isLicit strong io do_ = true → isLicit weak io do_ = true := by
  cases io <;> cases do_ <;> decide

-- ============================================================================
-- § 14: Bridge to PConstraint ([pancheva-zubizarreta-2018])
-- ============================================================================

/-- Deal's Strong PCC matches P&Z's Strong PCC on all 9 cells. -/
theorem strong_matches_pz (io do_ : Person) :
    isLicit strong io do_ = true ↔ IsLicit strongGrammar io do_ := by
  cases io <;> cases do_ <;> decide

/-- Deal's Weak PCC matches P&Z's Weak PCC on all 9 cells. -/
theorem weak_matches_pz (io do_ : Person) :
    isLicit weak io do_ = true ↔ IsLicit weakGrammar io do_ := by
  cases io <;> cases do_ <;> decide

/-- Deal's Me-first PCC matches P&Z's Me-first PCC on all 9 cells. -/
theorem mefirst_matches_pz (io do_ : Person) :
    isLicit meFirst io do_ = true ↔ IsLicit meFirstGrammar io do_ := by
  cases io <;> cases do_ <;> decide

/-- Strictly descending agrees with ultra-strong on 7 of 9 cells.
    All non-reflexive-SAP combinations match. -/
theorem sd_matches_ultra_non_reflexive :
    (isLicit strictlyDescending .first .second = true ↔ IsLicit ultraStrongGrammar .first .second) ∧
    (isLicit strictlyDescending .first .third = true ↔ IsLicit ultraStrongGrammar .first .third) ∧
    (isLicit strictlyDescending .second .first = true ↔ IsLicit ultraStrongGrammar .second .first) ∧
    (isLicit strictlyDescending .second .third = true ↔ IsLicit ultraStrongGrammar .second .third) ∧
    (isLicit strictlyDescending .third .first = true ↔ IsLicit ultraStrongGrammar .third .first) ∧
    (isLicit strictlyDescending .third .second = true ↔ IsLicit ultraStrongGrammar .third .second) ∧
    (isLicit strictlyDescending .third .third = true ↔ IsLicit ultraStrongGrammar .third .third) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- Strictly descending diverges from ultra-strong on ⟨1,1⟩:
    Deal bans it (1P DO satisfies SAT:[SPKR]), P&Z allows it
    (P-Primacy rescues: 1P IO is [+author]). -/
theorem sd_ultra_discrepancy_1_1 :
    isLicit strictlyDescending .first .first = false ∧
    IsLicit ultraStrongGrammar .first .first := ⟨rfl, by decide⟩

/-- Strictly descending diverges from ultra-strong on ⟨2,2⟩:
    Deal allows it (2P lacks [SPKR]; narrowing requires [PART];
    2P bears [PART]), P&Z bans it (P-Uniqueness violated, 2P
    lacks [+author] so no P-Primacy rescue). -/
theorem sd_ultra_discrepancy_2_2 :
    isLicit strictlyDescending .second .second = true ∧
    ¬ IsLicit ultraStrongGrammar .second .second := ⟨rfl, by decide⟩

-- ============================================================================
-- § 15: Bridge to CyclicAgree ([bejar-rezac-2009])
-- ============================================================================

/-- Probe satisfaction in [deal-2024]'s sense (SAT:[PART]) corresponds
    to residue depletion in [bejar-rezac-2009]'s cyclic Agree.

    A DP fully checks the partial probe [uπ, uParticipant] iff it bears
    [PART]. In Deal's terms, such a DP satisfies a SAT:[PART] probe. In
    B&R's terms, it depletes the active residue to ∅.

    This bridges the two frameworks: "the probe is satisfied" (Deal) ↔
    "no active residue remains" (B&R). -/
theorem residue_empty_iff_bears_part (p : Person) :
    (activeResidue partialProbe (personSpec .standard p)).isEmpty =
    dpBears p .part := by
  cases p <;> native_decide

/-- The converse direction: a DP that does NOT bear [PART] leaves
    non-empty residue — the probe continues to the next cycle. -/
theorem residue_nonempty_iff_lacks_part (p : Person) :
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
theorem sat_part_absorbs_dynint (dyn : DynInteraction) (io do_ : Person) :
    isLicit ⟨some .part, dyn⟩ io do_ = isLicit strong io do_ := by
  cases dyn <;> cases io <;> cases do_ <;> rfl

-- ============================================================================
-- § 17: Extended Typology — [ADDR] Grammars (§6.1)
-- ============================================================================

/-- **You-first PCC** (predicted): SAT:[ADDR], no dynamic interaction.
    2P DOs satisfy the probe → ⟨IO, 2P DO⟩ is illicit.
    Predicted by [deal-2024] §6.1 but not yet robustly attested. -/
def youFirst : DealGrammar := ⟨some .addr, .none_⟩

/-- **A-descending PCC** (predicted): SAT:[ADDR], [PART]↑ dynamic interaction.
    IO must outrank DO on the hierarchy 2 > 1 > 3.
    [deal-2024] §6.1 notes hints of this pattern in Catalan and
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

theorem yf_licit_count : licitCount youFirst = 6 := by decide
theorem ad_licit_count : licitCount aDescending = 5 := by decide

-- ============================================================================
-- § 18: Reverse PCC (§6.2)
-- ============================================================================

/-- Reverse PCC: the probe encounters IO before DO (IO preference).

    [deal-2024] §6.2: in structures where IO moves to a position
    between v and DO, the probe encounters IO first. This reverses the
    PCC restriction — now IO features can satisfy/narrow the probe,
    and DO is the argument that may fail to be licensed.

    Attested in Shapsug Adyghe, varieties of Swiss German, Czech,
    and Slovenian. -/
def reverseLicit (g : DealGrammar) (io do_ : Person) : Bool :=
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

/-- Strong PCC (2a): DO must be 3P — i.e. `[−participant]`, which over
    the full inventory is exactly non-SAP. Any IO is licit with a
    non-SAP DO; any SAP DO is illicit regardless of IO. -/
theorem strong_iff_3p_do (io do_ : Person) :
    isLicit strong io do_ = true ↔ ¬do_.IsSAP := by
  cases io <;> cases do_ <;> decide

/-- Weak PCC (2b): if IO is 3P (`[−participant]`), DO must be 3P.
    Equivalently: the only illicit cells are ⟨non-SAP IO, SAP DO⟩. -/
theorem weak_illicit_iff (io do_ : Person) :
    isLicit weak io do_ = false ↔ ¬io.IsSAP ∧ do_.IsSAP := by
  cases io <;> cases do_ <;> decide

/-- Me-first PCC (2c): if 1P is present, it must be IO. Equivalently:
    DO cannot be 1P. -/
theorem mefirst_iff_not_1p_do (io do_ : Person) :
    isLicit meFirst io do_ = true ↔ dpBears do_ .spkr = false := by
  cases io <;> cases do_ <;> decide

/-- Strictly descending PCC (2d): IO must outrank DO on 1 > 2 > 3
    (prominence). For featurally distinct cells, this is exactly the
    pattern. (Featurally identical cells — ⟨3,3⟩, ⟨2,2⟩, and the cells
    the two-feature system conflates — are licit except ⟨1,1⟩, where
    SAT:[SPKR] fires.) -/
theorem sd_off_diagonal_iff_outranks (io do_ : Person)
    (h : decomposePerson io ≠ decomposePerson do_) :
    isLicit strictlyDescending io do_ = true ↔
      io.prominence > do_.prominence := by
  cases io <;> cases do_ <;> first
    | exact absurd rfl h
    | decide

-- ============================================================================
-- § 20: Additional Entailment
-- ============================================================================

/-- Strong entails strictly descending: anything licit under Strong
    is licit under SD. (Strong bans all SAP DOs; SD bans only 1P DOs
    and ⟨3P IO, SAP DO⟩.) -/
theorem strong_entails_sd (io do_ : Person) :
    isLicit strong io do_ = true → isLicit strictlyDescending io do_ = true := by
  cases io <;> cases do_ <;> decide

-- ============================================================================
-- § 21: Feature Geometry Grounding
-- ============================================================================

/-- `dpBears` is grounded in the shared feature geometry `decomposePerson`
    from Phi/Geometry.lean. This makes the connection structural — Deal's
    person features are not independently stipulated but derived from the
    same privative geometry used by [pancheva-zubizarreta-2018]'s
    `satisfiesProminence` and [bejar-rezac-2009]'s `personSpec`. -/
theorem dpBears_grounded_in_decomposePerson (p : Person) :
    dpBears p .part = (decomposePerson p).hasParticipant ∧
    dpBears p .spkr = (decomposePerson p).hasAuthor := by
  cases p <;> exact ⟨rfl, rfl⟩

/-! ### Bridge: feature gluttony ([coon-keine-2021])

The paper engages [coon-keine-2021] directly (PF ramifications of
Agree "per Coon and Keine (2021)"; both are responses to the same
PCC typology). The two mechanisms — a probe that *stops too early*
(satisfaction) vs. a probe that *agrees too much* (gluttony) —
coincide on the strong and weak varieties cell-for-cell, and part
ways exactly on Me-First's 1>1 cell: Deal's [SAT:SPKR] probe is
satisfied by a first-person DO regardless of the IO (illicit), while
a gluttony probe fully matched by a first-person IO cannot glutton
(licit). [pancheva-zubizarreta-2018]'s me-first grammar sides with
Deal on that cell. -/

/-- The 1/2/3 grid both accounts state their typologies over. -/
private def grid3 : List Person := [.first, .second, .third]

open CoonKeine2021 in
/-- Strong and weak coincide with gluttony cell-for-cell: Deal's
    strong = K-opaque-dative gluttony; Deal's weak = transparent
    weak-probe gluttony. -/
theorem strong_weak_match_gluttony :
    (∀ io ∈ grid3, ∀ do_ ∈ grid3,
      (isLicit strong io do_ = true ↔
        ¬ pccViolation weakProbe true io do_)) ∧
    (∀ io ∈ grid3, ∀ do_ ∈ grid3,
      (isLicit weak io do_ = true ↔
        ¬ pccViolation weakProbe false io do_)) := by
  decide

open CoonKeine2021 in
/-- Me-First diverges from gluttony exactly at 1>1: satisfaction
    bans it, gluttony permits it. All other cells agree. -/
theorem mefirst_diverges_from_gluttony :
    (∀ io ∈ grid3, ∀ do_ ∈ grid3, (io, do_) ≠ (.first, .first) →
      (isLicit meFirst io do_ = true ↔
        ¬ pccViolation meFirstProbe false io do_)) ∧
    isLicit meFirst .first .first = false ∧
    ¬ pccViolation meFirstProbe false .first .first := by
  decide

end Deal2024
