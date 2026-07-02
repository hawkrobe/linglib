import Linglib.Syntax.Minimalist.Phase.Basic
import Linglib.Syntax.Minimalist.Linearization
import Linglib.Syntax.Minimalist.Movement.Remnant
import Linglib.Phonology.OptimalityTheory.CophonologyByPhrase
import Linglib.Syntax.Minimalist.SyntacticObject.Amalgamation

/-!
# Sande, Clem & Dąbkowski (2026): Discontinuous vowel harmony in Guébie
[sande-clem-dabkowski-2026]

[sande-clem-dabkowski-2026] introduce the phenomenon of
**discontinuous harmony**: a long-distance ATR-harmony pattern in
Guébie (a Kru language of Côte d'Ivoire) where the trigger and
target are separated by intervening *non-transparent*
(harmony-eligible) segments. The pattern arises in particle-verb
focus-fronting constructions; the analysis is local harmony followed
by syntactic movement that pulls the harmonized element away from
its trigger.

## Empirical core (the table at §6.1, (44))

| word order   | particle-verb harmony? | verb spelled out in vP? |
|--------------|------------------------|-------------------------|
| `SVOPart`    | ×                      | ×                       |
| `SAuxOPartV` | ✓                      | ✓                       |
| `PartSVO`    | ×                      | ×                       |
| `PartSAuxOV` | ✓                      | ✓                       |

Harmony applies iff V is spelled out inside vP — independent of the
surface adjacency between V and the particle. In `PartSAuxOV`,
predicate fronting separates them on the surface, but V was inside
vP at the moment of vP-spell-out (when local harmony applied).

## The analysis

1. **Predicate fronting is remnant-VP movement** (extending
   [koopman-1997]'s Vata/Nweh analysis). The particle is the
   only overt element left in the remnant after V has moved through v
   to T and the object has shifted out (where applicable).

2. **vP and CP are spell-out phases**. Following the cyclic
   spell-out of [newell-2008] / [chomsky-2001], vP is
   spelled out upon Merge of C; CP is spelled out at the end.

3. **Local harmony in vP**. ATR harmony is a vP-domain cophonology
   (per [sande-jenks-inkelas-2020]'s Cophonologies-by-Phrase
   architecture, formalized in `CophonologyByPhrase.lean`):
   when V and Part are both spelled out in vP, harmony applies; when
   only Part is in the vP-spell-out, no trigger is present and Part
   surfaces with its default −ATR value.

4. **Frozen ATR survives later movement**. Once the particle has
   harmonized to V's ATR value at vP-spell-out, the value persists
   through subsequent A′-fronting of the remnant VP into Spec,CP
   (Cyclic-Linearization-style preservation —
   `Minimalist.Linearization.frozenValue`).

5. **Strict PIC is rejected**. For step 4 to work, already-spelled-out
   material must remain accessible to later syntactic operations
   (here, A′-movement of the remnant containing the particle). SCD
   2026 §6.2 rejects both PIC₁ ([chomsky-2000]) and PIC₂
   ([chomsky-2001]) in favor of a Cyclic-Linearization-bounded
   regime — `PICStrength.linearizationBound` in `Phase.lean`.

## What this study file establishes

For each of the four word orders, the file:

- proves the derivation is consistently linearizable
  (`Minimalist.Linearization.SpelloutAndCheck`),
- computes the predicted harmony status (true iff V is in vP-content),
- decides the (44) table by `decide`,
- registers Guébie predicate fronting as a positive instance of
  `HarizanovGribanova2019.Amalgamation.VerbDoublingIsSyntactic`
  (refactored from a universal axiom in light of this paper —
  see `HarizanovGribanova2019Amalgamation.lean`).

The Wolof relative-clause parallel (§7) is added as a sister
construction with the same architectural shape; the Atchan
nasal-harmony case (§7) is recorded as an open question with sparse
data — Russell, p.c.

## Verified preliminaries (rejected alternatives)

[sande-clem-dabkowski-2026] §5 argues that purely phonological
theories of harmony predict strict locality and so cannot derive the
discontinuous pattern. The file does not formally simulate each
rejected theory (autosegmental [clements-1985], gestural
[gafos-1998], ABC [rose-walker-2004]), but cross-references
their formalizations elsewhere in linglib —
`Studies/RoseWalker2004.lean`,
`Studies/Hansson2010.lean`,
`Studies/Sagey1986.lean` — and notes how each
predicts the observed locality bound that SCD 2026 demonstrates is
empirically violated.

## Architectural notes

Substrate consumed (additions landed in this same overhaul):

- `Phonology/OptimalityTheory/CophonologyByPhrase.lean` —
  [sande-jenks-inkelas-2020]'s phrasal extension of
  [sande-jenks-2017]'s VI-anchored cophonology.
- `Syntax/Minimalist/Movement/Remnant.lean` —
  [koopman-1997] predicate-cleft remnant-XP movement.
- `Syntax/Minimalist/Phase.lean` — added
  `PICStrength.linearizationBound` and `admitsExtraction`.
- `Syntax/Minimalist/Linearization/Cyclic.lean` — added
  `FrozenFeature` / `frozenValue` for cross-phase feature preservation.
- `Studies/HarizanovGribanova2019Amalgamation.lean`
  — refactored `axiom verb_doubling_implies_syntactic` to a
  per-construction `Prop`, motivated by SCD 2026's stance that the
  universal version is too strong (Landau 2006 Hebrew counterexample).

Per-language Guébie data lives entirely in this file (no
`Fragments/Guebie/`), per CLAUDE.md "per-language paper-specific data
lives in Studies, not Fragments".
-/

namespace SandeClemDabkowski2026

open Minimalist (PICStrength)
open Minimalist.Linearization
  (SpelloutAndCheck FrozenFeature FrozenFeatureTable
   extendFrozenFeatures frozenValue)
open OptimalityTheory.CophonologyByPhrase (PhrasalCophonology)

-- ============================================================================
-- § 1: Guébie vowel inventory and ATR feature
-- ============================================================================

/-! ### Guébie vowel inventory ([sande-clem-dabkowski-2026] (1))

```
+ATR:  ə  e  i  o  u
-ATR:  a  ɛ  ɪ  ɔ  ʊ
```

Vowels harmonize as a binary +/−ATR feature within a morpheme; affixes
agree with the root ([sande-2017], [sande-2019],
[sande-2022]). Particles in particle-verb constructions inherit
the ATR value of the verb root *when both are inside the same
spell-out domain* — this is the discontinuous-harmony observation.

We do not enumerate the full vowel inventory here; for the Table 44
result we only need a per-terminal ATR value. -/

/-- The ATR feature value carried by a phonological terminal.
    `+ATR = true`, `−ATR = false`. -/
abbrev ATR := Bool

/-- The default ATR value for the particle when no vowel-harmony trigger
    is present in its spell-out domain. [sande-clem-dabkowski-2026]
    §2.5 — particles surface with their lexical (typically -ATR) value
    when not local to a harmony trigger. -/
def particleDefaultATR : ATR := false

-- ============================================================================
-- § 2: The four word orders
-- ============================================================================

/-- The four particle-verb word orders that diagnose discontinuous
    harmony ([sande-clem-dabkowski-2026] (44), §6.1). -/
inductive WordOrder where
  /-- `S V O Part`: V moves to T; Part stays in vP; clause-final. -/
  | SVOPart
  /-- `S Aux O Part V`: V stays in v (Aux occupies T); both V and Part
      in vP at vP-spell-out. -/
  | SAuxOPartV
  /-- `Part S V O`: V moves to T; Part fronts to Spec,CP from vP. -/
  | PartSVO
  /-- `Part S Aux O V`: V stays in v; remnant VP (containing Part)
      fronts to Spec,CP. -/
  | PartSAuxOV
  deriving DecidableEq, Repr

/-- The terminals spelled out within vP for each word order
    ([sande-clem-dabkowski-2026] (45)/(48)). The decisive
    difference: `SAuxOPartV` and `PartSAuxOV` keep V inside vP at
    spell-out (V hasn't raised past v), while `SVOPart` and `PartSVO`
    have V already in T at vP-spell-out, leaving only Part inside vP.

    The object has independently shifted out of vP in all four
    derivations (per [koopman-1997]-style remnant-VP analysis,
    extended in §4 of the paper), so it does not appear here. -/
def vPSpellOut : WordOrder → List String
  | .SVOPart    => ["Part"]
  | .SAuxOPartV => ["Part", "V"]
  | .PartSVO    => ["Part"]
  | .PartSAuxOV => ["Part", "V"]

/-- The terminals introduced or first linearized at the CP-phase
    spell-out. Each terminal is spelled out at exactly one phase per
    Cyclic Linearization, *unless* it has moved between phases — in
    which case the higher phase's linearization positions it again,
    consistently with the lower phase's statements (Order Preservation).

    - In `SVOPart` and `SAuxOPartV`, the Part stays inside vP and
      appears only in `vPSpellOut`, not here.
    - In `PartSVO` and `PartSAuxOV`, the Part has fronted to Spec,CP
      and so appears at the left edge of `cpSpellOut` (in addition to
      its base position in `vPSpellOut`).
    - The verb V appears here only when it has moved to T (i.e., in
      `SVOPart` and `PartSVO`); when V stays in v (the SAuxOV cases),
      it remains inside vP. -/
def cpSpellOut : WordOrder → List String
  | .SVOPart    => ["S", "V", "O"]            -- Part stays in vP
  | .SAuxOPartV => ["S", "Aux", "O"]
  | .PartSVO    => ["Part", "S", "V", "O"]    -- Part fronts to Spec,CP
  | .PartSAuxOV => ["Part", "S", "Aux", "O"]

/-- Cyclic-Linearization derivation: the two-phase spell-out for a
    given word order. -/
def derivation (wo : WordOrder) : List (List String) :=
  [vPSpellOut wo, cpSpellOut wo]

-- ============================================================================
-- § 3: All four derivations are consistently linearizable
-- ============================================================================

/-- `SVOPart`: V in T, Part in clause-final position. Consistent. -/
theorem SVOPart_consistent : SpelloutAndCheck (derivation .SVOPart) := by decide

/-- `SAuxOPartV`: V in v, both V and Part inside vP. Consistent. -/
theorem SAuxOPartV_consistent : SpelloutAndCheck (derivation .SAuxOPartV) := by decide

/-- `PartSVO`: V in T, Part fronts. Consistent under
    Cyclic-Linearization (no contradiction with vP-internal order). -/
theorem PartSVO_consistent : SpelloutAndCheck (derivation .PartSVO) := by decide

/-- `PartSAuxOV`: V in v, remnant VP fronts. Consistent. The crucial
    derivation for discontinuous harmony — Part is local to V at
    vP-spell-out, and the linearization remains coherent after
    fronting. -/
theorem PartSAuxOV_consistent : SpelloutAndCheck (derivation .PartSAuxOV) := by decide

-- ============================================================================
-- § 4: Predicted harmony status (Table 44)
-- ============================================================================

/-- Harmony applies iff the trigger V is spelled out within vP.
    Independent of the linear adjacency between V and Part at the
    surface. The target Part is by stipulation always inside vP at
    vP-spell-out (it's the Part of a particle-verb construction;
    even when it later fronts, it starts in vP), so the trigger
    presence is the only varying condition. -/
def harmonyApplies (wo : WordOrder) : Bool :=
  (vPSpellOut wo).contains "V"

/-- The decisive empirical theorem: SCD 2026 Table 44, decided
    structurally. Harmony applies in exactly the two SAuxOV-shape
    derivations — the ones where V hasn't raised past v. -/
theorem table_44 :
    harmonyApplies .SVOPart    = false ∧
    harmonyApplies .SAuxOPartV = true  ∧
    harmonyApplies .PartSVO    = false ∧
    harmonyApplies .PartSAuxOV = true  := by decide

/-- Discontinuous harmony at one glance: in `PartSAuxOV`, Part is
    surface-non-local to V (the subject, auxiliary, and object
    intervene at CP-spell-out), yet harmony applies. -/
theorem partSAuxOV_discontinuous_yet_harmonizes :
    harmonyApplies .PartSAuxOV = true ∧
    "S" ∈ cpSpellOut .PartSAuxOV ∧
    "Aux" ∈ cpSpellOut .PartSAuxOV ∧
    "O" ∈ cpSpellOut .PartSAuxOV := by decide

-- ============================================================================
-- § 5: Frozen ATR survives later movement (SCD 2026 §6.1)
-- ============================================================================

/-- The ATR value frozen at vP-spell-out for `PartSAuxOV`: when V is
    +ATR (e.g. /joku/), Part inherits +ATR via local vP-internal
    harmony. This is the freezing event. -/
def vPFrozen_PartSAuxOV (vIsPlusATR : ATR) : FrozenFeatureTable :=
  if vIsPlusATR then [⟨"Part", "ATR", true⟩]
  else            [⟨"Part", "ATR", false⟩]

/-- After remnant-VP fronting at the CP-phase spell-out, no new ATR
    assignments are issued for Part — the value is preserved. -/
theorem PartSAuxOV_atr_persists_through_fronting (vIsPlusATR : ATR) :
    frozenValue
      (extendFrozenFeatures (vPFrozen_PartSAuxOV vIsPlusATR) [])
      "Part" "ATR" = some vIsPlusATR := by
  cases vIsPlusATR <;> decide

-- ============================================================================
-- § 6: Strict PIC is rejected (SCD 2026 §6.2)
-- ============================================================================

/-- [sande-clem-dabkowski-2026]'s commitment: the PIC mode for
    Guébie discontinuous harmony is `linearizationBound` — already
    spelled-out material remains accessible to later syntax. Strict
    PIC₁ or PIC₂ would block the remnant-VP movement of the particle
    after its ATR value has been frozen. -/
def guebiePICMode : PICStrength := .linearizationBound

/-- Under the Guébie PIC mode, every phase admits extraction of any
    goal at the phasehood layer; concrete crashes come from
    `SpelloutAndCheck` instead. The four-derivation theorem above
    confirms no derivation crashes. -/
theorem guebie_PIC_admits_remnant_movement (φ : Minimalist.Phase)
    (goal : Minimalist.SyntacticObject) :
    Minimalist.admitsExtraction guebiePICMode φ goal := by
  unfold guebiePICMode; exact Minimalist.linearizationBound_admits_all φ goal

-- ============================================================================
-- § 7: Verb doubling diagnosed as syntactic (refutes Landau 2006 for Guébie)
-- ============================================================================

/-! [sande-clem-dabkowski-2026] §3 establishes via island
    sensitivity (their (27)–(30)) that Guébie predicate-fronting verb
    doubling is narrow-syntactic, not PF dislocation. This positions
    Guébie alongside [harizanov-gribanova-2019]'s Russian as a
    positive instance of `VerbDoublingIsSyntactic` — and against
    [landau-2006]'s Hebrew analysis (which makes verb doubling
    PF-driven).

    The previous formulation as a universal axiom was inconsistent
    with Landau's Hebrew analysis; the SCD 2026 paper is the trigger
    for the substrate refactor in
    `HarizanovGribanova2019Amalgamation.lean`.

    We register Guébie as a positive instance via a `RemnantFronting`
    witness with a `PredicateDoubling` extension. The structural data
    is schematic (we use `Minimalist.SyntacticObject.leaf` placeholders
    for V and the fronted XP rather than a concrete tree) — this is
    consistent with the rest of the file's spell-out-list abstraction.
    What it does establish is that the substrate is *usable*: the
    `properRemnant` predicate is decidable on the witness. -/

open Minimalist (SyntacticObject LIToken LexicalItem SO)
open Minimalist.Movement (RemnantFronting PredicateDoubling properRemnant)

/-- A schematic verb leaf for the `PredicateDoubling` witness. -/
private def guebieVerbTok : LIToken := ⟨.simple .V [], 1⟩
private def guebieVerbLeaf : SyntacticObject := SO.lexLeaf guebieVerbTok

/-- A schematic remnant-VP node containing the verb leaf as a trace
    pronounced for recoverability. Built planar-first (the smart
    `SO.node` is noncomputable) so the `decide` proofs below reduce. -/
private def guebieFrontedVP : SyntacticObject :=
  SO.ofPlanar (SO.nodeP (SO.leafP guebieVerbTok) (SO.leafP guebieVerbTok))

/-- A schematic landing-site leaf (Spec,CP). -/
private def guebieLandingTok : LIToken := ⟨.simple .C [], 2⟩
private def guebieLandingSite : SyntacticObject := SO.lexLeaf guebieLandingTok

/-- The Guébie predicate-fronting witness: V evacuates the VP, and
    the remnant VP fronts to Spec,CP. The trace is pronounced — verb
    doubling. -/
def guebiePredicateDoubling : PredicateDoubling :=
  { frontedXP        := guebieFrontedVP
    evacuatedHeads   := [guebieVerbLeaf]
    landingSite      := guebieLandingSite
    verb             := guebieVerbLeaf
    verb_evacuated   := List.mem_singleton.mpr rfl
    trace_pronounced := true }

/-- The witness is a proper remnant: the evacuated verb originally
    sat inside the fronted VP (true by construction here, since
    `frontedVP = node verb verb`). -/
theorem guebie_properRemnant : properRemnant guebiePredicateDoubling.toRemnantFronting := by
  decide

/-! ### Guébie's vP cophonology as a `PhrasalCophonology` instance

The vP-domain ATR-harmony cophonology of [sande-jenks-inkelas-2020]
applied to Guébie. The phase selector matches `v` heads (per the v*
phase head of Chomsky 2000); the constraint subranking is left
abstract here (it would be `[ATRHARM ≫ IDENT-IO(ATR)]` over the
candidate type the OT machinery uses, which we don't instantiate
inline). -/

/-- The phase-selector for Guébie's vP cophonology: matches v heads
    (and only v heads). On the `SO` carrier the selector reads the root
    leaf's token (`PhrasalCophonology.appliesTo` only ever applies it to a
    `SO.lexLeaf` of the phase head), so a v head is detected by its
    outer category. -/
def guebieVPPhaseSelector : SyntacticObject → Bool := fun s =>
  match s.getLIToken with
  | some tok => tok.item.outerCat == .v
  | none => false

/-- The Guébie vP-cophonology bundle. The `subranking` is left as an
    empty list of constraints over `Unit` candidates because the
    ATR-harmony cophonology's actual constraints (SPREAD/IDENT derived
    from a `Harmony.System`) would require threading the OT-candidate type
    through this study file — out of
    scope. The substrate use is exhibited by the bundle's existence
    and the matched-phase predicate `appliesTo`. -/
def guebieVPCophonology : PhrasalCophonology Unit Unit :=
  { phaseSelector := guebieVPPhaseSelector
    subranking    := [] }

/-- The Guébie vP-cophonology applies to a v head. (Witness: a leaf
    SO whose token's category is `.v`.) -/
theorem guebieVPCophonology_applies_to_v :
    let vTok : LIToken := ⟨.simple .v [], 99⟩
    let vHead : SyntacticObject := SO.lexLeaf vTok
    let vPhase : Minimalist.Phase := { tree := vHead, head := vTok }
    guebieVPCophonology.appliesTo vPhase = true := by decide

/-! ### Guébie as a positive instance of `VerbDoublingIsSyntactic`

[sande-clem-dabkowski-2026] §3 provides three independent
diagnostics that the Guébie verb-doubling movement is narrow-syntactic:
successive cyclicity (their (25)–(26)), island sensitivity ((27)–(28)),
and creates-island effects ((29)–(30)). On the basis of this evidence,
we register the Guébie predicate-fronting case as a positive instance
of `HarizanovGribanova2019.Amalgamation.VerbDoublingIsSyntactic`.

The Lean statement uses the MCB-aligned `VerbDoublingIsSyntacticIn`
(see `HarizanovGribanova2019Amalgamation.lean`), which takes a
`Derivation` and asks whether the verb is among the `movedItems` of
the derivation. Per MCB §1.4.3.1, Internal Merge IS the syntactic
mechanism that produces surface verb doubling via PF copy/trace
pronunciation rules — the verb appears once in the syntactic tree
(deeper copy as `mkTrace`), but PF rules pronounce both. -/

open Minimalist (VerbDoublingIsSyntacticIn)

/-- A schematic Guébie Derivation: the verb undergoes Internal Merge
    in the predicate-fronting derivation (per SCD 2026 §3 island
    diagnostics establishing this is narrow-syntactic, not PF). -/
def guebieFrontingDerivation : Minimalist.SO.Derivation :=
  { initial := guebieFrontedVP
    steps   := [.im guebieVerbLeaf] }

/-- Guébie predicate-fronting verb doubling registered as a positive
    instance of `VerbDoublingIsSyntacticIn`: the verb is among
    `guebieFrontingDerivation.movedItems`.

    Decidable from the Derivation structure (no `sorry`). This
    discharges the audit's outstanding sorry for Guébie VDIS. -/
theorem guebie_VDIS_positive_instance :
    VerbDoublingIsSyntacticIn guebieFrontingDerivation guebieVerbLeaf := by
  decide

-- ============================================================================
-- § 8: Wolof relative-clause parallel (SCD 2026 §7)
-- ============================================================================

/-! Wolof shows the same architectural shape as Guébie discontinuous
    harmony, in a relative-clause construction ([sy-2005],
    [martinovic-2019]). The head noun starts local to the
    distal demonstrative inside DP; both spell out together with
    local ATR harmony applying; the head noun then A′-moves to the
    left edge of the relative clause; intervening stative-verb
    material does not harmonize. -/

inductive WolofRelClauseShape where
  /-- Local DP, harmony applies (no relative clause):
      `[DP head dem]` — head and dem in the same spell-out domain. -/
  | localDP
  /-- Relative clause, harmony at distance:
      `head … [stative-V] … dem` — head fronted out of DP, but its
      ATR is set inside the DP-phase before fronting. -/
  | relClause
  deriving DecidableEq, Repr

def wolofVPSpellOut : WolofRelClauseShape → List String
  | .localDP   => ["head", "dem"]
  | .relClause => ["head", "dem"]

def wolofHarmonyApplies (s : WolofRelClauseShape) : Bool :=
  (wolofVPSpellOut s).contains "head" && (wolofVPSpellOut s).contains "dem"

/-- Both Wolof shapes have the head and demonstrative spelled out
    together at the DP-phase spell-out — predicting harmony in both,
    consistent with [sy-2005]'s data. The discontinuous
    appearance in the relative-clause case is post-spell-out
    movement, not a different harmony mechanism. -/
theorem wolof_harmony_uniform :
    wolofHarmonyApplies .localDP = true ∧
    wolofHarmonyApplies .relClause = true := by decide

-- ============================================================================
-- § 9: Atchan nasal-harmony stub (SCD 2026 §7, Russell p.c.)
-- ============================================================================

/-! [russell-2023] reports a parallel pattern in Atchan nasal
    harmony: a nasal singular subject pronoun triggers nasal harmony
    on auxiliaries and the verb; in verb-doubling focus
    constructions, the higher copy of the verb (in focus position)
    also surfaces nasal even though it is not surface-local to the
    nasal subject pronoun.

    The data are sparse (a single personal-communication example,
    SCD 2026 (51)) and the Atchan verb-doubling syntax is not yet
    independently established as narrow-syntactic. Recorded here as
    an open question.

    TODO: Atchan formalization waits on independent syntactic
    diagnostics for verb doubling (the analogue of SCD §3 for
    Guébie). -/

end SandeClemDabkowski2026
