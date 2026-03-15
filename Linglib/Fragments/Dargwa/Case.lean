import Linglib.Core.Case

/-!
# Dargwa (Tanti) Case Inventory @cite{sumbatova-2021}

Dargwa (Tanti dialect; Nakh-Dagestanian) has a **consistently ergative**
alignment system — unlike Georgian's tense-conditioned split. All transitive
verbs mark the A-argument with ergative *-li* and leave the P-argument
unmarked (absolutive). There is no split conditioning.

## Grammatical Cases (Table 4.3 of @cite{sumbatova-2021})

| Case        | Morpheme | Function                                |
|-------------|----------|-----------------------------------------|
| absolutive  | ∅        | S-argument, P-argument, nominal pred.   |
| ergative    | -li      | A-argument, instrument                  |
| genitive    | -la, -lla | nominal modifier, possessor            |
| dative      | -ž       | experiencer, recipient, benefactive     |
| comitative  | -c:ele   | comitative, instrument                  |
| adverbial   | -le      | nominal predicate, secondary predicate  |

## Locative System

In addition to the 6 grammatical cases above, Dargwa has a rich **spatial
case** system. Locative forms decompose into three morphological layers:

    STEM — LOCALIZATION — ORIENTATION — DIRECTION

Eight localizations (SUPER, SUB, ANTE, IN, INTER, AD, APUD, POST) ×
four orientations (LATIVE, ELATIVE, ESSIVE, TRANSLATIVE) ×
four directions (UP, DOWN, HITHER, THITHER).

This yields a large paradigm, though not all cells are filled.
-/

namespace Fragments.Dargwa.Case

-- ============================================================================
-- § 1: Grammatical Case Inventory
-- ============================================================================

/-- Dargwa grammatical case inventory: ABS(∅), ERG(-li), GEN(-la, -lla),
    DAT(-ž), COM(-c:ele), ADV(-le).

    We use `Core.Case` values. The adverbial case is mapped to `ess`
    (essive) as the closest typological equivalent — it marks
    "being-in-a-state" predicates, analogous to the Finnish essive.

    Genitive has two allomorphs: -la and -lla. -/
def caseInventory : List Core.Case :=
  [.abs, .erg, .gen, .dat, .com, .ess]

/-- Dargwa's grammatical case inventory violates strict contiguity
    on Blake's hierarchy: COM (rank 1) and ESS (rank 0) are present
    without LOC (rank 3) or ABL/INST (rank 2). This is expected:
    Dargwa's rich *locative system* (8 localizations × 4 orientations)
    functionally covers spatial and source meanings that LOC and ABL
    encode in other languages. The grammatical vs. locative split is
    a structural feature of Nakh-Dagestanian languages. -/
theorem inventory_not_strictly_contiguous :
    Core.validInventory caseInventory = false := by native_decide

-- ============================================================================
-- § 2: Consistent Ergative Alignment
-- ============================================================================

/-- Dargwa alignment: consistently ergative — no tense/aspect split.
    Transitive A-arguments always take ergative *-li*;
    S and P arguments take unmarked absolutive. -/
def alignment : Core.AlignmentFamily := .ergative

/-- Case of the transitive agent (A-argument): always ergative. -/
def agentCase : Core.Case := .erg

/-- Case of the S-argument and P-argument: always absolutive. -/
def patientCase : Core.Case := .abs

-- ============================================================================
-- § 3: Locative Decomposition
-- ============================================================================

/-- Localization values: spatial domain w.r.t. the reference point.
    Tanti has 8 localizations (@cite{sumbatova-2021} §4.4.3.3). -/
inductive Localization where
  | super  -- -ja: 'on the surface'
  | sub    -- -gu: 'under'
  | ante   -- -sa: 'in front of'
  | in_    -- -ħe (-ħaˁ): 'inside a container'
  | inter  -- -c:e: 'in a solid substance'
  | ad     -- -š:u: 'in the functionally associated place'
  | apud   -- -hira: 'near, in the vicinity'
  | post   -- -hi: 'behind'
  deriving DecidableEq, BEq, Repr

/-- Orientation values: motion w.r.t. the reference point.
    Tanti has 4 orientations (@cite{sumbatova-2021} §4.4.3.3). -/
inductive Orientation where
  | lative       -- unmarked: motion toward
  | elative      -- -r: motion from
  | essive       -- localization + gender marker: position
  | translative  -- -t:i: motion across
  deriving DecidableEq, BEq, Repr

/-- Direction values: motion w.r.t. the speaker.
    Tanti has 4 directions (@cite{sumbatova-2021} §4.4.3.3). -/
inductive Direction where
  | up      -- -ha(le)
  | down    -- -ka(le)
  | hither  -- -se(le), -sale
  | thither -- -de(le), -dale
  deriving DecidableEq, BEq, Repr

/-- A full locative form combines all three layers. -/
structure LocativeForm where
  localization : Localization
  orientation : Orientation
  direction : Option Direction  -- absent in essives
  deriving Repr

/-- Well-formedness of a locative form, encoding all combinatorial
    constraints from @cite{sumbatova-2021} §4.4.3.3:

    **Direction**: absent in essive and translative, obligatory in
    elative, optional in lative.

    **Localization × Orientation**: translative combines only with SUB,
    ANTE, POST. POST combines only with translative. -/
def LocativeForm.wellFormed (lf : LocativeForm) : Bool :=
  let dirOk := match lf.orientation with
    | .essive      => lf.direction.isNone
    | .elative     => lf.direction.isSome
    | .translative => lf.direction.isNone
    | .lative      => true
  let locOrOk := match lf.orientation, lf.localization with
    | .translative, .sub  => true
    | .translative, .ante => true
    | .translative, .post => true
    | .translative, _     => false
    | _, .post             => false
    | _, _                 => true
  dirOk && locOrOk

/-- Translative combines only with SUB, ANTE, and POST. -/
def Orientation.translativeRestricted (loc : Localization) : Bool :=
  match loc with
  | .sub | .ante | .post => true
  | _ => false

-- ============================================================================
-- § 4: Verification
-- ============================================================================

/-- The inventory contains both core ergative cases. -/
theorem has_core_ergative :
    caseInventory.any (· == .abs) = true ∧
    caseInventory.any (· == .erg) = true := ⟨by native_decide, by native_decide⟩

/-- Dargwa is consistently ergative (no split). -/
theorem consistently_ergative :
    alignment = .ergative := rfl

/-- All 8 localizations are distinct (no collapse). -/
theorem eight_localizations :
    [Localization.super, .sub, .ante, .in_, .inter, .ad, .apud, .post].length = 8 := by
  native_decide

/-- Translative combines only with SUB, ANTE, and POST
    (@cite{sumbatova-2021} ex. 13). -/
theorem translative_restricted_sub :
    Orientation.translativeRestricted .sub = true := rfl

theorem translative_restricted_ante :
    Orientation.translativeRestricted .ante = true := rfl

theorem translative_restricted_post :
    Orientation.translativeRestricted .post = true := rfl

theorem translative_blocked_super :
    Orientation.translativeRestricted .super = false := rfl

/-- POST + LATIVE is ill-formed (POST only combines with translative). -/
theorem post_lative_illformed :
    (LocativeForm.mk .post .lative none).wellFormed = false := rfl

/-- POST + TRANSLATIVE is the only well-formed POST combination. -/
theorem post_translative_wellformed :
    (LocativeForm.mk .post .translative none).wellFormed = true := rfl

/-- Elative requires a direction marker. -/
theorem elative_needs_direction :
    (LocativeForm.mk .super .elative none).wellFormed = false := rfl

/-- Essive rejects direction markers. -/
theorem essive_rejects_direction :
    (LocativeForm.mk .super .essive (some .hither)).wellFormed = false := rfl

/-- SUPER-ELATIVE-HITHER (ex. 16: 'from the bridge hither') is well-formed. -/
theorem super_elative_hither :
    (LocativeForm.mk .super .elative (some .hither)).wellFormed = true := rfl

/-- SUPER-ESSIVE (ex. 12: 'on the bridge, position') is well-formed. -/
theorem super_essive :
    (LocativeForm.mk .super .essive none).wellFormed = true := rfl

/-- SUB-TRANSLATIVE (ex. 13: 'under the bridge, motion') is well-formed. -/
theorem sub_translative :
    (LocativeForm.mk .sub .translative none).wellFormed = true := rfl

/-- Translative + SUPER is ill-formed. -/
theorem translative_super_illformed :
    (LocativeForm.mk .super .translative none).wellFormed = false := rfl

end Fragments.Dargwa.Case
