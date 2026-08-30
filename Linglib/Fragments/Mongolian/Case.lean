import Linglib.Features.Case.Basic
import Linglib.Syntax.Minimalist.Case.Dependent
import Linglib.Syntax.Minimalist.LateMerger

/-!
# Mongolian case

Mongolian (Khalkha and Chakhar) has an accusative-aligned system in which accusative is a
dependent case, valued on the lower of two NPs in the clause, nominative is assigned by finite T
under Agree, and dative is nonstructural. Because accusative is configurational it is available
at intermediate positions of a scrambling chain wherever a case competitor exists, which is what
Wholesale Late Merger needs to bleed Condition C; Condition C reconstruction tracks these case
positions rather than scrambling type or the A/A-bar distinction.

## References

* [gong-2022]
* [baker-vinokurova-2010]
-/

namespace Mongolian.Case

open Minimalist _root_.Case

/-- The Mongolian grammar of structural case: accusative on the lower of two NPs in the
    clause, nominative from T and genitive from D under Agree, and no dependent dative. -/
def grammar : CaseGrammar where
  domains := [(.D, {}), (.v, {}), (.C, { low := some .acc })]
  agree := [(.T, .nom), (.D, .gen)]

-- ============================================================================
-- S 2: Scrambling Types
-- ============================================================================

/-- Scrambling types in Mongolian, classified by distance and landing site.
    [gong-2022] section 2. -/
inductive ScrambleType where
  /-- Short scrambling: DO moves past IO within the clause. -/
  | SS
  /-- Intermediate scrambling: DO moves past the subject to
      pre-subject position within the clause. -/
  | IS
  /-- Long-distance scrambling: an argument moves out of an
      embedded finite clause into the matrix clause. -/
  | LDS
  deriving DecidableEq, Repr

/-- The grammatical role of the pronoun binder in the base order.
    This determines which case the binder bears, which in turn
    determines the structural height of the binder and whether
    a dependent ACC position exists above it. -/
inductive BinderRole where
  /-- Indirect object binder (bears DAT, nonstructural). -/
  | io
  /-- Subject binder (bears NOM, assigned by T). -/
  | subject
  deriving DecidableEq, Repr

-- ============================================================================
-- S 3: Mongolian Case Inventory
-- ============================================================================

/-- Mongolian case inventory.
    NOM, ACC, GEN, DAT, ABL, INST, COM.
    [gong-2022]: the cases relevant to scrambling and WLM are
    NOM (Agree-based), ACC (dependent), and DAT (nonstructural).

    Note: Mongolian lacks a dedicated locative suffix (LOC is expressed
    via postpositions like *deer* 'on'), creating a Blake hierarchy gap
    at rank 3 between DAT (rank 4) and ABL/INST (rank 2). This is a
    known counterexample to strict hierarchy contiguity. -/
def caseInventory : Finset Case :=
  {.nom, .acc, .gen, .dat, .abl, .inst, .com}

-- ============================================================================
-- S 4: Deriving WLM from Dependent Case
-- ============================================================================

/-- A Mongolian ditransitive: the subject above the direct object, shifted to the clause
    edge, above the dative indirect object. -/
def ditransitive : List PhasedNP :=
  [{ label := "subject" }, { label := "DO", phase := .v, shifted := true },
   { label := "IO", phase := .v, lexicalCase := some .dat }]

/-- Its cases, with finite T probing the clause. -/
def ditransitiveCases : List (NP × Valuation) := grammar.assign [(.T, .C)] ditransitive

/-- The direct object is valued accusative by the dependent rule, the subject being the
    caseless NP above it: the case position Wholesale Late Merger needs above the indirect
    object. -/
theorem do_gets_dependent_acc :
    getCaseOf "DO" ditransitiveCases = some .acc ∧
    getMechanismOf "DO" ditransitiveCases = some .dependent := by decide

/-- The subject is valued nominative by T, not by a dependent rule: there is no dependent
    case position above it. -/
theorem subject_gets_nom_by_agree :
    getCaseOf "subject" ditransitiveCases = some .nom ∧
    getMechanismOf "subject" ditransitiveCases = some .agree := by decide

/-- The indirect object keeps its lexical dative and neither competes for dependent case nor
    creates a case position. -/
theorem io_has_lexical_case : getMechanismOf "IO" ditransitiveCases = some .lexical := by decide

-- ============================================================================
-- S 5: Chain Positions for WLM (Derived)
-- ============================================================================

/-- Structural height encoding for Mongolian clause positions.
    Higher numbers = structurally higher positions. -/
def ioHeight : Nat := 1
def subjectHeight : Nat := 2
def specVPHeight : Nat := 3  -- intermediate landing site (edge of VP phase)

/-- Case positions available on a scrambling chain in Mongolian.

    **These are derived from the dependent case algorithm**, not stipulated:
    - Above IO: the direct object is valued dependent accusative
      (`do_gets_dependent_acc`), so Spec,VP is a case position
    - Above Subject: the subject is valued by T, not a dependent rule
      (`subject_gets_nom_by_agree`), so no case position exists -/
def casePositionsAbove (role : BinderRole) : List ChainPosition :=
  match role with
  | .io => [⟨specVPHeight, true⟩]
  | .subject => []

/-- Binder height from its grammatical role. -/
def binderHeight (role : BinderRole) : Nat :=
  match role with
  | .io => ioHeight
  | .subject => subjectHeight

-- ============================================================================
-- S 6: WLM Predictions
-- ============================================================================

/-- Whether WLM predicts Condition C reconstruction in a given scenario.
    This is the central prediction of [gong-2022]: reconstruction
    tracks case positions, not scrambling type or A/A-bar status. -/
def predictsReconstruction (role : BinderRole) : Bool :=
  wlmForcesReconstruction (casePositionsAbove role) (binderHeight role)

/-- Scrambling over IO: WLM bleeds Condition C.
    [gong-2022] (4), (18b), (27): dependent ACC is available at
    Spec,VP (`do_gets_dependent_acc`), so the NP restrictor
    can merge above the IO binder without violating Condition C. -/
theorem io_binder_no_reconstruction :
    predictsReconstruction .io = false := by decide

/-- Scrambling over Subject: WLM forces Condition C reconstruction.
    [gong-2022] (3), (20), (21), (29): no dependent case position
    exists above the subject (`subject_gets_nom_by_agree`),
    so the NP restrictor must merge below the subject binder. -/
theorem subject_binder_forces_reconstruction :
    predictsReconstruction .subject = true := by decide

-- ============================================================================
-- S 7: PP-Scrambling
-- ============================================================================

/-- PP-scrambling always forces Condition C reconstruction.
    PPs lack the DP-internal structure (determiner + NP restrictor)
    required for WLM. [gong-2022] (93)-(94): scrambling of PPs
    headed by *esreg* 'against' always shows obligatory reconstruction,
    regardless of whether the binder is an IO or Subject. -/
def ppReconstructsOverIO : Bool := ppAlwaysReconstructs
def ppReconstructsOverSubj : Bool := ppAlwaysReconstructs

theorem pp_always_reconstructs_io :
    ppReconstructsOverIO = true := rfl

theorem pp_always_reconstructs_subj :
    ppReconstructsOverSubj = true := rfl

end Mongolian.Case
