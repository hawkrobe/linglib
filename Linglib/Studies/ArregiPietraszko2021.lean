import Linglib.Syntax.Minimalist.GenHM
import Linglib.Phenomena.WordOrder.SubjectAuxInversion

/-!
# GenHM and Do-Support
@cite{arregi-pietraszko-2021}

Connects the GenHM formalization to empirical data from `SubjectAuxInversion.lean`.

## Structure

**§1** English GenHM chain configurations for A&P's four do-support contexts
**§2** The bridge table: each contextual datum paired with its GenHM prediction
**§3** The parallelism theorem: do-support uniformity across all four contexts
**§4** Deriving VMovementParam from GenHM

## Central Result

The parallelism of do-support across A&P's three core contexts (negation,
SAI, verum focus) plus VPE is a DERIVED consequence of GenHM chain
structure, not a stipulation about the V-movement parameter. The four
contexts involve two structurally distinct reasons for chain-splitting —
intervention by a [+P] specifier (negation, SAI, verum) and post-syntactic
[-P] on V* (VPE) — yet all produce the same do-support outcome because
spell-out depends only on WHETHER the chain is split.

A&P unify the three intervention contexts under a single specifier-intervention
rule (footnote 30). SAI is intervention by the subject in Spec,TP, NOT
"probe displacement"; verum focus is intervention by a covert specifier in
Spec,ΣP, NOT a "weak Foc head".

## Out of scope

Tag questions (e.g. *She likes him, doesn't she?*) are not in A&P's paper;
their analysis belongs in a future Sailor 2018 study file. A substantive
`TenseSupportContext → GenHMChain` bridge that would connect this file's
predictions to `Pollock1989.lean`'s `needsDoSupport` is deferred to a
cross-framework wiring follow-up. Orphan Assignment (the actual do-insertion
derivation) and the strong V parameter (A&P's cross-linguistic prediction)
are deferred to follow-up substrate work; `needsDoSupportGenHM` here is a
Boolean proxy.

-/

namespace ArregiPietraszko2021

open Phenomena.WordOrder.SubjectAuxInversion
open Minimalist

-- ============================================================================
-- § 1  English GenHM Chain Configurations
-- ============================================================================

/-! A&P's four do-support contexts as GenHM chains. The four chains involve
two distinct split mechanisms:

- **Split-by-Intervention** (a [+P] specifier intervenes between top of
  chain and V*): negation, SAI, verum focus.
- **Split-by-Deletion** (V* marked [-P] post-syntactically): VPE. -/

/-- **Negation chain**: T ... [Spec,ΣP: *not*] ... V

    "Sue does not eat fish" — overt *not* in Spec,ΣP intervenes.
    Split-by-Intervention. -/
def negationChain : GenHMChain where
  probeCat    := .T
  goalCat     := .V
  splitReason := some (.intervention .negSpecifier)

/-- **Verum focus chain**: T ... [Spec,ΣP: covert verum specifier] ... V

    "Sue DOES eat fish" — covert specifier in Spec,ΣP intervenes
    (cf. A&P fn. 30 — same intervention mechanism as negation).
    Split-by-Intervention. -/
def verumChain : GenHMChain where
  probeCat    := .T
  goalCat     := .V
  splitReason := some (.intervention .verumCovertSpecifier)

/-- **Question chain (SAI)**: C ← T ... [Spec,TP: subject] ... V

    "Where does Sue eat fish?" — the subject in Spec,TP intervenes
    between T (chained to C) and V*. Crucially this is intervention,
    NOT "probe displacement" — see A&P, where GenHM is taken to relate
    V, T, and C across the subject specifier.
    Split-by-Intervention. -/
def questionChain : GenHMChain where
  probeCat    := .T
  goalCat     := .V
  splitReason := some (.intervention .subjectInSpecTP)

/-- **VP ellipsis chain**: T ... V (with V* marked [-P] post-syntactically)

    "She runs faster than he does" — V is present and chained to T;
    VPE marks V* with [-P], blocking lowered Vocabulary Insertion.
    Split-by-Deletion (NOT goal-absence — A&P's analysis crucially has
    GenHM still applying). -/
def vpEllipsisChain : GenHMChain where
  probeCat    := .T
  goalCat     := .V
  splitReason := some .deletion

/-- A declarative chain with no split: T ... V

    "Sue eats fish" — clear chain, M-value lowers to V (affix hopping). -/
def declarativeChain : GenHMChain where
  probeCat    := .T
  goalCat     := .V
  splitReason := none

/-- Behavioral fact about declaratives: M-value lowers (affix hopping). -/
@[simp] theorem declarative_lowers : spellOutTarget declarativeChain = .onGoal := rfl

/-- Behavioral fact about declaratives with lexical V: no do-support. -/
@[simp] theorem declarative_no_doSupport :
    needsDoSupportGenHM declarativeChain false = false := rfl

-- ============================================================================
-- § 2  Bridge Table: Empirical Data Meets GenHM Predictions
-- ============================================================================

/-- A&P's do-support paradigm as a bridge table.

    Each row pairs an empirical datum from `SubjectAuxInversion.lean`
    with the GenHM chain configuration assigned in §1, the probe-content
    Boolean (lexical V = false, auxiliary = true), and the do-support
    prediction.

    Coverage: A&P's three core contexts (negation, SAI, verum focus) each
    tested with both lexical V and auxiliary; VPE tested with lexical V
    only (the auxiliary case is not a do-support trigger and not in A&P's
    discussion of VPE). -/
def doSupportTable : List (SAIDatum × GenHMChain × Bool × Bool) :=
  [ (ex32, negationChain,    false, true)   -- "Sue does not eat fish"
  , (ex34, negationChain,    true,  false)  -- "Sue is not eating fish"
  , (ex27, questionChain,    false, true)   -- "Where does Sue eat fish?"
  , (ex30, questionChain,    true,  false)  -- "Where is Sue eating fish?"
  , (ex39, verumChain,       false, true)   -- "Sue DOES eat fish"
  , (ex40, verumChain,       true,  false)  -- "She IS eating fish"
  , (ex38, vpEllipsisChain,  false, true)   -- "She runs faster than he does"
  ]

/-- Every row in the bridge table holds: the example is grammatical AND
    GenHM predicts the right do-support outcome. This single theorem
    replaces the per-example bridge theorems of earlier drafts — A&P's
    parallelism claim is precisely that the table is uniform. -/
theorem all_bridges_hold :
    ∀ row ∈ doSupportTable,
      row.1.acceptability = .grammatical ∧
      needsDoSupportGenHM row.2.1 row.2.2.1 = row.2.2.2 := by
  decide

-- ============================================================================
-- § 3  The Parallelism Theorem
-- ============================================================================

/-- **Parallelism for lexical verbs**: any split chain triggers do-support
    when the probe is contentless. Concrete consequence of the substrate
    theorem `lexical_verb_needs_doSupport_when_split`. -/
theorem doSupport_parallel_lexical
    (chain : GenHMChain) (h : chain.isSplit = true) :
    needsDoSupportGenHM chain false = true :=
  lexical_verb_needs_doSupport_when_split chain h

/-- **Parallelism for auxiliaries**: no chain triggers do-support when the
    probe carries lexical content. Concrete consequence of
    `auxiliaries_dont_need_doSupport`. -/
theorem doSupport_parallel_aux (chain : GenHMChain) :
    needsDoSupportGenHM chain true = false :=
  auxiliaries_dont_need_doSupport chain

/-- **Context-irrelevance**: any two chains with the same split status give
    the same do-support decision. The reason for the split (intervention
    vs deletion) is irrelevant. -/
theorem doSupport_context_irrelevant
    (chain₁ chain₂ : GenHMChain) (content : Bool)
    (h : chain₁.isSplit = chain₂.isSplit) :
    needsDoSupportGenHM chain₁ content = needsDoSupportGenHM chain₂ content :=
  doSupport_uniform_across_contexts chain₁ chain₂ content content h rfl

-- ============================================================================
-- § 4  Deriving VMovementParam from GenHM
-- ============================================================================

/-- A clear chain (no split) yields the `.raises` surface pattern. -/
theorem genHM_derives_raises :
    genHM_to_vMovementParam declarativeChain = .raises := rfl

/-- A split chain yields the `.inSitu` surface pattern. -/
theorem genHM_derives_inSitu :
    genHM_to_vMovementParam negationChain = .inSitu := rfl

/-! TODO: a substantive `chainOf : TenseSupportContext → GenHMChain` map
would let us state `needsDoSupport p ctx = needsDoSupportGenHM (chainOf ctx)
(contentOf p)` — converting Pollock1989's flat parameter into a derived
view of GenHM's chain structure. Deferred to a cross-framework wiring
follow-up that also touches `Pollock1989.lean`. -/

end ArregiPietraszko2021
