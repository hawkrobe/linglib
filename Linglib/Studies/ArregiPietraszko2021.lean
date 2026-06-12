import Linglib.Syntax.Minimalist.GenHM
import Linglib.Data.Examples.ArregiPietraszko2021

/-!
# GenHM and Do-Support
[arregi-pietraszko-2021]

Connects the GenHM formalization to A&P's do-support paradigm
(`Data/Examples/ArregiPietraszko2021.json`).

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

open Data.Examples
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

/-- Value of a `paperFeatures` key, if present. -/
def featureOf (row : LinguisticExample) (key : String) : Option String :=
  (row.paperFeatures.find? (·.1 == key)).map (·.2)

/-- Does the sentence use do-support? (`do_support` feature). -/
def usesDoSupport (row : LinguisticExample) : Option Bool :=
  (featureOf row "do_support").map (· == "true")

/-- Does the probe carry lexical content? (auxiliary = true, lexical
    V = false; `verb_type` feature). -/
def probeHasContent (row : LinguisticExample) : Option Bool :=
  (featureOf row "verb_type").map (· == "auxiliary")

/-- A&P's do-support paradigm as a bridge table: each generated row
    paired with the GenHM chain configuration assigned in §1.

    Coverage: A&P's three core contexts (negation, SAI, verum focus)
    each tested with lexical V, auxiliary, and the starred do-support
    misuse; VPE tested with lexical V only (the auxiliary case is not a
    do-support trigger and not in A&P's discussion of VPE). -/
def doSupportTable : List (LinguisticExample × GenHMChain) :=
  [ (Examples.ex32, negationChain)    -- "Sue does not eat fish"
  , (Examples.ex33, negationChain)    -- *"Sue not eats fish"
  , (Examples.ex34, negationChain)    -- "Sue is not eating fish"
  , (Examples.ex35, negationChain)    -- *"Sue does not be eating fish"
  , (Examples.ex27, questionChain)    -- "Where does Sue eat fish?"
  , (Examples.ex30, questionChain)    -- "Where is Sue eating fish?"
  , (Examples.ex31, questionChain)    -- *"Where does Sue be eating fish?"
  , (Examples.ex39, verumChain)       -- "Sue DOES eat fish"
  , (Examples.ex40, verumChain)       -- "She IS eating fish"
  , (Examples.ex41, verumChain)       -- *"She DOES be eating fish"
  , (Examples.ex38, vpEllipsisChain)  -- "She runs faster than he does"
  ]

/-- **Transfer equation**: a row in the bridge table is acceptable iff
    its use (or omission) of do-support matches the GenHM prediction for
    its chain and probe content. The starred rows (`ex31`, `ex33`,
    `ex35`, `ex41`) are exactly those whose do-support usage contradicts
    the prediction — A&P's parallelism claim is precisely that this
    holds uniformly across all four contexts. -/
theorem all_bridges_hold :
    ∀ p ∈ doSupportTable,
      p.1.judgment = .acceptable ↔
        usesDoSupport p.1 = (probeHasContent p.1).map (needsDoSupportGenHM p.2) := by
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
