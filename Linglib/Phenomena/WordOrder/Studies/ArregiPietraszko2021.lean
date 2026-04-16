import Linglib.Theories.Syntax.Minimalism.Formal.HeadMovement.GenHM
import Linglib.Phenomena.WordOrder.SubjectAuxInversion

/-!
# GenHM and Do-Support
@cite{arregi-pietraszko-2021}

Connects the GenHM formalization to empirical data from `SubjectAuxInversion.lean`.

## Structure

**§1** English terminal strength assignment
**§2** English GenHM chain configurations for the five do-support contexts
**§3** Theorems pairing each empirical datum with GenHM predictions
**§4** The parallelism theorem: do-support uniformity across all five contexts
**§5** Deriving VMovementParam from GenHM

## Central Result

The parallelism of do-support across negation, SAI, verum focus, tag questions,
and VP ellipsis is a DERIVED consequence of GenHM chain structure, not a
stipulation about the V-movement parameter. The five contexts involve three
distinct structural reasons for chain-splitting — weak intervention,
probe displacement, and goal absence — yet all produce the same do-support
outcome because spell-out depends only on WHETHER the chain is split.

-/

namespace ArregiPietraszko2021

open Phenomena.WordOrder.SubjectAuxInversion
open Minimalism

-- ============================================================================
-- § 1  English Terminal Strength Assignment
-- ============================================================================

/-- English terminal strength: Neg and Foc are weak; all others strong. -/
def englishStrength : TerminalStrengthAssignment := defaultStrength

theorem neg_is_weak : englishStrength .Neg = .weak := rfl
theorem foc_is_weak : englishStrength .Foc = .weak := rfl
theorem v_is_strong : englishStrength .V = .strong := rfl
theorem t_is_strong : englishStrength .T = .strong := rfl
theorem c_is_strong : englishStrength .C = .strong := rfl

-- ============================================================================
-- § 2  English GenHM Chain Configurations
-- ============================================================================

/-! The five do-support contexts, formalized as GenHM chains. Each chain has:
- A probe (T) and goal (V)
- A split reason encoding WHY the chain is split
- The English strength assignment

The five chains involve three distinct split mechanisms:
- **Split-by-Intervention**: negation (Neg), verum focus (Foc)
- **Split-by-Displacement**: SAI (T displaced to C)
- **Split-by-Deletion**: tag questions, VP ellipsis (goal absent) -/

/-- **Negation chain**: T ... Neg ... V

    "Sue does not eat fish" — Neg (weak) intervenes between T and V.
    Split-by-Intervention. -/
def negationChain : GenHMChain where
  probeCat := .T
  goalCat := .V
  splitReason := some (.weakIntervener .Neg)
  strength := englishStrength

/-- **Verum focus chain**: T ... Foc ... V

    "Sue DOES eat fish" — Foc (weak) intervenes between T and V.
    Split-by-Intervention. -/
def verumChain : GenHMChain where
  probeCat := .T
  goalCat := .V
  splitReason := some (.weakIntervener .Foc)
  strength := englishStrength

/-- **Question chain (SAI)**: C ← T ... V

    "Where does Sue eat fish?" — T is displaced to C via GenHM(C,T),
    breaking the T–V chain. The M-value cannot lower to V because T
    is no longer structurally adjacent to V.
    Split-by-Displacement. -/
def questionChain : GenHMChain where
  probeCat := .T
  goalCat := .V
  splitReason := some .probeDisplaced
  strength := englishStrength

/-- **Tag question chain**: T ... [VP absent]

    "She likes him, doesn't she?" — VP is anaphoric/absent in the tag.
    The M-value cannot lower because the goal is not available.
    Split-by-Deletion. -/
def tagChain : GenHMChain where
  probeCat := .T
  goalCat := .V
  splitReason := some .goalAbsent
  strength := englishStrength

/-- **VP ellipsis chain**: T ... [VP deleted]

    "She runs faster than he does" — VP is elided at PF. The M-value
    cannot lower because the goal has been deleted.
    Split-by-Deletion. -/
def vpEllipsisChain : GenHMChain where
  probeCat := .T
  goalCat := .V
  splitReason := some .goalAbsent
  strength := englishStrength

/-- A declarative chain with no split: T ... V

    "Sue eats fish" — clear chain, M-value lowers to V (affix hopping). -/
def declarativeChain : GenHMChain where
  probeCat := .T
  goalCat := .V
  splitReason := none
  strength := englishStrength

-- ============================================================================
-- § 2b  Chain Properties
-- ============================================================================

theorem negation_chain_split : negationChain.isSplit = true := rfl
theorem verum_chain_split : verumChain.isSplit = true := rfl
theorem question_chain_split : questionChain.isSplit = true := rfl
theorem tag_chain_split : tagChain.isSplit = true := rfl
theorem vpEllipsis_chain_split : vpEllipsisChain.isSplit = true := rfl
theorem declarative_chain_clear : declarativeChain.isSplit = false := rfl

/-- Well-formedness: intervention chains have genuinely weak interveners. -/
theorem negation_chain_wf : negationChain.wellFormed = true := rfl
theorem verum_chain_wf : verumChain.wellFormed = true := rfl
theorem question_chain_wf : questionChain.wellFormed = true := rfl
theorem tag_chain_wf : tagChain.wellFormed = true := rfl
theorem vpEllipsis_chain_wf : vpEllipsisChain.wellFormed = true := rfl
theorem declarative_chain_wf : declarativeChain.wellFormed = true := rfl

/-- In declaratives, the M-value lowers to V (affix hopping). -/
theorem declarative_lowers : spellOutTarget declarativeChain = .onGoal := rfl

/-- In declaratives with lexical verbs, no do-support is needed. -/
theorem declarative_no_doSupport : needsDoSupportGenHM declarativeChain false = false := rfl

-- ============================================================================
-- § 3  Bridge Theorems: Do-Support Predictions
-- ============================================================================

-- § 3a: Negation context (Split-by-Intervention)

/-- ex32 "Sue does not eat fish" — negation + lexical V → do-support -/
theorem bridge_genHM_ex32 :
    ex32.acceptability == .grammatical ∧
    needsDoSupportGenHM negationChain false = true := ⟨rfl, rfl⟩

/-- ex34 "Sue is not eating fish" — negation + auxiliary → no do-support -/
theorem bridge_genHM_ex34 :
    ex34.acceptability == .grammatical ∧
    needsDoSupportGenHM negationChain true = false := ⟨rfl, rfl⟩

-- § 3b: Question context (Split-by-Displacement)

/-- ex27 "Where does Sue eat fish?" — question + lexical V → do-support -/
theorem bridge_genHM_ex27 :
    ex27.acceptability == .grammatical ∧
    needsDoSupportGenHM questionChain false = true := ⟨rfl, rfl⟩

/-- ex30 "Where is Sue eating fish?" — question + auxiliary → no do-support -/
theorem bridge_genHM_ex30 :
    ex30.acceptability == .grammatical ∧
    needsDoSupportGenHM questionChain true = false := ⟨rfl, rfl⟩

-- § 3c: Verum focus context (Split-by-Intervention)

/-- ex39 "Sue DOES eat fish" — verum + lexical V → do-support -/
theorem bridge_genHM_ex39 :
    ex39.acceptability == .grammatical ∧
    needsDoSupportGenHM verumChain false = true := ⟨rfl, rfl⟩

/-- ex40 "She IS eating fish" — verum + auxiliary → no do-support -/
theorem bridge_genHM_ex40 :
    ex40.acceptability == .grammatical ∧
    needsDoSupportGenHM verumChain true = false := ⟨rfl, rfl⟩

-- § 3d: Tag questions (Split-by-Deletion)

/-- ex36 "She likes him, doesn't she?" — tag + lexical V → do-support -/
theorem bridge_genHM_ex36 :
    ex36.acceptability == .grammatical ∧
    needsDoSupportGenHM tagChain false = true := ⟨rfl, rfl⟩

-- § 3e: VP ellipsis (Split-by-Deletion)

/-- ex38 "She runs faster than he does" — VP ellipsis + lexical V → do-support -/
theorem bridge_genHM_ex38 :
    ex38.acceptability == .grammatical ∧
    needsDoSupportGenHM vpEllipsisChain false = true := ⟨rfl, rfl⟩

-- ============================================================================
-- § 4  The Parallelism Theorem
-- ============================================================================

/-- **The Parallelism Theorem (lexical verbs)**: Do-support is triggered
    in ALL five contexts with lexical verbs (contentless T), despite three
    different structural reasons for chain-splitting. -/
theorem doSupport_parallel_all_contexts_lexical :
    needsDoSupportGenHM negationChain false = true ∧
    needsDoSupportGenHM questionChain false = true ∧
    needsDoSupportGenHM verumChain false = true ∧
    needsDoSupportGenHM tagChain false = true ∧
    needsDoSupportGenHM vpEllipsisChain false = true :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- With auxiliaries, do-support is never needed in ANY context. -/
theorem doSupport_parallel_all_contexts_aux :
    needsDoSupportGenHM negationChain true = false ∧
    needsDoSupportGenHM questionChain true = false ∧
    needsDoSupportGenHM verumChain true = false ∧
    needsDoSupportGenHM tagChain true = false ∧
    needsDoSupportGenHM vpEllipsisChain true = false :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The abstract parallelism: for ANY two chains with the same split status,
    the do-support decision is identical. The reason for the split
    (intervention, displacement, deletion) is irrelevant. -/
theorem doSupport_context_irrelevant
    (chain₁ chain₂ : GenHMChain) (content : Bool)
    (h : chain₁.isSplit = chain₂.isSplit) :
    needsDoSupportGenHM chain₁ content = needsDoSupportGenHM chain₂ content :=
  doSupport_uniform_across_contexts chain₁ chain₂ content content h rfl

-- ============================================================================
-- § 5  Deriving VMovementParam from GenHM
-- ============================================================================

/-- A clear chain (no split) yields the `.raises` surface pattern. -/
theorem genHM_derives_raises :
    genHM_to_vMovementParam declarativeChain = .raises := rfl

/-- A split chain yields the `.inSitu` surface pattern. -/
theorem genHM_derives_inSitu :
    genHM_to_vMovementParam negationChain = .inSitu := rfl

/-- The Pollock1989 `needsDoSupport` function is consistent with GenHM
    predictions for lexical verbs across all contexts. -/
theorem genHM_consistent_with_pollock_lexical (ctx : TenseSupportContext) :
    needsDoSupport englishLexical ctx = true := by
  cases ctx <;> rfl

/-- The Pollock1989 `needsDoSupport` function is consistent with GenHM
    predictions for auxiliaries across all contexts. -/
theorem genHM_consistent_with_pollock_aux (ctx : TenseSupportContext) :
    needsDoSupport englishAux ctx = false := by
  cases ctx <;> rfl

end ArregiPietraszko2021
