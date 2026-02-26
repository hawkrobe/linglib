import Linglib.Core.Case.Basic
import Linglib.Core.Case.Hierarchy
import Linglib.Core.Case.Syncretism
import Linglib.Core.Case.LocalExtension

/-!
# Finnish Case Inventory @cite{blake-1994}

Finnish has **15 morphological cases** (Karlsson 2018), one of the richest
case systems in Europe:

- **Grammatical** (3): nominative, genitive, partitive (+ accusative for
  pronouns/total objects, often syncretic with NOM or GEN)
- **Internal local** (3): inessive (-ssA, 'in'), elative (-stA, 'out of'),
  illative (-Vn, 'into')
- **External local** (3): adessive (-llA, 'on/at'), ablative (-ltA, 'from'),
  allative (-lle, 'to/onto')
- **Other** (5–6): essive (-nA, 'as'), translative (-ksi, 'becoming'),
  abessive (-ttA, 'without'), comitative (-ine-, 'with'),
  instructive (-n, 'by means of')

Our 16-value `Core.Case` cannot represent the full Finnish system: essive,
translative, and abessive have no equivalent. The internal/external pairs
(inessive/adessive → LOC, elative/ablative → ABL, illative/allative → ALL)
are collapsed into a single rank.

Finnish lacks a dedicated **dative** case — the allative covers recipient
function (Blake 1994, Ch. 6: ALL → DAT extension). This creates a gap at
rank 4 (DAT) on Blake's hierarchy, making Finnish a known exception to
strict contiguity.

## References

- Blake, B. J. (1994). *Case*. Cambridge University Press.
- Karlsson, F. (2018). *Finnish: A Comprehensive Grammar* (3rd ed.). Routledge.
-/

namespace Fragments.Finnish.Case

-- ============================================================================
-- § 1: Case Inventory
-- ============================================================================

/-- Finnish case inventory mapped to `Core.Case`.

    15 Finnish cases → 9 Core.Case values (essive, translative, abessive
    have no equivalent; internal/external local pairs are collapsed):
    - NOM → .nom, ACC → .acc (pronoun/total-object accusative)
    - GEN → .gen, PART → .part
    - INE/ADE → .loc, ELA/ABL → .abl, ILL/ALL → .all
    - INSTR → .inst, COM → .com -/
def caseInventory : List Core.Case :=
  [.nom, .acc, .gen, .part, .loc, .abl, .all, .inst, .com]

/-- Finnish's mapped inventory **fails** strict contiguity: GEN (rank 5)
    and LOC (rank 3) have no DAT (rank 4) between them. Finnish uses
    allative for recipient function instead of a dedicated dative.

    This illustrates Blake's hedge: the hierarchy holds "usually" but
    languages like Finnish fill the dative slot with a local case
    extension (ALL → DAT, formalized in `LocalExtension.lean`). -/
theorem inventory_fails_strict :
    Core.validInventory caseInventory = false := by native_decide

/-- The allative-for-dative substitution is exactly the extension path
    formalized in `Core.localExtension`. -/
theorem allative_extends_to_dative :
    Core.Case.dat ∈ Core.localExtension .all := by simp [Core.localExtension]

-- ============================================================================
-- § 2: Syncretism
-- ============================================================================

/-- Finnish NOM/ACC syncretism: the accusative of non-pronominal singular
    nouns is identical to the nominative (Karlsson 2018, Ch. 13). -/
def nomAccSyncretism : Core.Syncretism :=
  ⟨.nom, .acc, by decide⟩

/-- Finnish ABL/INST are not syncretic — ablative (-ltA) and instructive
    (-n) are distinct forms. Unlike many IE languages where ABL and INST
    merge, Finnish keeps them separate. -/
theorem abl_inst_distinct :
    Core.hierarchyAdjacent .abl .inst = true := by native_decide

end Fragments.Finnish.Case
