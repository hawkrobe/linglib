import Linglib.Syntax.Mereological.Basic
import Linglib.Features.Number.Interp

/-!
# Mereological Syntax → Semantics Bridge
[adger-2025] [borer-2005] [wang-sun-2026]

Connects the syntactic visibility predicate (`labelInOnePartChain`) from
mereological syntax to the atoms-restriction `Number.atomsOf` — the
individuating operation [wang-sun-2026] and [adger-2025] assume for the
classifier head of a [borer-2005]-style nominal spine — closing the gap
between two independent uses of mereology in the library:

1. **Semantic mereology** (`Semantics/Mereology.lean`): part-whole over entities.
   CUM (cumulative), QUA (quantized), `Number.atomsOf` (restriction to atoms).
2. **Syntactic mereology** (`Mereological/`): part-of over syntactic
   objects. SynObj, subjoin, Dimensionality.

The syntactic parthood structure *determines* which semantic operations
compose into the denotation. Whether Cl is in D's 1-part chain determines
whether individuation (`Number.atomsOf`) applies:

- **Cl visible** (in 1-part chain) → atoms-restriction applies → QUA → sortal
- **Cl invisible** (cross-dimensional) → root passes through → CUM → mensural

This is the formal content of [wang-sun-2026]'s 的-contrast.
-/

namespace MereologicalSyntax

-- ════════════════════════════════════════════════════
-- § 1. Visibility as Individuation
-- ════════════════════════════════════════════════════

/-- Whether the classifier is structurally visible from a syntactic
    node: true iff Cl is in the node's 1-part chain. This syntactic
    predicate determines whether semantic individuation applies. -/
def individuates (d : SynObj) : Bool :=
  labelInOnePartChain .Cl d

-- ════════════════════════════════════════════════════
-- § 2. Nominal Denotation
-- ════════════════════════════════════════════════════

section Semantics

open _root_.Mereology

variable {α : Type*} [SemilatticeSup α]

/-- The nominal denotation at a syntactic node, given a root predicate P.

    When Cl is visible (in the node's 1-part chain), `Number.atomsOf` applies:
    the denotation picks out atomic instances of P (sortal/count).
    When Cl is invisible, P passes through unmodified (mensural/mass). -/
noncomputable def nominalDenotation (d : SynObj) (P : α → Prop) : α → Prop :=
  if individuates d then Number.atomsOf P else P

/-- Classifier-parametric variant: further restricts which atoms qualify,
    based on the classifier's semantic content
    (e.g., 张 *zhāng* restricts to flat-surface atoms). -/
noncomputable def nominalDenotationCL (d : SynObj) (P : α → Prop)
    (cl : α → Prop) : α → Prop :=
  if individuates d then Number.atomsOf (fun x => P x ∧ cl x) else P

-- ════════════════════════════════════════════════════
-- § 3. Core Bridge Theorems
-- ════════════════════════════════════════════════════

/-- **Core bridge**: when Cl is visible, the nominal denotation is
    quantized. Syntactic visibility → semantic individuation → QUA. -/
theorem visible_cl_gives_qua (d : SynObj) (P : α → Prop)
    (hv : individuates d = true) :
    QUA (nominalDenotation d P) := by
  unfold nominalDenotation; rw [hv]; exact qua_of_atom fun _ h => h.2

/-- When Cl is invisible, the denotation equals the root predicate. -/
theorem invisible_cl_preserves_root (d : SynObj) (P : α → Prop)
    (hv : individuates d = false) :
    nominalDenotation d P = P := by
  unfold nominalDenotation; simp [hv]

/-- Classifier-parametric bridge: visible Cl with classifier predicate
    still yields QUA. -/
theorem visible_cl_gives_qua_CL (d : SynObj) (P : α → Prop)
    (cl : α → Prop) (hv : individuates d = true) :
    QUA (nominalDenotationCL d P cl) := by
  unfold nominalDenotationCL; rw [hv]; exact qua_of_atom fun _ h => h.2

/-- When Cl is invisible and the root is cumulative, the denotation
    is cumulative — the mass/mensural reading. -/
theorem invisible_cl_cum (d : SynObj) (P : α → Prop)
    (hv : individuates d = false) (hc : CUM P) :
    CUM (nominalDenotation d P) := by
  rw [invisible_cl_preserves_root d P hv]; exact hc

-- ════════════════════════════════════════════════════
-- § 4. The 的-Contrast
-- ════════════════════════════════════════════════════

/-- The structural semantic contrast: the same root predicate, in two
    structures differing only in dimensional attachment, yields opposite
    mereological properties.

    The hypothesis `CUM P` is [borer-2005]'s thesis that root
    predicates are cumulative. -/
theorem de_semantic_contrast (d_no_de d_de : SynObj) (P : α → Prop)
    (h_vis : individuates d_no_de = true)
    (h_invis : individuates d_de = false)
    (hc : CUM P) :
    QUA (nominalDenotation d_no_de P) ∧
    CUM (nominalDenotation d_de P) :=
  ⟨visible_cl_gives_qua d_no_de P h_vis,
   invisible_cl_cum d_de P h_invis hc⟩

end Semantics

end MereologicalSyntax
