module

public import Linglib.Syntax.Case.Basic
public import Linglib.Syntax.Case.Order

/-!
# Telugu Case Inventory
[krishnamurti-gwynn-1985] [mcfadden-2018]

Telugu (Dravidian) has **5 core cases** with agglutinative suffixes:
NOM (∅), ACC (-ni), GEN (∅), DAT (-ki), and a locative postposition
(-lō 'in'). [krishnamurti-gwynn-1985] list these as the
productive case/postposition forms for modern Telugu nominals.

Like Tamil and other Dravidian languages, Telugu shows a robust
**NOM-vs-oblique split** in stem allomorphy: the nominative stem
form differs from the form used in all nonnominative contexts
([mcfadden-2018]). This split is predicted by the case containment
hierarchy ([caha-2009]), where all nonnominative cases include
the ACC feature in their syntactic representation; see
`Studies/Aitha2026.lean` for the analysis of Telugu stem allomorphy.
-/

@[expose] public section

namespace Telugu.Case

/-! ### Case inventory -/

/-- Telugu 5-case core inventory.
    ACC, GEN, DAT are inflectional suffixes within the prosodic word;
    LOC is realized by a postposition (-lō) in a separate prosodic word. -/
def inventory : Finset Case :=
  {.nom, .acc, .gen, .dat, .loc}

/-! ### Containment properties -/

/-- All nonnominative Telugu cases bear the ACC feature. -/
theorem acc_nonnom : Case.IsNonnominative .acc := by decide
theorem gen_nonnom : Case.IsNonnominative .gen := by decide
theorem dat_nonnom : Case.IsNonnominative .dat := by decide
theorem loc_nonnom : Case.IsNonnominative .loc := by decide
theorem nom_not_nonnom : ¬ Case.IsNonnominative .nom := by decide

/-! ### Cross-Dravidian connection -/

/-- Telugu and Tamil share the same core case spine on Blake's hierarchy.
    Both have NOM, ACC, GEN, DAT, LOC (Tamil additionally has ABL, INST, COM). -/
theorem telugu_subset_tamil :
    inventory ⊆ ({.nom, .acc, .gen, .dat, .loc, .abl, .inst, .com} : Finset Case) := by
  decide

end Telugu.Case
