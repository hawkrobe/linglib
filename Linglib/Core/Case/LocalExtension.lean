import Linglib.Core.Case.Hierarchy

/-!
# Local Case Extension Paths @cite{blake-1994}

Blake (1994, Ch. 6) documents how semantic cases — especially local cases —
extend to cover grammatical functions through grammaticalization (pp. 172–175).
He shows that this direction is always from spatial/concrete to
grammatical/abstract: a locative marker may extend to dative function, but
not vice versa.

The specific polysemy chains below are our synthesis of Blake's scattered
observations, not his explicit named paths:

- **Ablative** (source) → instrumental (means) → causal (reason)
- **Locative** (place) → dative (experiencer, temporal)
- **Allative** (goal) → dative (recipient) → benefactive

Blake documents ABL/INST syncretism (p. 175: "Ablative-instrumental syncretism
occurred in a number of Indo-European languages"), LOC→DAT extension (p. 188,
note 15), and ALL→DAT overlap (p. 174: "A dative will often express destination
as well"). We encode these as directed chains for computational use.

## References

- Blake, B. J. (1994). *Case*. Cambridge University Press. Ch. 6.
- Heine, B. (2009). Grammaticalization of cases. In Malchukov, A. & Spencer, A.
  (eds.), *The Oxford Handbook of Case*. OUP.
-/

namespace Core

-- ============================================================================
-- § 1: Extension Paths
-- ============================================================================

/-- The grammatical functions that a spatial case marker can extend to cover,
    ordered from most concrete to most abstract.

    Each path represents a cross-linguistically attested polysemy chain,
    synthesized from Blake's (1994, Ch. 6) discussion of case extension. -/
def localExtension : Case → List Case
  | .abl  => [.inst, .caus]          -- source → instrument → cause
  | .loc  => [.dat]                  -- location → temporal/experiencer
  | .all  => [.dat, .ben]            -- goal → recipient → benefactive
  | .inst => [.caus]                 -- instrument → cause (subpath of ABL)
  | _     => []

/-- Does case `c` have any grammatical extensions? -/
private def hasExtension (c : Case) : Bool :=
  !(localExtension c).isEmpty

-- ============================================================================
-- § 2: Extension Properties
-- ============================================================================

/-- ABL extends to INST and CAUS. -/
theorem abl_extends_inst : Case.inst ∈ localExtension .abl := by simp [localExtension]
theorem abl_extends_caus : Case.caus ∈ localExtension .abl := by simp [localExtension]

/-- ALL extends to DAT and BEN. -/
theorem all_extends_dat : Case.dat ∈ localExtension .all := by simp [localExtension]
theorem all_extends_ben : Case.ben ∈ localExtension .all := by simp [localExtension]

/-- LOC extends to DAT. -/
theorem loc_extends_dat : Case.dat ∈ localExtension .loc := by simp [localExtension]

/-- Core grammatical cases have no extensions — they don't extend to
    other grammatical functions (Blake 1994, Ch. 6: extensions go from
    peripheral/spatial to grammatical, never the reverse). -/
theorem nom_no_extension : localExtension .nom = [] := rfl
theorem acc_no_extension : localExtension .acc = [] := rfl
theorem erg_no_extension : localExtension .erg = [] := rfl
theorem abs_no_extension : localExtension .abs = [] := rfl

-- ============================================================================
-- § 3: Directionality
-- ============================================================================

/-- The ABL → INST → CAUS chain is properly ordered:
    each step goes from more concrete to more abstract. -/
theorem abl_chain_ordered :
    Case.hierarchyRank .abl ≥ Case.hierarchyRank .inst ∧
    Case.hierarchyRank .inst ≥ Case.hierarchyRank .caus := by decide

end Core
