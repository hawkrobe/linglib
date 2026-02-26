import Linglib.Core.Case.Hierarchy

/-!
# Local Case Extension Paths @cite{blake-2001}

Blake (2001, Ch. 5) documents regular paths by which spatial/local cases extend
to grammatical functions. These are cross-linguistically recurrent patterns of
polysemy (grammaticalization):

- **Ablative** (source) → instrumental (means) → causal (reason)
- **Locative** (place) → dative (experiencer, temporal)
- **Allative** (goal) → dative (recipient) → benefactive → purpose

These paths are implicational: if a language uses a spatial case marker for a
function further along the path, it also uses it for all earlier functions.
The direction is always from spatial/concrete to grammatical/abstract — a
locative marker may extend to dative function, but a dative marker does not
extend to locative function.

## References

- Blake, B. J. (2001). *Case* (2nd ed.). Cambridge University Press. Ch. 5.
- Heine, B. (2009). Grammaticalization of cases. In Malchukov, A. & Spencer, A.
  (eds.), *The Oxford Handbook of Case*. OUP.
-/

namespace Core.Case

-- ============================================================================
-- § 1: Extension Paths
-- ============================================================================

/-- The grammatical functions that a spatial case marker can extend to cover,
    ordered from most concrete to most abstract.

    Each path represents a cross-linguistically attested polysemy chain.
    If a language uses case X for function Y, it uses X for all functions
    before Y on the path (Blake 2001, Ch. 5). -/
def localExtension : Case → List Case
  | .abl  => [.inst, .caus]          -- source → instrument → cause
  | .loc  => [.dat]                  -- location → temporal/experiencer
  | .all  => [.dat, .ben]            -- goal → recipient → benefactive
  | .inst => [.caus]                 -- instrument → cause (subpath of ABL)
  | _     => []

/-- Does case `c` have any grammatical extensions? -/
def hasExtension (c : Case) : Bool :=
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
    other grammatical functions (Blake 2001: extensions go from
    peripheral/spatial to grammatical, never the reverse). -/
theorem nom_no_extension : localExtension .nom = [] := rfl
theorem acc_no_extension : localExtension .acc = [] := rfl
theorem erg_no_extension : localExtension .erg = [] := rfl
theorem abs_no_extension : localExtension .abs = [] := rfl

/-- Only peripheral cases have extensions. -/
theorem core_cases_no_extension (c : Case) (a : AlignmentFamily)
    (hCore : c.isCore a = true) : localExtension c = [] := by
  cases a <;> cases c <;> simp_all [Case.isCore, localExtension]

-- ============================================================================
-- § 3: Directionality
-- ============================================================================

/-- Extension sources are always peripheral (spatial) cases, never core. -/
def extensionSourcesPeripheralBool : Bool :=
  Case.allCases.all fun c =>
    if hasExtension c then !c.isCore .accusative && !c.isCore .ergative
    else true

theorem extension_sources_peripheral :
    extensionSourcesPeripheralBool = true := by native_decide

/-- The ABL → INST → CAUS chain is properly ordered:
    each step goes from more concrete to more abstract. -/
theorem abl_chain_ordered :
    Case.hierarchyRank .abl ≥ Case.hierarchyRank .inst ∧
    Case.hierarchyRank .inst ≥ Case.hierarchyRank .caus := by decide

end Core.Case
