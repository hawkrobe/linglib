import Linglib.Core.Word
import Linglib.Theories.Semantics.Polarity.CzechNegation

/-!
# Czech Determiners

Polarity-sensitive determiners central to Staňková's (2026) three-way negation
diagnostic. Czech lacks articles (`ArticleType.none_`), so the NCI/PPI contrast
on determiners is the primary scope diagnostic for negation position.

## Key items

- *žádný* 'no/any' — Negative Concord Item (NCI), licensed only by inner negation
- *nějaký* 'some' — Positive Polarity Item (PPI), must outscope negation
- *každý* 'every' — universal, not polarity-sensitive

## Cross-linguistic connections

- The žádný/nějaký contrast mirrors English *any* (NPI) vs *some* (PPI),
  but Czech žádný is an NCI requiring Agree with ¬ (Zeijlstra 2004),
  not just DE licensing.
- Bridges to `Phenomena.Negation.CzechThreeWayNeg.Diagnostic` for per-position
  compatibility.

## References

- Staňková, V. (2026). A three-way distinction of negation interpretation in Czech.
- Zeijlstra, H. (2004). Sentential Negation and Negative Concord. LOT.
- Giannakidou, A. (1998). Polarity Sensitivity as (Non)Veridical Dependency.
-/

namespace Fragments.Czech.Determiners

open Semantics.Polarity.CzechNegation

-- ============================================================================
-- Polarity Type
-- ============================================================================

/-- Polarity sensitivity type for Czech determiners. -/
inductive PolarityType where
  /-- Negative Concord Item: requires Agree with ¬ (Zeijlstra 2004).
      Stricter than NPI — needs structural relation, not just DE. -/
  | nci
  /-- Positive Polarity Item: must outscope negation.
      Blocked in the immediate scope of ¬. -/
  | ppi
  /-- Not polarity-sensitive. -/
  | neutral
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- Determiner Entry
-- ============================================================================

/-- A Czech determiner entry with polarity and morphological properties. -/
structure DetEntry where
  /-- Surface form -/
  form : String
  /-- Gloss -/
  gloss : String
  /-- Polarity sensitivity -/
  polarityType : PolarityType
  /-- Which diagnostic from Staňková Table 1 this item tests -/
  diagnostic : Option Diagnostic := none
  /-- Requires licensing by ¬ (NCIs only) -/
  requiresNegLicensing : Bool := false
  /-- Must outscope ¬ (PPIs only) -/
  mustOutscopeNeg : Bool := false
  /-- Can be used with mass nouns -/
  allowsMass : Bool := false
  deriving Repr, BEq

-- ============================================================================
-- The Czech Determiner Lexicon
-- ============================================================================

/-- *žádný* 'no, any (NCI)' — the prototypical Czech NCI.

Paradigm: žádný/žádná/žádné (masc/fem/neut), declined for case/number.
Requires licensing by ¬ via Agree at LF (Zeijlstra 2004).
Only licensed under inner negation (TP-level ¬), where the Agree relation
holds between ne- and žádný. Medial and outer negation are too high. -/
def zadny : DetEntry :=
  { form := "žádný"
  , gloss := "no/any.NCI"
  , polarityType := .nci
  , diagnostic := some .nciLicensed
  , requiresNegLicensing := true
  , allowsMass := true }

/-- *nějaký* 'some (PPI)' — the prototypical Czech PPI determiner.

Paradigm: nějaký/nějaká/nějaké (masc/fem/neut), declined for case/number.
Must outscope negation — compatible with medial and outer negation
(where ne- doesn't have narrow scope over the DP), but incompatible
with inner negation (where ne- c-commands and outscopes the PPI). -/
def nejaky : DetEntry :=
  { form := "nějaký"
  , gloss := "some.PPI"
  , polarityType := .ppi
  , diagnostic := some .ppiOutscoping
  , mustOutscopeNeg := true
  , allowsMass := true }

/-- *každý* 'every, each' — universal, not polarity-sensitive.

Compatible with all negation positions. Not a diagnostic for Staňková's
three-way distinction. -/
def kazdy : DetEntry :=
  { form := "každý"
  , gloss := "every"
  , polarityType := .neutral
  , allowsMass := false }

/-- *některý* 'some (partitive), certain' — existential, weakly PPI.

Similar to stressed English "some". Not as restricted as nějaký in
the scope of negation. -/
def nektery : DetEntry :=
  { form := "některý"
  , gloss := "some.PART"
  , polarityType := .ppi
  , mustOutscopeNeg := true }

def allDeterminers : List DetEntry := [zadny, nejaky, kazdy, nektery]

def lookup (form : String) : Option DetEntry :=
  allDeterminers.find? λ d => d.form == form

-- ============================================================================
-- Predicates
-- ============================================================================

/-- Is the determiner a Negative Concord Item? -/
def DetEntry.isNCI (d : DetEntry) : Bool := d.polarityType == .nci

/-- Is the determiner a Positive Polarity Item? -/
def DetEntry.isPPI (d : DetEntry) : Bool := d.polarityType == .ppi

-- ============================================================================
-- Verification
-- ============================================================================

#guard zadny.isNCI
#guard !zadny.isPPI
#guard nejaky.isPPI
#guard !nejaky.isNCI
#guard !kazdy.isNCI && !kazdy.isPPI

-- ============================================================================
-- Bridge to CzechThreeWayNeg: Negation Compatibility
-- ============================================================================

/-- Whether a determiner is compatible with a given negation position,
derived from the `licenses` function in CzechThreeWayNeg. -/
def compatibleWith (d : DetEntry) (pos : NegPosition) : Bool :=
  match d.diagnostic with
  | some diag => licenses pos diag
  | none      => true  -- neutral items are compatible everywhere

-- Per-position compatibility for žádný (NCI)
theorem zadny_inner  : compatibleWith zadny .inner  = true  := rfl
theorem zadny_medial : compatibleWith zadny .medial = false := rfl
theorem zadny_outer  : compatibleWith zadny .outer  = false := rfl

-- Per-position compatibility for nějaký (PPI)
theorem nejaky_inner  : compatibleWith nejaky .inner  = false := rfl
theorem nejaky_medial : compatibleWith nejaky .medial = true  := rfl
theorem nejaky_outer  : compatibleWith nejaky .outer  = true  := rfl

/-- žádný and nějaký have complementary distributions in negated PQs:
exactly the positions where žádný is licensed, nějaký is blocked, and vice versa.
This is the core diagnostic for distinguishing inner from non-inner negation. -/
theorem zadny_nejaky_complementary :
    ∀ pos : NegPosition,
      compatibleWith zadny pos = !compatibleWith nejaky pos := by
  intro pos; cases pos <;> rfl

/-- The NCI/PPI contrast uniquely identifies inner negation:
inner is the only position where žádný is OK and nějaký is blocked. -/
theorem nci_ppi_identifies_inner :
    ∀ pos : NegPosition,
      (compatibleWith zadny pos = true ∧ compatibleWith nejaky pos = false)
      → pos = .inner := by
  intro pos; cases pos <;> decide

end Fragments.Czech.Determiners
