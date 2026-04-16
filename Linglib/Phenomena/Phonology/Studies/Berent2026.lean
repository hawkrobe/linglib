import Linglib.Theories.Phonology.Syllable.Defs
import Linglib.Theories.Phonology.Constraints
import Linglib.Theories.Phonology.Doubling
import Linglib.Core.Logic.OT

/-!
# Berent (2026) @cite{berent-2026}

Three arguments for abstraction in phonology.
*Glossa: a journal of general linguistics* 12(1). 1--24.

Three experimental arguments that phonological grammar is substance-free,
algebraic, and amodal:

1. **Abstract**: syllable structure constraints (sonority sequencing) persist
   under articulatory suppression (TMS, mechanical) and in print reading,
   engaging Broca's area rather than motor cortex. Formalized as gradient
   markedness over the abstract `SonorityRank` type — the grammar sees only
   the ordering, not the articulatory features that correlate with it.

2. **Algebraic**: identity restrictions (*XX ban, OCP) generalize to novel
   feature values unattested in the speaker's language (Hebrew /θ/, novel
   ASL handshapes). Formalized as the type-polymorphic `mkOCP` constraint —
   Lean's parametric polymorphism IS the algebraic property.

3. **Amodal**: English speakers project spoken-language doubling constraints
   onto novel ASL signs, with a phonology--morphology split (identity banned
   in phonological contexts, reduplication preferred in morphological
   contexts). Formalized as competing OT parses over `DoublingParse`
   (see `Theories/Phonology/Doubling.lean`).

## Formalization strategy

The paper's central claims are metatheoretical — they argue about the
*nature* of phonological representations rather than proposing new formal
machinery. The deepest formalization insight is that Lean's type system
already embodies the distinctions Berent draws:

- **Substance-free** = `SonorityRank` is an abstract ordered type, not
  defined by articulatory features (refactored in `Syllable/Defs.lean`)
- **Algebraic** = `mkOCP` is parametrically polymorphic over `α`
  (added to `Constraints.lean`)
- **Amodal** = the same polymorphic constraint applies to any feature
  type, spoken or signed, by construction

The doubling theory (types, constraints, L1-parameterized model) is
factored into `Theories/Phonology/Doubling.lean`. The experimental
data supporting the doubling reversal is in
@cite{berent-bat-el-brentari-dupuis-vaknin-nusbaum-2016}.

@cite{berent-2026}
-/

namespace Phenomena.Phonology.Studies.Berent2026

open Core.OT
open Phonology.Syllable (SonorityRank)
open Phonology.Constraints
open Phonology.Doubling

-- ============================================================================
-- § 1: Onset Markedness — the sonority gradient
-- ============================================================================

/-- Onset sonority profile: the relationship between C1 and C2 sonority
    in a two-segment onset.

    The behavioral gradient rise > plateau > fall (@cite{berent-2026},
    Figure 1A; data from Berent et al. 2007) maps directly to this
    classification on the abstract `SonorityRank` type. -/
inductive OnsetProfile where
  | rise     -- C1 < C2: e.g. /bl/, /pr/ — least marked
  | plateau  -- C1 = C2: e.g. /bd/ — intermediate
  | fall     -- C1 > C2: e.g. /lb/, /nb/ — most marked
  deriving DecidableEq, Repr

/-- Classify a two-segment onset by its sonority profile.
    Operates on `SonorityRank` — the abstract hierarchy — not on
    articulatory features. -/
def onsetProfile (c1 c2 : SonorityRank) : OnsetProfile :=
  if c1.rank < c2.rank then .rise
  else if c1.rank == c2.rank then .plateau
  else .fall

/-- Onset markedness as an OT constraint: gradient violations by sonority
    profile. Uses `mkMarkGrad` from the shared constraint library.

    Rise = 0 violations, plateau = 1, fall = 2. This captures the
    behavioral gradient (blif > bnif > bdif > lbif; @cite{berent-2026},
    data from Berent et al. 2007). The gradient is determined entirely
    by the abstract `SonorityRank` ordering — the grammar does not inspect
    whether "rise" means "stop-before-liquid" vs. "nasal-before-vowel". -/
def onsetSSP : NamedConstraint OnsetProfile :=
  mkMarkGrad "SSP-ONSET" fun
    | .rise => 0
    | .plateau => 1
    | .fall => 2

/-- Gradient markedness of onset sonority profiles (convenience alias). -/
abbrev onsetMarkedness := onsetSSP.eval

theorem rise_lt_plateau : onsetMarkedness .rise < onsetMarkedness .plateau := by
  decide

theorem plateau_lt_fall : onsetMarkedness .plateau < onsetMarkedness .fall := by
  decide

theorem rise_unmarked : onsetMarkedness .rise = 0 := rfl

/-- The sonority gradient is determined by abstract rank, not by features.
    Two segments with the same `SonorityRank` are treated identically
    regardless of their articulatory specification. -/
theorem sonority_gradient_abstract (r1 r2 : SonorityRank) :
    onsetMarkedness (onsetProfile r1 r2) =
    if r1.rank < r2.rank then 0
    else if r1.rank == r2.rank then 1
    else 2 := by
  cases r1 <;> cases r2 <;> rfl

-- ============================================================================
-- § 2: Algebraic OCP — identity avoidance
-- ============================================================================

-- `adjacentIdentical` and `mkOCP` are defined in Constraints.lean and
-- are parametrically polymorphic over the feature type α. That
-- polymorphism IS the algebraic property: the OCP generalizes to novel
-- feature values by construction, because it cannot inspect what kind
-- of features it compares — only whether they are identical.

/-- OCP detects adjacent identity. -/
theorem ocp_detects_aa {α : Type} [BEq α] [LawfulBEq α]
    (a : α) (rest : List α) :
    adjacentIdentical (a :: a :: rest) =
    1 + adjacentIdentical (a :: rest) := by
  simp [adjacentIdentical]

/-- OCP passes over non-identical adjacency. -/
theorem ocp_passes_ab {α : Type} [BEq α] (a b : α) (rest : List α)
    (h : (a == b) = false) :
    adjacentIdentical (a :: b :: rest) =
    adjacentIdentical (b :: rest) := by
  simp [adjacentIdentical, h]

-- ============================================================================
-- § 3: The doubling reversal — summary
-- ============================================================================

-- The doubling theory (DoublingParse, DoublingGrammar, OT constraints)
-- is defined in Theories/Phonology/Doubling.lean. The experimental
-- evidence for the doubling reversal and the L1-morphology dependency
-- is formalized in BerentEtAl2016.lean, which provides the 2×2
-- dissociation between English and Hebrew speakers.
--
-- Here we re-export the core reversal theorem as a summary of the
-- paper's Argument 3 (amodality).

/-- The phonology--morphology reversal: the same OCP-XX produces
    opposite surface preferences depending on whether the morphological
    context licenses reduplication.

    This is the core of @cite{berent-2026}'s third argument: the
    reversal is amodal (it transfers from speech to sign) and
    L1-dependent (it depends on the speaker's morphological system).
    See `Phonology.Doubling.doubling_reversal` for the proof
    and @cite{berent-bat-el-brentari-dupuis-vaknin-nusbaum-2016} for
    the experimental evidence. -/
theorem amodal_doubling_reversal :
    (mkTableau phonCandidates phonRanking).optimal
      = {DoublingParse.nonidentical} ∧
    (mkTableau morphCandidates morphRanking).optimal
      = {DoublingParse.reduplication} :=
  doubling_reversal

end Phenomena.Phonology.Studies.Berent2026
