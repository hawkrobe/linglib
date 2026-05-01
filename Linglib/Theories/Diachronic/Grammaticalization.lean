import Mathlib.Order.Nat
import Linglib.Core.Morphology.MorphRule

/-!
# Grammaticalization
@cite{heine-1993} @cite{anderson-2006} @cite{bybee-perkins-pagliuca-1994}
@cite{lehmann-1985} @cite{heine-kuteva-2002} @cite{hopper-traugott-2003}

Grammaticalization: the diachronic process by which lexical items become
grammatical markers. The cline of verbal grammaticalization formalized
here is the 5-stage variant:

    full verb → auxiliary → clitic → affix → zero

## Attribution

The verbal cline is anchored on @cite{heine-1993} ch. 3 (the source
@cite{anderson-2006} cites at p. 5 as `Heine (1993: 48ff.)`).
Anderson's own running shorthand at p. 5 collapses to three stages
(`L[exical] V[erb] >> A[uxiliary] V > AF[fi]X`); the 5-stage form
here splits Heine's continuum at the canonical clitic/affix/zero
boundaries also used by @cite{lehmann-1985} and @cite{hopper-traugott-2003}.

**Caveat (@cite{heine-1993} p. 66, endorsed by @cite{anderson-2006} p. 5):**
"we are dealing with chains [of grammaticalization] and since chains
are by definition continuous structures, setting up stages along
these structures must remain an arbitrary and/or artificial endeavor."
The discrete enum below is a working approximation; consumer files
that need finer-grained transitions should pair `GramStage` with
their own intermediate-state predicates rather than treat the 5
cases as exhaustive.

This process is cross-linguistically unidirectional: movement is always toward
greater morphological boundedness (@cite{lehmann-1985}, @cite{hopper-traugott-2003}).

## Main definitions

- `GramStage`: stages on the grammaticalization cline
- `GramStage.boundedness`: numeric encoding of morphological boundedness
- `GramStage.toMorphStatus`: projection onto `Core.Morphology.MorphStatus`
- `AVCSource`: diachronic source constructions for auxiliary verb constructions

## Connections

- `Phenomena.Case.Studies.Haspelmath2021` (§0): form-frequency correspondence
  is a parallel diachronic process (phonological erosion of frequent forms).
  Apparatus co-located in the Haspelmath 2021 study file (single consumer);
  promote to substrate when a second diachronic study materializes.
- `Semantics.Noun.Binominal`: the bleaching cline for binominals (N+PP →
  pseudo-partitive → evaluative → modifier → intensifier) is a specialized
  grammaticalization path in the nominal domain.
- `Features.Subjectivity`: Traugott's subjectification cline is a semantic
  dimension of grammaticalization (see `Diachronic.Subjectification`).
-/

namespace Diachronic.Grammaticalization

-- ============================================================================
-- §1. The Grammaticalization Cline
-- ============================================================================

/-- Stage on the grammaticalization cline for verbal elements.
    Cline anchored on @cite{heine-1993} ch. 3; the 5-stage segmentation
    follows @cite{lehmann-1985} and @cite{hopper-traugott-2003} ch. 6;
    @cite{anderson-2006} ch. 7 traces grammaticalization of source
    constructions onto these stages. -/
inductive GramStage where
  /-- Lexical verb with full argument structure. -/
  | fullVerb
  /-- Grammaticalized verb, restricted morphosyntax. -/
  | auxiliary
  /-- Phonologically reduced, syntactically dependent. -/
  | clitic
  /-- Bound morpheme, part of the verbal word. -/
  | affix
  /-- No overt marker (grammaticalization endpoint). -/
  | zero
  deriving DecidableEq, Repr

/-- Boundedness increases monotonically along the cline. -/
def GramStage.boundedness : GramStage → Nat
  | .fullVerb  => 0
  | .auxiliary => 1
  | .clitic    => 2
  | .affix     => 3
  | .zero      => 4

instance : LinearOrder GramStage :=
  LinearOrder.lift' GramStage.boundedness
    (fun a b h => by cases a <;> cases b <;> simp_all [GramStage.boundedness])

/-- Unidirectionality: grammaticalization never reverses. Formalized as:
    if a language has a marker at stage s₂ that historically derives from
    stage s₁, then s₁ < s₂. -/
def isUnidirectional (_s₁ _s₂ : GramStage) (_h : _s₁ < _s₂) : Prop :=
  ¬(_s₂ < _s₁) -- follows from strict ordering, but makes the claim explicit

theorem unidirectional_of_lt {s₁ s₂ : GramStage} (h : s₁ < s₂) :
    isUnidirectional s₁ s₂ h :=
  Nat.not_lt.mpr (Nat.le_of_lt h)

/-- Project a grammaticalization stage onto its canonical
    `Core.Morphology.MorphStatus` realization. Auxiliaries and full
    verbs are free words on the cline; clitics map to simple-clitic
    status; affixes to inflectional-affix status; the zero endpoint
    has no overt morphological realization. -/
def GramStage.toMorphStatus : GramStage → Option Core.Morphology.MorphStatus
  | .fullVerb  => some .freeWord
  | .auxiliary => some .freeWord
  | .clitic    => some .simpleClitic
  | .affix     => some .inflAffix
  | .zero      => none

-- ============================================================================
-- §2. Source Constructions
-- ============================================================================

/-- Diachronic source construction from which an AVC grammaticalizes.
    @cite{anderson-2006} §7, @cite{heine-kuteva-2002}. -/
inductive AVCSource where
  /-- Serial verb constructions: two verbs in sequence, one
      grammaticalizes into an auxiliary. Common in West African, SE Asian. -/
  | serialVerb
  /-- Complement-taking verb: matrix verb takes clausal complement,
      the matrix verb grammaticalizes. Common source for modals. -/
  | complementTaking
  /-- Motion verb: 'go'/'come' grammaticalize into future/past markers.
      Cross-linguistically one of the most common paths. -/
  | motionVerb
  /-- Postural verb: 'sit'/'stand'/'lie' grammaticalize into
      progressive/habitual aspect markers. -/
  | posturalVerb
  deriving DecidableEq, Repr

end Diachronic.Grammaticalization
