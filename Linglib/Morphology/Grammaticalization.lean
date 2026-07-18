import Mathlib.Order.Nat

/-!
# Grammaticalization
[heine-1993] [anderson-2006] [bybee-perkins-pagliuca-1994]
[lehmann-1985] [heine-kuteva-2002] [hopper-traugott-2003]

Grammaticalization: the diachronic process by which lexical items become
grammatical markers. The cline of verbal grammaticalization formalized
here is the 5-stage variant:

    full verb → auxiliary → clitic → affix → zero

## Attribution

The verbal cline is anchored on [heine-1993] ch. 3 (the source
[anderson-2006] cites at p. 5 as `Heine (1993: 48ff.)`).
Anderson's own running shorthand at p. 5 collapses to three stages
(`L[exical] V[erb] >> A[uxiliary] V > AF[fi]X`); the 5-stage form
here splits Heine's continuum at the canonical clitic/affix/zero
boundaries also used by [lehmann-1985] and [hopper-traugott-2003].

**Caveat ([heine-1993] p. 66, endorsed by [anderson-2006] p. 5):**
"we are dealing with chains [of grammaticalization] and since chains
are by definition continuous structures, setting up stages along
these structures must remain an arbitrary and/or artificial endeavor."
The discrete enum below is a working approximation; consumer files
that need finer-grained transitions should pair `GramStage` with
their own intermediate-state predicates rather than treat the 5
cases as exhaustive.

This process is cross-linguistically unidirectional: movement is always toward
greater morphological boundedness ([lehmann-1985], [hopper-traugott-2003]).

## Main definitions

- `GramStage`: stages on the grammaticalization cline
- `GramStage.boundedness`: numeric encoding of morphological boundedness

## Connections

- `Haspelmath2021` (§0): form-frequency correspondence
  is a parallel diachronic process (phonological erosion of frequent forms).
  Apparatus co-located in the Haspelmath 2021 study file (single consumer);
  promote to substrate when a second diachronic study materializes.
- `Quantification.Binominal`: the bleaching cline for binominals (N+PP →
  pseudo-partitive → evaluative → modifier → intensifier) is a specialized
  grammaticalization path in the nominal domain.
- `Features.Subjectivity`: Traugott's subjectification cline is a semantic
  dimension of grammaticalization (see `Studies/Traugott2010.lean`).
-/

namespace Grammaticalization

/-- Stage on the grammaticalization cline for verbal elements.
    Cline anchored on [heine-1993] for the broad path
    `LV >> AV >> AFFIX`; the specific 5-stage segmentation
    (`fullVerb / auxiliary / clitic / affix / zero`) is a
    *coarsening* drawn from [lehmann-1985] and
    [hopper-traugott-2003] ch. 6, NOT a direct rendering of
    Heine's own staging (Heine 1993 §2.4.2 uses a finer 7-stage
    A-G chain: concrete-source → starting-down → budding →
    defective → linguistic-hybrid → firmly-grammaticalized →
    orphaning). [anderson-2006] p. 5 attributes the
    `LV >> AV > AFX` path to Heine 1993:48ff. without committing
    to a specific stage count; ch. 7 traces grammaticalization of
    source constructions onto whatever cline the framework adopts.
    The 5-stage enum here is the linglib working approximation,
    not Heine's own taxonomy. -/
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

end Grammaticalization
