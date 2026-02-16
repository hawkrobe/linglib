import Linglib.Phenomena.ScalarImplicatures.Basic
import Linglib.Phenomena.Modality.FreeChoice

/-!
# Meyer & Feiman (2021) — Composing Alternatives

Structural priming evidence that scalar and free choice implicatures
decompose into independently parameterizable sub-computations.

## Citation

Meyer, M.-C. & Feiman, R. (2021). Composing alternatives: The structural
source of scalar and free choice implicatures. *Journal of Memory and
Language*, 121, 104279.

## Core Contribution

Implicature computation factors into two sub-operations:

1. **ALT-GEN** (alternative generation): Computing what the speaker
   *could have said*
2. **ALT-NEG** (alternative negation): Strengthening by negating the
   un-uttered alternatives

Each sub-operation can independently be **online** (computed during
processing) or **offline** (pre-stored with the lexical entry). This
gives a spectrum of processing architectures:

| Item     | ALT-GEN  | ALT-NEG        | Category      |
|----------|----------|----------------|---------------|
| *some*   | online   | online         | Quantifier    |
| *three*  | offline  | online         | Numeral       |
| FC *or*  | —        | different mech | FC disjunction|

## Experimental Evidence (6 experiments)

Structural priming paradigm: if two expressions share a sub-computation,
processing one facilitates processing the other.

- **Exp 1–2**: *some* → numerals (bidirectional priming)
- **Exp 3–4**: numerals → *some* (bidirectional priming)
- **Exp 5**: FC *or* → *some* (NO priming)
- **Exp 6**: FC *or* → numerals (NO priming)

The pattern falsifies any uniform account: shared ALT-NEG between *some*
and numerals, but FC uses an entirely different mechanism (assertion-based
per Bar-Lev & Fox 2017, not negation-based).

## References

- Bar-Lev, M. E. & Fox, D. (2017). Universal free choice and Innocent
  Inclusion. *SALT 27*.
- Fox, D. (2007). Free choice and the theory of scalar implicatures.
  In Sauerland & Stateva (eds.), *Presupposition and Implicature in
  Compositional Semantics*.
- Chierchia, G. (2004). Scalar implicatures, polarity phenomena, and
  the syntax/pragmatics interface. In Belletti (ed.), *Structures and Beyond*.
-/

namespace Phenomena.ScalarImplicatures.Studies.MeyerFeiman2021


/-! ## Processing Architecture Types -/

/-- How alternatives are made available during processing.

Meyer & Feiman's key theoretical distinction (§1.2, §5):
- `online`: alternatives computed from the Horn scale at processing time
  (e.g., *some* → {*most*, *all*} derived from ⟨some, most, all⟩)
- `offline`: alternatives stored with the lexical entry
  (e.g., *three* → {*one*, *two*, *four*, ...} stored in the numeral system) -/
inductive AltGenSource where
  /-- Computed from Horn scale at processing time -/
  | online
  /-- Pre-stored with lexical entry -/
  | offline
  deriving DecidableEq, BEq, Repr, Inhabited

/-- What is done with alternatives once generated.

The mechanism by which un-uttered alternatives contribute to meaning:
- `exhaustification`: negate alternatives (standard SI: "not all")
- `innocentInclusion`: assert alternatives (FC: "may A ∧ may B")
- `none`: no strengthening operation applies -/
inductive AltNegMechanism where
  /-- IE: negate alternatives (standard scalar implicature) -/
  | exhaustification
  /-- II: assert alternatives (free choice inference) -/
  | innocentInclusion
  /-- No strengthening -/
  | none
  deriving DecidableEq, BEq, Repr, Inhabited

/-- A scalar item's implicature processing profile.

Combines ALT-GEN source and ALT-NEG mechanism to classify how a given
scalar item's implicature is computed. Meyer & Feiman argue that these
two dimensions are independently parameterizable (§5). -/
structure ProcessProfile where
  /-- How alternatives are generated -/
  altGen : AltGenSource
  /-- What is done with alternatives -/
  altNeg : AltNegMechanism
  deriving DecidableEq, BEq, Repr

instance : Inhabited ProcessProfile where
  default := ⟨.online, .exhaustification⟩


/-! ## Scalar Item Classification -/

/-- The three classes of scalar item distinguished by Meyer & Feiman.

The paper argues these are not merely taxonomic labels but reflect genuine
processing differences, as demonstrated by the priming pattern. -/
inductive ScalarItemClass where
  /-- Quantifiers: ALT-GEN online, ALT-NEG online (§2.1) -/
  | quantifier
  /-- Numerals: ALT-GEN offline, ALT-NEG online (§2.2) -/
  | numeral
  /-- Free choice disjunction: different mechanism entirely (§2.3) -/
  | freeChoiceDisjunction
  deriving DecidableEq, BEq, Repr, Inhabited

/-- The process profile for each scalar item class.

This is the paper's central theoretical claim (Table 1, §5). -/
def classProfile : ScalarItemClass → ProcessProfile
  | .quantifier          => ⟨.online, .exhaustification⟩
  | .numeral             => ⟨.offline, .exhaustification⟩
  | .freeChoiceDisjunction => ⟨.online, .innocentInclusion⟩

/-- Concrete scalar items used in the experiments. -/
inductive ScalarItem where
  | some_       -- Experiments 1–6 (target or prime)
  | three       -- Experiments 1–6 (target or prime)
  | four        -- Experiments 1–4
  | fcOr        -- Experiments 5–6 (FC disjunction under modal)
  deriving DecidableEq, BEq, Repr

/-- Classify a concrete item into its class. -/
def itemClass : ScalarItem → ScalarItemClass
  | .some_  => .quantifier
  | .three  => .numeral
  | .four   => .numeral
  | .fcOr   => .freeChoiceDisjunction

/-- Get the process profile for a concrete item. -/
def itemProfile (item : ScalarItem) : ProcessProfile :=
  classProfile (itemClass item)


/-! ## Priming Predictions

Meyer & Feiman's reasoning (§2.3, §5):

- Two items **prime** each other iff they share a sub-computation
- Shared ALT-NEG → cross-category priming (*some* ↔ numerals)
- Different ALT-NEG → no priming (FC ↮ *some*, FC ↮ numerals)
- Shared vs different ALT-GEN → asymmetry in priming strength -/

/-- Whether two scalar item classes share ALT-NEG. -/
def sharesAltNeg (a b : ScalarItemClass) : Bool :=
  (classProfile a).altNeg == (classProfile b).altNeg

/-- Whether two scalar item classes share ALT-GEN. -/
def sharesAltGen (a b : ScalarItemClass) : Bool :=
  (classProfile a).altGen == (classProfile b).altGen

/-- Predicted priming between two classes: occurs iff shared ALT-NEG. -/
def predictsPriming (a b : ScalarItemClass) : Bool :=
  sharesAltNeg a b


/-! ## Experimental Data -/

/-- Result of a structural priming experiment.

Each experiment tests whether processing a scalar implicature with
one item type facilitates processing with another. -/
structure PrimingExperiment where
  /-- Experiment identifier -/
  experiment : String
  /-- Prime scalar item class -/
  primeClass : ScalarItemClass
  /-- Target scalar item class -/
  targetClass : ScalarItemClass
  /-- Was significant priming observed? -/
  primingObserved : Bool
  /-- Number of participants -/
  nParticipants : Nat
  /-- Effect description -/
  effectDescription : String
  deriving Repr

/-- Experiments 1–2: *some* primes numerals. -/
def exp1_2 : PrimingExperiment :=
  { experiment := "Exp 1–2"
  , primeClass := .quantifier
  , targetClass := .numeral
  , primingObserved := true
  , nParticipants := 98
  , effectDescription := "After computing 'some→not all', participants more likely to compute 'three→exactly three'" }

/-- Experiments 3–4: numerals prime *some*. -/
def exp3_4 : PrimingExperiment :=
  { experiment := "Exp 3–4"
  , primeClass := .numeral
  , targetClass := .quantifier
  , primingObserved := true
  , nParticipants := 100
  , effectDescription := "After computing 'three→exactly three', participants more likely to compute 'some→not all'" }

/-- Experiment 5: FC *or* does NOT prime *some*. -/
def exp5 : PrimingExperiment :=
  { experiment := "Exp 5"
  , primeClass := .freeChoiceDisjunction
  , targetClass := .quantifier
  , primingObserved := false
  , nParticipants := 100
  , effectDescription := "FC 'or' computation does not facilitate 'some→not all'" }

/-- Experiment 6: FC *or* does NOT prime numerals. -/
def exp6 : PrimingExperiment :=
  { experiment := "Exp 6"
  , primeClass := .freeChoiceDisjunction
  , targetClass := .numeral
  , primingObserved := false
  , nParticipants := 100
  , effectDescription := "FC 'or' computation does not facilitate 'three→exactly three'" }

/-- All experiments from Meyer & Feiman (2021). -/
def allExperiments : List PrimingExperiment :=
  [exp1_2, exp3_4, exp5, exp6]


/-! ## Key Empirical Findings -/

/-- The three main findings of the paper (§5). -/
structure MainFindings where
  /-- Finding 1: Bidirectional priming between *some* and numerals -/
  someNumeralPriming : Bool
  /-- Finding 2: No priming between FC *or* and *some* -/
  noFCSomePriming : Bool
  /-- Finding 3: No priming between FC *or* and numerals -/
  noFCNumeralPriming : Bool
  deriving Repr

def mainFindings : MainFindings :=
  { someNumeralPriming := true
  , noFCSomePriming := true
  , noFCNumeralPriming := true }


/-! ## Connections to Other Phenomena

The process profile classification connects to several existing
phenomena in linglib. -/

/-- For each scale in the library's basic data, which process profile applies.

This connects Meyer & Feiman's classification to the Horn scale data
in `Phenomena.ScalarImplicatures.Basic`. -/
def scaleProfile (scale : Phenomena.ScalarImplicatures.HornScaleDatum) : ProcessProfile :=
  if scale.name == "Numerals" then
    classProfile .numeral
  else
    classProfile .quantifier

/-- Numeral Hurford rescue (e.g., "three or all") involves the offline/online
    profile — alternatives are stored, so exhaustification ("exactly three")
    is immediately available for Hurford rescue. -/
def hurfordNumeralProfile : ProcessProfile := classProfile .numeral

/-- FC phenomena use a fundamentally different mechanism from standard SI.

This connects to `Phenomena.Modality.FreeChoice`, where the FC inference
◇(A ∨ B) → ◇A ∧ ◇B is derived via Innocent Inclusion rather than
Innocent Exclusion. -/
def freeChoiceProfile : ProcessProfile := classProfile .freeChoiceDisjunction

/-- The asymmetry between SI and FC is a processing architecture difference,
    not just a semantic difference. Both involve alternatives, but:
    - SI: negate alternatives (IE)
    - FC: assert alternatives (II) -/
structure SIvsFCContrast where
  /-- Standard SI mechanism -/
  siMechanism : AltNegMechanism
  /-- FC mechanism -/
  fcMechanism : AltNegMechanism
  /-- Are they the same? -/
  sameMechanism : Bool
  deriving Repr

def siVsFc : SIvsFCContrast :=
  { siMechanism := .exhaustification
  , fcMechanism := .innocentInclusion
  , sameMechanism := false }


/-! ## Falsified Accounts

Meyer & Feiman's data rules out several theoretical positions (§5). -/

/-- Theoretical positions about scalar inference processing. -/
inductive TheoreticalPosition where
  /-- All scalar inferences use the same online computation -/
  | uniformOnline
  /-- All scalar inferences use stored/default meanings -/
  | uniformOffline
  /-- Scalar items differ in ALT-GEN but share ALT-NEG (M&F's position) -/
  | decomposed
  /-- Each scalar item class is fully independent -/
  | fullyIndependent
  deriving DecidableEq, BEq, Repr

/-- Whether a theoretical position is compatible with the priming data. -/
def compatibleWithData (pos : TheoreticalPosition) : Bool :=
  match pos with
  | .uniformOnline =>
    -- Predicts uniform priming across all pairs: falsified by Exp 5–6
    false
  | .uniformOffline =>
    -- Predicts no cross-category priming: falsified by Exp 1–4
    false
  | .decomposed =>
    -- Predicts selective priming (shared ALT-NEG only): confirmed
    true
  | .fullyIndependent =>
    -- Predicts no cross-category priming: falsified by Exp 1–4
    false


end Phenomena.ScalarImplicatures.Studies.MeyerFeiman2021
