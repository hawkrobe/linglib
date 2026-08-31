import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype
import Linglib.Data.Examples.AlbrightHayes2003

/-!
# Albright & Hayes 2003: rules vs. analogy in English past tenses

Morphological knowledge is a set of stochastic rules learned by minimal generalization over
the lexicon, each scored by its reliability (hits over scope, discounted for small scope). The
most reliable rules are *islands of reliability*, and the lexicon has them for regular as well
as irregular changes; the wug ratings of Experiment 2 track them for both — against the dual
mechanism model, whose single default rule leaves novel regulars context-free — while a purely
analogical model, free to use variegated similarity, misses the islands and misassigns the
regular allomorphs.

This file defines `StochasticRule` with its reliability order, the rules the paper reports
(`island_more_reliable`, `gleed_ranking`), the Table 3 cells (`IORCategory`), and reads
Appendix A — every rated past of the 58 wug stems — into cell means: `regulars_ior` and
`irregulars_ior` are the island effects for both past types, `regulars_not_cell_invariant` the
failure of the single-default-rule prediction, `tradeoff` the competition effect of Fig. 3–4,
`analogical_misses_islands` Table 4, and `burnt_underestimated` the rule-based model's one
systematic error. The wug-paradigm vocabulary is declared first.

## References

* [albright-hayes-2003]
* [albright-hayes-2002]
* [berko-1958]
* [pinker-prince-1988]
* [bybee-moder-1983]
* [mikheev-1997]
-/

/-! ### Wug-paradigm vocabulary ([berko-1958])

Shared typed vocabulary for wug studies, homed in the modern reference
paper for gradient wug responses. [berko-1958]
introduced the test as a probe for productive morpho-phonological
knowledge: presented with the nonce *wug*, children produce *wugs*
/wʌgz/ rather than refusing or randomising. A single parametric lens
class `HasFactor` (with lens laws) plus a `Rate` observable lets
studies state the qualitative discriminator between grammar-locus
accounts of productivity (novel forms show a factor gradient:
indexed-constraint [pater-2010], scaled-weight [coetzee-pater-2008])
and listing-locus accounts (novel forms are factor-invariant:
UseListed [zuraw-2000]). -/

namespace Morphology.WugTest

-- ============================================================================
-- §1. Attestation factor
-- ============================================================================

/-- Whether a stimulus is an *attested* lexical item or a *novel*
    (nonce, wug-like) form. The basic categorical contrast that
    [berko-1958] introduced and that every wug paradigm crosses. -/
inductive Attestation where
  | attested
  | novel
  deriving DecidableEq, Repr, Inhabited, Fintype

-- ============================================================================
-- §2. Lens class — the parametric factor schema
-- ============================================================================

/-! Studies' `Cell` types vary in what additional factors they cross
(item, paradigm slot, frequency stratum, IOR membership, …). The
shared minimum is that every wug cell carries some collection of
factors and a way to swap each one without touching others. The lens
laws (`get_set`, `set_get`, `set_set`) make `setFactor` a proper lens;
the paradigm-level predicates rely on them to express "swapping the
factor changes the rate" as a statement that quantifies over the rest
of the cell uniformly.

`HasFactor` takes the codomain `F` as a parameter so that one schema
covers `Attestation` (categorical), `ℝ` (frequency), `Bool` (binary
IOR membership), and any other factor a future study introduces.
Each `Cell` declares one `HasFactor` instance per factor it exposes;
typeclass synthesis routes by the requested `F`. -/

/-- A lens on `Cell` exposing a factor of type `F`. -/
class HasFactor (Cell : Type) (F : Type) where
  factorOf : Cell → F
  setFactor : F → Cell → Cell
  factorOf_setFactor :
      ∀ f c, factorOf (setFactor f c) = f
  setFactor_factorOf :
      ∀ c, setFactor (factorOf c) c = c
  setFactor_setFactor :
      ∀ f₁ f₂ c, setFactor f₁ (setFactor f₂ c) = setFactor f₁ c

/-- `Cell` has an attestation factor that can be swapped without
    touching other factors. The [berko-1958] dimension. -/
abbrev HasAttestation (Cell : Type) := HasFactor Cell Attestation

/-- `Cell` exposes a real-valued frequency factor (e.g. log token
    frequency of the source lexeme; log corpus frequency of an
    analogous attested compound). Frequency is `ℝ`-valued because
    lexical-frequency theories ([coetzee-pater-2008],
    [coetzee-kawahara-2013]) operate on log frequencies as a
    continuous regressor. -/
abbrev HasFrequency (Cell : Type) := HasFactor Cell ℝ

-- ============================================================================
-- §3. Observable
-- ============================================================================

/-- Per-cell numeric outcome — the wug paradigm's primary observable.
    Polymorphic over the codomain `R` so that empirical tables (`ℚ`
    proportions) and theory predictions (`ℝ` log-odds, MaxEnt
    probabilities) can both ride along the same predicate machinery. -/
abbrev Rate (Cell : Type) (R : Type) := Cell → R

-- ============================================================================
-- §4. Paradigm-level qualitative predicates
-- ============================================================================

/-! These predicates state empirical patterns at the paradigm level.
They are written in terms of `setFactor` (the lens), so any `Cell`
type with the relevant `HasFactor` instances can claim them without
re-deriving the universal quantification per study. The predicates
are *abstract*; they express a shape ("novel forms show a factor
gradient") that empirical studies and theoretical models may or may
not satisfy. -/

variable {Cell : Type} {F : Type} {R : Type}

/-- A rate observable shows the *novel-form factor gradient* if,
    holding all other factors constant and fixing `attestation =
    novel`, varying the `F`-typed factor strictly varies the rate.
    This is the prediction of indexed-constraint
    ([pater-2010]), scaled-weight
    ([coetzee-pater-2008]), and representation-strength
    ([moore-cantwell-2021], [smolensky-goldrick-2016])
    theories: novel forms inherit a frequency-conditioned grammar
    pressure from analogous lexical items and therefore show a
    factor gradient even though they are themselves unlisted. -/
def NovelShowsFactorGradient
    [HasAttestation Cell] [HasFactor Cell F] [LT F] [LT R]
    (rate : Rate Cell R) : Prop :=
  ∀ (c : Cell) (f₁ f₂ : F), f₁ < f₂ →
    rate (HasFactor.setFactor f₁ (HasFactor.setFactor Attestation.novel c)) <
    rate (HasFactor.setFactor f₂ (HasFactor.setFactor Attestation.novel c))

/-- A rate observable is *factor-invariant on novel forms* if, holding
    all other factors constant and fixing `attestation = novel`,
    varying the `F`-typed factor leaves the rate unchanged. This is
    the prediction of UseListed ([zuraw-2000]): novel forms have
    no lexical entry, so no entry-keyed factor lookup can affect their
    grammar pressure. The two hypotheses thus make opposite predictions
    on the same paradigm cell. -/
def NovelInvariantInFactor
    [HasAttestation Cell] [HasFactor Cell F]
    (rate : Rate Cell R) : Prop :=
  ∀ (c : Cell) (f₁ f₂ : F),
    rate (HasFactor.setFactor f₁ (HasFactor.setFactor Attestation.novel c)) =
    rate (HasFactor.setFactor f₂ (HasFactor.setFactor Attestation.novel c))

/-- Frequency-specific spelling of `NovelShowsFactorGradient` at
    `F := ℝ`. Kept as an `abbrev` for readability at use sites where
    "frequency gradient" is the linguist-facing terminology. -/
abbrev NovelShowsFreqGradient
    [HasAttestation Cell] [HasFrequency Cell] [LT R]
    (rate : Rate Cell R) : Prop :=
  NovelShowsFactorGradient (F := ℝ) rate

/-- Frequency-specific spelling of `NovelInvariantInFactor` at
    `F := ℝ`. -/
abbrev NovelInvariantInFrequency
    [HasAttestation Cell] [HasFrequency Cell]
    (rate : Rate Cell R) : Prop :=
  NovelInvariantInFactor (F := ℝ) rate

-- ============================================================================
-- §5. Discriminator theorem
-- ============================================================================

/-- The two predictions are *structurally* incompatible: any rate
    observable that satisfies both `NovelShowsFactorGradient` and
    `NovelInvariantInFactor` at the same factor type `F` must have a
    vacuous factor space (no two `F`-distinct values). On any cell
    whose typeclasses permit `f₁ < f₂` for some `F`-typed factors,
    the predicates are mutually exclusive — exactly the discriminator
    a wug paradigm is supposed to provide.

    For binary factors (`F := Bool`), the precondition `f₁ < f₂` is
    discharged automatically by `Bool.false_lt_true`; for real-valued
    factors (`F := ℝ`) any concrete pair like `(0 : ℝ) < 1` works.

    This is the structural source of the empirical claim that wug
    paradigms can adjudicate between grammar-locus and listing-locus
    accounts of productivity: the bridge theorem is a single
    application of this lemma to a study's cell type. -/
theorem novelGradient_inconsistent_with_invariance
    [HasAttestation Cell] [HasFactor Cell F] [LT F] [Preorder R]
    (rate : Rate Cell R)
    (h_grad : NovelShowsFactorGradient (F := F) rate)
    (h_inv  : NovelInvariantInFactor (F := F) rate)
    (c : Cell) (f₁ f₂ : F) (h_lt : f₁ < f₂) : False := by
  exact absurd (h_inv c f₁ f₂) (ne_of_lt (h_grad c f₁ f₂ h_lt))

end Morphology.WugTest

namespace AlbrightHayes2003

open Data.Examples Examples

/-! ### Stochastic rules -/

/-- A past-tense structural change: the three regular suffixes, a vowel change, or no change. -/
inductive PastChange where
  | suffixD
  | suffixT
  | suffixSchwaD
  | vowelChange
  | noChange
  deriving DecidableEq, Repr, Inhabited

def PastChange.isRegular : PastChange → Bool
  | .suffixD | .suffixT | .suffixSchwaD => true
  | .vowelChange | .noChange => false

/-- A stochastic rule: a change with the number of lexicon forms meeting its structural
description (`scope`) and the number on which the change holds (`hits`). -/
structure StochasticRule where
  change : PastChange
  scope : ℕ
  hits : ℕ
  hits_le_scope : hits ≤ scope
  deriving Repr

/-- `r` is less reliable than `s`: its raw confidence, hits over scope, is smaller — the
counts cross-multiplied. The lower-confidence-limit discount the paper applies to raw
confidence ([mikheev-1997], fitted at 0.55) is not formalized. -/
def StochasticRule.LessReliable (r s : StochasticRule) : Prop := r.hits * s.scope < s.hits * r.scope

instance (r s : StochasticRule) : Decidable (r.LessReliable s) := by
  unfold StochasticRule.LessReliable; infer_instance

/-- The general suffixation rule (7a) over the 4253-pair learning set. -/
def generalRule : StochasticRule := ⟨.suffixD, 4253, 4034, by decide⟩

/-- (8): *-t* after a voiceless fricative — every one of the 352 such verbs is regular. -/
def voicelessFricativeRule : StochasticRule := ⟨.suffixT, 352, 352, le_rfl⟩

/-- Table 1: the rules deriving *gleeded*, *gled*, *glode*, and *gleed*. -/
def gleeded : StochasticRule := ⟨.suffixSchwaD, 1234, 1146, by decide⟩
def gled : StochasticRule := ⟨.vowelChange, 7, 6, by decide⟩
def glode : StochasticRule := ⟨.vowelChange, 184, 6, by decide⟩
def gleedUnchanged : StochasticRule := ⟨.noChange, 1234, 29, by decide⟩

/-- An island of reliability outscores the general rule. -/
theorem island_more_reliable : generalRule.LessReliable voicelessFricativeRule := by decide

/-- Table 1's ranking of *gleed*'s pasts by raw confidence. -/
theorem gleed_ranking :
    gleedUnchanged.LessReliable glode ∧ glode.LessReliable gled ∧ gled.LessReliable gleeded := by
  decide

/-! ### The Core design (Table 3) and Appendix A -/

/-- A Core stem's cell: whether it occupies an island of reliability for the regular past and
for some irregular past. -/
structure IORCategory where
  iorForRegular : Bool
  iorForIrregular : Bool
  deriving DecidableEq, Repr

def IORCategory.ofString : String → Option IORCategory
  | "both" => some ⟨true, true⟩
  | "regOnly" => some ⟨true, false⟩
  | "irregOnly" => some ⟨false, true⟩
  | "neither" => some ⟨false, false⟩
  | _ => none

/-- A printed decimal read as an integer of its digits: ratings in hundredths, production
probabilities in thousandths. -/
def digits (s : String) : ℕ :=
  s.toList.foldl (fun n c => if c.isDigit then 10 * n + (c.toNat - '0'.toNat) else n) 0

/-- The Appendix A rows of one past type, in the cells satisfying `p` (Table A2's Peripheral
stems have no cell). -/
def rows (regular : Bool) (p : IORCategory → Bool) : List LinguisticExample :=
  Examples.all.filter fun r =>
    r.feature? "pastType" = some (if regular then "regular" else "irregular") ∧
      ((r.feature? "cell").bind IORCategory.ofString).any p

/-- A row's numeric feature. -/
def value (key : String) (r : LinguisticExample) : ℕ := digits ((r.feature? key).getD "0")

/-- The sum of a numeric feature over rows. -/
def total (key : String) (rs : List LinguisticExample) : ℕ := (rs.map (value key)).sum

/-- The mean of `key` over `A` exceeds its mean over `B`, cross-multiplied. -/
def MeanGT (key : String) (A B : List LinguisticExample) : Prop :=
  total key A * B.length > total key B * A.length

instance (key : String) (A B : List LinguisticExample) : Decidable (MeanGT key A B) := by
  unfold MeanGT; infer_instance

/-- Islands of reliability for regulars: novel regular pasts are rated higher, and volunteered
more often, when the stem occupies an island for the regular change. -/
theorem regulars_ior :
    MeanGT "adjustedRating" (rows true (·.iorForRegular)) (rows true (!·.iorForRegular)) ∧
      MeanGT "production" (rows true (·.iorForRegular)) (rows true (!·.iorForRegular)) := by
  decide

/-- Islands of reliability for irregulars, likewise. -/
theorem irregulars_ior :
    MeanGT "adjustedRating" (rows false (·.iorForIrregular)) (rows false (!·.iorForIrregular)) ∧
      MeanGT "production" (rows false (·.iorForIrregular)) (rows false (!·.iorForIrregular)) := by
  decide

/-- The single-default-rule prediction — novel regular ratings do not vary with the stem's
cell — fails on the Core data: the regulars-only and irregulars-only cells differ. -/
theorem regulars_not_cell_invariant :
    total "adjustedRating" (rows true (· = ⟨true, false⟩)) *
        (rows true (· = ⟨false, true⟩)).length ≠
      total "adjustedRating" (rows true (· = ⟨false, true⟩)) *
        (rows true (· = ⟨true, false⟩)).length := by
  decide

/-- Competition (Figs. 3–4): a past is rated higher when its rival is not in an island —
regulars in the regulars-only cell beat those in the both cell, and in the neither cell beat
those in the irregulars-only cell; irregulars symmetrically. -/
theorem tradeoff :
    MeanGT "adjustedRating" (rows true (· = ⟨true, false⟩)) (rows true (· = ⟨true, true⟩)) ∧
      MeanGT "adjustedRating" (rows true (· = ⟨false, false⟩)) (rows true (· = ⟨false, true⟩)) ∧
      MeanGT "adjustedRating" (rows false (· = ⟨false, true⟩)) (rows false (· = ⟨true, true⟩)) ∧
      MeanGT "adjustedRating" (rows false (· = ⟨false, false⟩))
        (rows false (· = ⟨true, false⟩)) := by
  decide

/-- The rule-based model's predicted regular ratings are higher in the regular islands: the
stimuli were chosen by the model. -/
theorem ruleBased_islands :
    MeanGT "ruleBased" (rows true (·.iorForRegular)) (rows true (!·.iorForRegular)) := by decide

/-- Table 4: on the twelve regular pasts in the best islands the analogical model, unable to
locate structured similarity, scores below both the participants and the rule-based model. -/
theorem analogical_misses_islands :
    ∀ r ∈ Examples.all,
      r.primaryText ∈ ["blafed", "driced", "naced", "teshed", "wissed", "flidged", "bredged",
        "daped", "shilked", "tarked", "spacked", "bligged"] →
      value "analogical" r < value "adjustedRating" r ∧
        value "analogical" r < value "ruleBased" r := by
  decide +kernel

/-- The pseudo-*burnt* irregulars of (15), Table A2. -/
def burnt : List LinguisticExample :=
  Examples.all.filter fun r =>
    r.primaryText ∈ ["grelt", "murnt", "scoilt", "shurnt", "skelt", "snelt", "squilt"]

/-- The rule-based model's one systematic error: it underrates the *burnt*-class forms, which
the analogical model overrates. -/
theorem burnt_underestimated :
    total "ruleBased" burnt < total "adjustedRating" burnt ∧
      total "adjustedRating" burnt < total "analogical" burnt := by
  decide

/-- Participants preferred regular pasts overall. -/
theorem regulars_preferred :
    MeanGT "rating" (Examples.all.filter fun r => r.feature? "pastType" = some "regular")
      (Examples.all.filter fun r => r.feature? "pastType" = some "irregular") := by
  decide

end AlbrightHayes2003
