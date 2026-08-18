import Linglib.Semantics.Polarity.Licensing

/-!
# Mandarin Polarity-Sensitive Items

Mandarin indefinite polarity items, typed by `Polarity.Item`.
The system has three layers: the bare interrogatives (*shéi* 谁 'who',
*shénme* 什么 'what') serve as indefinites in all non-specific
non-emphatic functions — seven of the nine implicational-map functions,
irrealis through free choice; the emphatic wh + *dōu*~*yě* series
('even, also; every, all') is interchangeable between the two particles,
restricted to the direct-negation function, and preverbal only; and the
free-choice determiner *rènhé* 任何 'any' occurs mainly with *dōu*.

Per-item asymmetries are encoded per entry: under direct negation only
*shénme* is perfect while bare *shéi* is degraded, and the survey
reports no indirect-negation data for the bare interrogatives, so no
entry lists those contexts.

## References

* [haspelmath-1997], §A.36, Fig. A.36
* [li-1992]
* [li-thompson-1981], pp. 528–530
-/

namespace Mandarin.PolarityItems

open Polarity

/-! ### Bare interrogatives -/

/-- *shéi* (谁 'who', non-interrogative) — NPI/FCI. The bare
    interrogatives cover the seven non-specific map functions
    ([haspelmath-1997] A.36.3, Fig. A.36); *shéi* is attested in questions
    (A266) and the free-choice span, but direct negation is omitted:
    *?Tā bù xǐhuan shéi* is degraded where *shénme* is perfect (A267,
    [li-1992] p. 150) — that slot belongs to the emphatic series. -/
def shei : Item :=
  { form := "shéi (谁, non-interrog.)"
  , licensor := some .weak
  , freeChoice := true
  , baseForce := .existential
  , licensingContexts :=
      [ .question, .conditionalAntecedent, .clausalComparative
      , .modalPossibility, .modalNecessity, .imperative, .generic ]
  , scalarDirection := some .strengthening }

/-- *shénme* (什么 'what', non-interrogative) — NPI/FCI, the same
    seven-function span plus perfect direct negation: *Tā bù xǐhuan
    shénme* 'He does not like anything' (A267); irrealis imperative *Chī
    diǎn shénme zài zǒu ba!* 'Please eat a little something before you
    leave' (A264, [li-1992] p. 152); conditional (A266). -/
def shenme : Item :=
  { form := "shénme (什么, non-interrog.)"
  , licensor := some .weak
  , freeChoice := true
  , baseForce := .existential
  , licensingContexts :=
      [ .negation, .question, .conditionalAntecedent, .clausalComparative
      , .modalPossibility, .modalNecessity, .imperative, .generic ]
  , scalarDirection := some .strengthening }

/-! ### The emphatic dōu~yě series -/

/-- *shéi dōu* ~ *shéi yě* (谁都/谁也, with clausemate negation) — the
    emphatic wh + *dōu*~*yě* series: *Tā shéi-dōu bù xìnren* 'She
    doesn't trust anyone' ([li-thompson-1981] p. 528). The two particles
    are interchangeable in the direct-negation function, the series' only
    region on the map, and occur preverbally only ([haspelmath-1997]
    A269, Fig. A.36). `baseForce` is universal: the same formation
    without negation is 'everyone', and [haspelmath-1997] (p. 309) leaves
    open whether the negated uses are indefinites or wide-scope
    universals. -/
def sheiDou : Item :=
  { form := "shéi dōu/yě (谁都/谁也, neg)"
  , licensor := some .antiMorphic
  , baseForce := .universal
  , licensingContexts := [.negation]
  , scalarDirection := some .strengthening
  , morphology := .indefPlusEven }

/-! ### The free-choice determiner -/

/-- *rènhé* (任何 'any') — free-choice determiner, mainly with the adverb
    *dōu*: free choice under modals (*Rènhé shíhou nǐ dōu kěyǐ lái* 'You
    can come anytime', A270), comparatives (A271, a *bǐ* NP-comparative,
    listed under `clausalComparative` per the covert-clausal routing convention
    of `Polarity.LicensingContext`), and direct negation (A272); the
    superordinate-negation use (A273) has no matching context row.
    Etymologically *rèn* 'allow; appoint' + old interrogative *hé* 'what'
    ([haspelmath-1997] A.36.2). -/
def renhe : Item :=
  { form := "rènhé (任何)"
  , licensor := some .weak
  , freeChoice := true
  , baseForce := .existential
  , licensingContexts := [.negation, .modalPossibility, .clausalComparative]
  , scalarDirection := some .strengthening }

/-! ### Verification -/

/-- Every attested context of every entry is predicted licensed. -/
theorem mandarin_licensing_sound :
    ∀ e ∈ [shei, shenme, sheiDou, renhe], ∀ c ∈ e.licensingContexts,
      c.licenses e := by decide

/-- The licensing keystone characterizes the emphatic series exactly: its
    anti-morphic licensor makes clausal negation the only licensing row,
    matching its direct-negation-only distribution. -/
theorem sheiDou_licensing_characterized :
    ∀ c, c.licenses sheiDou ↔ c ∈ sheiDou.licensingContexts := by decide

/-- Direct negation is attested with *shénme* but not with bare *shéi*,
    whose direct-negation slot the emphatic series fills instead. -/
theorem direct_negation_asymmetry :
    .negation ∈ shenme.licensingContexts ∧
      .negation ∉ shei.licensingContexts ∧
      .negation ∈ sheiDou.licensingContexts := by decide

end Mandarin.PolarityItems
