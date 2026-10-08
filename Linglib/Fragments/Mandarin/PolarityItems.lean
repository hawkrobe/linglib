module

public import Linglib.Semantics.Polarity.Licensing

/-!
# Mandarin Polarity-Sensitive Items

Mandarin indefinite polarity items, typed by `PolarityItem`.
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

@[expose] public section

namespace Mandarin.PolarityItems

open PolarityItem

/-! ### Bare interrogatives -/

/-- *shéi* (谁 'who', non-interrogative) — NPI/FCI. The bare
    interrogatives cover the seven non-specific map functions
    ([haspelmath-1997] A.36.3, Fig. A.36); *shéi* is attested in questions
    (A266) and the free-choice span, but direct negation is omitted:
    *?Tā bù xǐhuan shéi* is degraded where *shénme* is perfect (A267,
    [li-1992] p. 150) — that slot belongs to the emphatic series. -/
def shei : PolarityItem :=
  { form := "shéi"
  , licensor := some .weak
  , freeChoice := true
  , licensingContexts :=
      [ .question, .conditionalAntecedent, .clausalComparative
      , .modalPossibility, .modalNecessity, .imperative, .generic ] }

/-- *shénme* (什么 'what', non-interrogative) — NPI/FCI, the same
    seven-function span plus perfect direct negation: *Tā bù xǐhuan
    shénme* 'He does not like anything' (A267); irrealis imperative *Chī
    diǎn shénme zài zǒu ba!* 'Please eat a little something before you
    leave' (A264, [li-1992] p. 152); conditional (A266). -/
def shenme : PolarityItem :=
  { form := "shénme"
  , licensor := some .weak
  , freeChoice := true
  , licensingContexts :=
      [ .negation, .question, .conditionalAntecedent, .clausalComparative
      , .modalPossibility, .modalNecessity, .imperative, .generic ] }

/-! ### The emphatic dōu~yě series -/

/-- *shéi dōu* ~ *shéi yě* (谁都/谁也, with clausemate negation) — the
    emphatic wh + *dōu*~*yě* series: *Tā shéi-dōu bù xìnren* 'She
    doesn't trust anyone' ([li-thompson-1981] p. 528). The two particles
    are interchangeable in the direct-negation function, the series' only
    region on the map, and occur preverbally only ([haspelmath-1997]
    A269, Fig. A.36). The same formation without negation is 'everyone',
    and [haspelmath-1997] (p. 309) leaves open whether the negated uses are
    indefinites or wide-scope universals. -/
def sheiDou : PolarityItem :=
  { form := "shéi dōu"
  , licensor := some .antiMorphic
  , licensingContexts := [.negation] }

/-! ### The free-choice determiner -/

/-- *rènhé* (任何 'any') — free-choice determiner, mainly with the adverb
    *dōu*: free choice under modals (*Rènhé shíhou nǐ dōu kěyǐ lái* 'You
    can come anytime', A270), comparatives (A271, a *bǐ* NP-comparative,
    listed under `clausalComparative` per the covert-clausal routing convention
    of `PolarityItem.LicensingContext`), and direct negation (A272); the
    superordinate-negation use (A273) has no matching context row.
    Etymologically *rèn* 'allow; appoint' + old interrogative *hé* 'what'
    ([haspelmath-1997] A.36.2). -/
def renhe : PolarityItem :=
  { form := "rènhé"
  , licensor := some .weak
  , freeChoice := true
  , licensingContexts := [.negation, .modalPossibility, .clausalComparative] }

/-! ### Verification -/

/-- Every attested context of every entry admits it. -/
theorem mandarin_licensing_sound :
    ∀ e ∈ [shei, shenme, sheiDou, renhe], ∀ c ∈ e.licensingContexts, c.Admits e := by
  simp +decide [shei, shenme, sheiDou, renhe, LicensingContext.Admits]

/-- The emphatic series needs clausemate negation, so it is licensed exactly by the contexts
carrying anti-morphic strength, clausal negation alone among the named contexts. -/
theorem sheiDou_licensing_characterized (c : LicensingContext) :
    c.Licenses sheiDou ↔ c.licenser.Carries .antiMorphic :=
  LicensingContext.licenses_iff_carries rfl (by decide) (by decide)

/-- Direct negation is attested with *shénme* but not with bare *shéi*,
    whose direct-negation slot the emphatic series fills instead. -/
theorem direct_negation_asymmetry :
    .negation ∈ shenme.licensingContexts ∧
      .negation ∉ shei.licensingContexts ∧
      .negation ∈ sheiDou.licensingContexts := by
  refine ⟨by simp [shenme], fun h ↦ ?_, by simp [sheiDou]⟩
  simp only [shei, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h <;>
    exact absurd (congrArg LicensingContext.haspelmath h) (by decide)

end Mandarin.PolarityItems
