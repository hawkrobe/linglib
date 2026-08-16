import Linglib.Data.Examples.Baker1985
import Linglib.Morphology.Morphotactics.MirrorPrinciple

/-!
# The Mirror Principle and Morphosyntactic Explanation

Formalization of [baker-1985] (*Linguistic Inquiry* 16(3), 373–415): the Mirror
Principle's predictions verified against the paper's data — Chamorro *fan-* agreement
interacting with passive and causative (§§1, 3.1), the Agreement Restriction (§3.2),
causative-reciprocal ordering in Quechua and Bemba (§4.1), and passive-applicative
ordering in Huichol, Chi-Mwi:ni, and Kinyarwanda (§4.2).

## Main declarations

* `IsAttested`: the Agreement Restriction as empirical data — of Baker's (27) table,
  only inner+semantic (27a) and outer+surface (27d) occur.
* `isAttested_iff_deriveReference`: the Mirror Principle derives the restriction — a
  pattern is attested exactly when its reference is the one derivational timing
  dictates for its position.
* `chamorroPassiveAgreement`, `chamorroCausativeAgreement`, `chamorroCausativePassive`:
  the *fan-* data instantiating both attested patterns and the intermediate-subject
  prediction.
* `quechuaRecipInsideCaus` … `bembaCausInsideRecip`: the §4.1 ordering pairs.
* `huichol`, `chiMwini`, `kinyarwanda`: the applied affix universally inner to the
  passive affix (§4.2).

The glossed stimuli live in `Data/Examples/Baker1985.json` (generated module
`Data.Examples.Baker1985`); each analysis below names its stimulus row.
-/

namespace Baker1985

open Morphology.MirrorPrinciple

/-! ### The Agreement Restriction ([baker-1985] §3.2)

Of the four combinations of agreement position and GF reference, Baker's (27) records
only two as attested: outer agreement referencing surface GFs (27d: by far the most
common — Chamorro person-number agreement, Turkish, Sanskrit, Quechua) and inner
agreement referencing semantic GFs (27a: Chamorro causative *fan-*, with Achenese
agreement and Huichol verb suppletion consistent with it). No clear cases of (27b) or
(27c) are found.

Achenese ((31)) is a defused near-falsifier, not an instance of (27a): its verbal
agreement references semantic subjects under passivization, which would instantiate
the starred (27b) if the passive were marked by a morpheme inner to agreement — but
Achenese has no overt passive morphology, so no morpheme position exists and the
restriction is vacuously satisfied. -/

/-- The attested agreement patterns: exactly inner+semantic (27a) and outer+surface
(27d) of [baker-1985]'s (27). -/
def IsAttested (p : AgreementPattern) : Prop :=
  p = ⟨.inner, .semantic⟩ ∨ p = ⟨.outer, .surface⟩

instance : DecidablePred IsAttested := fun p =>
  inferInstanceAs (Decidable (p = ⟨.inner, .semantic⟩ ∨ p = ⟨.outer, .surface⟩))

/-- The Mirror Principle derives the Agreement Restriction: a pattern is attested
exactly when its GF reference is the one derivational timing dictates for its
position ([baker-1985] (27)). -/
theorem isAttested_iff_deriveReference {p : AgreementPattern} :
    IsAttested p ↔ p.reference = deriveReference p.position := by
  obtain ⟨pos, ref⟩ := p
  cases pos <;> cases ref <;> decide

/-- Every pattern the Mirror Principle derives is attested; no per-position
stipulation is needed. -/
theorem isAttested_derived (pos : AgreementPosition) :
    IsAttested ⟨pos, deriveReference pos⟩ :=
  isAttested_iff_deriveReference.mpr rfl

/-! ### Chamorro ([baker-1985] §§1, 3.1)

Chamorro number agreement *man-* ~ *fan-* registers plurality of the subject; passive
*-in-* promotes the object to subject; causative *na'-* adds a causer as subject
(data from [gibson-1980]).
Which "subject" *fan-* registers tracks its morphological position: outside the
passive marker it references the surface subject, inside the causative marker the
semantic subject. -/

/-- Passive *Para#u#fan-s-in-aolak* 'The children are going to be spanked by their
father': *fan-* outside *-in-* ([fan [in [saolak]]]), so *fan-* was added after
passive and references the derived (surface) subject ([baker-1985] (15b), (21)).
Stimulus row: `Examples.chamorro_15b`. -/
def chamorroPassiveAgreement : AgreementPattern := ⟨.outer, .surface⟩

/-- Causative *Hu#na'-fan-otchu* 'I made them eat': *fan-* inside *na'-*
([na' [fan [otchu]]]), so *fan-* was added before causative and references the
semantic subject of 'eat' ([baker-1985] (15c), (23)). Stimulus row:
`Examples.chamorro_15c`. -/
def chamorroCausativeAgreement : AgreementPattern := ⟨.inner, .semantic⟩

/-- The Chamorro passive pattern is the derived — hence attested — pattern for outer
agreement. -/
theorem chamorroPassiveAgreement_isAttested : IsAttested chamorroPassiveAgreement :=
  isAttested_iff_deriveReference.mpr rfl

/-- The Chamorro causative pattern is the derived — hence attested — pattern for
inner agreement. Together with `chamorroPassiveAgreement_isAttested`, a single
language exhibits both attested patterns, so the Agreement Restriction is a property
of UG, not a language-particular parameter ([baker-1985] §3.1). -/
theorem chamorroCausativeAgreement_isAttested : IsAttested chamorroCausativeAgreement :=
  isAttested_iff_deriveReference.mpr rfl

/-- Causative of passive *Hu#na'-fan-s-in-aolak i famagu'un gi as tata-n-niha* 'I had
the children spanked by their father': passive applies first, then causative; *fan-*
sits between the two GF-rule morphemes and registers the intermediate subject —
post-passive, pre-causative ([baker-1985] (25), (26)). Stimulus row:
`Examples.chamorro_25`. -/
def chamorroCausativePassive : Derivation :=
  [⟨.passive, "-in-"⟩, ⟨.causative, "na'-"⟩]

theorem chamorroCausativePassive_ruleOrder :
    ruleOrder chamorroCausativePassive = [.passive, .causative] := rfl

/-! ### Causative-reciprocal ordering: Quechua and Bemba ([baker-1985] §4.1)

Causative and reciprocal can attach in either order, and the morpheme order
determines the interpretation: whichever rule applies first is computed on the
pre-change grammatical functions. Quechua and Bemba show the same two orders; the
caus-recip order is interpreted differently in the two languages — Quechua links the
causer to the initial patient ((39b)), Bemba to the initial agent ((49b)) — because
Bemba's causative is Chamorro-type: the initial agent, not the patient, occupies the
object position Reciprocal Formation binds ((50)–(52)). Quechua data from
[muysken-1981]; Bemba data from [givon-1976]. -/

/-- *Maqa-naku-ya-chi-n* 'He is causing them to beat each other': reciprocal *-naku*
inside causative *-chi*, so Reciprocal applies first, linking agent and patient of
the root; Causative then adds the causer ([baker-1985] (39a), (45)–(46)). Stimulus
row: `Examples.quechua_39a`. -/
def quechuaRecipInsideCaus : Derivation :=
  [⟨.reflexReciprocal, "-naku"⟩, ⟨.causative, "-chi"⟩]

/-- *Maqa-chi-naku-rka-n* 'They let someone beat each other': causative *-chi* inside
reciprocal *-naku*, so Causative applies first; Reciprocal then links the causers to
the initial patients ([baker-1985] (39b), (47)–(48)). Stimulus row:
`Examples.quechua_39b`. -/
def quechuaCausInsideRecip : Derivation :=
  [⟨.causative, "-chi"⟩, ⟨.reflexReciprocal, "-naku"⟩]

theorem quechuaRecipInsideCaus_ruleOrder :
    ruleOrder quechuaRecipInsideCaus = [.reflexReciprocal, .causative] := rfl

theorem quechuaCausInsideRecip_ruleOrder :
    ruleOrder quechuaCausInsideRecip = [.causative, .reflexReciprocal] := rfl

/-- The two Quechua verb forms differ in rule order: the Mirror Principle ties the
morphological contrast to the interpretive one. -/
theorem quechua_ruleOrders_differ :
    ruleOrder quechuaRecipInsideCaus ≠ ruleOrder quechuaCausInsideRecip := by
  decide

/-- *Naa-mon-an-ya Mwape na Mutumba* 'I made Mwape and Mutumba see each other':
reciprocal *-an* inside causative *-ya* — the same order and interpretation as
Quechua (39a) ([baker-1985] (49a)). Stimulus row: `Examples.bemba_49a`. -/
def bembaRecipInsideCaus : Derivation :=
  [⟨.reflexReciprocal, "-an"⟩, ⟨.causative, "-ya"⟩]

/-- *Mwape na Chilufya baa-mon-eshy-ana Mutumba* 'Mwape and Chilufya made each other
see Mutumba': causative *-eshy* inside reciprocal *-ana*. Causative applies first
and — being Chamorro-type — puts the initial agent in object position, so Reciprocal
links causer and initial agent, unlike Quechua (39b) ([baker-1985] (49b), (52)).
Stimulus row: `Examples.bemba_49b`. -/
def bembaCausInsideRecip : Derivation :=
  [⟨.causative, "-eshy"⟩, ⟨.reflexReciprocal, "-ana"⟩]

theorem bembaRecipInsideCaus_ruleOrder :
    ruleOrder bembaRecipInsideCaus = [.reflexReciprocal, .causative] := rfl

theorem bembaCausInsideRecip_ruleOrder :
    ruleOrder bembaCausInsideRecip = [.causative, .reflexReciprocal] := rfl

/-- Bemba shows the same two rule orders as Quechua: the cross-linguistic difference
lies in the interpretation of the caus-recip order, not in the available orders
([baker-1985] §4.1). -/
theorem bemba_ruleOrders_match_quechua :
    ruleOrder bembaRecipInsideCaus = ruleOrder quechuaRecipInsideCaus ∧
    ruleOrder bembaCausInsideRecip = ruleOrder quechuaCausInsideRecip :=
  ⟨rfl, rfl⟩

/-- Both Quechua orders are acceptable stimuli with distinct interpretations — the
morphological contrast carries an interpretive one, as the Mirror Principle requires. -/
theorem quechua_both_orders_attested :
    Examples.quechua_39a.judgment = .acceptable ∧
    Examples.quechua_39b.judgment = .acceptable ∧
    Examples.quechua_39a.translation ≠ Examples.quechua_39b.translation :=
  ⟨rfl, rfl, by decide⟩

/-- Both Bemba orders are likewise acceptable with distinct interpretations. -/
theorem bemba_both_orders_attested :
    Examples.bemba_49a.judgment = .acceptable ∧
    Examples.bemba_49b.judgment = .acceptable ∧
    Examples.bemba_49a.translation ≠ Examples.bemba_49b.translation :=
  ⟨rfl, rfl, by decide⟩

/-! ### Passive-applicative ordering ([baker-1985] §4.2)

Applicative creates a new direct object ((53)); passive promotes a direct object to
subject ((12)). When an applicative feeds a passive — the applied object becomes the
surface subject — Applicative must apply first, so the Mirror Principle predicts the
applied affix universally closer to the root than the passive affix. Attested:
verb-appl-pass. Unattested: verb-pass-appl with oblique-to-subject promotion.
Huichol data from [comrie-1982], Chi-Mwi:ni from [kisseberth-abasheikh-1977],
Kinyarwanda from [kimenyi-1980]. -/

/-- Huichol *Tiiri yi-nauka-ti nawazi me-puutinanai-ri-yeri* 'Four children were
bought a knife': benefactive *-ri* inside passive *-yeri* ([baker-1985] (55)).
Stimulus row: `Examples.huichol_55`. -/
def huichol : Derivation := [⟨.applicative, "-ri"⟩, ⟨.passive, "-yeri"⟩]

/-- Chi-Mwi:ni *Mwa:limu tet-el-el-a chibu:ku na Nu:ru* 'The teacher was brought the
book by Nuru': applied *-el* inside passive *-a*, with aspect between them
([baker-1985] (56c)). Stimulus rows: `Examples.chimwiini_56c` and the starred
`Examples.chimwiini_56d`. -/
def chiMwini : Derivation := [⟨.applicative, "-el"⟩, ⟨.passive, "-a"⟩]

/-- Kinyarwanda *Ikaramu i-ra-andik-iish-w-a ibaruwa n'umugabo* 'The pen was
written-with the letter by the man': instrumental applicative *-iish* inside passive
*-w* ([baker-1985] (57c)). Stimulus rows: `Examples.kinyarwanda_57c` and
`Examples.kinyarwanda_57d`. -/
def kinyarwanda : Derivation := [⟨.applicative, "-iish"⟩, ⟨.passive, "-w"⟩]

/-- All three languages place the applied affix before the passive affix, as the
feeding order requires. -/
theorem appl_before_pass :
    ruleOrder huichol = [.applicative, .passive] ∧
    ruleOrder chiMwini = [.applicative, .passive] ∧
    ruleOrder kinyarwanda = [.applicative, .passive] :=
  ⟨rfl, rfl, rfl⟩

/-- The Mirror Principle's negative prediction in Chi-Mwi:ni: goal-to-subject promotion
under appl-inside-pass morphology is acceptable ((56c)); reading the same morphology
with patient-to-subject promotion is starred ((56d)), since Passive would then have to
precede Applicative syntactically while following it morphologically. -/
theorem chiMwini_star_contrast :
    Examples.chimwiini_56c.judgment = .acceptable ∧
    Examples.chimwiini_56d.judgment = .ungrammatical :=
  ⟨rfl, rfl⟩

/-- Kinyarwanda's counterpart of the starred Chi-Mwi:ni sentence is grammatical:
Kinyarwanda passive independently promotes either postverbal NP of a double-object
verb ((58)), so (57d) is not a Mirror Principle counterexample. -/
theorem kinyarwanda_57d_acceptable :
    Examples.kinyarwanda_57d.judgment = .acceptable := rfl

end Baker1985
