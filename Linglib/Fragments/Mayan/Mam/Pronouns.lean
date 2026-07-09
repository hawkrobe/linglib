import Linglib.Syntax.Category.Pronoun.Basic

/-!
# San Juan Atitán Mam Pronouns

Pronoun lexicon for San Juan Atitán Mam (SJA Mam, Mayan), from
[scott-2023] ch. 4, as `PersonalPronoun` values flowing through the
shared Pronoun API. Scott's central claim is that the reduced
subject/possessor forms are true pronouns in argument position — not
agreement markers (contra her own Scott 2020) and not a special clitic
series — so the entries live here rather than in an agreement paradigm.

Two series (Table 4.1 / 4.9, p. 160 / 185): the independent forms
*qini* (= *qin+=i*), *qoy* (= *qo'+=y*), *qo*, *=i*, *qi* (= *q+=i*),
3SG ∅, *qa*, and the reduced subject/possessor forms, where first-person
cells lose their base morphemes (*qin* [+author,+sg], *qo* [+author,−sg],
Table 4.10) via an impoverishment rule conditioned on agreement (§4.4)
while 2nd/3rd cells match the independent series. The disagreement
enclitic *=i* (gloss DISAGR; [noyer-1992], [harbour-2016]; §4.3.3)
realizes disagreeing [±author]/[±participant] values.

## Main declarations

* `Mam.iDisagr`, `Mam.qini`, `Mam.qoy`, `Mam.qo`, `Mam.qi`, `Mam.qa`:
  the pronoun lexical entries.
* `Mam.PronCell` with `.person`, `.number`, `.toPerson`, `.features`,
  `.Disagrees`: the paradigm cells and their φ-feature values.
* `Mam.independent`, `Mam.subjPoss`: the independent and reduced series
  by cell.
* `Mam.enclitic_iff_disagrees`, `Mam.reduction_iff_author`,
  `Mam.reduced_residue`: the enclitic-distribution and reduction
  generalizations, verified across the paradigm.

## Implementation notes

Feature values follow Table 4.4 (p. 183). Harbour's [±participant]
"functions more like a [+/−hearer] or [+/−addressee] feature" (p. 182),
so 1EXCL is [−participant] — this deliberately diverges from
`Person.Features`, whose `wellFormed` invariant (author → participant)
encodes the speech-act-participant convention; hence the fragment-local
`ScottFeatures`. Scott prefers the impoverishment derivation over
"positing a unique series of 'clitic' pronouns" (p. 162), citing the
Agree-affects-pronouns family (Cardinaletti & Starke, Nevins, Kramer,
Stegovec, Yuan). The independent series is "most morphosyntactically
rich" (fn. 2), the 2SG independent form being the enclitic *=i* itself.
Wordhood: *=i* is a morphological enclitic with promiscuous attachment
(nouns, verbs, pronouns, other clitics; allomorphs <i>/<y>, =ni after
[m]); whether *qi*/*qa* are words or enclitics Scott leaves open
(p. 163, her p. 39). None of this is a Cardinaletti–Starke deficiency
classification, so `strength` is left unset throughout.
-/

set_option autoImplicit false

namespace Mam

/-! ### Lexical entries -/

/-- *=i* — the disagreement enclitic pronoun (DISAGR): realizes disagreeing
    [±author]/[±participant] values, so φ-underspecified — it serves 1SG,
    1PL.EXCL, 2SG, and (with the plural piece *q*) 2PL, and doubles as the
    2SG "independent" form (Table 4.11, fn. 2). -/
def iDisagr : PersonalPronoun :=
  { form := "=i", person := none, number := none }

/-- *qini* — 1SG independent pronoun; bimorphemic *qin+=i* (base *qin*
    [+author,+sg] + disagreement enclitic, Table 4.9). -/
def qini : PersonalPronoun :=
  { form := "qini", person := some .first, number := some .singular }

/-- *qoy* — 1PL exclusive independent pronoun; bimorphemic *qo'+=y*
    (base *qo* [+author,−sg] + enclitic; glottalization from the enclitic,
    her fn. 7). -/
def qoy : PersonalPronoun :=
  { form := "qoy", person := some .firstExclusive, number := some .plural, }

/-- *qo* — 1PL inclusive independent pronoun; monomorphemic (1INCL's
    [+author,+participant] values *agree*, so no enclitic). -/
def qo : PersonalPronoun :=
  { form := "qo", person := some .firstInclusive, number := some .plural, }

/-- *qi* — 2PL pronoun, both series; bimorphemic *q+=i* (§4.3.3.2).
    Word-vs-enclitic status left open by Scott (p. 163). -/
def qi : PersonalPronoun :=
  { form := "qi", person := some .second, number := some .plural }

/-- *qa* — 3PL pronoun, both series; also the generic plural marker of the
    language (her (42)–(44)). Word-vs-enclitic status left open. -/
def qa : PersonalPronoun :=
  { form := "qa", person := some .third, number := some .plural }

/-- The clusivity-marked entries satisfy the API's well-formedness invariant
    (clusivity only on 1st-person non-singular). -/
theorem clusive_entries_wellFormed :
    qoy.toPronoun.WellFormed ∧ qo.toPronoun.WellFormed := by
  constructor <;> decide

/-! ### The paradigm -/

/-- A cell of the SJA Mam pronominal paradigm: the quadripartition
    (1EXCL/1INCL/2/3, Table 4.3) crossed with number, minus the principled
    gap *1SG-inclusive (Table 4.4). -/
inductive PronCell where
  | firstSg | firstPlExcl | firstPlIncl
  | secondSg | secondPl
  | thirdSg | thirdPl
  deriving DecidableEq, Repr

/-- PronCell person, in the API's vocabulary. -/
def PronCell.person : PronCell → UD.Person
  | .firstSg | .firstPlExcl | .firstPlIncl => .first
  | .secondSg | .secondPl => .second
  | .thirdSg | .thirdPl => .third

/-- PronCell number, in the API's vocabulary. -/
def PronCell.number : PronCell → UD.Number
  | .firstSg | .secondSg | .thirdSg => .Sing
  | _ => .Plur

/-- PronCell person in the canonical inventory: clusivity rides on the
    person value. -/
def PronCell.toPerson : PronCell → Person
  | .firstSg => .first
  | .firstPlExcl => .firstExclusive
  | .firstPlIncl => .firstInclusive
  | .secondSg | .secondPl => .second
  | .thirdSg | .thirdPl => .third

/-- [scott-2023]'s bivalent φ-features (Table 4.4, after [harbour-2016]):
    [±author], [±participant], [±singular]. Fragment-local because the
    participant convention (≈ [±hearer]: 1EXCL is [−participant]) is
    incompatible with `Person.Features`' author → participant
    invariant. -/
structure ScottFeatures where
  author : Bool
  participant : Bool
  singular : Bool
  deriving DecidableEq, Repr

/-- Feature values per cell — a transcription of Table 4.4. -/
def PronCell.features : PronCell → ScottFeatures
  | .firstSg     => ⟨true,  false, true⟩
  | .firstPlExcl => ⟨true,  false, false⟩
  | .firstPlIncl => ⟨true,  true,  false⟩
  | .secondSg    => ⟨false, true,  true⟩
  | .secondPl    => ⟨false, true,  false⟩
  | .thirdSg     => ⟨false, false, true⟩
  | .thirdPl     => ⟨false, false, false⟩

/-- [±author]/[±participant] values disagree — the condition under which the
    enclitic *=i* is inserted ([noyer-1992]; [scott-2023] §4.3.3). -/
def PronCell.Disagrees (c : PronCell) : Prop :=
  c.features.author ≠ c.features.participant

instance : DecidablePred PronCell.Disagrees := fun c => by
  unfold PronCell.Disagrees; infer_instance

/-- The feature table is faithful to the API-side person values:
    [+author] exactly at first person. -/
theorem author_iff_first (c : PronCell) :
    c.features.author = true ↔ c.person = .first := by
  cases c <;> simp [PronCell.features, PronCell.person]

/-- The feature table is faithful to the API-side number values:
    [+singular] exactly at singular cells. -/
theorem singular_iff_sing (c : PronCell) :
    c.features.singular = true ↔ c.number = .Sing := by
  cases c <;> simp [PronCell.features, PronCell.number]

/-- Independent pronoun by cell (Table 4.1 right column; 3SG has no overt
    pronoun). -/
def independent : PronCell → Option PersonalPronoun
  | .firstSg     => some qini
  | .firstPlExcl => some qoy
  | .firstPlIncl => some qo
  | .secondSg    => some iDisagr
  | .secondPl    => some qi
  | .thirdSg     => none
  | .thirdPl     => some qa

/-- Subject/possessor (reduced) pronoun by cell (Table 4.1 left column):
    first-person bases are bled by impoverishment (§4.4), so 1SG/1PL.EXCL
    surface as bare *=i* and 1PL.INCL as ∅; 2nd/3rd are identical to the
    independent series. -/
def subjPoss : PronCell → Option PersonalPronoun
  | .firstSg     => some iDisagr
  | .firstPlExcl => some iDisagr
  | .firstPlIncl => none
  | .secondSg    => some iDisagr
  | .secondPl    => some qi
  | .thirdSg     => none
  | .thirdPl     => some qa

/-- Morphological-parse data (Table 4.9): the form contains the disagreement
    enclitic. *qini* = *qin+=i*, *qoy* = *qo'+=y*, *qi* = *q+=i*, and *=i*
    itself; *qo* and *qa* contain no enclitic. -/
def bearsEnclitic (p : PersonalPronoun) : Bool :=
  p == iDisagr || p == qini || p == qoy || p == qi

/-! ### Verification theorems -/

/-- Noyer/Scott's disagreement generalization, verified across the whole
    paradigm: a cell's independent form contains *=i* iff its
    [±author]/[±participant] values disagree (Table 4.4 × Table 4.9/4.11). -/
theorem enclitic_iff_disagrees (c : PronCell) :
    (independent c).any bearsEnclitic = true ↔ c.Disagrees := by
  cases c <;> decide

/-- Reduction is exactly first-personhood: the subject/possessor form differs
    from the independent form precisely at [+author] cells (Table 4.1;
    the impoverishment rule targets [+author] under agreement, §4.4). -/
theorem reduction_iff_author (c : PronCell) :
    subjPoss c ≠ independent c ↔ c.features.author = true := by
  cases c <;> decide

/-- What reduction leaves behind is never a base: every reduced (≠ independent)
    cell surfaces as bare *=i* or as ∅ — the enclitic is all that survives
    impoverishment. -/
theorem reduced_residue (c : PronCell) (h : subjPoss c ≠ independent c) :
    subjPoss c = some iDisagr ∨ subjPoss c = none := by
  cases c <;> simp_all [subjPoss, independent] <;> decide

end Mam
