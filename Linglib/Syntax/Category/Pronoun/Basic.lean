import Mathlib.Order.Nat
import Linglib.Data.UD.Basic
import Linglib.Features.Case.Basic
import Linglib.Features.Register
import Linglib.Features.Prominence
import Linglib.Features.Gender.Basic
import Linglib.Features.Clusivity
import Linglib.Features.CoreferenceStatus
import Linglib.Features.Person.Decomposition
import Linglib.Morphology.Word.Basic

open Morphology (Word)

/-!
# Pronoun

Lexical core for the pronoun as a grammatical object: the general `Pronoun`
structure (the morphosyntactic core every pronoun type shares), the
`PersonalPronoun` schema for personal/referential pronouns (which `extends Pronoun`),
allocutive markers, and [cardinaletti-starke-1999]'s `Strength` deficiency
classification.

Cross-categorial features a pronoun carries — person, number, gender,
`Case` — are not redefined here; they live under `Features/` and are composed
in as fields of the general `Pronoun`.

## Main declarations

* `Pronoun` — the general pronoun object: surface form + agreement φ-features,
  everything true of *all* pronouns. Specializations `extends` it (mathlib-style:
  the general concept gets the plain name).
* `PersonalPronoun` — personal/referential pronoun: `extends Pronoun` with the
  register and referential-person features specific to deictic pronouns.
* `Pronoun.Strength` — [cardinaletti-starke-1999] strong/weak/clitic
  deficiency scale, a `LinearOrder` (`clitic < weak < strong`), carried
  per-series by `Pronoun.strength`. Orthogonal to
  [dechaine-wiltschko-2002]'s categorial pro-DP/φP/NP axis; a framework's
  structural account of the order stays in its study file.
* `Pronoun.AllocutiveEntry` — speaker–addressee (allocutive) markers.
-/


set_option autoImplicit false

/-! ### Structural deficiency ([cardinaletti-starke-1999]) -/

/-- [cardinaletti-starke-1999]'s three pronoun classes, linearly ordered by
    structural deficiency: `clitic < weak < strong` (more structure = greater;
    C&S's morphological asymmetry is exactly this chain). The classes are
    structural/distributional — clitic = deficient head, weak = deficient
    phrase, strong = non-deficient phrase; (un)stressedness is explicitly
    *not* the defining property (C&S document stressed deficients and
    unstressed strongs). Framework-neutral: only the scale lives here; a
    framework's structural account of it stays in its study file (e.g.
    [patel-grosz-grosz-2017]), and it is orthogonal to
    [dechaine-wiltschko-2002]'s pro-DP/pro-φP/pro-NP categorial axis.
    [cetnarowska-2004] and [jung-migdalski-2022] refine the scale four ways
    (splitting `strong` into stressed/unstressed); that refinement and its
    monotone collapse onto this scale live with those studies. -/
inductive Pronoun.Strength where
  /-- Deficient and a *head* (X°) at surface structure: verb-adjacent,
      clustering, prosodically dependent (Italian *lo*, French *le*, Slovak
      *mu*). Bottom of the scale. -/
  | clitic
  /-- Deficient but a *maximal projection*: confined to derived XP positions,
      non-coordinable, yet a prosodic word of its own (German *es*, Slovak
      *ono*, Italian dative *loro*). -/
  | weak
  /-- Non-deficient maximal projection: full structure — coordinable,
      c-modifiable, possible in θ- and peripheral positions, bears its own
      range restriction (Italian/French *lui*, Slovak *jemu*). Top of the
      scale. -/
  | strong
  deriving DecidableEq, Repr

namespace Pronoun.Strength


/-- Numeric embedding into ℕ preserving the deficiency order. -/
def toNat : Strength → Nat
  | .clitic => 0
  | .weak   => 1
  | .strong => 2

instance : LinearOrder Strength :=
  LinearOrder.lift' toNat
    (fun a b h => by cases a <;> cases b <;> simp_all [toNat])

/-- A clitic is more deficient than a weak pronoun. -/
theorem clitic_lt_weak : (.clitic : Strength) < .weak := by decide

/-- A weak pronoun is more deficient than a strong one. -/
theorem weak_lt_strong : (.weak : Strength) < .strong := by decide

/-- `clitic` is the most deficient class. -/
theorem clitic_le (s : Strength) : .clitic ≤ s := by cases s <;> decide

/-- `strong` is the least deficient class. -/
theorem le_strong (s : Strength) : s ≤ .strong := by cases s <;> decide

end Pronoun.Strength

/-- The general pronoun object: the morphosyntactic core shared by every pronoun
    type (personal, indefinite, demonstrative, interrogative, …). Carries what is true
    of *all* pronouns — surface form, agreement φ-features, and a binding-theoretic
    `bindingClass` *slot* (the Principle A/B/C role every pronoun has; `none` on the bare
    base, *fixed by the kind*: `PersonalPronoun` defaults it, reflexive/reciprocal shells
    declare it) — and has no denotation of its own; each specialization (`PersonalPronoun`
    for personal/
    referential pronouns, and future `IndefinitePronoun` etc.) `extends` this and
    supplies its own meaning. Coexists with `namespace Pronoun` (a type and a
    namespace may share a name, cf. `List`). -/
structure Pronoun where
  /-- Surface form (romanization or orthographic). -/
  form : String
  /-- Grammatical person — the canonical analytical inventory (root
      `Person`). Clusivity is carried as a person value: Tagalog *tayo* =
      `firstInclusive`, *kami* = `firstExclusive`; English *we* = plain
      `first` ([cysouw-2009]). -/
  person : Option Person := none
  /-- Grammatical number — the canonical analytical inventory (root
      `Number`); UD realization via `Number.toUD` (partial: the
      minimal/augmented values have no UD tag). -/
  number : Option Number := none
  /-- Grammatical case. -/
  case_ : Option Case := none
  /-- Grammatical gender. For 3rd-person pronouns in gendered languages
      (French il/elle, German er/sie/es, …). 1st/2nd-person pronouns and
      languages without pronominal gender leave this `none`. -/
  gender : Option Gender := none
  /-- Native script form (hangul, kanji, Devanagari, …). -/
  script : Option String := none
  /-- Pronoun type (UD `PronType`): the pro-form's lexical kind — personal (`Prs`),
      interrogative (`Int`), relative (`Rel`), demonstrative (`Dem`), … Real UD morphology,
      threaded onto the projected word by `toWord`; doubles as the lexical-kind axis the
      capability tower deferred. Reciprocal (`Rcp`) is *not* stored: `toWord` derives it
      from `bindingClass = .reciprocal`. `none` where unspecified. -/
  pronType : Option UD.PronType := none
  /-- The binding class this pro-form declares — its `Features.BindingSource Pronoun` value:
      Principle A anaphor (`.reflexive`/`.reciprocal`), B pronominal (`.pronoun`), or C
      R-expression. *One* source of an expression's binding class — the lexical declaration
      ([chomsky-1981]'s GB classes); the binding engine is polymorphic over `BindingSource`, so
      a theory may instead source the class structurally or from context. `none` for a bare
      φ-shell. -/
  bindingClass : Option Features.BindingClass := none
  /-- [cardinaletti-starke-1999] deficiency class of the form-*series* this entry
      represents, when the series is homogeneous (an Italian object clitic
      `some .clitic`, French *lui* `some .strong`). `none` = unrecorded, or no
      stable class ([jung-migdalski-2022]'s double-duty forms). Consumers
      condition on `some`; there is no default class — C&S's deficient-as-default
      ("Minimize Structure") is a refutable theory claim, not API. -/
  strength : Option Pronoun.Strength := none
  deriving Repr, BEq, DecidableEq

/-- Cross-linguistic *personal/referential* pronoun: the general `Pronoun` object
(form + φ-features) plus the register and referential-person features specific to
deictic pronouns. Covers personal pronouns across all Fragment languages;
any language-specific refinements remain in their respective Fragment files. -/
structure PersonalPronoun extends Pronoun where
  /-- Personal pronouns are Principle-B pronominals: the *type* fixes the binding class
      ([chomsky-1981]), overriding `Pronoun`'s `none` default so entries needn't restate it. -/
  bindingClass := some .pronoun
  /-- Personal pronouns are UD `PronType=Prs`; the *type* fixes the morphology. -/
  pronType := some UD.PronType.Prs
  /-- Register level (formality/honorifics). Binary T/V systems use
      `.informal`/`.formal`; ternary honorific systems (Hindi, Magahi,
      Maithili, Korean) use all three levels. -/
  register : Features.Register.Level := .informal
  /-- Referential person — who the pronoun refers to in terms of discourse
      role — when it diverges from formal/agreement person. For polite
      pronouns (Italian LEI, Spanish USTED, German SIE), the formal `person`
      field is 3rd (governing agreement, clitic allomorphy, reflexive binding),
      while `referentialPerson` is 2nd (governing the PCC, Fancy Constraint,
      resolved agreement). For ordinary pronouns, leave as `none` —
      referential person coincides with formal person.
      [adamson-zompi-2025] -/
  referentialPerson : Option Person := none
  deriving Repr, BEq, DecidableEq

namespace Pronoun

open Features.Register (Level)

/-! ### Realization as a `Word` -/

/-- The pronoun realized as a `Word`: a `.PRON`-category lexical item carrying the
    entry's φ-features (`person`/`number`/`case_`). The cross-linguistic realization
    every pronoun shares; language-specific refinements (e.g. English wh-words that
    surface as adverbs) stay in the relevant fragment. -/
def toWord (p : Pronoun) : Word :=
  { form := p.form, cat := .PRON,
    features := { person := p.person.map Person.toUD,
                  number := p.number.bind Number.toUD,
                  case_ := p.case_.map Case.toUD,
                  gender := p.gender.bind (·.toUD),
                  -- carry the binding-relevant morphology so a projected pro-form's class is
                  -- read off its own features, not recovered by surface-form lookup
                  reflex := p.bindingClass == some .reflexive,
                  pronType := if p.bindingClass == some .reciprocal then some .Rcp
                              else p.pronType } }

/-! ### Derived person category and well-formedness ([cysouw-2009]) -/

/-- The [cysouw-2009] `Category` this pronoun's person + number realizes,
    when fully specified — the neutral typological view of its
    person-reference, *derived* (not stored). `none` when person/number is
    underspecified, or for a clusivity-unmarked first-person plural (plain
    `first`, a syncretism over `.minIncl`/`.augIncl`/`.excl`, e.g. English
    *we*). -/
def category (p : Pronoun) : Option Person.Category :=
  match p.person, p.number with
  | some per, some num => Person.Category.ofPersonNumber per num
  | _, _ => none

/-- Well-formedness of a pronoun's φ-features: clusivity is borne only by a
    first-person non-singular (dual/plural) form — the inclusive/exclusive split
    of the 1st-person plural/dual ([cysouw-2009]). This is the invariant a
    person-value type tower would have enforced, carried as a *predicate* (the
    mathlib way) so illegal states are catchable without fragmenting the type. -/
def WellFormed (p : Pronoun) : Prop :=
  ∀ per, p.person = some per → per.MarksClusivity →
    p.number = some .dual ∨ p.number = some .plural ∨
    p.number = some .minimal ∨ p.number = some .augmented

instance (p : Pronoun) : Decidable p.WellFormed := by
  unfold WellFormed; infer_instance

/-! ### Lexical entry schemas ([alok-bhalla-2026]) -/

/-- Cross-linguistic allocutive marker entry.

Covers verbal suffixes, particles, and clitics that realize allocutive
agreement across all Fragment languages. -/
structure AllocutiveEntry where
  /-- Surface form of the marker -/
  form : String
  /-- Register level (matching PersonalPronoun.register scale) -/
  register : Level
  /-- Gloss string (e.g., "IMP.NH", "POL", "2sg.DAT.fam") -/
  gloss : String
  deriving Repr, BEq

end Pronoun
