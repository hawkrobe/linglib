import Linglib.Core.Word
import Linglib.Features.Case
import Linglib.Features.Register
import Linglib.Features.Prominence
import Linglib.Features.Gender

/-!
# Pronoun

Lexical core for the pronoun as a grammatical object: the general `Pronoun`
structure (the morphosyntactic core every pronoun type shares), the
`PersonalPronoun` schema for personal/referential pronouns (which `extends Pronoun`),
allocutive markers, the `Spec` referent-preference type, and
@cite{cardinaletti-starke-1999}'s `Strength` deficiency classification.

Cross-categorial features a pronoun carries — `Person`, `Number`, `Gender`,
`Case` — are not redefined here; they live under `Features/` and are composed
in as fields of the general `Pronoun`.

## Main declarations

* `Pronoun` — the general pronoun object: surface form + agreement φ-features,
  everything true of *all* pronouns. Specializations `extends` it (mathlib-style:
  the general concept gets the plain name).
* `PersonalPronoun` — personal/referential pronoun: `extends Pronoun` with the
  register and referential-person features specific to deictic pronouns.
* `Pronoun.Strength` — @cite{cardinaletti-starke-1999} strong/weak/clitic
  deficiency order (via `Strength.rank`). Orthogonal to
  @cite{dechaine-wiltschko-2002}'s categorial pro-DP/φP/NP axis; a framework's
  structural account of the order stays in its study file.
* `Pronoun.AllocutiveEntry` — speaker–addressee (allocutive) markers.
* `Pronoun.Spec` — which pronouns a referent uses (@cite{arnold-2026}); a social
  fact about a referent, not a property of the pronoun system.
-/

set_option autoImplicit false

/-- The general pronoun object: the morphosyntactic core shared by every pronoun
    type (personal, indefinite, demonstrative, interrogative, …). Carries only what
    is true of *all* pronouns — surface form and agreement φ-features — and has no
    denotation of its own; each specialization (`PersonalPronoun` for personal/
    referential pronouns, and future `IndefinitePronoun` etc.) `extends` this and
    supplies its own meaning. Coexists with `namespace Pronoun` (a type and a
    namespace may share a name, cf. `List`). -/
structure Pronoun where
  /-- Surface form (romanization or orthographic). -/
  form : String
  /-- Grammatical person (UD.Person via Core.Word abbrev). -/
  person : Option Person := none
  /-- Grammatical number. -/
  number : Option Number := none
  /-- Grammatical case. -/
  case_ : Option Features.Case := none
  /-- Grammatical gender. For 3rd-person pronouns in gendered languages
      (French il/elle, German er/sie/es, …). 1st/2nd-person pronouns and
      languages without pronominal gender leave this `none`. -/
  gender : Option Features.SurfaceGender := none
  /-- Native script form (hangul, kanji, Devanagari, …). -/
  script : Option String := none
  deriving Repr, BEq, DecidableEq

/-- Cross-linguistic *personal/referential* pronoun: the general `Pronoun` object
(form + φ-features) plus the register and referential-person features specific to
deictic pronouns. Covers personal pronouns across all Fragment languages;
any language-specific refinements remain in their respective Fragment files. -/
structure PersonalPronoun extends Pronoun where
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
      @cite{adamson-zompi-2025} -/
  referentialPerson : Option Features.Prominence.PersonLevel := none
  deriving Repr, BEq, DecidableEq

namespace Pronoun

open Features.Register (Level)
open Features (SurfaceGender)

/-! ### Realization as a `Word` -/

/-- The pronoun realized as a `Word`: a `.PRON`-category lexical item carrying the
    entry's φ-features (`person`/`number`/`case_`). The cross-linguistic realization
    every pronoun shares; language-specific refinements (e.g. English wh-words that
    surface as adverbs) stay in the relevant fragment. -/
def toWord (p : Pronoun) : Word :=
  { form := p.form, cat := .PRON,
    features := { person := p.person, number := p.number, case_ := p.case_ } }

/-! ### Structural deficiency (@cite{cardinaletti-starke-1999}) -/

/-- @cite{cardinaletti-starke-1999}'s three pronoun classes, ordered by
    structural deficiency (strong > weak > clitic). Framework-neutral: only the
    ranking lives here, and it is orthogonal to @cite{dechaine-wiltschko-2002}'s
    pro-DP/pro-φP/pro-NP categorial axis. A framework's structural account of
    the ranking stays in its study file (e.g. @cite{patel-grosz-grosz-2017}). -/
inductive Strength where
  /-- Full, stressed forms (e.g., English *me*, French *moi*). -/
  | strong
  /-- Reduced, unstressed but phonologically independent (e.g., German *es*). -/
  | weak
  /-- Phonologically deficient, attached to a host (e.g., French *me*, *te*, *le*). -/
  | clitic
  deriving DecidableEq, Repr

/-- Structural-richness rank: 2 (strong, least deficient) to 0 (clitic, most
    deficient). The @cite{cardinaletti-starke-1999} deficiency hierarchy is the
    reverse order. -/
def Strength.rank : Strength → Nat
  | .strong => 2
  | .weak   => 1
  | .clitic => 0

/-! ### Lexical entry schemas (@cite{alok-bhalla-2026}, @cite{arnold-2026}) -/

/-- Personal pronoun specification — which pronouns a person uses.

    A social-linguistic fact about a *referent* (not a property of the pronoun
    system) that may or may not be in common ground. Independent of grammatical
    gender: a person with known feminine gender may use she/her, they/them, or
    neopronouns. @cite{arnold-2026}: the pragmatic condition for *personal*
    singular *they* is knowing that the referent's personal pronouns are
    *they/them*. -/
inductive Spec where
  | heHim      -- he/him/his
  | sheHer     -- she/her/hers
  | theyThem   -- they/them/theirs
  deriving DecidableEq, Repr, BEq

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
