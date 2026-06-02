import Linglib.Core.Word
import Linglib.Features.Case
import Linglib.Features.Gender
import Linglib.Typology.Pronoun.Basic

/-!
# English Pronoun Lexicon Fragment
@cite{konnelly-cowper-2020} @cite{arnold-2026} @cite{balhorn-2004}

Lexical entries for English pronouns. Personal pronouns are values of the
cross-linguistic `PersonalPronoun` object; reflexives, reciprocals, and
wh-pronouns are bare `Pronoun` shells (φ-features + surface form, no referential
denotation of their own).

The pronoun *kind* is encoded by **which lexicon list** a form sits in
(`English.pronouns`, `reflexives`, `reciprocals`, `whWords`) — there is no
per-entry kind tag. Binding theories read
`English.NominalClassification.classifyNominal` (→ `Features.BindingClass`),
dispatching on those lists, rather than any English-local type.

## Gender (@cite{konnelly-cowper-2020})

Gender is stored directly as `PersonalPronoun.gender : Option SurfaceGender`:
*he*/*she*/*it* carry `.masculine`/`.feminine`/`.neuter`; singular *they* — the
Elsewhere/least-specified spellout — and 1st/2nd person carry **no** gender
feature (`none`). Per @cite{konnelly-cowper-2020}, *they*'s gender-neutrality is
the *absence* of a contrastive `[MASC]`/`[FEM]`/`[INANIM]` feature, not a positive
value; `none` encodes exactly that. Singular *they* is distinguished from
genderless 1st/2nd person by `person`, not gender. The contrastive-vs-adjunct
feature apparatus that @cite{konnelly-cowper-2020} theorize lives in their study
file, not on this cross-linguistic schema.
-/

namespace English.Pronouns

open Features (SurfaceGender)

/-! ### Personal pronouns (`PersonalPronoun`) -/

-- First person (no gender feature)
def i : PersonalPronoun := { form := "I", person := some .first, number := some .sg, case_ := some .nom }
def me : PersonalPronoun := { form := "me", person := some .first, number := some .sg, case_ := some .acc }
def we : PersonalPronoun := { form := "we", person := some .first, number := some .pl, case_ := some .nom }
def us : PersonalPronoun := { form := "us", person := some .first, number := some .pl, case_ := some .acc }

-- Second person (no gender feature)
def you : PersonalPronoun := { form := "you", person := some .second, number := some .sg }
def you_pl : PersonalPronoun := { form := "you", person := some .second, number := some .pl }

-- Third person
def he : PersonalPronoun := { form := "he", person := some .third, number := some .sg, case_ := some .nom, gender := some .masculine }
def him : PersonalPronoun := { form := "him", person := some .third, number := some .sg, case_ := some .acc, gender := some .masculine }
def she : PersonalPronoun := { form := "she", person := some .third, number := some .sg, case_ := some .nom, gender := some .feminine }
def her : PersonalPronoun := { form := "her", person := some .third, number := some .sg, case_ := some .acc, gender := some .feminine }
def it : PersonalPronoun := { form := "it", person := some .third, number := some .sg, gender := some .neuter }
def they : PersonalPronoun := { form := "they", person := some .third, number := some .pl, case_ := some .nom }
def them : PersonalPronoun := { form := "them", person := some .third, number := some .pl, case_ := some .acc }

-- Third-person singular *they* (@cite{arnold-2026}, @cite{balhorn-2004}): same
-- phonological form and gender-neutral feature as plural *they*, with singular
-- number. Covers both underspecified and personal singular *they*.
def they_sg : PersonalPronoun := { form := "they", person := some .third, number := some .sg, case_ := some .nom }
def them_sg : PersonalPronoun := { form := "them", person := some .third, number := some .sg, case_ := some .acc }

/-! ### Reflexive, reciprocal, and wh pronouns (bare `Pronoun`)

These are not referential pronouns; they carry φ-features and a surface form but
no denotation of their own. Their binding-theoretic kind is recovered by
`classifyNominal` from list membership, not a stored tag. -/

def myself : Pronoun := { form := "myself", person := some .first, number := some .sg }
def yourself : Pronoun := { form := "yourself", person := some .second, number := some .sg }
def himself : Pronoun := { form := "himself", person := some .third, number := some .sg, gender := some .masculine }
def herself : Pronoun := { form := "herself", person := some .third, number := some .sg, gender := some .feminine }
def itself : Pronoun := { form := "itself", person := some .third, number := some .sg, gender := some .neuter }
def ourselves : Pronoun := { form := "ourselves", person := some .first, number := some .pl }
def yourselves : Pronoun := { form := "yourselves", person := some .second, number := some .pl }
def themselves : Pronoun := { form := "themselves", person := some .third, number := some .pl }
def themself : Pronoun := { form := "themself", person := some .third, number := some .sg }

def eachOther : Pronoun := { form := "each other" }
def oneAnother : Pronoun := { form := "one another" }

def who : Pronoun := { form := "who" }
def whom : Pronoun := { form := "whom", case_ := some .acc }
def what : Pronoun := { form := "what" }
def which : Pronoun := { form := "which" }
def where_ : Pronoun := { form := "where" }
def when_ : Pronoun := { form := "when" }
def why : Pronoun := { form := "why" }
def how : Pronoun := { form := "how" }

/-! ### Lexicon lists (the kind partition) -/

/-- Reflexive pronouns (Principle A anaphors). -/
def reflexives : List Pronoun :=
  [myself, yourself, himself, herself, itself, ourselves, yourselves, themselves, themself]

/-- Reciprocal pronouns (bipartite-NP anaphors). -/
def reciprocals : List Pronoun := [eachOther, oneAnother]

/-- Wh-pronouns and wh-adverbs. -/
def whWords : List Pronoun := [who, whom, what, which, where_, when_, why, how]

end English.Pronouns

namespace English

/-- The English personal-pronoun inventory: the canonical `List PersonalPronoun`
    handle. Reflexives, reciprocals, and wh-words live in their own
    `English.Pronouns.*` lists. -/
def pronouns : List PersonalPronoun :=
  [Pronouns.i, Pronouns.me, Pronouns.we, Pronouns.us, Pronouns.you, Pronouns.you_pl,
   Pronouns.he, Pronouns.him, Pronouns.she, Pronouns.her, Pronouns.it,
   Pronouns.they, Pronouns.them, Pronouns.they_sg, Pronouns.them_sg]

/-! ### Gender feature facts (@cite{konnelly-cowper-2020}, @cite{arnold-2026}) -/

/-- Singular *they* bears no gender feature — the @cite{konnelly-cowper-2020}
    Elsewhere case. -/
theorem they_gender_none : Pronouns.they.gender = none := rfl

/-- Singular and plural *they* share the same (empty) gender feature despite
    differing in number — the structural correlate of @cite{arnold-2026}'s
    observation that underspecified and personal *they* share the ungendered
    morphosyntactic feature. -/
theorem sg_pl_same_gender : Pronouns.they_sg.gender = Pronouns.they.gender := rfl

end English
