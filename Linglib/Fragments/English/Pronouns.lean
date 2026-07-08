import Linglib.Data.UD.Basic
import Linglib.Features.Case.Basic
import Linglib.Features.Gender.Basic
import Linglib.Syntax.Category.Pronoun.Basic
import Linglib.Syntax.Category.Pronoun.Capabilities
import Linglib.Syntax.Category.Pronoun.Demonstrative

/-!
# English Pronoun Lexicon Fragment
[konnelly-cowper-2020] [arnold-2026] [balhorn-2004]

Lexical entries for English pronouns. Personal pronouns are values of the
cross-linguistic `PersonalPronoun` object; reflexives, reciprocals, and
wh-pronouns are bare `Pronoun` shells (φ-features + surface form, no referential
denotation of their own).

Each entry declares its `Pronoun.bindingClass`, so a form's binding-theoretic kind
is the entry's own declaration; the lexicon lists below group them by class. `Pronoun.toWord`
threads this onto the surface word's UD morphology (`Reflex`/`PronType`), where the
framework-neutral binding engine reads it back via `Binding.bindingClassOf`.

## Gender ([konnelly-cowper-2020])

Gender is stored directly as `PersonalPronoun.gender : Option Gender`:
*he*/*she*/*it* carry `.masculine`/`.feminine`/`.neuter`; singular *they* — the
Elsewhere/least-specified spellout — and 1st/2nd person carry **no** gender
feature (`none`). Per [konnelly-cowper-2020], *they*'s gender-neutrality is
the *absence* of a contrastive `[MASC]`/`[FEM]`/`[INANIM]` feature, not a positive
value; `none` encodes exactly that. Singular *they* is distinguished from
genderless 1st/2nd person by `person`, not gender. The contrastive-vs-adjunct
feature apparatus that [konnelly-cowper-2020] theorize lives in their study
file, not on this cross-linguistic schema.
-/

namespace English.Pronouns


/-! ### Personal pronouns (`PersonalPronoun`) -/

-- First person (no gender feature). `bindingClass := some .pronoun` is the PersonalPronoun default.
def i : PersonalPronoun := { form := "I", person := some .first, number := some .singular, case_ := some .nom }
def me : PersonalPronoun := { form := "me", person := some .first, number := some .singular, case_ := some .acc }
def we : PersonalPronoun := { form := "we", person := some .first, number := some .plural, case_ := some .nom }
def us : PersonalPronoun := { form := "us", person := some .first, number := some .plural, case_ := some .acc }

-- Second person (no gender feature)
def you : PersonalPronoun := { form := "you", person := some .second, number := some .singular }
def you_pl : PersonalPronoun := { form := "you", person := some .second, number := some .plural }

-- Third person
def he : PersonalPronoun := { form := "he", person := some .third, number := some .singular, case_ := some .nom, gender := some .masculine }
def him : PersonalPronoun := { form := "him", person := some .third, number := some .singular, case_ := some .acc, gender := some .masculine }
def she : PersonalPronoun := { form := "she", person := some .third, number := some .singular, case_ := some .nom, gender := some .feminine }
def her : PersonalPronoun := { form := "her", person := some .third, number := some .singular, case_ := some .acc, gender := some .feminine }
def it : PersonalPronoun := { form := "it", person := some .third, number := some .singular, gender := some .neuter }
def they : PersonalPronoun := { form := "they", person := some .third, number := some .plural, case_ := some .nom }
def them : PersonalPronoun := { form := "them", person := some .third, number := some .plural, case_ := some .acc }

-- Third-person singular *they* ([arnold-2026], [balhorn-2004]): same
-- phonological form and gender-neutral feature as plural *they*, with singular
-- number. Covers both underspecified and personal singular *they*.
def they_sg : PersonalPronoun := { form := "they", person := some .third, number := some .singular, case_ := some .nom }
def them_sg : PersonalPronoun := { form := "them", person := some .third, number := some .singular, case_ := some .acc }

/-! ### Reflexive, reciprocal, and wh pronouns (bare `Pronoun`)

These are not referential pronouns; they carry φ-features and a surface form but
no denotation of their own. Their binding-theoretic kind is the `bindingClass`
each declares (tagged per list below). -/

def myself : Pronoun := { form := "myself", person := some .first, number := some .singular, bindingClass := some .reflexive }
def yourself : Pronoun := { form := "yourself", person := some .second, number := some .singular, bindingClass := some .reflexive }
def himself : Pronoun := { form := "himself", person := some .third, number := some .singular, gender := some .masculine, bindingClass := some .reflexive }
def herself : Pronoun := { form := "herself", person := some .third, number := some .singular, gender := some .feminine, bindingClass := some .reflexive }
def itself : Pronoun := { form := "itself", person := some .third, number := some .singular, gender := some .neuter, bindingClass := some .reflexive }
def ourselves : Pronoun := { form := "ourselves", person := some .first, number := some .plural, bindingClass := some .reflexive }
def yourselves : Pronoun := { form := "yourselves", person := some .second, number := some .plural, bindingClass := some .reflexive }
def themselves : Pronoun := { form := "themselves", person := some .third, number := some .plural, bindingClass := some .reflexive }
def themself : Pronoun := { form := "themself", person := some .third, number := some .singular, bindingClass := some .reflexive }

def eachOther : Pronoun := { form := "each other", bindingClass := some .reciprocal }
def oneAnother : Pronoun := { form := "one another", bindingClass := some .reciprocal }

def who : Pronoun := { form := "who", pronType := some .Int, bindingClass := some .pronoun }
def whom : Pronoun := { form := "whom", case_ := some .acc, pronType := some .Int, bindingClass := some .pronoun }
def what : Pronoun := { form := "what", pronType := some .Int, bindingClass := some .pronoun }
def which : Pronoun := { form := "which", pronType := some .Int, bindingClass := some .pronoun }
def where_ : Pronoun := { form := "where", pronType := some .Int, bindingClass := some .pronoun }
def when_ : Pronoun := { form := "when", pronType := some .Int, bindingClass := some .pronoun }
def why : Pronoun := { form := "why", pronType := some .Int, bindingClass := some .pronoun }
def how : Pronoun := { form := "how", pronType := some .Int, bindingClass := some .pronoun }

/-! ### Demonstrative pronouns (`DemonstrativePronoun`)

Genuine deictic demonstratives — a two-way proximal/distal distance system ([moroney-2021]).
Unlike German *der* (a strong-article personal pronoun, see [patel-grosz-grosz-2017]), these encode
a real spatial contrast, so they are `Demonstrative` carriers. -/

def this_ : DemonstrativePronoun := { form := "this", person := some .third, number := some .singular, deixis := .proximal }
def that_ : DemonstrativePronoun := { form := "that", person := some .third, number := some .singular, deixis := .distal }
def these : DemonstrativePronoun := { form := "these", person := some .third, number := some .plural, deixis := .proximal }
def those : DemonstrativePronoun := { form := "those", person := some .third, number := some .plural, deixis := .distal }

/-- The four English demonstrative pronouns. -/
def demonstratives : List DemonstrativePronoun := [this_, that_, these, those]

/-- Every English demonstrative genuinely encodes a distance contrast (proximal/distal) — they are
    real `Demonstrative`s, the deictic property the morphological "DEM" label does not guarantee. -/
theorem demonstratives_encode_distance :
    ∀ d ∈ demonstratives, (Demonstrative.deixis d).EncodesDistance := by decide

/-! ### Lexicon lists (the kind partition) -/

/-- Reflexive pronouns (Principle A anaphors); each entry declares `bindingClass := .reflexive`. -/
def reflexives : List Pronoun :=
  [myself, yourself, himself, herself, itself, ourselves, yourselves, themselves, themself]

/-- Reciprocal pronouns (bipartite-NP anaphors); each declares `bindingClass := .reciprocal`. -/
def reciprocals : List Pronoun := [eachOther, oneAnother]

/-- Wh-pronouns and wh-adverbs (Principle B pronominals); each declares `bindingClass := .pronoun`. -/
def whWords : List Pronoun := [who, whom, what, which, where_, when_, why, how]

/-- Every reflexive entry is a Principle-A anaphor by its declaration. -/
theorem reflexives_are_anaphors : ∀ p ∈ reflexives, Bound.IsAnaphor p := by decide

/-- Every wh-word projects as wh-marked: the entry's `PronType=Int` reaches the surface
word's morphology (`UD.MorphFeatures.isWh`) through `Pronoun.toWord`. -/
theorem whWords_project_isWh : ∀ p ∈ whWords, p.toWord.features.isWh := by decide

end English.Pronouns

namespace English

/-- The English personal-pronoun inventory: the canonical `List PersonalPronoun`
    handle. Reflexives, reciprocals, and wh-words live in their own
    `English.Pronouns.*` lists. -/
def pronouns : List PersonalPronoun :=
  [Pronouns.i, Pronouns.me, Pronouns.we, Pronouns.us, Pronouns.you, Pronouns.you_pl,
   Pronouns.he, Pronouns.him, Pronouns.she, Pronouns.her, Pronouns.it,
   Pronouns.they, Pronouns.them, Pronouns.they_sg, Pronouns.them_sg]

/-! ### Gender feature facts ([konnelly-cowper-2020], [arnold-2026]) -/

/-- Singular *they* bears no gender feature — the [konnelly-cowper-2020]
    Elsewhere case. -/
theorem they_gender_none : Pronouns.they.gender = none := rfl

/-- Singular and plural *they* share the same (empty) gender feature despite
    differing in number — the structural correlate of [arnold-2026]'s
    observation that underspecified and personal *they* share the ungendered
    morphosyntactic feature. -/
theorem sg_pl_same_gender : Pronouns.they_sg.gender = Pronouns.they.gender := rfl

end English
