/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.Category.Pronoun.Basic
import Linglib.Syntax.Category.Complementizer.Basic
import Linglib.Syntax.Category.Verb.Complement.Basic

/-!
# Gã fragment

This file records the Gã (ISO 639-3 `gaa`; Kwa, Ghana) data of [allotey-2021]:
the pronoun paradigm of Table 3 as `PersonalPronoun` entries, the three
complementizers as `Complementizer` entries, the three-way embedded clause
typology they head together with the complement `Frame` each type records, and
the pro-drop profile. The complement-taking verbs are in
`Fragments/Ga/Predicates`.

## Implementation notes

The paper's finiteness diagnostics (tense restriction, focus fronting, NPI
licensing, negation placement; exx 104–125) all split the `ni`-clause from the
other two, so they are not stored as clause properties: finiteness is read off
the complementizer (`Complementizer.IsFinite`), and each diagnostic is a theorem
over the paper's rows in `Studies/Allotey2021`. The verb-movement diagnostic
(exx 120–125, after [pollock-1989]) needs phrase-structure substrate this
fragment does not carry. Lean does not accept `ɛ` or `ŋ` in identifiers, so
names use plain Latin (`ake`, `keji`, `nye`) and the IPA orthography lives in
`form`.

## References

* [allotey-2021]
* [noonan-2007]
* [pollock-1989]
-/

namespace Ga

/-! ### Pronouns -/

/-- The pronoun paradigm of [allotey-2021]'s Table 3. Each person–number cell has
    one elsewhere form realizing the subjective (nominative) and possessive
    columns; only the second and third person singular add a dedicated objective
    form (*bo*, *lɛ*).
    Subject pronouns are proclitics on the inflected verb and cannot be dropped.
    Not recorded: the clipped past-tense 1SG variant *ĩ* and the impersonal
    subject *a*. -/
def pronouns : List PersonalPronoun :=
  [{ form := "mi", person := some .first, number := some .singular },
   { form := "o", person := some .second, number := some .singular },
   { form := "bo", person := some .second, number := some .singular, case_ := some .acc },
   { form := "e", person := some .third, number := some .singular },
   { form := "lɛ", person := some .third, number := some .singular, case_ := some .acc },
   { form := "wɔ", person := some .first, number := some .plural },
   { form := "nyɛ", person := some .second, number := some .plural },
   { form := "amɛ", person := some .third, number := some .plural }]

/-- The subject proclitic of a person–number cell: its elsewhere form. In the
    paper's control examples the embedded subject of a controlled `ni`-clause is
    one of these, never silent; merged with the irrealis high tone the 1SG
    proclitic surfaces as the portmanteau *má* (exx 88, 100). -/
def subjectProclitic? (p : Person) (n : Number) : Option PersonalPronoun :=
  pronouns.find? λ q ↦ q.person == some p && q.number == some n && q.case_ != some .acc

/-! ### Complementizers -/

/-- *akɛ* — the finite declarative complementizer, typing the complements of
    utterance and attitude verbs ([allotey-2021] exx 47–49, 89a). -/
def ake : Complementizer where
  morphs := [.free "akɛ"]
  coding := some .indicative
  force := some .declarative
  verbForm := some .Fin

/-- *kɛji* — the finite complementizer of conditional clauses (ex 97a) and, under
    *le* 'know', of polar and alternative questions ('know if they will come',
    'know whether you or he bought it', exx 104, 108); glossed COND throughout
    the paper. -/
def keji : Complementizer where
  morphs := [.free "kɛji"]
  coding := some .indicative
  force := some .interrogative
  verbForm := some .Fin

/-- *ni* — the irrealis complementizer of controlled clauses, glossed C with the
    complement's verb glossed INF: a weak CP with no focus fronting and no
    independent tense (exx 107–109). Optionally overt with some control verbs
    (*tao* 'want', ex 34) and obligatory with others (*hiɛ-kã-nɔ* 'hope', ex 35);
    homophonous with the focus marker (ex 27). -/
def ni : Complementizer where
  morphs := [.free "ni"]
  coding := some .infinitive
  verbForm := some .Inf

/-- The three clause introducers that can head an embedded C (§5.5.1). -/
def complementizers : List Complementizer := [ake, keji, ni]

/-! ### Embedded clause typology -/

/-- The finite interrogative frame `kɛji` types. -/
def kejiFrame : Frame :=
  [.clausal (coding := some .indicative) (force := some .interrogative)]

/-- The controlled irrealis frame `ni` types: [noonan-2007]-infinitival, the
    paper's own term, with a subject that is an overt proclitic in the
    subjective (nominative) form of Table 3 — never null and never a lexical DP
    (exx 40–42). -/
def niFrame : Frame :=
  [.clausal (coding := some .infinitive) (embeddedSubject := some (.overt (some .nom)))]

/-- The three embedded clause types of [allotey-2021], named by the
    complementizer heading them (§5.5.1). The `ni` type is the controlled
    irrealis clause; `ni` also introduces true subjunctives with lexical subjects
    (ex 105) and, under *dwɛŋ* 'think', finite low-tone complements
    (exx 110–111), which are not of this type. -/
inductive EmbeddedClauseType where
  | ake
  | keji
  | ni
  deriving DecidableEq, Repr

namespace EmbeddedClauseType

/-- The complementizer heading the clause type. -/
def complementizer : EmbeddedClauseType → Complementizer
  | ake => Ga.ake
  | keji => Ga.keji
  | ni => Ga.ni

/-- The complement frame a verb selecting the clause type records; `akɛ` types
    the generic finite declarative. -/
def frame : EmbeddedClauseType → Frame
  | ake => Frame.finiteClause
  | keji => kejiFrame
  | ni => niFrame

end EmbeddedClauseType

/-! ### Typological profile -/

/-- Gã does not allow null pronominal subjects in matrix clauses: every clause
    requires an overt subject proclitic ([allotey-2021]). -/
def allowsProDrop : Bool := false

end Ga
