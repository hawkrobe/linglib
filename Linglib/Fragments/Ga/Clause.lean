/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.Category.Complementizer.Basic
import Linglib.Syntax.Category.Verb.ArgumentFrame.Takes

/-!
# Gã complementizers and embedded clause types

The three complementizers of [allotey-2021] (Gã, ISO 639-3 `gaa`; Kwa, Ghana)
as `Complementizer` entries, and the three-way embedded clause typology they
head, each type with the complement `ArgumentFrame` a verb selecting it records,
together with the subjunctive frame `ni` and `akɛ` share. Complementizer
selection is read off the entries: `akɛ` selects declarative force, `kɛji`
interrogative force, and `ni` irrealis reality status. The pronouns are in
`Fragments/Ga/Pronouns` and the complement-taking verbs in `Fragments/Ga/Verbs`.

## Implementation notes

`ni` records no [noonan-2007] coding: it heads the controlled infinitival
clause and the true subjunctive with a lexical subject alike (ex 105, *Osa
kplɛnɔ ni/akɛ Taki á-tsɛ́ Momo*), the paper's one irrealis complementizer,
so the axis it selects on is the reality status the two codings share.
Likewise `akɛ` records no coding, since the same subjunctive takes it: it is
the finite declarative typer, indifferent to mood. `Complementizer.IsFinite`
reads the verb form, and `ni` keeps the paper's primary characterization of
its clause, non-finite, although the subjunctive it also heads is not.

The paper's finiteness diagnostics (tense restriction, focus fronting, NPI
licensing, negation placement; exx 104–125) all split the `ni`-clause from the
other two, so they are not stored as clause properties: finiteness is read off
the complementizer (`Complementizer.IsFinite`), and each diagnostic is a theorem
over the paper's rows in `Studies/Allotey2021`. The verb-movement diagnostic
(exx 120–125, after [pollock-1989]) needs phrase-structure substrate this
fragment does not carry. Lean does not accept `ɛ` in plain identifiers, so names use Latin
letters (`ake`, `keji`) and the orthography lives in the morphs.

## References

* [allotey-2021]
* [noonan-2007]
* [pollock-1989]
-/

namespace Ga

/-! ### Complementizers -/

/-- *akɛ* — the finite declarative complementizer, typing the complements of
    utterance and attitude verbs (exx 47–49, 89a) in the indicative and, under
    *kplɛnɔ* 'agree', the subjunctive (ex 105). -/
def ake : Complementizer where
  morphs := [.free "akɛ"]
  force := some .declarative
  verbForm := some .Fin

/-- *kɛji* — the finite complementizer of conditional clauses (ex 97a) and,
    under *le* 'know', of polar and alternative questions ('know if they will
    come', 'know whether you or he bought it', exx 104, 108); glossed COND
    throughout the paper. -/
def keji : Complementizer where
  morphs := [.free "kɛji"]
  coding := some .indicative
  force := some .interrogative
  verbForm := some .Fin

/-- *ni* — the irrealis complementizer, glossed C: of the controlled clause,
    whose verb is glossed INF, a weak CP with no focus fronting and no
    independent tense (exx 107–109), and of the true subjunctive with a
    lexical subject (ex 105). Optionally overt with some control verbs (*tao*
    'want', ex 34) and obligatory with others (*hiɛ-kã-nɔ* 'hope', ex 35);
    homophonous with the focus marker (ex 27). -/
def ni : Complementizer where
  morphs := [.free "ni"]
  reality := some .irrealis
  verbForm := some .Inf

/-- The three clause introducers that can head an embedded C (§5.5.1). -/
def complementizers : List Complementizer := [ake, keji, ni]

/-! ### Embedded clause typology -/

/-- The indicative declarative frame `akɛ` types: the library's generic
    `ArgumentFrame.finiteClause`. -/
def akeFrame : ArgumentFrame := .finiteClause

/-- The finite interrogative frame `kɛji` types. -/
def kejiFrame : ArgumentFrame := .typedBy keji

/-- The controlled irrealis frame `ni` types: [noonan-2007]-infinitival, the
    paper's own term, with a subject that is an overt pronoun in the
    subjective (nominative) form of Table 3 — never null and never a lexical
    DP (exx 40–42). -/
def niFrame : ArgumentFrame :=
  ⟨some .nominal, [.clausal (coding := some .infinitive) (reality := ni.reality)
    (embeddedSubject := some (.overt (some .nom)))]⟩

/-- The subjunctive frame of *kplɛnɔ* 'agree' (ex 105): a finite declarative
    irrealis clause with a lexical subject, which `ni` types by its reality
    status and `akɛ` by its force, and `kɛji` does not type. Outside the
    three-way typology. -/
def subjunctiveFrame : ArgumentFrame :=
  ⟨some .nominal, [.clausal (coding := some .subjunctive) (force := ake.force)
    (reality := ni.reality)]⟩

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

/-- The complement frame a verb selecting the clause type records. -/
def frame : EmbeddedClauseType → ArgumentFrame
  | ake => akeFrame
  | keji => kejiFrame
  | ni => niFrame

end EmbeddedClauseType

end Ga
