/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Data.UD.Basic
import Linglib.Features.Case.Capabilities
import Linglib.Features.Number.Capabilities
import Linglib.Features.Person.Capabilities

/-!
# Word — the morphosyntactic word (ms-word) token
[kalin-bjorkman-etal-2026]

The surface token: the unit that (morpho)syntax treats as a word. Wordhood minimally
splits into the **ms-word** (which this type approximates: a CoNLL-U token is an
orthographic unit, and orthography does not reliably track the ms-word) and the
**p-word** (the prosodic word, `Phonology/Prosody/Word.lean`) — the "one area of
robust consensus" on the wordhood
problem ([kalin-bjorkman-etal-2026] §3.2); we follow the Element in calling ms-words
simply *words*. The split is descriptive, not a Lexicalist commitment: ms-words are
"crucial for lexicalist theories" but used descriptively by non-lexicalist ones too
(§3.2.1, §3.3), and this token carries no theory of how words are formed.

`Word` completes Morphology's word inventory: `Word.Term` (`Word/Term.lean`) is word-*internal* structure,
`Paradigm/Linkage` carries the word-forming correspondence (stem selection + realization), `Word` is the resulting *token* —
form + UD category + one `UD.MorphFeatures` bundle, i.e. a CoNLL-U row. The
ms-word vs p-word typology relating the two word notions ([kalin-bjorkman-etal-2026]
Table 3) is formalized in `Studies/KalinBjorkmanEtAl2026.lean`.

## Main declarations

* `Word` — the token, with its **admission rule** (see the declaration docstring).
* `Word.phi` — the φ-feature projection (person/number/gender).
* `Word.asPassive` — passive variant (voice morphology only; valence effects are
  `DepTree.frames`-level facts).
-/

namespace Morphology

set_option autoImplicit false

/-- A word: the pure CoNLL-U surface token — surface form, UD category, and UD
    morphology (one `UD.MorphFeatures` bundle; there is no separate word-level feature
    record).

    **Admission rule**: a property belongs on `Word` iff a Fragment-free token-level
    engine reads it off the token's *own* data; otherwise it lives on the typed lexical
    carrier (`Pronoun`, `NounEntry`, `Verb`, …) or on the consuming framework's own
    structures (e.g. DG subcategorization premises live on `DepTree.frames`, not here).
    Identity caveat: `BEq` is form + category, so homographs collapse — correct
    surface behavior. Theoretical word identity (which tokens share a lexeme, the
    Same Verb Problem) is relational and owned by the lexeme layer of
    `Paradigm/Linkage`; a CoNLL-U `lemma` field would be corpus disambiguation
    only, added if a corpus consumer needs it. -/
structure Word where
  form : String
  cat : UD.UPOS
  features : UD.MorphFeatures := {}
  deriving Repr

/-- Convenience constructor for a featureless word (form + category only). -/
def Word.mk' (form : String) (cat : UD.UPOS) : Word := { form := form, cat := cat }

/-- The φ-feature subset (person, number, gender) of a word, as a
    `UD.MorphFeatures` bundle. -/
def Word.phi (w : Word) : UD.MorphFeatures :=
  { person := w.features.person, number := w.features.number,
    gender := w.features.gender }

/-- A word bears the number its UD morphology ingests (`Number.fromUD`). -/
instance : HasNumber Word := ⟨fun w => w.features.number.bind Number.fromUD⟩

instance : HasPerson Word := ⟨fun w => w.features.person.map Person.fromUD⟩

instance : HasCase Word := ⟨fun w => w.features.case_.map Case.fromUD⟩

/-- Derive a passive variant: sets voice to passive. The valence change
    (detransitivization) is a frame-level fact carried by the passive analysis on
    `DepTree.frames`, not token data. Composes with `VerbEntry.toWordPastPart`. -/
def Word.asPassive (w : Word) : Word :=
  { w with features := { w.features with voice := some UD.Voice.Pass } }

instance : BEq Word where
  beq w1 w2 := w1.form == w2.form && w1.cat == w2.cat

instance : ToString Word where
  toString w := w.form

/-- Convert a word list to a readable string. -/
def wordsToString (ws : List Word) : String :=
  " ".intercalate (ws.map (·.form))

end Morphology
