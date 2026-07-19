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

The surface token: the unit (morpho)syntax treats as a word, approximating the
ms-word of the ms-word/p-word split ([kalin-bjorkman-etal-2026]; the p-word is
`Phonology/Prosody/Word.lean`). The token carries no theory of how words are
formed: word-internal structure is `Word/Tree.lean`, the word-forming
correspondence `Paradigm/Linkage`.

## Main declarations

* `Word` — the token
-/

namespace Morphology

set_option autoImplicit false

/-- A **word** is a surface token: a form with its UD category and UD
    morphology, as in a CoNLL-U row. A property belongs here only when a
    token-level engine reads it off the token's own data. Homographs collapse
    (`BEq` is form and category); which tokens share a lexeme is relational,
    carried by `Paradigm/Linkage`. -/
structure Word where
  /-- The surface form. -/
  form : String
  /-- The UD category. -/
  cat : UD.UPOS
  /-- The UD morphological features. -/
  features : UD.MorphFeatures := {}
  deriving Repr, DecidableEq

/-- Convenience constructor for a featureless word (form + category only). -/
def Word.mk' (form : String) (cat : UD.UPOS) : Word := { form := form, cat := cat }


/-- A word bears the number its UD morphology ingests (`Number.fromUD`). -/
instance : HasNumber Word := ⟨fun w => w.features.number.bind Number.fromUD⟩

instance : HasPerson Word := ⟨fun w => w.features.person.map Person.fromUD⟩

instance : HasCase Word := ⟨fun w => w.features.case_.map Case.fromUD⟩


instance : BEq Word where
  beq w1 w2 := w1.form == w2.form && w1.cat == w2.cat

instance : ToString Word where
  toString w := w.form


end Morphology
