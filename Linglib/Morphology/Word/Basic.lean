/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Data.UD.UPOS
public import Linglib.Morphology.Word.Features

/-!
# Word tokens

The surface token: the unit (morpho)syntax treats as a word, approximating the
ms-word of the ms-word/p-word split ([kalin-bjorkman-etal-2026]; the p-word is
`Phonology/Prosody/Word.lean`). The token carries no theory of how words are
formed: word-internal structure is `Word/Tree.lean`, the word-forming
correspondence `Paradigm/Linkage`. A property belongs on the token only when a
token-level engine reads it off the token's own data.
-/

@[expose] public section

namespace Morphology

/-- A word token is a surface form with its category, in the Universal Dependencies
inventory, and its features. -/
structure Word where
  /-- The surface form. -/
  form : String
  /-- The category. -/
  cat : UD.UPOS
  /-- The features. -/
  features : Features := ⊥
  deriving Repr, DecidableEq

/-- The featureless word with the given form and category. -/
def Word.mk' (form : String) (cat : UD.UPOS) : Word := { form := form, cat := cat }



/-- Words compare by form and category, ignoring features, so homographs
collapse. -/
instance : BEq Word where
  beq w1 w2 := w1.form == w2.form && w1.cat == w2.cat

instance : ToString Word where
  toString w := w.form


end Morphology
