/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Data.UD.Features

/-!
# Tense forms

This file defines tense forms. A tense form of a verb, in the sense of the traditional grammars,
is a member of the verb's tense paradigm, such as the German *Präteritum* and *Perfekt* or the
English simple past and past progressive. It is described here by its make-up, the tense
inflection of its finite verb and the nonfinite forms stacked under that verb. A synthetic form
has a finite lexical verb and nothing else; a periphrastic form has a finite auxiliary over
participles or infinitives, the lexical verb last. Which tense and which aspect a form expresses
is a matter of analysis and is left to studies.

## Main declarations

* `Tense.Form.Nonfinite` — the nonfinite verb forms that build periphrastic tense forms.
* `Tense.Form` — a tense form, by the inflection of its finite verb and its nonfinite chain.
* `Tense.Form.IsSynthetic` — the form consists of a finite lexical verb alone.
-/

namespace Tense

/-- A nonfinite verb form in a periphrastic tense form. -/
inductive Form.Nonfinite where
  /-- The infinitive, as German *bauen* under *werden*. -/
  | infinitive
  /-- The present participle, as English *building* under *be*. -/
  | presentParticiple
  /-- The past participle, as English *built* under *have* and German *gebaut* under *haben*. -/
  | pastParticiple
  deriving DecidableEq, Repr, Inhabited

/-- A tense form of a verb consists of its traditional name, the tense inflection of its finite
verb, and the nonfinite forms under the finite verb, outermost first, so that the lexical verb
is the last of them, or the finite verb itself when there are none. -/
structure Form where
  /-- The traditional name of the form. -/
  name : String
  /-- The tense inflection of the finite verb. -/
  finite : UD.Tense
  /-- The nonfinite forms under the finite verb, outermost first. -/
  nonfinite : List Form.Nonfinite := []
  deriving DecidableEq, Repr

namespace Form

/-- A synthetic form is a finite lexical verb with no auxiliary. -/
def IsSynthetic (f : Form) : Prop := f.nonfinite = []

instance : DecidablePred IsSynthetic := fun f ↦ inferInstanceAs (Decidable (f.nonfinite = []))

end Form

end Tense
