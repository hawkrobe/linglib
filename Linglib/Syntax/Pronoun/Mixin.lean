import Linglib.Syntax.Pronoun.Basic
import Linglib.Core.Word

/-!
# The pronoun word-class as a mixin

`PronounLike α` is the lexical word-class interface — a surface form and agreement
φ-features (`UD.MorphFeatures`) — abstracted over carriers, so that the `Pronoun` record,
a `Core.Word`, or a syntactic theory's representation are all treated uniformly. It is the
`[Pronoun α]`-style half of the lexical mixin pair (the binding half is `Binding.Lexicon`):
binding and agreement range over `[PronounLike α]` rather than a concrete pronoun type.

## Main declarations

* `PronounLike` — a carrier with a surface form and φ-features; instances for the `Pronoun`
  record and `Core.Word`.
-/

set_option autoImplicit false

/-- A carrier whose inhabitants are pronoun-like: a surface `form` and agreement φ-features
(`phi : α → UD.MorphFeatures`). The lexical word-class interface, abstracted over carriers
so binding/agreement can range over `[PronounLike α]`. -/
class PronounLike (α : Type) where
  /-- Surface form. -/
  form : α → String
  /-- Agreement φ-features. -/
  phi : α → UD.MorphFeatures

instance : PronounLike Pronoun where
  form := Pronoun.form
  phi := fun p => p.toWord.phi

instance : PronounLike Word where
  form := Word.form
  phi := Word.phi
