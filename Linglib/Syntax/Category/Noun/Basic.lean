import Linglib.Syntax.Gender.Capabilities
import Linglib.Morphology.Word.Basic

/-!
# Noun

The noun as a lexical entry: its citation form and its gloss, everything a noun of any
language carries. A proper name extends the entry with the natural gender its pronouns agree
with, where it has one, and projects as a third-person `PROPN` token; it is its own type rather
than a flag on the noun, since a name has no countability or plural and the syntax projects it
as a different head. A language with gender extends the entry with the controller gender in
its own carrier, the gender the language's assignment rules give the noun, and with whether
that gender follows the referent's sex, the one facet every system with a semantic core
reads; the facets particular rules read besides, animacy, rationality, declension class or
accent, are the fields of the fragments' further extensions. The general concept takes the
plain name and the specializations extend it, as in mathlib; a gendered noun bears the
comparative label its carrier does.

## Implementation notes

* A fragment's extension is its own `Noun`, in its namespace; a file that opens that
  namespace qualifies the name, the root `Noun` being in scope too.

## Main declarations

* `Noun` — the noun entry.
* `ProperName` — the entry of a name, with its natural gender and its `Word` token.
* `GenderedNoun G` — the entry with its controller gender over the carrier `G`.
-/

/-- A noun entry: citation form and gloss. -/
structure Noun where
  /-- The citation form. -/
  form : String
  /-- The gloss. -/
  gloss : String
  deriving DecidableEq, Repr

/-- A proper name: a noun that names its referent, with the natural gender its pronouns agree
with, where it has one. -/
structure ProperName extends Noun where
  /-- The natural gender, where the name has one. -/
  gender : Flat Gender := ⊥
  deriving DecidableEq, Repr

instance : HasGender ProperName := ⟨λ n => n.gender⟩

/-- The name as a word token: a third-person `PROPN` with its gender. -/
def ProperName.toWord (n : ProperName) : Morphology.Word :=
  { form := n.form, cat := .PROPN
    features := { person := some .third, gender := n.gender.bind Gender.toUD } }

/-- A noun with its controller gender over the carrier `G`, and whether that gender follows
the referent's sex. -/
structure GenderedNoun (G : Type*) extends Noun where
  /-- The controller gender: the agreements the noun takes. -/
  gender : G
  /-- Whether the gender follows the referent's sex. -/
  isNaturalGender : Bool := false
  deriving DecidableEq, Repr

/-- A gendered noun bears the comparative label of its gender. -/
instance {G : Type*} [HasGender G] : HasGender (GenderedNoun G) := ⟨λ n => genderOf n.gender⟩
