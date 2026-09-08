import Linglib.Syntax.Category.Pronoun.Basic
import Linglib.Syntax.Category.Pronoun.Capabilities
import Linglib.Syntax.Reciprocal

/-!
# Reciprocal pronouns — the pronominal exponent of reciprocity

The pronoun member of the reciprocal series: `ReciprocalPronoun` extends the general `Pronoun`
with the marker data of `Syntax/Reciprocal.lean`, the nominal strategy it realizes and the
readings it covers, and fixes the Principle-A reciprocal binding class. A fragment writes the
pronoun once and derives its `Reciprocal.Marker` entry with `toMarker`; Hungarian *egymás*,
Japanese *otagai* and Wan *ɔ̄ŋ̄* are such objects. Verbal and clitic reciprocal strategies are
not pronouns and stay bare markers.

## Main declarations

* `ReciprocalPronoun` — the lexical object (`extends Pronoun` + `strategy` + `readings`).
* `ReciprocalPronoun.toMarker` — its entry in a marker inventory.
* `HasPhi` / `Proform` / `Bound` instances routing the object through the Pronoun API.
-/

/-- A reciprocal pronoun: the general `Pronoun` (surface `form` + φ-features) as the nominal
    exponent of reciprocity, with the strategy it realizes and the readings it covers. The
    kind fixes the Principle-A reciprocal binding class, so entries need not restate it. -/
structure ReciprocalPronoun extends Pronoun where
  bindingClass := some .reciprocal
  /-- The nominal strategy: a dedicated pronoun (*egymás*, *otagai*) or a bipartite quantifier
      NP (*each other*). -/
  strategy : Reciprocal.Strategy := .recipPronoun
  /-- The readings the form covers. -/
  readings : List Reciprocal.Reading := [.reciprocal]
  deriving Repr, DecidableEq

/-- The marker entry of a reciprocal pronoun. -/
def ReciprocalPronoun.toMarker (p : ReciprocalPronoun) : Reciprocal.Marker :=
  { form := p.form, script := p.script, strategy := p.strategy, readings := p.readings }

/-- A reciprocal pronoun bears φ via its `Pronoun` core. -/
instance : HasPhi ReciprocalPronoun := ⟨λ p => p.toPronoun.toWord.phi⟩

instance : Proform ReciprocalPronoun := ⟨λ p => Proform.Domain p.toPronoun⟩

/-- Its binding class is the `Pronoun` core's, defaulting to the reciprocal. -/
instance : Bound ReciprocalPronoun := ⟨λ p => p.toPronoun.bindingClass.getD .reciprocal⟩
