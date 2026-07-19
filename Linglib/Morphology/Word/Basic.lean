import Linglib.Data.UD.Basic
import Linglib.Features.Case.Capabilities
import Linglib.Features.Number.Capabilities
import Linglib.Features.Person.Capabilities

/-!
# Word — the morphosyntactic word (ms-word) token
[kalin-bjorkman-etal-2026]

The surface token: the unit that (morpho)syntax treats as a word. Wordhood minimally
splits into the **ms-word** (this type) and the **p-word** (the prosodic word,
`Phonology/Prosodic/Word.lean`) — the "one area of robust consensus" on the wordhood
problem ([kalin-bjorkman-etal-2026] §3.2); we follow the Element in calling ms-words
simply *words*. The split is descriptive, not a Lexicalist commitment: ms-words are
"crucial for lexicalist theories" but used descriptively by non-lexicalist ones too
(§3.2.1, §3.3), and this token carries no theory of how words are formed.

`Word` completes Morphology's word inventory: `Word.Structure` (`Word/Structure.lean`) is word-*internal* structure,
`Paradigm/Linkage` carries the word-forming correspondence (stem selection + realization), `Word` is the resulting *token* —
form + UD category + one `UD.MorphFeatures` bundle, i.e. a CoNLL-U row. The
ms-word vs p-word typology relating the two word notions ([kalin-bjorkman-etal-2026]
Table 3) is formalized in `Studies/KalinBjorkmanEtAl2026.lean`.

## Main declarations

* `Word` — the token, with its **admission rule** (see the declaration docstring).
* `Word.phi` — the φ-feature projection (person/number/gender).
* `Word.Agree` — φ-agreement: a reflexive, symmetric, non-transitive tolerance relation.
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
    Identity caveat: `BEq` is form + category, so homographs collapse; a CoNLL-U
    `lemma` field is the known fix, deferred until a consumer needs it. -/
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

/-- φ-agreement between two words: their person/number/gender features are
    compatible (an unspecified feature is a wildcard). A reflexive, symmetric
    *tolerance* relation on `Word` (not transitive), decided by the shared
    `UD.MorphFeatures.compatible`. This is the feature-based agreement primitive
    binding and concord consumers share — no surface-form gender lookup. -/
def Word.Agree (w1 w2 : Word) : Prop := w1.phi.compatible w2.phi

instance (w1 w2 : Word) : Decidable (Word.Agree w1 w2) := by
  unfold Word.Agree; infer_instance

@[refl] theorem Word.Agree.refl (w : Word) : Word.Agree w w :=
  UD.MorphFeatures.compatible_self w.phi

/-- φ-agreement is symmetric — the docstring's "symmetric tolerance relation", as a
    theorem. -/
@[symm] theorem Word.Agree.symm {w1 w2 : Word} (h : Word.Agree w1 w2) : Word.Agree w2 w1 := by
  unfold Word.Agree at h ⊢
  rwa [UD.MorphFeatures.compatible_comm]

/-- φ-agreement is *not* transitive: an unspecified feature is a wildcard, so
    underspecified *they* agrees with both *she* and *he* while *she ≁ he*. -/
theorem Word.Agree.not_transitive :
    ¬ ∀ w1 w2 w3 : Word, Word.Agree w1 w2 → Word.Agree w2 w3 → Word.Agree w1 w3 := by
  intro h
  exact absurd
    (h ⟨"she", .PRON, { person := some .third, number := some .Sing, gender := some .Fem }⟩
       ⟨"they", .PRON, { person := some .third }⟩
       ⟨"he", .PRON, { person := some .third, number := some .Sing, gender := some .Masc }⟩
       (by decide) (by decide))
    (by decide)

/-- A word bears the number its UD morphology ingests (`Number.fromUD`). -/
instance : HasNumber Word := ⟨fun w => w.features.number.bind Number.fromUD⟩

instance : HasPerson Word := ⟨fun w => w.features.person.map Person.fromUD⟩

instance : HasCase Word := ⟨fun w => w.features.case_.map Case.fromUD⟩

/-- The φ-projection preserves `numberOf`: a word and its `phi` bundle bear
    the same number — the defeq `Word.Agree.hasNumber_compatible` relies on. -/
@[simp] theorem Word.numberOf_phi (w : Word) :
    HasNumber.numberOf w.phi = HasNumber.numberOf w := rfl

/-- φ-agreement entails number compatibility: the `HasNumber` mixin never
    diverges from the agreement engine on `Word`. -/
theorem Word.Agree.hasNumber_compatible {w1 w2 : Word} (h : w1.Agree w2) :
    HasNumber.Compatible w1 w2 :=
  UD.MorphFeatures.compatible_hasNumber (f1 := w1.phi) (f2 := w2.phi) h

-- `reflex` is deliberately not an agreement feature: a reflexive-marked token still
-- agrees with an unmarked one (the φ-projection drops it).
example : Word.Agree ⟨"sich", .PRON, { reflex := true }⟩ ⟨"Kind", .NOUN, {}⟩ := by decide

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
