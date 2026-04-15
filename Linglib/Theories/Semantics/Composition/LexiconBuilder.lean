import Linglib.Core.IntensionalLogic.Frame
import Linglib.Theories.Semantics.Composition.LexEntry
import Linglib.Theories.Semantics.Lexical.Verb.VerbEntry

/-!
# Lexicon Builder

Dispatch layer connecting Fragment classificatory data to compositional
semantics. Provides:

1. **Type dispatch** (`ComplementType.toTy`): deterministic mapping from verb
   complement type to Montague semantic type.

2. **Lexicon construction** (`buildLexicon`): assembles a `Lexicon F` from a
   list of named entries, replacing the hand-written match-on-strings pattern
   that Studies currently use.

3. **Entry construction** (`VerbCore.mkLexEntry`): given a VerbCore and a
   denotation of the appropriate type, produce a `LexEntry F`.

## Design

The dispatch layer does NOT generate denotations from features — that would
be too theory-laden. It provides the *type* and the *scaffolding*; the Study
still supplies the denotation. Domain-specific denotation builders
(`VerbCore.getCoSSemantics`, `VerbCore.veridicality`, etc.) remain in
`Theories/Semantics/Lexical/Verb/VerbEntry.lean`.

## Usage pattern

```
-- In a Study file:
import Linglib.Theories.Semantics.Composition.LexiconBuilder
import Linglib.Fragments.English.Predicates.Verbal

open Semantics.Composition.LexiconBuilder (buildLexicon)
open Semantics.Montague (LexEntry)

def myLexicon : Lexicon myModel :=
  buildLexicon [
    ("john", ⟨.e, john_sem⟩),
    ("sleeps", ⟨.et, sleeps_sem⟩),
    ("sees", ⟨.eet, sees_sem⟩)
  ]
```
-/

open Core.IntensionalLogic (Ty Frame)
open Semantics.Montague (LexEntry Lexicon)

/-! ## Type Dispatch -/

namespace Core.Verbs

open Core.IntensionalLogic (Ty)

/-- Map a verb's complement type to its Montague semantic type.

- Intransitives (`none`): `e → t` (1-place predicate)
- Transitives (`np`): `e → e → t` (2-place, object then subject)
- Ditransitives (`np_np`): `e → e → e → t` (IO, DO, subject)
- NP+PP (`np_pp`): `e → e → e → t` (same arity as ditransitive)
- Finite clause (`finiteClause`): `t → e → t` (proposition-taking)
- Infinitival (`infinitival`): `(e → t) → e → t` (property-taking)
- Gerund (`gerund`): `(e → t) → e → t` (same as infinitival)
- Small clause (`smallClause`): `(e → t) → e → t` (resultative predicate)
- Question (`question`): `(e → t) → e → t` (question-embedding) -/
def ComplementType.toTy : ComplementType → Ty
  | .none          => .e ⇒ .t
  | .np            => .e ⇒ .e ⇒ .t
  | .np_np         => .e ⇒ .e ⇒ .e ⇒ .t
  | .np_pp         => .e ⇒ .e ⇒ .e ⇒ .t
  | .finiteClause  => .t ⇒ .e ⇒ .t
  | .infinitival   => (.e ⇒ .t) ⇒ .e ⇒ .t
  | .gerund        => (.e ⇒ .t) ⇒ .e ⇒ .t
  | .smallClause   => (.e ⇒ .t) ⇒ .e ⇒ .t
  | .question      => (.e ⇒ .t) ⇒ .e ⇒ .t

/-- The semantic type of a verb, determined by its complement type. -/
def VerbCore.semanticType (v : VerbCore) : Ty :=
  v.complementType.toTy

end Core.Verbs

namespace Semantics.Composition.LexiconBuilder

open Core.Verbs (ComplementType VerbCore)

/-! ## Lexicon Construction -/

/-- Build a `Lexicon F` from a list of named entries.

Replaces the pattern of hand-written match expressions on strings that
Studies currently use. Lookup is linear in the entry list; this is fine
for the small lexicons (5–30 entries) typical of Study files.

```
def myLex : Lexicon myModel := buildLexicon [
  ("john", ⟨.e, john_sem⟩),
  ("sleeps", ⟨.et, sleeps_sem⟩)
]
```
-/
def buildLexicon {F : Frame} (entries : List (String × LexEntry F)) : Lexicon F :=
  λ s => (entries.find? (λ p => p.1 == s)).map (·.2)

/-- Extend a lexicon with additional entries. Later entries shadow earlier
    ones with the same name. -/
def extendLexicon {F : Frame} (base : Lexicon F) (extra : List (String × LexEntry F))
    : Lexicon F :=
  λ s => (extra.find? (λ p => p.1 == s)).map (·.2) |>.orElse (λ _ => base s)

/-- Merge two lexicons. The first lexicon takes priority on conflicts. -/
def mergeLexicons {F : Frame} (lex1 lex2 : Lexicon F) : Lexicon F :=
  λ s => (lex1 s).orElse (λ _ => lex2 s)

/-! ## Entry Construction -/

/-- Create a `LexEntry` for a verb, using `complementType.toTy` to determine
    the semantic type. The caller provides a denotation of the appropriate type.

    This ensures the entry's type tag matches the verb's argument structure
    by construction. -/
def VerbCore.mkLexEntry (v : VerbCore) (F : Frame) (denot : F.Denot v.semanticType)
    : LexEntry F :=
  ⟨v.semanticType, denot⟩

/-! ## Convenience -/

/-- The empty lexicon. -/
def emptyLexicon {F : Frame} : Lexicon F := λ _ => none

/-- A single-entry lexicon. -/
def singletonLexicon {F : Frame} (name : String) (entry : LexEntry F) : Lexicon F :=
  λ s => if s == name then some entry else none

end Semantics.Composition.LexiconBuilder
