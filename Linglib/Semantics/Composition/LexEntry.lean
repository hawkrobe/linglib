import Linglib.Core.Logic.Intensional.Frame

/-!
# Lexical Entry Types

Typed lexical entries for compositional semantics, polymorphic over an
effect functor `M` ([bumford-charlow-2024]): an entry's denotation is an
`M`-computation over its denotation domain. Scope-takers live at
`M = Cont R`, CI items at `M = Writer P`. The default `M := Id` recovers
the pure [heim-kratzer-1998] case, so every existing call site reads
unchanged; effectful lexicons supply an explicit `M`.

- `LexEntry F (M := Id)` — a typed denotation in frame `F`, carried by `M`
- `Lexicon F (M := Id)`  — string-keyed lookup of `M`-effectful entries
- `Lexicon.lift`         — embed a pure lexicon into any effect via `pure`
-/

namespace Semantics.Montague

open Core.Logic.Intensional

/-- A typed lexical entry whose denotation carries the effect `M`
(default `Id` = pure H&K). -/
structure LexEntry (F : Frame) (M : Type → Type := Id) where
  ty : Ty
  denot : M (F.Denot ty)

/-- String-keyed lexicon of `M`-effectful entries (default `Id`). -/
def Lexicon (F : Frame) (M : Type → Type := Id) :=
  String → Option (LexEntry F M)

/-- Embed a pure lexicon into effect `M` by `pure`-lifting every entry. -/
def Lexicon.lift {F : Frame} (M : Type → Type) [Pure M] (lex : Lexicon F) :
    Lexicon F M :=
  λ w => (lex w).map λ e => ⟨e.ty, pure e.denot⟩

end Semantics.Montague
