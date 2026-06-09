import Linglib.Core.Logic.Intensional.Frame

/-!
# Lexical Entry Types

Typed lexical entries for compositional semantics, polymorphic over an
effect functor `M` ([bumford-charlow-2024]): an entry's denotation is an
`M`-computation over its denotation domain. Scope-takers live at
`M = Cont R`, CI items at `M = Writer P`. The default `M := Id` recovers
the pure [heim-kratzer-1998] case, so every existing call site reads
unchanged; effectful lexicons supply an explicit `M`.

- `LexEntry E W (M := Id)` — a typed denotation over entity/index types `E`/`W`, carried by `M`
- `Lexicon E W (M := Id)`  — string-keyed lookup of `M`-effectful entries
- `Lexicon.lift`           — embed a pure lexicon into any effect via `pure`
-/

namespace Semantics.Montague

open Core.Logic.Intensional

/-- A typed lexical entry whose denotation carries the effect `M`
(default `Id` = pure H&K). -/
structure LexEntry (E W : Type) (M : Type → Type := Id) where
  ty : Ty
  denot : M (Denot E W ty)

/-- String-keyed lexicon of `M`-effectful entries (default `Id`). -/
def Lexicon (E W : Type) (M : Type → Type := Id) :=
  String → Option (LexEntry E W M)

/-- Embed a pure lexicon into effect `M` by `pure`-lifting every entry. -/
def Lexicon.lift {E W : Type} (M : Type → Type) [Pure M] (lex : Lexicon E W) :
    Lexicon E W M :=
  λ w => (lex w).map λ e => ⟨e.ty, pure e.denot⟩

end Semantics.Montague
