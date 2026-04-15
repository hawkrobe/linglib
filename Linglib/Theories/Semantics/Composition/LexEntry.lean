import Linglib.Core.IntensionalLogic.Frame

/-!
# Lexical Entry Types

Typed lexical entries for compositional semantics.

- `LexEntry F` — a typed denotation in frame `F`
- `Lexicon F` — string-keyed lookup of lexical entries
-/

namespace Semantics.Montague

open Core.IntensionalLogic

structure LexEntry (F : Frame) where
  ty : Ty
  denot : F.Denot ty

def Lexicon (F : Frame) := String → Option (LexEntry F)

end Semantics.Montague
