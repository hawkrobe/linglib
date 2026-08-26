import Linglib.Morphology.Paradigm.Basic
import Mathlib.Data.Fin.VecNotation

/-!
# Burmeso object agreement

The two classes of Burmeso object agreement prefixes over six noun classes in two numbers,
after Donohue's description as tabulated in [ackerman-malouf-2013].

## References

* [ackerman-malouf-2013]
-/

namespace Burmeso.ObjectAgreement

open Morphology

/-- The agreement prefixes. -/
inductive AgreementPrefix
  | j
  | s
  | g
  | b
  | t
  | n
  deriving DecidableEq, Repr

/-- The two classes over the cells I.sg, I.pl, …, VI.sg, VI.pl, each with unit weight. -/
def objectAgreement : ParadigmSystem 12 AgreementPrefix where
  entries :=
    [(![.j, .s, .g, .s, .g, .j, .j, .j, .j, .g, .g, .g], 1),
      (![.b, .t, .n, .t, .n, .b, .b, .b, .b, .n, .n, .n], 1)]

end Burmeso.ObjectAgreement
