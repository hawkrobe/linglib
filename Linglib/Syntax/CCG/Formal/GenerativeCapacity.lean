import Linglib.Core.Computability.NonContextFree.AnBnCnDn
import Linglib.Core.Computability.NonContextFree.AmBnCmDn
import Linglib.Core.Computability.NonContextFree.AnBnCn
import Linglib.Syntax.CCG.CrossSerial
import Linglib.Syntax.CCG.Basic

/-!
# CCG Generative Capacity

CCG is mildly context-sensitive: strictly more powerful than context-free grammars,
yet still polynomially parsable (@cite{steedman-2000}). The classic witness is the
counting / cross-serial language aⁿbⁿcⁿdⁿ, which is not context-free.

## What is established here

- `ccg_exceeds_cfg` / `witness_language_non_contextFree` — the witness language
  aⁿbⁿcⁿdⁿ is not context-free (re-using the pumping-lemma proof in
  `Core.Computability.NonContextFree`).

## What is *not* yet established (TODO)

- `ccg_generates_abcd` (below, `sorry`) — that a CCG actually *derives* aⁿbⁿcⁿdⁿ for
  every `n`. This is the other half of the proper inclusion CFG ⊊ CCG. It needs a
  uniform lexicon plus an `n`-indexed, surface-order-faithful derivation built by
  recursion on `n`, with the yield computed by induction. The concrete Dutch
  derivations in `CCG.CrossSerial` are 2- and 3-verb instances and are *not*
  surface-order-faithful (their categories encode the cross-serial binding but not the
  linear order;
  see `CCG.CrossSerial.jan_zag_zwemmen_piet_yield`), so they do not discharge this
  claim. The precise position of CCG in the hierarchy (weak equivalence to TAG/LIG/Head
  grammar) depends on the rule restrictions: @cite{vijay-shanker-weir-1994},
  @cite{kuhlmann-koller-satta-2010}.
-/

namespace CCG.GenerativeCapacity

open FourSymbol

/-- The four-block counting string aⁿbⁿcⁿdⁿ, as a list of surface symbols. -/
def abcdString (n : Nat) : List String :=
  List.replicate n "a" ++ List.replicate n "b" ++
    List.replicate n "c" ++ List.replicate n "d"

/-- **TODO (research-grade).** For every `n` there is a well-formed CCG derivation of
category `S` whose surface yield is aⁿbⁿcⁿdⁿ — the "CCG generates a non-context-free
language" direction of CFG ⊊ CCG. Stated in full rather than weakened; the proof
requires the uniform-lexicon, `n`-indexed construction described in the module
docstring and is not yet formalized. -/
theorem ccg_generates_abcd :
    ∀ n, ∃ d : CCG.DerivStep, d.cat = some CCG.S ∧ d.yield = abcdString n := by
  sorry

/-- The witness language aⁿbⁿcⁿdⁿ is not context-free. With `ccg_generates_abcd` this
would give the proper inclusion CFG ⊊ CCG; on its own it establishes only that the
target language lies beyond the context-free tier. -/
theorem ccg_exceeds_cfg : ¬ Language.IsContextFree anbncndn :=
  anbncndn_not_contextFree

/-- The witness language contains every `aⁿbⁿcⁿdⁿ` string and lacks the CFL pumping
property, hence is genuinely non-context-free. -/
theorem witness_language_non_contextFree :
    (∀ n : Nat, makeString_anbncndn n ∈ anbncndn) ∧
    ¬ HasCFLPumpingProperty anbncndn :=
  ⟨makeString_in_language, anbncndn_not_pumpable⟩

end CCG.GenerativeCapacity
