import Linglib.Core.Computability.NonContextFree.AnBnCnDn
import Linglib.Core.Computability.NonContextFree.AmBnCmDn
import Linglib.Core.Computability.NonContextFree.AnBnCn
import Linglib.Syntax.CCG.Basic

/-!
# CCG Generative Capacity

CCG is mildly context-sensitive: classical CCG is weakly equivalent to TAG, hence
strictly more powerful than context-free grammars ([vijay-shanker-weir-1994],
[weir-joshi-1988]). The classic witnesses are the counting / cross-serial languages
aⁿbⁿcⁿ and aⁿbⁿcⁿdⁿ, which are not context-free.

## What is established here

- `ccg_exceeds_cfg` / `witness_language_non_contextFree` — the witness language
  aⁿbⁿcⁿdⁿ is not context-free (re-using the pumping-lemma proof in
  `Core.Computability.NonContextFree`).

## Restrictions matter: which CCG generates these languages

The "CCG generates a non-context-free language" direction depends critically on the form
of CCG. [kuhlmann-koller-satta-2015] show that the CCG≡TAG equivalence holds for
*classical* CCG, where combinatory rules may be **restricted per grammar** (e.g. fired
only when the target of the primary input category is `S`). For *lexicalized CCG without
target restrictions* they prove the generative power is strictly *below TAG*. The key
point is about generating a language *exactly*: without target restrictions a CCG that
covers `aⁿbⁿcⁿ` also admits extra permuted strings, so it does not generate the language
`aⁿbⁿcⁿ` itself — it is the target restriction that filters these out. This subsystem's
`CCG.DerivStep` models the unrestricted, universal-rule variant (no rule restrictions), so
it is the wrong model for the exact-language construction.

A fully-proven construction of a rule-restricted (classical) CCG that generates aⁿbⁿcⁿ
is therefore *not* expressible over `DerivStep`; it lives in
`Studies/KuhlmannKollerSatta2015` (`ccg_generates_anbnc`), which models the target
restriction explicitly. The concrete Dutch derivations in `CCG.CrossSerial` are 2- and
3-verb instances and are *not* surface-order-faithful (their categories encode the
cross-serial binding but not the linear order; see
`CCG.CrossSerial.jan_zag_zwemmen_piet_yield`), so they do not establish a capacity claim.
-/

namespace CCG.GenerativeCapacity

open FourSymbol

/-- The witness language aⁿbⁿcⁿdⁿ is not context-free. Together with the rule-restricted
construction in `Studies/KuhlmannKollerSatta2015` (for the simpler witness aⁿbⁿcⁿ) this is
the non-context-free side of CFG ⊊ classical-CCG; on its own it establishes only that the
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
