import Linglib.Theories.Semantics.Tense.Evidential

/-!
# Bulgarian Evidential Fragment (Cumming 2026)

Paradigm entries for Bulgarian tense-evidential morphology from Cumming (2026),
Table 17. The -l participle interacts with tense to encode evidential perspective.

## Entries

| Form       | EP constraint | UP constraint | Nonfuture? |
|------------|---------------|---------------|------------|
| NFUT + -l  | T ≤ A         | T ≤ S         | yes        |
| FUT + -l   | A < T         | (none)        | no         |

## References

- Cumming, S. (2026). Tense and evidence. *L&P* 49:153–175. Table 17.
-/

namespace Fragments.Bulgarian.Evidentials

open TruthConditional.Sentence.Tense.Evidential

/-- Bulgarian NFUT + -l: T ≤ A (downstream), T ≤ S (nonfuture). -/
def nfutL : TenseEvidentialParadigm where
  label := "NFUT + -l"
  ep := .downstream
  up := .nonfuture

/-- Bulgarian FUT + -l: A < T (prospective). -/
def futL : TenseEvidentialParadigm where
  label := "FUT + -l"
  ep := .prospective
  up := .unconstrained

/-- All Bulgarian evidential entries. -/
def allEntries : List TenseEvidentialParadigm :=
  [nfutL, futL]

end Fragments.Bulgarian.Evidentials
