import Linglib.Theories.Semantics.Tense.Evidential
import Linglib.Theories.Interfaces.SyntaxSemantics.TAMEComposition

/-!
# Bulgarian Evidential Fragment (Cumming 2026; Stojković 2026)

Paradigm entries for Bulgarian tense-evidential morphology from Cumming (2026),
Table 17. The -l participle interacts with tense to encode evidential perspective.

## Entries (Cumming 2026)

| Form       | EP constraint | UP constraint | Nonfuture? |
|------------|---------------|---------------|------------|
| NFUT + -l  | T ≤ A         | T ≤ S         | yes        |
| FUT + -l   | A < T         | (none)        | no         |

## Compositional Derivations (Stojković 2026)

In Bulgarian, the L-form realizes Asp (inner aspect), not T as in SC.
The auxiliary realizes T. This means:

- **AUX + L** (spine through T): UP = nonfuture, EP unconstrained → direct past
- **Bare L** (spine truncated at Asp, no T): UP unconstrained, EP = downstream →
  indirect/evidential

## References

- Cumming, S. (2026). Tense and evidence. *L&P* 49:153–175. Table 17.
- Stojković, S. (2026). L-participle variation in South Slavic.
-/

namespace Fragments.Bulgarian.Evidentials

open Semantics.Tense.Evidential

/-- Bulgarian NFUT + -l: T ≤ A (downstream), T ≤ S (nonfuture). -/
def nfutL : TAMEEntry where
  label := "NFUT + -l"
  ep := .downstream
  up := .nonfuture

/-- Bulgarian FUT + -l: A < T (prospective). -/
def futL : TAMEEntry where
  label := "FUT + -l"
  ep := .prospective
  up := .unconstrained

/-- All Bulgarian evidential entries. -/
def allEntries : List TAMEEntry :=
  [nfutL, futL]

-- ════════════════════════════════════════════════════
-- § 2. Compositional Derivations (Stojković 2026)
-- ════════════════════════════════════════════════════

open Minimalism
open Theories.Interfaces.SyntaxSemantics.TAMEComposition

/-- Bulgarian head semantics: T contributes UP = nonfuture (T ≤ S),
    Evid contributes EP = downstream (T ≤ A). Asp is semantically
    perfective/imperfective but orthogonal to TAME composition here. -/
def bgHeadSemantics : Cat → HeadSemantics
  | .T    => { ep := none, up := some .nonfuture }
  | .Evid => { ep := some .downstream, up := none }
  | _     => HeadSemantics.silent

/-- Bulgarian exponents: L-form realizes Asp, auxiliary realizes T.
    This is the key difference from SC, where L realizes T. -/
def bgExponents : Exponents
  | .Asp  => some "L"
  | .T    => some "AUX"
  | _     => none

/-- Spine for BG AUX + L: through cartographic TP [V, v, Voice, Asp, T].
    Auxiliary present → T projected → UP = nonfuture. -/
def bgWithAuxSpine : ClauseSpine := ClauseSpine.cartographicTP

/-- Spine for BG bare L: truncated at Asp [V, v, Voice, Asp].
    No auxiliary → T not projected → UP unconstrained, EP from Evid
    is NOT projected either — but the bare L *itself* is evidential.

    In Stojković's analysis, the bare L in BG realizes an Asp head
    in a spine that includes Evid but NOT T: [V, v, Voice, Asp, Evid].
    The evidential interpretation comes from the Evid head being
    projected even without the T-level auxiliary. -/
def bgBareLSpine : ClauseSpine :=
  ⟨[.V, .v, .Voice, .Asp, .Evid], by decide⟩

/-- BG AUX + L derivation: full cartographic TP spine.
    Yields nonfuture past (UP = nonfuture, EP unconstrained). -/
def bgWithAux : TAMEDerivation where
  spine := bgWithAuxSpine
  headSem := bgHeadSemantics
  exponents := bgExponents

/-- BG bare L derivation: spine through Evid but without T.
    Yields indirect/evidential (UP unconstrained, EP = downstream). -/
def bgBareL : TAMEDerivation where
  spine := bgBareLSpine
  headSem := bgHeadSemantics
  exponents := bgExponents

end Fragments.Bulgarian.Evidentials
