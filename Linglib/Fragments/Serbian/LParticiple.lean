import Linglib.Theories.Interfaces.SyntaxSemantics.TAMEComposition

/-!
# Serbian/Croatian L-Participle Fragment

The SC L-participle (-o, -la, -lo, -li, -le, -la) combines with a present-tense
auxiliary (sam, si, je, smo, ste, su) to form the past tense. Without an auxiliary,
the bare L-form is unavailable as a main-clause predicate in standard SC
(unlike Bulgarian, where bare L-forms are evidential).

## TAME Analysis (Stojković 2026)

In the cartographic spine, T⁰ contributes UP = past (T < S) and Evid⁰
contributes EP = downstream (T ≤ A, indirect/reportative evidence). The
L-form realizes T; the auxiliary realizes Evid.

- **AUX + L** (full evidP spine): UP = past, EP = downstream → indirect past
  (reporting of past events, non-confirmative)
- **Bare L** (spine truncated at T, no Evid): UP = past, EP unconstrained →
  direct past (standard witnessed past)

The "direct past" reading arises from the *absence* of the evidential head,
not from a positive [+direct] feature — the EP dimension is simply unconstrained.

## References

- Stojković, S. (2026). L-participle variation in South Slavic.
- Cumming, S. (2026). Tense and evidence. *L&P* 49:153–175.
-/

namespace Fragments.Serbian.LParticiple

open Minimalism
open Semantics.Tense.Evidential
open Theories.Interfaces.SyntaxSemantics.TAMEComposition

-- ════════════════════════════════════════════════════
-- § 1. Morphological Paradigm
-- ════════════════════════════════════════════════════

/-- L-participle gender/number paradigm (present-tense auxiliary + past participle). -/
inductive LPartGender where
  | mascSg   -- -o (e.g., radio)
  | femSg    -- -la (e.g., radila)
  | neutSg   -- -lo (e.g., radilo)
  | mascPl   -- -li (e.g., radili)
  | femPl    -- -le (e.g., radile)
  | neutPl   -- -la (e.g., radila)
  deriving DecidableEq, Repr, BEq

/-- L-participle suffix. -/
def lPartSuffix : LPartGender → String
  | .mascSg => "-o"
  | .femSg  => "-la"
  | .neutSg => "-lo"
  | .mascPl => "-li"
  | .femPl  => "-le"
  | .neutPl => "-la"

/-- Present-tense auxiliary paradigm (person/number). -/
inductive AuxForm where
  | sg1  -- sam
  | sg2  -- si
  | sg3  -- je
  | pl1  -- smo
  | pl2  -- ste
  | pl3  -- su
  deriving DecidableEq, Repr, BEq

/-- Auxiliary surface form. -/
def auxForm : AuxForm → String
  | .sg1 => "sam"
  | .sg2 => "si"
  | .sg3 => "je"
  | .pl1 => "smo"
  | .pl2 => "ste"
  | .pl3 => "su"

-- ════════════════════════════════════════════════════
-- § 2. Per-Head Semantics
-- ════════════════════════════════════════════════════

/-- SC head semantics: T contributes past (T < S), Evid contributes
    downstream evidence (T ≤ A). All other heads are silent. -/
def scHeadSemantics : Cat → HeadSemantics
  | .T    => { ep := none, up := some .past }
  | .Evid => { ep := some .downstream, up := none }
  | _     => HeadSemantics.silent

-- ════════════════════════════════════════════════════
-- § 3. Exponents
-- ════════════════════════════════════════════════════

/-- SC exponents: L-form realizes T, auxiliary realizes Evid. -/
def scExponents : Exponents
  | .T    => some "L"
  | .Evid => some "AUX"
  | _     => none

-- ════════════════════════════════════════════════════
-- § 4. Named Derivations
-- ════════════════════════════════════════════════════

/-- AUX + L derivation: full spine through Evid.
    Yields indirect/reportative past (UP = past, EP = downstream). -/
def withAux : TAMEDerivation where
  spine := ClauseSpine.evidP
  headSem := scHeadSemantics
  exponents := scExponents

/-- Bare L derivation: spine truncated at T (cartographic TP, no Evid).
    Yields direct past (UP = past, EP unconstrained). -/
def bareL : TAMEDerivation where
  spine := ClauseSpine.cartographicTP
  headSem := scHeadSemantics
  exponents := scExponents

end Fragments.Serbian.LParticiple
