import Linglib.Theories.Semantics.Lexical.Verb.VerbEntry
import Linglib.Theories.Semantics.Attitudes.RationalAttitude
import Linglib.Theories.Syntax.Minimalism.Formal.ExtendedProjection.Basic

/-!
# Italian Verb Entries @cite{fusco-sgrizzi-2025}

Italian attitude and causative-attitude verbs, with emphasis on the
*di*/*a* infinitival alternation documented in Fusco & Sgrizzi (2025).

## The *di*/*a* Alternation

Italian *convincere* ('convince') selects two distinct infinitival complements:
- *di* + infinitive → CP-sized → CLOSURE applies → **belief** reading
  "Maria ha convinto Paolo di essere in pericolo"
  ('Maria convinced Paolo that he was in danger')
- *a* + infinitive → sub-CP (aP) → no CLOSURE → **intention** reading
  "Maria ha convinto Paolo a partire"
  ('Maria convinced Paolo to leave')

The complement marker (*di* vs *a*) tracks the complement's structural size,
which determines the rational attitude reading.

-/

namespace Fragments.Italian.Predicates

open Core.Verbs
open Minimalism (ComplementSize)
open Semantics.Attitudes.RationalAttitude (Reading readingFromSize)

-- ════════════════════════════════════════════════════════════════
-- § 1. Italian Infinitival Complementizers
-- ════════════════════════════════════════════════════════════════

/-- Italian infinitival complementizers, each associated with a complement size.

    - *di*: introduces CP-sized infinitival complements (propositional)
    - *a*: introduces sub-CP (aP) infinitival complements (event predicate)
    - *che*: introduces full finite CP complements -/
inductive InfComplementizer where
  | di   -- CP infinitival (belief): "di essere in pericolo"
  | a_   -- Sub-CP infinitival (intention): "a partire"
  deriving DecidableEq, BEq, Repr

/-- The complement size selected by each Italian infinitival complementizer. -/
def InfComplementizer.complementSize : InfComplementizer → ComplementSize
  | .di  => .cP   -- di-infinitives are CP-sized (propositional)
  | .a_  => .vP   -- aP is above vP but below TP (ex. 22); mapped to vP
                   -- as nearest available ComplementSize (threshold is CP)

/-- The rational attitude reading derived from each complementizer. -/
def InfComplementizer.reading : InfComplementizer → Reading :=
  readingFromSize ∘ InfComplementizer.complementSize

-- ════════════════════════════════════════════════════════════════
-- § 2. Italian Verb Entry
-- ════════════════════════════════════════════════════════════════

/-- An Italian verb entry extending `VerbCore` with the infinitival
    complementizer alternation. -/
structure ItalianVerbEntry extends VerbCore where
  /-- Which infinitival complementizers the verb selects -/
  infComplements : List InfComplementizer := []
  deriving Repr, BEq

-- ════════════════════════════════════════════════════════════════
-- § 3. Verb Data
-- ════════════════════════════════════════════════════════════════

/-- *convincere* 'convince' — causative attitude verb with dual infinitival
    selection. Takes *di*-infinitives (belief) and *a*-infinitives (intention).

    Fusco & Sgrizzi (2025), ex. (1)–(2):
    - (1a) Maria ha convinto Paolo di essere in pericolo (belief)
    - (1b) Maria ha convinto Paolo a partire (intention) -/
def convincere : ItalianVerbEntry :=
  { form := "convincere"
    complementType := .infinitival
    subjectTheta := some .agent
    objectTheta := some .experiencer
    controlType := .objectControl
    altComplementType := some .finiteClause
    opaqueContext := true
    -- No fixed attitudeBuilder: attitude type (belief vs intention)
    -- is determined by complement size, not lexically specified.
    infComplements := [.di, .a_] }

/-- *persuadere* 'persuade' — intention-only causative attitude verb.
    Selects only *a*-infinitives (no belief reading).

    Fusco & Sgrizzi (2025), §2: *persuadere* patterns exclusively with
    *a*-complements, unlike *convincere* which alternates. -/
def persuadere : ItalianVerbEntry :=
  { form := "persuadere"
    complementType := .infinitival
    subjectTheta := some .agent
    objectTheta := some .experiencer
    controlType := .objectControl
    opaqueContext := true
    -- No fixed attitudeBuilder: intention reading derived from
    -- complement selection (*a* only), not from lexical specification.
    infComplements := [.a_] }

/-- *credere* 'believe' — standard doxastic attitude verb.
    Takes *di*-infinitives and *che*-finite clauses (belief only). -/
def credere : ItalianVerbEntry :=
  { form := "credere"
    complementType := .finiteClause
    subjectTheta := some .experiencer
    controlType := .subjectControl
    altComplementType := some .infinitival
    opaqueContext := true
    attitudeBuilder := some (.doxastic .nonVeridical)
    infComplements := [.di] }

-- ════════════════════════════════════════════════════════════════
-- § 4. Bridge Theorems: Complementizer → Reading
-- ════════════════════════════════════════════════════════════════

/-- *di*-infinitives yield belief readings. -/
theorem di_yields_belief : InfComplementizer.reading .di = .belief := by decide

/-- *a*-infinitives yield intention readings. -/
theorem a_yields_intention : InfComplementizer.reading .a_ = .intention := by decide

/-- *convincere* supports both readings (one per complementizer). -/
theorem convincere_dual_reading :
    convincere.infComplements.map InfComplementizer.reading = [.belief, .intention] := by
  decide

/-- *persuadere* supports only the intention reading. -/
theorem persuadere_intention_only :
    persuadere.infComplements.map InfComplementizer.reading = [.intention] := by
  decide

/-- *credere* supports only the belief reading. -/
theorem credere_belief_only :
    credere.infComplements.map InfComplementizer.reading = [.belief] := by
  decide

/-- The *di*/*a* alternation in *convincere* is structurally grounded:
    the two complementizers select different complement sizes, which
    deterministically map to different attitude readings. -/
theorem convincere_alternation_is_structural :
    InfComplementizer.complementSize .di ≠ InfComplementizer.complementSize .a_ ∧
    InfComplementizer.reading .di ≠ InfComplementizer.reading .a_ := by
  decide

end Fragments.Italian.Predicates
