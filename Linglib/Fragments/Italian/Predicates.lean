import Linglib.Theories.Semantics.Verb.VerbEntry
import Linglib.Theories.Semantics.Attitudes.RationalAttitude
import Linglib.Theories.Syntax.Minimalism.ExtendedProjection.Basic

/-!
# Italian Verb Entries @cite{fusco-sgrizzi-2026}

Italian attitude and causative-attitude verbs, with emphasis on the
*di*/*a* infinitival alternation documented in @cite{fusco-sgrizzi-2026}.

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
  deriving DecidableEq, Repr

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

    @cite{fusco-sgrizzi-2026}, ex. (4):
    - (4a) Marco ha convinto Gianni di avere un figlio (belief)
    - (4b) Marco ha convinto Gianni a avere un figlio (intention) -/
def convincere : ItalianVerbEntry :=
  { form := "convincere"
    complementType := .infinitival
    controlType := .objectControl
    altComplementType := some .finiteClause
    opaqueContext := true
    -- No fixed attitude: attitude type (belief vs intention)
    -- is determined by complement size, not lexically specified.
    infComplements := [.di, .a_] }

/-- *credere* 'believe' — standard doxastic attitude verb.
    Takes *di*-infinitives and *che*-finite clauses (belief only). -/
def credere : ItalianVerbEntry :=
  { form := "credere"
    complementType := .finiteClause
    controlType := .subjectControl
    altComplementType := some .infinitival
    opaqueContext := true
    attitude := some (.doxastic .nonVeridical)
    infComplements := [.di] }

-- ════════════════════════════════════════════════════════════════
-- § 3b. Attitude Verb Data (@cite{grano-2024})
-- ════════════════════════════════════════════════════════════════

/-- *volere* 'want' — core desiderative verb, robustly subjunctive-selecting.

    @cite{grano-2024}, Table 1: Italian 'want' takes SBJV (marginally %IND).
    - (4a) Gianni vuole che Maria *sia*/%è contenta. (SBJV preferred)
    - (4b) Gianni vuole essere contento. (INF) -/
def volere : ItalianVerbEntry :=
  { form := "volere"
    complementType := .finiteClause
    controlType := .subjectControl
    altComplementType := some .infinitival
    passivizable := false
    opaqueContext := true
    attitude := some (.preferential (.degreeComparison .positive))
    levinClass := some .want
    infComplements := [.di] }

/-- *sperare* 'hope' — cross-linguistically variable mood selection.

    @cite{grano-2024}, Table 1: Italian 'hope' takes SBJV, %IND marginal.
    - (12) Gianni spera che Maria *sia*/%è contenta. (SBJV preferred)
    Unlike *volere*, *sperare* allows indicative marginally in Italian
    and freely in other Romance languages (French *espérer*, Portuguese
    *esperar*). -/
def sperare : ItalianVerbEntry :=
  { form := "sperare"
    complementType := .finiteClause
    controlType := .subjectControl
    altComplementType := some .infinitival
    passivizable := false
    opaqueContext := true
    attitude := some (.preferential (.degreeComparison .positive))
    infComplements := [.di] }

/-- *intendere* 'intend' — intention-reporting verb, robustly rejects indicative.

    @cite{grano-2024}, §2.2: Italian 'intend' primarily uses the periphrastic
    *avere intenzione di* or the control verb *intendere*. Indicative
    complements are never accepted. The rare literary usage with subjunctive
    (ex. 30, from Treccani) has a 'demand'-like interpretation.
    - (20) Intendo / Ho intenzione di andare al parco oggi. (INF only)
    - (28) *Intendo che Giovanni vada/va al parco oggi. (rejected) -/
def intendere : ItalianVerbEntry :=
  { form := "intendere"
    complementType := .infinitival
    controlType := .subjectControl
    passivizable := false
    opaqueContext := true
    attitude := some (.preferential (.degreeComparison .positive))
    levinClass := some .want
    infComplements := [.di] }

/-- *fare* 'make' — causative verb, robustly rejects indicative.

    @cite{grano-2024}, §2.4: Italian causatives accept nonfinite and
    subjunctive (with *sì che*) but reject indicative complements.
    - (39) Ho fatto andare Giovanni al parco. (INF)
    - (42a) Ho fatto sì che Giovanni *andasse*/*è andato al parco. (SBJV/*IND) -/
def fare_caus : ItalianVerbEntry :=
  { form := "fare"
    complementType := .infinitival
    controlType := .objectControl
    causative := some .make
    infComplements := [.a_] }

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

-- ════════════════════════════════════════════════════════════════
-- § 5. Mood Choice Bridge Theorems (@cite{grano-2024})
-- ════════════════════════════════════════════════════════════════

/-- *volere* has Levin want-class (core desiderative). -/
theorem volere_is_want_class :
    volere.levinClass = some .want := rfl

/-- *sperare* does NOT have Levin want-class (explains mood variation). -/
theorem sperare_not_want_class :
    sperare.levinClass ≠ some .want := by decide

/-- *intendere* has Levin want-class (patterns with *volere* on mood). -/
theorem intendere_is_want_class :
    intendere.levinClass = some .want := rfl

/-- *volere* and *intendere* share want-class; *sperare* does not.
    This predicts the mood choice asymmetry: *volere*/*intendere* robustly
    reject indicative, while *sperare* varies (@cite{grano-2024}, Table 1). -/
theorem mood_asymmetry_predicted :
    volere.levinClass = some .want ∧
    intendere.levinClass = some .want ∧
    sperare.levinClass ≠ some .want := by
  exact ⟨rfl, rfl, by decide⟩

end Fragments.Italian.Predicates
