import Linglib.Syntax.Category.Verb.Basic
import Linglib.Syntax.Minimalist.ExtendedProjection.Basic

/-!
# Italian Verb Entries [fusco-sgrizzi-2026]

Italian attitude and causative-attitude verbs, with emphasis on the
*di*/*a* infinitival alternation documented in [fusco-sgrizzi-2026].

## The *di*/*a* Alternation

Italian *convincere* ('convince') selects two distinct infinitival
complements: *di* + infinitive ("Maria ha convinto Paolo di essere in
pericolo", 'Maria convinced Paolo that he was in danger') and *a* +
infinitive ("Maria ha convinto Paolo a partire", 'Maria convinced
Paolo to leave'). The entries record which complementizers each verb
selects; [fusco-sgrizzi-2026]'s analysis of the alternation —
complement size determining the belief/intention reading — lives in
`Studies/FuscoSgrizzi2026.lean`.
-/

namespace Italian.Predicates

open ArgumentStructure
open Minimalist (ComplementSize)

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

-- ════════════════════════════════════════════════════════════════
-- § 2. Italian Verb Entry
-- ════════════════════════════════════════════════════════════════

/-- An Italian verb entry extending `Verb` with the infinitival
    complementizer alternation. -/
structure ItalianVerbEntry extends Verb where
  /-- Which infinitival complementizers the verb selects -/
  infComplements : List InfComplementizer := []
  deriving Repr, BEq

-- ════════════════════════════════════════════════════════════════
-- § 3. Verb Data
-- ════════════════════════════════════════════════════════════════

/-- *convincere* 'convince' — causative attitude verb with dual infinitival
    selection. Takes *di*-infinitives (belief) and *a*-infinitives (intention).

    [fusco-sgrizzi-2026], ex. (4):
    - (4a) Marco ha convinto Gianni di avere un figlio (belief)
    - (4b) Marco ha convinto Gianni a avere un figlio (intention) -/
def convincere : ItalianVerbEntry :=
  { form := "convincere"
    frames := [Frame.infinitival, Frame.finiteClause]
    readings := [{ frame := Frame.infinitival, control := some .objectControl }]
    opaqueContext := true
    -- No fixed attitude: attitude type (belief vs intention)
    -- is determined by complement size, not lexically specified.
    infComplements := [.di, .a_] }

/-- *credere* 'believe' — standard doxastic attitude verb.
    Takes *di*-infinitives and *che*-finite clauses (belief only). -/
def credere : ItalianVerbEntry :=
  { form := "credere"
    frames := [Frame.finiteClause, Frame.infinitival]
    readings := [{ frame := Frame.finiteClause, control := some .subjectControl }]
    opaqueContext := true
    attitude := some (.doxastic .nonVeridical)
    infComplements := [.di] }

-- ════════════════════════════════════════════════════════════════
-- § 3b. Attitude Verb Data ([grano-2024])
-- ════════════════════════════════════════════════════════════════

/-- *volere* 'want' — core desiderative verb, robustly subjunctive-selecting.

    [grano-2024], Table 1: Italian 'want' takes SBJV (marginally %IND).
    - (4a) Gianni vuole che Maria *sia*/%è contenta. (SBJV preferred)
    - (4b) Gianni vuole essere contento. (INF) -/
def volere : ItalianVerbEntry :=
  { form := "volere"
    frames := [Frame.finiteClause, Frame.infinitival]
    readings := [{ frame := Frame.finiteClause, control := some .subjectControl }]
    passivizable := false
    opaqueContext := true
    attitude := some (.preferential (.degreeComparison .positive))
    levinClass := some .want
    infComplements := [.di] }

/-- *sperare* 'hope' — cross-linguistically variable mood selection.

    [grano-2024], Table 1: Italian 'hope' takes SBJV, %IND marginal.
    - (12) Gianni spera che Maria *sia*/%è contenta. (SBJV preferred)
    Unlike *volere*, *sperare* allows indicative marginally in Italian
    and freely in other Romance languages (French *espérer*, Portuguese
    *esperar*). -/
def sperare : ItalianVerbEntry :=
  { form := "sperare"
    frames := [Frame.finiteClause, Frame.infinitival]
    readings := [{ frame := Frame.finiteClause, control := some .subjectControl }]
    passivizable := false
    opaqueContext := true
    attitude := some (.preferential (.degreeComparison .positive))
    infComplements := [.di] }

/-- *intendere* 'intend' — intention-reporting verb, robustly rejects indicative.

    [grano-2024], §2.2: Italian 'intend' primarily uses the periphrastic
    *avere intenzione di* or the control verb *intendere*. Indicative
    complements are never accepted. The rare literary usage with subjunctive
    (ex. 30, from Treccani) has a 'demand'-like interpretation.
    - (20) Intendo / Ho intenzione di andare al parco oggi. (INF only)
    - (28) *Intendo che Giovanni vada/va al parco oggi. (rejected) -/
def intendere : ItalianVerbEntry :=
  { form := "intendere"
    frames := [Frame.infinitival]
    readings := [{ frame := Frame.infinitival, control := some .subjectControl }]
    passivizable := false
    opaqueContext := true
    attitude := some (.preferential (.degreeComparison .positive))
    levinClass := some .want
    infComplements := [.di] }

/-- *fare* 'make' — causative verb, robustly rejects indicative.

    [grano-2024], §2.4: Italian causatives accept nonfinite and
    subjunctive (with *sì che*) but reject indicative complements.
    - (39) Ho fatto andare Giovanni al parco. (INF)
    - (42a) Ho fatto sì che Giovanni *andasse*/*è andato al parco. (SBJV/*IND) -/
def fare_caus : ItalianVerbEntry :=
  { form := "fare"
    frames := [Frame.infinitival]
    readings := [{ frame := Frame.infinitival, control := some .objectControl }]
    causative := some .make
    infComplements := [.a_] }

-- ════════════════════════════════════════════════════════════════
-- § 5. Mood Choice Bridge Theorems ([grano-2024])
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
    reject indicative, while *sperare* varies ([grano-2024], Table 1). -/
theorem mood_asymmetry_predicted :
    volere.levinClass = some .want ∧
    intendere.levinClass = some .want ∧
    sperare.levinClass ≠ some .want := by
  exact ⟨rfl, rfl, by decide⟩

end Italian.Predicates
