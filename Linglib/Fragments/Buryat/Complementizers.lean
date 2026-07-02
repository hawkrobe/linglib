import Linglib.Semantics.Verb.Basic
import Linglib.Data.UD.Basic

/-!
# Buryat Complementizers and Clause-Embedding Verbs
[bondarenko-2022] [bondarenko-2020] [bondarenko-2019]

This file records the clause-typing morphemes of Barguzin Buryat
(Mongolic) embedded clauses and the matrix verbs that select them.
Embedded clauses show three surface shapes ([bondarenko-2022] §4.3.1
ex. 30–32): bare `[… V-TENSE gɘ-žɘ]`, nominalized `[… V-PART-CASE]`,
and nominalized with the say-root `[… V-TENSE g-ɘːš-CASE]`.

## Main definitions

- `Buryat.Complementizer` — the say-root *gɘ*, the agentive participle
  *-Aːša*, and the imperfective converb *-žA* ([skribnik-2003]), with
  projections `form`, `verbForm`, and `host`
- `Buryat.hanaxa`, `Buryat.medexe`, `Buryat.xelexe`, `Buryat.duulaxa` —
  clause-embedding verbs; all four alternate between the finite-CP and
  nominalized (`.gerund`) frames (ex. 35–36, 50–51)

## Implementation notes

Bondarenko's head assignment (*gɘ* expones Cont, the suffixes are Comp
allomorphs) is paper-specific and lives in `Studies/Bondarenko2022.lean`;
rival carvings of Mongolic say-complementizers: [knyazev-2016],
[matic-pakendorf-2013]. Bare `§`-references are to [bondarenko-2022],
bare `ex.`/`fn.` references to [bondarenko-2020]. Identifiers are ASCII
romanizations (ɘ → e, ː → doubling, ž → zh, š → sh); `form` fields carry
the faithful transliterations, with capitals marking vowel-harmony
archiphonemes.
-/

namespace Buryat

/-- The three clause-typing morphemes of the Barguzin Buryat embedded
clause (§4.3.1 ex. 30–32). -/
inductive Complementizer where
  /-- *gɘ* — grammaticalized root of *gɘxɘ* 'say' (fn. 21: no speech act
  entailed under 'hear' or 'see'). -/
  | ge
  /-- *-Aːša* — agentive participle ([skribnik-2003]); appears next to
  nominal projections. -/
  | aasha
  /-- *-žA* — imperfective converb ([skribnik-2003]); appears next to
  verbs, also in analytical verb forms and sentential adjuncts (ex. 30). -/
  | zha
  deriving DecidableEq, Fintype, Repr

namespace Complementizer

/-- Surface form in Bondarenko's transliteration. Display only. -/
def form : Complementizer → String
  | .ge    => "gɘ"
  | .aasha => "-Aːša"
  | .zha   => "-žA"

/-- The verb form each suffix derives: participle for *-Aːša*, converb
for *-žA*; `none` for the root *gɘ*, which is not a suffix. -/
def verbForm : Complementizer → Option UD.VerbForm
  | .ge    => none
  | .aasha => some .Part
  | .zha   => some .Conv

/-- Category of the adjacent projection licensing each suffix (§4.3.1). -/
inductive Host where
  | nominal
  | verbal
  deriving DecidableEq, Fintype, Repr

/-- Licensing host of each suffix; `none` for the root *gɘ*. -/
def host : Complementizer → Option Host
  | .ge    => none
  | .aasha => some .nominal
  | .zha   => some .verbal

end Complementizer

/-! ### Clause-embedding verbs

Vendler class stays unset (`Verb.Aspect.vendlerClass` convention for
clause-embedding verbs). -/

/-- *hanaxa* 'think ~ remember': 'think' with a bare gɘžɘ-CP, 'remember'
with a nominalized complement (§4.4.3). `attitude` and `opaqueContext`
record the bare-CP frame; the nominalized frame's pre-existence
presupposition is tracked in `Semantics/Attitudes/PreExistence.lean`. -/
def hanaxa : Verb where
  form := "hanaxa"
  complementType := .finiteClause
  altComplementType := some .gerund
  attitude := some (.doxastic .nonVeridical)
  opaqueContext := true

/-- *mɘdɘxɘ* 'know' — factive in both frames (ex. 36); embeds polar
questions (ex. 3). -/
def medexe : Verb where
  form := "mɘdɘxɘ"
  complementType := .finiteClause
  altComplementType := some .gerund
  attitude := some (.doxastic .veridical)
  takesQuestionBase := true

/-- *xɘlɘxɘ* 'say' — non-factive with bare CPs; nominalized complements
are existence-entailing (ex. 51; speaker variation per fn. 30). -/
def xelexe : Verb where
  form := "xɘlɘxɘ"
  complementType := .finiteClause
  altComplementType := some .gerund
  speechActVerb := true

/-- *duːlaxa* 'hear' — non-factive with bare CPs, existence-entailing
with nominalized complements (ex. 50). -/
def duulaxa : Verb where
  form := "duːlaxa"
  complementType := .finiteClause
  altComplementType := some .gerund

end Buryat
