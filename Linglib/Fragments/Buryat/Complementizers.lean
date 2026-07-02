import Linglib.Semantics.Verb.Basic
import Linglib.Data.UD.Basic

/-!
# Buryat Complementizers and Clause-Embedding Verbs
[bondarenko-2022] [bondarenko-2020] [bondarenko-2019]

Modern Barguzin Buryat (Mongolic; Russian Federation) — the clause-typing
morphemes of embedded clauses and the matrix verbs that select bare
vs. nominalized complements.

## Three clause-typing morphemes

Embedded clauses show three surface shapes ([bondarenko-2022] §4.3.1
ex. 30–32; [bondarenko-2020]):

- bare CP: `[… V-TENSE gɘ-žɘ]` — the grammaticalized say-root *gɘ*
  (from *gɘxɘ* 'say', [bondarenko-2020] fn. 21) plus the converb suffix
  *-žA*; the complex is standardly cited as the complementizer *gɘžɘ*;
- nominalized clause without *gɘ*: `[… V-PART-CASE]`;
- nominalized clause with *gɘ*: `[… V-TENSE g-ɘːš-CASE]` — say-root plus
  the participial suffix *-Aːša* plus nominal morphology (case, optional
  possessive marking) and genitive subject.

*-Aːša* is the agentive participle (actor noun) and *-žA* the
imperfective converb ([skribnik-2003]). Capital letters mark
vowel-harmony archiphonemes (-aːša ~ -ɘːšɘ ~ -oːšo). *-Aːša* appears
when the clause complex combines with a nominal projection, *-žA* when
it combines directly with a verb ([bondarenko-2022] §4.3.1).

## Scope of this Fragment file

Per the Fragment-discipline rule (textbook-consensus metadata only),
this file records the morpheme inventory and its surface distribution.
[bondarenko-2022]'s head assignment — *gɘ* expones a Cont head, the two
suffixes are allomorphs of one Comp head — is paper-specific and lives
as Studies-local projections in `Studies/Bondarenko2022.lean`
(`buryatContExponent`, `buryatCompAllomorph`). Other treatments of
Mongolic say-complementizers ([knyazev-2016] on the categorial status
of Kalmyk *giž*; the areal SAY-grammaticalization pattern of
[matic-pakendorf-2013]) carve the morphology differently; the inventory
here is neutral between them.

## Matrix verbs

The clause-embedding verbs anchoring [bondarenko-2019],
[bondarenko-2020], and [bondarenko-2022] §4.4.3. All four are attested
in both frames ([bondarenko-2020]: nominalized frame at ex. 35–36,
50–51; bare gɘžɘ-CPs passim):

- *hanaxa* 'think ~ remember' — the headline alternating verb: bare CP
  = 'think' (non-veridical), nominalized complement = 'remember'
  (veridical via a pre-existence presupposition);
- *mɘdɘxɘ* 'know' — factive; also embeds polar questions;
- *xɘlɘxɘ* 'say' — speech-act verb;
- *duːlaxa* 'hear' — hearsay perception verb.

Constructor and definition names are ASCII romanizations (ɘ → e,
ː → vowel doubling, ž → zh, š → sh); `Complementizer.form` and
`Verb.form` carry the faithful transliterations.
-/

namespace Buryat

/-- The three clause-typing morphemes of the Barguzin Buryat embedded
clause ([bondarenko-2022] §4.3.1 ex. 30–32; [bondarenko-2020]). -/
inductive Complementizer where
  /-- *gɘ* — grammaticalized root of *gɘxɘ* 'say' ([bondarenko-2020]
  fn. 21: under verbs like 'hear' or 'see', gɘžɘ-clauses entail no
  speech act by the subject). -/
  | ge
  /-- *-Aːša* — agentive participle ([skribnik-2003]); appears when the
  clause complex combines with a nominal projection. -/
  | aasha
  /-- *-žA* — imperfective converb ([skribnik-2003]); appears when the
  clause combines directly with a verb (also found in analytical verb
  forms and sentential adjuncts, [bondarenko-2020] ex. 30). -/
  | zha
  deriving DecidableEq, Fintype, Repr

namespace Complementizer

/-- Surface form in Bondarenko's transliteration (capital letters mark
vowel-harmony archiphonemes). Display only. -/
def form : Complementizer → String
  | .ge    => "gɘ"
  | .aasha => "-Aːša"
  | .zha   => "-žA"

/-- The verb form each suffix derives on its host — participle for
*-Aːša*, converb for *-žA* (UD `VerbForm` cells); `none` for *gɘ*,
which is a verb root rather than a suffix. -/
def verbForm : Complementizer → Option UD.VerbForm
  | .ge    => none
  | .aasha => some .Part
  | .zha   => some .Conv

/-- Category of the adjacent projection licensing each suffix
([bondarenko-2022] §4.3.1): *-Aːša* combines with nominal projections,
*-žA* with verbs. -/
inductive Host where
  | nominal
  | verbal
  deriving DecidableEq, Fintype, Repr

/-- Surface distribution: the licensing host of each suffix; `none`
for the root *gɘ*. -/
def host : Complementizer → Option Host
  | .ge    => none
  | .aasha => some .nominal
  | .zha   => some .verbal

end Complementizer

/-! ### Clause-embedding verbs

Vendler class is left unset throughout, per the
`Verb.Aspect.vendlerClass` convention (`none` for clause-embedding
verbs). -/

/-- *hanaxa* 'think ~ remember'. The headline alternating verb of
[bondarenko-2019], [bondarenko-2020], and [bondarenko-2022] §4.4.3:
with a bare gɘžɘ-CP it is 'think'; with a nominalized participial
complement it is 'remember'. The `attitude` and `opaqueContext` values
record the bare-CP frame; the nominalized frame carries a pre-existence
presupposition (veridical 'remember'), a frame-conditioned meaning
tracked at the theory layer (`Semantics/Attitudes/PreExistence.lean`)
rather than in this entry. -/
def hanaxa : Verb where
  form := "hanaxa"
  complementType := .finiteClause
  altComplementType := some .gerund
  attitude := some (.doxastic .nonVeridical)
  opaqueContext := true

/-- *mɘdɘxɘ* 'know'. Factive doxastic in both frames ([bondarenko-2020]
ex. 36 for the nominalized frame); embeds polar questions
(*gü gɘžɘ* 'whether', [bondarenko-2020] ex. 3). -/
def medexe : Verb where
  form := "mɘdɘxɘ"
  complementType := .finiteClause
  altComplementType := some .gerund
  attitude := some (.doxastic .veridical)
  takesQuestionBase := true

/-- *xɘlɘxɘ* 'say'. Non-factive with bare CPs; nominalized complements
are existence-entailing ([bondarenko-2020] ex. 51; its fn. 30 notes
speaker variation on the nominalized frame). -/
def xelexe : Verb where
  form := "xɘlɘxɘ"
  complementType := .finiteClause
  altComplementType := some .gerund
  speechActVerb := true

/-- *duːlaxa* 'hear'. Hearsay perception verb: non-factive with bare
CPs, existence-entailing with nominalized complements
([bondarenko-2020] ex. 50; fn. 21 uses gɘžɘ-CPs under 'hear' as the
grammaticalization diagnostic for *gɘ*). -/
def duulaxa : Verb where
  form := "duːlaxa"
  complementType := .finiteClause
  altComplementType := some .gerund

end Buryat
