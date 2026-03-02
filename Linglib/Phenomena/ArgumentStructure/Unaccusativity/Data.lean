/-
Note: This file intentionally has no imports beyond Lean's Prelude.
All types here (String, Bool) are built-in. This keeps the diagnostic
data fully theory-neutral.
-/

/-!
# Unaccusativity Diagnostic Data
@cite{burzio-1986} @cite{levin-hovav-1995} @cite{perlmutter-1978} @cite{storment-2026}

Theory-neutral empirical data on unaccusativity diagnostics.

## Diagnostics

- **Quotative inversion** (QI): "whispered Mary" vs *"spoke Mary" (Storment 2026, NLLT)
- **There-insertion**: "there arrived a letter" vs *"there ran a man"
- **Locative inversion**: "into the room walked a man"
- **Resultative predication**: "the river froze solid" vs *"John ran tired"
- **Auxiliary selection**: Italian *è arrivato* (be) vs *ha dormito* (have)

-/

namespace Phenomena.ArgumentStructure.Unaccusativity.Data

/-- Syntactic diagnostics for unaccusativity. -/
inductive Diagnostic where
  | quotativeInversion       -- "whispered Mary" / *"spoke Mary"
  | thereInsertion           -- "there arrived a letter" / *"there ran a man"
  | locativeInversion        -- "into the room walked a man"
  | resultativePredication   -- "the river froze solid"
  | auxiliarySelection       -- Italian essere/avere split
  deriving DecidableEq, Repr, BEq

/-- Result of applying a diagnostic to a verb. -/
inductive DiagnosticResult where
  | passes    -- Verb behaves as unaccusative on this diagnostic
  | fails     -- Verb behaves as unergative/transitive
  | marginal  -- Intermediate or speaker-variable judgment
  deriving DecidableEq, Repr, BEq

/-- A single diagnostic judgment. -/
structure DiagnosticDatum where
  verbForm : String
  diagnostic : Diagnostic
  result : DiagnosticResult
  sentence : String
  language : String := "English"
  note : String := ""
  deriving Repr, BEq

-- ════════════════════════════════════════════════════
-- § Quotative Inversion Data (Storment 2026)
-- ════════════════════════════════════════════════════

def qi_whisper : DiagnosticDatum :=
  { verbForm := "whisper"
  , diagnostic := .quotativeInversion
  , result := .passes
  , sentence := "\"I'm tired,\" whispered Mary." }

def qi_murmur : DiagnosticDatum :=
  { verbForm := "murmur"
  , diagnostic := .quotativeInversion
  , result := .passes
  , sentence := "\"It's cold,\" murmured the child." }

def qi_shout : DiagnosticDatum :=
  { verbForm := "shout"
  , diagnostic := .quotativeInversion
  , result := .passes
  , sentence := "\"Watch out!\" shouted the guard." }

def qi_cry : DiagnosticDatum :=
  { verbForm := "cry"
  , diagnostic := .quotativeInversion
  , result := .passes
  , sentence := "\"Help!\" cried the sailor." }

def qi_scream : DiagnosticDatum :=
  { verbForm := "scream"
  , diagnostic := .quotativeInversion
  , result := .passes
  , sentence := "\"No!\" screamed the witness." }

def qi_mumble : DiagnosticDatum :=
  { verbForm := "mumble"
  , diagnostic := .quotativeInversion
  , result := .passes
  , sentence := "\"I don't know,\" mumbled the boy." }

def qi_mutter : DiagnosticDatum :=
  { verbForm := "mutter"
  , diagnostic := .quotativeInversion
  , result := .passes
  , sentence := "\"This is ridiculous,\" muttered the clerk." }

def qi_shriek : DiagnosticDatum :=
  { verbForm := "shriek"
  , diagnostic := .quotativeInversion
  , result := .passes
  , sentence := "\"A spider!\" shrieked the child." }

def qi_yell : DiagnosticDatum :=
  { verbForm := "yell"
  , diagnostic := .quotativeInversion
  , result := .passes
  , sentence := "\"Get down!\" yelled the sergeant." }

def qi_groan : DiagnosticDatum :=
  { verbForm := "groan"
  , diagnostic := .quotativeInversion
  , result := .passes
  , sentence := "\"Not again,\" groaned the student." }

def qi_grumble : DiagnosticDatum :=
  { verbForm := "grumble"
  , diagnostic := .quotativeInversion
  , result := .passes
  , sentence := "\"It's too early,\" grumbled the worker." }

def qi_hiss : DiagnosticDatum :=
  { verbForm := "hiss"
  , diagnostic := .quotativeInversion
  , result := .passes
  , sentence := "\"Be quiet,\" hissed the librarian." }

def qi_sigh : DiagnosticDatum :=
  { verbForm := "sigh"
  , diagnostic := .quotativeInversion
  , result := .passes
  , sentence := "\"If only,\" sighed the old woman." }

def qi_whimper : DiagnosticDatum :=
  { verbForm := "whimper"
  , diagnostic := .quotativeInversion
  , result := .passes
  , sentence := "\"It hurts,\" whimpered the child." }

def qi_snap : DiagnosticDatum :=
  { verbForm := "snap"
  , diagnostic := .quotativeInversion
  , result := .passes
  , sentence := "\"Enough!\" snapped the teacher." }

def qi_speak : DiagnosticDatum :=
  { verbForm := "speak"
  , diagnostic := .quotativeInversion
  , result := .fails
  , sentence := "*\"Hello,\" spoke Mary." }

def qi_talk : DiagnosticDatum :=
  { verbForm := "talk"
  , diagnostic := .quotativeInversion
  , result := .fails
  , sentence := "*\"Hello,\" talked Mary." }

/-- `say` passes QI (Storment 2026, ex. 9). Its VerbEntry captures the
    transitive indirect-speech frame ("John said that...") rather than the
    QI frame, so it is not connected to the smuggling bridge. -/
def qi_say : DiagnosticDatum :=
  { verbForm := "say"
  , diagnostic := .quotativeInversion
  , result := .passes
  , sentence := "\"I'm tired,\" said Mary."
  , note := "say is a standard QI verb; its VerbEntry captures the transitive indirect-speech frame rather than the QI frame" }

-- ════════════════════════════════════════════════════
-- § Quotative Inversion — Additional English Data (Storment 2026)
-- ════════════════════════════════════════════════════

/-- MoS verb with quote complement + PP goal still permits QI.
    @cite{storment-2026}: QI is blocked only when multiple DP arguments
    compete for Case licensing. A PP goal does not need Case. -/
def qi_whisper_transitive : DiagnosticDatum :=
  { verbForm := "whisper"
  , diagnostic := .quotativeInversion
  , result := .passes
  , sentence := "\"I know the answer,\" whispered the student to the teacher."
  , note := "Quote + PP goal: PP does not compete for Case, so QI is fine (Storment 2026, §5)" }

/-- QI with heavy subject (proper name): no degradation. -/
def qi_shout_heavysubj : DiagnosticDatum :=
  { verbForm := "shout"
  , diagnostic := .quotativeInversion
  , result := .passes
  , sentence := "\"Stop!\" shouted the police officer on duty."
  , note := "Heavy postverbal subject — QI still grammatical" }

/-- Pronominal subjects degrade QI (Storment 2026, §3: pronouns resist
    postverbal position in QI, unlike full DPs). -/
def qi_whisper_pronoun : DiagnosticDatum :=
  { verbForm := "whisper"
  , diagnostic := .quotativeInversion
  , result := .marginal
  , sentence := "?\"I'm tired,\" whispered she."
  , note := "Pronominal subjects degrade QI — full DPs preferred postverbally (§3)" }

/-- QI blocked with multiple DP arguments: the transitivity constraint
    (Storment 2026, §5, ex. 125). T⁰ can license only one DP (the theme);
    a second DP argument has no Case licenser. -/
def qi_whisper_double_obj : DiagnosticDatum :=
  { verbForm := "whisper"
  , diagnostic := .quotativeInversion
  , result := .fails
  , sentence := "*\"I will go to school,\" whispered Mary the news."
  , note := "QI blocked with two DP arguments — transitivity constraint from Case licensing (§5)" }

-- ════════════════════════════════════════════════════
-- § QI and LI: Distributional Contrasts (Storment 2026, §5–§6)
-- ════════════════════════════════════════════════════

/-! Quotative inversion and locative inversion share the same mechanism
    (smuggling of VP to Spec-VoiceP, Storment 2026 §6) but differ in
    their inputs and distribution:

    1. **Fronted constituent**: QI requires a quote; LI requires a locative PP
    2. **Transitivity constraint**: both QI and LI are blocked with multiple
       DP arguments, due to Case licensing
    3. **Pronominal subjects**: QI degrades with pronouns (§3); LI blocks them
    4. **Verb class**: QI targets MoS verbs; LI applies more broadly -/

/-- LI with transitive verb is ungrammatical. The transitivity constraint
    (Case licensing) applies to both QI and LI. -/
def li_kick : DiagnosticDatum :=
  { verbForm := "kick"
  , diagnostic := .locativeInversion
  , result := .fails
  , sentence := "*Into the room kicked the ball the player."
  , note := "LI blocked with transitive verb — both QI and LI show a transitivity constraint (Storment 2026, §5)" }

/-- LI with pronominal subject is strongly ungrammatical. -/
def li_arrive_pronoun : DiagnosticDatum :=
  { verbForm := "arrive"
  , diagnostic := .locativeInversion
  , result := .fails
  , sentence := "*Into the room arrived she."
  , note := "LI categorically blocks pronominal subjects (cf. QI which merely degrades them, §3)" }

-- ════════════════════════════════════════════════════
-- § Quotative Inversion — Setswana (Collins 1997, Storment 2026)
-- ════════════════════════════════════════════════════

/-! Setswana quotative inversion data from @cite{collins-1997}, discussed
    extensively in Storment (2026, §2–§3). Setswana QI uses class 17
    default subject agreement (SM17 `go`), never tracking the agent. -/

/-- Setswana QI with 'botsa' (ask). Collins 1997, cited as Storment ex. (4). -/
def qi_setswana_botsa : DiagnosticDatum :=
  { verbForm := "botsa"
  , diagnostic := .quotativeInversion
  , result := .passes
  , sentence := "'Le kae?' ga botsa Seabelo."
  , language := "Setswana"
  , note := "SM17.PST ask Seabelo — 'How are you?' asked Seabelo (Collins 1997)" }

/-- Setswana QI with 'bua' (say) + depictive. Storment ex. (11). -/
def qi_setswana_bua : DiagnosticDatum :=
  { verbForm := "bua"
  , diagnostic := .quotativeInversion
  , result := .passes
  , sentence := "'Dumela!' go bua Seabelo a tagilwe."
  , language := "Setswana"
  , note := "SM17 say Seabelo drunk — 'Hello!' says Seabelo drunk. Depictive follows Agent." }

/-- Setswana QI blocked with two DP arguments (transitivity constraint).
    Storment ex. (5). -/
def qi_setswana_transitivity : DiagnosticDatum :=
  { verbForm := "botsa"
  , diagnostic := .quotativeInversion
  , result := .fails
  , sentence := "*'Le kae?' ga botsa Mpho Seabelo."
  , language := "Setswana"
  , note := "SM17.PST ask Mpho Seabelo — transitivity constraint: two DPs block QI (§5)" }

-- ════════════════════════════════════════════════════
-- § QI Structural Evidence (Storment 2026, §3)
-- ════════════════════════════════════════════════════

/-! Structural evidence for the VP-smuggling analysis of QI (§3).
    These data test the positions of Theme, Agent, VP, and Quote
    predicted by the smuggling derivation (§4):

    - **Theme** → Spec-TP (controls agreement, licenses raising)
    - **Agent** → Spec-vP (in-situ, conjoint form, doesn't control agreement)
    - **VP** → Spec-VoiceP (VP-internal material precedes Agent)
    - **Quote** → DiscourseP (clause-external, can split, need not be grammatical) -/

/-- Type of structural evidence for QI clause structure. -/
inductive QIStructuralTest where
  | agreement           -- What controls verbal agreement in QI (§3.1)
  | parasiticGap        -- Whether QI licenses parasitic gaps (§3.2)
  | subjectRaising      -- Whether QI is compatible with subject raising (§3.3)
  | conjointDisjoint    -- Setswana CJ/DJ alternation — Agent position (§3.4)
  | quoteCategory       -- Quote behaves as clause-external (§3.5)
  | constituentOrdering -- Position of constituents relative to Agent
  deriving DecidableEq, Repr, BEq

/-- A structural evidence datum for QI clause structure. -/
structure QIStructuralDatum where
  test : QIStructuralTest
  result : DiagnosticResult
  sentence : String
  language : String := "English"
  note : String := ""
  deriving Repr, BEq

-- § Agreement (§3.1)

/-- English QI: verb agrees with postverbal agent, not with quote.
    Storment ex. (40). -/
def qi_agreement_english : QIStructuralDatum :=
  { test := .agreement
  , result := .passes
  , sentence := "\"Avoid beef,\" advise all the New Age dieticians."
  , note := "Verb 'advise' (pl) agrees with postverbal agent 'dieticians' (pl), not quote" }

/-- Setswana QI: SM surfaces as default SM17 (go), not agent's class.
    Storment exs. (77)–(80): go replaces ke (1sg), o (2sg), di (cl.10). -/
def qi_agreement_setswana : QIStructuralDatum :=
  { test := .agreement
  , result := .passes
  , sentence := "'Dumela,' go bua nna."
  , language := "Setswana"
  , note := "SM17 (go) instead of SM.1SG (ke) — default agreement, Agent not in Spec-TP" }

-- § Parasitic Gaps (§3.2)

/-- QI blocks parasitic gap licensing: Theme undergoes A-movement,
    not Ā-movement, so it cannot license a parasitic gap.
    Storment ex. (62a). -/
def qi_parasitic_gap_blocked : QIStructuralDatum :=
  { test := .parasiticGap
  , result := .fails
  , sentence := "*\"We should leave,\" thought Max without actually saying __."
  , note := "PG blocked: Theme A-movement (smuggling) cannot license PGs (§3.2)" }

/-- Non-QI preposed quote DOES license a parasitic gap:
    quote undergoes Ā-movement (topicalization), which licenses PGs.
    Storment ex. (62b). -/
def qi_parasitic_gap_baseline : QIStructuralDatum :=
  { test := .parasiticGap
  , result := .passes
  , sentence := "\"We should leave,\" Max thought without actually saying __."
  , note := "PG OK: preposed quote undergoes Ā-movement (topicalization), licensing PGs" }

-- § Subject Raising (§3.3)

/-- QI is compatible with subject-to-subject raising: quotative Theme
    can A-move through embedded Spec-TP to matrix Spec-TP.
    Storment ex. (67a). -/
def qi_raising : QIStructuralDatum :=
  { test := .subjectRaising
  , result := .passes
  , sentence := "\"Where did the wheat go?\" seemed to say the heron."
  , note := "Theme raises from embedded to matrix Spec-TP — A-movement chain (§3.3)" }

-- § Conjoint/Disjoint (§3.4)

/-- Setswana: disjoint morpheme 'a' blocked in QI — Agent remains
    vP-internal (conjoint position). Storment ex. (87). -/
def qi_conjoint_disjoint : QIStructuralDatum :=
  { test := .conjointDisjoint
  , result := .fails
  , sentence := "'Dumela,' go (*a) bua Seabelo."
  , language := "Setswana"
  , note := "Disjoint 'a' blocked: Agent in Spec-vP (vP-internal = conjoint domain, §3.4)" }

-- § Quote Category (§3.5)

/-- Quote can split around verb + agent: evidence for clause-external
    position (DiscourseP). Storment ex. (90). -/
def qi_quote_split : QIStructuralDatum :=
  { test := .quoteCategory
  , result := .passes
  , sentence := "\"But,\" said Frodo, \"that is a long way off.\""
  , note := "Split quote: quote is in DiscourseP, not a single constituent in Spec-TP (§3.5)" }

/-- Quote need not be grammatical: further evidence for clause-external
    status. Storment ex. (96a). -/
def qi_quote_nongrammatical : QIStructuralDatum :=
  { test := .quoteCategory
  , result := .passes
  , sentence := "\"Pop!\" goes the weasel."
  , note := "'Pop!' is not a grammatical sentence — quote is clause-external (§3.5)" }

-- § Constituent Ordering (Storment 2026, §2)

/-- Setswana: depictive follows Agent — depictives are vP-external
    adjuncts, so they stay behind when VP smuggles. Storment ex. (11). -/
def qi_ordering_depictive : QIStructuralDatum :=
  { test := .constituentOrdering
  , result := .passes
  , sentence := "'Dumela!' go bua Seabelo a tagilwe."
  , language := "Setswana"
  , note := "Depictive 'a tagilwe' (drunk) follows Agent — vP-external, stays in situ" }

/-- Setswana: manner adverb follows Agent — manner adverbs are
    vP-external, so they stay behind. Storment ex. (21). -/
def qi_ordering_manner : QIStructuralDatum :=
  { test := .constituentOrdering
  , result := .passes
  , sentence := "'Titi o molato,' go bua kgosi kapela."
  , language := "Setswana"
  , note := "Manner 'kapela' (quickly) follows Agent — vP-external, stays in situ" }

/-- Setswana: purpose clause follows Agent — purpose clauses are
    vP-external adjuncts. Storment ex. (17). -/
def qi_ordering_purpose : QIStructuralDatum :=
  { test := .constituentOrdering
  , result := .passes
  , sentence := "'Molelo!' go go-ile Seabelo go kopa thuso."
  , language := "Setswana"
  , note := "Purpose 'go kopa thuso' (to call for help) follows Agent — vP-external" }

/-- Setswana: restructuring complement precedes Agent — VP-internal
    material moves with VP via smuggling. Storment ex. (27). -/
def qi_ordering_complement : QIStructuralDatum :=
  { test := .constituentOrdering
  , result := .passes
  , sentence := "'Ke a go rata,' go batla go bua Seabelo."
  , language := "Setswana"
  , note := "Control comp 'batla go bua' (want to say) precedes Agent — VP-internal, moves with VP" }

/-- All QI structural evidence data points. -/
def allStructuralData : List QIStructuralDatum :=
  [ qi_agreement_english, qi_agreement_setswana
  , qi_parasitic_gap_blocked, qi_parasitic_gap_baseline
  , qi_raising
  , qi_conjoint_disjoint
  , qi_quote_split, qi_quote_nongrammatical
  , qi_ordering_depictive, qi_ordering_manner
  , qi_ordering_purpose, qi_ordering_complement ]

-- ════════════════════════════════════════════════════
-- § There-Insertion Data
-- ════════════════════════════════════════════════════

def there_arrive : DiagnosticDatum :=
  { verbForm := "arrive"
  , diagnostic := .thereInsertion
  , result := .passes
  , sentence := "There arrived a letter for you." }

def there_run : DiagnosticDatum :=
  { verbForm := "run"
  , diagnostic := .thereInsertion
  , result := .fails
  , sentence := "*There ran a man down the street." }

def there_sleep : DiagnosticDatum :=
  { verbForm := "sleep"
  , diagnostic := .thereInsertion
  , result := .fails
  , sentence := "*There slept a child in the bed." }

-- ════════════════════════════════════════════════════
-- § Locative Inversion Data
-- ════════════════════════════════════════════════════

def loc_arrive : DiagnosticDatum :=
  { verbForm := "arrive"
  , diagnostic := .locativeInversion
  , result := .passes
  , sentence := "Into the room arrived a messenger." }

def loc_whisper : DiagnosticDatum :=
  { verbForm := "whisper"
  , diagnostic := .locativeInversion
  , result := .marginal
  , sentence := "?From the back of the room whispered a voice."
  , note := "MoS verbs show variable acceptability in locative inversion" }

/-- All diagnostic data points. -/
def allData : List DiagnosticDatum :=
  [ qi_whisper, qi_murmur, qi_shout, qi_cry, qi_scream
  , qi_mumble, qi_mutter, qi_shriek, qi_yell, qi_groan
  , qi_grumble, qi_hiss, qi_sigh, qi_whimper, qi_snap
  , qi_speak, qi_talk, qi_say
  , qi_whisper_transitive, qi_shout_heavysubj, qi_whisper_pronoun
  , qi_whisper_double_obj
  , qi_setswana_botsa, qi_setswana_bua, qi_setswana_transitivity
  , there_arrive, there_run, there_sleep
  , loc_arrive, loc_whisper
  , li_kick, li_arrive_pronoun ]

/-- QI data only. -/
def qiData : List DiagnosticDatum :=
  allData.filter λ d => d.diagnostic == .quotativeInversion

/-- Locative inversion data only. -/
def liData : List DiagnosticDatum :=
  allData.filter λ d => d.diagnostic == .locativeInversion

end Phenomena.ArgumentStructure.Unaccusativity.Data
