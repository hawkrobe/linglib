/-!
# Complementation — complement selection and control

[noonan-2007]

Per-entry complementation features: which complement type a predicate selects
(`ComplementType`) and, for infinitival complements, its control type
(`ControlType`). Composed into lexical-core structures as fields
(`Verb.ArgStructure.complementType`), Pronoun-pattern style.

The cross-linguistic complementation typology also lives here:
[noonan-2007]'s six complement-clause types (`NoonanCompType`) and twelve
complement-taking-predicate classes (`CTPClass`) with their default reality
status (`RealityStatus`, `ctpRealityStatus`). The bridge between the two
inventories (`ComplementType ↔ NoonanCompType`) is paper-anchored in
`Studies/Noonan2007.lean`.

## Main declarations

* `ComplementType` — complement frame a predicate selects (English-leaning
  inventory: NP, double object, clausal, …)
* `ControlType` — subject/object control vs raising for infinitival complements
* `NoonanCompType` + `isReduced` — [noonan-2007]'s complement-clause types
* `CTPClass`, `RealityStatus`, `ctpRealityStatus` — [noonan-2007]'s CTP
  classification and realis/irrealis defaults
-/

/--
Complement type that the verb selects.

- Finite: "that" clauses ("John knows that Mary left")
- Infinitival: "to" complements ("John managed to leave")
- Gerund: "-ing" complements ("John stopped smoking")
- NP: Direct object ("John kicked the ball")
- None: Intransitive ("John slept")
-/
inductive ComplementType where
  | none            -- Intransitive
  | np              -- Transitive with NP object
  | np_np           -- Ditransitive: "give X Y"
  | np_pp           -- NP + PP: "put X on Y"
  | finiteClause    -- "that" clause
  | infinitival     -- "to" VP
  | gerund          -- "-ing" VP
  | smallClause     -- "consider X happy"
  | question        -- Embedded question "wonder who"
  deriving DecidableEq, Repr

/-- Is this complement type finite (i.e., does it contain a tense head)?

    Finite complements (.finiteClause,.question) have independent tense
    morphology; non-finite complements (.infinitival,.gerund,.smallClause)
    do not. -/
def ComplementType.isFinite : ComplementType → Bool
  | .finiteClause | .question => true
  | _ => false

/-- Is this complement type a nominal (DP) argument?

    Nominal complements project DP: the verb selects a noun phrase
    in object position. Relevant to c-selection in coordination:
    a verb that only selects nominal complements cannot independently
    license a CP conjunct ([schwarzer-2026]). -/
def ComplementType.isNominal : ComplementType → Bool
  | .np | .np_np | .np_pp => true
  | _ => false

/-- Is this complement type a clausal (CP) argument?

    Clausal complements project CP or reduced clausal structure.
    This covers finite clauses (*dass*-clauses), infinitivals,
    gerunds, small clauses, and embedded questions. -/
def ComplementType.isClausal : ComplementType → Bool
  | .finiteClause | .infinitival | .gerund | .smallClause | .question => true
  | _ => false

/--
Control type for verbs with infinitival complements.
-/
inductive ControlType where
  | subjectControl  -- "John tried to leave" (John = leaver)
  | objectControl   -- "John persuaded Mary to leave" (Mary = leaver)
  | raising         -- "John seems to be happy" (no theta role for matrix subject)
  | none            -- Not applicable
  deriving DecidableEq, Repr

/-! ### Noonan complement typology -/

/-- The six major complement types attested cross-linguistically.
    Ordered roughly from most to least "finite" (Noonan's "balanced" to
    "deranked"). -/
inductive NoonanCompType where
  | indicative     -- Finite clause with indicative mood marking
  | subjunctive    -- Finite clause with subjunctive/irrealis marking
  | paratactic     -- Juxtaposed clause, no subordinator
  | infinitive     -- Non-finite with "to" or equivalent
  | nominalized    -- Gerund / action nominal
  | participle     -- Participial complement
  deriving DecidableEq, Repr, BEq

/-- Is this complement type "reduced" (non-finite)? -/
def NoonanCompType.isReduced : NoonanCompType → Bool
  | .infinitive  => true
  | .nominalized => true
  | .participle  => true
  | _            => false

/-- Noonan's twelve CTP classes, organized by semantic contribution.

    The ordering follows [noonan-2007] Table 2.1 from most to least
    "assertive":
    - Utterance/propAttitude/pretence: report/judge propositional content
    - Commentative/knowledge: evaluate/know propositional content
    - Perception: direct experience
    - Desiderative/manipulative/modal: irrealis orientation
    - Achievement/phasal: aspectual
    - Negative: negation as CTP -/
inductive CTPClass where
  | utterance       -- say, tell, report
  | propAttitude    -- believe, think, suppose
  | pretence        -- pretend, act as if
  | commentative    -- regret, be sorry
  | knowledge       -- know, realize, discover
  | perception      -- see, hear, feel
  | desiderative    -- want, wish, hope
  | manipulative    -- make, cause, persuade, order
  | modal           -- can, must, should
  | achievement     -- positive: manage, dare; negative: try, forget to, avoid (§3.2.10)
  | phasal          -- start, stop, continue
  /-- A CTP whose sole semantic content is sentential negation
      ([noonan-2007] §3.2.13). Typologically rare; canonical examples
      are Fijian *sega* and Shuswap negative predicates. English `avoid`,
      `refrain`, `prevent` are NOT in this class — they are *negative
      achievement* predicates (§3.2.10). -/
  | negative
  deriving DecidableEq, Repr, BEq

/-- The fundamental realis/irrealis split that predicts complement type
    selection. Realis CTPs tend toward indicative; irrealis toward
    subjunctive/infinitive ([noonan-2007] §2.3). -/
inductive RealityStatus where
  | realis    -- CTP asserts or presupposes complement truth
  | irrealis  -- CTP does not commit to complement truth
  deriving DecidableEq, Repr

/-- Default reality status of each CTP class ([noonan-2007] Table 2.3). -/
def ctpRealityStatus : CTPClass → RealityStatus
  | .utterance    => .realis
  | .propAttitude => .realis
  | .pretence     => .irrealis
  | .commentative => .realis
  | .knowledge    => .realis
  | .perception   => .realis
  | .desiderative => .irrealis
  | .manipulative => .irrealis
  | .modal        => .irrealis
  | .achievement  => .irrealis
  | .phasal       => .realis
  | .negative     => .irrealis
