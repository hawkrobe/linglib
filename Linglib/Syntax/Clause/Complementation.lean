/-!
# Clause complementation: complement-clause typology

[noonan-2007] [deal-2026]

[noonan-2007]'s complement-clause types and complement-taking-predicate (CTP)
classes, plus [deal-2026]'s notional-complement surface structures and CP
external-shell inventory. Graduated from the dissolved `Typology/` drawer; the
unconsumed WALS subordination + Cristofaro complementation typology (and its
`native_decide` distribution theorems) was dropped.

## Main definitions

* `NoonanCompType` + `isReduced` — Noonan's complement-clause types.
* `CTPClass`, `RealityStatus`, `ctpRealityStatus`, `CTPDatum` — CTP classification.
* `ComplementClauseStructure` — surface complement-clause structure ([deal-2026]).
* `CPShell` / `CPShellInventory` / `isAttestedShell` — CP external-shell cartography ([deal-2026]).
-/

namespace Clause.Complementation

-- ============================================================================
-- §1. Noonan Complement Typology
-- ============================================================================

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
  deriving DecidableEq, Repr

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
  deriving DecidableEq, Repr

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

/-- A cross-linguistic datum about a complement-taking predicate.

    Each datum records:
    - Language and verb identification
    - CTP class (Noonan Table 2.1)
    - Which complement types this verb allows in this language
    - Reality status (defaults to `ctpRealityStatus ctpClass`, but
      overridable for exceptions)
    - Control/raising properties ([noonan-2007] §2.1--2.2)
    - Negative raising -/
structure CTPDatum where
  language : String
  verb : String
  ctpClass : CTPClass
  allowedCompTypes : List NoonanCompType
  realityStatus : RealityStatus
  hasEquiDeletion : Bool
  hasRaising : Bool
  hasNegativeRaising : Bool
  deriving DecidableEq, Repr

-- §8. Notional-Complement Surface Structure ([deal-2026])
-- ============================================================================

/-! ### Theory-neutral surface enum

Following the cross-framework reconciler discipline, `ComplementClauseStructure`
describes the *surface pattern* a notional complement clause realises, without
committing to one framework's internal analysis. Each Theory projects its native
account into this enum: HPSG always projects `headExternalModifier` for true
RCs; Minimalist (with [deal-2026]) projects `abarInternalCP` for Nez Perce
relative-embeddings (REs) and `barePropositionalCP` for English `that`-clauses.
-/

/-- Surface-pattern enumeration of notional-complement-clause shapes attested
    cross-linguistically.

    [deal-2026]'s typology dissolves the Kayne/Arsenij\'evi\'c ([kayne-2008],
    [kayne-2014], [arsenijevic-2009]) universalist claim that all
    clausal complementation is relativization. The *surface* options are
    independent of any one framework's commitments about underlying structure.

    The Kayne/Arsenij\'evi\'c universalist hypothesis is now a single decidable
    statement: `∀ c : ComplementClauseStructure, c = .abarInternalCP`. Deal 2026
    refutes it by exhibiting `.barePropositionalCP` as an attested cell
    (Nez Perce simplex embeddings and English *think*-complementation). -/
inductive ComplementClauseStructure where
  /-- CP with internal Ā-dependency from a high functional projection above TP.
      Nez Perce REs ([deal-2026]), Adyghe REs ([caponigro-polinsky-2011]),
      Bulgarian REs ([krapova-2010]). -/
  | abarInternalCP
  /-- Bare CP with no internal Ā-dependency. Nez Perce simplex embeddings and
      English *think*-complementation ([deal-2026]). -/
  | barePropositionalCP
  /-- CP wrapped in a nominal projection (D, possibly with N). Washo factive
      complementation ([hanink-bochnak-2017], [bochnak-hanink-2021]),
      Ndebele ([pietraszko-2019], with additional P shell). -/
  | nominalization
  /-- True relative clause: an adjunct modifier of a head noun. The pattern
      that Kayne/Arsenij\'evi\'c claim subsumes all others. -/
  | headExternalModifier
  /-- Internally-headed relative clause (Bambara, Navajo). -/
  | headInternalRelative
  /-- High adjunct, not complementation at all. Amahuaca attitude reports
      ([deal-2026] §3, citing Clem 2022 — needs separate bib entry). -/
  | adjunct
  deriving DecidableEq, Repr

-- ============================================================================
-- §9. CP External Shell Inventory ([deal-2026] Table 79)
-- ============================================================================

/-! ### CP-external wrapping shells

Where `ComplementSize` and `ClauseSpine` (Syntax/Minimalist/) record
*internal* clause height (vP/TP/CP/NmlzP), `CPShell` records what wraps the CP
*externally*. Deal 2026's Table 79 cross-classifies the two axes; this file
houses the external axis as Fragment-importable substrate.

Anchored to [deal-2026] Table 79; placement of individual languages in
Table 79 cells consumes per-language Fragment data and lives in
`Studies/Deal2026.lean`. -/

/-- A wrapping head category that may appear above a CP in a notional complement.
    [deal-2026] Table 79 attests three: D (Washo, Adyghe), N (Adyghe),
    P (Bulgarian, Ndebele). C is included as the base case to give a uniform
    representation of `bareCP` as `[.C]`. -/
inductive CPShell where
  /-- The CP itself (always present). -/
  | c
  /-- D shell (determiner wrapping CP). -/
  | d
  /-- N shell (nominal head between D and CP). -/
  | n
  /-- P shell (preposition wrapping the CP-headed argument). -/
  | p
  deriving DecidableEq, Repr

/-- An ordered shell list, innermost first.

    Convention: head element is the C of the CP itself; subsequent elements
    are progressively more peripheral wrappers. So `[.c, .d]` = `dCP` (D wraps
    CP), `[.c, .n, .d]` = `dnCP` (D wraps N wraps CP), `[.c, .d, .p]` = `pdCP`
    (P wraps D wraps CP). -/
abbrev CPShellInventory := List CPShell

/-- Predicate: this shell inventory is attested in [deal-2026] Table 79.

    Six attested shapes (one per cell), four shell-shapes:
    - `[.c]`        = `bareCP` (V CP row)
    - `[.c, .d]`    = `dCP`    (V D CP — Washo per [bochnak-hanink-2021])
    - `[.c, .n, .d]` = `dnCP`  (V D N CP row — Adyghe)
    - `[.c, .d, .p]` = `pdCP`  (V P D CP row — Bulgarian, Ndebele) -/
def isAttestedShell : CPShellInventory → Bool
  | [.c] => true
  | [.c, .d] => true
  | [.c, .n, .d] => true
  | [.c, .d, .p] => true
  | _ => false

/-- The bare-CP cell (Nez Perce REs and simplex; English *think*). -/
def bareCP : CPShellInventory := [.c]

/-- The V D CP cell (Washo per [bochnak-hanink-2021]). -/
def dCP : CPShellInventory := [.c, .d]

/-- The V D N CP cell (Adyghe REs per [caponigro-polinsky-2011]). -/
def dnCP : CPShellInventory := [.c, .n, .d]

/-- The V P D CP cell (Bulgarian REs per [krapova-2010];
    Ndebele per [pietraszko-2019]). -/
def pdCP : CPShellInventory := [.c, .d, .p]

/-! ### Concrete facts on the named witnesses

The full implicational generalisations ("every attested inventory containing P
also contains D") are folklore from inspection of the four named cells. We
prove the consumed facts directly on the named shells; the universal claim is
tracked in [deal-2026] Table 79 commentary, not as a Lean theorem
(general `List.Mem` reasoning over `CPShellInventory` would be substantial
boilerplate without proportionate payoff). -/

/-- The four named witnesses are all attested (Deal 2026 Table 79). -/
theorem named_shells_attested :
    isAttestedShell bareCP = true ∧
    isAttestedShell dCP = true ∧
    isAttestedShell dnCP = true ∧
    isAttestedShell pdCP = true := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- The pdCP cell contains both P and D — the empirical generalisation that
    P-shelling co-occurs with D-shelling. -/
theorem pdCP_contains_p_and_d : CPShell.p ∈ pdCP ∧ CPShell.d ∈ pdCP := by
  refine ⟨?_, ?_⟩ <;> decide

/-- The dnCP cell contains both N and D — N appears only inside a D shell. -/
theorem dnCP_contains_n_and_d : CPShell.n ∈ dnCP ∧ CPShell.d ∈ dnCP := by
  refine ⟨?_, ?_⟩ <;> decide

/-- Every named shell contains C (the CP itself). -/
theorem named_shells_contain_c :
    CPShell.c ∈ bareCP ∧ CPShell.c ∈ dCP ∧
    CPShell.c ∈ dnCP ∧ CPShell.c ∈ pdCP := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- An unattested example: `V P CP` (P with no D shell) — [deal-2026]
    Table 79 has no such cell. -/
theorem pCP_not_attested : isAttestedShell [.c, .p] = false := rfl

/-- Another unattested example: `V N CP` (N with no D shell). -/
theorem nCP_not_attested : isAttestedShell [.c, .n] = false := rfl

end Clause.Complementation
