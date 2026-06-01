import Linglib.Semantics.Verb.Basic

/-!
# Buryat Complementizers and Clause-Embedding Verbs
@cite{bondarenko-2022} @cite{bondarenko-2020} @cite{bondarenko-2017}

Modern Barguzin Buryat (Mongolic; Russian Federation) — clause-typing
morphology and the matrix verbs that select bare vs. nominalized
embedded clauses (@cite{bondarenko-2022} §4.3.1).

## Three clause-typing morphemes

- **gɔ** 'say' — verbal source; @cite{bondarenko-2022} §4.3.1 analyses
  it as the overt exponent of ContP (the projection introducing the
  CONT function at the left periphery of Cont-CPs). When *gɔ* is
  present, the embedded clause is a Cont-CP.
- **-Aːša** / **-žA** — Comp allomorphs of the participial nominaliser
  (vowel harmony / aspect-conditioned). Closes off a non-finite
  embedded clause; co-occurs with both Cont-CPs (alongside *gɔ*) and
  Sit-CPs (without *gɔ*).
- The contrast (Cont-CP = with *gɔ*; Sit-CP = without *gɔ*) is what
  makes Buryat the chapter's headline language for the bare/
  nominalized cut.

## Scope of this Fragment file

Per the project Fragment-discipline rule (textbook-consensus
metadata only): this file exposes only the **morphological inventory
and surface co-occurrence facts**. The Bondarenko-specific
ContP-bearing projection (`bearsContP`) lives as a Studies-local
projection in `Studies/Bondarenko2022.lean`,
not as a field of the morpheme record. Alternative analyses
(Knyazev's spanning-complementiser account, Stassen's serial-verb
analysis of *gɔ*) treat the morphology differently; this fragment
stays neutral.

## Matrix verbs

The verbs that anchor Bondarenko's bare-vs-nominalized arguments:

- *xanaxa* 'think / remember' — polysemous attitude verb; bare
  complement = thinking (Cont reading), nominalized complement =
  remembering (DP-argument reading). Anchors §4.4.3 about-argument.
- *boloxo* 'happen / become' — change-of-state verb taking situation
  arguments; bare complement reading.
- *medexe* 'know' — factive doxastic.
- *xelexe* 'say' — speech act verb; selects bare *gɔ*-marked
  complement.

-/

namespace Buryat.Complementizers


-- ════════════════════════════════════════════════════════════════
-- § 1. Clause-typing morpheme inventory
-- ════════════════════════════════════════════════════════════════

/-- The three clause-typing morphemes covered here. *Aːša* / *žA* are
    treated as separate morphemes by their phonological/aspectual
    distribution; some accounts unify them as allomorphs of a single
    Comp head. -/
inductive BuryatComplementizer where
  /-- *gɔ* — verbal "say"-source; overt exponent of ContP per
      @cite{bondarenko-2022} §4.3.1. ASCII identifier `gO` for kernel-
      reducer compatibility; the form string preserves the unicode. -/
  | gO
  /-- *-Aːša* — participial nominaliser (imperfective/non-future).
      ASCII identifier `aSha` for kernel-reducer compatibility. -/
  | aSha
  /-- *-žA* — participial nominaliser (perfective/factive).
      ASCII identifier `zhA` for kernel-reducer compatibility. -/
  | zhA
  deriving DecidableEq, Repr

/-- Phonological form (rough Latinisation; vowel-harmony variants
    abstracted away for citation purposes). -/
def BuryatComplementizer.form : BuryatComplementizer → String
  | .gO   => "gɔ"
  | .aSha => "-Aːša"
  | .zhA   => "-žA"

/-- Whether the morpheme is verbally sourced (vs. nominal/participial).
    *gɔ* is verbally sourced (from "say"); the participial nominalisers
    are not. -/
def BuryatComplementizer.isVerbal : BuryatComplementizer → Bool
  | .gO => true
  | _   => false

/-- Whether the morpheme is a participial nominaliser. The split into
    *Aːša* / *žA* by the participial allomorphy follows
    @cite{bondarenko-2022} §4.3.1. -/
def BuryatComplementizer.isParticipial : BuryatComplementizer → Bool
  | .aSha => true
  | .zhA   => true
  | .gO   => false

/-- Sanity check: the verbal/participial axes partition the inventory. -/
theorem verbal_xor_participial (c : BuryatComplementizer) :
    c.isVerbal = !c.isParticipial := by cases c <;> decide

-- ════════════════════════════════════════════════════════════════
-- § 2. Matrix verb entries
-- ════════════════════════════════════════════════════════════════

/-- *xanaxa* — 'think / remember'. Bondarenko's anchor verb for the
    bare-vs-nominalized argument-structure alternation
    (@cite{bondarenko-2022} §4.4.3). With bare complement → thinking
    (Cont reading); with nominalized complement → remembering
    (DP-argument reading + about-presupposition).

    Citation form is the eventive/cognition sense; the
    polysemy is tracked via `altComplementType`. -/
def xanaxa : VerbCore where
  form := "xanaxa"
  complementType := .finiteClause
  altComplementType := some .finiteClause
  attitude := some (.doxastic .nonVeridical)
  vendlerClass := some .activity
  opaqueContext := true

/-- *boloxo* — 'happen / become'. Eventive change-of-state verb.
    Selects situation-typed argument; relevant to §4.3.3 cross-
    linguistic-occurrence-verb generalization. -/
def boloxo : VerbCore where
  form := "boloxo"
  complementType := .finiteClause
  vendlerClass := some .achievement
  unaccusative := true

/-- *medexe* — 'know'. Factive doxastic; stative. -/
def medexe : VerbCore where
  form := "medexe"
  complementType := .finiteClause
  attitude := some (.doxastic .veridical)
  vendlerClass := some .state

/-- *xelexe* — 'say'. Speech-act verb; selects bare *gɔ*-marked
    complement per @cite{bondarenko-2022} §4.3.1. -/
def xelexe : VerbCore where
  form := "xelexe"
  complementType := .finiteClause
  speechActVerb := true
  vendlerClass := some .activity

-- ════════════════════════════════════════════════════════════════
-- § 3. Theorems
-- ════════════════════════════════════════════════════════════════

/-- *xanaxa* and *boloxo* are non-stative; *medexe* is stative.
    Consensus stativity per Vendler. -/
theorem stativity_split :
    xanaxa.vendlerClass = some .activity ∧
    boloxo.vendlerClass = some .achievement ∧
    medexe.vendlerClass = some .state ∧
    xelexe.vendlerClass = some .activity := ⟨rfl, rfl, rfl, rfl⟩

/-- *xanaxa* is the only verb here with two complement frames
    available (the bare-vs-nominalized alternation Bondarenko exploits
    in §4.4.3). -/
theorem only_xanaxa_alternates :
    xanaxa.altComplementType.isSome = true ∧
    boloxo.altComplementType.isSome = false ∧
    medexe.altComplementType.isSome = false ∧
    xelexe.altComplementType.isSome = false := ⟨rfl, rfl, rfl, rfl⟩

end Buryat.Complementizers
