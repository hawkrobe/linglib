/-!
# Icelandic Verbs (Predicates fragment)
[wood-2015]

Consensus lexical data for Icelandic verbs participating in the
*-st* / *-na* alternations made famous by [wood-2015]. Each
entry carries only the surface forms and a Boolean for whether an
active variant exists — every other piece of information about each
verb (the *-st* classification, the anticausative-marking morpheme,
the [cuervo-2003]-style root decomposition, the
possessive-dative diagnostic) is paper-specific apparatus and lives
in `Wood2015`, where it can
participate in further analysis without polluting the Fragment
schema.

This is the same discipline applied to other Fragment lexicons in
linglib: textbook-consensus lexical data on this side; competing
analyses on the Studies side.

Note on classification: in [wood-2015]'s analysis *-st* (historically
*sik* → *-sk* → *-st*) is **not** an exponent of Voice. It is a defective
`[−participant]` clitic — a featural subset of the reflexive pronoun —
that merges in a specifier/argument position and cliticizes to the verb.
It appears across the descriptive categories [wood-2015] distinguishes
(anticausative, generic middle, figure reflexive, reflexive, inherent,
subject-experiencer, reciprocal); the Voice/v exponents proper are *-na*
(Voice{∅}), *-Ø* (the elsewhere Voice exponent), and *-ka* (v), with
*-na*-marked anticausatives like *brotna*. The merge-site classification
and the *-st* / *-na* contrast are formalized in the Wood2015 study file,
not here.
-/

namespace Icelandic.Predicates

-- ============================================================================
-- § 1: Verb Entry
-- ============================================================================

/-- A lexical entry for an Icelandic verb participating in the
    *-st* / *-na* alternation. Carries only consensus surface data. -/
structure IcelandicStVerb where
  /-- Active / bare form, if one exists. `none` for inherent *-st*
      verbs (*nálgast*, *minnast*) and the subject-experiencer
      *leiðast*. -/
  activeForm : Option String
  /-- The intransitive form: typically suffixed with *-st*, with
      *-na* on `brotna` and friends, or identical to the active when
      the alternation is unmarked. -/
  stForm : String
  /-- English gloss for human readers. -/
  gloss : String
  /-- Whether an active variant exists (must agree with
      `activeForm.isSome`; the redundancy is a sanity check used by
      the consistency theorem below). -/
  hasActiveVariant : Bool
  deriving Repr, BEq, DecidableEq

-- ============================================================================
-- § 2: Verb Data
-- ============================================================================

/-- *opna* / *opnast* 'open'. -/
def opnast : IcelandicStVerb :=
  { activeForm := some "opna"
    stForm := "opnast"
    gloss := "open"
    hasActiveVariant := true }

/-- *splundra* / *splundrast* 'shatter'. -/
def splundrast : IcelandicStVerb :=
  { activeForm := some "splundra"
    stForm := "splundrast"
    gloss := "shatter"
    hasActiveVariant := true }

/-- *brjóta* / *brotna* 'break' — the canonical *-na*-marked
    anticausative (cf. *opnast* / *splundrast* with *-st*). -/
def brotna : IcelandicStVerb :=
  { activeForm := some "brjóta"
    stForm := "brotna"
    gloss := "break"
    hasActiveVariant := true }

/-- *selja* / *seljast* 'sell'. -/
def seljast : IcelandicStVerb :=
  { activeForm := some "selja"
    stForm := "seljast"
    gloss := "sell"
    hasActiveVariant := true }

/-- *lesa* / *lesast* 'read'. -/
def lesast : IcelandicStVerb :=
  { activeForm := some "lesa"
    stForm := "lesast"
    gloss := "read"
    hasActiveVariant := true }

/-- *setja* / *setjast* 'sit down' — a posture verb. -/
def setjast : IcelandicStVerb :=
  { activeForm := some "setja"
    stForm := "setjast"
    gloss := "sit down"
    hasActiveVariant := true }

/-- *klæða* / *klæðast* 'dress'. -/
def klaedast : IcelandicStVerb :=
  { activeForm := some "klæða"
    stForm := "klæðast"
    gloss := "dress"
    hasActiveVariant := true }

/-- *nálgast* 'approach' — no active variant; *-st* is lexicalized. -/
def nalgast : IcelandicStVerb :=
  { activeForm := none
    stForm := "nálgast"
    gloss := "approach"
    hasActiveVariant := false }

/-- *minnast* 'remember' — no active variant. -/
def minnast : IcelandicStVerb :=
  { activeForm := none
    stForm := "minnast"
    gloss := "remember"
    hasActiveVariant := false }

/-- *leiðast* 'be bored' — subject-experiencer; no active variant.
    *Mér leiðist í skólanum* 'I am bored in school'. -/
def leidast : IcelandicStVerb :=
  { activeForm := none
    stForm := "leiðast"
    gloss := "be bored"
    hasActiveVariant := false }

/-- *kyssa* / *kyssast* 'kiss' — used in reciprocal contexts:
    *Þau kyssast* 'They kissed (each other)'. -/
def kyssast : IcelandicStVerb :=
  { activeForm := some "kyssa"
    stForm := "kyssast"
    gloss := "kiss"
    hasActiveVariant := true }

/-- All *-st*-marked verb entries (excludes *-na*-marked verbs like
    *brotna*). The Wood2015 study file projects analytical data
    (stType, marking, root structure) over the same ten verbs in the
    same order. -/
def allStVerbs : List IcelandicStVerb :=
  [opnast, splundrast, seljast, lesast, setjast, klaedast,
   nalgast, minnast, leidast, kyssast]

-- ============================================================================
-- § 3: Self-Consistency
-- ============================================================================

/-- Sanity check: every verb whose `hasActiveVariant` is true also
    has `activeForm.isSome`. Catches schema drift in either field. -/
theorem alternating_have_active :
    (allStVerbs.filter (·.hasActiveVariant)).all
      (fun v => v.activeForm.isSome) = true := by decide

end Icelandic.Predicates
