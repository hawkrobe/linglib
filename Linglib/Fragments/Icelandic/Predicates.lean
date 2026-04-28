/-!
# Icelandic Verbs (Predicates fragment)
@cite{wood-2015}

Consensus lexical data for Icelandic verbs participating in the
*-st* / *-na* alternations made famous by @cite{wood-2015}. Each
entry carries only the surface forms and a Boolean for whether an
active variant exists — every other piece of information about each
verb (the *-st* classification, the anticausative-marking morpheme,
the @cite{cuervo-2003}-style root decomposition, the
possessive-dative diagnostic) is paper-specific apparatus and lives
in `Phenomena.ArgumentStructure.Studies.Wood2015`, where it can
participate in further analysis without polluting the Fragment
schema.

This is the same discipline applied to other Fragment lexicons in
linglib: textbook-consensus lexical data on this side; competing
analyses on the Studies side.

Note on classification: the morphological reflex *-st* (historically
*sik* → *-sk* → *-st*) realizes Voice across at least six descriptive
categories that @cite{wood-2015} identifies — anticausative, middle,
reflexive, inherent, subject-experiencer, reciprocal — plus *-na*-marked
anticausatives like *brotna*. The *-st* / *-na* contrast and the
parameters that distinguish these categories are formalized in the
Wood2015 study file, not here.
-/

namespace Fragments.Icelandic.Predicates

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

/-- *baða* / *baðast* 'bathe'. -/
def badast : IcelandicStVerb :=
  { activeForm := some "baða"
    stForm := "baðast"
    gloss := "bathe"
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
  [opnast, splundrast, seljast, lesast, badast, klaedast,
   nalgast, minnast, leidast, kyssast]

-- ============================================================================
-- § 3: Self-Consistency
-- ============================================================================

/-- Sanity check: every verb whose `hasActiveVariant` is true also
    has `activeForm.isSome`. Catches schema drift in either field. -/
theorem alternating_have_active :
    (allStVerbs.filter (·.hasActiveVariant)).all
      (fun v => v.activeForm.isSome) = true := by decide

end Fragments.Icelandic.Predicates
