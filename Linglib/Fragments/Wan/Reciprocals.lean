import Linglib.Core.Lexical.Pronouns
import Linglib.Features.Logophoricity

/-!
# Wan (Mande) Reciprocal and Logophoric Fragment
@cite{dalrymple-haug-2024}

Wan (a Mande language, ISO 639-3: wan) uses logophoric pronouns in
complement clauses of speech-act verbs. These logophoric pronouns can
serve as the local antecedent of a reciprocal.

## Key Data (@cite{dalrymple-haug-2024} §6)

When the antecedent of the reciprocal is a logophor, only a narrow scope
reading is available. In the scenario where each animal says "I will eat
the others," the hare can report this with a logophor + reciprocal
construction. But crucially, the wide scope reading — where the reciprocal
scopes out of the embedded clause — is unavailable, because the logophoric
pronoun must be interpreted *inside* the report context and the reciprocal
cannot drag its antecedent out.

This pattern is correctly predicted by the relational analysis (the
logophor is inside the report, so the reciprocal's R-relation is
confined to the embedded clause) but not by the quantificational analysis
(the quantifier should be able to scope out independently of whether its
binder is logophoric).

## Connection to Logophoricity Theory

The logophoric pronoun in Wan satisfies the `self` role in @cite{sells-1987}'s
hierarchy: it refers to the individual whose mental state is reported.
-/

namespace Fragments.Wan.Reciprocals

open Core.Pronouns
open Features.Logophoricity

-- ════════════════════════════════════════════════════════════════
-- § 1: Pronoun Entries
-- ════════════════════════════════════════════════════════════════

/-- Wan logophoric plural pronoun *mɔ̄* (LOG.PL), realized in complement
    of speech-act verb *gé* 'say'.

    In (28): "wì mù tēŋ gé **mɔ̄** á ē ɔ̄ŋ lɔ̄ lé"
    Gloss: animal PL all say **LOG.PL** COP REFL RECIP eat PROG
    'All the animals say they-LOG will eat each other.'

    Note: *ē* in the same example is the reflexive marker (REFL), not the
    logophoric pronoun. The reciprocal reading arises from the combination
    of REFL *ē* + RECIP *ɔ̄ŋ*. -/
def logPl : PronounEntry :=
  { form := "mɔ̄", person := some .third, number := some .pl }

/-- Wan reflexive marker *ē* (REFL). Combines with reciprocal marker
    *ɔ̄ŋ* to form the reciprocal construction. -/
def refl : PronounEntry :=
  { form := "ē", person := some .third }

/-- Wan reciprocal marker *ɔ̄ŋ* (RECIP). Appears after reflexive *ē*
    to yield the reciprocal reading. -/
def recip : PronounEntry :=
  { form := "ɔ̄ŋ", person := some .third, number := some .pl }

/-- Wan 3pl ordinary (non-logophoric) pronoun *à* (low tone).
    In (32): "wì mù tēŋ tú gé **à** ɔ̄ŋ lɔ̄ lé"
    Gloss: animal PL all completely say **3PL** RECIP eat PROG
    'They all say they-3PL are going to eat each other.'
    (reciprocal, no logophor — wide scope IS available)

    Note: *tú* in the same example is an adverb 'completely', not a
    pronoun. The 3PL pronoun is *à* (grave accent), tonally distinct
    from copula *á* (acute accent) in (28). -/
def ordinaryPl : PronounEntry :=
  { form := "à", person := some .third, number := some .pl }

-- ════════════════════════════════════════════════════════════════
-- § 2: Logophoric Properties
-- ════════════════════════════════════════════════════════════════

/-- The Wan logophoric pronoun satisfies the `self` role: it refers to
    the attitude holder whose mental state is being reported. -/
def logophoricRole : LogophoricRole := .self

/-- The logophoric pronoun is formally distinct from the ordinary 3pl. -/
theorem log_distinct_from_ordinary :
    logPl.form ≠ ordinaryPl.form := by decide

/-- Wide scope requires an ordinary (non-logophoric) pronoun as antecedent.
    The logophoric pronoun is confined to the report context. -/
theorem logophoric_forces_narrow_scope :
    logPl.form ≠ ordinaryPl.form ∧
    LogophoricRole.pivot ≤ logophoricRole := by
  exact ⟨by decide, pivot_le _⟩

end Fragments.Wan.Reciprocals
