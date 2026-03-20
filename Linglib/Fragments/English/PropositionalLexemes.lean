import Linglib.Theories.Pragmatics.Dialogue.KOS.Basic

/-!
# Propositional Lexemes
@cite{ginzburg-2012} Appendix C (exx. 10–12)

Propositional lexemes are words whose meaning is defined by reference to
the DGB state — they cannot be interpreted without knowing what question
is under discussion (MaxQUD) and what assertion is pending (MaxPending).

Examples: "yes", "no", "mmh", "uh-huh", "huh".

These are NOT ordinary content words — their denotation is a function
from DGB state to propositional content. This distinguishes them from
regular affirmatives/negatives in languages that use verbal echo
(e.g., Mandarin, Finnish).

## Key Properties

1. **DGB-dependent meaning**: content is determined by MaxQUD/MaxPending
2. **Polarity**: yes/mmh affirm; no negates
3. **Register**: mmh/uh-huh are informal variants of yes
4. **CR function**: huh requests clarification (constituent reading)
-/

namespace Fragments.English.PropositionalLexemes

open Theories.Pragmatics.Dialogue.KOS

-- ════════════════════════════════════════════════════
-- § 1. PropLexeme Structure
-- ════════════════════════════════════════════════════

/-- Which DGB component a propositional lexeme references. -/
inductive DGBRef where
  /-- References MaxQUD — the topmost question under discussion -/
  | maxQUD
  /-- References MaxPending — the most recent ungrounded assertion -/
  | maxPending
  /-- References both (e.g., for CR-initiating lexemes) -/
  | both
  deriving Repr, DecidableEq, BEq

/-- Polarity of a propositional lexeme's contribution. -/
inductive Polarity where
  | positive   -- affirms/accepts
  | negative   -- negates/rejects
  | cr         -- requests clarification
  deriving Repr, DecidableEq, BEq

/-- A propositional lexeme: a word whose meaning depends on DGB state. -/
structure PropLexeme where
  /-- Phonological form -/
  phon : String
  /-- Syntactic category -/
  cat : String := "S"
  /-- Which DGB component this lexeme references -/
  dgbRef : DGBRef
  /-- Polarity of the response -/
  polarity : Polarity
  /-- Informal description of the content rule -/
  contentRule : String
  /-- Source in @cite{ginzburg-2012} -/
  source : String := ""
  deriving Repr, DecidableEq, BEq

-- ════════════════════════════════════════════════════
-- § 2. Lexical Entries
-- ════════════════════════════════════════════════════

/-- "yes" — propositional abstract of MaxQUD.
@cite{ginzburg-2012} §7.5, ex. 21 (p. 232): content = max-qud([ ]).
When MaxQUD = ?p (a polar question), max-qud([ ]) = p.
DGB-PARAMS references max-qud : PolQuestion. -/
def yes : PropLexeme where
  phon := "yes"
  dgbRef := .maxQUD
  polarity := .positive
  contentRule := "cont = max-qud([]). DGB-PARAMS: max-qud : PolQuestion."
  source := "§7.5, ex. 21"

/-- "no" — negation of MaxQUD's propositional abstract.
@cite{ginzburg-2012} §7.5, ex. 25 (p. 233): content is a proposition such that
NegProp(cont) ∧ SimpleAns(cont, max-qud).
DGB-PARAMS references max-qud : PolQuestion. -/
def no : PropLexeme where
  phon := "no"
  dgbRef := .maxQUD
  polarity := .negative
  contentRule := "cont : Prop, c1 : NegProp(cont) ∧ SimpleAns(cont, max-qud)."
  source := "§7.5, ex. 25"

/-- "mmh" / "uh-huh" — informal positive acknowledgment.
@cite{ginzburg-2012} Appendix C. -/
def mmh : PropLexeme where
  phon := "mmh"
  dgbRef := .maxPending
  polarity := .positive
  contentRule := "Acknowledgment of MaxPending. Content = MaxPending content."
  source := "Appendix C"

/-- "huh" — clarification request.
@cite{ginzburg-2012} Appendix C. -/
def huh : PropLexeme where
  phon := "huh"
  dgbRef := .both
  polarity := .cr
  contentRule := "Requests repetition or clarification of MaxPending/MaxQUD."
  source := "Appendix C"

-- ════════════════════════════════════════════════════
-- § 3. Collected Data & Verification
-- ════════════════════════════════════════════════════

def propLexemes : List PropLexeme := [yes, no, mmh, huh]

/-- All propositional lexemes have non-empty content rules. -/
theorem all_have_content_rules :
    propLexemes.all (fun l => !l.contentRule.isEmpty) = true := by native_decide

/-- yes and no both reference MaxQUD (not MaxPending directly).
@cite{ginzburg-2012} §7.5: both derive content from max-qud via dgb-params. -/
theorem yes_no_reference_maxQUD :
    yes.dgbRef = .maxQUD ∧ no.dgbRef = .maxQUD := ⟨rfl, rfl⟩

/-- yes and no have opposite polarity. -/
theorem yes_no_opposite_polarity :
    yes.polarity ≠ no.polarity := by simp [yes, no]

/-- huh is the only CR lexeme. -/
theorem huh_unique_cr :
    propLexemes.filter (·.polarity == .cr) = [huh] := by native_decide

end Fragments.English.PropositionalLexemes
