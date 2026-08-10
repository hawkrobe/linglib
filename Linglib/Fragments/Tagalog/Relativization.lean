import Linglib.Syntax.RelativeClause.Basic

/-!
# Tagalog Relativization Fragment
[keenan-comrie-1977]

Two relative clause markers, differing only in RC position (postnominal
and prenominal); both use the linker *na ~ -ng* with gap in NP_rel
(-case) and relativize only the subject (*ang*-phrase). Non-subjects
are promoted to subject by voice alternation before relativizing.

Tagalog is one of the paper's subjects-only witnesses for HC₁/HC₃
(§1.3.1 p. 70), "on the assumption that the 'focus' NP is the subject" —
an assumption the paper itself flags as contested (§1.4.1.1, discussing
Schachter's critique).

Data from [keenan-comrie-1977] Table 1.
-/

namespace Tagalog

open RelativeClause

/-- Postnominal RC with the linker *na ~ -ng* — K&C's "invariable
    particle *ng*" — NP_rel (the *ang*-phrase) deleted. Subjects only
    (Table 1 p. 79; [keenan-comrie-1979] p. 347 ex. (110), from
    [schachter-otanes-1972] p. 123). -/
def relLinkerPost : Marker :=
  { form := "na/-ng"
  , npRel := .gap
  , bearsCaseMarking := false
  , rcPosition := .postNominal
  , positions := [.subject]
  , notes := "Linker; subject (ang-phrase) only; voice promotes non-subjects" }

/-- Prenominal RC with the linker *na ~ -ng*; NP_rel is deleted.
    Subjects only. "Restricting clauses can sometimes, especially when
    short, be presented to the left of the head ... a second RC-forming
    strategy" ([keenan-comrie-1979] p. 347, ex. (111)). -/
def relLinkerPre : Marker :=
  { form := "na/-ng"
  , npRel := .gap
  , bearsCaseMarking := false
  , rcPosition := .preNominal
  , positions := [.subject]
  , notes := "Linker; subject (ang-phrase) only; voice promotes non-subjects" }

/-- All Tagalog relative clause markers. -/
def relMarkers : List Marker := [relLinkerPost, relLinkerPre]

end Tagalog
