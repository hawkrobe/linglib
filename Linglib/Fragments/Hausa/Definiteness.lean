import Linglib.Syntax.Category.Determiner.Basic

/-!
# Hausa Definiteness Fragment

Hausa (Chadic, ISO `ha`). Two overt definite forms — the weak suffix *-n*
(masc./pl.; fem. *-r̃*), for uniquely identifiable referents including
first-mention inferables, and the strong *ɗîn*, restricted to hearer- or
discourse-old referents — a *bipartite* article system ([schwarz-2013] §4.2.2,
reporting [buba-1997] and [jaggar-2001]). The cell is provisional: bare
nominals also express definites (globally unique *rānā* 'sun', even some
re-mentions), and consonant-final loanwords take *ɗîn* as their sole definite
form, neutralizing the contrast there. Covarying (donkey) uses are unreported
for either form, so neither entry records one.
-/

namespace Hausa.Definiteness

/-- Hausa: weak *-n* (situational uniqueness), strong *ɗîn* (anaphoric), and
    the marked indefinite *wani* (fem. *wata*, pl. *wasu*; [jaggar-2001] §12.3). -/
def _root_.Hausa.Determiners.inventory : Determiner.Inventory :=
  [ .article { form := "-n", definiteness := .definite, exponent := .dedicatedMorpheme,
               uses := [.largerSituation] },
    .article { form := "ɗîn", definiteness := .definite, exponent := .dedicatedMorpheme,
               uses := [.anaphoric] },
    .article { form := "wani", definiteness := .indefinite, exponent := .dedicatedMorpheme } ]

/-- Hausa derives the `.bipartite` Moroney cell. -/
theorem marking : Determiners.inventory.markingStrategy = .bipartite := by decide

end Hausa.Definiteness
