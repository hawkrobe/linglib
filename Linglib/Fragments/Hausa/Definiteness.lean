import Linglib.Syntax.Category.Determiner.Basic

/-!
# Hausa Definiteness Fragment

Hausa (Chadic, ISO `ha`) has two definite articles ([schwarz-2013] §4.2.2,
after [buba-1997] and [jaggar-2001]): the weak suffix *-n* (*-r̃* after
feminine nouns), used for uniquely identifiable referents including inferable
first mentions, and the strong *ɗîn*, used for referents already in the
discourse. The two-article classification is tentative, since bare nominals
can also be definite and consonant-final loanwords take *ɗîn* for both uses.
Covarying (donkey) uses are unreported for both articles. The marked
indefinite is *wani* ([jaggar-2001] §12.3).
-/

namespace Hausa.Determiners

/-- The Hausa determiners are the weak definite *-n*, the strong definite
    *ɗîn*, and the marked indefinite *wani* (feminine *wata*, plural *wasu*). -/
def inventory : Determiner.Inventory :=
  [ .article { form := "-n", definiteness := .definite, exponent := .dedicatedMorpheme,
               uses := [.largerSituation] },
    .article { form := "ɗîn", definiteness := .definite, exponent := .dedicatedMorpheme,
               uses := [.anaphoric] },
    .article { form := "wani", definiteness := .indefinite, exponent := .dedicatedMorpheme } ]

/-- Hausa derives the `.bipartite` Moroney cell. -/
theorem marking : inventory.markingStrategy = .bipartite := by decide

end Hausa.Determiners
