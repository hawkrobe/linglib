import Linglib.Core.Nominal.ArticleInventory

/-!
# Cantonese Definiteness Fragment
@cite{cheng-sybesma-1999} @cite{jenks-2018}

Cantonese (ISO `yue`, Sinitic). Per @cite{cheng-sybesma-1999} and
@cite{jenks-2018} §6, Cantonese [Clf-N] phrases occur in both unique
and anaphoric definite environments. The structure is interpreted as
an ambiguous definite article — same distribution as English *the* —
making Cantonese `.generallyMarked` (Schwarz-style weak/strong
syncretism) rather than `.markedAnaphoric` like Mandarin.

Examples (paper §6.1):

- (54a) `Lou⁵baan² haa⁶zau³ lei⁴ gim²caa⁴ gung¹zok³` — Clf-N for
  larger-situation unique definite ("the boss").
- (55) Narrative sequence: anaphoric Clf-N tracks a previously
  introduced referent, paralleling English *the politician*.
- (56) Donkey: `Mui⁵ go³ jau⁵ jat¹ zek³ maa⁵ ge³ nung⁴fu¹ daa² zek³
  maa⁵` — Clf-N for the bound donkey reference.

This Fragment file commits the inventory; the cross-Sinitic typological
contrast with Mandarin is theoremed in
`Studies/Jenks2018.lean`.
-/

namespace Cantonese.Definiteness

open Core.Nominal (ArticleInventory)
open Features.Definiteness (DefMarkingStrategy)

/-- Cantonese: [Clf-N] is the syncretic definite (like English *the*); the
    same form serves both unique and anaphoric environments. Demonstratives
    are restricted to a narrower anaphoric subdistribution
    (@cite{jenks-2018} §6 example 57). -/
def articleInventory : ArticleInventory :=
  { hasIndefinite             := False
    hasUniqueArticle          := True
    hasAnaphoricArticle       := True
    uniqueAnaphoricSyncretism := True
    hasDemonstrative          := True
    hasPossessive             := True }

/-- Cantonese's inventory derives the `.generallyMarked` strategy
    (@cite{jenks-2018} Table 2). -/
theorem articleInventory_marking :
    articleInventory.toMarkingStrategy = .generallyMarked := rfl

end Cantonese.Definiteness
