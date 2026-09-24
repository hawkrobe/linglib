module

public import Linglib.Syntax.Case.Order

/-!
# Finnish case

Finnish has some fifteen cases, each with an ending in the singular. There are the
grammatical nominative, genitive, accusative and partitive, six local cases, and the essive,
translative, comitative, abessive and instructive. The accusative ending -t is confined to
the personal pronouns, as in *häne-t* 'him, her'. The local cases cross the direction of
motion with a region. The inessive -ssA 'in', the elative -stA 'out of' and the illative -Vn
'into' make up the interior series, and the adessive -llA 'on', the ablative -ltA 'off' and
the allative -lle 'onto' the exterior series. Finnish has no surface series, which Hungarian
has, and no dative, whose recipient function the allative covers, a gap [blake-1994]'s
hierarchy registers (`Studies/Blake1994.lean`).

The comparative label of the instructive, a case of manner and means as in *jala-n* 'on
foot', is the instrumental.

## Main definitions

* `Finnish.Case.inventory`: the cases, under their comparative labels.

## Main results

* `Finnish.Case.toCase_mem_inventory_iff`: the local cases are the interior and exterior series
  of the shared `Region × PathDir` decomposition.

The endings, spelled in segments, are in `Finnish.Declension`.

## References

* [karlsson-2017]
* [blake-1994]
-/

@[expose] public section

namespace Finnish.Case

/-- The Finnish cases under their comparative labels. -/
def inventory : Finset Case :=
  {.nom, .gen, .acc, .part, .ine, .ela, .ill, .ade, .abl, .all, .ess, .transl, .com, .abess,
    .inst}

/-- The local cases are the interior and exterior series: a cell of the shared spatial
decomposition is a Finnish case exactly when its region is not the surface. -/
theorem toCase_mem_inventory_iff {r : Case.Region} {d : Case.PathDir} {c : Case}
    (h : Case.toCase r d = some c) : c ∈ inventory ↔ r ≠ .surface := by
  cases r <;> cases d <;> cases h <;> decide

end Finnish.Case
