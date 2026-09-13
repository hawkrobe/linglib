import Linglib.Data.Treebank.Coverage.Schema

/-!
# KuhlmannNivre2006 — treebank coverage (generated)
[kuhlmann-nivre-2006]

Auto-generated from `Linglib/Data/Treebank/Coverage/KuhlmannNivre2006.json` by
`scripts/gen_treebank_coverage.py`. **Do not edit by hand** — edit the JSON and
re-run the generator.

The number of dependency trees of the Danish Dependency Treebank (DDT, the whole treebank less
17 malformed analyses, primary dependencies only) and of the training section of the analytical
layer of the Prague Dependency Treebank (PDT) at each gap degree and each edge degree, and the
number that are projective, planar, and well-nested. The table's percentages and its subtable
over the non-projective trees only are derived from these counts in
Studies/KuhlmannNivre2006.lean.
-/

namespace Data.Treebank.Coverage.KuhlmannNivre2006

/-- The 26 rows of Table 1, in the paper's row order. -/
def rows : List Row :=
  [⟨"DDT", "dani1285", .trees, 4393, .gapDegreeEq 0, .count, 3732⟩,
   ⟨"PDT", "czec1258", .trees, 73088, .gapDegreeEq 0, .count, 56168⟩,
   ⟨"DDT", "dani1285", .trees, 4393, .gapDegreeEq 1, .count, 654⟩,
   ⟨"PDT", "czec1258", .trees, 73088, .gapDegreeEq 1, .count, 16608⟩,
   ⟨"DDT", "dani1285", .trees, 4393, .gapDegreeEq 2, .count, 7⟩,
   ⟨"PDT", "czec1258", .trees, 73088, .gapDegreeEq 2, .count, 307⟩,
   ⟨"PDT", "czec1258", .trees, 73088, .gapDegreeEq 3, .count, 4⟩,
   ⟨"PDT", "czec1258", .trees, 73088, .gapDegreeEq 4, .count, 1⟩,
   ⟨"DDT", "dani1285", .trees, 4393, .edgeDegreeEq 0, .count, 3732⟩,
   ⟨"PDT", "czec1258", .trees, 73088, .edgeDegreeEq 0, .count, 56168⟩,
   ⟨"DDT", "dani1285", .trees, 4393, .edgeDegreeEq 1, .count, 584⟩,
   ⟨"PDT", "czec1258", .trees, 73088, .edgeDegreeEq 1, .count, 16585⟩,
   ⟨"DDT", "dani1285", .trees, 4393, .edgeDegreeEq 2, .count, 58⟩,
   ⟨"PDT", "czec1258", .trees, 73088, .edgeDegreeEq 2, .count, 259⟩,
   ⟨"DDT", "dani1285", .trees, 4393, .edgeDegreeEq 3, .count, 17⟩,
   ⟨"PDT", "czec1258", .trees, 73088, .edgeDegreeEq 3, .count, 63⟩,
   ⟨"DDT", "dani1285", .trees, 4393, .edgeDegreeEq 4, .count, 2⟩,
   ⟨"PDT", "czec1258", .trees, 73088, .edgeDegreeEq 4, .count, 10⟩,
   ⟨"PDT", "czec1258", .trees, 73088, .edgeDegreeEq 5, .count, 2⟩,
   ⟨"PDT", "czec1258", .trees, 73088, .edgeDegreeEq 6, .count, 1⟩,
   ⟨"DDT", "dani1285", .trees, 4393, .projective, .count, 3732⟩,
   ⟨"PDT", "czec1258", .trees, 73088, .projective, .count, 56168⟩,
   ⟨"DDT", "dani1285", .trees, 4393, .planar, .count, 3796⟩,
   ⟨"PDT", "czec1258", .trees, 73088, .planar, .count, 60048⟩,
   ⟨"DDT", "dani1285", .trees, 4393, .wellNested, .count, 4388⟩,
   ⟨"PDT", "czec1258", .trees, 73088, .wellNested, .count, 73010⟩]

end Data.Treebank.Coverage.KuhlmannNivre2006
