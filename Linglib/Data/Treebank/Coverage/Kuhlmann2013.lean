import Linglib.Data.Treebank.Coverage.Schema

/-!
# Kuhlmann2013 — treebank coverage (generated)
[kuhlmann-2013]

Auto-generated from `Linglib/Data/Treebank/Coverage/Kuhlmann2013.json` by
`scripts/gen_treebank_coverage.py`. **Do not edit by hand** — edit the JSON and
re-run the generator.

Rule and tree loss when the lexicalized LCFRS extracted from the training sections of five CoNLL
2006 dependency treebanks is restricted to fan-out 1 (projective), fan-out at most 2 (gap degree
at most 1), and well-nested rules of fan-out at most 2. Rules are counted as tokens; the JSON
records the losses the paper prints, and the generated rows carry the covered counts. The Arabic
rule total is printed as 5,839, which does not agree with the paper's stated 0.74% rule loss at
fan-out 1 (411 rules); the printed value is kept.
-/

namespace Data.Treebank.Coverage.Kuhlmann2013

/-- The 30 rows of Tables 3 and 4, in the paper's row order. -/
def rows : List Row :=
  [⟨"Arabic", "stan1318", .rules, 5839, .projective, .count, 5428⟩,
   ⟨"Arabic", "stan1318", .rules, 5839, .gapDegreeLe 1, .count, 5838⟩,
   ⟨"Arabic", "stan1318", .rules, 5839, .gapDegreeLeWellNested 1, .count, 5837⟩,
   ⟨"Arabic", "stan1318", .trees, 1460, .projective, .count, 1297⟩,
   ⟨"Arabic", "stan1318", .trees, 1460, .gapDegreeLe 1, .count, 1459⟩,
   ⟨"Arabic", "stan1318", .trees, 1460, .gapDegreeLeWellNested 1, .count, 1458⟩,
   ⟨"Czech", "czec1258", .rules, 1322111, .projective, .count, 1299828⟩,
   ⟨"Czech", "czec1258", .rules, 1322111, .gapDegreeLe 1, .count, 1321783⟩,
   ⟨"Czech", "czec1258", .rules, 1322111, .gapDegreeLeWellNested 1, .count, 1321704⟩,
   ⟨"Czech", "czec1258", .trees, 72703, .projective, .count, 55872⟩,
   ⟨"Czech", "czec1258", .trees, 72703, .gapDegreeLe 1, .count, 72391⟩,
   ⟨"Czech", "czec1258", .trees, 72703, .gapDegreeLeWellNested 1, .count, 72321⟩,
   ⟨"Danish", "dani1285", .rules, 99576, .projective, .count, 98347⟩,
   ⟨"Danish", "dani1285", .rules, 99576, .gapDegreeLe 1, .count, 99565⟩,
   ⟨"Danish", "dani1285", .rules, 99576, .gapDegreeLeWellNested 1, .count, 99559⟩,
   ⟨"Danish", "dani1285", .trees, 5190, .projective, .count, 4379⟩,
   ⟨"Danish", "dani1285", .trees, 5190, .gapDegreeLe 1, .count, 5181⟩,
   ⟨"Danish", "dani1285", .trees, 5190, .gapDegreeLeWellNested 1, .count, 5175⟩,
   ⟨"Slovene", "slov1268", .rules, 30284, .projective, .count, 29754⟩,
   ⟨"Slovene", "slov1268", .rules, 30284, .gapDegreeLe 1, .count, 30270⟩,
   ⟨"Slovene", "slov1268", .rules, 30284, .gapDegreeLeWellNested 1, .count, 30267⟩,
   ⟨"Slovene", "slov1268", .trees, 1534, .projective, .count, 1194⟩,
   ⟨"Slovene", "slov1268", .trees, 1534, .gapDegreeLe 1, .count, 1523⟩,
   ⟨"Slovene", "slov1268", .trees, 1534, .gapDegreeLeWellNested 1, .count, 1521⟩,
   ⟨"Turkish", "nucl1301", .rules, 62507, .projective, .count, 61583⟩,
   ⟨"Turkish", "nucl1301", .rules, 62507, .gapDegreeLe 1, .count, 62453⟩,
   ⟨"Turkish", "nucl1301", .rules, 62507, .gapDegreeLeWellNested 1, .count, 62439⟩,
   ⟨"Turkish", "nucl1301", .trees, 4997, .projective, .count, 4417⟩,
   ⟨"Turkish", "nucl1301", .trees, 4997, .gapDegreeLe 1, .count, 4964⟩,
   ⟨"Turkish", "nucl1301", .trees, 4997, .gapDegreeLeWellNested 1, .count, 4954⟩]

end Data.Treebank.Coverage.Kuhlmann2013
