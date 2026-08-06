import Linglib.Fragments.English.Nouns
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Fragments.English.Pronouns
import Linglib.Fragments.English.Determiners
import Linglib.Fragments.English.FunctionWords
import Linglib.Fragments.English.Auxiliaries
import Linglib.Syntax.DependencyGrammar.Projection
import Linglib.Syntax.DependencyGrammar.Formal.NonProjective
import Linglib.Syntax.DependencyGrammar.Formal.HarmonicOrder

/-!
# Dependency Locality as an Explanatory Principle for Word Order
[futrell-gibson-2020]

The worked derivations of [futrell-gibson-2020] ("Dependency locality as an
explanatory principle for word order", *Language* 96(2):371–412), §2.3–2.4,
built over the DG substrate (`totalDepLength`, `isProjective`, `gapDegree`,
the harmonic chain machinery), plus the §6 cross-linguistic data (Table 2):

* examples (3)–(4), p. 377 — displacement (extraposition, wh-movement)
  produces nonprojective trees, at gap degree 1 (the paper's "mildly
  context-sensitive" deviation from context-freeness);
* examples (7)–(8), p. 379 — short-before-long is DLM-optimal in
  head-initial contexts, and its mirror image long-before-short in
  head-final contexts;
* examples (9)–(10), p. 380 — consistent head direction minimizes
  dependency length in single-dependent chains (the DLM route to the
  Greenbergian harmonic correlations), while for a head with several short
  dependents, splitting them across the head beats consistency (the
  Gildea–Temperley exception, e.g. Spanish prenominal determiners);
* example (11), p. 381 — heavy NP shift: the DLM penalty of the
  verb–object–particle order is negligible for a light object but large
  for a heavy one (cf. the acceptability contrast in example (6));
* example (13), p. 382 — the random-order baseline: an attested sentence
  has lower dependency length than reorderings of the same tree;
* Table 2 — per-language head-final proportion and mean dependency length
  over UD 2.1 corpora.

The §4–5 corpus results themselves (random/optimal baseline Monte Carlo
comparisons, Figure 1) are statistical fits and are cited in prose only.
English words derive from the Fragment lexicon; the example trees follow
the paper's arc conventions (prepositions head their nouns, so arc lengths
match the printed figures).
-/

namespace FutrellEtAl2020

open Morphology (Word)
open DepGrammar DepGrammar.DependencyLength

/-! ### Fragment-derived words -/

private abbrev john := English.Nouns.john.toWordSg
private abbrev threw := English.Predicates.Verbal.throw.toWordPast
private abbrev out := English.FunctionWords.out.toWord
private abbrev the_ := English.Determiners.the.toWord
private abbrev trash := English.Nouns.trash.toWordSg
private abbrev sitting := English.Predicates.Verbal.sit.toWordPresPart
private abbrev in_ := English.FunctionWords.in_.toWord
private abbrev kitchen := English.Nouns.kitchen.toWordSg
private abbrev i_ := English.Pronouns.i.toWord
private abbrev think := English.Predicates.Verbal.think.toWordBase
private abbrev thinks := English.Predicates.Verbal.think.toWord3sg
private abbrev a_ := English.Determiners.a.toWord
private abbrev woman := English.Nouns.woman.toWordSg
private abbrev arrived := English.Predicates.Verbal.arrive.toWordPast
private abbrev who := English.Pronouns.who.toWord
private abbrev you := English.Pronouns.you.toWord
private abbrev know := English.Predicates.Verbal.know.toWordBase
private abbrev what := English.Pronouns.what.toWord
private abbrev he := English.Pronouns.he.toWord
private abbrev did := English.Auxiliaries.did.toWord
private abbrev from_ := English.FunctionWords.from_.toWord
private abbrev this_ := English.Determiners.this.toWord
private abbrev story := English.Nouns.story.toWordSg
private abbrev comes := English.Predicates.Verbal.come.toWord3sg
private abbrev yesterday : Word := Word.mk' "yesterday" .ADV
private abbrev ap : Word := Word.mk' "AP" .PROPN

/-- Schematic token for the paper's abstract tree diagrams (A, B, C, …). -/
private def tok (s : String) : Word := Word.mk' s .X

/-! ### Examples (3)–(4): displacement and nonprojectivity

Displacement produces nonprojective trees: right extraposition in (3),
where *who you know* modifies *woman* across the intervening verb, and
wh-movement in (4), where *what* is the object of *did*. Both sit at gap
degree 1 — the paper's point that natural languages deviate from
context-freeness ("projectivity corresponds formally to context-freeness")
only mildly. -/

/-- Example (3): "I think a woman arrived who you know" — extraposed
    relative clause. -/
def extraposition : DepTree :=
  { words := [i_, think, a_, woman, arrived, who, you, know]
    deps := [⟨1, 0, .nsubj⟩, ⟨1, 4, .ccomp⟩, ⟨4, 3, .nsubj⟩, ⟨3, 2, .det⟩,
             ⟨3, 7, .acl⟩, ⟨7, 5, .obj⟩, ⟨7, 6, .nsubj⟩]
    rootIdx := 1 }

/-- Example (4): "I know what he thinks you did yesterday" — wh-movement. -/
def whMovement : DepTree :=
  { words := [i_, know, what, he, thinks, you, did, yesterday]
    deps := [⟨1, 0, .nsubj⟩, ⟨1, 4, .ccomp⟩, ⟨4, 3, .nsubj⟩, ⟨4, 6, .ccomp⟩,
             ⟨6, 5, .nsubj⟩, ⟨6, 2, .obj⟩, ⟨6, 7, .advmod⟩]
    rootIdx := 1 }

example : isProjective extraposition = false := by decide
example : isProjective whMovement = false := by decide

/-- Displacement stays mildly non-context-free: both trees have gap degree 1. -/
theorem displacement_gap_degree_one :
    extraposition.gapDegree = 1 ∧ whMovement.gapDegree = 1 := by decide

/-! ### Examples (7)–(8): short-before-long and its head-final mirror

A head with three dependent phrases of sizes 1, 2, 3. In head-initial
contexts (7), placing them short-to-long after the head minimizes total
dependency length; in head-final contexts (8), the mirror-image
long-before-short order does — the Japanese-style preference
([yamashita-chang-2001]; heavy elements shift leftward). -/

/-- (7a) A [B] [C D] [E F G]: dependents short-to-long after the head. -/
def shortBeforeLong : DepTree :=
  { words := [tok "A", tok "B", tok "C", tok "D", tok "E", tok "F", tok "G"]
    deps := [⟨0, 1, .dep⟩, ⟨0, 2, .dep⟩, ⟨2, 3, .dep⟩, ⟨0, 4, .dep⟩,
             ⟨4, 5, .dep⟩, ⟨4, 6, .dep⟩]
    rootIdx := 0 }

/-- (7b) A [B C D] [E F] [G]: dependents long-to-short after the head. -/
def longBeforeShort : DepTree :=
  { words := [tok "A", tok "B", tok "C", tok "D", tok "E", tok "F", tok "G"]
    deps := [⟨0, 1, .dep⟩, ⟨1, 2, .dep⟩, ⟨1, 3, .dep⟩, ⟨0, 4, .dep⟩,
             ⟨4, 5, .dep⟩, ⟨0, 6, .dep⟩]
    rootIdx := 0 }

/-- (8a) [A B C] [D E] [F] G: the mirror image of (7a), head-final. -/
def longBeforeShortHF : DepTree :=
  { words := [tok "A", tok "B", tok "C", tok "D", tok "E", tok "F", tok "G"]
    deps := [⟨2, 0, .dep⟩, ⟨2, 1, .dep⟩, ⟨4, 3, .dep⟩, ⟨6, 2, .dep⟩,
             ⟨6, 4, .dep⟩, ⟨6, 5, .dep⟩]
    rootIdx := 6 }

/-- (8b) [A] [B C] [D E F] G: the mirror image of (7b), head-final. -/
def shortBeforeLongHF : DepTree :=
  { words := [tok "A", tok "B", tok "C", tok "D", tok "E", tok "F", tok "G"]
    deps := [⟨2, 1, .dep⟩, ⟨5, 3, .dep⟩, ⟨5, 4, .dep⟩, ⟨6, 0, .dep⟩,
             ⟨6, 2, .dep⟩, ⟨6, 5, .dep⟩]
    rootIdx := 6 }

/-- (7): short-before-long wins in head-initial contexts. -/
theorem short_before_long_head_initial :
    totalDepLength shortBeforeLong < totalDepLength longBeforeShort := by decide

/-- (8): long-before-short wins in head-final contexts. -/
theorem long_before_short_head_final :
    totalDepLength longBeforeShortHF < totalDepLength shortBeforeLongHF := by decide

/-- The head-final preference is the exact mirror of the head-initial one:
    mirrored trees have equal total dependency length. -/
theorem mirror_preserves_totalDepLength :
    totalDepLength longBeforeShortHF = totalDepLength shortBeforeLong ∧
    totalDepLength shortBeforeLongHF = totalDepLength longBeforeShort := by decide

/-! ### Examples (9)–(10): head-direction consistency and its exceptions

For single-dependent chains (9), consistent head direction keeps every
dependency adjacent — the DLM route to the Greenbergian harmonic
correlations (universals 2–6). The consistent chain achieves the
`listSpan` lower bound of the substrate's chain machinery
(`monotone_ascending_achieves_span`); the mixed order exceeds it. For a
head with several short dependents (10), the optimum instead splits them
across the head (Gildea–Temperley), predicting the documented exceptions
(e.g. prenominal determiners in otherwise head-initial Spanish). -/

/-- (9a) chain A → B → C → D linearized consistently: A B C D. -/
def consistentChain : DepTree :=
  { words := [tok "A", tok "B", tok "C", tok "D"]
    deps := [⟨0, 1, .dep⟩, ⟨1, 2, .dep⟩, ⟨2, 3, .dep⟩]
    rootIdx := 0 }

/-- (9b) the same chain linearized with mixed head direction: A C D B. -/
def mixedChain : DepTree :=
  { words := [tok "A", tok "C", tok "D", tok "B"]
    deps := [⟨0, 3, .dep⟩, ⟨3, 1, .dep⟩, ⟨1, 2, .dep⟩]
    rootIdx := 0 }

/-- (9): consistent head direction minimizes chain dependency length. -/
theorem consistent_chain_shorter :
    totalDepLength consistentChain < totalDepLength mixedChain := by decide

open DepGrammar.HarmonicOrder in
/-- The consistent chain achieves the substrate's span lower bound; the mixed
    linearization exceeds it. -/
theorem consistent_chain_achieves_span :
    chainTDL [0, 1, 2, 3] = listSpan [0, 1, 2, 3] ∧
    chainTDL [0, 3, 1, 2] > listSpan [0, 3, 1, 2] := by decide

/-- (10a) A B C D: both dependents (B and C–D) after the head A. -/
def dependentsSameSide : DepTree :=
  { words := [tok "A", tok "B", tok "C", tok "D"]
    deps := [⟨0, 1, .dep⟩, ⟨0, 2, .dep⟩, ⟨2, 3, .dep⟩]
    rootIdx := 0 }

/-- (10b) B A C D: the one-word dependent moved before the head. -/
def dependentsSplit : DepTree :=
  { words := [tok "B", tok "A", tok "C", tok "D"]
    deps := [⟨1, 0, .dep⟩, ⟨1, 2, .dep⟩, ⟨2, 3, .dep⟩]
    rootIdx := 1 }

/-- (10): with two dependents, splitting them across the head beats
    consistent head direction. -/
theorem split_beats_consistency :
    totalDepLength dependentsSplit < totalDepLength dependentsSameSide := by decide

/-! ### Example (11): heavy NP shift

The paper's flagship worked example. With a light object, the
verb–object–particle order costs only 1 extra unit of dependency length
(6 vs. 7) — matching the free alternation in example (6a). With a heavy
object, it costs 5 (11 vs. 16) — matching the near-obligatory shift in
(6c–d). DLM thus derives why heavy NP shift is weight-sensitive. -/

/-- (11a) "John threw out the trash", total dependency length 6. -/
def lightParticleEarly : DepTree :=
  { words := [john, threw, out, the_, trash]
    deps := [⟨1, 0, .nsubj⟩, ⟨1, 2, .compound⟩, ⟨1, 4, .obj⟩, ⟨4, 3, .det⟩]
    rootIdx := 1 }

/-- (11b) "John threw the trash out", total dependency length 7. -/
def lightParticleLate : DepTree :=
  { words := [john, threw, the_, trash, out]
    deps := [⟨1, 0, .nsubj⟩, ⟨1, 3, .obj⟩, ⟨3, 2, .det⟩, ⟨1, 4, .compound⟩]
    rootIdx := 1 }

/-- (11c) "John threw out the trash sitting in the kitchen", total 11. -/
def heavyParticleEarly : DepTree :=
  { words := [john, threw, out, the_, trash, sitting, in_, the_, kitchen]
    deps := [⟨1, 0, .nsubj⟩, ⟨1, 2, .compound⟩, ⟨1, 4, .obj⟩, ⟨4, 3, .det⟩,
             ⟨4, 5, .acl⟩, ⟨5, 6, .obl⟩, ⟨6, 8, .obl⟩, ⟨8, 7, .det⟩]
    rootIdx := 1 }

/-- (11d) "John threw the trash sitting in the kitchen out", total 16. -/
def heavyParticleLate : DepTree :=
  { words := [john, threw, the_, trash, sitting, in_, the_, kitchen, out]
    deps := [⟨1, 0, .nsubj⟩, ⟨1, 3, .obj⟩, ⟨3, 2, .det⟩, ⟨3, 4, .acl⟩,
             ⟨4, 5, .obl⟩, ⟨5, 7, .obl⟩, ⟨7, 6, .det⟩, ⟨1, 8, .compound⟩]
    rootIdx := 1 }

-- The printed totals of the four figures.
example : totalDepLength lightParticleEarly = 6 := by decide
example : totalDepLength lightParticleLate = 7 := by decide
example : totalDepLength heavyParticleEarly = 11 := by decide
example : totalDepLength heavyParticleLate = 16 := by decide

/-- The DLM penalty for late particle placement grows with object weight:
    1 for the light object, 5 for the heavy one. -/
theorem dlm_penalty_grows_with_weight :
    totalDepLength lightParticleLate - totalDepLength lightParticleEarly <
    totalDepLength heavyParticleLate - totalDepLength heavyParticleEarly := by decide

/-! ### Example (13): the random-order baseline

The attested sentence "this story comes from the AP" (total dependency
length 6) against two random reorderings of the same tree (9 and 11) —
the paper's illustration of the random-order baseline methodology of
§4–5, whose Monte-Carlo results are not formalized here. -/

/-- (13a) "this story comes from the AP", the attested order, total 6. -/
def attestedOrder : DepTree :=
  { words := [this_, story, comes, from_, the_, ap]
    deps := [⟨1, 0, .det⟩, ⟨2, 1, .nsubj⟩, ⟨2, 3, .obl⟩, ⟨3, 5, .obl⟩,
             ⟨5, 4, .det⟩]
    rootIdx := 2 }

/-- (13b) reordering "from AP the this story comes", total 9. -/
def reorderingB : DepTree :=
  { words := [from_, ap, the_, this_, story, comes]
    deps := [⟨4, 3, .det⟩, ⟨5, 4, .nsubj⟩, ⟨5, 0, .obl⟩, ⟨0, 1, .obl⟩,
             ⟨1, 2, .det⟩]
    rootIdx := 5 }

/-- (13c) reordering "comes AP the from story this", total 11. -/
def reorderingC : DepTree :=
  { words := [comes, ap, the_, from_, story, this_]
    deps := [⟨4, 5, .det⟩, ⟨0, 4, .nsubj⟩, ⟨0, 3, .obl⟩, ⟨3, 1, .obl⟩,
             ⟨1, 2, .det⟩]
    rootIdx := 0 }

example : totalDepLength attestedOrder = 6 := by decide
example : totalDepLength reorderingB = 9 := by decide
example : totalDepLength reorderingC = 11 := by decide

/-- The attested order beats both random reorderings of its tree. -/
theorem attested_below_reorderings :
    totalDepLength attestedOrder < totalDepLength reorderingB ∧
    totalDepLength attestedOrder < totalDepLength reorderingC := by decide

/-! ### Table 2: head-finality and dependency length

For each of the 46 languages measured over UD 2.1 corpora, the proportion
of head-final dependencies and the mean dependency length per word at
sentence lengths 10, 15, and 20. The paper reads the table together with
its scatterplots: more head-final languages have longer dependencies, and
the languages with especially long dependencies are predominantly
head-final ones such as Japanese, Korean, and Turkish.

Values are scaled integers — permille for the head-final proportion, ×100
for dependency lengths (mirroring the table's two decimal places) — so
that downstream list computations kernel-`decide`. UD language codes are
linglib annotation for cross-study joins (`Studies/LevshinaEtAl2023`);
they are not printed in the table, but match the language keys of the
paper's analysis pipeline, the CLIQS codebase its footnote cites
(<https://github.com/langprocgroup/cliqs/>, `typology3.csv`). -/

/-- One row of Table 2: head-final proportion and mean per-word dependency
lengths for one UD 2.1 language. -/
structure DepLengthRow where
  /-- Language name as printed in the table (e.g. "Norwegian (B)"). -/
  language : String
  /-- UD language code (linglib annotation, not part of the table). -/
  isoCode : String
  /-- Proportion of head-final dependencies, permille (881 = 0.881). -/
  propHeadFinal1000 : Nat
  /-- Mean dependency length per word at sentence length 10, ×100. -/
  depLengthAt10_100 : Nat
  /-- Mean dependency length per word at sentence length 15, ×100. -/
  depLengthAt15_100 : Nat
  /-- Mean dependency length per word at sentence length 20, ×100. -/
  depLengthAt20_100 : Nat
  deriving Repr, DecidableEq

/-- Table 2, in the paper's row order (descending head-final proportion). -/
def table2 : List DepLengthRow := [
  { language := "Korean", isoCode := "ko", propHeadFinal1000 := 881,
    depLengthAt10_100 := 201, depLengthAt15_100 := 249, depLengthAt20_100 := 284 },
  { language := "Japanese", isoCode := "ja", propHeadFinal1000 := 809,
    depLengthAt10_100 := 170, depLengthAt15_100 := 198, depLengthAt20_100 := 226 },
  { language := "Turkish", isoCode := "tr", propHeadFinal1000 := 778,
    depLengthAt10_100 := 199, depLengthAt15_100 := 236, depLengthAt20_100 := 261 },
  { language := "Hindi", isoCode := "hi", propHeadFinal1000 := 763,
    depLengthAt10_100 := 188, depLengthAt15_100 := 226, depLengthAt20_100 := 257 },
  { language := "Urdu", isoCode := "ur", propHeadFinal1000 := 745,
    depLengthAt10_100 := 186, depLengthAt15_100 := 227, depLengthAt20_100 := 249 },
  { language := "Hungarian", isoCode := "hu", propHeadFinal1000 := 726,
    depLengthAt10_100 := 178, depLengthAt15_100 := 213, depLengthAt20_100 := 240 },
  { language := "Mandarin", isoCode := "zh", propHeadFinal1000 := 661,
    depLengthAt10_100 := 203, depLengthAt15_100 := 251, depLengthAt20_100 := 298 },
  { language := "Basque", isoCode := "eu", propHeadFinal1000 := 587,
    depLengthAt10_100 := 177, depLengthAt15_100 := 210, depLengthAt20_100 := 229 },
  { language := "Ancient Greek", isoCode := "grc", propHeadFinal1000 := 566,
    depLengthAt10_100 := 234, depLengthAt15_100 := 274, depLengthAt20_100 := 308 },
  { language := "Latin", isoCode := "la", propHeadFinal1000 := 547,
    depLengthAt10_100 := 227, depLengthAt15_100 := 272, depLengthAt20_100 := 299 },
  { language := "Northern Sami", isoCode := "sme", propHeadFinal1000 := 542,
    depLengthAt10_100 := 185, depLengthAt15_100 := 220, depLengthAt20_100 := 262 },
  { language := "Dutch", isoCode := "nl", propHeadFinal1000 := 533,
    depLengthAt10_100 := 207, depLengthAt15_100 := 248, depLengthAt20_100 := 274 },
  { language := "Afrikaans", isoCode := "af", propHeadFinal1000 := 524,
    depLengthAt10_100 := 216, depLengthAt15_100 := 248, depLengthAt20_100 := 278 },
  { language := "Finnish", isoCode := "fi", propHeadFinal1000 := 521,
    depLengthAt10_100 := 167, depLengthAt15_100 := 192, depLengthAt20_100 := 216 },
  { language := "Latvian", isoCode := "lv", propHeadFinal1000 := 513,
    depLengthAt10_100 := 171, depLengthAt15_100 := 193, depLengthAt20_100 := 216 },
  { language := "Estonian", isoCode := "et", propHeadFinal1000 := 508,
    depLengthAt10_100 := 184, depLengthAt15_100 := 213, depLengthAt20_100 := 232 },
  { language := "German", isoCode := "de", propHeadFinal1000 := 500,
    depLengthAt10_100 := 204, depLengthAt15_100 := 245, depLengthAt20_100 := 281 },
  { language := "Modern Greek", isoCode := "el", propHeadFinal1000 := 472,
    depLengthAt10_100 := 159, depLengthAt15_100 := 186, depLengthAt20_100 := 202 },
  { language := "English", isoCode := "en", propHeadFinal1000 := 460,
    depLengthAt10_100 := 167, depLengthAt15_100 := 193, depLengthAt20_100 := 210 },
  { language := "Danish", isoCode := "da", propHeadFinal1000 := 420,
    depLengthAt10_100 := 172, depLengthAt15_100 := 201, depLengthAt20_100 := 213 },
  { language := "Swedish", isoCode := "sv", propHeadFinal1000 := 420,
    depLengthAt10_100 := 166, depLengthAt15_100 := 193, depLengthAt20_100 := 213 },
  { language := "Slovenian", isoCode := "sl", propHeadFinal1000 := 419,
    depLengthAt10_100 := 173, depLengthAt15_100 := 195, depLengthAt20_100 := 219 },
  { language := "Slovak", isoCode := "sk", propHeadFinal1000 := 412,
    depLengthAt10_100 := 165, depLengthAt15_100 := 185, depLengthAt20_100 := 210 },
  { language := "Norwegian (B)", isoCode := "nb", propHeadFinal1000 := 401,
    depLengthAt10_100 := 163, depLengthAt15_100 := 190, depLengthAt20_100 := 208 },
  { language := "Persian", isoCode := "fa", propHeadFinal1000 := 401,
    depLengthAt10_100 := 226, depLengthAt15_100 := 265, depLengthAt20_100 := 288 },
  { language := "Norwegian (N)", isoCode := "nn", propHeadFinal1000 := 390,
    depLengthAt10_100 := 163, depLengthAt15_100 := 192, depLengthAt20_100 := 206 },
  { language := "Czech", isoCode := "cs", propHeadFinal1000 := 389,
    depLengthAt10_100 := 169, depLengthAt15_100 := 194, depLengthAt20_100 := 213 },
  { language := "Italian", isoCode := "it", propHeadFinal1000 := 384,
    depLengthAt10_100 := 150, depLengthAt15_100 := 180, depLengthAt20_100 := 188 },
  { language := "Croatian", isoCode := "hr", propHeadFinal1000 := 380,
    depLengthAt10_100 := 168, depLengthAt15_100 := 189, depLengthAt20_100 := 206 },
  { language := "French", isoCode := "fr", propHeadFinal1000 := 374,
    depLengthAt10_100 := 151, depLengthAt15_100 := 175, depLengthAt20_100 := 189 },
  { language := "Portuguese", isoCode := "pt", propHeadFinal1000 := 373,
    depLengthAt10_100 := 155, depLengthAt15_100 := 181, depLengthAt20_100 := 200 },
  { language := "Bulgarian", isoCode := "bg", propHeadFinal1000 := 372,
    depLengthAt10_100 := 156, depLengthAt15_100 := 181, depLengthAt20_100 := 197 },
  { language := "Gothic", isoCode := "got", propHeadFinal1000 := 372,
    depLengthAt10_100 := 197, depLengthAt15_100 := 234, depLengthAt20_100 := 275 },
  { language := "Catalan", isoCode := "ca", propHeadFinal1000 := 371,
    depLengthAt10_100 := 155, depLengthAt15_100 := 178, depLengthAt20_100 := 194 },
  { language := "Ukrainian", isoCode := "uk", propHeadFinal1000 := 368,
    depLengthAt10_100 := 161, depLengthAt15_100 := 189, depLengthAt20_100 := 206 },
  { language := "Galician", isoCode := "gl", propHeadFinal1000 := 365,
    depLengthAt10_100 := 150, depLengthAt15_100 := 220, depLengthAt20_100 := 210 },
  { language := "Russian", isoCode := "ru", propHeadFinal1000 := 358,
    depLengthAt10_100 := 156, depLengthAt15_100 := 181, depLengthAt20_100 := 207 },
  { language := "Serbian", isoCode := "sr", propHeadFinal1000 := 349,
    depLengthAt10_100 := 160, depLengthAt15_100 := 182, depLengthAt20_100 := 200 },
  { language := "Church Slavonic", isoCode := "cu", propHeadFinal1000 := 341,
    depLengthAt10_100 := 200, depLengthAt15_100 := 241, depLengthAt20_100 := 272 },
  { language := "Vietnamese", isoCode := "vi", propHeadFinal1000 := 339,
    depLengthAt10_100 := 165, depLengthAt15_100 := 195, depLengthAt20_100 := 212 },
  { language := "Spanish", isoCode := "es", propHeadFinal1000 := 332,
    depLengthAt10_100 := 145, depLengthAt15_100 := 171, depLengthAt20_100 := 186 },
  { language := "Polish", isoCode := "pl", propHeadFinal1000 := 325,
    depLengthAt10_100 := 156, depLengthAt15_100 := 180, depLengthAt20_100 := 205 },
  { language := "Hebrew", isoCode := "he", propHeadFinal1000 := 314,
    depLengthAt10_100 := 154, depLengthAt15_100 := 181, depLengthAt20_100 := 195 },
  { language := "Romanian", isoCode := "ro", propHeadFinal1000 := 301,
    depLengthAt10_100 := 160, depLengthAt15_100 := 179, depLengthAt20_100 := 195 },
  { language := "Indonesian", isoCode := "id", propHeadFinal1000 := 244,
    depLengthAt10_100 := 148, depLengthAt15_100 := 175, depLengthAt20_100 := 194 },
  { language := "Arabic", isoCode := "ar", propHeadFinal1000 := 103,
    depLengthAt10_100 := 140, depLengthAt15_100 := 168, depLengthAt20_100 := 193 } ]

example : table2.length = 46 := rfl

end FutrellEtAl2020
