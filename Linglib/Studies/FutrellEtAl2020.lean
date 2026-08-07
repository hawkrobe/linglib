import Linglib.Fragments.English.Nouns
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Fragments.English.Pronouns
import Linglib.Fragments.English.Determiners
import Linglib.Fragments.English.FunctionWords
import Linglib.Fragments.English.Auxiliaries
import Linglib.Syntax.DependencyGrammar.Projectivity
import Linglib.Syntax.DependencyGrammar.Length

/-!
# Dependency Locality as an Explanatory Principle for Word Order
[futrell-gibson-2020]

This file formalizes the worked examples of [futrell-gibson-2020]
("Dependency locality as an explanatory principle for word order",
*Language* 96(2):371–412) — the §2.3–2.4 dependency trees, with every
total dependency length checked against the printed figure — and
transcribes its Table 2 (per-language head-final proportion and mean
dependency length over UD 2.1 corpora). The Monte Carlo corpus studies
of §4–5 are not formalized.

English words come from the Fragment lexicon, and the trees follow the
paper's drawing convention in which a preposition heads its noun, so arc
lengths match the printed diagrams. Mirror-image and reordering claims
are stated through `Graph.relabel`/`Graph.mirror`, so they hold by the
general invariance theorem rather than by inspection of hand-typed twins.
-/

namespace FutrellEtAl2020

open DependencyGrammar
open Morphology (Word)
open English.Nouns English.Predicates.Verbal English.Pronouns English.Determiners
  English.FunctionWords English.Auxiliaries

-- `this` is a Lean keyword, so the demonstrative needs a qualified alias.
private abbrev this_ := English.Determiners.this.toWord
private abbrev ap : Word := Word.mk' "AP" .PROPN

/-- Schematic token for the paper's abstract tree diagrams (A, B, C, …). -/
private def tok (s : String) : Word := Word.mk' s .X

/-! ### Examples (3)–(4): displacement and nonprojectivity

Displacement produces nonprojective trees: right extraposition in (3),
where *who you know* modifies *woman* across the intervening verb, and
wh-movement in (4), where *what* is the object of *did*. Both sit at gap
degree 1 — the paper's point that natural languages deviate from
context-freeness only mildly. -/

/-- Example (3): "I think a woman arrived who you know". -/
def extraposition : Graph 8 :=
  .ofArcs
    [i.toWord, think.toWordBase, a.toWord, woman.toWordSg, arrive.toWordPast,
     who.toWord, you.toWord, know.toWordBase]
    1
    [(1, 0, .nsubj), (1, 4, .ccomp), (4, 3, .nsubj), (3, 2, .det),
     (3, 7, .acl), (7, 5, .obj), (7, 6, .nsubj)]

/-- Example (4): "I know what he thinks you did yesterday". -/
def whMovement : Graph 8 :=
  .ofArcs
    [i.toWord, know.toWordBase, what.toWord, he.toWord, think.toWord3sg,
     you.toWord, did.toWord, Word.mk' "yesterday" .ADV]
    1
    [(1, 0, .nsubj), (1, 4, .ccomp), (4, 3, .nsubj), (4, 6, .ccomp),
     (6, 5, .nsubj), (6, 2, .obj), (6, 7, .advmod)]

example : ¬ IsProjective extraposition := by decide
example : ¬ IsProjective whMovement := by decide

/-- Displacement stays mildly non-context-free: both trees have gap degree 1. -/
theorem displacement_gap_degree_one :
    extraposition.gapDegree = 1 ∧ whMovement.gapDegree = 1 := by decide

/-! ### Examples (7)–(8): short-before-long and its head-final mirror

A head with three dependent phrases of sizes 1, 2, 3. In head-initial
contexts (7), placing them short-to-long after the head minimizes total
dependency length; the head-final long-before-short preference (8) is its
exact mirror — here literally `Graph.mirror`, so the equal-cost claim is
`Graph.totalLength_mirror`, not an inspection of hand-typed twins. -/

/-- (7a) A [B] [C D] [E F G]: dependents short-to-long after the head. -/
def shortBeforeLong : Graph 7 :=
  .ofArcs [tok "A", tok "B", tok "C", tok "D", tok "E", tok "F", tok "G"]
    0 [(0, 1, .dep), (0, 2, .dep), (2, 3, .dep), (0, 4, .dep), (4, 5, .dep), (4, 6, .dep)]

/-- (7b) A [B C D] [E F] [G]: dependents long-to-short after the head. -/
def longBeforeShort : Graph 7 :=
  .ofArcs [tok "A", tok "B", tok "C", tok "D", tok "E", tok "F", tok "G"]
    0 [(0, 1, .dep), (1, 2, .dep), (1, 3, .dep), (0, 4, .dep), (4, 5, .dep), (0, 6, .dep)]

/-- (7): short-before-long wins in head-initial contexts. -/
theorem short_before_long_head_initial :
    shortBeforeLong.totalLength < longBeforeShort.totalLength := by decide

/-- (8): the head-final regime is the mirror image, so long-before-short
    wins there at exactly the head-initial costs — by the general mirror
    invariance, no separate fixtures needed. -/
theorem long_before_short_head_final :
    shortBeforeLong.mirror.totalLength < longBeforeShort.mirror.totalLength := by
  simpa [Graph.totalLength_mirror] using short_before_long_head_initial

/-! ### Examples (9)–(10): head-direction consistency and its exceptions -/

/-- (9a) chain A → B → C → D linearized consistently: A B C D. -/
def consistentChain : Graph 4 :=
  .ofArcs [tok "A", tok "B", tok "C", tok "D"]
    0 [(0, 1, .dep), (1, 2, .dep), (2, 3, .dep)]

/-- (9b) the same chain linearized with mixed head direction: A C D B. -/
def mixedChain : Graph 4 :=
  .ofArcs [tok "A", tok "C", tok "D", tok "B"]
    0 [(0, 3, .dep), (3, 1, .dep), (1, 2, .dep)]

/-- (9): consistent head direction minimizes chain dependency length —
    the DLM route to the Greenbergian harmonic correlations. -/
theorem consistent_chain_shorter :
    consistentChain.totalLength < mixedChain.totalLength := by decide

/-- (10a) A B C D: both dependents (B and C–D) after the head A. -/
def dependentsSameSide : Graph 4 :=
  .ofArcs [tok "A", tok "B", tok "C", tok "D"]
    0 [(0, 1, .dep), (0, 2, .dep), (2, 3, .dep)]

/-- (10b) B A C D: the one-word dependent moved before the head. -/
def dependentsSplit : Graph 4 :=
  .ofArcs [tok "B", tok "A", tok "C", tok "D"]
    1 [(1, 0, .dep), (1, 2, .dep), (2, 3, .dep)]

/-- (10): with several short dependents, splitting them across the head
    beats consistency ([gildea-temperley-2010]), predicting the documented
    exceptions (e.g. prenominal determiners in head-initial Spanish). -/
theorem split_beats_consistency :
    dependentsSplit.totalLength < dependentsSameSide.totalLength := by decide

/-! ### Example (11): heavy NP shift

The paper's flagship worked example: the cost of the verb–object–particle
order is 1 for a light object (6 vs. 7) and 5 for a heavy one (11 vs. 16),
deriving the weight-sensitivity of heavy NP shift (cf. example (6)). -/

/-- (11a) "John threw out the trash", total dependency length 6. -/
def lightParticleEarly : Graph 5 :=
  .ofArcs [john.toWordSg, throw.toWordPast, out.toWord, the.toWord, trash.toWordSg]
    1 [(1, 0, .nsubj), (1, 2, .compound), (1, 4, .obj), (4, 3, .det)]

/-- (11b) "John threw the trash out", total dependency length 7. -/
def lightParticleLate : Graph 5 :=
  .ofArcs [john.toWordSg, throw.toWordPast, the.toWord, trash.toWordSg, out.toWord]
    1 [(1, 0, .nsubj), (1, 3, .obj), (3, 2, .det), (1, 4, .compound)]

/-- (11c) "John threw out the trash sitting in the kitchen", total 11. -/
def heavyParticleEarly : Graph 9 :=
  .ofArcs
    [john.toWordSg, throw.toWordPast, out.toWord, the.toWord, trash.toWordSg,
     sit.toWordPresPart, in_.toWord, the.toWord, kitchen.toWordSg]
    1
    [(1, 0, .nsubj), (1, 2, .compound), (1, 4, .obj), (4, 3, .det),
     (4, 5, .acl), (5, 6, .obl), (6, 8, .obl), (8, 7, .det)]

/-- (11d) "John threw the trash sitting in the kitchen out", total 16. -/
def heavyParticleLate : Graph 9 :=
  .ofArcs
    [john.toWordSg, throw.toWordPast, the.toWord, trash.toWordSg,
     sit.toWordPresPart, in_.toWord, the.toWord, kitchen.toWordSg, out.toWord]
    1
    [(1, 0, .nsubj), (1, 3, .obj), (3, 2, .det), (3, 4, .acl),
     (4, 5, .obl), (5, 7, .obl), (7, 6, .det), (1, 8, .compound)]

-- The printed totals of the four figures.
example : lightParticleEarly.totalLength = 6 := by decide
example : lightParticleLate.totalLength = 7 := by decide
example : heavyParticleEarly.totalLength = 11 := by decide
example : heavyParticleLate.totalLength = 16 := by decide

/-- The DLM penalty for late particle placement grows with object weight:
    1 for the light object, 5 for the heavy one. -/
theorem dlm_penalty_grows_with_weight :
    lightParticleLate.totalLength - lightParticleEarly.totalLength <
    heavyParticleLate.totalLength - heavyParticleEarly.totalLength := by decide

/-! ### Example (13): the random-order baseline

The attested sentence against reorderings of the same structure — stated
through `Graph.relabel`, so "same structure" is by construction, which is
what the paper's random-baseline methodology asserts. -/

/-- (13a) "this story comes from the AP", the attested order, total 6. -/
def attestedOrder : Graph 6 :=
  .ofArcs [this_, story.toWordSg, come.toWord3sg, from_.toWord, the.toWord, ap]
    2 [(1, 0, .det), (2, 1, .nsubj), (2, 3, .obl), (3, 5, .obl), (5, 4, .det)]

/-- The position permutation taking the attested order to the paper's
    first reordering "from AP the this story comes". -/
private def σB : Equiv.Perm (Fin 6) :=
  ⟨![3, 4, 5, 0, 2, 1], ![3, 5, 4, 0, 1, 2], by decide, by decide⟩

/-- (13b) the reordering, as a relabeling of the attested structure. -/
def reorderingB : Graph 6 := attestedOrder.relabel σB

example : attestedOrder.totalLength = 6 := by decide
example : reorderingB.totalLength = 9 := by decide

/-- The attested order beats the reordering — and since `reorderingB` is a
    `relabel` of `attestedOrder`, that they share a structure is not an
    assertion but a definition. -/
theorem attested_below_reordering :
    attestedOrder.totalLength < reorderingB.totalLength := by decide

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
  ⟨"Korean", "ko", 881, 201, 249, 284⟩,
  ⟨"Japanese", "ja", 809, 170, 198, 226⟩,
  ⟨"Turkish", "tr", 778, 199, 236, 261⟩,
  ⟨"Hindi", "hi", 763, 188, 226, 257⟩,
  ⟨"Urdu", "ur", 745, 186, 227, 249⟩,
  ⟨"Hungarian", "hu", 726, 178, 213, 240⟩,
  ⟨"Mandarin", "zh", 661, 203, 251, 298⟩,
  ⟨"Basque", "eu", 587, 177, 210, 229⟩,
  ⟨"Ancient Greek", "grc", 566, 234, 274, 308⟩,
  ⟨"Latin", "la", 547, 227, 272, 299⟩,
  ⟨"Northern Sami", "sme", 542, 185, 220, 262⟩,
  ⟨"Dutch", "nl", 533, 207, 248, 274⟩,
  ⟨"Afrikaans", "af", 524, 216, 248, 278⟩,
  ⟨"Finnish", "fi", 521, 167, 192, 216⟩,
  ⟨"Latvian", "lv", 513, 171, 193, 216⟩,
  ⟨"Estonian", "et", 508, 184, 213, 232⟩,
  ⟨"German", "de", 500, 204, 245, 281⟩,
  ⟨"Modern Greek", "el", 472, 159, 186, 202⟩,
  ⟨"English", "en", 460, 167, 193, 210⟩,
  ⟨"Danish", "da", 420, 172, 201, 213⟩,
  ⟨"Swedish", "sv", 420, 166, 193, 213⟩,
  ⟨"Slovenian", "sl", 419, 173, 195, 219⟩,
  ⟨"Slovak", "sk", 412, 165, 185, 210⟩,
  ⟨"Norwegian (B)", "nb", 401, 163, 190, 208⟩,
  ⟨"Persian", "fa", 401, 226, 265, 288⟩,
  ⟨"Norwegian (N)", "nn", 390, 163, 192, 206⟩,
  ⟨"Czech", "cs", 389, 169, 194, 213⟩,
  ⟨"Italian", "it", 384, 150, 180, 188⟩,
  ⟨"Croatian", "hr", 380, 168, 189, 206⟩,
  ⟨"French", "fr", 374, 151, 175, 189⟩,
  ⟨"Portuguese", "pt", 373, 155, 181, 200⟩,
  ⟨"Bulgarian", "bg", 372, 156, 181, 197⟩,
  ⟨"Gothic", "got", 372, 197, 234, 275⟩,
  ⟨"Catalan", "ca", 371, 155, 178, 194⟩,
  ⟨"Ukrainian", "uk", 368, 161, 189, 206⟩,
  ⟨"Galician", "gl", 365, 150, 220, 210⟩,
  ⟨"Russian", "ru", 358, 156, 181, 207⟩,
  ⟨"Serbian", "sr", 349, 160, 182, 200⟩,
  ⟨"Church Slavonic", "cu", 341, 200, 241, 272⟩,
  ⟨"Vietnamese", "vi", 339, 165, 195, 212⟩,
  ⟨"Spanish", "es", 332, 145, 171, 186⟩,
  ⟨"Polish", "pl", 325, 156, 180, 205⟩,
  ⟨"Hebrew", "he", 314, 154, 181, 195⟩,
  ⟨"Romanian", "ro", 301, 160, 179, 195⟩,
  ⟨"Indonesian", "id", 244, 148, 175, 194⟩,
  ⟨"Arabic", "ar", 103, 140, 168, 193⟩ ]

example : table2.length = 46 := rfl

end FutrellEtAl2020
