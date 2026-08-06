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

This file formalizes the worked examples of [futrell-gibson-2020]
("Dependency locality as an explanatory principle for word order",
*Language* 96(2):371–412) and transcribes its Table 2.

The examples in §2.3–2.4 are small dependency trees making the paper's
qualitative points: displacement yields nonprojective trees of gap
degree 1; placing short constituents before long ones minimizes total
dependency length after a head, and the mirror-image order does before a
head; consistent head direction is optimal for chains but not for a head
with several one-word dependents; the cost of keeping a verb particle
after the object grows with the weight of the object; and an attested
sentence has shorter dependencies than random reorderings of its own
tree. Every total dependency length agrees with the figure printed in
the paper, by `decide`.

Table 2 lists, for 46 languages measured over Universal Dependencies 2.1
corpora, the proportion of head-final dependencies and the mean
dependency length per word at sentence lengths 10, 15, and 20.

The Monte Carlo corpus studies of §4–5 are not formalized. English words
come from the Fragment lexicon, and the trees follow the paper's drawing
convention in which a preposition heads its noun, so arc lengths match
the printed diagrams.
-/

namespace FutrellEtAl2020

open Morphology (Word)
open DepGrammar DepGrammar.DependencyLength
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
context-freeness ("projectivity corresponds formally to context-freeness")
only mildly. -/

/-- Example (3): "I think a woman arrived who you know" — extraposed
    relative clause. -/
def extraposition : DepTree :=
  { words := [i.toWord, think.toWordBase, a.toWord, woman.toWordSg, arrive.toWordPast,
              who.toWord, you.toWord, know.toWordBase]
    deps := [⟨1, 0, .nsubj⟩, ⟨1, 4, .ccomp⟩, ⟨4, 3, .nsubj⟩, ⟨3, 2, .det⟩,
             ⟨3, 7, .acl⟩, ⟨7, 5, .obj⟩, ⟨7, 6, .nsubj⟩]
    rootIdx := 1 }

/-- Example (4): "I know what he thinks you did yesterday" — wh-movement. -/
def whMovement : DepTree :=
  { words := [i.toWord, know.toWordBase, what.toWord, he.toWord, think.toWord3sg,
              you.toWord, did.toWord, Word.mk' "yesterday" .ADV]
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
long-before-short order does. The paper cites experimental evidence for
the latter from Japanese, where heavy elements shift leftward. -/

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
across the head ([gildea-temperley-2010]), predicting the documented
exceptions (e.g. prenominal determiners in otherwise head-initial
Spanish). -/

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
  { words := [john.toWordSg, throw.toWordPast, out.toWord, the.toWord, trash.toWordSg]
    deps := [⟨1, 0, .nsubj⟩, ⟨1, 2, .compound⟩, ⟨1, 4, .obj⟩, ⟨4, 3, .det⟩]
    rootIdx := 1 }

/-- (11b) "John threw the trash out", total dependency length 7. -/
def lightParticleLate : DepTree :=
  { words := [john.toWordSg, throw.toWordPast, the.toWord, trash.toWordSg, out.toWord]
    deps := [⟨1, 0, .nsubj⟩, ⟨1, 3, .obj⟩, ⟨3, 2, .det⟩, ⟨1, 4, .compound⟩]
    rootIdx := 1 }

/-- (11c) "John threw out the trash sitting in the kitchen", total 11. -/
def heavyParticleEarly : DepTree :=
  { words := [john.toWordSg, throw.toWordPast, out.toWord, the.toWord, trash.toWordSg,
              sit.toWordPresPart, in_.toWord, the.toWord, kitchen.toWordSg]
    deps := [⟨1, 0, .nsubj⟩, ⟨1, 2, .compound⟩, ⟨1, 4, .obj⟩, ⟨4, 3, .det⟩,
             ⟨4, 5, .acl⟩, ⟨5, 6, .obl⟩, ⟨6, 8, .obl⟩, ⟨8, 7, .det⟩]
    rootIdx := 1 }

/-- (11d) "John threw the trash sitting in the kitchen out", total 16. -/
def heavyParticleLate : DepTree :=
  { words := [john.toWordSg, throw.toWordPast, the.toWord, trash.toWordSg,
              sit.toWordPresPart, in_.toWord, the.toWord, kitchen.toWordSg, out.toWord]
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
  { words := [this_, story.toWordSg, come.toWord3sg, from_.toWord, the.toWord, ap]
    deps := [⟨1, 0, .det⟩, ⟨2, 1, .nsubj⟩, ⟨2, 3, .obl⟩, ⟨3, 5, .obl⟩,
             ⟨5, 4, .det⟩]
    rootIdx := 2 }

/-- (13b) reordering "from AP the this story comes", total 9. -/
def reorderingB : DepTree :=
  { words := [from_.toWord, ap, the.toWord, this_, story.toWordSg, come.toWord3sg]
    deps := [⟨4, 3, .det⟩, ⟨5, 4, .nsubj⟩, ⟨5, 0, .obl⟩, ⟨0, 1, .obl⟩,
             ⟨1, 2, .det⟩]
    rootIdx := 5 }

/-- (13c) reordering "comes AP the from story this", total 11. -/
def reorderingC : DepTree :=
  { words := [come.toWord3sg, ap, the.toWord, from_.toWord, story.toWordSg, this_]
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
