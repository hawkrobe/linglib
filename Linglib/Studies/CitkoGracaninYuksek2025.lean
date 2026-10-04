/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Linearization.Spellout
public import Linglib.Syntax.Minimalist.Economy.Basic

/-!
# Citko and Gračanin-Yuksek (2025): Economy in PF reduction

[citko-gracanin-yuksek-2025] argue that economy chooses between the two mechanisms of PF
reduction, multidominance and ellipsis: among the derivations that yield the same string and the
same interpretation and violate no independent principle, the one with the fewest lexical
resources and operations wins. A coordinated wh-question (*What and when should you teach?*)
keeps each wh-phrase in its own conjunct, the conjuncts sharing their heads but not their
phrases. Building two clauses and eliding one costs more lexical items and an ellipsis; sharing
the whole C′ is cheaper still, but sends both wh-phrases through one vP edge, which the ban on
multiple wh-fronting excludes in English. A coordinated sluice (*I forgot what and when*) does
share the C′: both conjuncts must be reduced, so an ellipsis is unavoidable, and one [E] on the
shared C elides the shared TP once, at the price of a vP edge with two wh-specifiers. The ban on
multiple wh-fronting is therefore restated at PF as an asterisk on a phase edge with several
wh-specifiers, parameterised by edge: the elided vP edge is harmless, and multiple sluicing
divides speakers by whether the surviving CP edge counts.

Pronunciation Economy bans ellipsis with no effect on pronunciation. It excludes the sluice with
the coordinated-question shape, where one shared [E] complementizer has two TP complements and
the second deletion silences nothing new, and it forces the nonpaired sluice to carry two
complementizers, only one bearing [E]. In right node raising the same economy prefers sharing
the pivot to building it twice and, when the verbs match, sharing the verb phrase to eliding it.

Each candidate is a planar syntactic object with the chains of `Linearization/Chain.lean`, spelled
out as `Linearization/Spellout.lean` does: a token at two positions is shared, a moved wh-phrase
leaves the traces of its head at the vP edge and its base position, and the coordinator is left
out, so a string is its conjuncts' words. The predictions decide: the pronounced strings, the
deleted copies without antecedents that carry the paired reading, the asterisks, and the costs the
winners beat. A projection whose edge hosts several wh-specifiers receives an asterisk, which PF
cannot interpret unless the head is silenced or the language fronts several wh-phrases to an edge
of that category. A language's multiple-wh-fronting parameter is thus the set of phase categories
whose asterisks PF cannot interpret, so each object's asterisks that reach PF (`pfAsterisks`)
settle its convergence in every language at once.

## Implementation notes

The paper states the parameter as (27), an asterisk on every phase edge with several
wh-specifiers in a language without multiple wh-fronting, refines it after (29) by which phase
edges count, and mentions in a footnote the alternative statement used here: every such edge
receives an asterisk, which PF can interpret in a language with multiple wh-fronting. Which
categories head phases is the analysis's choice (`Minimalist.Phase`), so a parameter is any
`Finset Cat`; the paper's are `∅`, `{v}` and `{v, C}`.

## References

* [B. Citko and M. Gračanin-Yuksek, *Economy in PF reduction* (2025)][citko-gracanin-yuksek-2025]
* [J. Merchant, *The Syntax of Silence* (2001)][merchant-2001]
* [M. Marcolli, N. Chomsky and R. C. Berwick, *Mathematical Structure of Syntactic Merge: An
  Algebraic Model for Generative Linguistics* (2025)][marcolli-chomsky-berwick-2025]
* [Z. Belk, A. Neeleman and J. Philip, *What divides, and what unites, right-node raising*
  (2023)][belk-neeleman-philip-2023]
-/

@[expose] public section

namespace CitkoGracaninYuksek2025

open Minimalist Minimalist.PlanarSyntacticObject RoseTree
open Minimalist.SyntacticObject (Vertex)

/-! ### The lexicon -/

/-- `tok` builds a token from a category, its selection, its form, and the wh and [E] features. -/
def tok (id : ℕ) (cat : Cat) (sel : SelStack := []) (phon : String := "") (wh : Bool := false)
    (ellipsis : Bool := false) : LIToken :=
  ⟨LexicalItem.simple cat sel phon wh ellipsis, id⟩

def what := tok 1 .D (phon := "what") (wh := true)
def when := tok 2 .P (phon := "when") (wh := true)
def who := tok 3 .D (phon := "who") (wh := true)
def you := tok 4 .D (phon := "you")
def T := tok 5 .T [.v]
def v := tok 6 .v [.V]
def teach := tok 7 .V [.D] "teach"
def should := tok 8 .C [.T] "should"
def will := tok 9 .C [.T] "will"
/-- The null complementizer, and a second one. -/
def c := tok 10 .C [.T]
def c' := tok 11 .C [.T]
/-- The null complementizer bearing [E], and a second one. -/
def cE := tok 12 .C [.T] (ellipsis := true)
def cE' := tok 13 .C [.T] (ellipsis := true)
/-- The tokens a second, separately built clause draws. -/
def you' := tok 14 .D (phon := "you")
def T' := tok 15 .T [.v]
def v' := tok 16 .v [.V]
def teach' := tok 17 .V [.D] "teach"
/-- The auxiliary in T. -/
def shouldT := tok 18 .T [.v] "should"
def it := tok 19 .D (phon := "it")
def saw := tok 20 .V [.D] "saw"

/-! ### The candidate objects -/

/-- `clause` builds `[CP wh [C′ c [TP subj [T′ T [vP wh [v′ v VP]]]]]]`, the wh-phrase moved through
the edge of vP. -/
def clause (wh c subj T v : LIToken) (VP : PlanarSyntacticObject) : PlanarSyntacticObject :=
  wh * (c * (subj * (T * (traceOf wh * (v * VP)))))

/-- In non-bulk sharing under the complementizers `c₁` and `c₂`, each wh-phrase stays in its own
conjunct and the subject, T, v and verb are shared ((10b), (14), (16b), (38d), (45b), (46b)). -/
def nonBulk (c₁ c₂ : LIToken) : PlanarSyntacticObject :=
  (clause what c₁ you T v (teach * traceOf what)) * (clause when c₂ you T v (teach * traceOf when))

/-- In bulk sharing one C′ sits under both wh-phrases, both of which moved through its vP edge
((12b), (20b)). -/
def bulk (c : LIToken) : PlanarSyntacticObject :=
  let c' := c * (you * (T * (traceOf what * (traceOf when * (v * ((teach * traceOf what) *
    traceOf when))))))
  (what * c') * (when * c')

/-- Footnote 21's alternative to `bulk` shares a TP under two complementizers. -/
def bulkTP (c₁ c₂ : LIToken) : PlanarSyntacticObject :=
  let tp := you * (T * (traceOf what * (traceOf when * (v * ((teach * traceOf what) *
    traceOf when)))))
  (what * (c₁ * tp)) * (when * (c₂ * tp))

/-- The ellipsis analysis of the coordinated wh-question (11b) builds two clauses from separate
tokens and elides the first under its [E] complementizer, with its auxiliary in T as the
Sluicing-COMP generalization requires of a sluice. -/
def cwhEllipsis : PlanarSyntacticObject :=
  (what * (cE * (you * (shouldT * (traceOf what * (v * (teach * traceOf what))))))) *
    (clause when should you' T' v' (teach' * traceOf when))

/-- The double-ellipsis analysis of the coordinated sluice (19b) builds two clauses from separate
tokens and elides both, the second's object being the pronoun of vehicle change. -/
def csEllipsis : PlanarSyntacticObject :=
  (clause what cE you T v (teach * traceOf what)) * (clause when cE' you' T' v' ((teach' * it) *
    traceOf when))

/-- In a multiple question both wh-phrases are fronted through the vP edge, as in (28b) and, under
an [E] complementizer, the multiple sluice (29b). -/
def multipleQuestion (c : LIToken) : PlanarSyntacticObject :=
  who * (what * (c * (traceOf who * (T * (traceOf who * (traceOf what * (v * (saw *
    traceOf what))))))))

/-- The coordinated wh-question (10b), its complementizer shared. -/
abbrev cwh := nonBulk should should
/-- Its bulk-sharing rival (12b). -/
abbrev cwhBulk := bulk should
/-- Its rival with a null complementizer in the first conjunct (14). -/
abbrev cwhNullC := nonBulk c should
/-- Footnote 15 puts the null complementizer in the second conjunct instead. -/
abbrev cwhNullCSecond := nonBulk should c
/-- The embedded coordinated wh-question (15a) with its null complementizer shared, and with two
(15b). -/
abbrev cwhEmbedded := nonBulk c c
abbrev cwhEmbeddedTwoC := nonBulk c c'
/-- Two pronounced complementizers (16b). -/
abbrev cwhTwoAux := nonBulk should will
/-- The coordinated sluice (20b), (26b), (38b). -/
abbrev cs := bulk cE
/-- Its rival with two [E] complementizers over a shared TP (footnote 21). -/
abbrev csTwoC := bulkTP cE cE'
/-- The coordinated sluice with the shape of the coordinated wh-question, one shared [E]
complementizer over two TPs ((38d), (45c)). -/
abbrev csSharedC := nonBulk cE cE
/-- Two [E] complementizers (45b). -/
abbrev csnrTwoE := nonBulk cE cE'
/-- The nonpaired coordinated sluice (46b) has two complementizers, one bearing [E]. -/
abbrev csnr := nonBulk cE c

/-- The paired reading holds when the second conjunct holds a deleted copy of the first
conjunct's wh-phrase without an antecedent, the copy that vehicle change reads as an E-type
pronoun (footnote 20). -/
def Paired (t : PlanarSyntacticObject) : Prop :=
  ∃ x ∈ orphanTraces t, x.2 = what ∧ (⟨[1]⟩ : Core.Order.TreePath) ≤ x.1

instance : DecidablePred Paired := fun _ ↦ inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-! ### Economy and Pronunciation Economy (39) -/

/-- The tokens of `t`, each once. -/
def tokens (t : PlanarSyntacticObject) : Finset LIToken := ((tokenList t.val).map (·.2)).toFinset

/-- The terms of `t` are its subtrees, a shared constituent counted once, as
[marcolli-chomsky-berwick-2025]'s `subtrees` taken each once. -/
def terms (t : PlanarSyntacticObject) : Finset (RoseTree Vertex) :=
  ((vertices t.val).filterMap (subtreeAt t.val)).toFinset

/-- The cost of an object counts its tokens as the lexical items drawn, its internal terms as the
Merges, so that a shared constituent is built once, and its elided domains as the applications of
ellipsis. -/
def planarCost (t : PlanarSyntacticObject) : DerivationCost
  | .lexicalItems => (tokens t).card
  | .mergeOps => ((terms t).filter fun s ↦ s.arity ≠ 0).card
  | .agreeOps => 0
  | .ellipsisOps => (elidedDomains t).length

/-- The pronounceable tokens the application of ellipsis at the domain `K` silences. -/
def silencedBy (t : PlanarSyntacticObject) (K : Core.Order.TreePath) : Finset LIToken :=
  (tokens t).filter fun s ↦ s.phonForm?.isSome ∧ (occurrences t s).any (decide <| K ≤ ·)

/-- The application at `K` is vacuous when the earlier applications already silenced every token
it silences. -/
def IsVacuous (t : PlanarSyntacticObject) (K : Core.Order.TreePath) : Prop :=
  silencedBy t K ⊆ ((elidedDomains t).takeWhile (· ≠ K)).toFinset.biUnion (silencedBy t)

instance (t : PlanarSyntacticObject) (K : Core.Order.TreePath) : Decidable (IsVacuous t K) := by
  unfold IsVacuous; infer_instance

/-- Pronunciation Economy (39) requires that no application of ellipsis be vacuous. -/
def PronunciationEconomy (t : PlanarSyntacticObject) : Prop :=
  ∀ K ∈ elidedDomains t, ¬ IsVacuous t K

instance (t : PlanarSyntacticObject) : Decidable (PronunciationEconomy t) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-! ### The multiple-wh-fronting asterisk (27) -/

/-- `projection t` finds the specifiers and head of the projection at the root of `t`. Going down
the right spine, the specifiers are the left daughters above the head, which is the first
selecting item met; the result is `none` when the spine ends first. -/
def projection : RoseTree Vertex → Option (List (RoseTree Vertex) × LIToken)
  | .node (.inl none) [.node (.inl (some tok)) [], r] =>
      if tok.item.outerSel = [] then
        (projection r).map fun x ↦ (.node (.inl (some tok)) [] :: x.1, x.2)
      else some ([], tok)
  | .node (.inl none) [l, r] => (projection r).map fun x ↦ (l :: x.1, x.2)
  | _ => none

/-- A constituent is a wh-specifier when its head is a wh-token or its trace. -/
def IsWhSpecifier (s : RoseTree Vertex) : Prop :=
  ∃ tok ∈ (headToken? s).toList, tok.item.outerWh = true

instance (s : RoseTree Vertex) : Decidable (IsWhSpecifier s) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- The heads of the projections whose edges host several wh-specifiers, each of which receives
an asterisk. -/
def asterisked (t : PlanarSyntacticObject) : List LIToken :=
  (vertices t.val).filterMap fun p ↦ ((subtreeAt t.val p).bind projection).bind fun x ↦
    if 1 < x.1.countP (decide <| IsWhSpecifier ·) then some x.2 else none

/-- The categories of the asterisked projections whose heads reach PF unsilenced. The object
converges at PF under a multiple-wh-fronting parameter, the categories of the phases whose
asterisks PF cannot interpret, iff the parameter is disjoint from them. -/
def pfAsterisks (t : PlanarSyntacticObject) : Finset Cat :=
  (((asterisked t).filter (¬ IsSilenced t ·)).map (·.item.outerCat)).toFinset

/-! ### The multiple-wh-fronting parameter (27) by language -/

/-- In English variety A several wh-specifiers are banned at both phase edges, so multiple
sluicing crashes. -/
def englishA : Finset Cat := {.v, .C}
/-- In English variety B they are banned at the vP edge only, so multiple sluicing converges. -/
def englishB : Finset Cat := {.v}
/-- German and Greek lack multiple wh-fronting (30) but have multiple sluicing (31). -/
def german : Finset Cat := {.v}
def greek : Finset Cat := {.v}
/-- Russian moves all its wh-phrases, where English moves one (after (29)). -/
def russian : Finset Cat := ∅
/-- Romanian, where bulk sharing derives coordinated wh-questions (footnote 14). -/
def romanian : Finset Cat := ∅

/-! ### Coordinated wh-questions (§3.1) -/

theorem cwh_pf : pfPhon cwh = ["what", "when", "should", "you", "teach"] := by decide
theorem cwhEllipsis_pf : pfPhon cwhEllipsis = pfPhon cwh := by decide
theorem cwhBulk_pf : pfPhon cwhBulk = pfPhon cwh := by decide
theorem cwhNullC_pf : pfPhon cwhNullC = pfPhon cwh := by decide
/-- A pronounced complementizer in the first conjunct only precedes the second wh-phrase
(footnote 15). -/
theorem cwhNullCSecond_pf : pfPhon cwhNullCSecond = ["what", "should", "when", "you", "teach"] := by
  decide
theorem cwhTwoAux_pf : pfPhon cwhTwoAux = ["what", "should", "when", "will", "you", "teach"] := by
  decide

/-- Each wh-phrase is interpreted in its own conjunct. -/
theorem cwh_nonpaired : orphanTraces cwh = [] := by decide
/-- The shared C′ carries a copy of each wh-phrase into the other conjunct. -/
theorem cwhBulk_paired : Paired cwhBulk := by decide

theorem cwh_beats_ellipsis : planarCost cwh < planarCost cwhEllipsis := by decide
theorem cwhBulk_beats_cwh : planarCost cwhBulk < planarCost cwh := by decide
/-- The null complementizer of (14) adds structure and nothing to pronunciation. -/
theorem cwh_beats_nullC : planarCost cwh < planarCost cwhNullC := by decide
theorem cwhEmbedded_beats_twoC :
    planarCost cwhEmbedded < planarCost cwhEmbeddedTwoC := by decide

/-- Of the three phase edges of the bulk-sharing object, the two CP edges host one wh-phrase each
and the shared vP edge both, and its asterisk reaches PF ((37b)). -/
theorem pfAsterisks_cwhBulk : pfAsterisks cwhBulk = {.v} := by decide
/-- So bulk sharing crashes in English. -/
theorem cwhBulk_crashes :
    ¬ Disjoint englishA (pfAsterisks cwhBulk) ∧ ¬ Disjoint englishB (pfAsterisks cwhBulk) := by
  rw [pfAsterisks_cwhBulk]; decide
/-- In a multiple-wh-fronting language the same object converges (footnote 14). -/
theorem cwhBulk_converges_romanian : Disjoint romanian (pfAsterisks cwhBulk) :=
  Finset.disjoint_empty_left _
/-- Non-bulk sharing leaves one wh-phrase at each edge, so it converges in every language. -/
theorem pfAsterisks_cwh : pfAsterisks cwh = ∅ := by decide

/-! ### Coordinated sluices (§3.2) -/

theorem cs_pf : pfPhon cs = ["what", "when"] := by decide
theorem csEllipsis_pf : pfPhon csEllipsis = pfPhon cs := by decide
theorem cs_paired : Paired cs := by decide
theorem cs_beats_ellipsis : planarCost cs < planarCost csEllipsis := by decide
theorem cs_beats_twoC : planarCost cs < planarCost csTwoC := by decide

/-- The shared vP edge hosts two wh-specifiers, the asterisk of (26b). -/
theorem v_mem_asterisked_cs : v ∈ asterisked cs := by decide
/-- Elided, the asterisked edge never reaches PF, so the coordinated sluice converges in every
language. -/
theorem pfAsterisks_cs : pfAsterisks cs = ∅ := by decide

/-- Both phase edges of a multiple question reach PF with two wh-specifiers ((28b)). -/
theorem pfAsterisks_multipleQuestion : pfAsterisks (multipleQuestion c) = {.v, .C} := by decide
/-- So a multiple question crashes in English and converges in Russian. -/
theorem multipleQuestion_crashes :
    ¬ Disjoint englishA (pfAsterisks (multipleQuestion c)) ∧
      ¬ Disjoint englishB (pfAsterisks (multipleQuestion c)) := by
  rw [pfAsterisks_multipleQuestion]; decide
theorem multipleQuestion_converges_russian : Disjoint russian (pfAsterisks (multipleQuestion c)) :=
  Finset.disjoint_empty_left _
/-- Multiple sluicing elides the vP edge but not the CP edge ((29b)). -/
theorem pfAsterisks_multipleSluice : pfAsterisks (multipleQuestion cE) = {.C} := by decide
/-- So variety B, German and Greek converge and variety A does not. -/
theorem multipleSluicing :
    Disjoint englishB (pfAsterisks (multipleQuestion cE)) ∧
      Disjoint german (pfAsterisks (multipleQuestion cE)) ∧
      Disjoint greek (pfAsterisks (multipleQuestion cE)) ∧
      ¬ Disjoint englishA (pfAsterisks (multipleQuestion cE)) := by
  rw [pfAsterisks_multipleSluice]; decide

/-! ### Pronunciation Economy (§5, §6.1) -/

/-- With one shared [E] complementizer over two TPs, the second deletion silences nothing new. -/
theorem csSharedC_vacuous : ¬ PronunciationEconomy csSharedC := by decide
theorem csSharedC_pf : pfPhon csSharedC = pfPhon cs := by decide
theorem csSharedC_nonpaired : ¬ Paired csSharedC := by decide
theorem cs_economy : PronunciationEconomy cs ∧ PronunciationEconomy csEllipsis := by decide

theorem csnr_pf : pfPhon csnr = pfPhon cs := by decide
theorem csnr_economy : PronunciationEconomy csnr ∧ ¬ Paired csnr := by decide
/-- Two [E] complementizers over shared material elide it twice. -/
theorem csnrTwoE_vacuous : ¬ PronunciationEconomy csnrTwoE := by decide
theorem csnr_beats_twoE : planarCost csnr < planarCost csnrTwoE := by decide
/-- The nonpaired sluice is the cheapest nonpaired object respecting Pronunciation Economy, since
the shared [E] complementizer of (45c) draws one token fewer but elides vacuously. -/
theorem csnr_optimal : ∀ t ∈ [csSharedC, csnrTwoE],
    planarCost csnr < planarCost t ∨ ¬ PronunciationEconomy t := by decide
/-- The shared verb occurs in the second conjunct outside the elided TP and is silenced all the
same, so the object cannot surface as a coordinated wh-question (footnote 30). -/
theorem csnr_silences_shared :
    (∃ p ∈ occurrences csnr teach, ∀ K ∈ elidedDomains csnr, ¬ K ≤ p) ∧
      IsSilenced csnr teach := by decide

/-! ### Right node raising (§6.2) -/

def alice := tok 21 .D (phon := "Alice")
def iris := tok 22 .D (phon := "Iris")
def must := tok 23 .T [.V] "must"
/-- `must` bearing [E]. -/
def mustE := tok 24 .T [.V] "must" (ellipsis := true)
def oughtToBe := tok 25 .T [.V] "ought to be"
def shouldRNR := tok 26 .T [.V] "should"
def work := tok 27 .V [.P] "work"
def working := tok 28 .V [.P] "working"
def on := tok 29 .P [.N] "on"
def different := tok 30 .A (phon := "different")
def topics := tok 31 .N (phon := "topics")
def on' := tok 32 .P [.N] "on"
def different' := tok 33 .A (phon := "different")
def topics' := tok 34 .N (phon := "topics")

/-- The pivot, `on different topics`. -/
def pivot : PlanarSyntacticObject := on * (different * topics)

/-- `[TP subj [T′ T VP]]`. -/
def tp (subj T : LIToken) (VP : PlanarSyntacticObject) : PlanarSyntacticObject :=
  subj * (T * VP)

/-- Example (53b), after the pruning of [belk-neeleman-philip-2023] that removes the shared pivot
from the first conjunct, elides the first verb phrase, the bare verb, under [E] on `must`. -/
def rnrMixed : PlanarSyntacticObject :=
  (tp alice mustE (leaf work)) * (tp iris oughtToBe (working * pivot))
/-- Example (54) builds the first verb phrase with its own pivot and elides it. -/
def rnrElided : PlanarSyntacticObject :=
  merge
    (tp alice mustE
      (work * (on' * (different' * topics'))))
    (tp iris oughtToBe (working * pivot))
/-- Example (55b) shares the verb phrase, the verbs matching. -/
def rnrShared : PlanarSyntacticObject :=
  let VP := work * pivot
  (tp alice must VP) * (tp iris shouldRNR VP)
/-- The rival of (55b) with the shape of (53b). -/
def rnrMatchedMixed : PlanarSyntacticObject :=
  (tp alice mustE (leaf work)) * (tp iris shouldRNR (working * pivot))

theorem rnrMixed_pf : pfPhon rnrMixed =
    ["Alice", "must", "Iris", "ought to be", "working", "on", "different", "topics"] := by decide
theorem rnrElided_pf : pfPhon rnrElided = pfPhon rnrMixed := by decide
theorem rnrMixed_beats_elided :
    planarCost rnrMixed < planarCost rnrElided := by decide

theorem rnrShared_pf : pfPhon rnrShared =
    ["Alice", "must", "Iris", "should", "work", "on", "different", "topics"] := by decide
theorem rnrShared_isShared : IsShared rnrShared work := by decide
/-- With matching verbs, ellipsis is no longer an option. -/
theorem rnrShared_beats_mixed :
    planarCost rnrShared < planarCost rnrMatchedMixed := by decide

end CitkoGracaninYuksek2025
