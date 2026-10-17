module

public import Eval.Basic
public import Eval.Parser
public import Studies.Bobaljik2012

/-!
# Scoring theories of root suppletion on Bobaljik (2012)

The data are the cognate triples of Bobaljik's Tables 4.1 and 4.2, read from
`Data/Paradigms/Bobaljik2012`: for each, a source's judgment of which of a word's positive,
comparative and superlative share a root, and the root pattern over the grades that the judgment
gives (`Bobaljik2012.rootPattern`). A triple is observed unless a source rejects one of its forms
in its cell (`Contested`), as the 2009 questionnaire rejects Zajkov's Karelian *äij-in*.

Three theories say which root patterns three synthetic grades can show (`Theory.Generates`).
Elsewhere insertion over the containment hierarchy generates the contiguous patterns, Bobaljik's
containment with an antihomophonous and grounded vocabulary generates AAA, ABB and ABC
(`groundedGenerable_iff`), and a theory of the grades as independent cells generates every
pattern. A theory parses a triple into the grade whose structure its root's word realizes in each
cell: every grade itself, or the positive in a superlative that embeds it
(`Bobaljik2012.positiveEmbedding`). A theory fits a triple under a parse when a pattern it
generates, read through the parse, classes the grades as the triple does (`Theory.Fits`). The naive
parse reads every triple as synthetic (`naive`); Bobaljik's parse stipulates the
positive-embedding superlative for the Bulgarian and the Armenian 'many' (pp. 127-129), two
stipulations (`bobaljik`).

Triple by triple (`triples`), a theory is right on an observed triple it fits and wrong on one it
does not. Under the naive parse both containment theories are wrong on the Basque doublet and on
the Bulgarian and Armenian quantifiers (`wrong_naive_elsewhere`, `wrong_naive_grounded`). Bobaljik's
parse changes nothing off its stipulations (`verdict_bobaljik_of_notMem`) and makes both
quantifiers right (`verdict_bobaljik_stipulated`), leaving the Basque doublet, which the book leaves
open. Every theory is silent on the contested Karelian triple alone (`contested_ids`,
`verdict_eq_silent_iff`), and the theory without containment, reading every triple as synthetic,
is never wrong (`verdict_free_naive_ne_wrong`). Pattern by pattern (`patterns`), the linking
hypothesis is asymmetric: a theory predicts that no observed triple shows a pattern it cannot
generate on synthetic grades, and nothing about the others. Grounded containment alone is right
that no triple is AAB, both containment theories are wrong that none is ABA on the surface, and
the theory without containment predicts nothing (`verdict_patterns`).

## Implementation notes

* A theory's generated patterns are compared up to their classes of grades, so `Theory.Fits`
  ranges over the five representatives of `Morphology.Paradigm`.
* The pattern experiment scores theories of synthetic grades; the parses enter only the triple
  experiment, where Bobaljik's two are stipulations rather than a rule.

## References

* [bobaljik-2012]
-/

@[expose] public section

namespace Eval.Suppletion.Bobaljik2012

open Morphology Morphology.Exponence Morphology.Containment
open Data.Paradigms (RootClasses)
open _root_.Bobaljik2012 (rootPattern positiveEmbedding)
open _root_.Bobaljik2012.Paradigms

/-! ### The data -/

/-- The forms some source rejects in their cells. -/
def rejected : List Data.Paradigms.Form :=
  forms.filter (·.judgment = .ungrammatical)

/-- A triple is contested when a source rejects one of its forms in its cell. -/
def Contested (r : RootClasses) : Prop :=
  ∃ g ∈ rejected, ∃ f ∈ r.forms, g.cell = f.cell ∧ g.form = f.form ∧ g.lexeme.id = r.lexeme.id

instance : DecidablePred Contested := fun _ ↦ inferInstanceAs (Decidable (∃ g ∈ rejected, _))

/-! ### The theories -/

/-- Three theories of the root patterns of the grades. -/
inductive Theory
  /-- Elsewhere insertion over the containment hierarchy, from terminal antihomophonous rules. -/
  | elsewhere
  /-- Bobaljik's containment, with an antihomophonous and grounded vocabulary. -/
  | grounded
  /-- The grades as independent cells, without containment. -/
  | free
  deriving DecidableEq, Repr

/-- A theory generates a root pattern on three synthetic grades. -/
def Theory.Generates : Theory → Paradigm 3 ℕ → Prop
  | .elsewhere, p => ElsewhereGenerable p
  | .grounded, p => GroundedGenerable p
  | .free, _ => True

instance : ∀ T : Theory, DecidablePred T.Generates
  | .elsewhere => fun p ↦ decidable_of_iff _
      ((isContiguous_fin_three_iff p).symm.trans (isContiguous_iff_generable p))
  | .grounded => fun p ↦ decidable_of_iff ((p 0 = p 2 → p 0 = p 1) ∧ ¬ (p 0 = p 1 ∧ p 1 ≠ p 2))
      (by rw [Theory.Generates, groundedGenerable_iff, isContiguous_fin_three_iff])
  | .free => fun _ ↦ isTrue trivial

/-- The five root patterns over three grades, one of each class. -/
def shapes : List (Paradigm 3 ℕ) := [Paradigm.aaa, Paradigm.abb, Paradigm.abc, Paradigm.aba,
  Paradigm.aab]

/-- A theory fits a root pattern under a parse `e`, giving the grade whose structure the root's
word realizes in each cell, when a pattern it generates, read through `e`, classes the grades as
the root pattern does. -/
def Theory.Fits (T : Theory) (e : Fin 3 → Fin 3) (p : Paradigm 3 ℕ) : Prop :=
  ∃ q ∈ shapes, T.Generates q ∧ Setoid.ker (q ∘ e) = Setoid.ker p

instance (T : Theory) (e : Fin 3 → Fin 3) (p : Paradigm 3 ℕ) : Decidable (T.Fits e p) :=
  decidable_of_iff (∃ q ∈ shapes, T.Generates q ∧ (q (e 0) = q (e 1) ↔ p 0 = p 1) ∧
      (q (e 1) = q (e 2) ↔ p 1 = p 2) ∧ (q (e 0) = q (e 2) ↔ p 0 = p 2)) <| by
    simp only [Theory.Fits, ker_eq_ker_iff_fin_three, Function.comp_apply]

/-! ### The parses -/

/-- How a theory parses a triple, from the root pattern every theory shares, into the grade
whose structure the root's word realizes in each cell. -/
abbrev TripleParser := Parser RootClasses (Paradigm 3 ℕ) (Fin 3 → Fin 3)

/-- Every triple read as synthetic. -/
def naive : TripleParser := .ofRule fun _ ↦ some id

/-- Bobaljik's parse: synthetic, but for the Bulgarian and the Armenian 'many', whose
superlatives embed the positive (pp. 127-129). -/
def bobaljik : TripleParser :=
  ⟨fun _ ↦ some id, List.toFinmap
    [⟨bul_many.roots, positiveEmbedding⟩, ⟨hye_many.roots, positiveEmbedding⟩]⟩

theorem stipulations_naive : naive.stipulations = ∅ := Parser.stipulations_ofRule _

theorem card_stipulations_bobaljik : bobaljik.stipulations.card = 2 := by
  decide +kernel

/-! ### Triple by triple -/

/-- Each triple scored by whether a theory, under its parse, fits it. -/
def triples : Experiment (Theory × TripleParser) RootClasses Bool where
  observed r := if Contested r then none else some true
  predicted Tπ r := (Tπ.2.parse rootPattern r).map fun e ↦ decide (Tπ.1.Fits e (rootPattern r))

/-- Read as synthetic, the Basque doublet and the Bulgarian and Armenian quantifiers refute
Elsewhere insertion. -/
theorem wrong_naive_elsewhere :
    (rootClasses.filter (triples.verdict (.elsewhere, naive) · = .wrong)).map (·.id) =
      [eus_good_on.roots.id, bul_many.roots.id, hye_many.roots.id] := by
  decide +kernel

/-- Read as synthetic, the same three triples refute grounded containment. -/
theorem wrong_naive_grounded :
    (rootClasses.filter (triples.verdict (.grounded, naive) · = .wrong)).map (·.id) =
      [eus_good_on.roots.id, bul_many.roots.id, hye_many.roots.id] := by
  decide +kernel

/-- Bobaljik's parse agrees with the naive one off its stipulations. -/
theorem verdict_bobaljik_of_notMem {T : Theory} {r : RootClasses}
    (hr : r ∉ bobaljik.stipulations) :
    triples.verdict (T, bobaljik) r = triples.verdict (T, naive) r := by
  simp only [Experiment.verdict, triples, Parser.parse_of_notMem bobaljik rootPattern hr, naive,
    Parser.parse_ofRule]
  rfl

/-- Bobaljik's parse makes every theory right on the Bulgarian and Armenian quantifiers, so
under it the containment theories are wrong on the Basque doublet alone. -/
theorem verdict_bobaljik_stipulated (T : Theory) :
    triples.verdict (T, bobaljik) bul_many.roots = .correct ∧
      triples.verdict (T, bobaljik) hye_many.roots = .correct := by
  cases T <;> decide +kernel

/-- The only contested triple is Zajkov's Karelian one. -/
theorem contested_ids : (rootClasses.filter Contested).map (·.id) = [krl_many.roots.id] := by
  decide +kernel

/-- Under a parse whose rule covers every triple, a theory is silent exactly on the contested
triples. -/
theorem verdict_eq_silent_iff {T : Theory} {π : TripleParser} (hπ : ∀ p, π.rule p = some id)
    (r : RootClasses) : triples.verdict (T, π) r = .silent ↔ Contested r := by
  obtain ⟨e, he⟩ : ∃ e, π.parse rootPattern r = some e := by
    cases h : π.table.lookup r <;> simp [Parser.parse, h, hπ]
  by_cases hc : Contested r
  · simp [Experiment.verdict, triples, he, hc, Verdict.of]
  · simp only [Experiment.verdict, triples, he, hc, Option.map_some, ite_false, Verdict.of,
      iff_false]
    split <;> simp

/-- Read as synthetic, every root pattern fits the theory without containment. -/
theorem free_fits_id (p : Paradigm 3 ℕ) : Theory.free.Fits id p := by
  simp only [Theory.Fits, Theory.Generates, true_and, Function.comp_id, ker_eq_ker_iff_fin_three,
    shapes, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
  by_cases h01 : p 0 = p 1 <;> by_cases h12 : p 1 = p 2 <;> by_cases h02 : p 0 = p 2 <;>
    simp_all [Paradigm.aaa, Paradigm.abb, Paradigm.abc, Paradigm.aba, Paradigm.aab]

/-- Read as synthetic, the theory without containment is never wrong. -/
theorem verdict_free_naive_ne_wrong (r : RootClasses) :
    triples.verdict (.free, naive) r ≠ .wrong := by
  simp only [Experiment.verdict, triples, naive, Parser.parse_ofRule, Option.map_some,
    free_fits_id, decide_true]
  split <;> simp [Verdict.of]

/-! ### Pattern by pattern -/

/-- Each root pattern scored by whether an observed triple shows it, with the asymmetric linking
hypothesis: a theory predicts the absence of each pattern it cannot generate. -/
def patterns : Experiment Theory (Paradigm 3 ℕ) Bool where
  observed c :=
    some (decide (∃ r ∈ rootClasses, ¬ Contested r ∧ Setoid.ker (rootPattern r) = Setoid.ker c))
  predicted T c := if T.Generates c then none else some false

/-- Grounded containment is right that no triple is AAB, where Elsewhere insertion predicts
nothing; both are wrong that none is ABA; the theory without containment predicts nothing. -/
theorem verdict_patterns :
    patterns.verdict .grounded Paradigm.aab = .correct ∧
      patterns.verdict .elsewhere Paradigm.aab = .silent ∧
      patterns.verdict .grounded Paradigm.aba = .wrong ∧
      patterns.verdict .elsewhere Paradigm.aba = .wrong ∧
      ∀ c, patterns.verdict .free c = .silent := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, fun _ ↦ rfl⟩

end Eval.Suppletion.Bobaljik2012
