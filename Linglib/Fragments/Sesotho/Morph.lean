module

public import Linglib.Core.Computability.RegularExpressions

/-!
# Sesotho verb affixes

The affixes of the Sesotho (Southern Sotho) verb and the order in which they appear. Before
the stem, word-edge inward, come the subject marker, the negative *-sa-*, a tense, aspect or
mood marker and the object marker or the reflexive; after it, stem-outward, the reversive
*-oll-*, the extensions that change valence (the causative *-is-*, the neuter *-eh-*, the
applicative *-el-*, the completive *-ell-*, which reduplicates the applicative, and the
reciprocal *-an-*), the passive *-w-*, the perfect *-il-*, the mood ending and the
interrogative or relative *-ng*. A form takes at most one affix of each position except the
extensions, which stack, so the template is a regular expression over the positions with the
extension position starred, and a string of affixes in linear order, the stem left out, is
licensed when its positions match it.

The inventory and its order are those [hahn-degen-futrell-2021] extract from the corpus of
[demuth-1992] and document from [doke-mofokeng-1967]. The corpus fuses some neighbouring
markers, a tense prefix with the following object marker in particular, and treats the
interrogative *-ng*, a clitic form of *eng* 'what', as a suffix.

## Main definitions

* `Sesotho.Verb.Slot`, `Sesotho.Verb.Exponent`: the affix positions and the affixes of each.
* `Sesotho.Verb.prefixes`, `Sesotho.Verb.suffixes`: the positions before and after the stem,
  word-edge inward and stem-outward.
* `Sesotho.Verb.template`, `Sesotho.Verb.Licensed`: the regular expression over the positions
  and the affix strings it admits.

## Main results

* `Sesotho.Verb.licensed_of_sublist`: a string that fills each position at most once, in
  order, is licensed.
* `Sesotho.Verb.licensed_replicate_extension`: the extension position takes any number of
  affixes.

## Implementation notes

The affixes are cited in their docstrings and not entered as morphs: the subject and object
markers are paradigms over person, number and noun class, and the perfect and the mood endings
vary with their context, which a paradigm layer would carry. The infinitive prefix *ho-* is not
entered.

## References

* [M. Hahn, J. Degen, R. Futrell, *Modeling Word and Morpheme Order in Natural Language as an
  Efficient Trade-Off of Memory and Surprisal* (2021)][hahn-degen-futrell-2021]
* [K. Demuth, *Acquisition of Sesotho* (1992)][demuth-1992]
* [C. M. Doke, S. M. Mofokeng, *Textbook of Southern Sotho Grammar* (1967)][doke-mofokeng-1967]
-/

@[expose] public section

namespace Sesotho.Verb

/-- The affix positions of the verb: the prefix positions word-edge inward, then the suffix
positions stem-outward. -/
inductive Slot where
  /-- The subject marker. -/
  | subject
  /-- The negative *-sa-*. -/
  | negation
  /-- The tense, aspect and mood prefixes. -/
  | tam
  /-- The object marker or the reflexive. -/
  | object
  /-- The reversive *-oll-*. -/
  | reversive
  /-- The extensions that change valence. -/
  | extension
  /-- The passive *-w-*. -/
  | voice
  /-- The perfect *-il-*. -/
  | tense
  /-- The mood ending. -/
  | mood
  /-- The interrogative and the relative *-ng*. -/
  | interrogativeRelative
  deriving DecidableEq, Repr

/-- The affixes of each position. -/
inductive Exponent : Slot → Type where
  /-- The subject marker of a main clause. -/
  | subject : Exponent .subject
  /-- The subject marker of a relative clause. -/
  | relativeSubject : Exponent .subject
  /-- The negative *-sa-*. -/
  | negative : Exponent .negation
  /-- The future *-tla-*, *-tlo-*, *-ilo-*. -/
  | future : Exponent .tam
  /-- The present *-a-*. -/
  | present : Exponent .tam
  /-- The potential *-ka-*. -/
  | potential : Exponent .tam
  /-- The persistive *-sa-*. -/
  | persistive : Exponent .tam
  /-- The recent past *-tswa-*. -/
  | recentPast : Exponent .tam
  /-- The object marker. -/
  | object : Exponent .object
  /-- The reflexive. -/
  | reflexive : Exponent .object
  /-- The reversive *-oll-*: *tlama* 'bind', *tlamolla* 'loosen'. -/
  | reversive : Exponent .reversive
  /-- The causative *-is-*. -/
  | causative : Exponent .extension
  /-- The neuter *-eh-*, *-ahal-*, which removes an argument. -/
  | neuter : Exponent .extension
  /-- The applicative *-el-*, which adds one. -/
  | applicative : Exponent .extension
  /-- The completive *-ell-*, a reduplicated applicative. -/
  | completive : Exponent .extension
  /-- The reciprocal *-an-*. -/
  | reciprocal : Exponent .extension
  /-- The passive *-w-*. -/
  | passive : Exponent .voice
  /-- The perfect *-il-*, *-its-* among its allomorphs. -/
  | perfect : Exponent .tense
  /-- The indicative ending, *-a* or *-e*. -/
  | indicative : Exponent .mood
  /-- The subjunctive ending, *-e* or *-a*, plural *-eng*. -/
  | subjunctive : Exponent .mood
  /-- The imperative *-e*. -/
  | imperative : Exponent .mood
  /-- The plural imperative *-ang*. -/
  | imperativePlural : Exponent .mood
  /-- The interrogative *-ng*. -/
  | interrogative : Exponent .interrogativeRelative
  /-- The relative *-ng*. -/
  | relative : Exponent .interrogativeRelative
  deriving DecidableEq

/-- The prefix positions, word-edge inward. -/
def prefixes : List Slot := [.subject, .negation, .tam, .object]

/-- The suffix positions, stem-outward. -/
def suffixes : List Slot :=
  [.reversive, .extension, .voice, .tense, .mood, .interrogativeRelative]

open RegularExpression in
/-- The template: the positions in linear order, each at most once, the extension position any
number of times. -/
def template : RegularExpression Slot :=
  sublists [.subject, .negation, .tam, .object, .reversive] * (char .extension).star *
    sublists [.voice, .tense, .mood, .interrogativeRelative]

/-- A string of affixes, in linear order, is licensed when its positions match the template. -/
def Licensed (w : List (Σ σ, Exponent σ)) : Prop := w.map Sigma.fst ∈ template.matches'

instance : DecidablePred Licensed := fun _ ↦ inferInstanceAs (Decidable (_ ∈ _))

open List RegularExpression in
/-- A string of affixes that fills each position at most once, in order, is licensed. -/
theorem licensed_of_sublist {w : List (Σ σ, Exponent σ)}
    (h : w.map Sigma.fst <+ prefixes ++ suffixes) : Licensed w := by
  have h' : w.map Sigma.fst <+
      ([.subject, .negation, .tam, .object, .reversive] ++ [.extension]) ++
        [.voice, .tense, .mood, .interrogativeRelative] := h
  obtain ⟨a', c, hw, ha', hc⟩ := sublist_append_iff.mp h'
  obtain ⟨a, b, rfl, ha, hb⟩ := sublist_append_iff.mp ha'
  have hb' : b ∈ KStar.kstar ({[Slot.extension]} : Language Slot) := by
    rcases sublist_singleton.mp hb with rfl | rfl
    · exact Language.nil_mem_kstar _
    · exact Language.mem_kstar.mpr ⟨[[.extension]], rfl, fun y hy ↦ by
        rw [List.mem_singleton.mp hy]; exact Set.mem_singleton _⟩
  simp only [Licensed, template, matches'_mul, matches'_star, matches'_sublists, matches'_char,
    Language.mem_mul]
  exact ⟨a ++ b, ⟨a, ha, b, hb', rfl⟩, c, hc, hw.symm⟩

open RegularExpression in
/-- The extension position takes any number of affixes: `n` applicatives are licensed. -/
theorem licensed_replicate_extension (n : ℕ) :
    Licensed (List.replicate n ⟨_, Exponent.applicative⟩) := by
  simp only [Licensed, template, matches'_mul, matches'_star, matches'_sublists, matches'_char,
    Language.mem_mul, List.map_replicate]
  refine ⟨_, ⟨[], List.nil_sublist _, _, ?_, rfl⟩, [], List.nil_sublist _, List.append_nil _⟩
  exact Language.mem_kstar.mpr ⟨List.replicate n [.extension], by simp, fun y hy ↦ by
    rw [List.eq_of_mem_replicate hy]; exact Set.mem_singleton _⟩

end Sesotho.Verb
