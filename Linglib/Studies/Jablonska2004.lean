import Linglib.Data.Examples.Jablonska2004
import Linglib.Studies.Svenonius2004

/-!
# Jabłońska (2004): When the Prefixes Meet the Suffixes

This file formalizes [jablonska-2004], the account of the readings of the Polish prefix *po-*
as a function of the verbalizer it attaches to. The verbalizer classes of Table 1 and Table 2
(`Verbalizer`) each carry an Aktionsart profile (`Verbalizer.profile`) and a continuum for
*po-* to measure along, (40): the run time of a process, the scale of a gradable property, (16),
or a path, (55). A derivation stacks the four prefix positions of (41) and the Secondary
Imperfective as layers (`Layer`) over a stem, each merging only when its selectional
requirement is met (`Layer.merge`), and well-formedness (`WellFormed`) and perfectivity
(`Perfective`) are read off the resulting profile. The seven shapes of a well-formed derivation
(`wellFormed_iff`) yield the paper's generalizations: stacking is contingent on the Secondary
Imperfective (`si_of_asp3`), a purely perfectivizing prefix stacks with nothing (`eq_of_perf`),
only the interval-denoting classes form Secondary Imperfectives (`denotesInterval_of_si`), and
the stacking generalization of [svenonius-2004] follows (`wellStacked`). The readings of *po-*
follow from the continuum and the boundaries of the stem (`Asp1Reading`, `Asp3Reading`) and
reproduce Table 2 (`asp1Reading_iff_table2`). The attested forms are analysed (`attested`) and
the starred ones excluded (`starred_not_wellFormed`).

## Implementation notes

* The Aktionsart profile of a bare stem is atelic throughout, the paper's unbounded bare stem;
  the semelfactive is the punctual class and the stative the non-dynamic one. The continuum,
  the telos and the adjectival base are the paper's own parameters.
* The semelfactive suffix values [uPerf] against Asp1, (47): a bare semelfactive is perfective,
  and a purely perfectivizing prefix over it is a vacuous viewpoint shift, (70), which Table 2
  hedges as "yes ???" (`wellFormed_perf_iff`). A lexical prefix on a semelfactive stays
  possible in principle, (79a) and fn. 20.
* With directed motion stems the purely perfectivizing position is filled by *do-* or *przy-*,
  Table 2 fn. c; the model records these stems as lacking a telos of their own.
* The "considerable change" reading is confined to *-ej-* stems: fn. 22 records that
  inchoative *-n-* stems lack it without deriving the gap. The inceptive *za-* of (53) reads an
  *-ej-* stem as a state and is recorded as a row only.

## References

* [jablonska-2004]
* [svenonius-2004]
* [demirdache-uribe-etxebarria-2000]
* [rothstein-2004]
-/

namespace Jablonska2004

open Data.Examples (LinguisticExample)
open Features (AspectualProfile)
open Morphology (Morph)
open Verb (Stem)
open Svenonius2004 (PrefixClass WellStacked)
open Polish.Verbs

/-! ### Verbalizers -/

/-- The verbalizer classes of Table 1 and Table 2. -/
inductive Verbalizer
  /-- The high processual verbalizers *-i/y-* and *-aj-*, with root insertion inside ν. -/
  | processual
  /-- The high instantaneous verbalizer, semelfactive *-n-*. -/
  | semelfactive
  /-- The low verbalizer *-ej-*: a degree achievement over an adjectival base, (2b). -/
  | degree
  /-- The low inchoative verbalizer *-n-*, (2a). -/
  | inchoative
  /-- A directed-motion stem, measuring movement along a path, (55). -/
  | directedMotion
  /-- A non-directed-motion stem, a high processual verbalizer, (49). -/
  | nonDirectedMotion
  /-- A stative stem. -/
  | stative
  deriving DecidableEq

/-- The continuum along which *po-* measures development, (40). -/
inductive Continuum
  | temporal
  | degree
  | path
  deriving DecidableEq

namespace Verbalizer

/-- The Aktionsart profile of a bare stem: atelic, lacking a right boundary, Section 2.3;
punctual for the semelfactive, Section 2.3.1; stative for the statives, which lack a left
boundary, Section 5. -/
def profile : Verbalizer → AspectualProfile
  | semelfactive => ⟨.atelic, .punctual, .dynamic⟩
  | stative => ⟨.atelic, .durative, .stative⟩
  | _ => ⟨.atelic, .durative, .dynamic⟩

/-- The continuum a verbalizer supplies; a semelfactive is a point and supplies none. -/
def continuum : Verbalizer → Option Continuum
  | processual | nonDirectedMotion | stative => some .temporal
  | degree | inchoative => some .degree
  | directedMotion => some .path
  | semelfactive => none

/-- Punctual: no continuum to measure along, (45). -/
def IsPunctual (v : Verbalizer) : Prop := v.profile.duration = .punctual

instance : DecidablePred IsPunctual := λ v => inferInstanceAs (Decidable (v.profile.duration = _))

/-- Dynamic eventualities come with a left boundary, the preceding state at which the event does
not hold, Section 2.3; states do not. -/
def HasLeftBoundary (v : Verbalizer) : Prop := v.profile.dynamicity = .dynamic

instance : DecidablePred HasLeftBoundary :=
  λ v => inferInstanceAs (Decidable (v.profile.dynamicity = _))

/-- A natural telos for a purely perfectivizing prefix to coincide with, (10): the end of the
scale of a gradable property, or the change of state of the affected object of a processual
verb, Section 2.2. -/
def HasTelos (v : Verbalizer) : Prop := v = processual ∨ v = degree ∨ v = inchoative

instance : DecidablePred HasTelos := λ v => inferInstanceAs (Decidable (v = _ ∨ v = _ ∨ v = _))

/-- An adjectival base in the derivational history, (2b) and (72): no Result phrase. -/
def IsAdjectival (v : Verbalizer) : Prop := v = degree

instance : DecidablePred IsAdjectival := λ v => inferInstanceAs (Decidable (v = _))

/-- Denotes a delimitable interval, the selectional requirement of the Secondary Imperfective,
(66): a temporal continuum and a left boundary. -/
def DenotesInterval (v : Verbalizer) : Prop := v.continuum = some .temporal ∧ v.HasLeftBoundary

instance : DecidablePred DenotesInterval :=
  λ v => inferInstanceAs (Decidable (v.continuum = _ ∧ v.HasLeftBoundary))

@[simp] theorem isPunctual_iff (v : Verbalizer) : v.IsPunctual ↔ v = semelfactive := by
  cases v <;> decide

@[simp] theorem hasLeftBoundary_iff (v : Verbalizer) : v.HasLeftBoundary ↔ v ≠ stative := by
  cases v <;> decide

@[simp] theorem isAdjectival_iff (v : Verbalizer) : v.IsAdjectival ↔ v = degree := Iff.rfl

@[simp] theorem hasTelos_iff (v : Verbalizer) :
    v.HasTelos ↔ v = processual ∨ v = degree ∨ v = inchoative := Iff.rfl

@[simp] theorem denotesInterval_iff (v : Verbalizer) :
    v.DenotesInterval ↔ v = processual ∨ v = nonDirectedMotion := by
  cases v <;> decide

end Verbalizer

/-! ### Aspectual layers -/

/-- The aspectual level reached by a derivation, (41). -/
inductive Level
  | root
  | asp1
  | asp2
  | asp3
  deriving DecidableEq

/-- The aspectual profile of the predicate built so far: the highest projection merged; whether
it is [+Perf], bounded by a Reference Time AFTER its Event Time; and whether its delimited
subevents are changes of state of their participants, the contribution of a lexical prefix,
(30), so that iterated subevents can overlap and be S-summed, (36) and (37). -/
structure Profile where
  level : Level
  bounded : Bool
  resultative : Bool
  deriving DecidableEq

/-- The four prefix positions of (41) and the Secondary Imperfective. -/
inductive Layer
  /-- A lexical prefix in the complement of RP, valuing [uPerf] against Asp1. -/
  | lexical (m : Morph)
  /-- A superlexical prefix in Spec,Asp1P, a Reference Time AFTER the Event Time, (40). -/
  | asp1 (m : Morph)
  /-- A purely perfectivizing prefix in Spec,Asp2P, (68). -/
  | perf (m : Morph)
  /-- The Secondary Imperfective, Asp2 with the semantics WITHIN or OUTSIDE, (66). -/
  | si
  /-- *po-* in Spec,Asp3P, above the Secondary Imperfective, (26). -/
  | asp3 (m : Morph)
  deriving DecidableEq

namespace Layer

/-- Merging a layer over a bare stem of class `v` with profile `p`, when the layer's selectional
requirement is met. A lexical prefix needs a Result phrase, (72); *po-* in Asp1 needs a
continuum, (40); both value [uPerf] against Asp1 and cannot co-occur, (42). A purely
perfectivizing prefix in Asp2 needs a telos and an unbounded predicate, since a second Reference
Time AFTER the first is a vacuous viewpoint shift, (70), which also bars it from a semelfactive,
(47). The Secondary Imperfective selects a delimited interval, (32) and (66), in the Asp2 slot,
(68). *po-* in Asp3 selects a [-Perf] predicate, (25), whose iterated subevents are S-summable,
(36), which requires each to be a change of state of its participant, (37) and (61). -/
def merge (v : Verbalizer) : Layer → Profile → Option Profile
  | lexical _, ⟨.root, _, _⟩ => if v.IsAdjectival then none else some ⟨.asp1, true, true⟩
  | asp1 _, ⟨.root, _, _⟩ => if v.IsPunctual then none else some ⟨.asp1, true, false⟩
  | perf _, ⟨.root, _, r⟩ => if ¬ v.IsPunctual ∧ v.HasTelos then some ⟨.asp2, true, r⟩ else none
  | si, ⟨.asp1, _, r⟩ => if v.DenotesInterval then some ⟨.asp2, false, r⟩ else none
  | asp3 _, ⟨.asp2, false, true⟩ => some ⟨.asp3, true, true⟩
  | _, _ => none

/-- The prefix morph of a layer. -/
def prefix? : Layer → Option Morph
  | lexical m | asp1 m | perf m | asp3 m => some m
  | si => none

/-- A lexical prefix. -/
def IsLexical : Layer → Prop
  | lexical _ => True
  | _ => False

instance : DecidablePred IsLexical
  | lexical _ => isTrue trivial
  | asp1 _ | perf _ | si | asp3 _ => isFalse id

end Layer

/-! ### Derivations -/

/-- The profile after merging the layers `ls`, innermost first, over profile `p`. -/
def profileFrom (v : Verbalizer) : Profile → List Layer → Option Profile
  | p, [] => some p
  | p, l :: ls => (l.merge v p).bind (profileFrom v · ls)

/-- The profile of a derivation over a bare stem of class `v`. -/
def profile (v : Verbalizer) (ls : List Layer) : Option Profile :=
  profileFrom v ⟨.root, false, false⟩ ls

/-- A derivation is well-formed when every layer's selectional requirement is met. -/
def WellFormed (v : Verbalizer) (ls : List Layer) : Prop := (profile v ls).isSome

instance (v : Verbalizer) (ls : List Layer) : Decidable (WellFormed v ls) :=
  inferInstanceAs (Decidable (_ = true))

/-- The derived predicate is [+Perf]: bounded by a Reference Time, or a bare semelfactive, whose
suffix values [uPerf] against Asp1, (47). It is then no complement of a phasal verb and has no
present-tense interpretation, the tests of Section 2.1. -/
def Perfective (v : Verbalizer) (ls : List Layer) : Prop :=
  match profile v ls with
  | some p => p.bounded = true ∨ v.IsPunctual
  | none => False

instance (v : Verbalizer) (ls : List Layer) : Decidable (Perfective v ls) := by
  unfold Perfective; split <;> infer_instance

@[local simp] private theorem bind_ite_none_left {α β : Type*} {c : Prop} [Decidable c]
    {a : α} {f : α → Option β} : (if c then none else some a).bind f = if c then none else f a := by
  split_ifs <;> rfl

@[local simp] private theorem bind_ite_none_right {α β : Type*} {c : Prop} [Decidable c]
    {a : α} {f : α → Option β} : (if c then some a else none).bind f = if c then f a else none := by
  split_ifs <;> rfl

/-- The seven shapes of a well-formed derivation: a bare stem; a lexical prefix, (30); *po-* in
Asp1, (27); a purely perfectivizing prefix, (67); a lexically prefixed or Asp1-delimited stem
under the Secondary Imperfective, (31a) and (56); and *po-* in Asp3 over a lexically prefixed
Secondary Imperfective, (34). -/
theorem wellFormed_iff {v : Verbalizer} {ls : List Layer} :
    WellFormed v ls ↔
      ls = [] ∨
      (∃ m, ls = [.lexical m] ∧ ¬ v.IsAdjectival) ∨
      (∃ m, ls = [.asp1 m] ∧ ¬ v.IsPunctual) ∨
      (∃ m, ls = [.perf m] ∧ ¬ v.IsPunctual ∧ v.HasTelos) ∨
      (∃ m, ls = [.lexical m, .si] ∧ ¬ v.IsAdjectival ∧ v.DenotesInterval) ∨
      (∃ m, ls = [.asp1 m, .si] ∧ ¬ v.IsPunctual ∧ v.DenotesInterval) ∨
      (∃ m m', ls = [.lexical m, .si, .asp3 m'] ∧ ¬ v.IsAdjectival ∧ v.DenotesInterval) := by
  constructor
  · intro h
    obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1 h
    clear h
    rcases ls with _ | ⟨a, ls⟩
    · exact Or.inl rfl
    cases a <;> simp_all [profile, profileFrom, Layer.merge] <;>
      rcases ls with _ | ⟨b, ls⟩ <;> simp_all [profileFrom, Layer.merge] <;>
      cases b <;> simp_all <;>
      rcases ls with _ | ⟨c, ls⟩ <;> simp_all [profileFrom, Layer.merge]
    cases c <;> simp_all
    rcases ls with _ | ⟨d, ls⟩ <;> simp_all [profileFrom, Layer.merge]
  · rintro (rfl | ⟨m, rfl, h⟩ | ⟨m, rfl, h⟩ | ⟨m, rfl, h₁, h₂⟩ | ⟨m, rfl, h₁, h₂⟩ |
        ⟨m, rfl, h₁, h₂⟩ | ⟨m, m', rfl, h₁, h₂⟩) <;>
      simp_all [WellFormed, profile, profileFrom, Layer.merge]

/-- The seven shapes, as a case split on a well-formedness hypothesis. -/
local macro "shapes" h:term : tactic =>
  `(tactic| rcases wellFormed_iff.1 $h with rfl | ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ | ⟨_, rfl, _, _⟩ |
      ⟨_, rfl, _, _⟩ | ⟨_, rfl, _, _⟩ | ⟨_, _, rfl, _, _⟩)

/-! ### The paper's generalizations -/

section Generalizations

variable {v : Verbalizer} {ls : List Layer} {m m' : Morph}

/-- A bare stem is perfective exactly when it is a semelfactive, (46). -/
theorem perfective_nil_iff : Perfective v [] ↔ v.IsPunctual := by
  simp [Perfective, profile, profileFrom]

/-- Stacking is contingent on the Secondary Imperfective, Section 5: *po-* in Asp3 stacks only
over a secondary imperfective, (24) and (42), and never over an attenuative-frequentative, (61). -/
theorem si_of_asp3 (h : WellFormed v ls) (hm : .asp3 m ∈ ls) :
    ∃ m', ls = [.lexical m', .si, .asp3 m] := by
  shapes h <;> simp_all

/-- A purely perfectivizing prefix stacks on nothing and nothing stacks on it, (70): it is in
complementary distribution with the Secondary Imperfective, (67), (69) and (68). -/
theorem eq_of_perf (h : WellFormed v ls) (hm : .perf m ∈ ls) : ls = [.perf m] := by
  shapes h <;> simp_all

/-- Only the interval-denoting classes, the processual and the non-directed motion stems, form
Secondary Imperfectives: not the degree achievements, (59) and (74), the inchoatives, (76), the
semelfactives, (48) and (79b), the directed motion stems, (80), or the statives. -/
theorem denotesInterval_of_si (h : WellFormed v ls) (hm : .si ∈ ls) : v.DenotesInterval := by
  shapes h <;> simp_all

/-- A lexical prefix and *po-* in Asp1 both value [uPerf] against Asp1, so they do not co-occur,
(42): no Multiple Agree. -/
theorem not_lexical_and_asp1 (h : WellFormed v ls) : ¬ (.lexical m ∈ ls ∧ .asp1 m' ∈ ls) := by
  shapes h <;> simp_all

/-- *po-* in Asp3 makes the derivation perfective, (33). -/
theorem perfective_of_asp3 (h : WellFormed v ls) (hm : .asp3 m ∈ ls) : Perfective v ls := by
  shapes h <;> cases v <;> simp_all [Perfective, profile, profileFrom, Layer.merge]

/-- A derivation closed by the Secondary Imperfective is imperfective: the
attenuative-frequentative forms, (56) and (64), are imperfectives, and Asp3 *po-* selects for
[-Perf], (25). -/
theorem not_perfective_of_getLast_si (h : WellFormed v ls) (hl : ls.getLast? = some .si) :
    ¬ Perfective v ls := by
  shapes h <;> cases v <;> simp_all [Perfective, profile, profileFrom, Layer.merge]

/-- The prefix sequence of a derivation, outermost first, under any classification `f` that
agrees with the lexical/superlexical split, is well-stacked in the sense of [svenonius-2004]:
the superlexical prefix is always outside the lexical one. -/
theorem wellStacked (h : WellFormed v ls) (f : Layer → PrefixClass)
    (hf : ∀ l, (f l).IsSuperlexical ↔ ¬ l.IsLexical) :
    WellStacked (ls.reverse.filterMap λ l => l.prefix?.map (·, f l)) := by
  shapes h <;> simp_all [WellStacked, Layer.prefix?, Layer.IsLexical]

end Generalizations

/-! ### Table 2 -/

section Table2

variable (v : Verbalizer) (m : Morph)

/-- Table 2, Asp2: a purely perfectivizing prefix needs a telos, (10) and (67), which the
motion stems and the statives lack, and an unbounded stem, which the semelfactive is not, (47):
the cell Table 2 hedges as "yes ???" is closed. -/
theorem wellFormed_perf_iff :
    WellFormed v [.perf m] ↔ v = .processual ∨ v = .degree ∨ v = .inchoative := by
  cases v <;> simp [wellFormed_iff]

/-- Table 2, the Secondary Imperfective: the processual and non-directed motion stems, which
are also the classes on which *po-* stacks in Asp3, (43) and (83). -/
theorem wellFormed_lexical_si_iff :
    WellFormed v [.lexical m, .si] ↔ v = .processual ∨ v = .nonDirectedMotion := by
  cases v <;> simp [wellFormed_iff]

end Table2

/-! ### Readings -/

/-- The readings of superlexical *po-*. -/
inductive Reading
  /-- 'for a while': an arbitrary Reference Time, short of any telos, (12) and (27). -/
  | delimitative
  /-- A degree of change short of the end of the scale, (11) and (22). -/
  | considerableChange
  /-- 'away': ground covered along the path, (50). -/
  | centrifugal
  /-- A Reference Time after the last of the S-summed subevents, one per atom of the plural
  internal argument, each reaching its telos, (23) and (28). -/
  | distributive
  /-- A Reference Time BEFORE the Event Time, fixing the missing left boundary of a state,
  (54). -/
  | inceptive
  deriving DecidableEq

/-- The readings of *po-* in Spec,Asp1P on a stem of class `v`, `plural` the plurality of the
internal argument: the reading measures along the stem's continuum, (40); the distributive
reading S-sums one subevent per atom of a plural internal argument, each with its telos, (36);
and the inceptive reading fixes a left boundary the stem lacks, Section 2.4. -/
def Asp1Reading (v : Verbalizer) (plural : Bool) : Reading → Prop
  | .delimitative => v.continuum = some .temporal
  | .considerableChange => v = .degree
  | .centrifugal => v.continuum = some .path
  | .distributive => plural = true ∧ v.HasTelos
  | .inceptive => ¬ v.HasLeftBoundary

instance (v : Verbalizer) (plural : Bool) : DecidablePred (Asp1Reading v plural) := λ r => by
  cases r <;> unfold Asp1Reading <;> infer_instance

/-- The readings of *po-* in Spec,Asp3P, (34): delimitative when the third Reference Time
falls WITHIN the inherited first one, distributive when it follows the last iterated subevent,
which needs a plural internal argument, (28e). -/
def Asp3Reading (plural : Bool) : Reading → Prop
  | .delimitative => True
  | .distributive => plural = true
  | _ => False

instance (plural : Bool) : DecidablePred (Asp3Reading plural) := λ r => by
  cases r <;> unfold Asp3Reading <;> infer_instance

/-- The Asp1 column of Table 2. -/
def table2Asp1 : Verbalizer → List Reading
  | .processual => [.delimitative, .distributive]
  | .semelfactive => []
  | .degree => [.distributive, .considerableChange]
  | .inchoative => [.distributive]
  | .directedMotion => [.centrifugal]
  | .nonDirectedMotion => [.delimitative]
  | .stative => [.inceptive, .delimitative]

/-- The derived readings of *po-* in Asp1, with a plural internal argument, are those of
Table 2: no delimitative reading with the change-of-state stems, Section 5, and the inceptive
reading only with the statives, Section 2.4. -/
theorem asp1Reading_iff_table2 (v : Verbalizer) (r : Reading) :
    Asp1Reading v true r ↔ r ∈ table2Asp1 v := by
  cases v <;> cases r <;> decide

/-- Without a plural internal argument the distributive reading is gone: (28c) has only the
delimitative reading, the external argument being outside the scope of *po-*, (29). -/
theorem not_asp1Reading_distributive (v : Verbalizer) : ¬ Asp1Reading v false .distributive := by
  simp [Asp1Reading]

/-! ### The paper's analyses -/

/-- An analysis of an attested form: the fragment stem, its verbalizer class, the layers
innermost first, the plurality of the internal argument, and the paper's readings of the
superlexical *po-*, if any. -/
structure Analysis where
  ex : LinguisticExample
  stem : Stem
  verbalizer : Verbalizer
  layers : List Layer
  plural : Bool
  readings : List Reading

/-- The reading is available to the superlexical *po-* of the analysis, at Asp3 when the
derivation is closed by *po-* there and at Asp1 otherwise. -/
def Analysis.Available (a : Analysis) (r : Reading) : Prop :=
  match a.layers.getLast? with
  | some (.asp3 _) => Asp3Reading a.plural r
  | _ => Asp1Reading a.verbalizer a.plural r

instance (a : Analysis) (r : Reading) : Decidable (a.Available r) := by
  unfold Analysis.Available; split <;> infer_instance

/-- The attested forms: the degree achievements of (10) and (23), the processual stems of (24),
(27), (28), (30), (31), (34) and (43), the inchoatives of (39), the semelfactive of (46), the
motion stems of (50), (51) and (80), the statives of (54) and fn. 21, the
attenuative-frequentatives of (56) and (65), the purely perfectivized stems of (67), (69) and
(75), the class shift of (77), the lexically prefixed semelfactive of (79) and the lexical *po-*
of (81) to (83). -/
def attested : List Analysis :=
  [⟨Examples.ex_10a_po, ciemniec, .degree, [.asp1 po], false, [.considerableChange]⟩,
   ⟨Examples.ex_10a_z, ciemniec, .degree, [.perf z], false, []⟩,
   ⟨Examples.ex_23a, babiec, .degree, [.asp1 po], true, [.distributive]⟩,
   ⟨Examples.ex_24a, czytac, .processual, [.lexical prze, .si, .asp3 po], true, [.distributive]⟩,
   ⟨Examples.ex_27a, czytac, .processual, [.asp1 po], false, [.delimitative]⟩,
   ⟨Examples.ex_28a, chowac, .processual, [.asp1 po], true, [.distributive, .delimitative]⟩,
   ⟨Examples.ex_28b, pisac, .processual, [.lexical prze, .si, .asp3 po], true,
     [.distributive, .delimitative]⟩,
   ⟨Examples.ex_28c, spiewac, .processual, [.asp1 po], false, [.delimitative]⟩,
   ⟨Examples.ex_28d, chodzic, .nonDirectedMotion, [.lexical w, .si, .asp3 po], true,
     [.distributive, .delimitative]⟩,
   ⟨Examples.ex_30, pisac, .processual, [.lexical prze], false, []⟩,
   ⟨Examples.ex_31a, pisac, .processual, [.lexical prze, .si], false, []⟩,
   ⟨Examples.ex_34a, pisac, .processual, [.lexical prze, .si, .asp3 po], true, [.delimitative]⟩,
   ⟨Examples.ex_34b, pisac, .processual, [.lexical prze, .si, .asp3 po], true, [.distributive]⟩,
   ⟨Examples.ex_39a, marznac, .inchoative, [.asp1 po], true, [.distributive]⟩,
   ⟨Examples.ex_43a, kopac, .processual, [.lexical ob, .si, .asp3 po], true,
     [.distributive, .delimitative]⟩,
   ⟨Examples.ex_46b, machnac, .semelfactive, [], false, []⟩,
   ⟨Examples.ex_50b, biec, .directedMotion, [.asp1 po], false, [.centrifugal]⟩,
   ⟨Examples.ex_51a, chodzic, .nonDirectedMotion, [.asp1 po], false, [.delimitative]⟩,
   ⟨Examples.ex_54a, kochac, .stative, [.asp1 po], false, [.inceptive]⟩,
   ⟨Examples.fn21, siedziec, .stative, [.asp1 po], false, [.delimitative]⟩,
   ⟨Examples.ex_56b, grac, .processual, [.asp1 po, .si], false, [.delimitative]⟩,
   ⟨Examples.ex_65a, dmuchac, .processual, [.asp1 po, .si], false, [.delimitative]⟩,
   ⟨Examples.ex_67a_pf, tracic, .processual, [.perf s], false, []⟩,
   ⟨Examples.ex_69a_pf, brudzic, .processual, [.perf po], false, []⟩,
   ⟨Examples.ex_75a, gasnac, .inchoative, [.lexical wy], false, []⟩,
   ⟨Examples.ex_75b, gasnac, .inchoative, [.perf z], false, []⟩,
   ⟨Examples.ex_77, gasnac, .processual, [.lexical wy, .si], false, []⟩,
   ⟨Examples.ex_79a, szepnac, .semelfactive, [.lexical pod], false, []⟩,
   ⟨Examples.ex_80b, plywac, .nonDirectedMotion, [.lexical do_, .si], false, []⟩,
   ⟨Examples.ex_81c, rownac, .processual, [.lexical po], false, []⟩,
   ⟨Examples.ex_82c, rownac, .processual, [.lexical po, .si], false, []⟩,
   ⟨Examples.ex_83a, rownac, .processual, [.lexical po, .si, .asp3 po], true, [.distributive]⟩]

/-- The starred forms: *po-* in Asp3 over a perfective, (24b) and (42); the Secondary
Imperfective of a bare stem, (32), of a semelfactive, (48) and (79b), of a purely perfectivized
stem, (67), (69), (73) and (78), of a degree achievement, (74), and of an inchoative, (76);
*po-* on a semelfactive, (45) and (63b); and *po-* over an attenuative-frequentative, (61). -/
def starred : List Analysis :=
  [⟨Examples.ex_24b, czytac, .processual, [.lexical prze, .asp3 po], true, []⟩,
   ⟨Examples.ex_32a, robic, .processual, [.si], false, []⟩,
   ⟨Examples.ex_42b, kopac, .processual, [.lexical ob, .asp3 po], false, []⟩,
   ⟨Examples.ex_45a, warknac, .semelfactive, [.asp1 po], false, []⟩,
   ⟨Examples.ex_48, warknac, .semelfactive, [.asp1 po, .si], false, []⟩,
   ⟨Examples.ex_61a, grac, .processual, [.asp1 po, .si, .asp3 po], false, []⟩,
   ⟨Examples.ex_63b, miauknac, .semelfactive, [.asp1 po], false, []⟩,
   ⟨Examples.ex_67a_si, tracic, .processual, [.perf s, .si], false, []⟩,
   ⟨Examples.ex_69a_si, brudzic, .processual, [.perf po, .si], false, []⟩,
   ⟨Examples.ex_73a, dziczec, .degree, [.perf z, .si], false, []⟩,
   ⟨Examples.ex_74, siwiec, .degree, [.asp1 po, .si], false, []⟩,
   ⟨Examples.ex_76, gasnac, .inchoative, [.lexical wy, .si], false, []⟩,
   ⟨Examples.ex_78, gasnac, .inchoative, [.perf z, .si], false, []⟩,
   ⟨Examples.ex_79b, szepnac, .semelfactive, [.lexical pod, .si], false, []⟩]

/-- Every attested form is a well-formed derivation. -/
theorem attested_wellFormed : ∀ a ∈ attested, WellFormed a.verbalizer a.layers := by decide

/-- Every starred form is excluded. -/
theorem starred_not_wellFormed : ∀ a ∈ starred, ¬ WellFormed a.verbalizer a.layers := by decide

/-- The paper's readings of *po-* are the derived ones. -/
theorem attested_readings : ∀ a ∈ attested, ∀ r ∈ a.readings, a.Available r := by decide

/-- The fragment's dictionary aspect of each analysed stem is the bare-stem perfectivity the
model derives: perfective for the semelfactives, imperfective otherwise, (46). -/
theorem attested_stem_perfectivity :
    ∀ a ∈ attested, (a.stem.perfectivity = .perfective ↔ Perfective a.verbalizer []) := by
  decide

/-- The attested derivations closed by the Secondary Imperfective are imperfective and the rest
perfective, by the tests of Section 2.1: (31a) and the attenuative-frequentatives pass the
phasal-complement test, (33) and (46) fail it. -/
theorem attested_perfective :
    ∀ a ∈ attested, (Perfective a.verbalizer a.layers ↔ a.layers.getLast? ≠ some .si) := by
  decide

end Jablonska2004
