import Linglib.Data.Examples.Cuervo2003
import Linglib.Syntax.Minimalist.Verbal.LittleV
import Linglib.Syntax.Minimalist.Defs
import Linglib.Fragments.Romance.Spanish.Verbs
import Linglib.Fragments.English.Verbs

/-!
# Cuervo (2003): Datives at Large

This file formalizes the central claim of [cuervo-2003]: dative arguments have structural
meanings. A dative is licensed by an applicative head, and what it means is read off where that
head merges in the event structure, the chain of [cuervo-2003]'s flavors of v
(`Minimalist.LittleV`). Table (28) distinguishes three positions. Below every verbal head, the
applicative takes the theme DP as its complement and relates the dative to an individual, as a
recipient, a source or a possessor according to the verb and to pragmatics: the low applicative,
the double object construction of Chapter 2. Between two heads, it takes the lower vP, a result
state, as its complement and is itself the complement of the dynamic head above, so the dative
participates in two events, external to the state and internal to the change or activity: the
affected applicative of Chapter 3, the addition to Pylkkänen's typology. Above every head, it
takes the whole vP and relates the dative to the event: the high applicative of Chapter 4, an
experiencer over a state or a change and a benefactive or malefactive, the ethical dative, over an
activity. Every cell of table (40) is a value of `Site.meaning`.

Three restrictions turn the geometry into predictions. A low applicative needs the theme as the
complement of the root, which it is in a simple structure whose root licenses an object, but not
in a complex one, where the theme is the specifier of the lower vP, nor in a predicational state;
so the double object construction is structurally incompatible with causatives and inchoatives
(§3.1, §3.2.3), and Baker's gap, the absence of the construction with unaccusatives, reduces to
simple verbs of change, with which Spanish has it (*A Gabi le llegaron dos cartas*). English lacks
the affected applicative and every high one, and has the low applicative TO under activities
alone, which is why its causatives, inchoatives and unaccusatives take no dative at all. A high
applicative requires an animate dative, so an inanimate dative with an inchoative is affected and
nothing else, while an animate one is ambiguous between the affected reading and the
unintentional-responsibility reading of a high applicative over vGO (§4.2.3). And the Spanish
high applicative over an activity is defective: it is spelled out by a clitic and projects no
specifier, so an unergative takes a dative clitic and no dative DP (§4.3.2).

## Main definitions

* `Site`, `Site.Low`, `Site.Affected`, `Site.High`, `Site.complement`, `Site.selector`: the merge
  site of an applicative and the three types of table (28).
* `Meaning`, `LowRelation`, `Site.meaning`: table (40).
* `Predicate`, `Predicate.ThemeIsRootComplement`: a verb's use with its event structure.
* `Inventory`, `spanish`, `english`, `Inventory.Licenses`, `meanings`: which datives a language's
  applicative heads license and what they mean.

## Main results

* `Site.Affected.biEventive`, `Site.Affected.selector_dynamic`, `Site.not_affected_of_state`: an
  affected dative needs two events and a dynamic head above it, so none is applied under a state.
* `not_licenses_low_of_biEventive`, `english_not_licenses_of_biEventive`,
  `english_not_licenses_change`: no double object construction with a complex structure; no
  dative at all in English causatives, inchoatives and simple verbs of change.
* `unergative_clitic_only`: the only dative of a Spanish unergative is an animate ethical clitic.
* `inchoative_meanings`: an animate dative with an inchoative is affected or experiencer, an
  inanimate one affected alone.
* `rows`: every example's acceptability and reported meaning are as `meanings` predicts.

## Implementation notes

The site is the pair of the heads above and below the applicative, so the three types are the
three ways of cutting a nonempty list. Dative case, clitic doubling and the movement of the
dative to the subject position of unaccusatives (§2.0.5, §3.2.2.1) are not represented, nor are
the sub-types of low applicative beyond the relation read, the resultatives and particles of
§3.3, or the defective applicatives of other languages. The low relation is the verb's, as the
paper takes it to be fixed by the verb's meaning and by pragmatics. Italian is left out, since
the paper attests its double object construction with *arrivare* alone.

## References

* [cuervo-2003]
* [pylkkanen-2008]
* [baker-1996]
-/

namespace Cuervo2003

open Minimalist Data.Examples

/-! ### The merge site of an applicative -/

/-- The site of an applicative head in an event structure: the verbal heads above ApplP and the
heads of its complement, highest first. -/
structure Site where
  above : List LittleV
  below : List LittleV
  deriving DecidableEq, Repr

namespace Site

variable (s : Site)

/-- The event structure the applicative sits in. -/
def heads : List LittleV := s.above ++ s.below

/-- A low applicative: Appl takes the theme DP as its complement, below every verbal head, and
ApplP is the complement of the root. -/
def Low : Prop := s.below = []

/-- A high applicative: ApplP is the complement of no verbal head, Voice or Tense taking it. -/
def High : Prop := s.above = []

/-- An affected applicative: Appl takes a vP as its complement and ApplP is the complement of the
verbal head above, so the dative participates in two events. -/
def Affected : Prop := s.above ≠ [] ∧ s.below ≠ []

instance : DecidablePred Low := fun _ ↦ inferInstanceAs (Decidable (_ = _))
instance : DecidablePred High := fun _ ↦ inferInstanceAs (Decidable (_ = _))
instance : DecidablePred Affected := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- The category of Appl's complement, the theme DP of a low applicative and a vP otherwise
(table (28)). -/
def complement : Cat := if s.below = [] then .D else .v

/-- The verbal head ApplP is the complement of: the lowest head above it, whose root takes
ApplP when the applicative is low; none when it is high. -/
def selector : Option LittleV := s.above.getLast?

theorem complement_eq_D_iff : s.complement = .D ↔ s.Low := by
  simp [complement, Low]

theorem selector_eq_none_iff : s.selector = none ↔ s.High := by
  simp [selector, High]

/-- The three types of table (28) partition the sites in a nonempty structure. -/
theorem low_or_affected_or_high (h : s.heads ≠ []) : s.Low ∨ s.Affected ∨ s.High := by
  by_cases hb : s.below = [] <;> by_cases ha : s.above = [] <;>
    simp_all [heads, Low, Affected, High]

theorem Affected.not_low (h : s.Affected) : ¬ s.Low := h.2

theorem Affected.not_high (h : s.Affected) : ¬ s.High := h.1

/-- An affected dative requires two events. -/
theorem Affected.biEventive (h : s.Affected) : LittleV.BiEventive s.heads := by
  obtain ⟨ha, hb⟩ := h
  unfold LittleV.BiEventive heads
  rw [List.length_append]
  have := List.length_pos_iff.2 ha
  have := List.length_pos_iff.2 hb
  omega

/-- The head an affected applicative is the complement of is dynamic: it embeds the state below
the applicative. -/
theorem Affected.selector_dynamic (hw : LittleV.IsWellFormed s.heads) (h : s.Affected) :
    ∀ v ∈ s.selector, v.Dynamic := by
  intro v hv
  obtain ⟨ha, hb⟩ := h
  rw [selector, Option.mem_def, List.getLast?_eq_some_iff] at hv
  obtain ⟨l, hl⟩ := hv
  obtain ⟨w, t, hb'⟩ := List.exists_cons_of_ne_nil hb
  refine LittleV.Embeds.dynamic (w := w) (List.isChain_pair.1 (hw.2.infix ⟨l, t, ?_⟩))
  simp [heads, hl, hb']

/-- No affected dative is applied under a state, the empty cell of table (40). -/
theorem not_affected_of_state (hw : LittleV.IsWellFormed s.heads)
    (h : s.selector = some .vBE) :
    ¬ s.Affected :=
  fun ha ↦ (ha.selector_dynamic s hw _ h) rfl

end Site

/-- The sites of an applicative in the structure `l`: every cut of the list. -/
def sites (l : List LittleV) : List Site :=
  (List.range (l.length + 1)).map fun i ↦ ⟨l.take i, l.drop i⟩

theorem mem_sites_iff {l : List LittleV} {s : Site} : s ∈ sites l ↔ s.heads = l := by
  constructor
  · intro h
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 h
    exact List.take_append_drop i l
  · rintro rfl
    exact List.mem_map.2 ⟨s.above.length, List.mem_range.2 (by simp [Site.heads]),
      by simp [Site.heads]⟩

/-! ### Meanings (table (40)) -/

/-- The meanings a dative argument can have. -/
inductive Meaning where
  | recipient
  | source
  | possessor
  | affected
  /-- The experiencer of a state or of a change; over a change, also the person unintentionally
  responsible for it (§4.2.3). -/
  | experiencer
  /-- The benefactive or malefactive of an activity, the ethical dative (§4.3.2). -/
  | ethical
  deriving DecidableEq, Repr

/-- The relation a low applicative expresses between the dative and the theme: the dynamic
transfer to a recipient or from a source of [pylkkanen-2008], or the static possession of
Chapter 2's low applicative AT. -/
inductive LowRelation where
  | to
  | from
  | at
  deriving DecidableEq, Repr

def LowRelation.meaning : LowRelation → Meaning
  | .to => .recipient
  | .from => .source
  | .at => .possessor

/-- The meaning of a dative at a site, given the low relation the verb supplies: an individual
related to the theme when low, affected when between two events, and over the whole event the
experiencer of a state or change or the ethical dative of an activity. -/
def Site.meaning (s : Site) (r : LowRelation) : Meaning :=
  match s.above, s.below with
  | _, [] => r.meaning
  | [], v :: _ => if v = .vDO then .ethical else .experiencer
  | _ :: _, _ :: _ => .affected

/-! ### Predicates -/

/-- A verb in one of its uses: the entry, the frame of the use, its event structure, whether a
stative root is predicational, with its argument in the specifier of vBE, and the relation a low
applicative under it expresses. -/
structure Predicate where
  verb : Verb
  frame : ArgumentFrame
  heads : List LittleV
  predicational : Bool := false
  relation : LowRelation := .to

namespace Predicate

variable (p : Predicate)

/-- The theme is the complement of the root, where a low applicative can take it: the root
licenses an object, the structure is simple, since the theme of a complex one is the specifier of
the lower vP (§3.2.2.3), and the state is not predicational (§1.3.3). -/
def ThemeIsRootComplement : Prop :=
  p.frame.HasNominal ∧ ¬ LittleV.BiEventive p.heads ∧ p.predicational = false

instance : Decidable p.ThemeIsRootComplement := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

end Predicate

section Spanish

/-- *mandar* 'send', a directional activity: the low applicative TO, (29a). -/
def mandar : Predicate := ⟨Spanish.Verbs.mandar, .np, [.vDO], false, .to⟩

/-- *preparar* 'fix', a verb of creation: the low applicative TO, (30). -/
def preparar : Predicate := ⟨Spanish.Verbs.preparar, .np, [.vDO], false, .to⟩

/-- *sacar* 'take away', directional away: the low applicative FROM, (31). -/
def sacar : Predicate := ⟨Spanish.Verbs.sacar, .np, [.vDO], false, .from⟩

/-- *lavar* 'wash', a non-directional activity: the low applicative AT, (32). -/
def lavar : Predicate := ⟨Spanish.Verbs.lavar, .np, [.vDO], false, .at⟩

/-- *admirar* 'admire', a transitive state (fn. 4 of Chapter 1): the low applicative AT, (33). -/
def admirar : Predicate := ⟨Spanish.Verbs.admirar, .np, [.vBE], false, .at⟩

/-- *llegar* 'arrive', a simple verb of movement: the low applicative TO, (34). -/
def llegar : Predicate := ⟨Spanish.Verbs.llegar, .unaccusative, [.vGO], false, .to⟩

/-- *salir* 'come out', a simple verb of movement whose dative is the inalienable location of
the theme, (54a). -/
def salir : Predicate := ⟨Spanish.Verbs.salir, .unaccusative, [.vGO], false, .at⟩

/-- *suceder* 'happen', a simple verb of happening, (49). -/
def suceder : Predicate := ⟨Spanish.Verbs.suceder, .unaccusative, [.vGO], false, .at⟩

/-- *sobrar* 'be extra', an existential state whose theme is the complement of the root, (38). -/
def sobrar : Predicate := ⟨Spanish.Verbs.sobrar, .unaccusative, [.vBE], false, .at⟩

/-- *gustar* 'appeal to', a predicational state whose theme is the specifier of vBE, (37). -/
def gustar : Predicate := ⟨Spanish.Verbs.gustar, .unaccusative, [.vBE], true, .at⟩

/-- *romper* 'break' as a causative, (35). -/
def romperCausative : Predicate := ⟨Spanish.Verbs.romper.toVerb, .np, [.vDO, .vBE], false, .at⟩

/-- *romperse* 'break' as an inchoative, (36), (60). -/
def romperInchoative : Predicate :=
  ⟨Spanish.Verbs.romper.toVerb, .unaccusative, [.vGO, .vBE], false, .at⟩

/-- *abrir* 'open' as a causative, (90a). -/
def abrirCausative : Predicate := ⟨Spanish.Verbs.abrir.toVerb, .np, [.vDO, .vBE], false, .at⟩

/-- *abrirse* 'open' as an inchoative, (90b). -/
def abrirInchoative : Predicate :=
  ⟨Spanish.Verbs.abrir.toVerb, .unaccusative, [.vGO, .vBE], false, .at⟩

/-- *quemarse* 'burn' as an inchoative, (55). -/
def quemarInchoative : Predicate :=
  ⟨Spanish.Verbs.quemar.toVerb, .unaccusative, [.vGO, .vBE], false, .at⟩

/-- *caminar* 'walk', an unergative, (39a), (78). -/
def caminar : Predicate := ⟨Spanish.Verbs.caminar, .intransitive, [.vDO], false, .at⟩

/-- *correr* 'run' as an unergative, (66). -/
def correr : Predicate := ⟨Spanish.Verbs.correr, .intransitive, [.vDO], false, .at⟩

/-- *correr una carrera* 'run a race', the transitive use, (67a). -/
def correrTransitive : Predicate := ⟨Spanish.Verbs.correr, .np, [.vDO], false, .at⟩

end Spanish

section English

/-- *pass* as a transitive activity, (85a'). -/
def pass : Predicate := ⟨English.pass.toVerb, .np, [.vDO], false, .to⟩

/-- Causative *open*, (88). -/
def openCausative : Predicate := ⟨English.open_.toVerb, .np, [.vDO, .vBE], false, .to⟩

/-- Inchoative *open*, (89a). -/
def openInchoative : Predicate :=
  ⟨English.open_.toVerb, .unaccusative, [.vGO, .vBE], false, .to⟩

/-- *arrive*, a simple verb of movement, (92b). -/
def arrive : Predicate := ⟨English.arrive.toVerb, .unaccusative, [.vGO], false, .to⟩

end English

/-! ### Inventories of applicative heads -/

/-- A language's applicative heads and their restrictions. -/
structure Inventory where
  /-- Has the affected applicative; English does not (§3.2.3). -/
  affected : Bool
  /-- Has high applicatives; English does not (§4.3). -/
  high : Bool
  /-- The low applicatives it has, by the relation read and the head the root combines with;
  English has the low applicative TO under activities alone (§3.2.3). -/
  low : LowRelation → LittleV → Bool
  /-- The high applicative over an activity projects a specifier; the Spanish one is defective
  and spelled out by a clitic alone (§4.3.2). -/
  ethicalSpecifier : Bool

/-- Spanish has every type, its ethical applicative defective. -/
def spanish : Inventory := ⟨true, true, fun _ _ ↦ true, false⟩

/-- English has the low applicative TO under activities and nothing else. -/
def english : Inventory := ⟨false, false, fun r v ↦ r = .to && v = .vDO, true⟩

/-- A dative argument as the applicative licenses it: its site, whether it is animate and whether
it is a full DP rather than a clitic alone. -/
structure Dative where
  site : Site
  animate : Bool
  fullDP : Bool
  deriving DecidableEq, Repr

/-- The inventory `i` licenses the dative `d` with the predicate `p`: the site is a cut of the
predicate's structure; a low applicative needs the theme as the root's complement and the head
of the language for that relation and structure; an affected one needs the affected head; a high
one needs a high head, an animate dative and, over an activity with a full DP, a specifier. -/
def Inventory.Licenses (i : Inventory) (p : Predicate) (d : Dative) : Prop :=
  d.site ∈ sites p.heads ∧
    (d.site.Low →
      p.ThemeIsRootComplement ∧ ∀ v ∈ p.heads.getLast?, i.low p.relation v = true) ∧
    (d.site.Affected → i.affected = true) ∧
    (d.site.High →
      i.high = true ∧ d.animate = true ∧
        (d.fullDP = true → p.heads.head? = some .vDO → i.ethicalSpecifier = true))

instance (i : Inventory) (p : Predicate) (d : Dative) : Decidable (i.Licenses p d) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- The meanings of a dative of the given animacy and form with `p` in the language `i`: those of
its licensed sites. -/
def meanings (i : Inventory) (p : Predicate) (animate fullDP : Bool) : List Meaning :=
  ((sites p.heads).filter fun s ↦ i.Licenses p ⟨s, animate, fullDP⟩).map
    (·.meaning p.relation)

/-! ### The double object construction and Baker's gap (§3.1, §3.2.3) -/

/-- No low applicative with a complex structure: the theme is the specifier of the lower vP. -/
theorem not_licenses_low_of_biEventive {i : Inventory} {p : Predicate} {d : Dative}
    (hc : LittleV.BiEventive p.heads) (hl : d.site.Low) : ¬ i.Licenses p d :=
  fun h ↦ (h.2.1 hl).1.2.1 hc

/-- With a complex structure a dative is affected or high, so a language without the affected
applicative has only high datives there. -/
theorem licenses_of_biEventive {i : Inventory} {p : Predicate} {d : Dative}
    (hc : LittleV.BiEventive p.heads) (h : i.Licenses p d) : d.site.Affected ∨ d.site.High := by
  have hne : d.site.heads ≠ [] := by
    rw [mem_sites_iff.1 h.1]; exact fun e ↦ by simp [LittleV.BiEventive, e] at hc
  rcases d.site.low_or_affected_or_high hne with hl | ha | hh
  · exact absurd h (not_licenses_low_of_biEventive hc hl)
  · exact .inl ha
  · exact .inr hh

/-- English takes no dative with a causative or an inchoative, lacking affected and high
applicatives, (88), (89). -/
theorem english_not_licenses_of_biEventive {p : Predicate} {d : Dative}
    (hc : LittleV.BiEventive p.heads) : ¬ english.Licenses p d := by
  intro h
  rcases licenses_of_biEventive hc h with ha | hh
  · exact absurd (h.2.2.1 ha) (by decide)
  · exact absurd (h.2.2.2 hh).1 (by decide)

/-- Baker's gap: English takes no dative with a simple verb of change either, its low
applicative being confined to activities, (92). -/
theorem english_not_licenses_change {p : Predicate} {d : Dative} (hp : p.heads = [.vGO]) :
    ¬ english.Licenses p d := by
  intro h
  rcases d.site.low_or_affected_or_high (by rw [mem_sites_iff.1 h.1, hp]; simp) with hl | ha | hh
  · have := (h.2.1 hl).2 .vGO (by simp [hp])
    revert this; cases p.relation <;> decide
  · exact absurd (h.2.2.1 ha) (by decide)
  · exact absurd (h.2.2.2 hh).1 (by decide)

/-- Spanish has the double object construction with a simple verb of change, against Baker's
generalization, (93a). -/
theorem spanish_change_low : spanish.Licenses llegar ⟨⟨[.vGO], []⟩, true, true⟩ := by decide

/-! ### The ethical dative (§4.3) -/

/-- The only dative a Spanish unergative takes is an animate ethical clitic: without an object no
low applicative, without two events no affected one, and the high applicative over an activity
projects no specifier, (66), (74a), (78). -/
theorem unergative_clitic_only {p : Predicate} (hp : p.heads = [.vDO])
    (ho : ¬ p.frame.HasNominal) (d : Dative) :
    spanish.Licenses p d ↔ d = ⟨⟨[], [.vDO]⟩, true, false⟩ := by
  obtain ⟨⟨a, b⟩, an, dp⟩ := d
  simp only [Inventory.Licenses, mem_sites_iff, Site.heads, hp, spanish, Site.Low, Site.High,
    Site.Affected, Predicate.ThemeIsRootComplement, ho, Dative.mk.injEq, Site.mk.injEq]
  rcases a with _ | ⟨v, a⟩ <;> rcases b with _ | ⟨w, b⟩ <;> simp

/-- With an object the same verb takes a low dative DP, (67a). -/
theorem transitive_low_dp :
    spanish.Licenses correrTransitive ⟨⟨[.vDO], []⟩, true, true⟩ := by decide

/-! ### Datives with inchoatives (§4.2.3) -/

/-- An animate dative with an inchoative is affected, between the two events, or the
experiencer unintentionally responsible for the change, above vGO; an inanimate one is affected
alone, (55), (60). -/
theorem inchoative_meanings {p : Predicate} (hp : p.heads = [.vGO, .vBE]) (dp : Bool) :
    meanings spanish p true dp = [.experiencer, .affected] ∧
      meanings spanish p false dp = [.affected] := by
  cases dp <;>
    simp [meanings, hp, sites, List.range_succ, Inventory.Licenses, spanish, LittleV.BiEventive,
      Predicate.ThemeIsRootComplement, Site.Low, Site.High, Site.Affected, Site.meaning]

/-- A dative with a causative is affected alone: the high applicative over an activity licenses
no full DP, (35), (90a). -/
theorem causative_meanings {p : Predicate} (hp : p.heads = [.vDO, .vBE]) :
    meanings spanish p true true = [.affected] := by
  simp [meanings, hp, sites, List.range_succ, Inventory.Licenses, spanish, LittleV.BiEventive,
    Predicate.ThemeIsRootComplement, Site.Low, Site.High, Site.Affected, Site.meaning]

/-! ### The rows -/

/-- The predicate of an example. -/
def predicate? (e : LinguisticExample) : Option Predicate :=
  e.parse? "predicate"
    [("mandar", mandar), ("preparar", preparar), ("sacar", sacar), ("lavar", lavar),
      ("admirar", admirar), ("llegar", llegar), ("salir", salir), ("suceder", suceder),
      ("sobrar", sobrar), ("gustar", gustar), ("romperCausative", romperCausative),
      ("romperInchoative", romperInchoative), ("abrirCausative", abrirCausative),
      ("abrirInchoative", abrirInchoative), ("quemarInchoative", quemarInchoative),
      ("caminar", caminar), ("correr", correr), ("correrTransitive", correrTransitive),
      ("pass", pass), ("openCausative", openCausative), ("openInchoative", openInchoative),
      ("arrive", arrive)]

/-- The inventory of an example's language. -/
def inventory? (e : LinguisticExample) : Option Inventory :=
  List.lookup e.language [("stan1288", spanish), ("stan1293", english)]

/-- The meaning an example reports for its dative. -/
def meaning? (e : LinguisticExample) : Option Meaning :=
  e.parse? "meaning"
    [("recipient", .recipient), ("source", .source), ("possessor", .possessor),
      ("affected", .affected), ("experiencer", .experiencer), ("ethical", .ethical)]

/-- The meanings the model gives an example's dative. -/
def predicted (e : LinguisticExample) : Option (List Meaning) := do
  let i ← inventory? e
  let p ← predicate? e
  let a ← e.parse? "animate" [("yes", true), ("no", false)]
  let f ← e.parse? "dative" [("dp", true), ("clitic", false)]
  return meanings i p a f

/-- Every example is acceptable exactly when its dative has a licensed site, and the meaning
the paper reports is among those licensed; where the paper reports an unintentional
responsibility reading, it is the high applicative's experiencer reading. -/
theorem rows : ∀ e ∈ Examples.all, ∃ ms ∈ predicted e,
    (.marginal ≤ e.judgment ↔ ms ≠ []) ∧ (∀ m ∈ meaning? e, m ∈ ms) ∧
      ∀ j ∈ e.readings.lookup "unintentional responsibility",
        (.marginal ≤ j ↔ .experiencer ∈ ms) := by
  decide +kernel

end Cuervo2003
