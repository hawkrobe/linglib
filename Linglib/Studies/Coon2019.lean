import Linglib.Semantics.Root.Defs
import Linglib.Syntax.Minimalist.Verbal.Voice
import Linglib.Fragments.Mayan.Chuj.RootClasses
import Linglib.Fragments.Mayan.Chuj.VoiceSystem
import Linglib.Data.Examples.Coon2019
import Mathlib.Tactic.DeriveFintype

/-!
# Coon 2019: building verbs in Chuj

[coon-2019] argues from the Chuj verb stem that the root decides whether there is an internal
argument and the functional head v ~ Voice⁰ decides the rest. Roots fall into four classes
that semantic type partly distinguishes, transitive and intransitive roots being event
predicates over an entity, positional roots measure functions and nominal roots properties, and
a verb stem is a root plus one of the heads Ø, -w, -ch and -j, the first doubling as the null
head of intransitive roots, which merge an agent with inherent ergative case, an agent without
it, an implicit agent, or no agent. Since finite Infl⁰ licenses one absolutive
argument, an agent without ergative case takes it, so a transitive root under -w cannot realize
its argument as a full DP and does so as a bare NP composed by Restrict or as an implicit
argument bound by Existential Closure, the suffix -aj being the overt reflex of that binding in
absolutive antipassives and in passives with an implicit agent, while an intransitive root,
whose sole argument is a DP, admits no -w at all. Every stem of a transitive root thus composes
with an internal argument, and a language without the head that merges an agent free of
ergative case, Ch'ol, has no agentive intransitive stems.

## Implementation notes

The heads are Minimalist Voice heads whose parametric semantics supplies the three properties
the licensing count reads, an external argument, its implicitness, and inherent ergative case
recorded as Case checking, and the count adopts the Obligatory Case Parameter of footnote 15,
one of the two options the paper leaves open. The class of a root fixes which realizations its
internal slot admits; that an intransitive root's argument is only ever a full DP encodes the
absence of unaccusative subject incorporation, (48), which the paper leaves to typology, and no
implicit option for such roots is attested. The event semantics of §3.2.2 records truth
conditions; the locus of Existential Closure that separates the two antipassives lives in the
-aj predicate. Status suffixes, derived transitives in -ej, word order, stative -an stems, the
inanimate causer of (70a) and the isolated -j form (71) are recorded as data only.

## References

* [J. Coon, *Building verbs in Chuj: Consequences for the nature of roots* (2019)][coon-2019]
* [S. Chung and W. A. Ladusaw, *Restriction and Saturation* (2004)][chung-ladusaw-2004]
* [M. Diesing, *Indefinites* (1992)][diesing-1992]
* [H. Harley, *The 'bundling' hypothesis and the disparate functions of little v*
  (2017)][harley-2017]
* [A. Kratzer, *Severing the external argument from its verb* (1996)][kratzer-1996]
* [H. Davis, *Deep unaccusativity and zero syntax in St'át'imcets* (1997)][davis-1997]
* [R. Henderson, *The roots of measurement* (2017)][henderson-2017]
* [J. M. Maxwell, *Chuj intransitives: Or when can an intransitive verb take an object?*
  (1976)][maxwell-1976]
* [A. Alexiadou, E. Anagnostopoulou and F. Schäfer, *The properties of anticausatives
  crosslinguistically* (2006)][alexiadou-anagnostopoulou-schaefer-2006]
* [J. Wood, *Icelandic Morphosyntax and Argument Structure* (2015)][wood-2015]
-/

namespace Coon2019

open Chuj Minimalist.Voice Data.Examples ArgumentStructure

/-! ### Root classes -/

/-- [coon-2019]'s coordinates for the four root classes, (3) and §3.3: transitive and
intransitive roots are event predicates over an internal argument, only the former compatible
with the agent-merging Voice head; positional roots are measure functions after
[henderson-2017] and nominal roots properties, neither selecting an internal argument in the
sense of (2). -/
def _root_.Chuj.RootClass.toRoot : RootClass → Semantics.Root
  | .tv =>
    { valency := some {.internal}, denotationType := some (.e ⇒ .s ⇒ .t),
      licensesTransitiveVoice := true }
  | .itv => { valency := some {.internal}, denotationType := some (.e ⇒ .s ⇒ .t) }
  | .pos => { valency := some ∅, denotationType := some (.e ⇒ .s ⇒ .d) }
  | .nom => { valency := some ∅, denotationType := some (.e ⇒ .t) }

/-- √TV and √ITV share type and valency, after [davis-1997]; compatibility with external
causation by an agent alone separates them, §3.3. -/
theorem tv_itv_differ_only_in_voice :
    RootClass.tv.toRoot.denotationType = RootClass.itv.toRoot.denotationType ∧
      RootClass.tv.toRoot.valency = RootClass.itv.toRoot.valency ∧
      RootClass.tv.toRoot.licensesTransitiveVoice ≠
        RootClass.itv.toRoot.licensesTransitiveVoice :=
  ⟨rfl, rfl, by decide⟩

/-! ### The v ~ Voice⁰ heads -/

/-- The v ~ Voice⁰ heads of the verb stem, (6) and (78): the transitive Ø, the null intransitive
head of §2.1, and the suffixes -w, -ch and -j. -/
inductive V
  | transitive | intransitive | w | ch | j
  deriving DecidableEq, Fintype, Repr

/-- The exponent of each head, the Ø slot shared by the two null heads. -/
def V.exponent : V → VoiceSuffix
  | .transitive | .intransitive => .null
  | .w => .w
  | .ch => .ch
  | .j => .j

/-- The Minimalist Voice head each realizes, a bundled v ~ Voice⁰ after [harley-2017]
introducing the external argument as in [kratzer-1996] and specified for whether and what it
introduces as in [alexiadou-anagnostopoulou-schaefer-2006] and [wood-2015]: the transitive
head and -w both merge an agent, footnote 10, the former assigning it inherent ergative case,
recorded as Case checking; -ch merges an implicit, existentially bound agent in its specifier,
(64), the impersonal cell with a specifier; -j and the null intransitive head introduce no
external argument and project no specifier, (68), the expletive cell. -/
def V.head : V → Head
  | .transitive => { flavor := .agentive, hasD := true, checksCase := true }
  | .intransitive => { flavor := .expletive, hasD := false }
  | .w => { flavor := .agentive, hasD := true }
  | .ch => { flavor := .impersonal, hasD := true }
  | .j => { flavor := .expletive, hasD := false }

/-- The two agent-introducing heads differ in inherent ergative case alone, footnote 10. -/
theorem w_head_eq : V.w.head = { V.transitive.head with checksCase := false } := rfl

/-- Every head keeps its [D] feature in step with its cell except -ch, whose specifier hosts
the implicit agent of (64) that the impersonal cell leaves specifierless. -/
theorem dCoherent : (∀ v : V, v ≠ .ch → v.head.DCoherent) ∧ ¬ V.ch.head.DCoherent :=
  ⟨λ v => by cases v <;> decide, by decide⟩

/-- The head properties behind (78), read off the substrate cells: every head but -j and the
null intransitive head introduces an external argument, -ch alone an implicit one, the
transitive head alone assigns inherent ergative case, recorded as Case checking. -/
theorem head_table :
    (∀ v : V, v.head.IntroducesExternal ↔ v ≠ .intransitive ∧ v ≠ .j) ∧
      (∀ v : V, v.head.ExternalImplicit ↔ v = .ch) ∧
      ∀ v : V, v.head.ChecksCase ↔ v = .transitive := by
  refine ⟨?_, ?_, ?_⟩ <;> intro v <;> cases v <;> decide

/-! ### Licensing -/

/-- How the internal argument slot of a root is realized, (56) and (78): a full DP saturating
it, a bare NP restricting it, an implicit argument saturating it as a variable to be bound, or
no slot. -/
inductive Internal
  | dp | np | implicit | absent
  deriving DecidableEq, Fintype, Repr

/-- The realizations a root class admits: a transitive root composes with its argument in every
stem, §5; nominal and positional roots select nothing, (39); an intransitive root's argument is
a full DP, a coordinate stipulated here, since nothing in the analysis rules out (48b) and the
paper leaves the absence of unaccusative subject incorporation to typology, while no implicit
option for such roots is attested. -/
def internals : RootClass → List Internal
  | .tv => [.dp, .np, .implicit]
  | .itv => [.dp]
  | .pos | .nom => [.absent]

/-- The licenser of an argument, (78). -/
inductive Licenser
  | voice | infl | unlicensed
  deriving DecidableEq, Repr

/-- Who licenses each argument position of a stem, §3.2.1 and §3.2.2: the head cases its own
specifier when it assigns inherent ergative, finite Infl⁰ cases a DP the head does not, and a
bare NP, an implicit argument and an absent one need no case. -/
def licenser (v : V) (i : Internal) : ArgPosition → Licenser
  | .external =>
    if v.head.IntroducesExternal ∧ ¬ v.head.ExternalImplicit then
      (if v.head.ChecksCase then .voice else .infl) else .unlicensed
  | .internal => if i = .dp then .infl else .unlicensed

/-- A stem is licensed when Infl⁰ has exactly one argument to license: it licenses one
absolutive argument, and must license one, the Obligatory Case Parameter that footnote 15
offers beside an economy condition to keep the transitive head off stems whose only DP it would
case itself. -/
def Licensed (v : V) (i : Internal) : Prop :=
  (Finset.univ.filter λ a => licenser v i a = .infl).card = 1

instance (v : V) (i : Internal) : Decidable (Licensed v i) := by unfold Licensed; infer_instance

/-- The selection each head imposes on the root, (78) and §2.1: the transitive head and the
passive -ch need a root whose event admits an external agent, and so does -j apart from
isolated forms like (71); the null intransitive head needs an unaccusative root; -w needs only
a root, its ban on intransitive roots following from licensing rather than selection, §3.3. -/
def V.Selects : V → Semantics.Root → Prop
  | .transitive, r | .ch, r | .j, r => r.licensesTransitiveVoice = true
  | .intransitive, r => r.valency = some {.internal} ∧ r.licensesTransitiveVoice = false
  | .w, _ => True

instance (v : V) (r : Semantics.Root) : Decidable (v.Selects r) := by
  cases v <;> simp only [V.Selects] <;> infer_instance

/-- A well-formed stem from a root class: the head selects the root, the root admits the
realization, and the arguments are licensed. -/
def WellFormed (rc : RootClass) (v : V) (i : Internal) : Prop :=
  v.Selects rc.toRoot ∧ i ∈ internals rc ∧ Licensed v i

instance (rc : RootClass) (v : V) (i : Internal) : Decidable (WellFormed rc v i) := by
  unfold WellFormed; infer_instance

/-- A root class forms a stem with one of the suffixes Ø, -w, -ch and -j when some head with
that exponent is well-formed on it under some realization; stems with other derivational
suffixes, (11) and (15), are not in view. -/
def IsGrammatical (rc : RootClass) (vs : VoiceSuffix) : Prop :=
  ∃ v : V, v.exponent = vs ∧ ∃ i, WellFormed rc v i

instance (rc : RootClass) (vs : VoiceSuffix) : Decidable (IsGrammatical rc vs) := by
  unfold IsGrammatical; infer_instance

/-- The distribution of the four heads over the root classes, derived: √TV takes all four,
(45) and (59) to (60); √ITV only Ø, (47); √POS and √NOM only -w, (45), apart from isolated forms
like (71). -/
theorem isGrammatical_iff :
    (∀ vs, IsGrammatical .tv vs) ∧ (∀ vs, IsGrammatical .itv vs ↔ vs = .null) ∧
      (∀ vs, IsGrammatical .pos vs ↔ vs = .w) ∧ ∀ vs, IsGrammatical .nom vs ↔ vs = .w := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro vs <;> cases vs <;> decide

/-- The stems of a transitive root, (78) and (79): a full DP under the transitive head and under
both passives, a bare NP or an implicit argument under -w. -/
theorem tv_stems :
    Finset.univ.filter (λ p : V × Internal => WellFormed .tv p.1 p.2) =
      {(.transitive, .dp), (.ch, .dp), (.j, .dp), (.w, .np), (.w, .implicit)} := by
  decide

/-- No stem of -w has a full DP internal argument, (37): Infl⁰ is taken by the agent. -/
theorem w_no_dp (rc : RootClass) : ¬ WellFormed rc .w .dp := by
  cases rc <;> decide

/-- A transitive root under -w requires its complement, (38), and a nominal root rejects one,
(39): the difference lies in the root. -/
theorem w_complement : ¬ WellFormed .tv .w .absent ∧ ¬ WellFormed .nom .w .np := by decide

/-- No -w on an intransitive root, (47): with the agent on Infl⁰ the root's DP argument goes
unlicensed, §3.3, a consequence of licensing rather than selection, given that the argument is a
DP. -/
theorem itv_no_w : (∀ i, ¬ WellFormed .itv .w i) ∧ V.w.Selects RootClass.itv.toRoot :=
  ⟨λ i => by cases i <;> decide, trivial⟩

/-- Every class forms a verb stem with some head, §5: root class is not surface category. -/
theorem every_class_verbalizes (rc : RootClass) : ∃ vs, IsGrammatical rc vs := by
  cases rc
  exacts [⟨.null, by decide⟩, ⟨.null, by decide⟩, ⟨.w, by decide⟩, ⟨.w, by decide⟩]

/-- Table (78) for the stems of a transitive root: the external argument licensed by
v ~ Voice⁰ in the transitive, absent or implicit in the passives, licensed by Infl⁰ under -w;
the internal argument licensed by Infl⁰ except under -w. -/
theorem licenser_table :
    licenser .transitive .dp .external = .voice ∧ licenser .transitive .dp .internal = .infl ∧
      licenser .ch .dp .external = .unlicensed ∧ licenser .j .dp .external = .unlicensed ∧
      licenser .w .np .external = .infl ∧ licenser .w .np .internal = .unlicensed ∧
      licenser .w .implicit .internal = .unlicensed := by
  decide

/-- An agentive intransitive stem: an overt external argument licensed by Infl⁰, hence a single
absolutive argument, §3. -/
def AgentiveIntransitive (v : V) (i : Internal) : Prop :=
  licenser v i .external = .infl ∧ Licensed v i

instance (v : V) (i : Internal) : Decidable (AgentiveIntransitive v i) := by
  unfold AgentiveIntransitive; infer_instance

/-- Only -w forms agentive intransitive stems, (49), the head that merges an agent without
ergative case. A language lacking it, Ch'ol, has no agentive intransitive verb stems and forms
its unergatives and antipassives on nominal stems under a light verb, §3.4.2. -/
theorem agentiveIntransitive_iff (v : V) (i : Internal) :
    AgentiveIntransitive v i ↔ v = .w ∧ i ≠ .dp := by
  cases v <;> cases i <;> decide

/-! ### Implicit arguments and -aj -/

/-- The implicit arguments of a stem: the existentially bound agent of -ch and the implicit
internal argument of the absolutive antipassive. -/
def Implicit (v : V) (i : Internal) : ArgPosition → Prop
  | .external => v.head.ExternalImplicit
  | .internal => i = .implicit

/-- The suffix -aj, an overt reflex of Existential Closure ([diesing-1992]) binding an implicit
argument above v ~ VoiceP, §4.2: present exactly when the stem has one. -/
def Aj (v : V) (i : Internal) : Prop := ∃ a, Implicit v i a

instance (v : V) (i : Internal) (a : ArgPosition) : Decidable (Implicit v i a) := by
  cases a <;> simp only [Implicit] <;> infer_instance

instance (v : V) (i : Internal) : Decidable (Aj v i) := by unfold Aj; infer_instance

/-- Table (58): -aj on the -chaj passive and the -waj absolutive antipassive, on neither the -j
passive, whose agent is absent, nor the incorporation antipassive, whose argument is bound at
once, footnote 28. -/
theorem aj_table :
    Aj .ch .dp ∧ Aj .w .implicit ∧ ¬ Aj .j .dp ∧ ¬ Aj .w .np ∧ ¬ Aj .transitive .dp := by
  decide

/-! ### Agent diagnostics -/

/-- The reading of an oblique -uj phrase adjoined to a passive: the agent when the head has an
implicit agent to identify, (62) and (66a); otherwise a cause of any kind, an agent not
excluded but not required, (65) and (66b). -/
inductive ObliqueReading
  | agent | cause
  deriving DecidableEq, Repr

/-- The reading of the -uj phrase under each head. -/
def V.obliqueReading (v : V) : ObliqueReading :=
  if v.head.ExternalImplicit then .agent else .cause

/-- Agent-oriented adverbs and purpose clauses need an agent, overt or implicit, §4.1: -ch
admits them and reads its oblique as the agent, (62) and (63); -j rejects them and reads its
oblique as a cause, (65) and (67). -/
theorem passive_contrast :
    V.ch.head.IntroducesExternal ∧ ¬ V.j.head.IntroducesExternal ∧
      V.obliqueReading .ch = .agent ∧ V.obliqueReading .j = .cause := by
  decide

/-! ### Composing the internal argument -/

section Semantics

variable {E S : Type*} (P : E → S → Prop) (Q : E → Prop) (a : E)

/-- Restrict, footnote 19 after [chung-ladusaw-2004]: a property complement narrows the root
without saturating its argument, (44b). -/
def restrict : E → S → Prop := λ x e => P x e ∧ Q x

/-- Existential Closure, footnote 19 after [chung-ladusaw-2004]: the open argument is bound at
the event level, (44c). -/
def close : S → Prop := λ e => ∃ x, P x e

/-- The transitive stem, (43): the DP saturates the root by Functional Application. -/
def transitiveStem : S → Prop := P a

/-- The incorporation antipassive, (44): the bare NP restricts the root and Existential Closure
applies at once, so nothing is left open above v ~ VoiceP, footnote 28. -/
def incorporationStem : S → Prop := close (restrict P Q)

/-- The absolutive antipassive, (75): the implicit argument saturates the root as a variable
that the closure -aj spells out binds; the truth conditions coincide with closing at the root,
the difference of locus that footnote 28 draws being what `aj` records. -/
def absolutiveStem : S → Prop := close P

/-- Every stem of a transitive root composes with an internal argument, §5: each describes
events in which the root relation holds of some entity, so the transitive and incorporation
stems entail the absolutive one, a corollary the paper does not draw. -/
theorem stems_close :
    (∀ e, transitiveStem P a e → absolutiveStem P e) ∧
      ∀ e, incorporationStem P Q e → absolutiveStem P e :=
  ⟨λ _ h => ⟨a, h⟩, λ _ ⟨x, h, _⟩ => ⟨x, h⟩⟩

end Semantics

/-! ### The rows -/

/-- The root of a row, from the fragment lexicon by its form. -/
def rowRoot (row : LinguisticExample) : Option ChujRoot :=
  row.feature? "rootForm" >>= λ f => allRoots.find? (·.form == f)

private def heads : List (String × V) :=
  [("transitive", .transitive), ("intransitive", .intransitive), ("w", .w), ("ch", .ch),
    ("j", .j)]

/-- A stem row: the root class, the head, the realization of the internal slot, and whether
-aj appears. -/
structure Stem where
  /-- The root class. -/
  root : RootClass
  /-- The head. -/
  head : V
  /-- The realization of the internal slot. -/
  internal : Internal
  /-- Whether -aj appears. -/
  hasAj : Bool

/-- The stem a row records. -/
def Stem.ofRow (row : LinguisticExample) : Option Stem := do
  guard (row.feature? "construction" = some "stem")
  return ⟨(← rowRoot row).class', ← row.parse? "head" heads,
    ← row.parse? "internal"
      [("dp", Internal.dp), ("np", .np), ("implicit", .implicit), ("none", .absent)],
    ← row.parse? "aj" [("yes", true), ("no", false)]⟩

/-- The stems of §2 to §4 and (79): a row is grammatical exactly when its stem is well-formed,
and a grammatical row bears -aj exactly when its stem has an implicit argument. -/
theorem stem_rows : ∀ row ∈ Examples.all, row.feature? "construction" = some "stem" →
    ∃ s ∈ Stem.ofRow row,
      (row.judgment ≠ .ungrammatical ↔ WellFormed s.root s.head s.internal) ∧
        (row.judgment ≠ .ungrammatical → (s.hasAj = true ↔ Aj s.head s.internal)) := by
  decide

/-- The head a diagnostic row tests. -/
def diagnosticHead (row : LinguisticExample) : Option V := do
  guard (row.feature? "construction" = some "diagnostic")
  row.parse? "head" heads

/-- (63) and (67): agent-oriented adverbs and purpose clauses are admitted exactly under a head
with an agent. -/
theorem diagnostic_rows : ∀ row ∈ Examples.all,
    row.feature? "construction" = some "diagnostic" →
    ∃ v ∈ diagnosticHead row, (row.judgment ≠ .ungrammatical ↔ v.head.IntroducesExternal) := by
  decide

/-- The head and the recorded reading of an oblique row. -/
def obliqueRow (row : LinguisticExample) : Option (V × ObliqueReading) := do
  guard (row.feature? "oblique").isSome
  return (← row.parse? "head" heads,
    ← row.parse? "oblique" [("agent", ObliqueReading.agent), ("cause", .cause)])

/-- (62), (65), (66), (70) and (73): the -uj phrase names the agent under -ch and a cause under
-j. -/
theorem oblique_rows : ∀ row ∈ Examples.all, (row.feature? "oblique").isSome = true →
    ∃ p ∈ obliqueRow row, p.2 = p.1.obliqueReading := by
  decide

end Coon2019
