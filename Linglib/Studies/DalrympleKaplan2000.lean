import Linglib.Core.Order.Flat
import Linglib.Morphology.Unification
import Linglib.Features.Case.Basic
import Linglib.Features.Person.Decomposition
import Linglib.Features.Person.Resolve
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Basic

/-!
# Dalrymple & Kaplan 2000: Feature Indeterminacy and Feature Resolution
[dalrymple-kaplan-2000]

Set-valued syntactic features, against atomic-value-plus-equality. Two phenomena, one
representational move (§4, eq. 25: "Sets encode indeterminate feature possibilities"):

* **Indeterminacy** (distributive features: case, noun class, vform): a syncretic form
  bears a *set* of atomic values — German *was* `{NOM, ACC}` — and contextual
  requirements are *membership* assertions (`ACC ∈ (↑ OBJ CASE)`), not equalities. The
  paper refutes the two obvious alternatives: disjunctive specification DNF-collapses
  into a homophone listing (§3.1), and underspecification both derives `NOM = ACC` by
  transitivity of equality and overgenerates dative contexts (§3.2).
* **Resolution** (nondistributive features: person, gender): a coordinate phrase's
  person/gender is the **union** of its conjuncts' marker sets (§6, §7) — person values
  are subsets of `{S, H}` (`{S}` 1exc, `{S,H}` 1inc, `{H}` 2nd, `{}` 3rd), and the
  union analysis predicts the full Fula paradigm (87–88), the collapsed
  English/Spanish/Slovak system (91–92), and the gender tables of Hindi (112),
  Icelandic (120), and Slovene with the conjunction contributing `F` (126–127).

The deliberate sharp line (§8): *resolving* features are never indeterminate —
Hindi *wah* is masc-or-fem by wide-scope **disjunction** (ambiguity), not by a set
value, which is why `*wah arrived.MASC and arrived.FEM` fails (128).

This is the flagship counterexample to treating the flat information order
(`Morphology/Unification.lean`) as linguistically definitional: indeterminate
agreement is an *annotation-level* phenomenon demanding non-flat (set-valued) slots.
`toIndet` below certifies the relationship — the flat order embeds into the
(superset-ordered) indeterminacy lattice as the determinate fragment, with `⊥`
(no information) mapping to the universal set.

Formal highlights replicated as theorems: the German/Polish contrast set
((17)/(28) vs (32); (40) vs (41)), the §3 refutations, verb-side indeterminacy
(Xhosa (56), Chicheŵa (59), German *kaufen* (62)), the resolution tables, the
minimal-model derivation of *José y tu* (96–97), the Sag-et-al intersection
refutation (§6.5, (100)–(101) vs Fula), and the De Morgan duality (102–103) — which
is mathlib's `Finset.compl_union`. The person-marker sets also project onto the
binary person decomposition of `Features/Person.lean`, with the inclusive/exclusive
collapse made explicit.
-/

namespace DalrympleKaplan2000


/-! ### §4: indeterminate values are sets; checking is membership -/

/-- An indeterminate feature value: the set of atomic values the form can realize
    (eq. 25). Singleton = determinate. -/
abbrev IndetVal (α : Type*) := Finset α

/-- Contextual requirement (eq. 27): the required atom is a member of the value set. -/
abbrev requires {α : Type*} [DecidableEq α] (c : α) (v : IndetVal α) : Prop := c ∈ v

/-- German relative pronouns (26): *wer* nominative, *was* syncretic, *wem* dative. -/
def wer : IndetVal Case := {Case.nom}
def was : IndetVal Case := {Case.nom, Case.acc}
def wem : IndetVal Case := {Case.dat}

/-- (17)/(28): *Ich habe gegessen was übrig war* — *was* satisfies the matrix verb's
    accusative requirement and the relative clause's nominative requirement at once. -/
theorem was_satisfies_both : requires Case.acc was ∧ requires Case.nom was := by
  constructor <;> decide

/-- (32): `*Wem du vertraust muss klug sein` — *wem* `{DAT}` satisfies *vertraut* but
    not the matrix `NOM ∈` requirement. -/
theorem wem_fails_matrix : requires Case.dat wem ∧ ¬ requires Case.nom wem := by
  constructor <;> decide

/-- Polish (40)/(41): *kogo* `{ACC, GEN}` survives coordination of an ACC-taking and a
    GEN-taking verb; *co* `{NOM, ACC}` does not. -/
def kogo : IndetVal Case := {Case.acc, Case.gen}
def co : IndetVal Case := {Case.nom, Case.acc}

theorem kogo_grammatical : requires Case.acc kogo ∧ requires Case.gen kogo := by
  constructor <;> decide

theorem co_ungrammatical : requires Case.acc co ∧ ¬ requires Case.gen co := by
  constructor <;> decide

/-! ### §3: why the rival accounts fail -/

/-- An atomic-value account: one case value checked by equality against every
    requirement. -/
def atomicSatisfies (x : Case) (reqs : List Case) : Prop := ∀ r ∈ reqs, x = r

private theorem not_atomicSatisfies_acc_nom (x : Case) :
    ¬ atomicSatisfies x [Case.acc, Case.nom] := fun h =>
  absurd ((h Case.acc (by simp)) ▸ (h Case.nom (by simp))) (by decide)

/-- §3.2 (eq. 24): no single atomic value satisfies both verbs of (17) — transitivity
    of equality would force `NOM = ACC`. -/
theorem underspecification_fails : ¬ ∃ x : Case, atomicSatisfies x [Case.acc, Case.nom] :=
  fun ⟨x, h⟩ => not_atomicSatisfies_acc_nom x h

/-- §3.1 (18)–(21): disjunctive specification means *choosing* one disjunct per
    utterance — and every choice from `{NOM, ACC}` fails one of the two requirements.
    The set-based account (`was_satisfies_both`) succeeds where every disjunctive
    resolution fails: that contrast is the paper's argument. -/
theorem disjunction_collapses :
    ∀ x ∈ was, ¬ atomicSatisfies x [Case.acc, Case.nom] :=
  fun x _ => not_atomicSatisfies_acc_nom x

/-! ### §4.4: indeterminate *requirements* (verb-side sets) -/

/-- Xhosa (54)–(56): *zibomvu* requires its subject's noun class to be in `{7/8, 9/10}`
    (classes as their singular-class numbers), so class-7/8 *izandla* and class-9/10
    *neendlebe* conjuncts each satisfy it. -/
theorem xhosa_zibomvu : (7 : ℕ) ∈ ({7, 9} : Finset ℕ) ∧ (9 : ℕ) ∈ ({7, 9} : Finset ℕ) := by
  constructor <;> decide

/-- German (60)–(63): *kaufen* imposes `(↑ SUBJ PERSON) ∈ {1, 3}`; right-node raising
    over a 1-person and a 3-person subject satisfies the requirement in each conjunct. -/
def kaufenReq : IndetVal UD.Person := {UD.Person.first, UD.Person.third}

theorem kaufen_rnr :
    requires UD.Person.first kaufenReq ∧ requires UD.Person.third kaufenReq ∧
      ¬ requires UD.Person.second kaufenReq := by
  refine ⟨by decide, by decide, by decide⟩

/-! ### The refinement certificate: the flat order is the determinate fragment

`Morphology/Unification.lean`'s flat slot order embeds into the indeterminacy
lattice: a determinate commitment `↑x` is the singleton `{x}`, and *no
information* (`⊥`) is the universal set (any realization possible). Information
increases as sets *shrink*, so the embedding is order-reversing into `⊆` — i.e. an
embedding into the superset order. Set-valued slots are a refinement of the flat
layer, not a rival to it. -/

/-- A flat slot as an indeterminate value: `⊥` = no commitment = anything goes. -/
def toIndet : Flat Case → IndetVal Case
  | ⊥ => Finset.univ
  | (x : Case) => {x}

private theorem univ_ne_singleton (y : Case) : (Finset.univ : Finset Case) ≠ {y} := by
  intro h
  have hc : (Finset.univ : Finset Case).card = 1 := by rw [h, Finset.card_singleton]
  rw [Finset.card_univ] at hc
  exact absurd hc (by decide)

theorem toIndet_injective : Function.Injective toIndet := by
  intro a b h
  match a, b with
  | ⊥, ⊥ => rfl
  | ⊥, (y : Case) => exact absurd h (univ_ne_singleton y)
  | (x : Case), ⊥ => exact absurd h.symm (univ_ne_singleton x)
  | (x : Case), (y : Case) =>
    simp only [toIndet, Finset.singleton_inj] at h
    exact Flat.coe_inj.mpr h

/-- The embedding certificate: flat subsumption is superset inclusion of realization
    sets. More committed = smaller set; `⊥` sits below everything because `univ`
    contains everything. -/
theorem le_iff_toIndet_superset (a b : Flat Case) :
    a ≤ b ↔ toIndet b ⊆ toIndet a := by
  cases a with
  | bot => exact iff_of_true bot_le (Finset.subset_univ _)
  | coe x =>
    cases b with
    | bot =>
      refine iff_of_false (Flat.not_coe_le_bot x) fun h => ?_
      exact univ_ne_singleton x (Finset.Subset.antisymm h (Finset.subset_univ _))
    | coe z => simp [toIndet, eq_comm]

/-! ### §§5–6: feature resolution — person as marker sets, resolution as union -/

/-- The person markers (§6): `S` speaker, `H` hearer. §6.3 argues no third marker is
    attested (Sierra Popoluca's "limited inclusive" is an inclusive dual, per Noyer). -/
inductive Marker where
  | S
  | H
  deriving DecidableEq, Repr, Fintype

abbrev PersonSet := Finset Marker

/-- Fula's four-way system (87): full use of the marker inventory. -/
def fula1exc : PersonSet := {Marker.S}
def fula1inc : PersonSet := {Marker.S, Marker.H}
def fula2 : PersonSet := {Marker.H}
def fula3 : PersonSet := (∅ : Finset Marker)

/-- Resolution is union (77, 93): "the person feature of a coordinate structure is
    resolved to be the UNION of the person features of the conjuncts". -/
def resolve (p q : PersonSet) : PersonSet := p ∪ q

/-- The Fula resolution table (78)/(88), in full. -/
theorem fula_table :
    resolve fula1exc fula2 = fula1inc ∧
    resolve (resolve fula1exc fula2) fula3 = fula1inc ∧
    resolve fula1exc fula3 = fula1exc ∧
    resolve fula2 fula3 = fula2 ∧
    resolve fula3 fula3 = fula3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- English/Spanish/Slovak collapse the inclusive/exclusive distinction (§6.2): all
    first person is `{S, H}` — preserving only attested syntactic distinctions at the
    cost of the referential correlation (Aronoff's impersonal *you*, French *on*). -/
def eng1 : PersonSet := {Marker.S, Marker.H}
def eng2 : PersonSet := {Marker.H}
def eng3 : PersonSet := (∅ : Finset Marker)

/-- The collapsed-system resolution table (91)/(92). -/
theorem english_table :
    resolve eng1 eng2 = eng1 ∧ resolve eng1 eng3 = eng1 ∧
    resolve eng2 eng3 = eng2 ∧ resolve eng3 eng3 = eng3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- *José y tu habláis* (95)–(99): the resolved person of `3 ∪ 2` is `{H}` — the
    minimal model — so the 2PL verb's constraining equation `=c {H}` succeeds and the
    1PL verb's `=c {S,H}` fails. -/
theorem jose_y_tu :
    resolve eng3 eng2 = eng2 ∧ resolve eng3 eng2 ≠ eng1 := by
  constructor <;> decide

/-! ### The substrate bridge: `Person.resolve` is marker-set union -/

/-- The marker sets of the canonical quadripartition values — the Fula
    encoding (87). Plain `first` underdetermines clusivity (their §6.2
    English collapse picks `{S, H}` by stipulation), and `zero` is
    outside the system, so both map to `none`. -/
def markerSetOf : Person → Option PersonSet
  | .firstExclusive => some fula1exc
  | .firstInclusive => some fula1inc
  | .second => some fula2
  | .third => some fula3
  | _ => none

/-- The substrate's canonical resolution is the paper's union (77)/(93):
    on the quadripartition, `Person.resolve` commutes with the marker
    encoding — the same grounding `Person.resolve_profile` states
    intrinsically, here in the paper's own vocabulary. -/
theorem person_resolve_is_union :
    ∀ p q : Person, ∀ sp sq : PersonSet,
      markerSetOf p = some sp → markerSetOf q = some sq →
      markerSetOf (Person.resolve p q) = some (resolve sp sq) := by
  decide

/-- Two markers bound the system (§6.3): at most four person values are expressible,
    matching the maximally differentiated (Fula-type) inventory. -/
theorem two_markers_four_persons : Fintype.card PersonSet = 4 := by
  rw [Fintype.card_finset]
  rfl

/-! ### §6.5: union vs intersection — Sag et al. refuted, De Morgan vindicated -/

/-- Sag et al. 1985's marker sets (100): first = `{}`, second = `{XSP}`,
    third = `{XSP, THP}`, resolution by *intersection*. Reusing our two markers for
    their two. -/
def sag1 : PersonSet := (∅ : Finset Marker)
def sag2 : PersonSet := {Marker.S}
def sag3 : PersonSet := {Marker.S, Marker.H}

/-- The refutation (§6.5): with first person as `∅`, intersection makes *you and I*
    and *Bill and I* indistinguishable — "it is in principle impossible to distinguish
    different kinds of coordination involving a first person pronoun", so Fula's
    inclusive/exclusive contrast is underivable. Union keeps them apart. -/
theorem sag_intersection_fails :
    sag1 ∩ sag2 = sag1 ∩ sag3 ∧ resolve fula1exc fula2 ≠ resolve fula1exc fula3 := by
  constructor <;> decide

/-- The De Morgan duality (102)–(103): any union analysis transforms into an
    equivalent intersection analysis over complement sets (markers reread as
    *absences*). The paper's observation is mathlib's `Finset.compl_union`. -/
theorem union_intersection_duality (p q : PersonSet) : (p ∪ q)ᶜ = pᶜ ∩ qᶜ :=
  Finset.compl_union p q

/-! ### §7: gender resolution by the same mechanism -/

/-- Gender markers; per-language assignments below reuse one inventory. -/
inductive GMark where
  | M
  | F
  | N
  deriving DecidableEq, Repr, Fintype

abbrev GenderSet := Finset GMark

/-- Hindi (111): two genders, masculine `{M}`, feminine `{}` — mixed coordination
    resolves masculine (112). -/
theorem hindi_table :
    (({GMark.M} : GenderSet) ∪ {GMark.M} = {GMark.M}) ∧
    (({GMark.M} : GenderSet) ∪ ∅ = {GMark.M}) ∧
    ((∅ : GenderSet) ∪ ∅ = ∅) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- Icelandic (119): masc `{M}`, fem `{F}`, neut `{M, F}` — like genders preserved,
    any mixture resolves neuter (118/120). -/
theorem icelandic_mixed_is_neuter :
    (({GMark.M} : GenderSet) ∪ {GMark.F} = {GMark.M, GMark.F}) ∧
    (({GMark.M} : GenderSet) ∪ {GMark.M, GMark.F} = {GMark.M, GMark.F}) ∧
    (({GMark.F} : GenderSet) ∪ {GMark.M, GMark.F} = {GMark.M, GMark.F}) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- Slovene (122)/(126)–(127): masc `{F, N}`, fem `{F}`, neut `{N}`, and the
    *conjunction itself* contributes `F ∈ (↑ GENDER)` — deriving the surprising
    `NEUT & NEUT = MASC` (123)–(124). -/
-- Named (unlike Hindi/Icelandic, stated with bare `∪`) because Slovene resolution is
-- *not* bare union: the conjunction itself contributes `F` (126).
def slovResolve (p q : GenderSet) : GenderSet := p ∪ q ∪ {GMark.F}

theorem slovene_neut_neut_is_masc :
    slovResolve {GMark.N} {GMark.N} = ({GMark.F, GMark.N} : GenderSet) ∧
    slovResolve {GMark.F} {GMark.F} = ({GMark.F} : GenderSet) := by
  constructor <;> decide

/-! ### Bridge: marker sets project onto the binary person decomposition

`Features/Person.lean`'s two-boolean decomposition (`hasAuthor`, `hasParticipant`) is
the image of the marker-set representation: `S ∈ p` is authorship, membership of
either marker is participanthood. The map collapses exactly the inclusive/exclusive
distinction — Fula's `{S}` and `{S, H}` land on the same binary value — which is the
formal content of §6.2's "fewer pronominal distinctions". -/

open Person in
/-- Project a marker set onto the binary decomposition. -/
def toBinary (p : PersonSet) : Person.Features :=
  { hasParticipant := Marker.S ∈ p ∨ Marker.H ∈ p
    hasAuthor := Marker.S ∈ p }

open Person in
theorem toBinary_values :
    toBinary fula1exc = firstF ∧ toBinary fula1inc = firstF ∧
    toBinary fula2 = secondF ∧ toBinary fula3 = thirdF := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [toBinary, fula1exc, fula1inc, fula2, fula3, firstF, secondF, thirdF]

/-- The inclusive/exclusive collapse, explicitly: the binary decomposition cannot
    separate Fula's two first persons. -/
theorem binary_collapses_clusivity :
    toBinary fula1exc = toBinary fula1inc ∧ fula1exc ≠ fula1inc := by
  constructor
  · simp [toBinary, fula1exc, fula1inc]
  · decide

/-! ### BundleLike with `Finset` slots: the generic substrate accommodates indeterminacy

A multi-feature indeterminacy bundle is just a Pi type with `Finset` slots,
ordered superset-first (more determinate = smaller set). `BundleLike`'s
slot type family `S : F → Type*` (parameter `S` carrying its own
order) covers this case without any new generic machinery: `S t :=
(Finset (V t))ᵒᵈ`. The `BundleLike.Subsumes` order then reads, per slot,
`b₁ t ≤ b₂ t` in the order dual — i.e. `(b₂ t).1 ⊆ (b₁ t).1` — which is
exactly the §4 (eq. 25) information-as-set-of-possibilities convention.

This is the structural payoff: a feature-space tweak (Finset slots
instead of Flat slots), not a re-development of the lattice theory. -/

/-- An indeterminacy bundle: each slot holds a `Finset` of possible
atomic values, ordered superset-first via `Finset`'s order dual. -/
abbrev IndetBundle (F : Type*) (V : F → Type*) : Type _ :=
  (t : F) → (Finset (V t))ᵒᵈ

namespace IndetBundle

variable {F : Type*} {V : F → Type*}

instance : BundleLike (IndetBundle F V) F
    (fun t => (Finset (V t))ᵒᵈ) :=
  ⟨fun b => b⟩

instance : LawfulBundleLike (IndetBundle F V) :=
  ⟨fun _ _ h => h⟩

end IndetBundle

/-! Concrete witness: a 1-feature Case-indeterminacy bundle. We
exhibit two bundles — *was* {NOM, ACC} and *wer* {NOM} — and confirm
that `wer` subsumes (is more determinate than) `was`, via the
generic `BundleLike.Subsumes`. -/

/-- A single-feature Case bundle. -/
abbrev CaseBundle := IndetBundle Unit (fun _ => Case)

def wasBundle : CaseBundle := fun _ => OrderDual.toDual was
def werBundle : CaseBundle := fun _ => OrderDual.toDual wer

/-- *wer* {NOM} is more determinate than *was* {NOM, ACC}: their
subsumption in the generic `BundleLike` order matches set-superset on
the slot. -/
theorem wer_subsumes_was : BundleLike.Subsumes wasBundle werBundle := by
  intro _
  show wer ⊆ was
  decide

end DalrympleKaplan2000
