import Linglib.Core.Order.Flat
import Linglib.Core.Order.PartialUnify
import Linglib.Data.UD.Basic
import Linglib.Features.Basic
import Linglib.Features.Case.Basic
import Linglib.Features.Person.Decomposition
import Linglib.Features.Person.Resolve
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib.Order.BoundedOrder.Basic

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
(the subsumption/unification substrate at the end of this file) as
linguistically definitional: indeterminate
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

The flat slot order (this file's subsumption substrate below) embeds into the
indeterminacy lattice: a determinate commitment `↑x` is the singleton `{x}`, and *no
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


-- ============================================================================
-- Subsumption/unification substrate (demoted from Morphology/Unification.lean;
-- sole consumer was this study — see [dalrymple-kaplan-2000] on indeterminacy)
-- ============================================================================

/-!
## Subsumption and unification on `UD.MorphFeatures`
[shieber-1986]

The information ordering of unification-based grammar ([shieber-1986] §3.2), on
`UD.MorphFeatures` — the depth-1, reentrancy-free fragment of Shieber's feature
structures. Every feature here is atomic-valued, so paths are single features, the
reentrancy clause of subsumption is vacuous, and the definition (§3.2.2: `D ⊑ D′` iff
`D(l) ⊑ D′(l)` for all `l ∈ dom(D)`; "an atomic feature structure neither subsumes nor
is subsumed by a different atomic feature structure"; "variables subsume all other
feature structures") reduces to the product of flat orders. Subsumption is registered
as `≤` (Shieber's `⊑`); the all-`none` bundle — Shieber's variable `[ ]` — is `⊥`.

Unification (§3.2.3) is "the most general feature structure `D` such that `D′ ⊑ D` and
`D′′ ⊑ D`", failing on conflict: `MorphFeatures.unify` returns `some` exactly on
`Compatible` (= bounded above) inputs, and its result is the least upper bound
(`unify_isLUB`). The example laws of §3.2.3 are theorems: unification is idempotent
(`unify_self`), commutative (`unify_comm`), and variables are identity elements
(`bot_unify`).

## Main declarations

* `instance : PartialOrder UD.MorphFeatures` — subsumption ("only a partial order",
  §3.2.3), with decidable `≤`.
* `instance : OrderBot UD.MorphFeatures` — the empty bundle is bottom.
* `instance : SemilatticeInf UD.MorphFeatures` — the meet is Shieber's
  *generalization* (anti-unification): total, unlike the join.
* `UD.MorphFeatures.Compatible` — boundedness above (`BddAbove {f, g}`), decidable
  via the `Bool` check (`compatible_iff_bddAbove`).
* `unify_isLUB`, `unify_eq_some_iff_isLUB`, `unify_comm`, `unify_assoc`,
  `unify_self`, `bot_unify`/`unify_bot`, `unify_mono` — the §3.2.3 laws plus
  associativity and guarded monotonicity.

## Theory-neutrality boundary

Three strata with different statuses: the *record* is annotation consensus
(`Data/UD/Basic.lean`); the *order* `≤` is shared substrate every framework consumes
its own way (DM's matching clause, underspecification, syncretism down-sets); the
*operations* `⊔`/`⊓` are commitments of the unification tradition — [shieber-1986]
§3.1 states unification-as-sole-combinator as a design constraint, and rival
frameworks combine differently (DM matches and competes; Minimalist Agree values
asymmetrically). This file is *not* that tradition's headquarters: unification-based
grammar (PATR, HPSG, LFG — reentrant feature structures, phrasal combination) is a
syntax family whose substrate belongs in `Syntax/` when consuming studies demand it.
What lives here is only the tradition's morphological-bundle fragment — the algebra
of one token's Feats column — which it shares with rivals: at the level of claims
about morphological feature combination this file is a sibling of `DM/` and
`Nanosyntax/`, not a foundation beneath them.

## Implementation notes

Morphology owns the bundle algebra: `MorphFeatures` is the token's morphology (UD's
Feats column), and unification at the ms-word level is the morphology/syntax interface
operation. The *matching clause* of DM's Subset Principle (an exponent is insertable
iff `exponent.features ≤ morpheme.features`) *could* consume `≤` directly, but the
existing `Morphology/DM/VocabularyInsertion.lean` matches by `List`-subset on `[BEq F]`
rather than `MorphFeatures.≤`; bridging is left for a future PR. The competition
clause — most-specified-wins — is separate `argmax` machinery already implemented in
that same file. (Nanosyntax's Superset Principle is *not* a consumer: it matches by
containment of syntactic trees, see `Nanosyntax/TreeSpellout.lean`'s `NanoTree.contains`,
not by an order on flat bundles.) Lives apart from `Data/UD/Basic.lean` so the
(heavily imported) standard mirror stays mathlib-free — this file is the one that
pays for `Mathlib.Order` — and it is the canonical home for order instances on
`UD.MorphFeatures`.

The non-distributivity of the subsumption lattice is a documented
obstruction (`Flat.unify_distinct_eq_none`): any ≥3-value slot
(here, `Case`) makes the per-slot lattice the diamond Mₙ, modular but
*not* distributive ([carpenter-1992] p. 15, eq. (4), notes this
explicitly: "our partial orders are *not* required to be distributive
(and in fact, are not even required to be modular)"). This matters for
generalization-then-unification reorderings in paradigm-induction
learners.
-/

set_option autoImplicit false

/-! ### The flat order on one feature slot

The slot-level subsumption relation ([shieber-1986] §3.2.2: `⊥` below
everything, distinct atoms incomparable) is the order of `Flat`
(`Linglib/Core/Order/Flat.lean`), whose
`PartialOrder`/`OrderBot`/`SemilatticeInf`/`PartialUnify` instances
supply the per-slot steps of the bundle-level proofs below.
-/

namespace UD

/-- The 14-case feature-type index for `MorphFeatures` — the signature
of UD's Feats column treated as a fixed finite type family. -/
inductive MorphFeatureType where
  | number | gender | case_ | definite | degree | pronType
  | reflex
  | person | verbForm | tense | aspect | mood | voice | polarity
  deriving DecidableEq, Repr, Fintype

namespace MorphFeatureType

/-- Per-slot value space. The reflex slot is privative (`Unit`); all
other slots take their concrete UD enum. -/
def Val : MorphFeatureType → Type
  | .number   => Number
  | .gender   => Gender
  | .case_    => Case
  | .definite => Definite
  | .degree   => Degree
  | .pronType => PronType
  | .reflex   => Unit
  | .person   => Person
  | .verbForm => VerbForm
  | .tense    => Tense
  | .aspect   => Aspect
  | .mood     => Mood
  | .voice    => Voice
  | .polarity => Polarity

instance : ∀ t, DecidableEq (Val t)
  | .number   => inferInstanceAs (DecidableEq Number)
  | .gender   => inferInstanceAs (DecidableEq Gender)
  | .case_    => inferInstanceAs (DecidableEq Case)
  | .definite => inferInstanceAs (DecidableEq Definite)
  | .degree   => inferInstanceAs (DecidableEq Degree)
  | .pronType => inferInstanceAs (DecidableEq PronType)
  | .reflex   => inferInstanceAs (DecidableEq Unit)
  | .person   => inferInstanceAs (DecidableEq Person)
  | .verbForm => inferInstanceAs (DecidableEq VerbForm)
  | .tense    => inferInstanceAs (DecidableEq Tense)
  | .aspect   => inferInstanceAs (DecidableEq Aspect)
  | .mood     => inferInstanceAs (DecidableEq Mood)
  | .voice    => inferInstanceAs (DecidableEq Voice)
  | .polarity => inferInstanceAs (DecidableEq Polarity)

end MorphFeatureType

end UD

namespace UD.MorphFeatures

/-! ### Subsumption is a partial order with bottom -/

/-- Subsumption ([shieber-1986] §3.2.2): `f` carries a subset of `g`'s information —
field-wise flat order on the option slots, implication on the `reflex` flag. -/
def Subsumes (f g : MorphFeatures) : Prop :=
  f.number ≤ g.number ∧ f.gender ≤ g.gender ∧ f.case_ ≤ g.case_ ∧
  f.definite ≤ g.definite ∧ f.degree ≤ g.degree ∧
  f.pronType ≤ g.pronType ∧ (f.reflex = true → g.reflex = true) ∧
  f.person ≤ g.person ∧ f.verbForm ≤ g.verbForm ∧ f.tense ≤ g.tense ∧
  f.aspect ≤ g.aspect ∧ f.mood ≤ g.mood ∧ f.voice ≤ g.voice ∧
  f.polarity ≤ g.polarity

/-! ### `MorphFeatures` as a feature bundle, and the derived order

`MorphFeatures` realizes `BundleLike` over the 14-case signature
`MorphFeatureType` ([carpenter-1992]'s abstract feature structure): each
slot projects to a `Flat` value, with the `reflex` flag normalized
`false ↦ none`, `true ↦ some ()` (the privative `Unit` case). The
valuation is injective, so `MorphFeatures` is `LawfulBundleLike`, and the
subsumption order *is* the per-slot `Flat` order pulled back along `val`
(`subsumes_iff_val_le`) — the `PartialOrder`/`OrderBot` laws derive from
the bundle embedding rather than being proved field by field. -/

/-- The valuation: project each slot as a `Flat` value, normalizing
`reflex : Bool` to a privative `Flat Unit`. -/
def val (f : MorphFeatures) :
    (t : MorphFeatureType) → Flat (MorphFeatureType.Val t)
  | .number   => f.number
  | .gender   => f.gender
  | .case_    => f.case_
  | .definite => f.definite
  | .degree   => f.degree
  | .pronType => f.pronType
  | .reflex   => if f.reflex then (↑() : Flat Unit) else ⊥
  | .person   => f.person
  | .verbForm => f.verbForm
  | .tense    => f.tense
  | .aspect   => f.aspect
  | .mood     => f.mood
  | .voice    => f.voice
  | .polarity => f.polarity

instance : BundleLike MorphFeatures MorphFeatureType
    (fun t => Flat (MorphFeatureType.Val t)) where
  val := MorphFeatures.val

private theorem reflex_eq_of_val_reflex_eq {b1 b2 : Bool}
    (h : (if b1 then (↑() : Flat Unit) else ⊥) = if b2 then ↑() else ⊥) :
    b1 = b2 := by
  cases b1 <;> cases b2 <;> simp_all

/-- The valuation is injective: a `MorphFeatures` bundle is determined by
its per-slot assignments (with `reflex` reconstructed from `Option Unit`). -/
theorem val_injective : Function.Injective MorphFeatures.val := by
  intro f g h
  cases f; cases g
  simp only [mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact congrFun h .number
  · exact congrFun h .gender
  · exact congrFun h .case_
  · exact congrFun h .definite
  · exact congrFun h .degree
  · exact congrFun h .pronType
  · exact reflex_eq_of_val_reflex_eq (congrFun h .reflex)
  · exact congrFun h .person
  · exact congrFun h .verbForm
  · exact congrFun h .tense
  · exact congrFun h .aspect
  · exact congrFun h .mood
  · exact congrFun h .voice
  · exact congrFun h .polarity

instance : LawfulBundleLike MorphFeatures :=
  ⟨val_injective⟩

private theorem reflex_val_le_iff {b1 b2 : Bool} :
    (if b1 then (↑() : Flat Unit) else ⊥) ≤ (if b2 then ↑() else ⊥)
      ↔ (b1 = true → b2 = true) := by
  cases b1 <;> cases b2 <;> simp

/-- Subsumption is exactly the bundle order: the field-wise 14-conjunct form
coincides with the per-slot `Flat` order on the valuation `val`. -/
theorem subsumes_iff_val_le (f g : MorphFeatures) : Subsumes f g ↔ val f ≤ val g := by
  rw [Pi.le_def]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ t
    cases t
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
    · exact h6
    · exact reflex_val_le_iff.mpr h7
    · exact h8
    · exact h9
    · exact h10
    · exact h11
    · exact h12
    · exact h13
    · exact h14
  · intro h
    exact ⟨h .number, h .gender, h .case_, h .definite, h .degree, h .pronType,
           reflex_val_le_iff.mp (h .reflex), h .person, h .verbForm, h .tense,
           h .aspect, h .mood, h .voice, h .polarity⟩

instance : PartialOrder MorphFeatures where
  le := Subsumes
  le_refl f := (subsumes_iff_val_le f f).mpr le_rfl
  le_trans f g h hfg hgh :=
    (subsumes_iff_val_le f h).mpr
      (((subsumes_iff_val_le f g).mp hfg).trans ((subsumes_iff_val_le g h).mp hgh))
  le_antisymm f g hfg hgf :=
    val_injective (le_antisymm ((subsumes_iff_val_le f g).mp hfg)
      ((subsumes_iff_val_le g f).mp hgf))

instance (f g : MorphFeatures) : Decidable (Subsumes f g) := by
  unfold Subsumes; infer_instance

/-- Subsumption is decidable (each slot is). -/
instance (f g : MorphFeatures) : Decidable (f ≤ g) :=
  inferInstanceAs (Decidable (Subsumes f g))

/-- The empty bundle — Shieber's variable `[ ]` — is bottom: "variables subsume all
other feature structures … they contain no information at all" (§3.2.2). -/
instance : OrderBot MorphFeatures where
  bot := {}
  bot_le f := (subsumes_iff_val_le {} f).mpr (by
    intro t; cases t <;> exact bot_le)

/-! ### Compatibility is boundedness above; unification is the least upper bound -/

/-- `Prop`-native compatibility: the pair is bounded above in the subsumption
order — mathlib's `BddAbove`, so the bounds API applies directly. Characterized by
the executable `compatible` check via `compatible_iff_bddAbove`, which also makes
it decidable. -/
def Compatible (f g : MorphFeatures) : Prop := BddAbove ({f, g} : Set MorphFeatures)

/-- The left input subsumes the merge. -/
theorem le_merge_left (f g : MorphFeatures) : f ≤ f.merge g := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first
      | exact Flat.le_or_left _ _
      | exact fun hr => by simp [merge, hr]

private theorem le_or_of_clause {α : Type _} [BEq α] [LawfulBEq α] {a b : Flat α}
    (hcl : (a.isNone || b.isNone || a == b) = true) : b ≤ a.or b := by
  cases a with
  | bot => exact le_rfl
  | coe v =>
    cases b with
    | bot => exact bot_le
    | coe x =>
      obtain rfl : v = x :=
        Flat.coe_inj.mp (eq_of_beq (show ((v : Flat α) == ↑x) = true from hcl))
      exact le_rfl

/-- The right input subsumes the merge — *given compatibility* (the doubly committed
slots agree, so the left bias is harmless). -/
theorem le_merge_right {f g : MorphFeatures} (h : f.compatible g = true) :
    g ≤ f.merge g := by
  simp only [compatible, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩ := h
  exact ⟨le_or_of_clause h1, le_or_of_clause h2,
         le_or_of_clause h3, le_or_of_clause h4,
         le_or_of_clause h5, le_or_of_clause h6,
         fun hr => by simp [merge, hr],
         le_or_of_clause h7, le_or_of_clause h8,
         le_or_of_clause h9, le_or_of_clause h10,
         le_or_of_clause h11, le_or_of_clause h12,
         le_or_of_clause h13⟩

/-- The merge is below every common upper bound — minimality ("the *most general*
feature structure", §3.2.3). -/
theorem merge_le {f g u : MorphFeatures} (hf : f ≤ u) (hg : g ≤ u) :
    f.merge g ≤ u := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14⟩ := hf
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14⟩ := hg
  refine ⟨Flat.or_le a1 b1, Flat.or_le a2 b2, Flat.or_le a3 b3,
          Flat.or_le a4 b4, Flat.or_le a5 b5, Flat.or_le a6 b6, ?_,
          Flat.or_le a8 b8, Flat.or_le a9 b9, Flat.or_le a10 b10,
          Flat.or_le a11 b11, Flat.or_le a12 b12, Flat.or_le a13 b13,
          Flat.or_le a14 b14⟩
  intro hr
  rcases Bool.or_eq_true_iff.mp (by simpa [merge] using hr) with h | h
  · exact a7 h
  · exact b7 h

private theorem clause_of_le {α : Type _} [BEq α] [LawfulBEq α] {a b u : Flat α}
    (ha : a ≤ u) (hb : b ≤ u) : (a.isNone || b.isNone || a == b) = true := by
  cases a with
  | bot => rfl
  | coe x =>
    cases b with
    | bot => rfl
    | coe y =>
      obtain rfl : u = ↑x := Flat.coe_le_iff.mp ha
      obtain rfl : y = x := Flat.coe_le_coe.mp hb
      exact beq_self_eq_true _

/-- Bounded above implies the executable check passes. -/
theorem compatible_of_le {f g u : MorphFeatures} (hf : f ≤ u) (hg : g ≤ u) :
    f.compatible g = true := by
  obtain ⟨a1, a2, a3, a4, a5, a6, _, a8, a9, a10, a11, a12, a13, a14⟩ := hf
  obtain ⟨b1, b2, b3, b4, b5, b6, _, b8, b9, b10, b11, b12, b13, b14⟩ := hg
  simp only [compatible, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨clause_of_le a1 b1, clause_of_le a2 b2⟩,
    clause_of_le a3 b3⟩, clause_of_le a4 b4⟩, clause_of_le a5 b5⟩,
    clause_of_le a6 b6⟩, clause_of_le a8 b8⟩, clause_of_le a9 b9⟩,
    clause_of_le a10 b10⟩, clause_of_le a11 b11⟩, clause_of_le a12 b12⟩,
    clause_of_le a13 b13⟩, clause_of_le a14 b14⟩

/-- The `Bool` check is exactly boundedness above in the subsumption order: the
order-theoretic identity of "compatible". -/
theorem compatible_iff_bddAbove (f g : MorphFeatures) :
    f.compatible g = true ↔ Compatible f g := by
  constructor
  · intro h
    refine ⟨f.merge g, fun x hx => ?_⟩
    rcases hx with rfl | hx
    · exact le_merge_left _ g
    · rw [Set.mem_singleton_iff.mp hx]
      exact le_merge_right h
  · rintro ⟨u, hu⟩
    exact compatible_of_le (hu (Set.mem_insert _ _)) (hu (Set.mem_insert_of_mem _ rfl))

instance (f g : MorphFeatures) : Decidable (Compatible f g) :=
  decidable_of_iff _ (compatible_iff_bddAbove f g)

/-- Unification succeeds exactly on compatible inputs (§3.2.3: otherwise it "fails"). -/
theorem unify_eq_some_iff (f g : MorphFeatures) :
    (f.unify g).isSome = true ↔ Compatible f g := by
  rw [← compatible_iff_bddAbove]
  unfold unify
  by_cases hc : f.compatible g = true <;> simp [hc]

/-- **Unification is the least upper bound** ([shieber-1986] §3.2.3: "the most general
feature structure `D` such that `D′ ⊑ D` and `D′′ ⊑ D`"). -/
theorem unify_isLUB {f g u : MorphFeatures} (h : f.unify g = some u) :
    IsLUB {f, g} u := by
  unfold unify at h
  by_cases hc : f.compatible g = true
  · simp only [hc, if_true, Option.some.injEq] at h
    subst h
    constructor
    · intro x hx
      rcases Set.mem_insert_iff.mp hx with rfl | hx
      · exact le_merge_left _ g
      · rw [Set.mem_singleton_iff.mp hx]
        exact le_merge_right hc
    · intro v hv
      exact merge_le (hv (Set.mem_insert _ _)) (hv (Set.mem_insert_of_mem _ rfl))
  · simp [hc] at h

/-! ### Generalization: the meet

Shieber's *generalization* (anti-unification): the most specific bundle subsumed by
both inputs. Unlike unification it is total — the meet always exists — so
`MorphFeatures` is a genuine `SemilatticeInf` with `⊥`. -/

instance : Min MorphFeatures where
  min f g :=
    { number   := f.number ⊓ g.number
      gender   := f.gender ⊓ g.gender
      case_    := f.case_ ⊓ g.case_
      definite := f.definite ⊓ g.definite
      degree   := f.degree ⊓ g.degree
      pronType := f.pronType ⊓ g.pronType
      reflex   := f.reflex && g.reflex
      person   := f.person ⊓ g.person
      verbForm := f.verbForm ⊓ g.verbForm
      tense    := f.tense ⊓ g.tense
      aspect   := f.aspect ⊓ g.aspect
      mood     := f.mood ⊓ g.mood
      voice    := f.voice ⊓ g.voice
      polarity := f.polarity ⊓ g.polarity }

private theorem band_true_left {x y : Bool} (h : (x && y) = true) : x = true := by
  cases x <;> simp_all

private theorem band_true_right {x y : Bool} (h : (x && y) = true) : y = true := by
  cases y <;> simp_all

private theorem band_true_intro {x y : Bool} (hx : x = true) (hy : y = true) :
    (x && y) = true := by simp [hx, hy]

instance : SemilatticeInf MorphFeatures :=
  { (inferInstance : PartialOrder MorphFeatures),
    (inferInstance : Min MorphFeatures) with
    inf := min
    inf_le_left := fun f g => show Subsumes (min f g) f from
      ⟨inf_le_left, inf_le_left, inf_le_left, inf_le_left, inf_le_left, inf_le_left,
       fun hr => band_true_left hr,
       inf_le_left, inf_le_left, inf_le_left, inf_le_left, inf_le_left, inf_le_left,
       inf_le_left⟩
    inf_le_right := fun f g => show Subsumes (min f g) g from
      ⟨inf_le_right, inf_le_right, inf_le_right, inf_le_right, inf_le_right, inf_le_right,
       fun hr => band_true_right hr,
       inf_le_right, inf_le_right, inf_le_right, inf_le_right, inf_le_right, inf_le_right,
       inf_le_right⟩
    le_inf := fun c f g hcf hcg => by
      obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14⟩ := hcf
      obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14⟩ := hcg
      exact ⟨le_inf a1 b1, le_inf a2 b2, le_inf a3 b3,
             le_inf a4 b4, le_inf a5 b5, le_inf a6 b6,
             fun hr => band_true_intro (a7 hr) (b7 hr),
             le_inf a8 b8, le_inf a9 b9, le_inf a10 b10,
             le_inf a11 b11, le_inf a12 b12, le_inf a13 b13,
             le_inf a14 b14⟩ }

/-! ### Unification computes least upper bounds — further laws -/

/-- `MorphFeatures` carries the pairwise-LUB structure of [carpenter-1992]'s
bounded complete partial order: `unify` is the partial join, with
`unify_isLUB` and `compatible_iff_bddAbove` supplying the two class
axioms. The unification laws — commutativity, associativity (with
failure propagating), `⊥`-identity, idempotence, monotonicity — are
inherited as one-line corollaries of the generic theorems in
`Core/Order/PartialUnify.lean`. -/
instance : PartialUnify MorphFeatures where
  unify := MorphFeatures.unify
  isLUB_of_unify_eq_some := unify_isLUB
  isSome_unify_of_bddAbove {a b} h :=
    (unify_eq_some_iff a b).mpr h

/-- The instance-projected `unify` is the same function as
`MorphFeatures.unify`. -/
@[simp] theorem unify_eq_partialUnify (f g : MorphFeatures) :
    PartialUnify.unify f g = f.unify g := rfl

/-- Unification succeeds with value `u` exactly when `u` is the least upper bound. -/
theorem unify_eq_some_iff_isLUB {f g u : MorphFeatures} :
    f.unify g = some u ↔ IsLUB {f, g} u := by
  rw [← unify_eq_partialUnify]
  exact PartialUnify.unify_eq_some_iff_isLUB

/-- Unification is commutative — a consequence of *total* compatibility: doubly
committed slots agree, so the per-field left bias washes out. -/
theorem unify_comm (f g : MorphFeatures) : f.unify g = g.unify f := by
  rw [← unify_eq_partialUnify, ← unify_eq_partialUnify]
  exact PartialUnify.unify_comm f g

/-- Unification is idempotent (§3.2.3's example law). -/
@[simp] theorem unify_self (f : MorphFeatures) : f.unify f = some f := by
  rw [← unify_eq_partialUnify]; exact PartialUnify.unify_self f

/-- Variables are unification identity elements (§3.2.3's example law):
unifying with the empty bundle returns the other input. -/
@[simp] theorem bot_unify (f : MorphFeatures) :
    (⊥ : MorphFeatures).unify f = some f := by
  rw [← unify_eq_partialUnify]; exact PartialUnify.bot_unify f

/-- Unification is associative, with failure propagating ([shieber-1986] §3.2.3's
order-independence): both associations compute the lub of all three bundles. -/
theorem unify_assoc (f g h : MorphFeatures) :
    (f.unify g).bind (·.unify h) = (g.unify h).bind (f.unify ·) := by
  have := PartialUnify.unify_assoc f g h
  simp only [unify_eq_partialUnify] at this
  exact this

/-- The empty bundle is a right identity for unification. -/
@[simp] theorem unify_bot (f : MorphFeatures) :
    f.unify (⊥ : MorphFeatures) = some f := by
  rw [← unify_eq_partialUnify]; exact PartialUnify.unify_bot f

/-- Unification fails exactly on incompatible inputs. -/
theorem unify_eq_none_iff (f g : MorphFeatures) :
    f.unify g = none ↔ ¬ Compatible f g := by
  rw [← unify_eq_partialUnify]
  exact PartialUnify.unify_eq_none_iff (a := f) (b := g)

/-- Unification is monotone where defined: shrinking both inputs preserves success and
shrinks the output. (Unguarded `merge`-monotonicity is false — the guard is needed.) -/
theorem unify_mono {f₁ f₂ g₁ g₂ u₂ : MorphFeatures} (hf : f₁ ≤ f₂) (hg : g₁ ≤ g₂)
    (h2 : f₂.unify g₂ = some u₂) : ∃ u₁, f₁.unify g₁ = some u₁ ∧ u₁ ≤ u₂ := by
  rw [← unify_eq_partialUnify] at h2
  obtain ⟨u₁, hu₁, hle⟩ := PartialUnify.unify_mono hf hg h2
  exact ⟨u₁, unify_eq_partialUnify _ _ ▸ hu₁, hle⟩

end UD.MorphFeatures
