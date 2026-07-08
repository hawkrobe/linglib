import Linglib.Semantics.Plurality.Reciprocal
import Linglib.Semantics.Plurality.Algebra

/-!
# Heim, Lasnik & May (1991): Reciprocity and Plurality

[heim-lasnik-may-1991]

Linguistic Inquiry 22(1): 63–101.

The quantificational analysis of reciprocals: *each other* is not a
simplex anaphor but decomposes at LF into a **distributor** (*each*,
moved to the antecedent NP) and a **reciprocator** (*e other*), each
inheriting its semantics from its non-reciprocal use. The LF of
"the men saw each other" is
`[[the men]₁ each₂] saw [e₂ other]₃` — a four-part structure
*group antecedent – distributor – reciprocator – predicate* (their (9)).
This is the quantificational arm of the comparison drawn in
`Semantics/Reference/Reciprocals.lean`, and the decomposed counterpart of
Link's holistic `Algebra.DJR` operator.

Two puzzles drive the paper (both from [higginbotham-1985] and
[higginbotham-1980]): the **grain problem** — "John and Mary told each
other that they should leave" is three-ways ambiguous (I/you/we readings)
though binding theory allows only one indexing — and the **scope
puzzle** — embedded reciprocals allow broad and narrow construals. Both
resolve through the double indexing of plural NPs (range + distribution
indices, their (26)–(29)): the pronoun construals bound by the
quantificational *each*/*other* indices are singular bound variables
(I/you readings), those coindexed with the referential range index are
coreference anaphora (we readings), and scope covaries with anaphora type
because distributors are undefined on atoms and cannot iterate.

## Main declarations

* `other` (16), `reciprocator` (18), `distributor` (19)/(28) — the
  compositional pieces; the distributor is the `Finset`-level,
  world-free form of `Plurality.distMaximal` and `Algebra.D`.
* `eachOtherLF` + `eachOtherLF_iff_strongReciprocity` — the keystone:
  the each∘other composition derives `StrongReciprocity` (their (21)),
  plugging the LF analysis into the DKMPK entailment lattice.
* `eachOtherLF_singleton` — distribution over a singleton is vacuous:
  the semantic shadow of the definedness restriction that derives the
  plural-antecedent requirement (\**Mary saw each other*).
* `eachOtherLF_asymmetric_contradictory` — (68) "they are taller than
  each other" is contradictory on any genuine plurality.
* `PronounConstrual`, `GrainReading`, `AnaphoraType` — the grain
  solution (29)/(49): four construals, four readings, I/you = bound
  variable vs we = coreference.
* `EachAttachment`, `scopeWellFormed` — the scope solution (67):
  narrow ⇔ coreference and broad ⇔ bound variable, derived from the
  sum-host requirement on distributors and Principle A on the trace
  of *each*.

## Todo

* §4.2 long-distance reciprocals (Specified Subject Condition evasion
  via broad scope) and the *each … the other* variant constructions.
* Weaker-than-universal force: HLM restrict attention to two-membered
  groups (their fn. on (18)); connecting the composition to the weaker
  DKMPK schemes for larger groups is rival territory
  ([dalrymple-et-al-1998]).
-/

namespace HeimLasnikMay1991

open Semantics.Plurality.Reciprocal

variable {A : Type*} [DecidableEq A]

/-! ### The compositional pieces (§2.2)

HLM's model is `⟨D, A, Π⟩`: a domain with mereological structure, atoms
`A`, and proper-part-of `Π`; `·Π` is the proper-*atomic*-part relation.
Pluralities are encoded here as `Finset A` (sums of atoms) with `·Π` as
membership, matching the `(R, X)` signature of
`Semantics.Plurality.Reciprocal`. -/

/-- (16): *other* as a 3-place relation — referent `z` is an atomic part
    of the range `y` distinct from the contrast `x`. In reciprocals both
    implicit arguments are supplied by the derived antecedent phrase:
    the contrast is bound by *each*, the range is coreferential with the
    antecedent. -/
def other (contrast : A) (range : Finset A) (z : A) : Prop :=
  z ∈ range ∧ z ≠ contrast

/-- (18): the reciprocator `[e other]` with universal force — `x` stands
    in `ζ` to every *other* atomic part of the range. (HLM adopt
    universal force while restricting attention to two-membered groups,
    where universal and existential force coincide.) -/
def reciprocator (range : Finset A) (ζ : A → A → Prop) (x : A) : Prop :=
  ∀ z, other x range z → ζ x z

/-- (19)/(28): the distributor — *each* or the covert `D` — universally
    quantifies over the atomic parts of its host NP. The world-free
    `Finset` form of `Plurality.distMaximal` (English floated *each*)
    and of `Algebra.D` (Link's D operator). -/
def distributor (np : Finset A) (φ : A → Prop) : Prop :=
  ∀ x ∈ np, φ x

/-- The LF of "np V each other" after *each*-movement (their (8)/(20)):
    the distributor scopes over the reciprocated predicate, with the
    reciprocator's range and contrast both anaphoric to the derived
    antecedent. -/
def eachOtherLF (np : Finset A) (R : A → A → Prop) : Prop :=
  distributor np (reciprocator np R)

/-! ### The keystone (their (21)) -/

/-- The compositional each∘other analysis derives Strong Reciprocity:
    HLM's truth conditions "coincide with those of the standard semantic
    analyses". Through the entailment lattice of
    `Semantics.Plurality.Reciprocal`, the weaker schemes follow
    (`strong_imp_weak`, …). -/
theorem eachOtherLF_iff_strongReciprocity (np : Finset A) (R : A → A → Prop) :
    eachOtherLF np R ↔ StrongReciprocity R np := by
  constructor
  · intro h x hx y hy hyx
    exact h x hx y ⟨hy, hyx⟩
  · intro h x hx z hz
    exact h x hx z hz.1 hz.2

/-- Distribution over a singleton yields a vacuously true reciprocal —
    no reciprocal content at all. HLM derive the plural-antecedent
    requirement (\**Mary saw each other*) more strongly: `·Π` is defined
    only on sum counterdomains, so distributors cannot apply to singular
    NPs; this vacuity is the semantic shadow of that definedness
    restriction. -/
theorem eachOtherLF_singleton (a : A) (R : A → A → Prop) :
    eachOtherLF {a} R := by
  intro x hx z hz
  obtain ⟨hz1, hz2⟩ := hz
  rw [Finset.mem_singleton] at hx hz1
  exact absurd (hz1.trans hx.symm) hz2

/-- (68) "They are taller than each other" is contradictory: the
    each∘other composition over an asymmetric relation fails on every
    genuine plurality. Under embedding, only broad scope of *each*
    rescues it ((69)/(70)); with an explicit matrix distributor,
    re-attachment would stack distributors ((71)/(72)), so only the
    contradictory narrow reading survives. -/
theorem eachOtherLF_asymmetric_contradictory
    {np : Finset A} {R : A → A → Prop}
    (hasym : ∀ x y, R x y → ¬ R y x) (hcard : 2 ≤ np.card) :
    ¬ eachOtherLF np R := by
  intro h
  have hpos : 0 < np.card := by omega
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
  obtain ⟨y, hy, hyx⟩ := np.exists_mem_ne (by omega) x
  exact hasym x y (h x hx y ⟨hy, hyx⟩) (h y hy x ⟨hx, hyx.symm⟩)

/-! ### The grain problem (§3)

Plural NPs bear a *range* index and, optionally, a *distribution* index
((26)–(28)); in a reciprocal LF the reciprocator contributes a third
index. An embedded plural pronoun anaphoric to the antecedent therefore
has exactly four construals ((29)/(49)) — the theory is exactly as
fine-grained as the attested ambiguity of "John and Mary told each other
that they should leave". -/

/-- The four construals of an embedded plural pronoun in a reciprocal
    sentence ((49a–d)). -/
inductive PronounConstrual where
  /-- coindexed with the antecedent's referential *range* index -/
  | range
  /-- range-coindexed, with its own covert distributor `D` -/
  | rangeDistributed
  /-- bound by the *distribution* index contributed by *each* -/
  | distributor
  /-- bound by the *reciprocator*'s index -/
  | reciprocator
  deriving DecidableEq, Repr

/-- The readings of "John and Mary told each other that they should
    leave" ((43): *I* = "each told the other: I should leave", *you* =
    "…: you should leave", *we* together/separately). -/
inductive GrainReading where
  | I
  | you
  | weTogether
  | weSeparately
  deriving DecidableEq, Repr

/-- (49a–d): each construal yields exactly one reading. -/
def PronounConstrual.reading : PronounConstrual → GrainReading
  | .distributor      => .I
  | .reciprocator     => .you
  | .range            => .weTogether
  | .rangeDistributed => .weSeparately

/-- Bound-variable vs coreference anaphora — the *type* distinction the
    grain solution encodes structurally (§3.1, against
    [higginbotham-1985]'s linking alternative, where I/we would be one
    vague reading). -/
inductive AnaphoraType where
  | boundVariable
  | coreference
  deriving DecidableEq, Repr

/-- Construals bound by the quantificational *each*/*other* indices are
    singular bound variables; range-coindexed construals are coreference
    with the referential sum. Hence I/you = bound variable, we =
    coreference. -/
def PronounConstrual.anaphoraType : PronounConstrual → AnaphoraType
  | .distributor | .reciprocator  => .boundVariable
  | .range | .rangeDistributed    => .coreference

/-- A bound-variable construal ranges over atoms; a coreferential one
    denotes the antecedent's sum (§2.4). -/
def PronounConstrual.denotesAtom (c : PronounConstrual) : Bool :=
  c.anaphoraType == .boundVariable

/-- Whether the construal places the pronoun under a distributor of its
    own ((49d)). -/
def PronounConstrual.hostsDistributor : PronounConstrual → Bool
  | .rangeDistributed => true
  | _                 => false

/-- Preposed adjuncts block bound-variable anaphora ((61): a quantifier
    cannot bind into a preposed adjunct), so "After they had left the
    room, the candidates criticized each other" (60) keeps only the *we*
    construals, while the postposed (57) is fully ambiguous. -/
def PronounConstrual.availableInPreposedAdjunct (c : PronounConstrual) : Bool :=
  c.anaphoraType == .coreference

/-- The preposed-adjunct diagnostic isolates exactly the bound-variable
    construals: what (60) loses relative to (57) is the I and you
    readings. -/
theorem preposed_adjunct_blocks_bound_variables :
    ∀ c : PronounConstrual,
      c.availableInPreposedAdjunct = false ↔
        c.reading = .I ∨ c.reading = .you := by
  intro c
  cases c <;> simp [PronounConstrual.availableInPreposedAdjunct,
    PronounConstrual.anaphoraType, PronounConstrual.reading]

/-! ### The scope puzzle (§4)

"John and Mary think they like each other" (64) has a narrow reading
(they think: we like each other) and a broad one (each thinks: I like
the other). HLM resolve it as the attachment site of *each* ((67)):
to the embedded pronoun (narrow) or to the matrix subject (broad). The
correlation with anaphora type is *derived*: distributors need
sum-denoting hosts and cannot iterate, and the trace of *each* must be
bound by the index its host acquires (Principle A). -/

/-- Where *each* attaches at LF ((67a)/(67b)). -/
inductive EachAttachment where
  /-- `[they₁ each₂] like [e₂ other]` — narrow scope -/
  | embedded
  /-- `[[John and Mary]₁ each₂] think they₂ like [e₂ other]` — broad -/
  | matrix
  deriving DecidableEq, Repr

/-- Wellformedness of an attachment–construal pair, from two independent
    constraints: an *each* attached to the embedded pronoun needs a
    sum-denoting host that is not already distributed ((72): distributors
    do not iterate), and under matrix attachment the pronoun must carry
    the distribution index so that the trace of *each* is A-bound
    (Principle A, their (74)). -/
def scopeWellFormed : EachAttachment → PronounConstrual → Prop
  | .embedded, c =>
      c.denotesAtom = false ∧ c.hostsDistributor = false
  | .matrix, c => c = .distributor

/-- Narrow scope forces a coreferential pronoun ((67a)). -/
theorem narrow_forces_coreference (c : PronounConstrual)
    (h : scopeWellFormed .embedded c) :
    c.anaphoraType = .coreference := by
  cases c <;> simp_all [scopeWellFormed, PronounConstrual.denotesAtom,
    PronounConstrual.anaphoraType]

/-- Broad scope forces a bound-variable pronoun ((67b)): scope and
    anaphora type covary, the paper's answer to Williams's nonscope
    alternative (§4.1). -/
theorem broad_forces_bound_variable (c : PronounConstrual)
    (h : scopeWellFormed .matrix c) :
    c.anaphoraType = .boundVariable := by
  cases c <;> simp_all [scopeWellFormed, PronounConstrual.anaphoraType]

/-- Under embedded attachment exactly one construal survives: plain
    range coreference — (67a)'s indexing is forced. -/
theorem embedded_unique_construal (c : PronounConstrual) :
    scopeWellFormed .embedded c ↔ c = .range := by
  cases c <;> simp [scopeWellFormed, PronounConstrual.denotesAtom,
    PronounConstrual.anaphoraType, PronounConstrual.hostsDistributor]

end HeimLasnikMay1991
