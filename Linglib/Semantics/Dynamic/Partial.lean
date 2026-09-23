module

public import Mathlib.Data.PFun
public import Linglib.Semantics.Dynamic.Update
public import Linglib.Semantics.Presupposition.Context

/-!
# Partial Context Change Potentials

Heim's context change potentials are *partial* functions on contexts: the
domain condition IS the presupposition ([heim-1983]'s "c admits φ",
[karttunen-1974-presupposition]'s "c satisfies-the-presuppositions-of φ").
`CCP.Partial P := Set P →. Set P` grounds this in mathlib's
`PFun`: `Part.Dom` is admittance, and the satisfaction law for conjunction —
"c admits φ∧ψ iff c admits φ and c[φ] admits ψ" — is the domain condition
of partial-function composition, true by construction (`admits_seq`).

This is partiality of the *arrow*, and it is orthogonal to the partiality
of the *points*: DRT's embeddings are partial assignments of discourse
referents (`Possibility.domain`, `Part`-valued — `Dynamic/State.lean`),
which encodes referential growth, not presupposition. The two compose in
`Dynamic/FileChange.lean`, where `FCP` is `CCP.Partial` at partial-point
states. ([haug-2014]'s "partial dynamic semantics" is the *point* sense.)

`ofPartialProp` sends a static partial proposition to its Heimian update:
defined iff the context globally satisfies the presupposition (whole-state
admittance, NOT per-world filtering), updating by intersecting with the
assertion. Under this bridge the filtering connectives of
`Presupposition/Basic.lean` stop being stipulations: `andFilter`,
`impFilter`, and `orFilter` are *derived* as the admittance conditions of
dynamic conjunction, conditional, and disjunction
(`admits_seq_ofPartialProp` etc.).

## Main declarations

- `CCP.Partial`, `admits`, `ofTotal`, `ofPartialProp`
- `seq`, `neg`, `cond`, `disj` — the partial-update clauses
  ([heim-1983] gives CCPs for *not/and/if*; the disjunction clause with
  ¬φ local context follows [beaver-2001])
- `seq_eq_kleisliComp` — sequencing is Kleisli composition for `Part`:
  the partiality column of the effect view, beside `Collapse.lean`'s
  powerset column
- `admits_seq` — the Karttunen satisfaction law, by construction
- `IsEliminative` — Heim's Principle (A), closed under negation and
  sequencing
- `supports`, `entails` — a state supports an update it is a fixed point
  of, and `φ` entails `ψ` when every update with `φ` supports `ψ`;
  entailment is absorption, `seq φ ψ = φ` (`entails_iff_seq_eq`)
- `admits_ofPartialProp` — admittance is `Context.presupSatisfied`
- `mem_ofPartialProp_self` — a context is a fixed point of an atomic update iff
  presupposition and assertion hold throughout it ([heim-1992]'s `c + φ = same`)
- `admits_seq_ofPartialProp`, `admits_cond_ofPartialProp`,
  `admits_disj_ofPartialProp` — the filtering connectives, derived

## References

- [heim-1983], [heim-1982], [heim-1992], [karttunen-1974-presupposition]
- [beaver-2001], [veltman-1996], [groenendijk-stokhof-1990]
- [moggi-1991], [shan-2001], [haug-2014]
-/

@[expose] public section

namespace DynamicSemantics

open Presupposition

/-- A partial context change potential: a partial function on information
    states, the partial variant of the `CCP` API. The domain condition is
    the presupposition; `Part.Dom` is [heim-1983]'s admittance. -/
abbrev CCP.Partial (S : Type*) := Set S →. Set S

namespace CCP.Partial

variable {P W : Type*} {φ ψ χ : CCP.Partial P} {s : Set P}

/-- `u.admits s`: the update is defined at `s` ([heim-1983]'s "s admits u",
    [karttunen-1974-presupposition]'s satisfaction). This is `Part.Dom`. -/
def admits (u : CCP.Partial P) (s : Set P) : Prop := (u s).Dom

/-- Total CCPs are partial CCPs with trivial presupposition. -/
def ofTotal (φ : CCP P) : CCP.Partial P := fun s => Part.some (φ s)

@[simp] theorem admits_ofTotal (φ : CCP P) (s : Set P) :
    (ofTotal φ).admits s := trivial

/-- The Heimian update of a static partial proposition: defined iff the
    context globally satisfies the presupposition
    (`Context.presupSatisfied`), updating by intersecting with the
    assertion.

    The whole-state domain condition is what separates admittance from
    per-world filtering (`updateFromSat`): a context containing a single
    presupposition-failing world admits nothing, rather than silently
    discarding the world. -/
def ofPartialProp (p : PartialProp W) : CCP.Partial W :=
  fun s => ⟨Context.presupSatisfied s p, fun _ => { w ∈ s | p.assertion w }⟩

@[simp] theorem ofPartialProp_get (p : PartialProp W) (s : Set W)
    (h : ((ofPartialProp p) s).Dom) :
    ((ofPartialProp p) s).get h = { w ∈ s | p.assertion w } := rfl

/-- A context is a fixed point of an atomic update iff the presupposition and the assertion
hold throughout it ([heim-1992]'s `c + φ = same`). -/
theorem mem_ofPartialProp_self (p : PartialProp W) (s : Set W) :
    s ∈ ofPartialProp p s ↔ s ⊆ p.presup ∧ s ⊆ p.assertion :=
  ⟨fun ⟨h, e⟩ => ⟨h, Set.sep_eq_self_iff_mem_true.1 e⟩,
   fun ⟨h, e⟩ => ⟨h, Set.sep_eq_self_iff_mem_true.2 e⟩⟩

/-! ### Connectives -/

/-- Sequencing (dynamic conjunction): `s[φ ∧ ψ] = s[φ][ψ]`. This is
    `PFun.comp`; the projection behavior of conjunction is the
    composition law of partial functions. -/
def seq (φ ψ : CCP.Partial P) : CCP.Partial P := ψ.comp φ

/-- Sequencing is Kleisli composition for the `Part` monad: a partial CCP
    is a Kleisli arrow `Set P → Part (Set P)`, definitionally — the
    partiality column of the effect view of dynamic semantics, beside the
    powerset column in `Collapse.lean` ([moggi-1991], [shan-2001]). -/
theorem seq_eq_kleisliComp (φ ψ : Set P → Part (Set P)) :
    (seq φ ψ : Set P → Part (Set P)) = φ >=> ψ := rfl

/-- Heim negation: `s[¬φ] = s \ s[φ]`, defined iff `s[φ]` is. -/
def neg (φ : CCP.Partial P) : CCP.Partial P := fun s => (φ s).map (s \ ·)

/-- Heim conditional: `s[if φ, ψ] = s \ (s[φ] \ s[φ][ψ])`, defined iff
    `s[φ]` and `s[φ][ψ]` are. -/
def cond (φ ψ : CCP.Partial P) : CCP.Partial P :=
  fun s => (φ s).bind fun sφ => (ψ sφ).map fun sφψ => s \ (sφ \ sφψ)

/-- Disjunction with ¬φ local context for the second disjunct
    ([beaver-2001]; [heim-1983] gives CCPs only for *not/and/if*):
    `s[φ ∨ ψ] = s[φ] ∪ (s \ s[φ])[ψ]`. -/
def disj (φ ψ : CCP.Partial P) : CCP.Partial P :=
  fun s => (φ s).bind fun sφ => (ψ (s \ sφ)).map fun sψ => sφ ∪ sψ

/-! ### Eliminativity -/

/-- A partial update is *eliminative* if its defined outputs shrink the input
([heim-1982]'s Principle (A); [groenendijk-stokhof-1990]'s `↓`-direction). -/
def IsEliminative (φ : CCP.Partial P) : Prop := ∀ s, ∀ s' ∈ φ s, s' ⊆ s

theorem isEliminative_ofPartialProp (p : PartialProp W) :
    (ofPartialProp p).IsEliminative := fun _ _ h ↦ (Part.mem_mk_iff.mp h).2 ▸ Set.sep_subset _ _

theorem isEliminative_neg (φ : CCP.Partial P) : (neg φ).IsEliminative := fun _ _ h ↦ by
  obtain ⟨t, -, rfl⟩ := (Part.mem_map_iff _).mp h
  exact Set.sdiff_subset

theorem IsEliminative.seq (hφ : φ.IsEliminative) (hψ : ψ.IsEliminative) :
    (seq φ ψ).IsEliminative := fun s s' h ↦ by
  obtain ⟨t, ht, hs'⟩ := Part.mem_bind_iff.mp h
  exact (hψ t s' hs').trans (hφ s t ht)

theorem isEliminative_cond (φ ψ : CCP.Partial P) : (cond φ ψ).IsEliminative := fun _ _ h ↦ by
  obtain ⟨_, -, h⟩ := Part.mem_bind_iff.mp h
  obtain ⟨_, -, rfl⟩ := (Part.mem_map_iff _).mp h
  exact Set.sdiff_subset

/-! ### Support and entailment -/

/-- `s` supports `φ`: the update changes nothing ([heim-1992]'s `c + φ = c`,
[veltman-1996]'s acceptance). -/
def supports (s : Set P) (φ : CCP.Partial P) : Prop := φ s = Part.some s

/-- Support is being a fixed point of the update. -/
theorem supports_iff_mem : supports s φ ↔ s ∈ φ s := Part.eq_some_iff

/-- After a supported update, sequencing continues from the same state. -/
theorem supports.seq_apply (h : supports s φ) (ψ : CCP.Partial P) : seq φ ψ s = ψ s := by
  rw [seq, PFun.comp_apply, h, Part.bind_some]

/-- Dynamic entailment: every defined update with `φ` supports `ψ`
([veltman-1996]'s acceptance consequence; [heim-1982]'s entailment between
file change potentials). -/
def entails (φ ψ : CCP.Partial P) : Prop := ∀ s, ∀ s' ∈ φ s, supports s' ψ

/-- Entailment is absorption: `φ` entails `ψ` iff sequencing `ψ` after `φ`
changes nothing. -/
theorem entails_iff_seq_eq : entails φ ψ ↔ seq φ ψ = φ := by
  constructor
  · intro h
    funext s
    refine Part.ext fun t ↦ ?_
    rw [seq, PFun.comp_apply, Part.mem_bind_iff]
    constructor
    · rintro ⟨s', hs', ht⟩
      rw [h s s' hs', Part.mem_some_iff] at ht
      exact ht ▸ hs'
    · exact fun ht ↦ ⟨t, ht, by rw [h s t ht]; exact Part.mem_some t⟩
  · intro h s s' hs'
    rw [supports, Part.eq_some_iff]
    have hs'' : s' ∈ seq φ ψ s := by rw [h]; exact hs'
    obtain ⟨t, ht, hst⟩ := Part.mem_bind_iff.mp hs''
    exact Part.mem_unique ht hs' ▸ hst

theorem entails_trans (h₁ : entails φ ψ) (h₂ : entails ψ χ) : entails φ χ :=
  fun s s' hs' ↦ h₂ s' s' (supports_iff_mem.mp (h₁ s s' hs'))

/-- Whatever follows from the second conjunct follows from the conjunction. -/
theorem entails_seq_left (h : entails ψ χ) (φ : CCP.Partial P) : entails (seq φ ψ) χ :=
  fun _ s' hs' ↦ let ⟨t, _, ht⟩ := Part.mem_bind_iff.mp hs'; h t s' ht

/-! ### The satisfaction law -/

/-- **The Karttunen satisfaction law** ([karttunen-1974-presupposition]), by construction:
    `s` admits `φ ∧ ψ` iff `s` admits `φ` and `s[φ]` admits `ψ`. The
    statement is the domain condition of `Part.bind`. -/
theorem admits_seq (φ ψ : CCP.Partial P) (s : Set P) :
    (seq φ ψ).admits s ↔ ∃ h : φ.admits s, ψ.admits ((φ s).get h) :=
  Iff.rfl

/-- The satisfaction law, with admittance of the first conjunct given. -/
theorem admits_seq_iff (φ ψ : CCP.Partial P) (s : Set P)
    (h : φ.admits s) :
    (seq φ ψ).admits s ↔ ψ.admits ((φ s).get h) :=
  ⟨fun ⟨_, hb⟩ => hb, fun hb => ⟨h, hb⟩⟩

/-- Negation projects: `s` admits `¬φ` iff `s` admits `φ`. -/
@[simp] theorem admits_neg (φ : CCP.Partial P) (s : Set P) :
    (neg φ).admits s ↔ φ.admits s :=
  Iff.rfl

/-- Conditional admittance: `s` admits `if φ, ψ` iff `s` admits `φ` and
    `s[φ]` admits `ψ` — the same condition as conjunction
    ([karttunen-1974-presupposition]). -/
theorem admits_cond (φ ψ : CCP.Partial P) (s : Set P) :
    (cond φ ψ).admits s ↔ ∃ h : φ.admits s, ψ.admits ((φ s).get h) :=
  Iff.rfl

/-- Disjunction admittance: `s` admits `φ ∨ ψ` iff `s` admits `φ` and the
    ¬φ local context `s \ s[φ]` admits `ψ`. -/
theorem admits_disj (φ ψ : CCP.Partial P) (s : Set P) :
    (disj φ ψ).admits s ↔
      ∃ h : φ.admits s, ψ.admits (s \ (φ s).get h) :=
  Iff.rfl

/-! ### The Stalnaker bridge -/

/-- Admittance of an atomic update is the static layer's
    `Context.presupSatisfied`, by construction: the dynamic definedness
    condition and the satisfaction-theoretic context condition are one
    notion. -/
theorem admits_ofPartialProp (p : PartialProp W) (s : Set W) :
    (ofPartialProp p).admits s ↔ Context.presupSatisfied s p :=
  Iff.rfl

/-! ### Filtering connectives, derived

Under `ofPartialProp`, the admittance conditions of the dynamic
connectives are pointwise exactly the presuppositions of the *filtering*
connectives of `Presupposition/Basic.lean` — Karttunen filtering is the
composition law of partial updates, not a stipulation. -/

/-- Dynamic conjunction admits `s` iff `s` satisfies `andFilter`'s
    presupposition pointwise. -/
theorem admits_seq_ofPartialProp (p q : PartialProp W) (s : Set W) :
    (seq (ofPartialProp p) (ofPartialProp q)).admits s ↔
      ∀ w ∈ s, (PartialProp.andFilter p q).presup w :=
  ⟨fun ⟨hp, hq⟩ _ hw => ⟨hp hw, fun ha => hq ⟨hw, ha⟩⟩,
   fun h => ⟨fun w hw => (h w hw).1, fun w hw => (h w hw.1).2 hw.2⟩⟩

/-- Dynamic conditional admits `s` iff `s` satisfies `impFilter`'s
    presupposition pointwise. -/
theorem admits_cond_ofPartialProp (p q : PartialProp W) (s : Set W) :
    (cond (ofPartialProp p) (ofPartialProp q)).admits s ↔
      ∀ w ∈ s, (PartialProp.impFilter p q).presup w :=
  admits_seq_ofPartialProp p q s

/-- Dynamic disjunction admits `s` iff `s` satisfies `orFilter`'s
    presupposition pointwise: the ¬φ local context is Karttunen's
    negative-antecedent filtering. -/
theorem admits_disj_ofPartialProp (p q : PartialProp W) (s : Set W) :
    (disj (ofPartialProp p) (ofPartialProp q)).admits s ↔
      ∀ w ∈ s, (PartialProp.orFilter p q).presup w :=
  ⟨fun ⟨hp, hq⟩ _ hw => ⟨hp hw, fun hna => hq ⟨hw, fun hc => hna hc.2⟩⟩,
   fun h => ⟨fun w hw => (h w hw).1,
     fun w hw => (h w hw.1).2 (fun ha => hw.2 ⟨hw.1, ha⟩)⟩⟩

/-- Negation projects the atomic presupposition unchanged. -/
theorem admits_neg_ofPartialProp (p : PartialProp W) (s : Set W) :
    (neg (ofPartialProp p)).admits s ↔ ∀ w ∈ s, p.presup w :=
  Iff.rfl

end CCP.Partial

end DynamicSemantics
