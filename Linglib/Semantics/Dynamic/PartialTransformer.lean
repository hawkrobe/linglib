import Mathlib.Data.PFun
import Linglib.Semantics.Dynamic.ContextChange
import Linglib.Semantics.Presupposition.Context

/-!
# Partial Context Change Potentials
[karttunen-1974] [heim-1983]

Heim's context change potentials are *partial* functions on contexts: the
domain condition IS the presupposition ([heim-1983]'s "c admits φ",
[karttunen-1974]'s "c satisfies-the-presuppositions-of φ").
`PartialCCP P := InfoStateOf P →. InfoStateOf P` grounds this in mathlib's
`PFun`: `Part.Dom` is admittance, and the satisfaction law for conjunction —
"c admits φ∧ψ iff c admits φ and c[φ] admits ψ" — is the domain condition
of partial-function composition, true by construction (`admits_pseq`).

`ofPartialProp` sends a static partial proposition to its Heimian update:
defined iff the context globally satisfies the presupposition (whole-state
admittance, NOT per-world filtering), updating by intersecting with the
assertion. Under this bridge the filtering connectives of
`Presupposition/Basic.lean` stop being stipulations: `andFilter`,
`impFilter`, and `orFilter` are *derived* as the admittance conditions of
dynamic conjunction, conditional, and disjunction
(`admits_pseq_ofPartialProp` etc.).

## Main declarations

- `PartialCCP`, `admits`, `ofCCP`, `ofPartialProp`
- `pseq`, `pneg`, `pcond`, `pdisj` — the partial-update clauses
  ([heim-1983] gives CCPs for *not/and/if*; the disjunction clause with
  ¬φ local context follows [beaver-2001])
- `admits_pseq` — the Karttunen satisfaction law, by construction
- `admits_ofPartialProp_iff_presupSatisfied` — admittance is
  `Context.presupSatisfied`
- `admits_pseq_ofPartialProp`, `admits_pcond_ofPartialProp`,
  `admits_pdisj_ofPartialProp` — the filtering connectives, derived
-/

namespace DynamicSemantics

open Semantics.Presupposition

/-- A partial context change potential: a partial function on information
    states. The domain condition is the presupposition; `Part.Dom` is
    [heim-1983]'s admittance. -/
abbrev PartialCCP (P : Type*) := InfoStateOf P →. InfoStateOf P

namespace PartialCCP

variable {P W : Type*}

/-- `u.admits s`: the update is defined at `s` ([heim-1983]'s "s admits u",
    [karttunen-1974]'s satisfaction). This is `Part.Dom`. -/
def admits (u : PartialCCP P) (s : InfoStateOf P) : Prop := (u s).Dom

/-- Total CCPs are partial CCPs with trivial presupposition. -/
def ofCCP (φ : CCP P) : PartialCCP P := λ s => Part.some (φ s)

@[simp] theorem admits_ofCCP (φ : CCP P) (s : InfoStateOf P) :
    (ofCCP φ).admits s := trivial

/-- The Heimian update of a static partial proposition: defined iff every
    world of the input satisfies the presupposition, updating by
    intersecting with the assertion.

    The whole-state domain condition is what separates admittance from
    per-world filtering (`updateFromSat`): a context containing a single
    presupposition-failing world admits nothing, rather than silently
    discarding the world. -/
def ofPartialProp (p : PartialProp W) : PartialCCP W :=
  λ s => ⟨∀ w ∈ s, p.presup w, λ _ => { w ∈ s | p.assertion w }⟩

@[simp] theorem ofPartialProp_get (p : PartialProp W) (s : InfoStateOf W)
    (h : ((ofPartialProp p) s).Dom) :
    ((ofPartialProp p) s).get h = { w ∈ s | p.assertion w } := rfl

/-! ### Connectives -/

/-- Sequencing (dynamic conjunction): `s[φ ∧ ψ] = s[φ][ψ]`. This is
    `PFun.comp`; the projection behavior of conjunction is the
    composition law of partial functions. -/
def pseq (φ ψ : PartialCCP P) : PartialCCP P := ψ.comp φ

/-- Heim negation: `s[¬φ] = s \ s[φ]`, defined iff `s[φ]` is. -/
def pneg (φ : PartialCCP P) : PartialCCP P := λ s => (φ s).map (s \ ·)

/-- Heim conditional: `s[if φ, ψ] = s \ (s[φ] \ s[φ][ψ])`, defined iff
    `s[φ]` and `s[φ][ψ]` are. -/
def pcond (φ ψ : PartialCCP P) : PartialCCP P :=
  λ s => (φ s).bind λ sφ => (ψ sφ).map λ sφψ => s \ (sφ \ sφψ)

/-- Disjunction with ¬φ local context for the second disjunct
    ([beaver-2001]; [heim-1983] gives CCPs only for *not/and/if*):
    `s[φ ∨ ψ] = s[φ] ∪ (s \ s[φ])[ψ]`. -/
def pdisj (φ ψ : PartialCCP P) : PartialCCP P :=
  λ s => (φ s).bind λ sφ => (ψ (s \ sφ)).map λ sψ => sφ ∪ sψ

/-! ### The satisfaction law -/

/-- **The Karttunen satisfaction law** ([karttunen-1974]), by construction:
    `s` admits `φ ∧ ψ` iff `s` admits `φ` and `s[φ]` admits `ψ`. The
    statement is the domain condition of `Part.bind`. -/
theorem admits_pseq (φ ψ : PartialCCP P) (s : InfoStateOf P) :
    (pseq φ ψ).admits s ↔ ∃ h : φ.admits s, ψ.admits ((φ s).get h) :=
  Iff.rfl

/-- The satisfaction law, with admittance of the first conjunct given. -/
theorem admits_pseq_iff (φ ψ : PartialCCP P) (s : InfoStateOf P)
    (h : φ.admits s) :
    (pseq φ ψ).admits s ↔ ψ.admits ((φ s).get h) :=
  ⟨λ ⟨_, hb⟩ => hb, λ hb => ⟨h, hb⟩⟩

/-- Negation projects: `s` admits `¬φ` iff `s` admits `φ`. -/
@[simp] theorem admits_pneg (φ : PartialCCP P) (s : InfoStateOf P) :
    (pneg φ).admits s ↔ φ.admits s :=
  Iff.rfl

/-- Conditional admittance: `s` admits `if φ, ψ` iff `s` admits `φ` and
    `s[φ]` admits `ψ` — the same condition as conjunction
    ([karttunen-1974]). -/
theorem admits_pcond (φ ψ : PartialCCP P) (s : InfoStateOf P) :
    (pcond φ ψ).admits s ↔ ∃ h : φ.admits s, ψ.admits ((φ s).get h) :=
  Iff.rfl

/-- Disjunction admittance: `s` admits `φ ∨ ψ` iff `s` admits `φ` and the
    ¬φ local context `s \ s[φ]` admits `ψ`. -/
theorem admits_pdisj (φ ψ : PartialCCP P) (s : InfoStateOf P) :
    (pdisj φ ψ).admits s ↔
      ∃ h : φ.admits s, ψ.admits (s \ (φ s).get h) :=
  Iff.rfl

/-! ### The Stalnaker bridge -/

/-- Admittance of an atomic update is global presupposition satisfaction. -/
theorem admits_ofPartialProp (p : PartialProp W) (s : InfoStateOf W) :
    (ofPartialProp p).admits s ↔ ∀ w ∈ s, p.presup w :=
  Iff.rfl

/-- Admittance is the static layer's `Context.presupSatisfied`: the dynamic
    definedness condition and the satisfaction-theoretic context condition
    are one notion. -/
theorem admits_ofPartialProp_iff_presupSatisfied (p : PartialProp W)
    (c : CommonGround.ContextSet W) :
    (ofPartialProp p).admits c ↔ Context.presupSatisfied c p :=
  Iff.rfl

/-! ### Filtering connectives, derived

Under `ofPartialProp`, the admittance conditions of the dynamic
connectives are pointwise exactly the presuppositions of the *filtering*
connectives of `Presupposition/Basic.lean` — Karttunen filtering is the
composition law of partial updates, not a stipulation. -/

/-- Dynamic conjunction admits `s` iff `s` satisfies `andFilter`'s
    presupposition pointwise. -/
theorem admits_pseq_ofPartialProp (p q : PartialProp W) (s : InfoStateOf W) :
    (pseq (ofPartialProp p) (ofPartialProp q)).admits s ↔
      ∀ w ∈ s, (PartialProp.andFilter p q).presup w := by
  constructor
  · rintro ⟨hp, hq⟩ w hw
    exact ⟨hp w hw, λ ha => hq w ⟨hw, ha⟩⟩
  · intro h
    exact ⟨λ w hw => (h w hw).1, λ w hw => (h w hw.1).2 hw.2⟩

/-- Dynamic conditional admits `s` iff `s` satisfies `impFilter`'s
    presupposition pointwise. -/
theorem admits_pcond_ofPartialProp (p q : PartialProp W) (s : InfoStateOf W) :
    (pcond (ofPartialProp p) (ofPartialProp q)).admits s ↔
      ∀ w ∈ s, (PartialProp.impFilter p q).presup w := by
  constructor
  · rintro ⟨hp, hq⟩ w hw
    exact ⟨hp w hw, λ ha => hq w ⟨hw, ha⟩⟩
  · intro h
    exact ⟨λ w hw => (h w hw).1, λ w hw => (h w hw.1).2 hw.2⟩

/-- Dynamic disjunction admits `s` iff `s` satisfies `orFilter`'s
    presupposition pointwise: the ¬φ local context is Karttunen's
    negative-antecedent filtering. -/
theorem admits_pdisj_ofPartialProp (p q : PartialProp W) (s : InfoStateOf W) :
    (pdisj (ofPartialProp p) (ofPartialProp q)).admits s ↔
      ∀ w ∈ s, (PartialProp.orFilter p q).presup w := by
  constructor
  · rintro ⟨hp, hq⟩ w hw
    exact ⟨hp w hw, λ hna => hq w ⟨hw, λ hc => hna hc.2⟩⟩
  · intro h
    exact ⟨λ w hw => (h w hw).1,
           λ w hw => (h w hw.1).2 (λ ha => hw.2 ⟨hw.1, ha⟩)⟩

/-- Negation projects the atomic presupposition unchanged. -/
theorem admits_pneg_ofPartialProp (p : PartialProp W) (s : InfoStateOf W) :
    (pneg (ofPartialProp p)).admits s ↔ ∀ w ∈ s, p.presup w :=
  Iff.rfl

end PartialCCP

end DynamicSemantics
