import Linglib.Features.Number.Interp
import Linglib.Syntax.Minimalist.ExtendedProjection.Basic

/-!
# Borer (2005): the nominal spine and the mass/count distinction

[borer-2005] locates the mass/count distinction in functional structure rather than in
nouns: a root denotes a cumulative predicate, the classifier head (Borer's CL#, the `Q`
head of the nominal extended projection) individuates it, and the number head (`#`, the
`Num` head) counts the individuated units. Individuation is the restriction of a predicate
to its atoms — `Number.atomsOf`, the operation that also interprets singular number — so
the count reading of any root is quantized (`div_qua`) while its mass reading stays
cumulative, and classifier and non-classifier languages differ only in whether the
individuating head is spelled out and further restricted by a classifier (`DivCL`).

The order of the two heads, individuation below counting, follows from their semantic
types: individuation takes a cumulative predicate to a quantized one, and counting takes a
quantized predicate to a measured one, so the counting head has no well-typed input unless
the individuating head is projected below it (`status`, `q_below_num`); this is the order
the extended projection's F-values encode (`fValue_Q_lt_Num`). Borer sets this against
[chierchia-1998]'s lexical mass/count distinction and its cross-linguistic parameter: the
two accounts agree that mass denotations are cumulative and count denotations quantized,
and disagree on whether the distinction is a property of nouns or of the spine.

## References

* [borer-2005]
* [chierchia-1998]
-/

namespace Borer2005

open Mereology Minimalist

variable {α : Type*} [SemilatticeSup α] (P : α → Prop)

/-! ### Individuation and counting -/

/-- Borer's individuating head (CL#, the `Q` head) restricts a root predicate to its
atoms — the singular-number restriction `Number.atomsOf`. -/
abbrev Div : α → Prop := Number.atomsOf P

/-- Individuated predicates are quantized: the count reading of any root is `QUA`. -/
theorem div_qua : QUA (Div P) := qua_of_atom fun _ h => h.2

/-- Sums of individuated units of a cumulative root stay in the root's denotation:
pluralities of beer-units are beer. -/
theorem algClosure_div_sub (hCum : CUM P) : ∀ x, AlgClosure (Div P) x → P x :=
  fun x hx => (algClosure_of_cum hCum).1 (algClosure_mono (fun _ h => h.1) x hx)

/-- The number head counts individuated units: *three beers* is the quantizing
modification of `Div √BEER` to measure `3`. -/
def count {M : Type*} (μ : α → M) (n : M) : α → Prop := QMOD (Div P) μ n

theorem count_qua {M : Type*} (μ : α → M) (n : M) : QUA (count P μ n) :=
  (div_qua P).subset fun _ h => h.1

/-- In a classifier language the classifier fills the individuating head and restricts
which atoms count as units (Mandarin *zhī* to small animals); non-classifier languages
individuate covertly, with the trivial classifier (`divCL_true`). -/
abbrev DivCL (cl : α → Prop) : α → Prop := Div fun x => P x ∧ cl x

theorem divCL_qua (cl : α → Prop) : QUA (DivCL P cl) := div_qua _

theorem divCL_sub_div {cl : α → Prop} {x : α} (h : DivCL P cl x) : Div P x := ⟨h.1.1, h.2⟩

theorem divCL_true : DivCL P (fun _ => True) = Div P := by
  funext x; simp [DivCL, Div, Number.atomsOf]

/-! ### The nominal spine -/

/-- A nominal spine is count when it projects the individuating head. -/
abbrev Countable (spine : List Cat) : Prop := Cat.Q ∈ spine

example : Countable [.N, .n, .Q, .Num, .D] := by decide
example : ¬ Countable [.N, .n, .D] := by decide

/-- The mereological type of a nominal denotation along the spine: cumulative (a root),
quantized (individuated), or measured (counted). -/
inductive Status where
  | cum
  | qua
  | measured
  deriving DecidableEq, Repr

/-- The typing of the semantically active heads: individuation takes cumulative to
quantized (`div_qua`) and counting takes quantized to measured (`count_qua`); the other
heads are transparent. -/
def typing : Cat → Option (Status × Status)
  | .Q => some (.cum, .qua)
  | .Num => some (.qua, .measured)
  | _ => none

/-- The type of a spine's denotation, composed bottom-up from a cumulative root; `none`
when some head receives input of the wrong type. -/
def status (spine : List Cat) : Option Status :=
  spine.foldl (fun s c => s.bind fun s => match typing c with
    | some (i, o) => if s = i then some o else none
    | none => some s) (some .cum)

/-- Individuation below counting is the only well-typed order of the two heads. -/
theorem q_below_num :
    status [.N, .n, .Q, .Num] = some .measured ∧ status [.N, .n, .Num, .Q] = none := by
  decide

/-- Every truncation of the spine is well-typed — the bare root is mass, the individuated
root a single unit, the counted root a measured plurality — except counting without
individuation. -/
theorem status_truncations :
    status [.N, .n] = some .cum ∧ status [.N, .n, .Q] = some .qua ∧
      status [.N, .n, .Num] = none := by
  decide

/-- The extended projection's F-values place the individuating head below the counting
head. -/
theorem fValue_Q_lt_Num : fValue .Q < fValue .Num := by decide

end Borer2005
