/-!
# Chatzikyriakidis & Luo (2020): MTT semantics via coercive subtyping
[chatzikyriakidis-luo-2020]

Modern Type Theory (MTT) analysis where common nouns denote *types*,
not predicates, and subtyping is *coercive* — `A ≤_c B` whenever
there is a unique implicit coercion `c : A → B` that the elaborator
inserts on demand (paper §2.4, eqs. CA/CD on p. 40).

**Coercive vs subsumptive.** C&L explicitly reject subsumptive
subtyping for MTT (p. 39): "subsumptive subtyping is incompatible
with some key properties of modern type theories and, as a
consequence, cannot be employed for an MTT." This file uses Lean's
`Coe` typeclass, which is the canonical coercive-subtyping mechanism
(value-level coercion functions, automatic elaboration-time
insertion).

**Coherence.** Paper p. 40 fn 18 requires unique coercions between
any two types. Lean's typeclass resolution picks an instance by
priority rather than enforcing uniqueness; coherence is therefore
the file author's responsibility, documented via `CoherentCoercion`
Props below.

## Main definitions

* Paper §3.2.1 CNs-as-types: `Human`, `Book` as inductive types.
* Paper §3.2.2 eq. 3.30-3.33 paradigm: `Man = Σx:Human.male(x)`,
  `heavy_book = Σx:Book.heavy(x)`, `read : Human → Book → Prop`,
  with `read john_man warAndPeace_heavy` well-typed via projective
  coercive subtyping.
* `CoherentCoercion A B`: Prop axiom stating any two `Coe` paths
  from `A` to `B` agree (paper coherence requirement, not enforced
  by Lean — proved per-instance).

## References

* [chatzikyriakidis-luo-2020] §2.4 (coercive subtyping),
  §3.2.1 (CNs as types), §3.2.2 (subtyping in MTT-semantics,
  esp. eq. 3.30-3.33 and projective subtyping at eq. 3.33).
-/

namespace ChatzikyriakidisLuo2020

/-! ### Paper §3.2.1: CNs as types -/

inductive Human where
  | john
  | mary
  | bob
  deriving DecidableEq, Repr

inductive Book where
  | warAndPeace
  | hamlet
  deriving DecidableEq, Repr

/-! ### Paper §3.2.2: projective subtyping via Σ-types

`Man := Σx:Human.male(x)` (paper eq. 2.41); `Man ≤_π₁ Human`
(eq. 2.42, p. 41) — the first projection is the coercion. In Lean,
this is `{h : Human // Male h}` with `Coe ... Human` via
`Subtype.val`. -/

def Male : Human → Prop
  | .john => True
  | .mary => False
  | .bob  => True

abbrev Man := { h : Human // Male h }

instance : Coe Man Human where coe := Subtype.val

/-- `Heavy : Book → Prop`; `heavy_book := Σx:Book.heavy(x)`
    (paper §3.2.2, eq. 3.31). -/
def Heavy : Book → Prop
  | .warAndPeace => True
  | .hamlet      => False

abbrev HeavyBook := { b : Book // Heavy b }

instance : Coe HeavyBook Book where coe := Subtype.val

/-! ### Paper eq. 3.30-3.33 paradigm: `read john W&P` -/

/-- Paper §3.2.2: `read : Human → Book → Prop`. -/
def read : Human → Book → Prop := fun _ _ => True

/-- `johnMan : Man` (John is a Man = a male Human). -/
def johnMan : Man := ⟨.john, trivial⟩

/-- `warAndPeaceHeavy : HeavyBook` (War & Peace is a heavy book). -/
def warAndPeaceHeavy : HeavyBook := ⟨.warAndPeace, trivial⟩

/-- **Paper eq. 3.32 paradigm theorem.** `read johnMan warAndPeaceHeavy`
    is well-typed: Lean's elaborator inserts the coercions
    `Man → Human` and `HeavyBook → Book` automatically. This is the
    paper's signature example showing why projective coercive
    subtyping matters — neither `johnMan : Human` nor
    `warAndPeaceHeavy : Book` holds judgmentally, but `read` applies
    by way of the Coe instances. -/
example : Prop := read johnMan warAndPeaceHeavy

/-- The expanded form: applying the explicit coercions yields the
    same term Lean's elaborator produces implicitly (paper rule CD,
    p. 40: `f(a) = f(c(a))`). -/
theorem read_johnMan_wpHeavy_expanded :
    read johnMan warAndPeaceHeavy = read (↑johnMan : Human) (↑warAndPeaceHeavy : Book) := rfl

/-! ### Coherence (paper p. 41 fn 18) -/

/-- Coherence of coercions between two types: any two `Coe`-derived
    coercion functions agree. Lean's typeclass resolution does not
    enforce this (it picks by priority); the user declares and proves
    coherence on a case-by-case basis. -/
class CoherentCoercion (A B : Type) [Coe A B] : Prop where
  coh : ∀ (c₁ c₂ : A → B), c₁ = (Coe.coe : A → B) → c₂ = (Coe.coe : A → B) → c₁ = c₂

/-- The Man-to-Human coercion is trivially coherent: there is only
    one `Coe` instance declared. -/
instance : CoherentCoercion Man Human where
  coh _ _ h₁ h₂ := h₁.trans h₂.symm

/-- The HeavyBook-to-Book coercion is trivially coherent. -/
instance : CoherentCoercion HeavyBook Book where
  coh _ _ h₁ h₂ := h₁.trans h₂.symm

/-! ### Paper §3.2.2: subtyping propagates through function types

C&L p. 55: if `A' ≤ A` and `B ≤ B'`, then `A → B ≤ A' → B'`
(contravariance + covariance). In Lean this is automatic — any
`f : Human → Prop` accepts `m : Man` via Coe insertion. -/

def Talks : Human → Prop := fun _ => True

example : Prop := Talks johnMan  -- Lean inserts `Coe Man Human` for the argument

/-! ### Failure case: missing coercion is a type error

The paper's selectional-restriction argument: if there is no
`Coe Book Human`, then `Talks warAndPeace` fails to elaborate.
Lean's type error IS the paper's "category mistake" (paper §3.2.1,
table 3.1 commentary). The following would not typecheck:

```
example : Prop := Talks Book.warAndPeace
```
-/

end ChatzikyriakidisLuo2020
