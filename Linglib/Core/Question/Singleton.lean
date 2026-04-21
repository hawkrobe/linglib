import Linglib.Core.Question.Hamblin

/-!
# Question — singleton-alternative predicate
@cite{bhatt-dayal-2020} @cite{roelofsen-farkas-2015}

A foundational predicate over `Question W`: an issue is *singleton* iff its
alternative set is a singleton, i.e. there is exactly one maximal
resolving proposition. This isolates the algebraic shape that drives
several cross-linguistic question-particle analyses:

- @cite{bhatt-dayal-2020}'s analysis of Hindi-Urdu *kya:* (eq. 23):
  the polar question particle presupposes that its sister denotes a
  question whose alternative set is a singleton (the "highlighted"
  cell, in the sense of @cite{roelofsen-farkas-2015}).
- the parallel analysis of Mandarin *nandao* that
  @cite{bhatt-dayal-2020} fn. 11 cites as the model for kya:.

Declarative contents are exactly the singleton ones (under finiteness
of `props`); the standard two-cell polar `polar p` (with both `p` and
`pᶜ` as alternatives) is **not** singleton when `p` is non-trivial.

The "highlighted polar" terminology of @cite{roelofsen-farkas-2015} is a
notational alias for `declarative p` in the inquisitive setting; we do
not introduce a separate definition because the singleton alternative is
the only feature that distinguishes it from the two-cell `polar p`, and
that feature is `IsSingleton (declarative p)` itself.

Particle-specific bindings (kya:, nandao) live in their respective study
files (`Phenomena/Questions/Studies/`) and use `IsSingleton` /
`SingletonQuestion` directly.
-/

namespace Core

namespace Question

universe u
variable {W : Type u}

/-! ### `IsSingleton` predicate -/

/-- An inquisitive content is **singleton** iff its alternative set
    contains exactly one element. The shape encoded by the singleton
    presupposition of @cite{bhatt-dayal-2020}'s eq. 23 (kya:) and the
    parallel nandao analysis cited in @cite{bhatt-dayal-2020} fn. 11. -/
def IsSingleton (P : Question W) : Prop :=
  ∃ p, alt P = {p}

/-- A `declarative p` content is singleton — its unique alternative is
    `p` itself. The base case for all singleton-presuppositional
    constructions. -/
theorem isSingleton_declarative (p : Set W) :
    IsSingleton (declarative p) :=
  ⟨p, alt_declarative p⟩

@[simp] theorem isSingleton_top : IsSingleton (⊤ : Question W) :=
  ⟨Set.univ, alt_top⟩

@[simp] theorem isSingleton_bot : IsSingleton (⊥ : Question W) :=
  ⟨∅, alt_bot⟩

/-- **Subsingleton + nonempty characterization**: an issue is singleton
    iff its alternative set is both `Subsingleton` and `Nonempty` in
    mathlib's sense. Bridges `IsSingleton` to mathlib's set API. -/
theorem isSingleton_iff_subsingleton_and_nonempty (P : Question W) :
    IsSingleton P ↔ (alt P).Subsingleton ∧ (alt P).Nonempty := by
  refine ⟨?_, ?_⟩
  · rintro ⟨p, hp⟩
    refine ⟨?_, ?_⟩
    · rw [hp]; exact Set.subsingleton_singleton
    · rw [hp]; exact Set.singleton_nonempty p
  · rintro ⟨hsub, ⟨p, hp⟩⟩
    refine ⟨p, ?_⟩
    apply Set.eq_singleton_iff_unique_mem.mpr
    refine ⟨hp, ?_⟩
    intro q hq
    exact hsub hq hp

/-- A declarative content is singleton with witness `info P`: combines
    `isDeclarative_iff_alt_eq_singleton` with the definition of
    `IsSingleton`. -/
theorem IsSingleton.of_isDeclarative {P : Question W}
    (h : P.isDeclarative) : IsSingleton P :=
  ⟨P.info, (isDeclarative_iff_alt_eq_singleton P).mp h⟩

/-- **Two-distinct-alternatives obstruction**: if `P` has two distinct
    alternatives, `P` is not singleton. The contrapositive: singleton
    issues admit at most one alternative. Drives the polar Q failure
    case below. -/
theorem not_isSingleton_of_two_alternatives (P : Question W)
    {p₁ p₂ : Set W} (h₁ : p₁ ∈ alt P) (h₂ : p₂ ∈ alt P) (hne : p₁ ≠ p₂) :
    ¬ IsSingleton P := by
  rintro ⟨p, hp⟩
  rw [hp, Set.mem_singleton_iff] at h₁ h₂
  exact hne (h₁.trans h₂.symm)

/-- The two-cell polar question `polar p` (in the standard
    @cite{ciardelli-groenendijk-roelofsen-2018} / Hamblin sense) is
    **not** singleton when `p` is non-trivial — it has two distinct
    alternatives `p` and `pᶜ`. This is the structural reason the
    @cite{bhatt-dayal-2020} kya:-style "singleton presupposition"
    cannot be satisfied by a two-cell polar Q; it requires the
    one-cell highlighted polar of @cite{roelofsen-farkas-2015}
    (= `declarative p`). -/
theorem not_isSingleton_polar_of_nontrivial {p : Set W}
    (hne : p ≠ ∅) (hnu : p ≠ Set.univ) :
    ¬ IsSingleton (polar p) := by
  have halt : alt (polar p) = {p, pᶜ} := alt_polar_of_nontrivial hne hnu
  have hp_alt : p ∈ alt (polar p) := by
    rw [halt]; exact Set.mem_insert _ _
  have hpc_alt : pᶜ ∈ alt (polar p) := by
    rw [halt]; exact Set.mem_insert_of_mem _ rfl
  have hne_alt : p ≠ pᶜ := by
    intro h
    apply hne
    ext w
    refine ⟨?_, fun h => h.elim⟩
    intro hw
    have : w ∈ pᶜ := h ▸ hw
    exact this hw
  exact not_isSingleton_of_two_alternatives (polar p) hp_alt hpc_alt hne_alt

/-! ### `SingletonQuestion` subtype

The mathlib-style packaging of "issue with singleton-alternative
presupposition satisfied". Used by particle-specific study files
(kya:, nandao) as the type of felicitous sister content. -/

/-- The **subtype of singleton issues** — issues whose alternative set
    is a singleton. Used as the well-typed sister-content for
    singleton-presuppositional Q-particles
    (@cite{bhatt-dayal-2020}, kya: eq. 23 and parallel nandao analysis
    cited in fn. 11). The mathlib pattern for "predicate + partial
    function" pairs: rather than `Option`-valued partial interpretation,
    use a subtype. -/
def SingletonQuestion (W : Type u) : Type u :=
  {Q : Question W // IsSingleton Q}

namespace SingletonQuestion

/-- The underlying issue of a `SingletonQuestion` — the truth-conditional
    content delivered when the singleton presupposition is satisfied.
    @cite{bhatt-dayal-2020} eq. 23: `⟦kya:⟧` returns its sister `Q`
    unchanged on felicitous inputs. -/
def issue (Q : SingletonQuestion W) : Question W := Q.val

/-- The unique alternative of a singleton issue (the "highlighted" cell
    in @cite{roelofsen-farkas-2015}'s sense). -/
noncomputable def witness (Q : SingletonQuestion W) : Set W :=
  Q.property.choose

theorem alt_eq_singleton_witness (Q : SingletonQuestion W) :
    alt Q.issue = {Q.witness} :=
  Q.property.choose_spec

/-- Constructor from a declarative — the canonical felicitous input. -/
def ofDeclarative (p : Set W) : SingletonQuestion W :=
  ⟨declarative p, isSingleton_declarative p⟩

@[simp] theorem ofDeclarative_issue (p : Set W) :
    (ofDeclarative p).issue = declarative p := rfl

end SingletonQuestion

end Question

end Core
