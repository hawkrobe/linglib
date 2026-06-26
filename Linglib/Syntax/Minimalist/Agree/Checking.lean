import Linglib.Syntax.Minimalist.Features
import Linglib.Syntax.Minimalist.Agree.Basic

/-!
# Host-dependent interpretability and ordered feature activation
[chomsky-1995] [hewett-2026]

Two feature utilities that survive the retirement of the 1995 checking **lifecycle**. The
`TrackedFeature` activate→check→erase state machine and its `convergesAtLF`/`convergesAtSpellOut`
convergence predicates — Old-Minimalism feature checking — are removed: consistency of feature
assignments across substructures is now the MCB Birkhoff renormalization
`Minimalist.headConsistency` (the "single recursive map", `Agree/Consistency.lean`), a post-syntactic
filter over the feature-free core, not a per-feature state machine.

What remains:

- **Host-dependent interpretability** (`isInterpretableOn`): whether a feature type is
  +/−Interpretable on a given host category ([chomsky-1995] Ch. 4 — categorial and nominal
  φ-features are interpretable; Case and functional-head φ-features are not).
- **Ordered activation indices** (`ActivationIndex`, [hewett-2026] ex. (23)): a feature carries an
  ordered tuple of category keys; each c-commanding head strips the leftmost matching key, and an
  exhausted tuple is `.active`. The formal core of Hewett's *Joint Selection via Activate* — a
  [preminger-2014] "derivational time bomb". (Reformulating [hewett-2026]'s selection itself in
  terms of the Birkhoff machinery is future work.)
-/

namespace Minimalist

/-! ### Host-dependent interpretability -/

/-- Whether a feature type is interpretable on a given host category.

    [chomsky-1995] Ch 4: Categorial features and φ-features of
    nouns are +Interpretable. Case features, φ-features on functional
    heads (T, v, C), and EPP/strong features are –Interpretable.

    This encodes the default mapping. Individual languages or analyses
    may override (e.g., [zeijlstra-2012] treats embedded tense as
    uninterpretable in SOT languages). -/
def isInterpretableOn (fv : FeatureVal) (host : Cat) : Interpretability :=
  match fv.inherentInterpretability with
  | some i => i  -- host-independent features
  | none => match fv with
    -- Phi-features: interpretable on N/D (substantive), uninterpretable on T/v/C (functional)
    | .phi _ => match host with
      | .N | .D => .interpretable
      | _ => .uninterpretable
    -- Wh, Q, Foc, Rel: interpretable on C (their natural host)
    | .wh _ | .q _ | .foc _ | .rel _ =>
      if host == .C then .interpretable else .uninterpretable
    -- Tense, finite: interpretable on T
    | .tense _ | .finite _ =>
      if host == .T then .interpretable else .uninterpretable
    -- Fallback: interpretable (conservative)
    | _ => .interpretable

/-- Phi on N is interpretable; phi on T is not. -/
theorem phi_on_N_interpretable (pf : PhiFeature) :
    isInterpretableOn (.phi pf) .N = .interpretable := rfl

theorem phi_on_T_uninterpretable (pf : PhiFeature) :
    isInterpretableOn (.phi pf) .T = .uninterpretable := rfl

/-! ### Feature activation status -/

/-- The activation state of a feature: `.inactive` while its activation tuple is non-empty
    (a [preminger-2014] "derivational time bomb"), `.active` once the tuple is exhausted. The
    codomain of `ActivationIndex.toStatus`. -/
inductive FeatureStatus where
  /-- Present but dormant: an unexhausted activation tuple, awaiting licensing by the right
      c-commanding heads ([hewett-2026] ex. (23)). -/
  | inactive
  /-- Fully activated: the tuple is exhausted and the feature is accessible. -/
  | active
  deriving Repr, DecidableEq

/-! ### Ordered activation tuples ([hewett-2026] ex. (23))

[hewett-2026] ex. (23) (adapted from [merchant-2015]): a feature
can be indexed by an ordered tuple of category keys `(c₁, …, cₙ)`. Each
c-commanding head bearing key `k` strips `c₁` from the tuple **if `k = c₁`**
(matching activation). When the tuple is exhausted the feature transitions
from `.inactive` to `.active`.

`ActivationIndex α` is parametric over the key type `α` — for Semitic
l-selection `α` combines `Cat` and `SemiticTemplate`, but the mechanism
generalizes to any domain where features require ordered multi-head
activation (e.g., applicatives, serial verbs). -/

/-- An ordered tuple of activation keys. Stripping proceeds left-to-right:
    only the leftmost key can be matched at any derivational step. -/
structure ActivationIndex (α : Type) [BEq α] where
  /-- Keys remaining to be stripped. Empty = fully activated. -/
  remaining : List α
  deriving Repr

/-- Attempt to strip the leftmost key. Succeeds only if `key` matches
    the head of the tuple (matching activation). Non-matching keys and
    already-empty tuples are no-ops. -/
def ActivationIndex.activate {α : Type} [BEq α] (idx : ActivationIndex α)
    (key : α) : ActivationIndex α :=
  match idx.remaining with
  | k :: rest => if k == key then ⟨rest⟩ else idx
  | [] => idx

/-- Is the tuple fully stripped? -/
def ActivationIndex.isFullyActive {α : Type} [BEq α]
    (idx : ActivationIndex α) : Bool :=
  idx.remaining.isEmpty

/-- Map activation state to the `FeatureStatus`: non-empty
    tuples are `.inactive`, empty tuples are `.active`. -/
def ActivationIndex.toStatus {α : Type} [BEq α]
    (idx : ActivationIndex α) : FeatureStatus :=
  if idx.isFullyActive then .active else .inactive

/-- Matching key strips the head. -/
theorem activate_matching_strips {α : Type} [BEq α] [LawfulBEq α]
    (k : α) (rest : List α) :
    (ActivationIndex.mk (k :: rest) : ActivationIndex α).activate k
    = ⟨rest⟩ := by
  simp [ActivationIndex.activate]

/-- Non-matching key is a no-op. -/
theorem activate_nonmatching_noop {α : Type} [BEq α] [LawfulBEq α]
    (k₁ k₂ : α) (rest : List α) (h : k₁ ≠ k₂) :
    (ActivationIndex.mk (k₁ :: rest) : ActivationIndex α).activate k₂
    = ⟨k₁ :: rest⟩ := by
  simp [ActivationIndex.activate, beq_iff_eq, h]

/-- Empty tuple is fully active. -/
theorem empty_is_active {α : Type} [BEq α] :
    (ActivationIndex.mk (α := α) []).isFullyActive = true := rfl

/-- Non-empty tuple is not fully active. -/
theorem nonempty_is_inactive {α : Type} [BEq α] (k : α) (rest : List α) :
    (ActivationIndex.mk (k :: rest) : ActivationIndex α).isFullyActive
    = false := rfl

/-- Empty tuple maps to `.active` status. -/
theorem empty_toStatus_active {α : Type} [BEq α] :
    (ActivationIndex.mk (α := α) []).toStatus = .active := rfl

/-- Non-empty tuple maps to `.inactive` status. -/
theorem nonempty_toStatus_inactive {α : Type} [BEq α]
    (k : α) (rest : List α) :
    (ActivationIndex.mk (k :: rest) : ActivationIndex α).toStatus
    = .inactive := rfl

/-- Activation on an already-empty tuple is a no-op. -/
theorem activate_empty_noop {α : Type} [BEq α] (key : α) :
    (ActivationIndex.mk (α := α) []).activate key = ⟨[]⟩ := rfl

/-- Full activation chain: stripping each key in order yields `.active`. -/
theorem full_activation_chain {α : Type} [BEq α] [LawfulBEq α]
    (k₁ k₂ : α) :
    let idx : ActivationIndex α := ⟨[k₁, k₂]⟩
    (idx.activate k₁ |>.activate k₂).toStatus = .active := by
  simp [ActivationIndex.activate, ActivationIndex.toStatus,
        ActivationIndex.isFullyActive]

end Minimalist
