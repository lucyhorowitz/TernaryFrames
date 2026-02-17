/-
Copyright (c) 2026 Lucy Horowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz
-/
import Mathlib.Data.Set.Defs

/-!
# Bilateral Incompatibility Semantics

This file formalizes the framework of incoherence-space semantics, following the
presentation in Simonelli's "Implication Space Semantics as Bilateral Incompatibility
Semantics" and the blog post "Incoherence-space semantics" by L. Horowitz.

The core idea: semantic values are assigned to *positions* consisting in assertions and
denials, and the semantic value of a position is its *incoherence closure* — the set of
positions that incompatibility-entail it.

We work at maximum generality: positions are `List (Move L)`, so that order and repetition
are tracked. Quotienting to multisets (exchange) or sets (exchange + contraction) can be
considered as additional structure.

## Main definitions

* `Move`: A signed sentence — either an assertion (`Move.assert`) or a denial (`Move.deny`).
* `IncoherenceSpace`: A type of sentences equipped with a set of incoherent positions,
  satisfying the constraint that asserting and denying the same atomic is incoherent.
* `IncoherenceSpace.perp`: The incoherence profile `X⊥` of a set of positions.
* `IncoherenceSpace.dperp`: The incoherence closure `X⊥⊥`.
* `IncoherenceSpace.fusion`: The fusion operation `X ⋓ Y` on sets of positions.

## References

* Simonelli, R. (2025). "Implication Space Semantics as Bilateral Incompatibility Semantics."
* Horowitz, L. (2025). "Incoherence-space semantics." Topos Institute Blog.
* Kaplan, D. (2022). Dissertation.
* Brandom, R. (2008). *Between Saying and Doing*. Oxford University Press.
* Hlobil, U. and Brandom, R. (2024). *Reasons for Logic, Logic for Reasons*.
-/

universe u

/-- A `Move` over a language `L` is a signed sentence: either an assertion `+A` or a
denial `−A`. -/
inductive Move (L : Type u) where
  /-- Assert sentence `A`. -/
  | assert : L → Move L
  /-- Deny sentence `A`. -/
  | deny : L → Move L
  deriving DecidableEq

namespace Move

/-- Flip the sign of a move: assertion becomes denial and vice versa. -/
def flip {L : Type u} : Move L → Move L
  | assert A => deny A
  | deny A => assert A

@[simp]
theorem flip_flip {L : Type u} (m : Move L) : m.flip.flip = m := by
  cases m <;> rfl

@[simp]
theorem flip_assert {L : Type u} (A : L) : (Move.assert A).flip = Move.deny A := rfl

@[simp]
theorem flip_deny {L : Type u} (A : L) : (Move.deny A).flip = Move.assert A := rfl

end Move

/-- An `IncoherenceSpace` on a language `L` specifies a set of *incoherent* positions
(where a position is a `List (Move L)`).

The constraints are:
* The empty position is coherent (`empty_coherent`).
* Any position containing both `+p` and `−p` for an atomic `p` is incoherent
  (`atomic_incoherent`).

Persistence is **not** assumed: `Γ ∈ I` does not imply `Γ ++ Δ ∈ I`. This is the key
innovation enabling the accommodation of defeasible material incompatibilities. -/
class IncoherenceSpace (L : Type u) where
  /-- The set of incoherent positions. -/
  I : Set (List (Move L))
  /-- The empty position is coherent. -/
  empty_coherent : [] ∉ I
  /-- Asserting and denying the same sentence yields an incoherent position. -/
  atomic_incoherent : ∀ (p : L) (Γ : List (Move L)),
    Move.assert p ∈ Γ → Move.deny p ∈ Γ → Γ ∈ I

namespace IncoherenceSpace

variable {L : Type u} [IncoherenceSpace L]

/-! ### Incoherence profiles

The incoherence profile of a set `X` of positions is the set of positions `Γ` such that
`Γ ++ Δ ∈ I` for every `Δ ∈ X`. The double profile `X⊥⊥` (incoherence closure) is a
closure operator and gives the semantic values in ISS. -/

section Perp

/-- The incoherence profile of a set of positions:
`perp X = {Γ | ∀ Δ ∈ X, Γ ++ Δ ∈ I}`. -/
def perp (X : Set (List (Move L))) : Set (List (Move L)) :=
  {Γ | ∀ Δ ∈ X, Γ ++ Δ ∈ I}

/-- The incoherence closure (double profile):
`dperp X = perp (perp X) = X⊥⊥`. -/
def dperp (X : Set (List (Move L))) : Set (List (Move L)) :=
  perp (perp X)

theorem mem_perp_iff {X : Set (List (Move L))} {Γ : List (Move L)} :
    Γ ∈ perp X ↔ ∀ Δ ∈ X, Γ ++ Δ ∈ I :=
  Iff.rfl

theorem mem_dperp_iff {X : Set (List (Move L))} {Γ : List (Move L)} :
    Γ ∈ dperp X ↔ ∀ Δ ∈ perp X, Γ ++ Δ ∈ I :=
  Iff.rfl

/-! #### Antitone behavior of perp -/

/-- `perp` is antitone: if `X ⊆ Y`, then `perp Y ⊆ perp X`. -/
theorem perp_antimono {X Y : Set (List (Move L))} (h : X ⊆ Y) : perp Y ⊆ perp X :=
  fun _ hΓ Δ hΔ => hΓ Δ (h hΔ)

/-- `dperp` is monotone: if `X ⊆ Y`, then `dperp X ⊆ dperp Y`. -/
theorem dperp_mono {X Y : Set (List (Move L))} (h : X ⊆ Y) : dperp X ⊆ dperp Y :=
  perp_antimono (perp_antimono h)

end Perp

/-! ### Incompatibility entailment

`Δ` incompatibility-entails `Γ` when `perp {Γ} ⊆ perp {Δ}`, i.e., everything incompatible
with `Γ` is also incompatible with `Δ`. Equivalently, `Δ ∈ dperp {Γ}`. -/

section Entailment

/-- Incompatibility entailment between positions: `Δ` incompatibility-entails `Γ` when
everything incompatible with `Γ` is also incompatible with `Δ`. -/
def IncompEntails (Δ Γ : List (Move L)) : Prop :=
  perp {Γ} ⊆ perp {Δ}

scoped infix:50 " ⊨ᵢ " => IncoherenceSpace.IncompEntails

/-- Incompatibility entailment is reflexive. -/
theorem incompEntails_refl (Γ : List (Move L)) : Γ ⊨ᵢ Γ :=
  fun _ h => h

/-- Incompatibility entailment is transitive. -/
theorem incompEntails_trans {Γ Δ Θ : List (Move L)}
    (h₁ : Γ ⊨ᵢ Δ) (h₂ : Δ ⊨ᵢ Θ) : Γ ⊨ᵢ Θ :=
  fun _ h => h₁ (h₂ h)

end Entailment

/-! ### Fusion of sets of positions

The fusion operation `X ⋓ Y` combines two sets of positions by taking all pairwise
concatenations. This is the key multiplicative operation in the semantics. -/

section Fusion

variable {L : Type u}

/-- Fusion of two sets of positions: `X ⋓ Y = {Γ ++ Δ | Γ ∈ X, Δ ∈ Y}`. -/
def fusion (X Y : Set (List (Move L))) : Set (List (Move L)) :=
  {Γ | ∃ Δ ∈ X, ∃ Θ ∈ Y, Γ = Δ ++ Θ}

scoped infixl:70 " ⋓ " => IncoherenceSpace.fusion

theorem mem_fusion_iff {X Y : Set (List (Move L))} {Γ : List (Move L)} :
    Γ ∈ fusion X Y ↔ ∃ Δ ∈ X, ∃ Θ ∈ Y, Γ = Δ ++ Θ :=
  Iff.rfl

/-- Fusion is associative (since `++` on lists is associative). -/
theorem fusion_assoc (X Y Z : Set (List (Move L))) :
    fusion (fusion X Y) Z = fusion X (fusion Y Z) := by
  apply Set.ext; intro Γ; simp only [mem_fusion_iff]; constructor
  · rintro ⟨ΔΘ, ⟨Δ, hΔ, Θ, hΘ, rfl⟩, Ψ, hΨ, rfl⟩
    exact ⟨Δ, hΔ, Θ ++ Ψ, ⟨Θ, hΘ, Ψ, hΨ, rfl⟩, by rw [List.append_assoc]⟩
  · rintro ⟨Δ, hΔ, ΘΨ, ⟨Θ, hΘ, Ψ, hΨ, rfl⟩, rfl⟩
    exact ⟨Δ ++ Θ, ⟨Δ, hΔ, Θ, hΘ, rfl⟩, Ψ, hΨ, by rw [List.append_assoc]⟩

/-- Fusion with the singleton of the empty list on the left is the identity. -/
theorem fusion_nil_left (X : Set (List (Move L))) : fusion {[]} X = X := by
  apply Set.ext; intro Γ; simp only [mem_fusion_iff]; constructor
  · rintro ⟨Δ, hΔ, Θ, hΘ, rfl⟩
    cases hΔ; simpa
  · intro hΓ
    exact ⟨[], rfl, Γ, hΓ, by simp⟩

/-- Fusion with the singleton of the empty list on the right is the identity. -/
theorem fusion_nil_right (X : Set (List (Move L))) : fusion X {[]} = X := by
  apply Set.ext; intro Γ; simp only [mem_fusion_iff]; constructor
  · rintro ⟨Δ, hΔ, Θ, hΘ, rfl⟩
    cases hΘ; simpa
  · intro hΓ
    exact ⟨Γ, hΓ, [], rfl, by simp⟩

end Fusion

end IncoherenceSpace
