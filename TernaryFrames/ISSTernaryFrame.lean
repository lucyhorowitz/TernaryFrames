/-
Copyright (c) 2026 Lucy Horowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz
-/
import TernaryFrames.Basic
import TernaryFrames.DayConvolution

/-!
# Incoherence Spaces as Ternary Frames

This file formalizes the connection between incoherence spaces and ternary frames,
as described in Horowitz (2025) "Incoherence-space semantics," Section 3.

## Architecture

- **Worlds**: positions `List (Move L)`
- **Semantic values**: incoherence-closed sets `ClosedSet L ⊆ Set (List (Move L))`

`ClosedSet L` is **not** a ternary frame; it is the quantale of semantic values (propositions)
indexed over the positions-as-worlds. The ternary frame instance lives on `List (Move L)`.

## The ternary relation

Following the blog post, we define:
`R(Γ, Δ, Θ) ↔ Θ ⊨ᵢ Γ ++ Δ`, i.e., `perp {Γ ++ Δ} ⊆ perp {Θ}`.
This says "Θ is achievable from combining Γ and Δ" (Γ + Δ ≤_IE Θ in blog notation).

The associated preorder is `Γ ≤ Δ ↔ Δ ⊨ᵢ Γ`, i.e., `{Γ}⊥ ⊆ {Δ}⊥` in the blog notation.

## Main definitions and results

* `instPreorderPos`: `List (Move L)` is a preorder via `Γ ≤ Δ ↔ Δ ⊨ᵢ Γ`.
* `instTernaryFramePos`: `List (Move L)` is a `TernaryFrame` via `R Γ Δ Θ ↔ Θ ⊨ᵢ Γ ++ Δ`.
* `R_pos_iff`: Unfolding the ternary relation to a perp-subset statement.
* `instIsCommutativePos`: Under `[IsContainment L]`, the frame is commutative.
* `fusion_sub_tensor`: `X ⋓ Y ⊆ TernaryFrame.tensor X Y` (bare `IncoherenceSpace`).
* `tensor_sub_dtensor`: `TernaryFrame.tensor X.carrier Y.carrier ⊆ (X ⊗ᶜ Y).carrier`
  under `[IsExchange L]`.
* `dtensor_eq_dperp_tensor`: `(X ⊗ᶜ Y).carrier = dperp (TernaryFrame.tensor X.carrier Y.carrier)`
  under `[IsExchange L]`.

## References

* Horowitz, L. (2025). "Incoherence-space semantics." Topos Institute Blog.
-/

universe u

open IncoherenceSpace IncoherenceSpace.ClosedSet

namespace IncoherenceSpace

variable {L : Type u} [IncoherenceSpace L]

/-! ### Preorder on positions -/

section PositionPreorder

/-- The preorder on positions given by incompatibility entailment:
`Γ ≤ Δ` iff `{Γ}⊥ ⊆ {Δ}⊥`, i.e., `Δ ⊨ᵢ Γ` in Lean notation.

This matches the blog's `p ≤_IE q` iff `{p}⊥ ⊆ {q}⊥`,
meaning that `q` is inferentially stronger than `p`. -/
instance instPreorderPos : Preorder (List (Move L)) where
  le Γ Δ := Δ ⊨ᵢ Γ
  le_refl Γ := incompEntails_refl Γ
  le_trans _ _ _ h₁ h₂ := incompEntails_trans h₂ h₁

theorem le_pos_iff {Γ Δ : List (Move L)} : Γ ≤ Δ ↔ Δ ⊨ᵢ Γ := Iff.rfl

/-- `Γ ≤ Δ` iff `perp {Γ} ⊆ perp {Δ}`, matching the blog's `{Γ}⊥ ⊆ {Δ}⊥`. -/
theorem le_pos_iff' {Γ Δ : List (Move L)} : Γ ≤ Δ ↔ perp {Γ} ⊆ perp {Δ} := Iff.rfl

end PositionPreorder

/-! ### TernaryFrame on positions -/

section PositionTernaryFrame

/-- The ternary frame on positions: `R Γ Δ Θ ↔ Θ ⊨ᵢ Γ ++ Δ` (`perp {Γ ++ Δ} ⊆ perp {Θ}`).

"Θ is achievable from combining Γ and Δ": it has at least as many witnesses against it
as the combination Γ ++ Δ, i.e. Γ + Δ ≤_IE Θ in the blog's order. -/
instance instTernaryFramePos : TernaryFrame (List (Move L)) where
  R Γ Δ Θ := Θ ⊨ᵢ Γ ++ Δ

/-- Unfolding the ternary relation: `R Γ Δ Θ ↔ perp {Γ ++ Δ} ⊆ perp {Θ}`. -/
theorem R_pos_iff (Γ Δ Θ : List (Move L)) :
    TernaryFrame.R Γ Δ Θ ↔ perp {Γ ++ Δ} ⊆ perp {Θ} := by
  simp only [TernaryFrame.R, IncompEntails]

end PositionTernaryFrame

/-! ### Commutativity under IsContainment -/

section PositionCommutativity

variable [IsContainment L]

/-- Under `IsContainment`, `perp {Γ ++ Δ} = perp {Δ ++ Γ}`:
incoherence only depends on which moves are present (as a set), so any reordering is fine. -/
theorem perp_singleton_append_comm (Γ Δ : List (Move L)) :
    perp ({Γ ++ Δ} : Set (List (Move L))) = perp {Δ ++ Γ} := by
  ext Ψ
  simp only [mem_perp_iff, Set.mem_singleton_iff, forall_eq]
  constructor
  · intro h
    rw [mem_I_iff] at h ⊢
    obtain ⟨p, ha, hd⟩ := h
    exact ⟨p, by simp only [List.mem_append] at ha ⊢; tauto,
              by simp only [List.mem_append] at hd ⊢; tauto⟩
  · intro h
    rw [mem_I_iff] at h ⊢
    obtain ⟨p, ha, hd⟩ := h
    exact ⟨p, by simp only [List.mem_append] at ha ⊢; tauto,
              by simp only [List.mem_append] at hd ⊢; tauto⟩

/-- Under `IsContainment`, the ternary frame on positions is commutative. -/
instance instIsCommutativePos : TernaryFrame.IsCommutative (List (Move L)) where
  comm {Γ Δ Θ} h := by
    rw [R_pos_iff] at *
    rwa [perp_singleton_append_comm]

end PositionCommutativity

/-! ### Connection theorems: fusion, tensor, and Day convolution -/

section ConnectionTheorems

/-- The fusion `X ⋓ Y ⊆ TernaryFrame.tensor X Y`:
every concatenation `Γ ++ Δ` with `Γ ∈ X`, `Δ ∈ Y` satisfies `R Γ Δ (Γ ++ Δ)` by reflexivity.

This holds for bare `IncoherenceSpace`. -/
theorem fusion_sub_tensor (X Y : Set (List (Move L))) :
    X ⋓ Y ⊆ TernaryFrame.tensor X Y := by
  intro Θ hΘ
  obtain ⟨Γ, hΓ, Δ, hΔ, rfl⟩ := mem_fusion_iff.mp hΘ
  exact ⟨Γ, Δ, incompEntails_refl (Γ ++ Δ), hΓ, hΔ⟩

variable [IsExchange L]

/-- `TernaryFrame.tensor X.carrier Y.carrier ⊆ (X ⊗ᶜ Y).carrier`.

Given `Θ ∈ tensor X Y`, there exist `Γ ∈ X`, `Δ ∈ Y` with `perp {Γ ++ Δ} ⊆ perp {Θ}`.
Since `{Γ ++ Δ} ⊆ fusion X Y`, antitonicity gives `perp (fusion X Y) ⊆ perp {Γ ++ Δ}`,
and composing: `perp (fusion X Y) ⊆ perp {Θ}`, i.e., `Θ ∈ dperp (fusion X Y)`. -/
theorem tensor_sub_dtensor (X Y : ClosedSet L) :
    TernaryFrame.tensor X.carrier Y.carrier ⊆ (X ⊗ᶜ Y).carrier := by
  intro Θ ⟨Γ, Δ, hR, hΓ, hΔ⟩
  rw [R_pos_iff] at hR
  -- hR : perp {Γ ++ Δ} ⊆ perp {Θ}
  -- goal : Θ ∈ dperp (fusion X.carrier Y.carrier)
  --      = { Θ | perp (fusion X.carrier Y.carrier) ⊆ perp {Θ} }
  simp only [coe_dtensor, dperp, perp, Set.mem_setOf_eq]
  -- goal: ∀ Ψ, (∀ Φ ∈ X.carrier ⋓ Y.carrier, Ψ ++ Φ ∈ I) → Θ ++ Ψ ∈ I
  intro Ψ hΨ
  -- hΨ says Ψ ∈ perp (fusion X Y), so Ψ ++ (Γ ++ Δ) ∈ I
  have hΨΓΔ : Ψ ++ (Γ ++ Δ) ∈ I := hΨ (Γ ++ Δ) (mem_fusion_iff.mpr ⟨Γ, hΓ, Δ, hΔ, rfl⟩)
  -- Ψ ∈ perp {Γ ++ Δ} (i.e., Ψ ++ (Γ ++ Δ) ∈ I for the single element Γ ++ Δ)
  have hΨ_in_perp : Ψ ∈ perp ({Γ ++ Δ} : Set (List (Move L))) := fun _ hx =>
    Set.mem_singleton_iff.mp hx ▸ hΨΓΔ
  -- hR transports to Ψ ∈ perp {Θ}, i.e. Ψ ++ Θ ∈ I
  have hΨΘ : Ψ ++ Θ ∈ I := hR hΨ_in_perp Θ rfl
  -- Exchange: Θ ++ Ψ ∈ I
  exact (I_append_comm Ψ Θ).mp hΨΘ

/-- `(X ⊗ᶜ Y).carrier = dperp (TernaryFrame.tensor X.carrier Y.carrier)`.

The Day convolution carrier equals the incoherence closure of the ternary tensor.
This is the main connection theorem from the blog: `X ⊗^c Y = (X ⊗ Y)^⊥⊥`. -/
theorem dtensor_eq_dperp_tensor (X Y : ClosedSet L) :
    (X ⊗ᶜ Y).carrier = dperp (TernaryFrame.tensor X.carrier Y.carrier) := by
  simp only [coe_dtensor]
  apply Set.Subset.antisymm
  · exact dperp_mono (fusion_sub_tensor X.carrier Y.carrier)
  · rw [← dperp_idempotent (X.carrier ⋓ Y.carrier)]
    exact dperp_mono (tensor_sub_dtensor X Y)

end ConnectionTheorems

end IncoherenceSpace
