/-
Copyright (c) 2026 Lucy Horowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz
-/
import TernaryFrames.Containment
import Mathlib.Algebra.Order.Quantale
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Data.Set.Lattice

/-!
# Day Convolution and the Quantale Structure on ClosedSet

This file equips the lattice of `⊥⊥`-closed sets with a **Day convolution tensor**:

  `X ⊗ᶜ Y := (X ⋓ Y)⊥⊥ = dperp (fusion X Y)`

where `fusion X Y = {Γ ++ Δ | Γ ∈ X, Δ ∈ Y}` is the fusion operation from
`IncoherenceSpace.lean`.

## Main results

* `iInter_dperp_closed`: Arbitrary intersections of `dperp`-closed sets are closed
  (under `[IsExchange L]`).
* `instCompleteLattice`: `ClosedSet L` is a `CompleteLattice` (under `[IsContainment L]`,
  which provides `[IsExchange L]`).
* `dperp_fusion_congr_right/left`: `dperp (fusion X (dperp Y)) = dperp (fusion X Y)`
  (under `[IsExchange L]`).
* `ClosedSet.dtensor`: The Day convolution tensor `X ⊗ᶜ Y`.
* `ClosedSet.dunit`: The unit `dperp {[]}` for the tensor.
* `instIsQuantale`: `(ClosedSet L, ⊗ᶜ)` is a commutative unital quantale — a complete
  lattice where `⊗ᶜ` distributes over all joins.

## Notes

The `ClosedSet L` structure itself requires `[IsContainment L]`, so instances on `ClosedSet L`
carry that assumption. The underlying set-level lemmas (e.g. `dperp_fusion_congr_right`) only
need `[IsExchange L]`.

## References

* Horowitz, L. (2025). "Incoherence-space semantics." Topos Institute Blog.
-/

universe u

open IncoherenceSpace

namespace IncoherenceSpace

variable {L : Type u} [IncoherenceSpace L]

/-! ### Arbitrary intersections of closed sets -/

section ArbitraryInter

variable [IsExchange L]

/-- An arbitrary intersection of `dperp`-closed sets is `dperp`-closed. -/
theorem iInter_dperp_closed {ι : Type*} {X : ι → Set (List (Move L))}
    (hX : ∀ i, dperp (X i) = X i) : dperp (⋂ i, X i) = ⋂ i, X i := by
  apply Set.Subset.antisymm
  · intro Γ hΓ
    simp only [Set.mem_iInter] at *
    intro i
    exact hX i ▸ dperp_mono (Set.iInter_subset _ i) hΓ
  · exact subset_dperp _

end ArbitraryInter

/-! ### Key congruence lemmas for dperp and fusion -/

section DperpFusionCongr

variable [IsExchange L]

/-- The perp of `fusion X Y` is contained in the perp of `fusion X (dperp Y)`.

Given `Γ ∈ perp (fusion X Y)`, for any `Δ₁ ∈ X` and `Δ₂ ∈ dperp Y`:
- `Γ ++ Δ₁ ∈ perp Y` (from hypothesis, using append-associativity)
- `Δ₂ ∈ dperp Y = perp (perp Y)`, so `Δ₂ ++ (Γ ++ Δ₁) ∈ I`
- By Exchange: `(Γ ++ Δ₁) ++ Δ₂ ∈ I`, i.e., `Γ ++ (Δ₁ ++ Δ₂) ∈ I`.
-/
theorem perp_fusion_subset_right (X Y : Set (List (Move L))) :
    perp (fusion X Y) ⊆ perp (fusion X (dperp Y)) := by
  intro Γ hΓ Θ hΘ
  obtain ⟨Δ₁, hΔ₁, Δ₂, hΔ₂, rfl⟩ := mem_fusion_iff.mp hΘ
  -- Γ ++ Δ₁ ∈ perp Y
  have hΓΔ₁ : Γ ++ Δ₁ ∈ perp Y := by
    intro Δ₂' hΔ₂'
    have : Γ ++ (Δ₁ ++ Δ₂') ∈ I := hΓ (Δ₁ ++ Δ₂') ⟨Δ₁, hΔ₁, Δ₂', hΔ₂', rfl⟩
    rwa [← List.append_assoc] at this
  -- Δ₂ ∈ dperp Y, so Δ₂ ++ (Γ ++ Δ₁) ∈ I
  have happ : Δ₂ ++ (Γ ++ Δ₁) ∈ I := hΔ₂ (Γ ++ Δ₁) hΓΔ₁
  -- Exchange: (Γ ++ Δ₁) ++ Δ₂ ∈ I
  have hswap : (Γ ++ Δ₁) ++ Δ₂ ∈ I := (I_append_comm Δ₂ (Γ ++ Δ₁)).mp happ
  rwa [← List.append_assoc]

/-- Replacing `Y` by `dperp Y` in the right slot of fusion does not change `dperp (fusion X -)`.
-/
theorem dperp_fusion_congr_right (X Y : Set (List (Move L))) :
    dperp (fusion X (dperp Y)) = dperp (fusion X Y) := by
  apply Set.Subset.antisymm
  · exact perp_antimono (perp_fusion_subset_right X Y)
  · exact dperp_mono (fun Γ ⟨Δ, hΔ, Θ, hΘ, h⟩ => ⟨Δ, hΔ, Θ, subset_dperp Y hΘ, h⟩)

/-- The perp of `fusion X Y` is contained in the perp of `fusion (dperp X) Y`.

Symmetric to `perp_fusion_subset_right`, using Exchange on both sides. -/
theorem perp_fusion_subset_left (X Y : Set (List (Move L))) :
    perp (fusion X Y) ⊆ perp (fusion (dperp X) Y) := by
  intro Γ hΓ Θ hΘ
  obtain ⟨Δ₁, hΔ₁, Δ₂, hΔ₂, rfl⟩ := mem_fusion_iff.mp hΘ
  -- Δ₂ ++ Γ ∈ perp X
  have hΔ₂Γ : Δ₂ ++ Γ ∈ perp X := by
    intro Δ₁' hΔ₁'
    have : Γ ++ (Δ₁' ++ Δ₂) ∈ I := hΓ (Δ₁' ++ Δ₂) ⟨Δ₁', hΔ₁', Δ₂, hΔ₂, rfl⟩
    -- Γ ++ Δ₁' ++ Δ₂ ∈ I → (Δ₂ ++ Γ) ++ Δ₁' ∈ I via Exchange
    rw [← List.append_assoc] at this
    -- this : (Γ ++ Δ₁') ++ Δ₂ ∈ I
    have h1 : Δ₂ ++ (Γ ++ Δ₁') ∈ I := (I_append_comm (Γ ++ Δ₁') Δ₂).mp this
    rw [← List.append_assoc] at h1
    -- h1 : (Δ₂ ++ Γ) ++ Δ₁' ∈ I
    exact h1
  -- Δ₁ ∈ dperp X, so Δ₁ ++ (Δ₂ ++ Γ) ∈ I
  have happ : Δ₁ ++ (Δ₂ ++ Γ) ∈ I := hΔ₁ (Δ₂ ++ Γ) hΔ₂Γ
  -- Goal: Γ ++ (Δ₁ ++ Δ₂) ∈ I
  -- happ: Δ₁ ++ Δ₂ ++ Γ ∈ I (by append_assoc)
  rw [← List.append_assoc] at happ
  -- happ : (Δ₁ ++ Δ₂) ++ Γ ∈ I
  exact (I_append_comm (Δ₁ ++ Δ₂) Γ).mp happ

/-- Replacing `X` by `dperp X` in the left slot of fusion does not change `dperp (fusion - Y)`.
-/
theorem dperp_fusion_congr_left (X Y : Set (List (Move L))) :
    dperp (fusion (dperp X) Y) = dperp (fusion X Y) := by
  apply Set.Subset.antisymm
  · exact perp_antimono (perp_fusion_subset_left X Y)
  · exact dperp_mono (fun Γ ⟨Δ, hΔ, Θ, hΘ, h⟩ => ⟨Δ, subset_dperp X hΔ, Θ, hΘ, h⟩)

end DperpFusionCongr

/-! ### Fusion and indexed unions -/

section FusionUnion

set_option linter.unusedSectionVars false in
/-- Fusion distributes over indexed unions on the right:
`fusion X (⋃ i, Y i) = ⋃ i, fusion X (Y i)`. -/
theorem fusion_iUnion_right {ι : Type*} (X : Set (List (Move L))) (Y : ι → Set (List (Move L))) :
    fusion X (⋃ i, Y i) = ⋃ i, fusion X (Y i) := by
  apply Set.ext; intro Γ; simp only [mem_fusion_iff]; constructor
  · rintro ⟨Δ, hΔ, Θ, hΘ, rfl⟩
    obtain ⟨i, hΘi⟩ := Set.mem_iUnion.mp hΘ
    exact Set.mem_iUnion.mpr ⟨i, Δ, hΔ, Θ, hΘi, rfl⟩
  · intro hΓ
    obtain ⟨i, Δ, hΔ, Θ, hΘ, rfl⟩ := Set.mem_iUnion.mp hΓ
    exact ⟨Δ, hΔ, Θ, Set.mem_iUnion.mpr ⟨i, hΘ⟩, rfl⟩

set_option linter.unusedSectionVars false in
/-- Fusion distributes over indexed unions on the left:
`fusion (⋃ i, X i) Y = ⋃ i, fusion (X i) Y`. -/
theorem fusion_iUnion_left {ι : Type*} (X : ι → Set (List (Move L))) (Y : Set (List (Move L))) :
    fusion (⋃ i, X i) Y = ⋃ i, fusion (X i) Y := by
  apply Set.ext; intro Γ; simp only [mem_fusion_iff]; constructor
  · rintro ⟨Δ, hΔ, Θ, hΘ, rfl⟩
    obtain ⟨i, hΔi⟩ := Set.mem_iUnion.mp hΔ
    exact Set.mem_iUnion.mpr ⟨i, Δ, hΔi, Θ, hΘ, rfl⟩
  · intro hΓ
    obtain ⟨i, Δ, hΔ, Θ, hΘ, rfl⟩ := Set.mem_iUnion.mp hΓ
    exact ⟨Δ, Set.mem_iUnion.mpr ⟨i, hΔ⟩, Θ, hΘ, rfl⟩

set_option linter.unusedSectionVars false in
/-- Fusion distributes over biunions on the right (alias). -/
theorem fusion_iUnion₂_right {ι : Type*} (X : Set (List (Move L)))
    (Y : ι → Set (List (Move L))) :
    fusion X (⋃ i, Y i) = ⋃ i, fusion X (Y i) :=
  fusion_iUnion_right X Y

set_option linter.unusedSectionVars false in
/-- Fusion is monotone in both arguments. -/
theorem fusion_mono {X X' Y Y' : Set (List (Move L))}
    (hX : X ⊆ X') (hY : Y ⊆ Y') : fusion X Y ⊆ fusion X' Y' :=
  fun _ ⟨Δ, hΔ, Θ, hΘ, h⟩ => ⟨Δ, hX hΔ, Θ, hY hΘ, h⟩

end FusionUnion

/-! ### CompleteLattice on ClosedSet

Under `[IsExchange L]`, `ClosedSet L` is a `CompleteLattice`.
The Day convolution tensor and commutativity additionally require `[IsContainment L]`.
-/

namespace ClosedSet

variable [IsExchange L]

noncomputable instance instSupSet : SupSet (ClosedSet L) where
  sSup s := ⟨dperp (⋃ X ∈ s, X.carrier), dperp_idempotent _⟩

noncomputable instance instInfSet : InfSet (ClosedSet L) where
  sInf s := ⟨⋂ X ∈ s, X.carrier, by
    -- dperp (⋂ X ∈ s, X.carrier) = ⋂ X ∈ s, X.carrier
    apply Set.Subset.antisymm
    · -- dperp is smaller: for each X ∈ s, dperp (⋂ ...) ⊆ X.carrier
      intro Γ hΓ
      simp only [Set.mem_iInter] at hΓ ⊢
      intro X hX
      exact X.closed ▸ dperp_mono (Set.biInter_subset_of_mem hX) hΓ
    · exact subset_dperp _⟩

@[simp]
theorem coe_sSup (s : Set (ClosedSet L)) :
    (sSup s).carrier = dperp (⋃ X ∈ s, X.carrier) := rfl

@[simp]
theorem coe_sInf (s : Set (ClosedSet L)) :
    (sInf s).carrier = ⋂ X ∈ s, X.carrier := rfl

noncomputable instance instCompleteLattice [IsContainment L] : CompleteLattice (ClosedSet L) where
  __ := instLattice
  __ := instBoundedOrder
  __ := instSupSet
  __ := instInfSet
  le_sSup s X hX := by
    simp only [le_def, coe_sSup]
    intro Γ hΓ
    exact subset_dperp _ (Set.mem_biUnion hX hΓ)
  sSup_le s X hX := by
    simp only [le_def, coe_sSup]
    rw [← X.closed]
    exact dperp_mono (Set.iUnion₂_subset hX)
  sInf_le s X hX := by
    simp only [le_def, coe_sInf]
    exact fun Γ hΓ => (Set.mem_iInter₂.mp hΓ) X hX
  le_sInf s X hX := by
    simp only [le_def, coe_sInf]
    exact fun Γ hΓ => Set.mem_iInter₂.mpr (fun Y hY => hX Y hY hΓ)
  le_top _ := Set.subset_univ _
  bot_le X := I_subset_closed X.closed

/-! ### Day convolution tensor

The Day convolution tensor `X ⊗ᶜ Y := dperp (fusion X Y)`. -/

/-- The **Day convolution tensor** `X ⊗ᶜ Y := dperp (fusion X Y)`.

This is the `⊥⊥`-closure of the set of all concatenations `Γ ++ Δ` with `Γ ∈ X`, `Δ ∈ Y`.
It is the semantic value of the conjunction of two positions in ISS. -/
def dtensor (X Y : ClosedSet L) : ClosedSet L :=
  ⟨dperp (X.carrier ⋓ Y.carrier), dperp_idempotent _⟩

scoped infixl:70 " ⊗ᶜ " => ClosedSet.dtensor

@[simp]
theorem coe_dtensor (X Y : ClosedSet L) :
    (X ⊗ᶜ Y).carrier = dperp (X.carrier ⋓ Y.carrier) := rfl

/-- The unit for the Day convolution tensor: `dperp {[]}`.

Under `IsContainment`, `dperp {[]}` is the smallest `dperp`-closed set containing the
empty position. -/
def dunit : ClosedSet L :=
  ⟨dperp {[]}, dperp_idempotent _⟩

@[simp]
theorem coe_dunit : (dunit (L := L)).carrier = dperp {[]} := rfl


/-! #### Associativity -/

/-- The Day convolution tensor is associative.

Proof: use `dperp_fusion_congr_left/right` to absorb the inner `dperp`s, then `fusion_assoc`. -/
theorem dtensor_assoc (X Y Z : ClosedSet L) : X ⊗ᶜ Y ⊗ᶜ Z = X ⊗ᶜ (Y ⊗ᶜ Z) := by
  apply ext; intro Γ
  -- LHS carrier = dperp (fusion (dperp (fusion X.carrier Y.carrier)) Z.carrier)
  -- RHS carrier = dperp (fusion X.carrier (dperp (fusion Y.carrier Z.carrier)))
  change Γ ∈ dperp (dperp (X.carrier ⋓ Y.carrier) ⋓ Z.carrier) ↔
         Γ ∈ dperp (X.carrier ⋓ dperp (Y.carrier ⋓ Z.carrier))
  -- Remove the inner dperp using congr lemmas, then use fusion_assoc
  rw [dperp_fusion_congr_left, fusion_assoc, dperp_fusion_congr_right]

/-! #### Unit laws -/

/-- `dunit ⊗ᶜ X = X`: the unit is a left identity. -/
theorem dtensor_dunit_left (X : ClosedSet L) : dunit ⊗ᶜ X = X := by
  apply ext; intro Γ; simp only [coe_dtensor, coe_dunit]
  rw [dperp_fusion_congr_left, fusion_nil_left, X.closed]

/-- `X ⊗ᶜ dunit = X`: the unit is a right identity. -/
theorem dtensor_dunit_right (X : ClosedSet L) : X ⊗ᶜ dunit = X := by
  apply ext; intro Γ; simp only [coe_dtensor, coe_dunit]
  rw [dperp_fusion_congr_right, fusion_nil_right, X.closed]

/-! #### Commutativity -/

--/-- Under `IsContainment`, `dperp (fusion X Y) = dperp (fusion Y X)`.

--Under `IsContainment`, incoherence is purely about the *set* of moves present (not their order),
--so `Γ ++ (Δ₁ ++ Δ₂) ∈ I ↔ Γ ++ (Δ₂ ++ Δ₁) ∈ I` because both express the same set-membership
--condition. -/

-- Commutativity requires IsContainment (not just Exchange): permuting moves within a
-- concatenation needs incoherence to depend only on the *set* of moves, not their order.


section Commutativity

variable [IsContainment L]

-- Helper: permuting moves in a position doesn't affect incoherence under IsContainment.
omit [IsExchange L] in
private theorem perp_fusion_comm_aux {X Y : Set (List (Move L))} :
    perp (fusion X Y) ⊆ perp (fusion Y X) := by
  intro Γ h Θ hΘ
  obtain ⟨Δ₂, hΔ₂, Δ₁, hΔ₁, rfl⟩ := mem_fusion_iff.mp hΘ
  have h₀ : Γ ++ (Δ₁ ++ Δ₂) ∈ I := h (Δ₁ ++ Δ₂) ⟨Δ₁, hΔ₁, Δ₂, hΔ₂, rfl⟩
  -- Under IsContainment: membership in I only depends on the set of moves, not their order.
  -- After simp [List.mem_append], hp_a : p ∈ Γ ∨ (p ∈ Δ₁ ∨ p ∈ Δ₂), goal: p ∈ Γ ∨ (p ∈ Δ₂ ∨ p ∈ Δ₁)
  rw [mem_I_iff] at h₀ ⊢
  obtain ⟨p, hp_a, hp_d⟩ := h₀
  simp only [List.mem_append] at hp_a hp_d ⊢
  exact ⟨p,
    hp_a.elim Or.inl (fun h => Or.inr (h.elim Or.inr Or.inl)),
    hp_d.elim Or.inl (fun h => Or.inr (h.elim Or.inr Or.inl))⟩


omit [IsExchange L] in
/-- Under `IsContainment`, `dperp (fusion X Y) = dperp (fusion Y X)`.

Under `IsContainment`, incoherence is purely about the *set* of moves present (not their order),
so `Γ ++ (Δ₁ ++ Δ₂) ∈ I ↔ Γ ++ (Δ₂ ++ Δ₁) ∈ I` because both express the same set-membership
condition. -/
theorem dperp_fusion_comm (X Y : Set (List (Move L))) :
    dperp (fusion X Y) = dperp (fusion Y X) :=
  Set.Subset.antisymm
    (perp_antimono perp_fusion_comm_aux)
    (perp_antimono perp_fusion_comm_aux)

/-- The Day convolution tensor is commutative. -/
theorem dtensor_comm (X Y : ClosedSet L) : X ⊗ᶜ Y = Y ⊗ᶜ X := by
  apply ext; intro Γ; simp only [coe_dtensor]
  exact Set.ext_iff.mp (dperp_fusion_comm X.carrier Y.carrier) Γ

end Commutativity

/-! #### Monoid and CommMonoid structures -/

instance instMul : Mul (ClosedSet L) where mul := dtensor
instance instOne : One (ClosedSet L) where one := dunit

@[simp] theorem mul_def (X Y : ClosedSet L) : X * Y = X ⊗ᶜ Y := rfl
@[simp] theorem one_def : (1 : ClosedSet L) = dunit := rfl

instance instMulOneClass : MulOneClass (ClosedSet L) where
  one_mul := dtensor_dunit_left
  mul_one := dtensor_dunit_right

instance instSemigroup : Semigroup (ClosedSet L) where
  mul_assoc := dtensor_assoc

instance instMonoid : Monoid (ClosedSet L) where
  __ := instMulOneClass
  __ := instSemigroup

instance instCommMonoid [IsContainment L] : CommMonoid (ClosedSet L) where
  mul_comm := dtensor_comm


/-! #### Quantale axioms -/

/-- Auxiliary: `fusion X (⋃ Y ∈ s, Y.carrier) = ⋃ Y ∈ s, fusion X Y.carrier`. -/
private theorem fusion_biUnion_right (X : Set (List (Move L))) (s : Set (ClosedSet L)) :
    fusion X (⋃ Y ∈ s, Y.carrier) = ⋃ Y ∈ s, fusion X Y.carrier := by
  apply Set.ext; intro Θ
  constructor
  · intro hΘ
    obtain ⟨Δ, hΔ, Ψ, hΨ, rfl⟩ := mem_fusion_iff.mp hΘ
    obtain ⟨Y, hYs, hΨY⟩ := Set.mem_iUnion₂.mp hΨ
    exact Set.mem_iUnion₂.mpr ⟨Y, hYs, mem_fusion_iff.mpr ⟨Δ, hΔ, Ψ, hΨY, rfl⟩⟩
  · intro hΘ
    obtain ⟨Y, hYs, hΘY⟩ := Set.mem_iUnion₂.mp hΘ
    obtain ⟨Δ, hΔ, Ψ, hΨ, rfl⟩ := mem_fusion_iff.mp hΘY
    exact mem_fusion_iff.mpr ⟨Δ, hΔ, Ψ, Set.mem_iUnion₂.mpr ⟨Y, hYs, hΨ⟩, rfl⟩

set_option linter.unusedSectionVars false in
/-- `dperp (⋃ i, dperp (A i)) = dperp (⋃ i, A i)`:
absorbing inner `dperp`s inside an indexed union. -/
theorem dperp_iUnion_dperp [IsExchange L] {ι : Type*} (A : ι → Set (List (Move L))) :
    dperp (⋃ i, dperp (A i)) = dperp (⋃ i, A i) := by
  apply Set.Subset.antisymm
  · -- dperp (⋃ i, dperp (A i)) ⊆ dperp (⋃ i, A i)
    -- Step 1: ⋃ i, dperp (A i) ⊆ dperp (⋃ i, A i)
    --   For each i: dperp (A i) ⊆ dperp (⋃ i, A i) by dperp_mono + subset_iUnion
    -- Step 2: apply dperp_mono, then absorb via dperp_idempotent
    rw [← dperp_idempotent (⋃ i, A i)]
    exact dperp_mono (Set.iUnion_subset (fun i => dperp_mono (Set.subset_iUnion A i)))
  · -- dperp (⋃ i, A i) ⊆ dperp (⋃ i, dperp (A i))
    -- because ⋃ i, A i ⊆ ⋃ i, dperp (A i) via subset_dperp
    exact dperp_mono (Set.iUnion_mono (fun i => subset_dperp _))

/-- The Day convolution tensor distributes over arbitrary joins on the right. -/
theorem dtensor_sSup_right (X : ClosedSet L) (s : Set (ClosedSet L)) :
    X ⊗ᶜ sSup s = sSup ((X ⊗ᶜ ·) '' s) := by
  apply ext
  -- After simp: goal is
  -- dperp (X.carrier ⋓ dperp (⋃ Y ∈ s, Y.carrier)) = dperp (⋃ Z ∈ (X ⊗ᶜ · '' s), Z.carrier)
  simp only [coe_dtensor, coe_sSup]
  -- Step 1: LHS = dperp (⋃ Y ∈ s, X.carrier ⋓ Y.carrier)
  --   via dperp_fusion_congr_right + fusion_biUnion_right
  have hLHS : dperp (X.carrier ⋓ dperp (⋃ Y ∈ s, Y.carrier)) =
              dperp (⋃ Y ∈ s, X.carrier ⋓ Y.carrier) := by
    rw [dperp_fusion_congr_right, fusion_biUnion_right]
  -- Step 2: RHS = dperp (⋃ Y ∈ s, dperp (X.carrier ⋓ Y.carrier))
  --   by unfolding the image and carrier
  have hRHS : dperp (⋃ Z ∈ ((X ⊗ᶜ · : ClosedSet L → ClosedSet L) '' s), Z.carrier) =
              dperp (⋃ Y ∈ s, dperp (X.carrier ⋓ Y.carrier)) := by
    congr 1
    apply Set.ext; intro Θ
    simp only [Set.mem_iUnion, Set.mem_image]
    constructor
    · rintro ⟨Z, ⟨Y, hYs, rfl⟩, hΘ⟩
      exact ⟨Y, hYs, hΘ⟩
    · rintro ⟨Y, hYs, hΘ⟩
      exact ⟨X ⊗ᶜ Y, ⟨Y, hYs, rfl⟩, hΘ⟩
  rw [hLHS, hRHS]
  -- Step 3: dperp (⋃ Y ∈ s, A Y) = dperp (⋃ Y ∈ s, dperp (A Y))
  intro Γ; constructor
  · intro hΓ
    apply dperp_mono (Set.iUnion₂_mono (fun Y _ => subset_dperp _)) hΓ
  · intro hΓ
    -- hΓ : Γ ∈ dperp (⋃ Y ∈ s, dperp (A_Y))
    -- need: Γ ∈ dperp (⋃ Y ∈ s, A_Y)
    -- suffices: ⋃ Y ∈ s, dperp (A_Y) ⊆ dperp (⋃ Y ∈ s, A_Y)
    --   then apply perp_antimono (perp_antimono h) = dperp_mono
    have hsub : ⋃ Y ∈ s, dperp (X.carrier ⋓ Y.carrier) ⊆
                dperp (⋃ Y ∈ s, X.carrier ⋓ Y.carrier) := by
      apply Set.iUnion₂_subset
      intro Y hY
      exact dperp_mono (Set.subset_iUnion₂ (s := fun Y _ => X.carrier ⋓ Y.carrier) Y hY)
    rw [← dperp_idempotent (⋃ Y ∈ s, X.carrier ⋓ Y.carrier)]
    exact dperp_mono hsub hΓ

/-- `ClosedSet L` is a quantale under the Day convolution tensor. -/
instance instIsQuantale [IsContainment L] : IsQuantale (ClosedSet L) where
  mul_sSup_distrib X s := by
    -- Goal: X * sSup s = ⨆ Y ∈ s, X * Y
    rw [mul_def, dtensor_sSup_right]
    -- Goal: sSup ((X ⊗ᶜ ·) '' s) = ⨆ Y ∈ s, X * Y
    apply le_antisymm
    · apply sSup_le
      rintro _ ⟨Y, hYs, rfl⟩
      -- goal: (fun x => X ⊗ᶜ x) Y ≤ ⨆ y ∈ s, X * y
      change X ⊗ᶜ Y ≤ ⨆ y ∈ s, X * y
      rw [← mul_def]
      exact le_iSup₂ (f := fun W (_ : W ∈ s) => X * W) Y hYs
    · apply iSup₂_le
      intro Y hYs
      apply le_sSup
      exact ⟨Y, hYs, (mul_def X Y).symm⟩
  sSup_mul_distrib s Z := by
    -- Goal: sSup s * Z = ⨆ X ∈ s, X * Z
    -- Use commutativity: sSup s * Z = Z * sSup s
    rw [show sSup s * Z = Z * sSup s from mul_comm _ _,
        mul_def, dtensor_sSup_right]
    -- Goal: sSup ((Z ⊗ᶜ ·) '' s) = ⨆ W ∈ s, W * Z
    apply le_antisymm
    · apply sSup_le
      rintro _ ⟨W, hWs, rfl⟩
      -- (fun x => Z ⊗ᶜ x) W = Z ⊗ᶜ W = W * Z
      change Z ⊗ᶜ W ≤ ⨆ x ∈ s, x * Z
      have heq : Z ⊗ᶜ W = W * Z := by rw [← mul_def]; exact dtensor_comm Z W
      rw [heq]
      exact le_iSup₂ (f := fun W (_ : W ∈ s) => W * Z) W hWs
    · apply iSup₂_le
      intro W hWs
      apply le_sSup
      -- need W ∈ s and (fun x => Z ⊗ᶜ x) W = W * Z
      change ∃ a ∈ s, (fun x => Z ⊗ᶜ x) a = W * Z
      refine ⟨W, hWs, ?_⟩
      change Z ⊗ᶜ W = W * Z
      rw [← mul_def]
      exact dtensor_comm Z W

end ClosedSet

end IncoherenceSpace
