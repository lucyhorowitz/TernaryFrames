/-
Copyright (c) 2026 Lucy Horowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz
-/
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Defs.Unbundled
import Mathlib.Data.Set.Defs

/-!
# Ternary Frames

This file defines ternary frames in the sense of substructural logic, following the nLab
presentation. A ternary frame is a set equipped with a ternary relation `R`, where `R x y z`
is read as "`z` is a possible result of combining `x` and `y`."

## Main definitions

* `TernaryFrame`: a type equipped with a ternary relation `R`.
* `TernaryFrame.IsCompatible`: the compatibility condition for an ordered ternary frame, stating
  that `R` is antitone in its first two arguments and monotone in its third.
* `TernaryFrame.IsAssociative`: the associativity condition on `R`.
* `TernaryFrame.IsCommutative`: the exchange/commutativity condition on `R`.
* `TernaryFrame.HasUnit`: existence of a truth set `T` acting as a unit for `R` with respect
  to the order.

## References

* [nLab, *Ternary frame*](https://ncatlab.org/nlab/show/ternary+frame)
-/

universe u

/-- A `TernaryFrame` on a type `W` is a ternary relation `R : W → W → W → Prop`.

Following the nLab convention, `R x y z` is read as "`z` is a possible result of combining
`x` and `y`." -/
class TernaryFrame (W : Type u) where
  /-- The ternary relation. `R x y z` means `z` is a possible result of combining `x` and `y`. -/
  R : W → W → W → Prop

namespace TernaryFrame

variable {W : Type u} [TernaryFrame W]

section Compatibility

variable [Preorder W]

/-- An ordered ternary frame satisfies the compatibility condition: `R` is antitone in its first
two arguments and monotone in its third. That is, if `R x y z` and `x' ≤ x`, `y' ≤ y`,
`z ≤ z'`, then `R x' y' z'`. -/
class IsCompatible (W : Type u) [TernaryFrame W] [Preorder W] : Prop where
  /-- If `R x y z` and `x' ≤ x`, `y' ≤ y`, `z ≤ z'`, then `R x' y' z'`. -/
  protected compat : ∀ {x x' y y' z z' : W},
    R x y z → x' ≤ x → y' ≤ y → z ≤ z' → R x' y' z'

theorem compat [IsCompatible W] {x x' y y' z z' : W}
    (h : R x y z) (hx : x' ≤ x) (hy : y' ≤ y) (hz : z ≤ z') : R x' y' z' :=
  IsCompatible.compat h hx hy hz

theorem compat_left [IsCompatible W] {x x' y z : W}
    (h : R x y z) (hx : x' ≤ x) : R x' y z :=
  compat h hx le_rfl le_rfl

theorem compat_right [IsCompatible W] {x y y' z : W}
    (h : R x y z) (hy : y' ≤ y) : R x y' z :=
  compat h le_rfl hy le_rfl

theorem compat_out [IsCompatible W] {x y z z' : W}
    (h : R x y z) (hz : z ≤ z') : R x y z' :=
  compat h le_rfl le_rfl hz

end Compatibility

section Exchange

/-- A ternary frame satisfies the exchange condition if `R x y z` implies `R y x z`. -/
class IsCommutative (W : Type u) [TernaryFrame W] : Prop where
  /-- The ternary relation is commutative in its first two arguments. -/
  protected comm : ∀ {x y z : W}, R x y z → R y x z

theorem comm [IsCommutative W] {x y z : W} (h : R x y z) : R y x z :=
  IsCommutative.comm h

theorem comm_iff [IsCommutative W] {x y z : W} : R x y z ↔ R y x z :=
  ⟨comm, comm⟩

end Exchange

section Associativity

/-- A ternary frame satisfies the associativity condition if for all `x`, `y`, `u`, `v`:
there exists `z` with `R x y z` and `R z u v` if and only if there exists `w` with
`R y u w` and `R x w v`. -/
class IsAssociative (W : Type u) [TernaryFrame W] : Prop where
  /-- Forward direction: `R x y z ∧ R z u v` implies `∃ w, R y u w ∧ R x w v`. -/
  protected assoc_left : ∀ {x y z u v : W}, R x y z → R z u v → ∃ w, R y u w ∧ R x w v
  /-- Backward direction: `R y u w ∧ R x w v` implies `∃ z, R x y z ∧ R z u v`. -/
  protected assoc_right : ∀ {x y u w v : W}, R y u w → R x w v → ∃ z, R x y z ∧ R z u v

theorem assoc_left [IsAssociative W] {x y z u v : W}
    (hxyz : R x y z) (hzuv : R z u v) : ∃ w, R y u w ∧ R x w v :=
  IsAssociative.assoc_left hxyz hzuv

theorem assoc_right [IsAssociative W] {x y u w v : W}
    (hyuw : R y u w) (hxwv : R x w v) : ∃ z, R x y z ∧ R z u v :=
  IsAssociative.assoc_right hyuw hxwv

theorem assoc_iff [IsAssociative W] {x y u v : W} :
    (∃ z, R x y z ∧ R z u v) ↔ (∃ w, R y u w ∧ R x w v) :=
  ⟨fun ⟨_, hxyz, hzuv⟩ => assoc_left hxyz hzuv,
   fun ⟨_, hyuw, hxwv⟩ => assoc_right hyuw hxwv⟩

end Associativity

section Unit

variable [Preorder W]

/-- A truth set `T` is a unit for the ternary relation with respect to the preorder, satisfying:
`x ≤ y` iff there exists `t ∈ T` with `R t x y`, and `x ≤ y` iff there exists `s ∈ T` with
`R x s y`. -/
class HasUnit (W : Type u) [TernaryFrame W] [Preorder W] where
  /-- The truth set. -/
  T : Set W
  /-- `x ≤ y` implies there exists `t ∈ T` with `R t x y`. -/
  protected le_of_left : ∀ {x y : W}, x ≤ y → ∃ t ∈ T, R t x y
  /-- If there exists `t ∈ T` with `R t x y`, then `x ≤ y`. -/
  protected left_of_le : ∀ {x y : W} {t : W}, t ∈ T → R t x y → x ≤ y
  /-- `x ≤ y` implies there exists `s ∈ T` with `R x s y`. -/
  protected le_of_right : ∀ {x y : W}, x ≤ y → ∃ s ∈ T, R x s y
  /-- If there exists `s ∈ T` with `R x s y`, then `x ≤ y`. -/
  protected right_of_le : ∀ {x y : W} {s : W}, s ∈ T → R x s y → x ≤ y

variable [HasUnit W]

theorem le_iff_exists_unit_left {x y : W} :
    x ≤ y ↔ ∃ t ∈ HasUnit.T (W := W), R t x y :=
  ⟨HasUnit.le_of_left, fun ⟨_, ht, hR⟩ => HasUnit.left_of_le ht hR⟩

theorem le_iff_exists_unit_right {x y : W} :
    x ≤ y ↔ ∃ s ∈ HasUnit.T (W := W), R x s y :=
  ⟨HasUnit.le_of_right, fun ⟨_, hs, hR⟩ => HasUnit.right_of_le hs hR⟩

end Unit

/-! ### Semantic connectives

We define the connectives of substructural logic as operations on `Set W`, interpreting
propositions as sets of worlds. Following the nLab:

* `x ∈ P ⊗ₜ Q` iff there exist `y z` with `R y z x`, `y ∈ P`, and `z ∈ Q`.
* `x ∈ P ⊸ₜ Q` iff for all `y z`, `R x y z` and `y ∈ P` imply `z ∈ Q`.
* `x ∈ P ⟜ₜ Q` iff for all `y z`, `R y x z` and `y ∈ P` imply `z ∈ Q`.
* `x ∈ munit` iff `x ∈ T` (the truth set).
-/

section Connectives

/-- The multiplicative tensor (fusion) of two propositions. `x ∈ tensor P Q` iff there exist
`y z` with `R y z x`, `y ∈ P`, and `z ∈ Q`. -/
def tensor (P Q : Set W) : Set W :=
  {x | ∃ y z, R y z x ∧ y ∈ P ∧ z ∈ Q}

/-- The left residual (linear implication). `x ∈ lhom P Q` iff for all `y z`, if `R x y z`
and `y ∈ P`, then `z ∈ Q`. -/
def lhom (P Q : Set W) : Set W :=
  {x | ∀ y z, R x y z → y ∈ P → z ∈ Q}

/-- The right residual (reverse linear implication). `x ∈ rhom P Q` (written `P ⟜ₜ Q`) iff
for all `y z`, if `R y x z` and `y ∈ P`, then `z ∈ Q`. This is the right adjoint to
`P ⊗ₜ _`, i.e., `P ⊗ₜ Q ⊆ S ↔ Q ⊆ P ⟜ₜ S`. -/
def rhom (P Q : Set W) : Set W :=
  {x | ∀ y z, R y x z → y ∈ P → z ∈ Q}

scoped infixl:70 " ⊗ₜ " => TernaryFrame.tensor
scoped infixr:60 " ⊸ₜ " => TernaryFrame.lhom
scoped infixl:60 " ⟜ₜ " => TernaryFrame.rhom

/-- The multiplicative unit, given by the truth set `T`. -/
def munit [Preorder W] [HasUnit W] : Set W := HasUnit.T

/-! #### Additive connectives

The additive connectives are simply the set-theoretic operations: intersection for conjunction,
union for disjunction, `Set.univ` for top, and `∅` for zero. -/

/-- Additive conjunction: `x ∈ P &ₜ Q` iff `x ∈ P` and `x ∈ Q`. -/
def ameet (P Q : Set W) : Set W := P ∩ Q

/-- Additive disjunction: `x ∈ P ⊕ₜ Q` iff `x ∈ P` or `x ∈ Q`. -/
def ajoin (P Q : Set W) : Set W := P ∪ Q

/-- Additive truth: `x ∈ atop` always. -/
def atop : Set W := Set.univ

/-- Additive falsity: `x ∈ azero` never. -/
def azero : Set W := ∅

scoped infixl:65 " &ₜ " => TernaryFrame.ameet
scoped infixl:64 " ⊕ₜ " => TernaryFrame.ajoin

end Connectives

/-! ### Properties of connectives -/

section ConnectiveProperties

/-! #### Membership characterizations -/

theorem mem_lhom_iff {P Q : Set W} {x : W} :
    x ∈ P ⊸ₜ Q ↔ ∀ y z, R x y z → y ∈ P → z ∈ Q :=
  Iff.rfl

theorem mem_rhom_iff {P Q : Set W} {x : W} :
    x ∈ P ⟜ₜ Q ↔ ∀ y z, R y x z → y ∈ P → z ∈ Q :=
  Iff.rfl

theorem mem_tensor_iff {P Q : Set W} {x : W} :
    x ∈ P ⊗ₜ Q ↔ ∃ y z, R y z x ∧ y ∈ P ∧ z ∈ Q :=
  Iff.rfl

/-! #### Monotonicity of connectives -/

theorem tensor_mono {P P' Q Q' : Set W} (hP : P ⊆ P') (hQ : Q ⊆ Q') :
    P ⊗ₜ Q ⊆ P' ⊗ₜ Q' :=
  fun _ ⟨y, z, hR, hy, hz⟩ => ⟨y, z, hR, hP hy, hQ hz⟩

theorem lhom_antimono_left {P P' Q : Set W} (hP : P ⊆ P') :
    P' ⊸ₜ Q ⊆ P ⊸ₜ Q :=
  fun _ h y z hR hy => h y z hR (hP hy)

theorem lhom_mono_right {P Q Q' : Set W} (hQ : Q ⊆ Q') :
    P ⊸ₜ Q ⊆ P ⊸ₜ Q' :=
  fun _ h y z hR hy => hQ (h y z hR hy)

theorem rhom_antimono_left {P P' Q : Set W} (hP : P ⊆ P') :
    P' ⟜ₜ Q ⊆ P ⟜ₜ Q :=
  fun _ h y z hR hy => h y z hR (hP hy)

theorem rhom_mono_right {P Q Q' : Set W} (hQ : Q ⊆ Q') :
    P ⟜ₜ Q ⊆ P ⟜ₜ Q' :=
  fun _ h y z hR hy => hQ (h y z hR hy)

/-! #### Exchange symmetry -/

/-- Under exchange, `tensor` is commutative. -/
theorem tensor_comm [IsCommutative W] (P Q : Set W) : P ⊗ₜ Q = Q ⊗ₜ P :=
  Set.ext fun _ =>
    ⟨fun ⟨y, z, hR, hy, hz⟩ => ⟨z, y, comm hR, hz, hy⟩,
     fun ⟨y, z, hR, hy, hz⟩ => ⟨z, y, comm hR, hz, hy⟩⟩

/-! #### Up-closure under compatibility -/

variable [Preorder W]

theorem lhom_isUpperSet [IsCompatible W] {P Q : Set W} : IsUpperSet (P ⊸ₜ Q) :=
  fun _ _ hab h y z hR hy => h y z (compat_left hR hab) hy

theorem rhom_isUpperSet [IsCompatible W] {P Q : Set W} : IsUpperSet (P ⟜ₜ Q) :=
  fun _ _ hab h y z hR hy => h y z (compat_right hR hab) hy

end ConnectiveProperties

/-! ### Residuation (tensor-hom adjunction)

The key structural result: `tensor` is left adjoint to both `lhom` and `rhom` in the
appropriate sense. These adjunctions hold for any ternary frame, with no additional conditions. -/

section Residuation

/-- Left residuation: `P ⊗ₜ Q ⊆ S ↔ P ⊆ Q ⊸ₜ S`.

Fixing `Q` on the right, `_ ⊗ₜ Q` is left adjoint to `Q ⊸ₜ _`. -/
theorem tensor_sub_iff_sub_lhom {P Q S : Set W} :
    P ⊗ₜ Q ⊆ S ↔ P ⊆ Q ⊸ₜ S := by
  constructor
  · intro h x hx y z hR hy
    exact h ⟨x, y, hR, hx, hy⟩
  · intro h x ⟨y, z, hR, hy, hz⟩
    exact h hy z x hR hz

/-- Counit of the left adjunction: `(Q ⊸ₜ S) ⊗ₜ Q ⊆ S`. -/
theorem lhom_tensor_sub {Q S : Set W} : (Q ⊸ₜ S) ⊗ₜ Q ⊆ S :=
  tensor_sub_iff_sub_lhom.mpr fun _ h => h

/-- Unit of the left adjunction: `P ⊆ Q ⊸ₜ (P ⊗ₜ Q)`. -/
theorem sub_lhom_tensor {P Q : Set W} : P ⊆ Q ⊸ₜ (P ⊗ₜ Q) :=
  tensor_sub_iff_sub_lhom.mp fun _ h => h

/-- Right residuation: `P ⊗ₜ Q ⊆ S ↔ Q ⊆ P ⟜ₜ S`.

Fixing `P` on the left, `P ⊗ₜ _` is left adjoint to `P ⟜ₜ _`. -/
theorem tensor_sub_iff_sub_rhom {P Q S : Set W} :
    P ⊗ₜ Q ⊆ S ↔ Q ⊆ P ⟜ₜ S := by
  constructor
  · intro h x hx y z hR hy
    exact h ⟨y, x, hR, hy, hx⟩
  · intro h x ⟨y, z, hR, hy, hz⟩
    exact h hz y x hR hy

/-- Counit of the right adjunction: `P ⊗ₜ (P ⟜ₜ S) ⊆ S`. -/
theorem tensor_rhom_sub {P S : Set W} : P ⊗ₜ (P ⟜ₜ S) ⊆ S :=
  tensor_sub_iff_sub_rhom.mpr fun _ h => h

/-- Unit of the right adjunction: `Q ⊆ P ⟜ₜ (P ⊗ₜ Q)`. -/
theorem sub_rhom_tensor {P Q : Set W} : Q ⊆ P ⟜ₜ (P ⊗ₜ Q) :=
  tensor_sub_iff_sub_rhom.mp fun _ h => h

/-! #### Exchange identifies the two residuals -/

/-- Under exchange, the left and right residuals coincide: `P ⊸ₜ Q = P ⟜ₜ Q`.
Both reduce to `{x | ∀ y z, R x y z → y ∈ P → z ∈ Q}`, since `R x y z ↔ R y x z`. -/
theorem lhom_eq_rhom [IsCommutative W] (P Q : Set W) : P ⊸ₜ Q = P ⟜ₜ Q :=
  Set.ext fun _ =>
    ⟨fun h y z hR hy => h y z (comm hR) hy,
     fun h y z hR hy => h y z (comm hR) hy⟩

end Residuation

/-! ### Unit laws

We show that `munit` is a left and right unit for `tensor`. The inclusion `P ⊆ munit ⊗ₜ P`
uses reflexivity and the unit axiom; the reverse `munit ⊗ₜ P ⊆ P` additionally requires `P`
to be up-closed (`IsUpperSet`). -/

section UnitLaws

variable [Preorder W] [HasUnit W]

/-- `P ⊆ munit ⊗ₜ P`: every `x ∈ P` is witnessed by a unit element on the left. -/
theorem sub_munit_tensor {P : Set W} : P ⊆ munit ⊗ₜ P := by
  intro x hx
  obtain ⟨t, ht, hR⟩ := HasUnit.le_of_left (le_refl x)
  exact ⟨t, x, hR, ht, hx⟩

/-- `munit ⊗ₜ P ⊆ P` when `P` is up-closed: if `R t z x` with `t ∈ T` and `z ∈ P`,
then `z ≤ x`, so `x ∈ P` by up-closure. -/
theorem munit_tensor_sub {P : Set W} (hP : IsUpperSet P) : munit ⊗ₜ P ⊆ P := by
  intro x ⟨y, z, hR, hy, hz⟩
  exact hP (HasUnit.left_of_le hy hR) hz

/-- `munit ⊗ₜ P = P` for up-closed `P`. -/
theorem munit_tensor_eq {P : Set W} (hP : IsUpperSet P) : munit ⊗ₜ P = P :=
  Set.ext fun _ => ⟨fun h => munit_tensor_sub hP h, fun h => sub_munit_tensor h⟩

/-- `P ⊆ P ⊗ₜ munit`: every `x ∈ P` is witnessed by a unit element on the right. -/
theorem sub_tensor_munit {P : Set W} : P ⊆ P ⊗ₜ munit := by
  intro x hx
  obtain ⟨s, hs, hR⟩ := HasUnit.le_of_right (le_refl x)
  exact ⟨x, s, hR, hx, hs⟩

/-- `P ⊗ₜ munit ⊆ P` when `P` is up-closed: if `R y s x` with `s ∈ T` and `y ∈ P`,
then `y ≤ x`, so `x ∈ P` by up-closure. -/
theorem tensor_munit_sub {P : Set W} (hP : IsUpperSet P) : P ⊗ₜ munit ⊆ P := by
  intro x ⟨y, z, hR, hy, hz⟩
  exact hP (HasUnit.right_of_le hz hR) hy

/-- `P ⊗ₜ munit = P` for up-closed `P`. -/
theorem tensor_munit_eq {P : Set W} (hP : IsUpperSet P) : P ⊗ₜ munit = P :=
  Set.ext fun _ => ⟨fun h => tensor_munit_sub hP h, fun h => sub_tensor_munit h⟩

end UnitLaws

/-! ### Associativity of tensor

Under `IsAssociative`, the tensor product on `Set W` is associative. -/

section TensorAssoc

variable [IsAssociative W]

theorem tensor_assoc (P Q S : Set W) : (P ⊗ₜ Q) ⊗ₜ S = P ⊗ₜ (Q ⊗ₜ S) := by
  apply Set.ext; intro x; constructor
  · rintro ⟨a, b, hRabx, ⟨c, d, hRcda, hc, hd⟩, hb⟩
    obtain ⟨w, hRdbw, hRcwx⟩ := assoc_left hRcda hRabx
    exact ⟨c, w, hRcwx, hc, d, b, hRdbw, hd, hb⟩
  · rintro ⟨c, w, hRcwx, hc, d, b, hRdbw, hd, hb⟩
    obtain ⟨a, hRcda, hRabx⟩ := assoc_right hRdbw hRcwx
    exact ⟨a, b, hRabx, ⟨c, d, hRcda, hc, hd⟩, hb⟩

end TensorAssoc

/-! ### Negation

Negation can be defined in two ways:

1. Via a **falsity set** `F ⊆ W`: define `¬ₜ P = P ⊸ₜ F`, where `F` is the set interpreting
   the constant `⊥`. This gives `x ∈ ¬ₜ P ↔ ∀ y z, R x y z → y ∈ P → z ∈ F`.

2. Via a **compatibility relation** `C : W → W → Prop`: define `¬ₜ P = {x | ∀ y, C x y → y ∉ P}`.
   This is the approach used in relevant logic (the Routley star). -/

section Negation

/-- A ternary frame with a falsity set `F`, used to interpret `⊥` and define negation
as `¬ₜ P = P ⊸ₜ F`. -/
class HasFalsity (W : Type u) [TernaryFrame W] where
  /-- The falsity set. -/
  F : Set W

/-- Negation via the falsity set: `¬ₜ P = P ⊸ₜ F`. -/
def lneg [HasFalsity W] (P : Set W) : Set W := lhom P HasFalsity.F

/-- Right negation via the falsity set: `P ⊸ₜ⁻ = rhom P F`. -/
def rneg [HasFalsity W] (P : Set W) : Set W := rhom P HasFalsity.F

scoped prefix:75 "¬ₗ" => TernaryFrame.lneg
scoped prefix:75 "¬ᵣ" => TernaryFrame.rneg

theorem mem_lneg_iff [HasFalsity W] {P : Set W} {x : W} :
    x ∈ ¬ₗP ↔ ∀ y z, R x y z → y ∈ P → z ∈ HasFalsity.F :=
  Iff.rfl

theorem mem_rneg_iff [HasFalsity W] {P : Set W} {x : W} :
    x ∈ ¬ᵣP ↔ ∀ y z, R y x z → y ∈ P → z ∈ HasFalsity.F :=
  Iff.rfl

/-- Under exchange, the two negations coincide. -/
theorem lneg_eq_rneg [HasFalsity W] [IsCommutative W] (P : Set W) : ¬ₗP = ¬ᵣP :=
  lhom_eq_rhom P HasFalsity.F

/-- A ternary frame with a compatibility relation `C`, used to define negation in
relevant logic style. -/
class HasCompat (W : Type u) [TernaryFrame W] where
  /-- The compatibility relation. `C x y` means `x` and `y` are compatible. -/
  C : W → W → Prop

/-- Negation via the compatibility relation: `x ∈ cneg P` iff for all `y`, `C x y`
implies `y ∉ P`. -/
def cneg [HasCompat W] (P : Set W) : Set W :=
  {x | ∀ y, HasCompat.C x y → y ∉ P}

scoped prefix:75 "~" => TernaryFrame.cneg

theorem mem_cneg_iff [HasCompat W] {P : Set W} {x : W} :
    x ∈ ~P ↔ ∀ y, HasCompat.C x y → y ∉ P :=
  Iff.rfl

/-- Compatibility negation is antitone: if `P ⊆ Q` then `~Q ⊆ ~P`. -/
theorem cneg_antimono [HasCompat W] {P Q : Set W} (h : P ⊆ Q) : ~Q ⊆ ~P :=
  fun _ hx y hC hy => hx y hC (h hy)

/-- Double negation introduction for compatibility negation: `P ⊆ ~~P` when `C` is
symmetric. -/
theorem sub_cneg_cneg [HasCompat W] (hC : ∀ x y : W, HasCompat.C x y → HasCompat.C y x)
    {P : Set W} : P ⊆ ~(~P) :=
  fun x hx y hCxy hy => hy x (hC x y hCxy) hx

end Negation

/-! ### Distributivity of tensor over unions

Tensor distributes over arbitrary unions in both arguments. Together with associativity,
commutativity (exchange), and the unit laws on up-closed sets, this makes the up-closed
sets of an ordered ternary frame into a quantale (a complete lattice with a semigroup
operation distributing over joins).

We state distributivity in terms of set-builder unions to avoid extra lattice imports. -/

section Distributivity

/-- Tensor distributes over arbitrary unions on the right:
`P ⊗ₜ (⋃ i, Q i) = ⋃ i, (P ⊗ₜ Q i)`. -/
theorem tensor_union_right {P : Set W} {ι : Type*} {Q : ι → Set W} :
    P ⊗ₜ {x | ∃ i, x ∈ Q i} = {x | ∃ i, x ∈ P ⊗ₜ Q i} :=
  Set.ext fun _ =>
    ⟨fun ⟨y, z, hR, hy, ⟨i, hz⟩⟩ => ⟨i, y, z, hR, hy, hz⟩,
     fun ⟨i, y, z, hR, hy, hz⟩ => ⟨y, z, hR, hy, ⟨i, hz⟩⟩⟩

/-- Tensor distributes over arbitrary unions on the left:
`(⋃ i, P i) ⊗ₜ Q = ⋃ i, (P i ⊗ₜ Q)`. -/
theorem tensor_union_left {Q : Set W} {ι : Type*} {P : ι → Set W} :
    {x | ∃ i, x ∈ P i} ⊗ₜ Q = {x | ∃ i, x ∈ P i ⊗ₜ Q} :=
  Set.ext fun _ =>
    ⟨fun ⟨y, z, hR, ⟨i, hy⟩, hz⟩ => ⟨i, y, z, hR, hy, hz⟩,
     fun ⟨i, y, z, hR, hy, hz⟩ => ⟨y, z, hR, ⟨i, hy⟩, hz⟩⟩

/-- Tensor distributes over binary unions on the right. -/
theorem tensor_union_right₂ {P Q₁ Q₂ : Set W} :
    P ⊗ₜ (Q₁ ∪ Q₂) = (P ⊗ₜ Q₁) ∪ (P ⊗ₜ Q₂) :=
  Set.ext fun _ =>
    ⟨fun ⟨y, z, hR, hy, hz⟩ => by
       cases hz with
       | inl h => exact Or.inl ⟨y, z, hR, hy, h⟩
       | inr h => exact Or.inr ⟨y, z, hR, hy, h⟩,
     fun h => by
       cases h with
       | inl h => obtain ⟨y, z, hR, hy, hz⟩ := h; exact ⟨y, z, hR, hy, Or.inl hz⟩
       | inr h => obtain ⟨y, z, hR, hy, hz⟩ := h; exact ⟨y, z, hR, hy, Or.inr hz⟩⟩

/-- Tensor distributes over binary unions on the left. -/
theorem tensor_union_left₂ {P₁ P₂ Q : Set W} :
    (P₁ ∪ P₂) ⊗ₜ Q = (P₁ ⊗ₜ Q) ∪ (P₂ ⊗ₜ Q) :=
  Set.ext fun _ =>
    ⟨fun ⟨y, z, hR, hy, hz⟩ => by
       cases hy with
       | inl h => exact Or.inl ⟨y, z, hR, h, hz⟩
       | inr h => exact Or.inr ⟨y, z, hR, h, hz⟩,
     fun h => by
       cases h with
       | inl h => obtain ⟨y, z, hR, hy, hz⟩ := h; exact ⟨y, z, hR, Or.inl hy, hz⟩
       | inr h => obtain ⟨y, z, hR, hy, hz⟩ := h; exact ⟨y, z, hR, Or.inr hy, hz⟩⟩

end Distributivity

end TernaryFrame
