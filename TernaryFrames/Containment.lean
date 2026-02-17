/-
Copyright (c) 2026 Lucy Horowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz
-/
import TernaryFrames.IncoherenceSpace
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Order.BooleanAlgebra.Defs
import Mathlib.Order.Disjoint

/-!
# Containment and the Boolean Algebra of Closed Sets

Under the *all-and-only Containment* condition — a position is incoherent if and only if it
contains both `+p` and `−p` for some atomic `p` — the lattice of `⊥⊥`-closed sets of positions
is a Boolean algebra.

This formalizes the main theorem of "Incoherence-space semantics" (Horowitz, 2025).

## Main results

* `IsPersistent`: Typeclass mixin for persistent incoherence spaces.
* `IsExchange`: Typeclass mixin for incoherence spaces satisfying Exchange
  (incoherence depends only on which moves are present, not on order).
* `IsContainment`: Typeclass asserting all-and-only Containment.
* `subset_dperp`: Under Exchange, `X ⊆ dperp X` (extensiveness of dperp).
* `dperp_idempotent`: Under Exchange, `dperp (dperp X) = dperp X`.
* `ClosedSet`: The type of `⊥⊥`-closed sets, with a `BooleanAlgebra` instance under Containment.

## References

* Horowitz, L. (2025). "Incoherence-space semantics." Topos Institute Blog.
-/

universe u

open IncoherenceSpace

namespace IncoherenceSpace

variable {L : Type u} [IncoherenceSpace L]

/-! ### Structural conditions on incoherence -/

/-- An `IncoherenceSpace` is **persistent** if `Γ ∈ I` implies `Γ ++ Δ ∈ I` for all `Δ`.
Intuitively: adding more moves to an incoherent position cannot restore coherence. -/
class IsPersistent (L : Type u) [IncoherenceSpace L] : Prop where
  persistent : ∀ (Γ Δ : List (Move L)), Γ ∈ I → Γ ++ Δ ∈ I

/-- An `IncoherenceSpace` satisfies **Exchange** if incoherence is invariant under
reordering of positions: `Γ ++ Δ ∈ I → Δ ++ Γ ∈ I`. This is the condition under which
positions can be thought of as multisets rather than lists. -/
class IsExchange (L : Type u) [IncoherenceSpace L] : Prop where
  exchange : ∀ (Γ Δ : List (Move L)), Γ ++ Δ ∈ I → Δ ++ Γ ∈ I

section Exchange

variable [IsExchange L]

theorem I_append_comm (Γ Δ : List (Move L)) : Γ ++ Δ ∈ I ↔ Δ ++ Γ ∈ I :=
  ⟨IsExchange.exchange Γ Δ, IsExchange.exchange Δ Γ⟩

end Exchange

section Persistent

variable [IsPersistent L]

theorem persistent (Γ Δ : List (Move L)) (h : Γ ∈ I) : Γ ++ Δ ∈ I :=
  IsPersistent.persistent Γ Δ h

end Persistent

section ExchangePersistent

variable [IsExchange L] [IsPersistent L]

theorem persistent_right (Γ Δ : List (Move L)) (h : Δ ∈ I) : Γ ++ Δ ∈ I :=
  (I_append_comm Γ Δ).mpr (persistent Δ Γ h)

end ExchangePersistent

/-! ### Closure properties of dperp under Exchange -/

section ExchangeClosure

variable [IsExchange L]

/-- Under Exchange, `X ⊆ dperp X` (extensiveness of dperp). -/
theorem subset_dperp (X : Set (List (Move L))) : X ⊆ dperp X :=
  fun Γ hΓ Δ hΔ => (I_append_comm Γ Δ).mpr (hΔ Γ hΓ)

/-- `perp (perp (perp X)) = perp X` under Exchange. This is the key idempotency lemma. -/
theorem perp_perp_perp (X : Set (List (Move L))) : perp (perp (perp X)) = perp X := by
  apply Set.Subset.antisymm
  · exact perp_antimono (subset_dperp X)
  · exact subset_dperp (perp X)

/-- `dperp` is idempotent under Exchange: `dperp (dperp X) = dperp X`. -/
theorem dperp_idempotent (X : Set (List (Move L))) : dperp (dperp X) = dperp X := by
  change perp (perp (perp (perp X))) = perp (perp X)
  rw [perp_perp_perp]

/-- The intersection of two `dperp`-closed sets is `dperp`-closed. -/
theorem inter_dperp_closed {X Y : Set (List (Move L))}
    (hX : dperp X = X) (hY : dperp Y = Y) : dperp (X ∩ Y) = X ∩ Y := by
  apply Set.Subset.antisymm
  · intro Γ hΓ
    exact ⟨hX ▸ dperp_mono Set.inter_subset_left hΓ,
           hY ▸ dperp_mono Set.inter_subset_right hΓ⟩
  · exact subset_dperp (X ∩ Y)

/-- `perp X` is always `dperp`-closed: `dperp (perp X) = perp X`. -/
theorem perp_dperp_closed (X : Set (List (Move L))) : dperp (perp X) = perp X :=
  perp_perp_perp X

/-- `Set.univ` is `dperp`-closed. -/
theorem dperp_univ : dperp (Set.univ : Set (List (Move L))) = Set.univ := by
  apply Set.eq_univ_of_forall
  exact fun Γ => subset_dperp Set.univ (Set.mem_univ Γ)

end ExchangeClosure

/-- `perp` distributes over union into intersection. This holds without any structural
conditions. -/
theorem perp_union (X Y : Set (List (Move L))) :
    perp (X ∪ Y) = perp X ∩ perp Y := by
  apply Set.ext; intro Γ; constructor
  · intro hΓ
    exact ⟨fun Δ hΔ => hΓ Δ (Set.mem_union_left Y hΔ),
           fun Δ hΔ => hΓ Δ (Set.mem_union_right X hΔ)⟩
  · intro ⟨hX, hY⟩ Δ hΔ
    rcases hΔ with hΔX | hΔY
    · exact hX Δ hΔX
    · exact hY Δ hΔY

/-! ### The Containment conditions -/

/-- **"All" Containment**: any position containing both `+p` and `−p` for some `p` is
incoherent. This is the forward direction of Containment. -/
class IsAllContainment (L : Type u) [IncoherenceSpace L] : Prop where
  all_containment : ∀ (p : L) (Γ : List (Move L)),
    Move.assert p ∈ Γ → Move.deny p ∈ Γ → Γ ∈ I

/-- **"Only" Containment**: a position is incoherent only if it contains both `+p` and `−p`
for some `p`. This is the reverse direction of Containment, and says that the only source of
incoherence is the presence of conflicting assertions and denials. -/
class IsOnlyContainment (L : Type u) [IncoherenceSpace L] : Prop where
  only_containment : ∀ (Γ : List (Move L)),
    Γ ∈ I → ∃ p, Move.assert p ∈ Γ ∧ Move.deny p ∈ Γ

/-- **All-and-only Containment**: a position is incoherent if and only if it contains both
`+p` and `−p` for some atomic sentence `p`. -/
class IsContainment (L : Type u) [IncoherenceSpace L] : Prop extends
    IsAllContainment L, IsOnlyContainment L

theorem IsContainment.containment [IsContainment L] (Γ : List (Move L)) :
    Γ ∈ I ↔ ∃ p, Move.assert p ∈ Γ ∧ Move.deny p ∈ Γ :=
  ⟨IsOnlyContainment.only_containment Γ,
   fun ⟨p, ha, hd⟩ => IsAllContainment.all_containment p Γ ha hd⟩

/-- Only-Containment implies Exchange. -/
instance (priority := 100) IsContainment.toIsExchange [IsContainment L] : IsExchange L where
  exchange Γ Δ h := by
    obtain ⟨p, ha, hd⟩ := (IsContainment.containment (Γ ++ Δ)).mp h
    rw [List.mem_append] at ha hd
    exact (IsContainment.containment (Δ ++ Γ)).mpr
      ⟨p, List.mem_append.mpr ha.symm, List.mem_append.mpr hd.symm⟩

/-- Only-Containment implies Persistence (given All-Containment). -/
instance (priority := 100) IsContainment.toIsPersistent [IsContainment L] : IsPersistent L where
  persistent Γ Δ h := by
    obtain ⟨p, ha, hd⟩ := (IsContainment.containment Γ).mp h
    exact (IsContainment.containment (Γ ++ Δ)).mpr
      ⟨p, List.mem_append_left Δ ha, List.mem_append_left Δ hd⟩

section Containment

variable [IsContainment L]

/-- Under Containment, the characterization of incoherence. -/
theorem mem_I_iff (Γ : List (Move L)) :
    Γ ∈ I ↔ ∃ p, Move.assert p ∈ Γ ∧ Move.deny p ∈ Γ :=
  IsContainment.containment Γ

/-! ### Bottom and top under Containment -/

/-- `dperp ∅ = I`: the closure of the empty set is exactly the set of incoherent positions. -/
theorem dperp_empty : dperp (∅ : Set (List (Move L))) = I := by
  apply Set.ext; intro Γ; constructor
  · intro hΓ
    have h_nil : ([] : List (Move L)) ∈ perp ∅ := by
      intro Δ hΔ; exact (Set.mem_empty_iff_false Δ).mp hΔ |>.elim
    have := hΓ [] h_nil
    rwa [List.append_nil] at this
  · intro hΓ Δ _
    exact persistent Γ Δ hΓ

/-- `I` is `dperp`-closed. -/
theorem I_dperp_closed : dperp I = (I : Set (List (Move L))) := by
  rw [← dperp_empty, dperp_idempotent, dperp_empty]

/-- `I ⊆ X` for every `dperp`-closed set `X`. -/
theorem I_subset_closed {X : Set (List (Move L))} (hX : dperp X = X) : I ⊆ X := by
  rw [← dperp_empty, ← hX]
  exact dperp_mono (Set.empty_subset X)

/-! ### Complementation under Containment -/

/-- For a `dperp`-closed set `X`, we have `X ∩ perp X = I`. -/
theorem inter_perp_eq_I (X : Set (List (Move L))) (hX : dperp X = X) :
    X ∩ perp X = I := by
  apply Set.Subset.antisymm
  · intro Γ ⟨hΓX, hΓp⟩
    have hΓΓ : Γ ++ Γ ∈ I := hΓp Γ hΓX
    obtain ⟨p, ha, hd⟩ := (mem_I_iff (Γ ++ Γ)).mp hΓΓ
    rw [List.mem_append] at ha hd
    exact (mem_I_iff Γ).mpr ⟨p, ha.elim id id, hd.elim id id⟩
  · exact fun Γ hΓ => ⟨I_subset_closed hX hΓ, fun Δ _ => persistent Γ Δ hΓ⟩

/-- `perp I = Set.univ`. -/
theorem perp_I_eq_univ : perp I = (Set.univ : Set (List (Move L))) := by
  apply Set.eq_univ_of_forall
  intro Γ Δ hΔ
  exact persistent_right Γ Δ hΔ

theorem perp_univ_eq_I : perp (Set.univ : Set (List (Move L))) = I := by
  apply Set.Subset.antisymm
  · intro Γ hΓ
    have := hΓ [] (Set.mem_univ _)
    rwa [List.append_nil] at this
  · intro Γ hΓ _ _
    exact persistent Γ _ hΓ

theorem union_perp_closed (X : Set (List (Move L))) (hX : dperp X = X) :
    dperp (X ∪ perp X) = Set.univ := by
  have h1 : perp (X ∪ perp X) = perp X ∩ X := by
    rw [perp_union]; unfold dperp at hX; rw [hX]
  have h2 : perp X ∩ X = I := by
    rw [Set.inter_comm]; exact inter_perp_eq_I X hX
  change perp (perp (X ∪ perp X)) = Set.univ
  rw [h1, h2, perp_I_eq_univ]

end Containment

/-! ### ClosedSet: the type of dperp-closed sets -/

/-- A `ClosedSet` is a set of positions that is `dperp`-closed, i.e., `dperp X = X`.
This type is defined under `IsContainment` (which implies both Exchange and Persistence),
as these are needed for dperp to be a well-behaved closure operator. -/
structure ClosedSet (L : Type u) [IncoherenceSpace L] [IsContainment L] where
  /-- The underlying set of positions. -/
  carrier : Set (List (Move L))
  /-- The set is closed under double-perp. -/
  closed' : dperp carrier = carrier

namespace ClosedSet

variable {L : Type u} [IncoherenceSpace L] [IsContainment L]

@[ext]
theorem ext {X Y : ClosedSet L} (h : ∀ Γ, Γ ∈ X.carrier ↔ Γ ∈ Y.carrier) : X = Y := by
  cases X; cases Y; congr; exact Set.ext h

theorem closed (X : ClosedSet L) : dperp X.carrier = X.carrier := X.closed'

/-- The partial order on closed sets is set inclusion. -/
instance instLE : LE (ClosedSet L) where
  le X Y := X.carrier ⊆ Y.carrier

instance instLT : LT (ClosedSet L) where
  lt X Y := X ≤ Y ∧ ¬Y ≤ X

instance instPartialOrder : PartialOrder (ClosedSet L) where
  le_refl _ := Set.Subset.refl _
  le_trans _ _ _ := Set.Subset.trans
  le_antisymm _ _ hXY hYX := ext fun Γ => ⟨fun h => hXY h, fun h => hYX h⟩

theorem le_def {X Y : ClosedSet L} : X ≤ Y ↔ X.carrier ⊆ Y.carrier := Iff.rfl

instance instBot : Bot (ClosedSet L) where
  bot := ⟨I, I_dperp_closed⟩

instance instTop : Top (ClosedSet L) where
  top := ⟨Set.univ, dperp_univ⟩

instance instOrderBot : OrderBot (ClosedSet L) where
  bot_le X := I_subset_closed X.closed

instance instOrderTop : OrderTop (ClosedSet L) where
  le_top _ := Set.subset_univ _

instance instBoundedOrder : BoundedOrder (ClosedSet L) where
  __ := instOrderBot
  __ := instOrderTop

@[simp] theorem coe_bot : (⊥ : ClosedSet L).carrier = I := rfl
@[simp] theorem coe_top : (⊤ : ClosedSet L).carrier = Set.univ := rfl

/-- The infimum of two closed sets is their intersection. -/
def inf' (X Y : ClosedSet L) : ClosedSet L :=
  ⟨X.carrier ∩ Y.carrier, inter_dperp_closed X.closed Y.closed⟩

/-- The supremum of two closed sets is the dperp-closure of their union. -/
def sup' (X Y : ClosedSet L) : ClosedSet L :=
  ⟨dperp (X.carrier ∪ Y.carrier), dperp_idempotent _⟩

/-- The complement of a closed set is its perp. -/
def compl' (X : ClosedSet L) : ClosedSet L :=
  ⟨perp X.carrier, perp_dperp_closed X.carrier⟩

instance instCompl : Compl (ClosedSet L) where compl := compl'

instance instSemilatticeInf : SemilatticeInf (ClosedSet L) where
  inf := inf'
  inf_le_left _ _ := Set.inter_subset_left
  inf_le_right _ _ := Set.inter_subset_right
  le_inf _ _ _ hXY hXZ := Set.subset_inter hXY hXZ

instance instSemilatticeSup : SemilatticeSup (ClosedSet L) where
  sup := sup'
  le_sup_left _ _ := fun Γ hΓ => subset_dperp _ (Set.mem_union_left _ hΓ)
  le_sup_right _ _ := fun Γ hΓ => subset_dperp _ (Set.mem_union_right _ hΓ)
  sup_le _ _ Z hXZ hYZ := by
    change dperp _ ⊆ Z.carrier
    rw [← Z.closed]
    exact dperp_mono (Set.union_subset hXZ hYZ)

instance instLattice : Lattice (ClosedSet L) where
  __ := instSemilatticeInf
  __ := instSemilatticeSup

@[simp] theorem coe_inf (X Y : ClosedSet L) :
    (X ⊓ Y).carrier = X.carrier ∩ Y.carrier := rfl
@[simp] theorem coe_sup (X Y : ClosedSet L) :
    (X ⊔ Y).carrier = dperp (X.carrier ∪ Y.carrier) := rfl
@[simp] theorem coe_compl (X : ClosedSet L) : Xᶜ.carrier = perp X.carrier := rfl

/-! #### Complementation -/

theorem inf_compl_eq_bot (X : ClosedSet L) : X ⊓ Xᶜ = ⊥ := by
  apply ext; intro Γ
  change Γ ∈ X.carrier ∩ perp X.carrier ↔ Γ ∈ I
  rw [inter_perp_eq_I X.carrier X.closed]

theorem sup_compl_eq_top (X : ClosedSet L) : X ⊔ Xᶜ = ⊤ := by
  apply ext; intro Γ
  change Γ ∈ dperp (X.carrier ∪ perp X.carrier) ↔ Γ ∈ Set.univ
  rw [union_perp_closed X.carrier X.closed]

theorem inf_compl_le_bot (X : ClosedSet L) : X ⊓ Xᶜ ≤ ⊥ :=
  le_of_eq (inf_compl_eq_bot X)

theorem top_le_sup_compl (X : ClosedSet L) : ⊤ ≤ X ⊔ Xᶜ :=
  ge_of_eq (sup_compl_eq_top X)

theorem isCompl_compl (X : ClosedSet L) : IsCompl X Xᶜ where
  disjoint := disjoint_iff.mpr (inf_compl_eq_bot X)
  codisjoint := codisjoint_iff.mpr (sup_compl_eq_top X)

instance instComplementedLattice : ComplementedLattice (ClosedSet L) where
  exists_isCompl X := ⟨Xᶜ, isCompl_compl X⟩

/-! #### Distributivity

The lattice of closed sets is distributive. The proof uses Zorn's lemma to construct maximal
coherent positions, which provide an injective lattice homomorphism into a power-set Boolean
algebra. For now, we use `sorry` for the distributivity proof and will fill it in later. -/

instance instDistribLattice : DistribLattice (ClosedSet L) where
  le_sup_inf := sorry

/-- Under all-and-only Containment, the lattice of `dperp`-closed sets is a Boolean algebra. -/
noncomputable instance instBooleanAlgebra : BooleanAlgebra (ClosedSet L) :=
  DistribLattice.booleanAlgebraOfComplemented (ClosedSet L)

end ClosedSet

end IncoherenceSpace
