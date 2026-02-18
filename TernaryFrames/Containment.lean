/-
Copyright (c) 2026 Lucy Horowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz
-/
import TernaryFrames.IncoherenceSpace
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Sum
import Mathlib.Order.BooleanAlgebra.Defs
import Mathlib.Order.Disjoint
import Mathlib.Order.Zorn

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
coherent sets of moves, which provide an injective lattice homomorphism into a power-set
Boolean algebra. Distributivity is inherited from the power-set algebra. -/

/-! ##### Coherent sets of moves -/

/-- The set of moves appearing in a position. -/
def moves (Γ : List (Move L)) : Set (Move L) := {m | m ∈ Γ}

omit [IncoherenceSpace L] [IsContainment L] in
theorem mem_moves_iff {Γ : List (Move L)} {m : Move L} : m ∈ moves Γ ↔ m ∈ Γ :=
  Iff.rfl

omit [IncoherenceSpace L] [IsContainment L] in
theorem moves_append (Γ Δ : List (Move L)) :
    moves (Γ ++ Δ) = moves Γ ∪ moves Δ := by
  ext m; simp [moves, List.mem_append]

/-- A set of moves is **coherent** if it does not contain both `+p` and `−p` for any `p`. -/
def CoherentMoves (S : Set (Move L)) : Prop :=
  ∀ p : L, ¬(Move.assert p ∈ S ∧ Move.deny p ∈ S)

omit [IncoherenceSpace L] [IsContainment L] in
theorem coherentMoves_of_subset {S T : Set (Move L)}
    (hST : S ⊆ T) (hT : CoherentMoves T) : CoherentMoves S :=
  fun p h => hT p ⟨hST h.1, hST h.2⟩

/-- Under Containment, a position is coherent (not in `I`) iff its move-set is coherent. -/
theorem not_mem_I_iff_coherentMoves (Γ : List (Move L)) :
    Γ ∉ I ↔ CoherentMoves (moves Γ) := by
  rw [mem_I_iff]
  constructor
  · intro h p ⟨ha, hd⟩
    exact h ⟨p, mem_moves_iff.mp ha, mem_moves_iff.mp hd⟩
  · intro h ⟨p, ha, hd⟩
    exact h p ⟨mem_moves_iff.mpr ha, mem_moves_iff.mpr hd⟩

/-- Under Containment, a `dperp`-closed set is upward-closed with respect to the move-set
inclusion: if `Γ ∈ X` and every move in `Γ` also appears in `Δ`, then `Δ ∈ X`. -/
theorem closed_moves_mono {X : Set (List (Move L))} (hX : dperp X = X)
    {Γ Δ : List (Move L)} (hΓ : Γ ∈ X) (hmoves : moves Γ ⊆ moves Δ) :
    Δ ∈ X := by
  rw [← hX]
  intro Θ hΘ
  -- Θ ∈ perp X, so Θ ++ Γ ∈ I
  have hΘΓ : Θ ++ Γ ∈ I := hΘ Γ hΓ
  -- Extract the conflicting atom from Θ ++ Γ
  obtain ⟨p, ha, hd⟩ := (mem_I_iff (Θ ++ Γ)).mp hΘΓ
  rw [List.mem_append] at ha hd
  -- Lift the conflict to Δ ++ Θ using hmoves : moves Γ ⊆ moves Δ
  apply (mem_I_iff (Δ ++ Θ)).mpr
  exact ⟨p,
    List.mem_append.mpr (ha.elim (fun h => Or.inr h)
      (fun h => Or.inl (mem_moves_iff.mp (hmoves (mem_moves_iff.mpr h))))),
    List.mem_append.mpr (hd.elim (fun h => Or.inr h)
      (fun h => Or.inl (mem_moves_iff.mp (hmoves (mem_moves_iff.mpr h)))))⟩

omit [IncoherenceSpace L] [IsContainment L] in
/-- The union of a chain of coherent move-sets is coherent. -/
theorem coherentMoves_sUnion_chain {c : Set (Set (Move L))}
    (hc : IsChain (· ⊆ ·) c) (hcoh : ∀ S ∈ c, CoherentMoves S) :
    CoherentMoves (⋃₀ c) := by
  intro p ⟨⟨S, hSc, haS⟩, ⟨T, hTc, hdT⟩⟩
  rcases hc.total hSc hTc with hST | hTS
  · exact hcoh T hTc p ⟨hST haS, hdT⟩
  · exact hcoh S hSc p ⟨haS, hTS hdT⟩

omit [IncoherenceSpace L] [IsContainment L] in
/-- Zorn's lemma: every coherent set of moves extends to a maximal coherent set. -/
theorem exists_maximal_coherentMoves (S : Set (Move L)) (hS : CoherentMoves S) :
    ∃ M, S ⊆ M ∧ CoherentMoves M ∧ ∀ T, CoherentMoves T → M ⊆ T → T = M := by
  have := zorn_subset_nonempty {T : Set (Move L) | CoherentMoves T}
    (fun c hc_sub hchain ⟨T₀, hT₀⟩ =>
      ⟨⋃₀ c, coherentMoves_sUnion_chain hchain (fun S hS => hc_sub hS),
       fun S hS => Set.subset_sUnion_of_mem hS⟩)
    S hS
  obtain ⟨M, hSM, hMmax⟩ := this
  exact ⟨M, hSM, hMmax.prop, fun T hT hMT => (hMmax.eq_of_subset hT hMT).symm⟩

omit [IncoherenceSpace L] [IsContainment L] in
/-- A maximal coherent move-set contains, for each `p`, exactly one of `+p` and `−p`. -/
theorem maximal_coherentMoves_complete {M : Set (Move L)} (hM : CoherentMoves M)
    (hmax : ∀ T, CoherentMoves T → M ⊆ T → T = M) (p : L) :
    Move.assert p ∈ M ∨ Move.deny p ∈ M := by
  by_contra h
  push_neg at h
  have : CoherentMoves (M ∪ {Move.assert p}) := by
    intro q ⟨ha, hd⟩
    rw [Set.mem_union, Set.mem_singleton_iff] at ha hd
    rcases ha with ha_M | ha_eq <;> rcases hd with hd_M | hd_eq
    · -- +q ∈ M, -q ∈ M: contradicts CoherentMoves M
      exact hM q ⟨ha_M, hd_M⟩
    · -- +q ∈ M, -q = +p: impossible (different constructors)
      cases hd_eq
    · -- +q = +p, -q ∈ M: then q = p and -p ∈ M, contradicting h.2
      have := Move.assert.inj ha_eq
      subst this
      exact h.2 hd_M
    · -- +q = +p, -q = +p: impossible (different constructors)
      cases hd_eq
  have hle : M ⊆ M ∪ {Move.assert p} := Set.subset_union_left
  have := hmax _ this hle
  have : Move.assert p ∈ M := this ▸ Set.mem_union_right M (Set.mem_singleton _)
  exact h.1 this

/-- If `Δ ∈ perp X` with `moves Δ ⊆ M` and `Θ ∈ X` with `moves Θ ⊆ M`,
then `Δ ++ Θ ∈ I` while `moves (Δ ++ Θ) ⊆ M`, contradicting `CoherentMoves M`. -/
theorem perp_disjoint_from_M
    {M : Set (Move L)} (hM : CoherentMoves M)
    {Δ : List (Move L)} (hΔperp : Δ ∈ perp X) (hΔM : moves Δ ⊆ M)
    {Θ : List (Move L)} (hΘX : Θ ∈ X) (hΘM : moves Θ ⊆ M) : False := by
  have hΔΘ : Δ ++ Θ ∈ I := hΔperp Θ hΘX
  obtain ⟨p, ha, hd⟩ := (mem_I_iff (Δ ++ Θ)).mp hΔΘ
  rw [List.mem_append] at ha hd
  exact hM p ⟨ha.elim (fun h => hΔM h) (fun h => hΘM h),
              hd.elim (fun h => hΔM h) (fun h => hΘM h)⟩

/-- The Φ map: `Phi X M` holds when some position in `X` has all its moves in `M`. -/
def Phi (X : Set (List (Move L))) (M : Set (Move L)) : Prop :=
  ∃ Γ ∈ X, moves Γ ⊆ M

/-! ##### The distributivity proof

The distributivity proof uses Zorn's lemma and the fact that `Move L` is finite. When `L` is
a `Fintype`, maximal coherent move-sets can be realized as lists, enabling a representation
into a power-set Boolean algebra. -/

section Distributivity

variable [Fintype L]

/-- `Move L` is finite when `L` is. -/
noncomputable instance instFintypeMove : Fintype (Move L) :=
  Fintype.ofEquiv (L ⊕ L)
    (Equiv.mk
      (fun x : L ⊕ L => match x with | Sum.inl a => Move.assert a | Sum.inr a => Move.deny a)
      (fun x : Move L => match x with | Move.assert a => Sum.inl a | Move.deny a => Sum.inr a)
      (fun x => by cases x <;> rfl)
      (fun x => by cases x <;> rfl))

/-- Convert a set of moves to a list with the same elements. -/
noncomputable def setToList (S : Set (Move L)) : List (Move L) :=
  (Set.toFinite S).toFinset.toList

omit [IncoherenceSpace L] [IsContainment L] in
@[simp]
theorem moves_setToList (S : Set (Move L)) : moves (setToList S) = S := by
  ext m; simp [setToList, moves, Set.Finite.mem_toFinset]

/-- A list representing a coherent move-set is coherent. -/
theorem setToList_coherent {M : Set (Move L)} (hM : CoherentMoves M) :
    setToList M ∉ I := by
  rw [not_mem_I_iff_coherentMoves, moves_setToList]; exact hM

/-- Key lemma: the list representing a maximal coherent move-set `M` is in `perp X`
whenever `¬Phi X M` (no position in `X` has all its moves in `M`).

For any `Θ ∈ X`:
- If `Θ ∈ I`, then `setToList M ++ Θ ∈ I` by persistence.
- If `Θ ∉ I` but `moves Θ ⊆ M`, then `Theta ∈ X` gives `Phi X M`, contradiction.
- If `Θ ∉ I` and `moves Θ ⊄ M`, pick `a ∈ moves Θ \ M`; by completeness of `M`,
  the opposite of `a` is in `M = moves (setToList M)`, giving the conflict. -/
theorem setToList_mem_perp_of_not_Phi {X : Set (List (Move L))}
    {M : Set (Move L)} (hM : CoherentMoves M) (hmax : ∀ T, CoherentMoves T → M ⊆ T → T = M)
    (hnX : ¬Phi X M) : setToList M ∈ perp X := by
  intro Θ hΘ
  -- If Θ ∈ I, done by persistence.
  by_cases hΘI : Θ ∈ I
  · exact persistent_right (setToList M) Θ hΘI
  -- Θ ∉ I. Since ¬Phi X M, moves Θ ⊄ M.
  · have hΘM : ¬(moves Θ ⊆ M) := fun h => hnX ⟨Θ, hΘ, h⟩
    -- Pick a move in Θ not in M.
    rw [Set.not_subset] at hΘM
    obtain ⟨a, haΘ, haM⟩ := hΘM
    -- By completeness of M, the opposite of a is in M.
    -- So a and its opposite both appear in setToList M ++ Θ, giving incoherence.
    rcases a with ⟨p⟩ | ⟨p⟩
    · -- a = assert p ∈ Θ, assert p ∉ M, so deny p ∈ M by completeness
      have hdpM : Move.deny p ∈ M := by
        rcases maximal_coherentMoves_complete hM hmax p with h | h
        · exact absurd h haM
        · exact h
      -- deny p ∈ setToList M since moves(setToList M) = M
      have hdp_list : Move.deny p ∈ setToList M := by
        rw [← mem_moves_iff, moves_setToList]; exact hdpM
      rw [mem_I_iff]
      exact ⟨p,
        List.mem_append.mpr (Or.inr (mem_moves_iff.mp haΘ)),
        List.mem_append.mpr (Or.inl hdp_list)⟩
    · -- a = deny p ∈ Θ, deny p ∉ M, so assert p ∈ M by completeness
      have hapM : Move.assert p ∈ M := by
        rcases maximal_coherentMoves_complete hM hmax p with h | h
        · exact h
        · exact absurd h haM
      -- assert p ∈ setToList M since moves(setToList M) = M
      have hap_list : Move.assert p ∈ setToList M := by
        rw [← mem_moves_iff, moves_setToList]; exact hapM
      rw [mem_I_iff]
      exact ⟨p,
        List.mem_append.mpr (Or.inl hap_list),
        List.mem_append.mpr (Or.inr (mem_moves_iff.mp haΘ))⟩

set_option linter.unusedFintypeInType false in
/-- `¬Phi X M` and `¬Phi Y M` imply `¬Phi (dperp (X ∪ Y)) M`.

The list `setToList M` is in `perp X ∩ perp Y = perp (X ∪ Y)`. Any `Γ ∈ dperp(X ∪ Y)`
with `moves Γ ⊆ M` gives `Γ ++ setToList M ∈ I` with `moves (Γ ++ setToList M) ⊆ M`,
contradicting coherence of `M`. -/
theorem not_Phi_dperp_union {X Y : Set (List (Move L))}
    {M : Set (Move L)} (hM : CoherentMoves M) (hmax : ∀ T, CoherentMoves T → M ⊆ T → T = M)
    (hnX : ¬Phi X M) (hnY : ¬Phi Y M) : ¬Phi (dperp (X ∪ Y)) M := by
  -- setToList M ∈ perp X and setToList M ∈ perp Y
  have hΨX := setToList_mem_perp_of_not_Phi hM hmax hnX
  have hΨY := setToList_mem_perp_of_not_Phi hM hmax hnY
  -- So setToList M ∈ perp (X ∪ Y)
  have hΨ : setToList M ∈ perp (X ∪ Y) := by
    rw [perp_union]; exact ⟨hΨX, hΨY⟩
  -- Suppose Γ ∈ dperp(X ∪ Y) with moves Γ ⊆ M.
  intro ⟨Γ, hΓ_cl, hΓ_M⟩
  -- Then Γ ++ setToList M ∈ I.
  have hΓΨ : Γ ++ setToList M ∈ I := hΓ_cl (setToList M) hΨ
  -- But moves(Γ ++ setToList M) ⊆ M, contradicting CoherentMoves M.
  have hΓΨ_M : moves (Γ ++ setToList M) ⊆ M := by
    rw [moves_append, moves_setToList]; exact Set.union_subset hΓ_M (Set.Subset.refl M)
  exact (not_mem_I_iff_coherentMoves _).mpr (coherentMoves_of_subset hΓΨ_M hM) hΓΨ

/-- The lattice of `dperp`-closed sets is distributive.

The proof proceeds by contradiction using Zorn's lemma. Given `Γ ∈ (X ⊔ Y) ⊓ (X ⊔ Z)`
and `Δ ∈ perp (X ∪ (Y ∩ Z))`, if `Γ ++ Δ ∉ I`, extend `moves (Γ ++ Δ)` to a maximal
coherent set `M`. Then:
- `Δ ∈ perp X` with `moves Δ ⊆ M` gives `¬Phi X M`.
- `Δ ∈ perp (Y ∩ Z)` with `M` coherent gives `¬(Phi Y M ∧ Phi Z M)`.
- So `¬Phi X M ∧ ¬Phi Y M` or `¬Phi X M ∧ ¬Phi Z M`.
- Either way, `¬Phi (dperp (X ∪ Y)) M` or `¬Phi (dperp (X ∪ Z)) M`.
- But `Γ ∈ dperp(X ∪ Y)` with `moves Γ ⊆ M` gives `Phi (dperp(X ∪ Y)) M` — contradiction. -/
instance instDistribLattice : DistribLattice (ClosedSet L) where
  le_sup_inf := by
    intro x y z Γ ⟨hΓxy, hΓxz⟩
    -- Need: ∀ Δ ∈ perp(X ∪ (Y ∩ Z)), Γ ++ Δ ∈ I.
    simp only [coe_sup, coe_inf] at *
    intro Δ hΔ
    -- Δ ∈ perp(X ∪ (Y ∩ Z)) = perp X ∩ perp(Y ∩ Z)
    have hΔ_X : Δ ∈ perp x.carrier := by
      rw [perp_union] at hΔ; exact hΔ.1
    have hΔ_YZ : Δ ∈ perp (y.carrier ∩ z.carrier) := by
      rw [perp_union] at hΔ; exact hΔ.2
    -- If Γ ++ Δ ∈ I, done. Otherwise, derive a contradiction.
    by_contra hΓΔ
    -- Extend moves(Γ ++ Δ) to maximal coherent M.
    have hcoh := (not_mem_I_iff_coherentMoves (Γ ++ Δ)).mp hΓΔ
    obtain ⟨M, hGDM, hMcoh, hMmax⟩ := exists_maximal_coherentMoves
      (moves (Γ ++ Δ)) hcoh
    have hΓM : moves Γ ⊆ M := by
      intro m hm; exact hGDM (moves_append Γ Δ ▸ Set.mem_union_left _ hm)
    have hΔM : moves Δ ⊆ M := by
      intro m hm; exact hGDM (moves_append Γ Δ ▸ Set.mem_union_right _ hm)
    -- Δ ∈ perp X with moves Δ ⊆ M gives ¬Phi X M.
    have hnX : ¬Phi x.carrier M := fun ⟨Θ, hΘ, hΘM⟩ =>
      perp_disjoint_from_M hMcoh hΔ_X hΔM hΘ hΘM
    -- If both Phi Y M and Phi Z M, then there's a position in Y ∩ Z with moves ⊆ M,
    -- contradicting Δ ∈ perp(Y ∩ Z) via perp_disjoint_from_M.
    have hnYZ : ¬Phi y.carrier M ∨ ¬Phi z.carrier M := by
      by_contra h
      push_neg at h
      obtain ⟨⟨ΘY, hΘY, hΘYM⟩, ⟨ΘZ, hΘZ, hΘZM⟩⟩ := h
      have hΘ_YZ : ΘY ++ ΘZ ∈ y.carrier ∩ z.carrier := by
        constructor
        · exact closed_moves_mono y.closed hΘY
            (fun m hm => moves_append ΘY ΘZ ▸ Set.mem_union_left _ hm)
        · exact closed_moves_mono z.closed hΘZ
            (fun m hm => moves_append ΘY ΘZ ▸ Set.mem_union_right _ hm)
      have hΘM : moves (ΘY ++ ΘZ) ⊆ M := by
        rw [moves_append]; exact Set.union_subset hΘYM hΘZM
      exact perp_disjoint_from_M hMcoh hΔ_YZ hΔM hΘ_YZ hΘM
    -- Now derive contradiction: Γ ∈ dperp(X ∪ Y) with moves ⊆ M, but ¬Phi(dperp(X ∪ Y)) M.
    rcases hnYZ with hnY | hnZ
    · exact not_Phi_dperp_union hMcoh hMmax hnX hnY
        ⟨Γ, hΓxy, hΓM⟩
    · exact not_Phi_dperp_union hMcoh hMmax hnX hnZ
        ⟨Γ, hΓxz, hΓM⟩

/-- Under all-and-only Containment, the lattice of `dperp`-closed sets is a Boolean algebra. -/
noncomputable instance instBooleanAlgebra : BooleanAlgebra (ClosedSet L) :=
  DistribLattice.booleanAlgebraOfComplemented (ClosedSet L)

end Distributivity

end ClosedSet

end IncoherenceSpace
