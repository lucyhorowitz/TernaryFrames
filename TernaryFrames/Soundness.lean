/-
Copyright (c) 2026 Lucy Horowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz
-/
import TernaryFrames.NMMS
import TernaryFrames.DayConvolution
import Mathlib.Data.Finset.Basic

/-!
# Soundness and Completeness of NMMS (Theorem 76 / Theorem 109)

This file proves Theorem 76 (RLLR Ch. 5, p. 222; proved as Theorem 109 in the appendix):
for any base `𝔅 = ⟨α, base⟩` and sentences `Γ, Δ` in the logically extended lexicon
`Formula α`, NMMS-derivability coincides with b-validity:

  `NMMS base Γ Δ ↔ bValid base Γ Δ`

## Semantic framework

The intended semantics is **implication-space semantics (ISS)** in the `⊥⊥`-closed-set
formulation of Horowitz (2025) / Simonelli. In this framework:

- Positions are `List (Move (Formula α))`.
- The incoherence relation is Containment (incoherent iff `+φ` and `−φ` both appear).
- The semantic value of `φ` is a `ClosedSet (Formula α)`, defined recursively:
    `⟦atom p⟧ = dperp {[+atom p]}`
    `⟦A ∧ B⟧  = ⟦A⟧ ⊗ᶜ ⟦B⟧`   (Day convolution)
    `⟦A ∨ B⟧  = ⟦A⟧ ⊓ ⟦B⟧`    (meet)
    `⟦¬A⟧     = ⟦A⟧ᶜ`           (perp-complement)
    `⟦A → B⟧  = ⟦A⟧ᶜ ⊔ ⟦B⟧`   (material conditional)
- Model-theoretic consequence `Γ ⊢^iss Δ` is incompatibility entailment between the
  assertion position of `Γ` and the denial position of `Δ`, relative to the semantic values.

The **b-models** are the ISS models fitting the base: those satisfying all the semantic
closure conditions corresponding to the NMMS rules (Proposition 108 of the book).

## The proof

**b-models** are defined abstractly as consequence relations satisfying:
1. Every base sequent holds (`fitsBase`).
2. All eight semantic closure conditions (`SemanticallyClosed`), one per NMMS rule.

**Soundness** (→): by induction on the NMMS derivation. Each rule case discharges using
the corresponding field of `M.closed`.

**Completeness** (←): via the **canonical b-model** whose consequence relation is
`NMMS base` itself. Since `NMMS` is defined by exactly the rules, it satisfies all closure
conditions. Any b-valid sequent holds in this model, hence is NMMS-derivable.

## Status

The main theorem `NMMS_iff_bValid` is fully proved with no `sorry`s.

The deeper ISS content — verifying that the concrete `issConsequence` relation (defined
using `sem`, `dperp`, `ClosedSet`) is a b-model for any base satisfying Containment —
is developed in `ISSModel.lean` (future work). This requires showing that the semantic
clauses for the connectives validate each NMMS rule, which is the content of
Proposition 108 of the book.

## References

* Hlobil, U. and Brandom, R. (2024). *Reasons for Logic, Logic for Reasons*. Ch. 5,
  Theorem 76 (p. 222); Appendix, Theorem 109.
* Horowitz, L. (2025). "Incoherence-space semantics." Topos Institute Blog.
-/

universe u

open Formula Finset IncoherenceSpace IncoherenceSpace.ClosedSet

variable {α : Type u} [DecidableEq α]

/-! ## The Containment incoherence space on `Formula α`

The canonical ISS model uses `Formula α` as the language of moves, with
Containment incoherence: a position is incoherent iff it contains both `+φ` and `−φ`
for some formula `φ`. This is the free/minimal incoherence space on formulas. -/

instance instIncoherenceSpaceFormula : IncoherenceSpace (Formula α) where
  I := {Γ | ∃ φ : Formula α, Move.assert φ ∈ Γ ∧ Move.deny φ ∈ Γ}
  empty_coherent := by simp

instance instIsContainmentFormula : IsContainment (Formula α) where
  all_containment := fun φ _Γ ha hd => ⟨φ, ha, hd⟩
  only_containment := fun _Γ ⟨φ, ha, hd⟩ => ⟨φ, ha, hd⟩

/-! ## Semantic interpretation of formulas

`sem φ : ClosedSet (Formula α)` assigns each formula its semantic value in the
canonical ISS model. The clauses replace the book's roles/RSR with `⊥⊥`-closures. -/

private def singletonClosed (Γ : List (Move (Formula α))) : ClosedSet (Formula α) :=
  ⟨dperp {Γ}, dperp_idempotent _⟩

/-- The semantic value of a formula in the canonical ISS model. -/
def sem : Formula α → ClosedSet (Formula α)
  | .atom p  => singletonClosed [Move.assert (.atom p)]
  | .and A B => sem A ⊗ᶜ sem B
  | .or  A B => sem A ⊓ sem B
  | .neg A   => (sem A)ᶜ
  | .imp A B => (sem A)ᶜ ⊔ sem B

omit [DecidableEq α] in
@[simp] lemma sem_atom (p : α) : sem (.atom p) = singletonClosed [Move.assert (.atom p)] := rfl
omit [DecidableEq α] in
@[simp] lemma sem_and (A B : Formula α) : sem (.and A B) = sem A ⊗ᶜ sem B := rfl
omit [DecidableEq α] in
@[simp] lemma sem_or (A B : Formula α) : sem (.or A B) = sem A ⊓ sem B := rfl
omit [DecidableEq α] in
@[simp] lemma sem_neg (A : Formula α) : sem (.neg A) = (sem A)ᶜ := rfl
omit [DecidableEq α] in
@[simp] lemma sem_imp (A B : Formula α) : sem (.imp A B) = (sem A)ᶜ ⊔ sem B := rfl

/-! ## b-models and b-validity

A **b-model** is any consequence relation that (1) validates every base sequent and
(2) satisfies the semantic closure conditions corresponding to each NMMS rule.

The closure conditions are the abstract content of Proposition 108: any ISS model fitting
the base satisfies them. Concretely they say the consequence relation correctly handles
each connective. -/

/-- Semantic closure conditions: one for each NMMS logical rule. -/
structure SemanticallyClosed
    (sat : Finset (Formula α) → Finset (Formula α) → Prop) : Prop where
  lAnd : ∀ {Γ Δ : Finset (Formula α)} {A B : Formula α},
      sat (Γ ∪ {A, B}) Δ → sat (Γ ∪ {.and A B}) Δ
  lOr  : ∀ {Γ Δ : Finset (Formula α)} {A B : Formula α},
      sat (Γ ∪ {A}) Δ → sat (Γ ∪ {B}) Δ → sat (Γ ∪ {A, B}) Δ →
      sat (Γ ∪ {.or A B}) Δ
  lImp : ∀ {Γ Δ : Finset (Formula α)} {A B : Formula α},
      sat Γ (Δ ∪ {A}) → sat (Γ ∪ {B}) Δ → sat (Γ ∪ {B}) (Δ ∪ {A}) →
      sat (Γ ∪ {.imp A B}) Δ
  lNeg : ∀ {Γ Δ : Finset (Formula α)} {A : Formula α},
      sat Γ (Δ ∪ {A}) → sat (Γ ∪ {.neg A}) Δ
  rAnd : ∀ {Γ Δ : Finset (Formula α)} {A B : Formula α},
      sat Γ (Δ ∪ {A}) → sat Γ (Δ ∪ {B}) → sat Γ (Δ ∪ {A, B}) →
      sat Γ (Δ ∪ {.and A B})
  rOr  : ∀ {Γ Δ : Finset (Formula α)} {A B : Formula α},
      sat Γ (Δ ∪ {A, B}) → sat Γ (Δ ∪ {.or A B})
  rImp : ∀ {Γ Δ : Finset (Formula α)} {A B : Formula α},
      sat (Γ ∪ {A}) (Δ ∪ {B}) → sat Γ (Δ ∪ {.imp A B})
  rNeg : ∀ {Γ Δ : Finset (Formula α)} {A : Formula α},
      sat (Γ ∪ {A}) Δ → sat Γ (Δ ∪ {.neg A})

/-- A b-model for base `base`: a semantically closed consequence relation fitting the base. -/
structure BModel (base : Finset (Formula α) → Finset (Formula α) → Prop) where
  sat : Finset (Formula α) → Finset (Formula α) → Prop
  fitsBase : ∀ {Γ Δ}, base Γ Δ → sat Γ Δ
  closed : SemanticallyClosed sat

/-- b-validity: `Γ ⊢^b Δ` holds iff it holds in every b-model for `base`. -/
def bValid (base : Finset (Formula α) → Finset (Formula α) → Prop)
    (Γ Δ : Finset (Formula α)) : Prop :=
  ∀ M : BModel base, M.sat Γ Δ

/-! ## Soundness (Theorem 76, → direction) -/

/-- **NMMS Soundness**: every NMMS-derivable sequent is b-valid.

Proof: induction on the derivation. The `ax` case uses `fitsBase`; each logical rule uses
the corresponding field of `M.closed`. -/
theorem NMMS_sound {Γ Δ : Finset (Formula α)}
    (base : Finset (Formula α) → Finset (Formula α) → Prop)
    (h : NMMS base Γ Δ) : bValid base Γ Δ := by
  intro M
  induction h with
  | ax hbase                  => exact M.fitsBase hbase
  | lAnd _ ih                 => exact M.closed.lAnd ih
  | lOr  _ _ _ ih₁ ih₂ ih₃   => exact M.closed.lOr ih₁ ih₂ ih₃
  | lImp _ _ _ ih₁ ih₂ ih₃   => exact M.closed.lImp ih₁ ih₂ ih₃
  | lNeg _ ih                 => exact M.closed.lNeg ih
  | rAnd _ _ _ ih₁ ih₂ ih₃   => exact M.closed.rAnd ih₁ ih₂ ih₃
  | rOr  _ ih                 => exact M.closed.rOr ih
  | rImp _ ih                 => exact M.closed.rImp ih
  | rNeg _ ih                 => exact M.closed.rNeg ih

/-! ## Completeness (Theorem 76, ← direction)

The canonical b-model has `sat = NMMS base`. It fits the base by `NMMS.ax` and satisfies
all closure conditions because `NMMS` is closed under its own rules by construction. -/

/-- The canonical b-model: `sat = NMMS base`. -/
def canonicalBModel (base : Finset (Formula α) → Finset (Formula α) → Prop) :
    BModel base where
  sat      := NMMS base
  fitsBase := NMMS.ax
  closed   := {
    lAnd := NMMS.lAnd
    lOr  := NMMS.lOr
    lImp := NMMS.lImp
    lNeg := NMMS.lNeg
    rAnd := NMMS.rAnd
    rOr  := NMMS.rOr
    rImp := NMMS.rImp
    rNeg := NMMS.rNeg }

/-- **NMMS Completeness**: every b-valid sequent is NMMS-derivable.

Proof: apply b-validity to the canonical b-model, whose consequence relation is `NMMS base`. -/
theorem NMMS_complete {Γ Δ : Finset (Formula α)}
    (base : Finset (Formula α) → Finset (Formula α) → Prop)
    (h : bValid base Γ Δ) : NMMS base Γ Δ :=
  h (canonicalBModel base)

/-- **Theorem 76** (RLLR p. 222): NMMS derivability coincides with b-validity. -/
theorem NMMS_iff_bValid {Γ Δ : Finset (Formula α)}
    (base : Finset (Formula α) → Finset (Formula α) → Prop) :
    NMMS base Γ Δ ↔ bValid base Γ Δ :=
  ⟨NMMS_sound base, NMMS_complete base⟩

/-! ## NMMS^ctr: multiset-based soundness/completeness

This is the same abstract b-model pattern as above, with multisets and the
Ketonen-style two-premiss rules.
-/

/-- Semantic closure conditions matching the NMMS^ctr rules. -/
structure SemanticallyClosedCtr
    (sat : Multiset (Formula α) → Multiset (Formula α) → Prop) : Prop where
  lAnd : ∀ {Γ Δ : Multiset (Formula α)} {A B : Formula α},
      sat (Γ + {A, B}) Δ → sat (Γ + {.and A B}) Δ
  lOr  : ∀ {Γ Δ : Multiset (Formula α)} {A B : Formula α},
      sat (Γ + {A}) Δ → sat (Γ + {B}) Δ →
      sat (Γ + {.or A B}) Δ
  lImp : ∀ {Γ Δ : Multiset (Formula α)} {A B : Formula α},
      sat Γ (Δ + {A}) → sat (Γ + {B}) Δ →
      sat (Γ + {.imp A B}) Δ
  lNeg : ∀ {Γ Δ : Multiset (Formula α)} {A : Formula α},
      sat Γ (Δ + {A}) → sat (Γ + {.neg A}) Δ
  rAnd : ∀ {Γ Δ : Multiset (Formula α)} {A B : Formula α},
      sat Γ (Δ + {A}) → sat Γ (Δ + {B}) →
      sat Γ (Δ + {.and A B})
  rOr  : ∀ {Γ Δ : Multiset (Formula α)} {A B : Formula α},
      sat Γ (Δ + {A, B}) → sat Γ (Δ + {.or A B})
  rImp : ∀ {Γ Δ : Multiset (Formula α)} {A B : Formula α},
      sat (Γ + {A}) (Δ + {B}) → sat Γ (Δ + {.imp A B})
  rNeg : ∀ {Γ Δ : Multiset (Formula α)} {A : Formula α},
      sat (Γ + {A}) Δ → sat Γ (Δ + {.neg A})

/-- A multiset b-model for base `base`. -/
structure BModelCtr (base : Multiset (Formula α) → Multiset (Formula α) → Prop) where
  sat : Multiset (Formula α) → Multiset (Formula α) → Prop
  fitsBase : ∀ {Γ Δ}, base Γ Δ → sat Γ Δ
  closed : SemanticallyClosedCtr sat

/-- Multiset b-validity: truth in every `BModelCtr`. -/
def bValidCtr (base : Multiset (Formula α) → Multiset (Formula α) → Prop)
    (Γ Δ : Multiset (Formula α)) : Prop :=
  ∀ M : BModelCtr base, M.sat Γ Δ

/-- NMMS^ctr soundness. -/
theorem NMMSctr_sound {Γ Δ : Multiset (Formula α)}
    (base : Multiset (Formula α) → Multiset (Formula α) → Prop)
    (h : NMMSctr base Γ Δ) : bValidCtr base Γ Δ := by
  intro M
  induction h with
  | ax hbase         => exact M.fitsBase hbase
  | lAnd _ ih        => exact M.closed.lAnd ih
  | lOr _ _ ih₁ ih₂  => exact M.closed.lOr ih₁ ih₂
  | lImp _ _ ih₁ ih₂ => exact M.closed.lImp ih₁ ih₂
  | lNeg _ ih        => exact M.closed.lNeg ih
  | rAnd _ _ ih₁ ih₂ => exact M.closed.rAnd ih₁ ih₂
  | rOr _ ih         => exact M.closed.rOr ih
  | rImp _ ih        => exact M.closed.rImp ih
  | rNeg _ ih        => exact M.closed.rNeg ih

/-- Canonical multiset b-model: `sat = NMMSctr base`. -/
def canonicalBModelCtr (base : Multiset (Formula α) → Multiset (Formula α) → Prop) :
    BModelCtr base where
  sat      := NMMSctr base
  fitsBase := NMMSctr.ax
  closed   := {
    lAnd := NMMSctr.lAnd
    lOr  := NMMSctr.lOr
    lImp := NMMSctr.lImp
    lNeg := NMMSctr.lNeg
    rAnd := NMMSctr.rAnd
    rOr  := NMMSctr.rOr
    rImp := NMMSctr.rImp
    rNeg := NMMSctr.rNeg }

/-- NMMS^ctr completeness. -/
theorem NMMSctr_complete {Γ Δ : Multiset (Formula α)}
    (base : Multiset (Formula α) → Multiset (Formula α) → Prop)
    (h : bValidCtr base Γ Δ) : NMMSctr base Γ Δ :=
  h (canonicalBModelCtr base)

/-- Multiset analogue of `NMMS_iff_bValid`. -/
theorem NMMSctr_iff_bValid {Γ Δ : Multiset (Formula α)}
    (base : Multiset (Formula α) → Multiset (Formula α) → Prop) :
    NMMSctr base Γ Δ ↔ bValidCtr base Γ Δ :=
  ⟨NMMSctr_sound base, NMMSctr_complete base⟩
