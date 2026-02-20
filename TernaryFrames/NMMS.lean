/-
Copyright (c) 2026 Lucy Horowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz
-/
import TernaryFrames.Formula
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Multiset.Basic

/-!
# NMMS and NMMS^ctr Sequent Calculi

This file defines two sequent calculi from Hlobil & Brandom,
*Reasons for Logic, Logic for Reasons*, Ch. 3:

- **NMMS**: the Non-Monotonic Material Sequent calculus, working with **sets** (`Finset`)
  of formulas on each side. This gives exchange and contraction for free.
- **NMMS^ctr**: the multiset variant of NMMS, working with **multisets** (`Multiset`).
  This gives exchange but not contraction. Uses Ketonen-style rules.

## Axiom schema

Both calculi are parameterized by a **base consequence relation** `base`, which provides
the axiom instances. In the book (Ch. 3), this is an arbitrary consequence relation on the
base vocabulary. The narrowly logical rules then extend it to compound formulas.

For the Containment soundness theorem (see `Soundness.lean`), we take `base` to be the
Containment relation `(Γ ∩ Δ).Nonempty` / `∃ A, A ∈ Γ ∧ A ∈ Δ`.

## Key structural difference between NMMS and NMMS^ctr

The rules for `[L∨]`, `[L→]`, and `[R∧]` differ:
- **NMMS**: these rules have **three** premisses (including a "mixed" premiss)
- **NMMS^ctr**: these rules have **two** premisses (Ketonen-style; mixed premiss dropped)

## References

* Hlobil, U. and Brandom, R. (2024). *Reasons for Logic, Logic for Reasons*. Ch. 3, pp. 103–130.
-/

universe u

open Formula

variable {α : Type u}

/-! ## NMMS: set-based sequent calculus -/

/-- The NMMS sequent calculus parameterized by a base consequence relation `base`.

Sequents `Γ ⊢ Δ` have `Finset (Formula α)` on each side, giving exchange and contraction
for free.

The `ax` rule fires when `base Γ Δ` holds. For Containment soundness, instantiate `base`
with `(Γ ∩ Δ).Nonempty`.

Rules for `lOr`, `lImp`, `rAnd` have **three** premisses (the "mixed" premiss distinguishes
NMMS from the Ketonen-style NMMS^ctr).

No weakening and no Cut (out of scope). -/
inductive NMMS [DecidableEq α]
    (base : Finset (Formula α) → Finset (Formula α) → Prop) :
    Finset (Formula α) → Finset (Formula α) → Prop where
  /-- Axiom: fires when the base consequence relation holds. -/
  | ax    : base Γ Δ → NMMS base Γ Δ
  /-- [L∧]: `Γ, A, B ⊢ Δ` → `Γ, A∧B ⊢ Δ` (one premiss) -/
  | lAnd  : NMMS base (Γ ∪ {A, B}) Δ → NMMS base (Γ ∪ {.and A B}) Δ
  /-- [L∨]: three premisses — the third "mixed" premiss `Γ, A, B ⊢ Δ` distinguishes NMMS
  from NMMS^ctr (which uses only the first two). -/
  | lOr   : NMMS base (Γ ∪ {A}) Δ → NMMS base (Γ ∪ {B}) Δ →
            NMMS base (Γ ∪ {A, B}) Δ → NMMS base (Γ ∪ {.or A B}) Δ
  /-- [L→]: three premisses — the third "mixed" premiss `Γ, B ⊢ Δ, A` distinguishes NMMS
  from NMMS^ctr. -/
  | lImp  : NMMS base Γ (Δ ∪ {A}) → NMMS base (Γ ∪ {B}) Δ →
            NMMS base (Γ ∪ {B}) (Δ ∪ {A}) → NMMS base (Γ ∪ {.imp A B}) Δ
  /-- [L¬]: `Γ ⊢ A, Δ` → `Γ, ¬A ⊢ Δ` (one premiss) -/
  | lNeg  : NMMS base Γ (Δ ∪ {A}) → NMMS base (Γ ∪ {.neg A}) Δ
  /-- [R∧]: three premisses — the third "mixed" premiss `Γ ⊢ Δ, A, B` distinguishes NMMS
  from NMMS^ctr. -/
  | rAnd  : NMMS base Γ (Δ ∪ {A}) → NMMS base Γ (Δ ∪ {B}) →
            NMMS base Γ (Δ ∪ {A, B}) → NMMS base Γ (Δ ∪ {.and A B})
  /-- [R∨]: `Γ ⊢ Δ, A, B` → `Γ ⊢ Δ, A∨B` (one premiss) -/
  | rOr   : NMMS base Γ (Δ ∪ {A, B}) → NMMS base Γ (Δ ∪ {.or A B})
  /-- [R→]: `Γ, A ⊢ Δ, B` → `Γ ⊢ Δ, A→B` (one premiss) -/
  | rImp  : NMMS base (Γ ∪ {A}) (Δ ∪ {B}) → NMMS base Γ (Δ ∪ {.imp A B})
  /-- [R¬]: `Γ, A ⊢ Δ` → `Γ ⊢ Δ, ¬A` (one premiss) -/
  | rNeg  : NMMS base (Γ ∪ {A}) Δ → NMMS base Γ (Δ ∪ {.neg A})

/-! ## NMMS^ctr: multiset-based (Ketonen-style) sequent calculus -/

/-- The NMMS^ctr sequent calculus parameterized by a base consequence relation `base`.

Sequents `Γ ⊢ Δ` have `Multiset (Formula α)` on each side, giving exchange but not
contraction.

Rules for `lOr`, `lImp`, `rAnd` have **two** premisses (Ketonen-style), dropping the
"mixed" third premiss of NMMS.

No weakening and no Cut (out of scope). -/
inductive NMMSctr [DecidableEq α]
    (base : Multiset (Formula α) → Multiset (Formula α) → Prop) :
    Multiset (Formula α) → Multiset (Formula α) → Prop where
  /-- Axiom: fires when the base consequence relation holds. -/
  | ax    : base Γ Δ → NMMSctr base Γ Δ
  /-- [L∧]: `Γ + {A, B} ⊢ Δ` → `Γ + {A∧B} ⊢ Δ` (one premiss) -/
  | lAnd  : NMMSctr base (Γ + {A, B}) Δ → NMMSctr base (Γ + {.and A B}) Δ
  /-- [L∨]: two premisses (Ketonen-style; no mixed third premiss) -/
  | lOr   : NMMSctr base (Γ + {A}) Δ → NMMSctr base (Γ + {B}) Δ →
            NMMSctr base (Γ + {.or A B}) Δ
  /-- [L→]: two premisses (Ketonen-style; no mixed third premiss) -/
  | lImp  : NMMSctr base Γ (Δ + {A}) → NMMSctr base (Γ + {B}) Δ →
            NMMSctr base (Γ + {.imp A B}) Δ
  /-- [L¬]: `Γ ⊢ Δ + {A}` → `Γ + {¬A} ⊢ Δ` (one premiss) -/
  | lNeg  : NMMSctr base Γ (Δ + {A}) → NMMSctr base (Γ + {.neg A}) Δ
  /-- [R∧]: two premisses (Ketonen-style; no mixed third premiss) -/
  | rAnd  : NMMSctr base Γ (Δ + {A}) → NMMSctr base Γ (Δ + {B}) →
            NMMSctr base Γ (Δ + {.and A B})
  /-- [R∨]: `Γ ⊢ Δ + {A, B}` → `Γ ⊢ Δ + {A∨B}` (one premiss) -/
  | rOr   : NMMSctr base Γ (Δ + {A, B}) → NMMSctr base Γ (Δ + {.or A B})
  /-- [R→]: `Γ + {A} ⊢ Δ + {B}` → `Γ ⊢ Δ + {A→B}` (one premiss) -/
  | rImp  : NMMSctr base (Γ + {A}) (Δ + {B}) → NMMSctr base Γ (Δ + {.imp A B})
  /-- [R¬]: `Γ + {A} ⊢ Δ` → `Γ ⊢ Δ + {¬A}` (one premiss) -/
  | rNeg  : NMMSctr base (Γ + {A}) Δ → NMMSctr base Γ (Δ + {.neg A})
