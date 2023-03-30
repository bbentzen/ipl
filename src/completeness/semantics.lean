/-
Copyright (c) 2023 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import ..default

open form classical

@[reducible] def wrld := set form

/- Kripke models -/

structure model := 
  (W : set wrld)
  (R : wrld → wrld → Prop) 
  (val : ℕ → wrld → Prop)
  (refl : ∀ w ∈ W, R w w)
  (trans : ∀ w ∈ W, ∀ v ∈ W, ∀ u ∈ W, R w v → R v u → R w u)

local attribute [instance] prop_decidable

@[simp]
def forces_form (M : model) : form → wrld → Prop
|  (#p)   := λ v, M.val p v
| (bot) := λ v, false 
| (p ⊃ q) := λ v, (∀ w ∈ M.W, v ∈ M.W → M.R v w → forces_form p w → forces_form q w)
| (p & q) := λ v, forces_form p v ∧ forces_form q v
| (p ∨ q) := λ v, forces_form p v ∨ forces_form q v

/- Forcing -/

notation w `⊩` `⦃` M `⦄ ` p := forces_form M p w

/- Local logical consequence -/

def forces_ctx (M : model) (Γ : set form) : wrld → Prop :=
λ w, ∀ p, p ∈ Γ → forces_form M p w

notation w `⊩` `⦃` M `⦄ ` p := forces_ctx M p w

def sem_csq (Γ : set form) (p : form) := 
∀ (M : model) (w ∈ M.W), (w ⊩⦃M⦄ Γ) → (w ⊩⦃M⦄ p)

notation Γ ` ⊨ᵢ ` p := sem_csq Γ p

/- a helpful lemma -/

lemma ctx_tt_to_subctx_tt {Γ Δ : set form} {M : model} {w : wrld} : 
  (w ⊩⦃M⦄ Γ) → Δ ⊆ Γ → (w ⊩⦃M⦄ Δ) :=
by { intros h s p pmem, apply h, apply s, assumption}