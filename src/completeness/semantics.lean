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
  (mono : ∀ p, ∀ w1 w2 ∈ W, val p w1 → R w1 w2 →  val p w2)
local attribute [instance] prop_decidable

@[simp]
def forces_form (M : model) : form → wrld → Prop
|  (#p)   := λ v, M.val p v
| (bot) := λ v, false 
| (p ⊃ q) := λ v, ∀ w ∈ M.W, v ∈ M.W → M.R v w → forces_form p w → forces_form q w
| (p & q) := λ v, forces_form p v ∧ forces_form q v
| (p ∨ q) := λ v, forces_form p v ∨ forces_form q v

/- Forcing -/

notation w `⊩` `{` M `} ` p := forces_form M p w

/- Local logical consequence -/

def forces_ctx (M : model) (Γ : set form) : wrld → Prop :=
λ w, ∀ p, p ∈ Γ → forces_form M p w

notation w `⊩` `{` M `} ` Γ := forces_ctx M Γ w

def sem_csq (Γ : set form) (p : form) := 
∀ (M : model) (w ∈ M.W), (w ⊩{M} Γ) → (w ⊩{M} p)

notation Γ ` ⊨ᵢ ` p := sem_csq Γ p

/- a helpful lemma -/

lemma ctx_tt_to_subctx_tt {Γ Δ : set form} {M : model} {w : wrld} : 
  (w ⊩{M} Γ) → Δ ⊆ Γ → (w ⊩{M} Δ) :=
by { intros h s p pmem, apply h, apply s, assumption}

lemma mono_r {M : model}: 
∀ p : form, ∀ w1 w2 ∈ M.W, (w1 ⊩ { M } p) → M.R w1 w2 →  (w2 ⊩ { M } p):=
begin
intro p,
induction p,
simp,
apply M.mono,

simp,

simp,
intros w1 w2 hw1 hw2 a M.mono2 w3 hw3 _ M.mono3 hw3p,
apply a,
assumption,
assumption,
apply M.trans,
assumption,
apply hw2, 
assumption,
assumption,
assumption,
assumption,

simp,
intros w1 w2 hw1 hw2 a M.mono2 w3,
split,
apply p_ih_a,
exact hw1,
assumption',
apply p_ih_a_1,
exact hw1,
assumption',


simp,
intros w1 w2 hw1 hw2 a M.mono2,
cases a,
left,
apply p_ih_a,
exact hw1,
assumption',
right,
apply p_ih_a_1,
exact hw1,
assumption',
end


