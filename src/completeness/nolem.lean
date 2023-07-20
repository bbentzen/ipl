/-
Copyright (c) 2023 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen, Dongheng Chen, Huayu Guo
-/

-- lem is invalid

import .semantics

open form

namespace no_lem

def W : set bool := {ff, tt}

def R : bool → bool → Prop :=  --- w0 sees w1 
λ w v, w = v ∨ w = ff 

lemma Rrefl : ∀ w : bool, w ∈ W → R w w :=
begin
  intros w h, unfold R,
  left, refl
end

lemma Rtrans : ∀ w ∈ W, ∀ v ∈ W, ∀ u ∈ W,
 R w v → R v u → R w u :=
begin
  intros w v u hw hv hu rwv rvu,
  cases rwv, 
    { rw rwv, assumption },
    { cases rvu,
      rw rvu.symm,
      repeat { right, assumption } },
end

@[simp]
def val : nat → bool → Prop :=
λ _ w, w = tt

def atom0_ne_atom1 : #0 ≠ #1 :=
λ h, (@form.no_confusion false #0 #1 h) zero_ne_one

lemma mono : ∀ p, ∀ w1 w2 ∈ W, val p w1 → R w1 w2 →  val p w2:=
begin
  intros p w1 w2 iw1 iw2 val1 r12,
  cases r12,
    { rw r12.symm,
      assumption },
    { apply false.elim,
      apply bool.ff_ne_tt,
      rw r12.symm,
      assumption },  
end

def M : model bool :=
begin
  fapply model.mk,
  exact W,
  exact R,
  exact val,
  exact Rrefl,
  exact Rtrans,
  exact mono,
end

lemma M_lem : 
  ¬ (ff ⊩{M} (#0 ∨ ~#0)) :=
begin
  intro h, 
  cases h,
    { revert h,
      unfold M,
      simp },
    { fapply h,
      exact tt,
      left, refl,
      right, simp,
      right, refl,
      unfold M, simp }
end

end no_lem

lemma no_lem: 
 ¬ ∀ p, (∅ ⊨ᵢ p ∨ ~p) :=
begin
  intro h,
  apply no_lem.M_lem,
  apply h,
  right,
  simp,
  unfold forces_ctx,
  simp
end

