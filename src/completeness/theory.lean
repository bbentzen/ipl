/-
Copyright (c) 2023 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import ..default 

open form

/- Hilbert-style axiomatization of intuitionistic propositional logic -/

inductive prf : set form → form → Prop
| ax {Γ} {p} (h : p ∈ Γ) : prf Γ p
| k {Γ} {p q} : prf Γ (p ⊃ (q ⊃ p))
| s {Γ} {p q r} : prf Γ ((p ⊃ (q ⊃ r)) ⊃ ((p ⊃ q) ⊃ (p ⊃ r)))
| exf {Γ} {p} : prf Γ (⊥ ⊃ p)
| mp {Γ} {p q} (hpq: prf Γ (p ⊃ q)) (hp : prf Γ p) : prf Γ q
| pr1 {Γ} {p q} : prf Γ ((p & q) ⊃ p)
| pr2 {Γ} {p q} : prf Γ ((p & q) ⊃ q)
| pair {Γ} {p q} : prf Γ (p ⊃ (q ⊃ (p & q)))
| inr {Γ} {p q} : prf Γ (p ⊃ (p ∨ q))
| inl {Γ} {p q} : prf Γ (q ⊃ (p ∨ q))
| case {Γ} {p q r} : prf Γ ((p ⊃ r) ⊃ ((q ⊃ r) ⊃ ((p ∨ q) ⊃ r)))

notation Γ ` ⊢ᵢ ` p := prf Γ p
notation Γ ` ⊬ᵢ ` p := prf Γ p → false

/- some helpful lemmas -/

namespace prf

lemma id {p : form } {Γ :  set form } :
  Γ ⊢ᵢ p ⊃ p :=
mp (mp (@s  Γ p (p ⊃ p) p) k) k

theorem deduction {Γ :  set form } {p q : form } :
  (Γ ⸴ p ⊢ᵢ q) → (Γ ⊢ᵢ p ⊃ q) :=
begin
  generalize eq : (Γ ⸴ p) = Γ',
  intro h,
  induction h; subst eq,
  { repeat {cases h_h},
    exact id,
    { exact mp k (ax h_h) } },
  { exact mp k k },
  { exact mp k s },
  { exact mp k exf },
  { apply mp,
    { exact (mp s (h_ih_hpq rfl)) },
    { exact h_ih_hp rfl } },
  { exact mp k pr1 },
  { exact mp k pr2 },
  { exact mp k pair },
  { exact mp k inr },
  { exact mp k inl },
  { exact mp k case }
end

theorem contradeduction {Γ :  set form } {p q : form } :
  (Γ ⊬ᵢ p ⊃ q) → (Γ ⸴ p ⊬ᵢ q) :=
begin
  intros hn h,
  exact hn (prf.deduction h)
end

-- helpful for the compl proof

lemma or_intro1 {p : form } {Γ :  set form } (q) :
  (Γ ⊢ᵢ p) → (Γ ⊢ᵢ p ∨ q) :=
begin
  intros hp,
  apply prf.mp,
  { apply prf.inr },
  { assumption }
end

lemma or_intro2 {q : form } {Γ :  set form } (p) :
  (Γ ⊢ᵢ q) → (Γ ⊢ᵢ p ∨ q) :=
begin
  intros hp,
  apply prf.mp,
  { apply prf.inl },
  { assumption }
end

lemma or_elim {p q r : form } {Γ :  set form } :
  (Γ ⊢ᵢ p ∨ q) → (Γ ⸴ p ⊢ᵢ r) → (Γ ⸴ q ⊢ᵢ r) → (Γ ⊢ᵢ r) :=
begin
  intros hpq hp hq,
  apply prf.mp,
  { apply prf.mp,
    apply prf.mp,
    { apply prf.case,
      exact p,
      exact q},
    repeat {apply deduction, assumption} },
  { assumption }
end

lemma and_elim1 {p q : form } {Γ :  set form } :
  (Γ ⊢ᵢ (p & q)) → (Γ ⊢ᵢ p) :=
begin
  intros hp,
  apply prf.mp,
  { apply prf.pr1, exact q },
  { assumption }
end

lemma and_elim2 {p q : form } {Γ :  set form } :
  (Γ ⊢ᵢ (p & q)) → (Γ ⊢ᵢ q) :=
begin
  intros hp,
  apply prf.mp,
  { apply prf.pr2, exact p },
  { assumption },
end

/- structural rules -/

lemma sub_weak {Γ Δ :  set form } {p : form } :
  (Δ ⊢ᵢ p) → (Δ ⊆ Γ) → (Γ ⊢ᵢ p) :=
begin
  intros hp h,
  induction hp,
  { apply ax, exact h hp_h },
  { exact k },
  { exact s },
  { exact exf },
  { apply mp,
    { exact hp_ih_hpq h },
    {exact hp_ih_hp h} },
  { exact pr1 },
  { exact pr2 },
  { exact pair },
  { exact inr },
  { exact inl },
  { exact case }
end

end prf