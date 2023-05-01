/-
Copyright (c) 2023 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import ..encoding.encode .theory .semantics

open nat set classical

local attribute [instance, priority 0] prop_decidable

/- prime extension of context set -/

namespace  ctx

def is_closed (Γ :  set form) := 
∀ {p : form}, (Γ ⊢ᵢ p) → p ∈ Γ

def has_disj (Γ :  set form) := 
∀ {p q : form}, ((p ∨ q) ∈ Γ) → ((p ∈ Γ) ∨ (q ∈ Γ))

def is_prime (Γ :  set form) := 
is_closed Γ ∧ has_disj Γ

/-- extension -/

def insert_form (Γ :  set form) (p q r : form) :  set form :=
if (Γ ⸴ p ⊢ᵢ r) then Γ ⸴ q else Γ ⸴ p

@[simp]
def insert_code (Γ :  set form) (r : form) (n : nat) :  set form :=
match encodable.decode (form) n with
| none := Γ
| some (p ∨ q) := if Γ ⊢ᵢ p ∨ q then insert_form Γ p q r else Γ
| some _ := Γ
end

@[simp]
def insertn (Γ :  set form) (r : form) : nat →  set form
| 0     := Γ 
| (n+1) := insert_code (insertn n) r n 

@[simp]
def primen (Γ :  set form) (r : form) : nat →  set form
| 0     := Γ
| (n+1) := ⋃ i, insertn (primen n) r i 

@[simp]
def prime (Γ :  set form) (r : form) :  set form := 
⋃ n, primen Γ r n

/- prime extends the original set -/

lemma subset_insert_code {Γ :  set form} {r : form} (n) :
  Γ ⊆ insert_code Γ r n :=
begin
  intros v hv, simp, 
  cases (encodable.decode (form) _),
    { assumption },
    { induction val,
      assumption',
      unfold insert_code ite,
      induction (prop_decidable _),
      { assumption },
      { unfold insert_form ite, 
      induction (prop_decidable _),
        repeat { right, assumption } } }
end

lemma primen_subset_prime {Γ :  set form} {r : form} (n) :
  primen Γ r n ⊆ prime Γ r :=
subset_Union _ _

lemma subset_insertn {Γ :  set form} {r : form} {n} :
  Γ ⊆ insertn Γ r n :=
begin
  induction n,
  { simp }, 
  { simp, cases (encodable.decode (form) _) with p,
    { assumption },
      induction p,
        assumption',
      { simp [ite], 
        induction (prop_decidable _),
        { simp, assumption },
        { simp [insert_form, ite], 
          induction (prop_decidable _),
            repeat {intros q hq, right, exact n_ih hq} } } }
end

lemma subset_prime_self {Γ :  set form} {r : form} :
  Γ ⊆ prime Γ r :=
primen_subset_prime 0

lemma insertn_sub_primen {Γ :  set form} {r : form} {n m : nat} :
  insertn (primen Γ r n) r m ⊆ primen Γ r (n+1) :=
subset_Union _ _

lemma insertn_to_prime {Γ :  set form} {r : form} {n m : nat} :
  insertn (primen Γ r n) r m ⊆ prime Γ r :=
by induction m; 
[ apply primen_subset_prime, 
  exact subset.trans insertn_sub_primen (primen_subset_prime _) ]

/- prime has the disjunction property -/

lemma in_prime_in_primen {Γ :  set form} {p r : form} :
  (p ∈ prime Γ r ) → ∃ n, p ∈ primen Γ r n :=
mem_Union.1

lemma in_primen_in_insertn {Γ :  set form} {p r : form} {n} :
  (p ∈ primen Γ r (n+1) ) → ∃ i, p ∈ insertn (primen Γ r n) r i :=
mem_Union.1

lemma primen_subset_succ {Γ :  set form} {r : form} {n : nat} :
  primen Γ r n ⊆ primen Γ r (n+1) :=
begin
  apply subset.trans,
  { apply subset_insertn,
    assumption' },
  { exact subset_Union _ _}
end

lemma primen_mono {Γ :  set form} {r : form} {m n : nat} (h : n ≤ m) :
  primen Γ r n ⊆ primen Γ r m :=
by induction h; [refl, exact subset.trans h_ih primen_subset_succ ]

lemma insertn_mono {Γ :  set form} {r : form} {m n : nat} (h : n ≤ m) :
  insertn Γ r n ⊆ insertn Γ r m :=
by induction h; [refl, exact subset.trans h_ih (subset_insert_code _)]

def primen_sub_prf {Γ :  set form} {p r : form} : 
  (prime Γ r ⊢ᵢ p) → ∃ n, primen Γ r n ⊢ᵢ p :=
begin
  generalize eq : prime Γ r = Γ',
  intro h, induction h; subst eq,
  { cases in_prime_in_primen h_h with n hpq,
    exact ⟨n, prf.ax hpq⟩ }, 

  repeat {
      constructor,
      apply prf.k <|> apply prf.s <|> apply prf.exf <|>
      apply prf.pr1 <|> apply prf.pr2 <|> apply prf.pair <|> 
      apply prf.inr <|> apply prf.inl <|> apply prf.case,
      exact 0
    },

  { cases h_ih_hpq rfl with i h_ext_pq,
    cases h_ih_hp rfl with j h_ext_p,
    cases (prop_decidable (i ≤ j)),
    { have hn: j ≤ i :=
        begin
          cases nat.le_total,
          assumption,
          contradiction
      end,
      constructor,
      { apply prf.mp,
        { assumption },
        { apply prf.sub_weak,
          { exact h_ext_p },
          { apply primen_mono,
            assumption } } } },
    { constructor,
      { apply prf.mp,
        { apply prf.sub_weak,
          { exact h_ext_pq },
          { apply primen_mono,
            assumption } },
          assumption } } }
end

lemma prf_primen_prf_insertn {Γ :  set form} {p r : form} {n} :
  (primen Γ r (n+1) ⊢ᵢ p) → ∃ i, insertn (primen Γ r n) r i ⊢ᵢ p :=
begin
  generalize eq : primen Γ r (n+1) = Γ',
  intro h, induction h; subst eq,
  { cases in_primen_in_insertn h_h with n hpq,
    exact ⟨n, prf.ax hpq⟩ },

    repeat {
      constructor,
      apply prf.k <|> apply prf.s <|> apply prf.exf <|>
      apply prf.pr1 <|> apply prf.pr2 <|> apply prf.pair <|> 
      apply prf.inr <|> apply prf.inl <|> apply prf.case,
      exact 0
    },

    { cases h_ih_hpq rfl with i h_ext_pq,
      cases h_ih_hp rfl with j h_ext_p,
      cases (prop_decidable (i ≤ j)),
      { have hn: j ≤ i :=
              begin
                cases nat.le_total,
                assumption,
                contradiction
            end,
        constructor,
        { apply prf.mp,
          { assumption },
          { apply prf.sub_weak,
            { exact h_ext_p },
            { apply insertn_mono,
              assumption } } } },
      { constructor,
        { apply prf.mp,
          { apply prf.sub_weak,
            { exact h_ext_pq },
            { apply insertn_mono, assumption } },
          { assumption } } } }
end

def prime_insertn_disj {Γ :  set form} {p q r : form} (h : (p ∨ q) ∈ prime Γ r) : 
  ∃ n, p ∈ (insertn (primen Γ r n) r (encodable.encode (p ∨ q)+1)) ∨ 
       q ∈ (insertn (primen Γ r n) r (encodable.encode (p ∨ q)+1)) :=
begin
  cases in_prime_in_primen h with n hpq,
  fapply exists.intro,
  { exact n },
  { unfold insertn insert_code,
    rw (encodable.encodek ((p ∨ q))),
    simp [insert_code, ite], 
    induction (prop_decidable _) with h1 h2,
    { exact false.elim (h1 (prf.sub_weak (prf.ax hpq) (subset_insertn))) },
    { simp [insert_form, ite],
      induction (prop_decidable _),
        { left,left, refl },
        { right,left, refl } } }
end

def prime_has_disj {Γ :  set form} {p q r : form} : 
  ((p ∨ q) ∈ prime Γ r) → p ∈ prime Γ r ∨ q ∈ prime Γ r :=
begin
  intro h, cases prime_insertn_disj h with n hpq, cases hpq,
  { left, apply insertn_to_prime hpq },
  { right, apply insertn_to_prime hpq }
end

/- prime is closed -/

lemma prime_prf_disj_self {Γ :  set form} {p r : form} : 
  (prime Γ r ⊢ᵢ r ∨ p) → ∃ n, p ∈ (insertn (primen Γ r n) r (encodable.encode (r ∨ p)+1)) :=
begin
  intros h,
  cases primen_sub_prf h with n hpq,
  constructor,
    unfold insertn insert_code,
    rw (encodable.encodek ((r ∨ p))),
    simp [insert_code, ite],
    induction (prop_decidable _) with h1 h2,
    { exact false.elim (h1 (prf.sub_weak hpq (subset_insertn))) },
    { simp [insert_form, ite],
      induction (prop_decidable _) with h1' h2',
      { apply false.elim,
        apply h1',
        apply prf.ax, 
        { left, refl} },
      { left, refl } }
end

def prime_is_closed {Γ :  set form} {p q r : form} : 
  (prime Γ r ⊢ᵢ p) → p ∈ prime Γ r :=
by { intros h, cases prime_prf_disj_self (prf.or_intro2 r h), apply insertn_to_prime, assumption' }

/- prime preserves consistency -/

lemma insertn_prf {Γ :  set form} {p : form} {i} : 
  (insertn Γ p i ⊢ᵢ p) → (Γ ⊢ᵢ p) :=
begin
  induction i,
  { simp }, 
  { simp [insertn, insert_code],
    cases (encodable.decode (form) _) with p,
    { assumption },
    { induction p,
        assumption',
        { simp [ite], 
          induction (prop_decidable _),
            { assumption },
            { simp [insert_form, ite],
              induction (prop_decidable _),
              { intro, contradiction },
              { intro, apply i_ih, 
                apply prf.or_elim,
                assumption' } } } } }
end

-- these two are better (positive)

def primen_not_prfn {Γ :  set form} {r : form} {n} : 
  (primen Γ r n ⊢ᵢ r) → (Γ ⊢ᵢ r) :=
begin
  induction n with k ih,
    simp,

    unfold primen,
    intro h,
    cases prf_primen_prf_insertn h,
    apply ih, apply insertn_prf h_1
end

def prime_not_prf {Γ :  set form} {r : form} : 
  (prime Γ r ⊢ᵢ r) → (Γ ⊢ᵢ r) :=
begin
  intros hm,
  cases primen_sub_prf hm,
  apply primen_not_prfn h
end

-- Closure under derivability

end  ctx

lemma prime_of_prime {Γ :  set form} {r : form} : 
 ctx.is_prime (ctx.prime Γ r) :=
begin
  split,
    intro, apply ctx.prime_is_closed, assumption,
    intros p q, apply ctx.prime_has_disj
end

lemma prime_no_prf {Γ :  set form} {r : form} (h : Γ ⊬ᵢ r) : 
 ctx.prime Γ r ⊬ᵢ r :=
λ hm, h (ctx.prime_not_prf hm)

/- the canonical model construction -/

-- domain

namespace canonical

def is_consist (Γ :  set form) := Γ ⊬ᵢ ⊥

def domain : set (wrld) := {w | is_consist w ∧  ctx.is_prime w}

-- accessibility

def access : wrld → wrld → Prop :=
λ w v, w ⊆ v

-- valuation

def val : ℕ → wrld → Prop :=
λ q w, w ∈ domain ∧ (#q) ∈ w

-- reflexivity

lemma access.refl :
  ∀ w ∈ domain, access w w :=
begin
  intros, unfold access
end

-- transitivity

lemma access.trans : ∀ w ∈ domain, ∀ v ∈ domain, ∀ u ∈ domain,
  access w v → access v u → access w u :=
begin
  unfold access,
  intros _ hw _ hu u  hu hwv hvu q hq,
  apply hvu, apply hwv, assumption
end

lemma access.mono :
∀ p, ∀ w1 w2 ∈ domain, 
val p w1 → access w1 w2 →  val p w2 :=
begin
  intros p w1 w2 hw1 hw2 vp1 w12,
  split,
  { assumption },
  { apply w12,
    exact vp1.2 }
end

def M : model :=
begin
  fapply model.mk,
    apply domain,
    apply access,
    apply val,
    apply access.refl,
    apply access.trans,
    apply access.mono
end

/- simple lemmas -/

lemma consist_of_not_prf {Γ :  set form} {p : form} : 
  (Γ ⊬ᵢ p) → is_consist Γ :=
λ nhp nc, nhp (prf.mp prf.exf nc)

/- truth is membership in the canonical model -/

lemma model_tt_iff_prf {p : form} : 
  ∀ (w ∈ domain), (w ⊩{M} p) ↔ (w ⊢ᵢ p) :=
begin
  induction p with p p q hp hq p q hp hq p q hp hq,
  -- atom 
  { intros, 
    split, 
    { intro h, exact prf.ax h.right },
    { intro,
      split, 
      { assumption },
      { apply H.2.1, assumption } } },
  -- ⊥
  { simp [forces_form],
    intros w H hn, exact H.1 hn },
  -- ⊃
  intros,
  split,
  { intro Hw,
    cases (em _),
    { assumption },
    { have hd : ctx.prime (w ⸴ p) q ∈ domain :=
        begin
          split,
          exact consist_of_not_prf (prime_no_prf (prf.contradeduction h)),
          apply prime_of_prime,
        end,
      apply false.elim,
      apply prime_no_prf (prf.contradeduction h),
      cases hq ( ctx.prime (w ⸴ p) q) _,
      apply mp,
      apply Hw _ hd,
      { exact H },
      intros p Hp,
      apply ctx.subset_prime_self,
      { right, assumption },
      { apply (hp (ctx.prime (w ⸴ p) q) _).2,
        { apply prf.ax,
          apply ctx.subset_prime_self,
          left, simp },
        exact hd },
      exact hd } },
  { intro hpq,
    intros v Hv Hw hwv hpv,
    apply (hq v Hv).2,
    apply prf.mp,
    { apply prf.sub_weak, assumption, assumption },
    { apply (hp v Hv).1, assumption } },
    -- &
    { intros, split,
      { intro hpq,
        apply prf.mp, apply prf.mp, apply prf.pair,
        apply (hp w H).1,
        exact hpq.1,
        apply (hq w H).1,
        exact hpq.2 },
      { intro hpq, split,
        apply (hp w H).2,
        apply prf.and_elim1 hpq,
        apply (hq w H).2,
        apply prf.and_elim2 hpq } },
    -- ∨ 
  { intros,
    split,
    { intro hpq,
      cases hpq,
      { apply prf.or_intro1,
        apply (hp w H).1 hpq },
      { apply prf.or_intro2,
        apply (hq w H).1 hpq } },
    { intro hpq,
      cases (H.2.2 (H.2.1 hpq)),
      { left, apply (hp w H).2,
        apply prf.ax, assumption },
      { right, apply (hq w H).2,
        apply prf.ax, assumption } } },
end

lemma ctx_tt_of_prf {Γ :  set form} (wm : Γ ∈ domain) : 
  (Γ ⊩{M} Γ) :=
by { intros p hp, apply (model_tt_iff_prf Γ wm).2, apply prf.ax, assumption }

/- the completeness theorem -/

theorem completeness {Γ :  set form} {p : form} : 
  (Γ ⊨ᵢ p) → (Γ ⊢ᵢ p) :=
begin
  apply (@not_imp_not (Γ ⊢ᵢ p) (Γ ⊨ᵢ p) (prop_decidable _)).1,
  intros nhp hp,
  have hd: ctx.prime Γ p ∈ domain :=
    begin
      split,
      apply consist_of_not_prf,
      exact prime_no_prf nhp, 
      apply (prime_of_prime)
    end,
  apply absurd,
  fapply hp,
  { exact M },
  { exact ctx.prime Γ p },
  { exact hd },

  { apply ctx_tt_to_subctx_tt,
    apply ctx_tt_of_prf hd,
    apply ctx.subset_prime_self },

  { intro hpm,
    apply prime_no_prf nhp,
    exact (model_tt_iff_prf _ hd).1 hpm },
end

end canonical