/-
Copyright (c) 2023 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import ..encoding.encode .theory .semantics

open nat set classical

local attribute [instance, priority 0] prop_decidable

variables {σ : nat}

/- maximal set of a context -/

namespace ctx

def is_closed (Γ : ctx σ) := 
∀ {p : form σ}, (Γ ⊢ᵢ p) → p ∈ Γ

def has_disj (Γ : ctx σ) := 
∀ {p q : form σ}, ((p ∨ q) ∈ Γ) → ((p ∈ Γ) ∨ (q ∈ Γ))

def is_max (Γ : ctx σ) := 
is_closed Γ ∧ has_disj Γ

/-- extension -/

def insert_form (Γ : ctx σ) (p q r : form σ) : ctx σ :=
if (Γ ⸴ p ⊢ᵢ r) then Γ ⸴ q else Γ ⸴ p

@[simp]
def insert_code (Γ : ctx σ) (r : form σ) (n : nat) : ctx σ :=
match encodable.decode (form σ) n with
| none := Γ
| some (p ∨ q) := if Γ ⊢ᵢ p ∨ q then insert_form Γ p q r else Γ
| some _ := Γ
end

@[simp]
def insertn (Γ : ctx σ) (r : form σ) : nat → ctx σ
| 0     := Γ 
| (n+1) := insert_code (insertn n) r n 

@[simp]
def maxn (Γ : ctx σ) (r : form σ) : nat → ctx σ
| 0     := Γ
| (n+1) := ⋃ i, insertn (maxn n) r i 

@[simp]
def max (Γ : ctx σ) (r : form σ) : ctx σ := 
⋃ n, maxn Γ r n

/- max extends the original set -/

lemma subset_insert_code {Γ : ctx σ} {r : form σ} (n) :
  Γ ⊆ insert_code Γ r n :=
begin
  intros v hv, simp, 
  cases (encodable.decode (form σ) _),
    { assumption },
    { induction val,
      repeat { assumption },
      unfold insert_code ite,
      induction (prop_decidable _),
      { assumption },
      { unfold insert_form ite, 
      induction (prop_decidable _),
        repeat { right, assumption } } }
end

lemma maxn_subset_max {Γ : ctx σ} {r : form σ} (n) :
  maxn Γ r n ⊆ max Γ r :=
subset_Union _ _

lemma subset_insertn {Γ : ctx σ} {r : form σ} {n} :
  Γ ⊆ insertn Γ r n :=
begin
  induction n,
  { simp }, 
  { simp, cases (encodable.decode (form σ) _) with p,
    { assumption },
      induction p,
        repeat {assumption},
      { simp [ite], 
        induction (prop_decidable _),
        { simp, assumption },
        { simp [insert_form, ite], 
          induction (prop_decidable _),
            repeat {intros q hq, right, exact n_ih hq} } } }
end

lemma subset_max_self {Γ : ctx σ} {r : form σ} :
  Γ ⊆ max Γ r :=
maxn_subset_max 0

lemma insertn_sub_maxn {Γ : ctx σ} {r : form σ} {n m : nat} :
  insertn (maxn Γ r n) r m ⊆ maxn Γ r (n+1) :=
subset_Union _ _

lemma insertn_to_max {Γ : ctx σ} {r : form σ} {n m : nat} :
  insertn (maxn Γ r n) r m ⊆ max Γ r :=
by induction m; 
[ apply maxn_subset_max, 
  exact subset.trans insertn_sub_maxn (maxn_subset_max _) ]

/- max has the disjunction property -/

lemma in_max_in_maxn {Γ : ctx σ} {p r : form σ} :
  (p ∈ max Γ r ) → ∃ n, p ∈ maxn Γ r n :=
mem_Union.1

lemma in_maxn_in_insertn {Γ : ctx σ} {p r : form σ} {n} :
  (p ∈ maxn Γ r (n+1) ) → ∃ i, p ∈ insertn (maxn Γ r n) r i :=
mem_Union.1

lemma maxn_subset_succ {Γ : ctx σ} {r : form σ} {n : nat} :
  maxn Γ r n ⊆ maxn Γ r (n+1) :=
begin
  apply subset.trans,
  { apply subset_insertn,
    repeat {assumption} },
  { exact subset_Union _ _}
end

lemma maxn_mono {Γ : ctx σ} {r : form σ} {m n : nat} (h : n ≤ m) :
  maxn Γ r n ⊆ maxn Γ r m :=
by induction h; [refl, exact subset.trans h_ih maxn_subset_succ ]

lemma insertn_mono {Γ : ctx σ} {r : form σ} {m n : nat} (h : n ≤ m) :
  insertn Γ r n ⊆ insertn Γ r m :=
by induction h; [refl, exact subset.trans h_ih (subset_insert_code _)]

def maxn_sub_prf {Γ : ctx σ} {p r : form σ} : 
  (max Γ r ⊢ᵢ p) → ∃ n, maxn Γ r n ⊢ᵢ p :=
begin
  generalize eq : max Γ r = Γ',
  intro h, induction h; subst eq,
  { cases in_max_in_maxn h_h with n hpq,
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
          { apply maxn_mono,
            assumption } } } },
    { constructor,
      { apply prf.mp,
        { apply prf.sub_weak,
          { exact h_ext_pq },
          { apply maxn_mono,
            assumption } },
          assumption } } }
end

lemma prf_maxn_prf_insertn {Γ : ctx σ} {p r : form σ} {n} :
  (maxn Γ r (n+1) ⊢ᵢ p) → ∃ i, insertn (maxn Γ r n) r i ⊢ᵢ p :=
begin
  generalize eq : maxn Γ r (n+1) = Γ',
  intro h, induction h; subst eq,
  { cases in_maxn_in_insertn h_h with n hpq,
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

def max_insertn_disj {Γ : ctx σ} {p q r : form σ} (h : (p ∨ q) ∈ max Γ r) : 
  ∃ n, p ∈ (insertn (maxn Γ r n) r (encodable.encode (p ∨ q)+1)) ∨ 
       q ∈ (insertn (maxn Γ r n) r (encodable.encode (p ∨ q)+1)) :=
begin
  cases in_max_in_maxn h with n hpq,
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

def max_has_disj {Γ : ctx σ} {p q r : form σ} : 
  ((p ∨ q) ∈ max Γ r) → p ∈ max Γ r ∨ q ∈ max Γ r :=
begin
  intro h, cases max_insertn_disj h with n hpq, cases hpq,
  { left, apply insertn_to_max hpq },
  { right, apply insertn_to_max hpq }
end

/- max is closed -/

lemma max_prf_disj_self {Γ : ctx σ} {p r : form σ} : 
  (max Γ r ⊢ᵢ r ∨ p) → ∃ n, p ∈ (insertn (maxn Γ r n) r (encodable.encode (r ∨ p)+1)) :=
begin
  intros h,
  cases maxn_sub_prf h with n hpq,
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

def max_is_closed {Γ : ctx σ} {p q r : form σ} : 
  (max Γ r ⊢ᵢ p) → p ∈ max Γ r :=
by { intros h, cases max_prf_disj_self (prf.or_intro2 r h), apply insertn_to_max, repeat {assumption} }

/- max preserves consistency -/

lemma insertn_prf {Γ : ctx σ} {p : form σ} {i} : 
  (insertn Γ p i ⊢ᵢ p) → (Γ ⊢ᵢ p) :=
begin
  induction i,
  { simp }, 
  { simp [insertn, insert_code],
    cases (encodable.decode (form σ) _) with p,
    { assumption },
    { induction p,
        repeat {assumption},
        { simp [ite], 
          induction (prop_decidable _),
            { assumption },
            { simp [insert_form, ite],
              induction (prop_decidable _),
              { intro, contradiction },
              { intro, apply i_ih, 
                apply prf.or_elim,
                repeat {assumption } } } } } }
end

-- these two are better (positive)

def maxn_not_prfn {Γ : ctx σ} {p : form σ} {n} : 
  (maxn Γ p n ⊢ᵢ p) → (Γ ⊢ᵢ p) :=
begin
  induction n with k ih,
    simp,

    unfold maxn,
    intro h,
    cases prf_maxn_prf_insertn h,
    apply ih, apply insertn_prf h_1
end

def max_not_prf {Γ : ctx σ} {p : form σ} : 
  (max Γ p ⊢ᵢ p) → (Γ ⊢ᵢ p) :=
begin
  intros hm,
  cases maxn_sub_prf hm,
  apply maxn_not_prfn h
end

-- Closure under derivability

end ctx

lemma max_of_max {Γ : ctx σ} {r : form σ} : 
ctx.is_max (ctx.max Γ r) :=
begin
  split,
    intro, apply ctx.max_is_closed, assumption,
    intros p q, apply ctx.max_has_disj
end

lemma max_no_prf {Γ : ctx σ} {r : form σ} (h : Γ ⊬ᵢ r) : 
ctx.max Γ r ⊬ᵢ r :=
λ hm, h (ctx.max_not_prf hm)

/- the canonical model construction -/

-- domain

namespace canonical

def is_consist (Γ : ctx σ) := Γ ⊬ᵢ ⊥

def domain (σ : nat) : set (wrld σ) := {w | is_consist w ∧ ctx.is_max w}

-- accessibility

def access : wrld σ → wrld σ → Prop :=
λ w v, w ⊆ v

-- valuation

def val : fin σ → wrld σ → Prop :=
λ q w, w ∈ domain σ ∧ (#q) ∈ w

-- reflexivity

lemma access.refl :
  ∀ w ∈ domain σ, access w w :=
begin
  intros, unfold access
end

-- transitivity

lemma access.trans : ∀ w ∈ domain σ, ∀ v ∈ domain σ, ∀ u ∈ domain σ,
  access w v → access v u → access w u :=
begin
  unfold access,
  intros _ hw _ hu u  hu hwv hvu q hq,
  apply hvu, apply hwv, assumption
end

def model : @model σ :=
begin
  fapply model.mk,
    apply domain σ,
    apply access,
    apply val,
    apply access.refl,
    apply access.trans
end

/- simple lemmas -/

lemma consist_of_not_prf {Γ : ctx σ} {p : form σ} : 
  (Γ ⊬ᵢ p) → is_consist Γ :=
λ nhp nc, nhp (prf.mp prf.exf nc)

/- truth is membership in the canonical model -/

lemma model_tt_iff_prf {p : form σ} : 
  ∀ (w ∈ domain σ), (w ⊩⦃model⦄ p) ↔ (w ⊢ᵢ p) :=
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
    { have hd : ctx.max (w ⸴ p) q ∈ domain σ :=
        begin
          split,
          exact consist_of_not_prf (max_no_prf (prf.contradeduction h)),
          apply max_of_max,
        end,
      apply false.elim,
      apply max_no_prf (prf.contradeduction h),
      cases hq (ctx.max (w ⸴ p) q) _,
      apply mp,
      apply Hw _ hd,
      { exact H },
      intros p Hp,
      apply ctx.subset_max_self,
      { right, assumption },
      { apply (hp (ctx.max (w ⸴ p) q) _).2,
        { apply prf.ax,
          apply ctx.subset_max_self,
          left, simp },
        exact hd },
      exact hd } },
  { intro hpq,
    intros v Hv Hw hwv hp2,
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

lemma ctx_tt_of_prf {Γ : ctx σ} (wm : Γ ∈ domain σ) : 
  (Γ ⊩⦃model⦄ Γ) :=
by { intros p hp, apply (model_tt_iff_prf Γ wm).2, apply prf.ax, assumption }

/- the completeness theorem -/

theorem completeness {Γ : ctx σ} {p : form σ} : 
  (Γ ⊨ᵢ p) → (Γ ⊢ᵢ p) :=
begin
  apply (@not_imp_not (Γ ⊢ᵢ p) (Γ ⊨ᵢ p) (prop_decidable _)).1,
  intros nhp hp,
  have hd: ctx.max Γ p ∈ domain σ :=
    begin
      split,
      apply consist_of_not_prf,
      exact max_no_prf nhp, 
      apply (max_of_max)
    end,
  apply absurd,
  fapply hp,
  { exact model },
  { exact ctx.max Γ p },
  { exact hd },

  { apply ctx_tt_to_subctx_tt,
    apply ctx_tt_of_prf hd,
    apply ctx.subset_max_self },

  { intro hpm,
    apply max_no_prf nhp,
    exact (model_tt_iff_prf _ hd).1 hpm },
end

end canonical
