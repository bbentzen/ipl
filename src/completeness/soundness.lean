/-
Copyright (c) 2023 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Dongheng Chen, Huayu Guo
-/
import .theory .semantics

theorem soundness {Γ :  set form} {p : form} : 
  (Γ ⊢ᵢ p) → (Γ ⊨ᵢ p) :=
begin
intro h,
induction h,
intros M w h_w,
simp,
intro b,
apply b,
assumption,

intros M w h_w,
simp,
intros a w_1 hw1 hw vww hw1p w_2 hw2 _ vw_1w_2 hw2p,
apply mono_r,
exact hw1,
assumption',

intros M w1 iw1 hwΓ w2 whp1 _ rwhp whpqr w3 iw3 whp3 whpw3 w3hpq w4 iw4  _ rw34 hp4,

--apply semmp,
--assumption',
have h: (w4 ⊩ {M} h_q ⊃ h_r),
apply whpqr,
assumption',
apply M.trans,
assumption,
apply iw3,
assumption',

apply h,
assumption',
apply M.refl,
assumption,
have h': (w4 ⊩ {M} h_p ⊃ h_q),
exact mono_r (h_p ⊃ h_q) w3 w4 iw3 iw4 w3hpq rw34,
apply h',
assumption',
apply M.refl,
assumption',

intros _ _ _ _,
simp,

intros M w hw wΓ,
apply h_ih_hpq,
assumption',
apply M.refl,
assumption,
apply h_ih_hp,
exact hw,
apply wΓ,

intros M w1 iw1 hwΓ w2 iw2 _ vw12 h,
cases h with hp hq,
apply hp,

intros M w1 iw1 hwΓ w2 iw2 _ vw12 h,
cases h with hp hq,
apply hq,

intros M w1 iw1 hwΓ w2 iw2 _ vw12 hp w3 iw3 _ vw23 w3q,
split,
apply mono_r,
apply iw2,
assumption',

intros M w1 iw1 hwΓ w2 iw2 _ vw12 hp3,
left,
exact hp3,

intros _ _ _ _ _ _ _ _ hp3,
right,
exact hp3,

intros M w1 iw1 _ w2 _ _ _ hp3 _ iw3 _ _ w3qr _ _ _ _ w4pq,
cases w4pq with hp hq,
apply hp3,
assumption',
apply M.trans,
assumption,
exact iw3,
assumption,
apply M.trans,
assumption,
exact iw3,
assumption',
apply M.refl,
assumption,
apply w3qr,
assumption',
end