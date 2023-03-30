/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad and Bruno Bentzen
-/

import .encodable ..language

namespace form

private def constructors:= ℕ ⊕ unit ⊕ unit ⊕ unit ⊕ unit

local notation `catom` v := sum.inl v
local notation `cbot`    := sum.inr (sum.inl unit.star)
local notation `cimpl`   := sum.inr (sum.inr (sum.inl unit.star))
local notation `cand`    := sum.inr (sum.inr (sum.inr (sum.inl unit.star)))
local notation `cor`     := sum.inr (sum.inr (sum.inr (sum.inr unit.star)))

@[simp]
private def arity: constructors → nat
| (catom v) := 0
| cbot      := 0
| cimpl     := 2
| cand      := 2
| cor       := 2

variable {σ : nat}

private def f : form → Wfin arity
| (atom v)   := ⟨catom v, fin.mk_fn0⟩
| (bot)    := ⟨cbot, fin.mk_fn0⟩
| (impl p q) := ⟨cimpl, fin.mk_fn2 (f p) (f q)⟩
| (and p q) := ⟨cand, fin.mk_fn2 (f p) (f q)⟩
| (or p q) := ⟨cor, fin.mk_fn2 (f p) (f q)⟩

private def finv : Wfin arity → form
| ⟨catom a, fn⟩ := atom a 
| ⟨cbot, fn⟩    := bot
| ⟨cimpl, fn⟩   := impl (finv (fn ⟨0, dec_trivial⟩)) (finv (fn ⟨1, dec_trivial⟩))
| ⟨cand, fn⟩   := and (finv (fn ⟨0, dec_trivial⟩)) (finv (fn ⟨1, dec_trivial⟩))
| ⟨cor, fn⟩   := or (finv (fn ⟨0, dec_trivial⟩)) (finv (fn ⟨1, dec_trivial⟩))

instance [encodable ℕ] : encodable form :=
begin
  haveI : encodable (constructors σ) :=
    by { unfold constructors, apply_instance },
  exact encodable.of_left_inverse f finv (by { intro p, induction p; simp [f, finv, *] })
end

end form