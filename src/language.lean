/-
Copyright (c) 2023 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

variable σ : nat

/- language definition -/

inductive form : Type
| atom : fin σ → form
| bot : form
| impl : form → form → form
| and : form → form → form
| or : form → form → form

prefix `#` := form.atom
notation `⊥` := form.bot _
infix `⊃` := form.impl
notation p `&` q := form.and p q
notation p `∨` q := form.or p q
notation `~`:40 p := form.impl p (form.bot _)

/- context notation -/

@[reducible]
def ctx (σ : nat) : Type := set (form σ)

notation `·` := {}
notation Γ ` ⸴ ` p := set.insert p Γ