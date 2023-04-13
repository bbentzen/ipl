-- lem is invalid

def cW : set (wrld) := {{atom 0}, {atom 1}}

def cR : wrld → wrld → Prop :=  --- w0 sees w1 
λ w v, w = v ∨ w = {atom 0} 

lemma cRrefl : ∀ w : wrld, w ∈ cW → (cR) w w :=
begin
  intros w h, unfold cR,
  left, refl
end

example {p q r: Prop}: (p → (q → r)) → ((p → q) → (p → r)) :=
λ hpqr hpq hp, (hpqr hp)(hpq hp)

lemma cRtrans : ∀ w ∈ cW, ∀ v ∈ cW, ∀ u ∈ cW,
 (cR) w v → (cR) v u → (cR) w u :=
begin
  intros w v u hw hv hu rwv rvu,
  cases rwv, 
    rw rwv, assumption,
    cases rvu, rw rvu.symm, right, assumption,

    right, assumption
end

@[simp]
def cval : nat → wrld → Prop :=
λ _ w, w = {atom 1}

def atom0_ne_atom1 : #0 ≠ #1 :=
λ h, (@form.no_confusion false #0 #1 h) zero_ne_one

def counterex : model :=
begin
  fapply model.mk,
  exact cW,
  exact cR,
  exact cval,
  exact cRrefl,
  exact cRtrans,
  exact cmono
end

lemma counterex_lem {p : form} : 
  ¬ ({#0} ⊩{counterex} (#0 ∨ ~#0)) :=
begin
  intro h, 
  cases h,
  simp at h, revert h, unfold counterex, simp,
  fapply h,
  exact {#1},
  left, refl,
  right, simp,
  right, refl,
  unfold counterex, simp
end


lemma no_lem {p : form} : 
 ¬ (∅ ⊨ᵢ p ∨ ~p) :=
begin
  intro h,  
end

