-- lem is invalid
import .semantics
open form
namespace no_lem
def W : set (wrld) := {{atom 0}, {atom 1}}

def R : wrld → wrld → Prop :=  --- w0 sees w1 
λ w v, w = v ∨ w = {atom 0} 

lemma Rrefl : ∀ w : wrld, w ∈ W → R w w :=
begin
  intros w h, unfold R,
  left, refl
end

lemma Rtrans : ∀ w ∈ W, ∀ v ∈ W, ∀ u ∈ W,
 R w v → R v u → R w u :=
begin
  intros w v u hw hv hu rwv rvu,
  cases rwv, 
    rw rwv, assumption,
    cases rvu, rw rvu.symm, right, assumption,
    right, assumption
end

@[simp]
def val : nat → wrld → Prop :=
λ _ w, w = {atom 1}

def M : model :=
begin
  fapply model.mk,
  exact W,
  exact R,
  exact val,
  exact Rrefl,
  exact Rtrans,
end

lemma M_lem : 
  ¬ ({#0} ⊩{M} (#0 ∨ ~#0)) :=
begin
  intro h, 
  cases h,
  simp at h, revert h, unfold M, simp,
  fapply h,
  exact {#1},
  left, refl,
  right, simp,
  right, refl,
  unfold M, simp
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

