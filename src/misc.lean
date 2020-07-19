import algebra.group.basic
import data.zmod.basic
import data.equiv.basic
import tactic
import data.set.basic 

import .cayleys

variables {G₁ : Type*} {G₂ : Type*} [group G₁] [group G₂]

open equiv function set

def hom_induces_group (f : G₁ →* G₂) : group (range f) :=
{ mul := has_mul.mul,
  mul_assoc := mul_assoc,
  one := has_one.one,
  one_mul := one_mul,
  mul_one := mul_one,
  inv := has_inv.inv,
  mul_left_inv := mul_left_inv,
}

def ψ (h : G₁ ≃* G₂): perm G₁ → perm G₂ := λ θ, 
{ to_fun := h.1 ∘ θ.1 ∘ h.2,
  inv_fun := h.1 ∘ θ.2 ∘ h.2,
  left_inv := begin
    intro x,
    calc (h.to_fun ∘ θ.inv_fun ∘ h.inv_fun) ((h.to_fun ∘ θ.to_fun ∘ h.inv_fun) x) 
          = (h.to_fun ∘ θ.inv_fun ∘ (h.inv_fun ∘ h.to_fun) ∘ θ.to_fun ∘ h.inv_fun) x : rfl 
      ... = (h.to_fun ∘ θ.inv_fun ∘ id ∘ θ.to_fun ∘ h.inv_fun) x : by rw left_inverse.id h.3
      ... = (h.to_fun ∘ (θ.inv_fun ∘ θ.to_fun) ∘ h.inv_fun) x : rfl 
      ... = (h.to_fun ∘ id ∘ h.inv_fun) x : by rw left_inverse.id θ.3
      ... = (h.to_fun ∘ h.inv_fun) x : rfl 
      ... = id x : by rw right_inverse.id h.4,
  end,
  right_inv := begin 
    intro x,
    calc (h.to_fun ∘ θ.to_fun ∘ h.inv_fun) ((h.to_fun ∘ θ.inv_fun ∘ h.inv_fun) x)
          = (h.to_fun ∘ θ.to_fun ∘ (h.inv_fun ∘ h.to_fun) ∘ θ.inv_fun ∘ h.inv_fun) x : rfl 
      ... = (h.to_fun ∘ θ.to_fun ∘ id ∘ θ.inv_fun ∘ h.inv_fun) x : by rw left_inverse.id h.3
      ... = (h.to_fun ∘ (θ.to_fun ∘ θ.inv_fun) ∘ h.inv_fun) x : rfl 
      ... = (h.to_fun ∘ id ∘ h.inv_fun) x : by rw right_inverse.id θ.4 
      ... = (h.to_fun ∘ h.inv_fun) x : rfl 
      ... = id x : by rw right_inverse.id h.4,
  end,
}

lemma embedding_diagram_com (h : G₁ ≃* G₂) 
  : (ψ h) ∘ (lift_to_perm G₁).1 = (lift_to_perm G₂).1 ∘ h.1 := begin 
  ext g x,
  have H₁ : ((ψ h ∘ (lift_to_perm G₁).to_fun) g) x = (h.1 g) * x,
    calc ((ψ h ∘ (lift_to_perm G₁).to_fun) g) x 
          = h.1 (g * (h.2 x)) : rfl 
      ... = (h.1 g) * (h.1 (h.2 x)) : mul_equiv.map_mul h g (h.inv_fun x) 
      ... = (h.1 g) * ((h.1 ∘ h.2) x) : rfl 
      ... = (h.1 g) * (id x) : by rw right_inverse.id h.4,
  have H₂ : (((lift_to_perm G₂).to_fun ∘ h.1) g) x = (h.1 g) * x := rfl,
  rw [H₁, H₂],
end 