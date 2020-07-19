import algebra.group.basic
import data.zmod.basic
import data.equiv.basic
import tactic

import data.set.basic

universes u v

open equiv function set

lemma perms_eq_fun_eq {X : Type u} (p : perm X) (q : perm X) (h : p.to_fun = q.to_fun) : p = q := 
begin 
  apply perm.ext,
  intro x,
  exact congr_fun h x,
end 

def notcayleys {X : Type u} {Y : Type v} (h : X ≃ Y) : perm X ≃* perm Y :=
begin 
  let F := λ (p : perm X), ({
    to_fun    := h.1 ∘ p.1 ∘ h.2,
    inv_fun   := h.1 ∘ p.2 ∘ h.2,
    left_inv  := λ y, by simp,
    right_inv := λ y, by simp,
  } : perm Y),
  let G := λ (p : perm Y), ({
    to_fun    := h.2 ∘ p.1 ∘ h.1,
    inv_fun   := h.2 ∘ p.2 ∘ h.1,
    left_inv  := λ y, by simp,
    right_inv := λ y, by simp,
  } : perm X),
  exact ⟨F, G, λ x, by {ext, simp}, λ x, by {ext, simp}, 
         λ p q, by {apply perms_eq_fun_eq (F (p * q)) ((F p) * (F q)), 
                    apply conj_comp h p.to_fun q.to_fun}⟩,
end

def lift_to_perm (G : Type*) [group G] : G →* perm G := {
  to_fun := λ g, {
    to_fun    := λ x, g * x,
    inv_fun   := λ x, g⁻¹ * x,
    left_inv  := λ h, by simp,
    right_inv := λ h, by simp
  },
  map_one' := by {ext, simp},
  map_mul' := λ g h, by {ext, simp [mul_assoc _ _ _]},
}

theorem cayleys (G : Type*) [group G] : ∃ (f : G →* perm G), injective f := 
begin
  use lift_to_perm G,
  intros g₁ g₂ h,
  suffices H : ((lift_to_perm G).to_fun g₁) 1 = ((lift_to_perm G).to_fun g₂) 1,
  { have h₁ : ((lift_to_perm G).to_fun g₁) 1 = g₁ * 1 := rfl,
    have h₂ : ((lift_to_perm G).to_fun g₂) 1 = g₂ * 1 := rfl,
    rw [h₁, h₂] at H,
    exact (mul_left_inj 1).mp H,
  },
  exact congr_fun (congr_arg coe_fn h) 1,
end

variables {G₁ : Type*} {G₂ : Type*} [group G₁] [group G₂]

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
  have H₂ : (((lift_to_perm G₂).to_fun ∘ h.1) g) x = (h.1 g) * x, by refl,
  rw [H₁, H₂],
end 

def hom_induces_group (f : G₁ →* G₂) : group (range f) :=
{ mul := has_mul.mul,
  mul_assoc := mul_assoc,
  one := has_one.one,
  one_mul := one_mul,
  mul_one := mul_one,
  inv := has_inv.inv,
  mul_left_inv := mul_left_inv,
}

noncomputable def inj_hom_induces_iso (f : G₁ →* G₂) (h_inj : injective f) : G₁ ≃* range f :=
{ to_fun    := λ g, ⟨f g, set.mem_range_self g⟩,
  inv_fun   := begin 
    rintro ⟨a, b⟩,
    choose h hk using b,
    exact h,
  end,
  left_inv  := begin
    intro x,
    simp,
    apply h_inj,
    have H : f x ∈ range f := set.mem_range_self x,
    rw classical.some_spec H,
  end,
  right_inv := begin 
    intro y,
    ext,
    rcases y with ⟨y, ⟨x, hx⟩⟩,
    simp,
    have H := Exists.intro x hx,
    rw classical.some_spec H,
  end,
  map_mul'  := λ x y, by {ext, simp},
}
