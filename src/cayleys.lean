import algebra.group.basic
import data.zmod.basic
import data.equiv.basic
import tactic

import data.set.basic

universes u v

open equiv function set

variables (G : Type u) [group G]

lemma perms_eq_fun_eq {X : Type u} (p : perm X) (q : perm X) (h : p.to_fun = q.to_fun) : p = q := 
begin 
  apply perm.ext,
  intro x,
  exact congr_fun h x,
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

lemma lift_to_perm_inj {G : Type*} [group G] : injective (lift_to_perm G) := 
begin 
  intros g₁ g₂ h,
  have H : ((lift_to_perm G) g₁) 1 = ((lift_to_perm G) g₂) 1, rw h,
  exact (mul_left_inj 1).mp H,
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

theorem cayleys (G : Type*) [group G] : ∃ (f : G →* perm G), injective f := 
begin
  use lift_to_perm G,
  exact lift_to_perm_inj,
end

variables {G₁ : Type*} {G₂ : Type*} [group G₁] [group G₂]

noncomputable 
def inj_hom_induces_iso (f : G₁ →* G₂) (h_inj : injective f) : G₁ ≃* range f :=
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

noncomputable 
theorem cayleys2 {G : Type*} [group G] : G ≃* range (lift_to_perm G) 
:= inj_hom_induces_iso (lift_to_perm G) lift_to_perm_inj