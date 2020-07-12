import algebra.group.basic
import group_theory.subgroup
import data.zmod.basic
import data.equiv.basic
import tactic

universes u v

namespace equiv.perm
open equiv function subgroup

variables {α : Type u}

lemma perms_eq_fun_eq {X : Type u} (p : perm X) (q : perm X) (h : p.to_fun = q.to_fun) : p = q := 
begin 
   apply perm.ext,
   intro x,
   exact congr_fun h x,
end 

lemma notcayleys {X : Type u} {Y : Type v} (h : X ≃ Y) : perm X ≃* perm Y :=
begin 
   let F := λ (p : perm X), ({
      to_fun := h.1 ∘ p.1 ∘ h.2,
      inv_fun := h.1 ∘ p.2 ∘ h.2,
      left_inv := λ y, by simp [left_inverse.id h.3, left_inverse.id p.3, right_inverse.id h.4],
      right_inv := λ y, by simp [left_inverse.id h.3, left_inverse.id p.4, left_inverse.id h.4],
   } : perm Y),
   let G := λ (p : perm Y), ({
      to_fun := h.2 ∘ p.1 ∘ h.1,
      inv_fun := h.2 ∘ p.2 ∘ h.1,
      left_inv := λ y, by simp [right_inverse.id h.4, left_inverse.id p.3, right_inverse.id h.3],
      right_inv := λ y, by simp [right_inverse.id h.4, left_inverse.id p.4, right_inverse.id h.3],
   } : perm X),
   have leftinv : left_inverse G F,
   {
      intro p,
      apply perms_eq_fun_eq _ _,
      calc (G (F p)).to_fun = (h.inv_fun ∘ h.to_fun) ∘ p.to_fun ∘ h.inv_fun ∘ h.to_fun : rfl 
      ... = id ∘ p.to_fun ∘ h.inv_fun ∘ h.to_fun : by rw right_inverse.id h.3
      ... = p.to_fun ∘ (h.inv_fun ∘ h.to_fun) : rfl 
      ... = p.to_fun ∘ id : by rw right_inverse.id h.3,
   },
   have rightinv : right_inverse G F,
   {
      intro p, 
      apply perms_eq_fun_eq _ _,
      calc (F (G p)).to_fun = (h.to_fun ∘ h.inv_fun) ∘ p.to_fun ∘ h.to_fun ∘ h.inv_fun : rfl 
      ... = id ∘ p.to_fun ∘ h.to_fun ∘ h.inv_fun : by rw left_inverse.id h.4
      ... = p.to_fun ∘ (h.to_fun ∘ h.inv_fun) : rfl 
      ... = p.to_fun ∘ id : by rw left_inverse.id h.4,
   },
   have perm_mul : ∀ (x y : perm X), F (x * y) = F x * F y,
   {
      intros p q,
      have HH := p * q,
      apply perms_eq_fun_eq _ _,
      apply conj_comp h p.to_fun q.to_fun,
   },
   exact ⟨F, G, leftinv, rightinv, perm_mul⟩,
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

end equiv.perm