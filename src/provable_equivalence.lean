import definitions
import category
import entails

namespace TT
open entails

def entails_eq (A : type) (a₁ a₂ : tset A) := ⊨ (a₁ ≃ a₂)

section equivalence_relation

  variable A : type

  theorem entails_eq_refl : reflexive (entails_eq A) :=
    λ α, by { apply intro_eq, any_goals {WF_prover}, apply entails.all_intro, refine entails.iff_refl; WF_prover; refl}

  theorem entails_eq_symm : symmetric (entails_eq A) :=
    λ α β ent_eq, by {apply all_intro, apply entails.and_comm, apply all_elim, assumption}

  theorem entails_eq_trans : transitive (entails_eq A) :=
    λ α β θ ent_αβ ent_βθ, all_intro $ iff_trans (^↑β ∈ ↑0) (all_elim ent_αβ) (all_elim ent_βθ)

  theorem entails_eq_equiv : equivalence (entails_eq A) :=
    ⟨entails_eq_refl A, entails_eq_symm A, entails_eq_trans A⟩

end equivalence_relation

section setoid

  def TT.setoid (A : type) : setoid (tset A) := 
    {r := entails_eq A, iseqv := entails_eq_equiv A}

  local attribute [instance] TT.setoid

  variable A : type

  def tsetoid := quotient (TT.setoid A)

  def to_tsetoid := quot.mk (entails_eq A)

  def coe_tset_tsetoid : has_coe (tset A) (tsetoid A) := ⟨to_tsetoid A⟩
  local attribute [instance] coe_tset_tsetoid
    
  def tset.star_singleton : tsetoid 𝟙 :=
    by {apply to_tsetoid, apply tset.mk _ ⟦𝟙 | ⊤⟧, apply WF.comp, exact WF.top}

end setoid

section



  def AB_setoid : setoid (tset (A 𝕏 B)) := TT.setoid (A 𝕏 B)

  local attribute [instance] AB_setoid

  def lifted_is_subset_of_terms {A B : type} : tset A → tset B → tsetoid (A 𝕏 B) → Prop := 
    λ α β, (
      quotient.lift 
        (λ F : tset (A 𝕏 B), ⊨ F ⊆ α 𝕏 β)
        (begin
          intros F₁ F₂ heq,
          simp,
          constructor; sorry
        end)
    )

end

end TT