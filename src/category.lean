/-
The associated category of a type theory

Author: Billy Price
-/
import category_theory.category
import TL
import lemmas



namespace TT

section 
  variable A : type

  def closed : type → term → Prop := WF list.nil

  def tset (A: type) := {α : term // WF [] (𝒫 A) α}

  def tset.mk (α : term) : closed (𝒫 A) α → tset A:= subtype.mk α

  instance tset_has_coe : has_coe (tset A) term := coe_subtype

  def empty_tset (A : type) : tset A := tset.mk A ⟦A | ⊥⟧ (by apply_rules WF_rules)

  def singleton_star : tset Unit := tset.mk Unit ⟦Unit | ⊤⟧ (by apply_rules WF_rules)

  def is_graph {A B: type} (α : tset A) (β : tset B) (F : tset (A ×× B)) : Prop :=
    ⊨ (F ⊆[𝒫 A] (term_prod A B α β)) ⋀ (∀' A ((𝟘 ∈ α) ⟹ (∃!' B $ ⟪𝟙,𝟘⟫ ∈ F)))

  def graph {A B} (α : tset A) (β : tset B) := {F : tset (A ×× B) // is_graph α β F}
  
  instance graph_has_tset_coe (A B : type) (α : tset A) (β : tset B) : has_coe (graph α β) (tset (A ×× B)) := coe_subtype

  def graph.mk {A B} {α : tset A} {β : tset B} (F : tset (A ×× B)) : is_graph α β F → graph α β := subtype.mk F

  def id_graph {A} (α : tset A) : graph α α :=
  begin
    refine graph.mk _ _,
    refine tset.mk _ (term_prod A A α α) _,
    apply_rules WF_rules,
    any_goals {apply rfl},
    sorry,
    sorry,
    sorry,
  end

  def composition {A B E: type} {α : tset A} {β : tset B} {η : tset E} (F : graph α β) (G : graph β η)  : graph α η :=
  begin
    fapply graph.mk,
    apply tset.mk (A ×× E) ⟦ A ×× E | ∃' A (∃' E ((𝟚 ≃[A ×× E] ⟪𝟙,𝟘⟫) ⋀ (∃' B ((⟪𝟚,𝟘⟫ ∈ F) ⋀ (⟪𝟘, 𝟙⟫ ∈ G)))))⟧,
    apply WF.comp,
    apply WF.ex,
    apply WF.ex,
    apply WF.and,
    {apply WF.eq_intro, apply WF.var, refl, apply WF.pair, apply WF.var, refl, apply WF.var, refl},
    apply WF.ex,
    apply WF.and,
      {apply WF.elem, apply WF.pair, apply WF.var;refl, apply WF.var;refl, sorry},
      {apply WF.elem, apply WF.pair, apply WF.var;refl, apply WF.var;refl, sorry},
    sorry
  end

  #check id_graph 

end


end TT

namespace category_theory

namespace TT

open TT

-- instance category : small_category (Σ A : type, tset A) :=
-- { hom := λ ⟨A,α⟩ ⟨B,β⟩, graph α β,
--   id := λ ⟨A,α⟩, id_graph α,
--   -- comp := λ A B E F G, composition F G,
--   -- id_comp' := λ C D F, by cases F; refl,
--   -- comp_id' := λ C D F, by cases F; refl,
--   -- assoc' := by intros; refl
--   }


end TT

end category_theory