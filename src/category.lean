/-
The associated category of a type theory

Author: Billy Price
-/
import category_theory.category
import definitions
import wellformedness
import entails



namespace TT

open entails


/-! ### tset -/

  /- Closed terms of type 𝒫 A.
    An α : tset A is basically a set of A's, i.e. "term-set"
  -/
  def tset (A: type) : Type := {α : term // closed (𝒫 A) α}

  -- constructor
  def tset.mk (A : type) (α : term) : closed (𝒫 A) α → tset A:= subtype.mk α

  -- coerce tsets to terms
  instance tset_has_coe (A : type) : has_coe (tset A) term := coe_subtype

  @[WF_rules]
  def WF.tset {A} {Γ} (α : tset A) : WF Γ (𝒫 A) α
    := WF.closed_add_context α.property

  -- The empty set of any type
  def empty_tset (A : type) : tset A := tset.mk A ⟦ A | ⊥ ⟧ (by WF_prover)

  -- The universal set of any type
  def univ_tset (A : type) : tset A := tset.mk A ⟦ A | ⊤ ⟧ (by WF_prover)

  def elem_tset {A} (a α) : term := a ∈[A] α
  infix ` ∈ ` := elem_tset

  def tset_eq {A} (α₁ α₂ : tset A) : term := term_eq 𝒫 A α₁ α₂
  infix ` ≃ ` := tset_eq

  def tset_subset {A} (α₁ α₂ : tset A) : term := term_subset A α₁ α₂
  infix ` ⊆ ` := tset_subset


  def elem_of_elem_subset {Γ A H} {wfH : WF Γ Ω H} (a) {wfa : WF Γ A a} (α₁ α₂ : term) : entails Γ ⊤ (α₁ ⊆[A] α₂) → entails Γ H (a ∈[A] α₁) → entails Γ H (a ∈[A] α₂) :=
  begin
    intro hsub,
    apply entails.to_meta_imp,
    apply add_hyp, assumption,
    convert sub A  _ (all_elim hsub), simp, simp, assumption,
  end

  def lift_subset {Γ A B H} (α₁ α₂ : tset A) : entails Γ H (α₁ ⊆[A] α₂) → entails (B::Γ) (^H) (^α₁ ⊆[A] ^α₂) :=
  begin
    intro hsub,
    apply
  end

  def tset_prod {A B} (α : tset A) (β : tset B) : tset (A 𝕏 B)
    := tset.mk (A 𝕏 B) (term_prod A B α β) (by repeat {constructor}; apply_rules WF_rules)
  infix ` 𝕏 ` := tset_prod

  @[simp]
  def elem_tset_prod {Γ} {H} {A B} {wfH : WF (A 𝕏 B :: Γ) Ω H} {α : tset A} {β : tset B} :
  entails ((A 𝕏 B) :: Γ) H ((term.var 0) ∈[A 𝕏 B] ^(α 𝕏 β)) ↔ entails ((A 𝕏 B) :: Γ) H (∃[A,B] $ (↑1 ∈[A] ^^^α) ⋀ (↑0 ∈[B] ^^^β) ⋀ (↑2 ≃[A 𝕏 B] ⟪↑1,↑0⟫)) :=
  begin
    rw entails.to_meta_iff, simp,
    convert add_hyp (by assumption) (all_elim $ comp _),
    repeat {constructor}; repeat {apply WF.lift_once};
    apply_rules WF_rules
  end

  def elem_left_tset_of_elem_prod {Γ} {H} {A B} {α : tset A} {β : tset B} (a b : term) : entails Γ H (⟪a,b⟫ ∈[A 𝕏 B] α 𝕏 β) → entails Γ H (a ∈[A] α) :=
    sorry

  def elem_right_tset_of_elem_prod {Γ} {H} {A B} {α : tset A} {β : tset B} (a b : term) : entails Γ H (⟪a,b⟫ ∈[A 𝕏 B] α 𝕏 β) → entails Γ H (b ∈[B] β) :=
    sorry


/-! ### graph -/
section
  
  variables {A B : type}

  /- F is a tset representing the graph of a function from α to β -/
  def is_graph (α : tset A) (β : tset B) (F : tset (A 𝕏 B)) : Prop :=
    (⊨ F ⊆ α 𝕏 β)
      ∧
    (⊨ ∀' A ((↑0 ∈[A] α) ⟹ (∃!' B $ ⟪↑1,↑0⟫ ∈[A 𝕏 B] F))) -- F is functional

  /- The Type of graphs -/
  def graph (α : tset A) (β : tset B) : Type
    := {F : tset (A 𝕏 B) // is_graph α β F}

  -- graphs are tsets (which are terms)
  instance graph_has_coe {α : tset A} {β : tset B}
    : has_coe (graph α β) (tset (A 𝕏 B)) := coe_subtype

  def graph_eq {α : tset A} {β : tset B} (F₁ F₂ : graph α β) : term
    := @tset_eq (A 𝕏 B) F₁ F₂
  infix ` ≃ ` := graph_eq

  def graph_subset {α : tset A} {β : tset B} (F₁ F₂ : graph α β) : term
    := @tset_eq (A 𝕏 B) F₁ F₂
  infix ` ⊆ ` := graph_subset

  -- constructor
  def graph.mk {α : tset A} {β : tset B} (F : tset (A 𝕏 B))
    : is_graph α β F → graph α β := subtype.mk F

  @[WF_rules]
  def WF.graph {A B Γ} {α : tset A} {β : tset B} {F : graph α β}
    : WF Γ (𝒫 (A 𝕏 B)) F := WF.closed_add_context F.val.property

  @[WF_rules]
  def WF.elem_graph {A B Γ} {α : tset A} {β : tset B} {ab : term} {F : graph α β}
    : WF Γ (A 𝕏 B) ab → WF Γ Ω (ab ∈[A 𝕏 B] F) := λ _, (by apply_rules WF_rules)
  
  -- retrieve proof of F ⊆ α × β
  def graph.is_subset {A B α β} (F :@graph A B α β)
    : ⊨ (↑F ⊆ (α 𝕏 β)) := (F.property).1
  
  -- retrieve proof of functionality "F : α → β"
  def graph.is_functional {A B α β} (F :@graph A B α β)
    : ⊨ (∀' A ((↑0 ∈ α) ⟹ (∃!' B $ ⟪↑1,↑0⟫ ∈ F))) := (F.property).2

  lemma elem_prod_of_elem_graph {H} {A B Γ} {α : tset A} {β : tset B} {ab : term} {F : graph α β}
    : entails Γ H (ab ∈[A 𝕏 B] F) → entails Γ H (ab ∈[A 𝕏 B] α 𝕏 β) :=
  begin
    intro ent_subset,
    sorry
  end


  -- -- the identity graph
  -- def diagonal {A} (α : tset A) : graph α α :=
  --   ( graph.mk 
  --     ( tset.mk (A 𝕏 A) ⟦ A 𝕏 A | ∃' A (↑1 ≃[A 𝕏 A] ⟪↑0,↑0⟫) ⟧
  --       (by apply_rules [WF_rules, WF.closed_add_context];refl)
  --     )
  --   ) (sorry)
    -- (by { 
    --   split,
    --     { apply all_intro,
    --       simp,
    --       rw imp_iff_ent,
    --       -- apply cut (∃' A (↑1 ≃[A 𝕏 A] ⟪↑0,↑0⟫)⁅↑0⁆),
    --       -- rw ←elem_iff_spec,
    --       -- apply axm,
    --       -- any_goals {WF_prover;refl},
    --       -- simp,
    --       -- apply ex_intro,
    --       sorry },
        
    --   } )

end

/-! ### composition -/

section
  open term



  open term

  variables {A B C D : type}
  variable {α : tset A}
  variable {β : tset B}
  variable {η : tset C}
  variable {δ : tset D}

  /- The underlying term of the composition of two graphs -/
  def composition_term (F : graph α β) (G : graph β η) : term :=
    ⟦ A 𝕏 C | -- all d : A × C such that
              ∃[A,C] -- ∃ a c,
              ( (↑2 ≃[A 𝕏 C] ⟪↑1,↑0⟫) -- d = ⟨a,c⟩
                ⋀
                (∃' B ((⟪↑2,↑0⟫ ∈[A 𝕏 B] ^^^^F) ⋀ (⟪↑0, ↑1⟫ ∈[B 𝕏 C] ^^^^G))) ) ⟧ -- ∃ b, ⟨a,b⟩ ∈ F ∧ ⟨b,c⟩ ∈ G

  
  /- The composition construction is a well-formed term -/
  @[WF_rules]
  def WF.composition (F : graph α β) (G : graph β η) : closed (𝒫 (A 𝕏 C)) (composition_term F G) :=
    by apply_rules WF_rules; refl
    
  /- The graph which is the composition of two graphs 
  Note we define F ∘ G as what would usually be G ∘ F (this is just the Lean convention) -/
  def composition (F : graph α β) (G : graph β η) : graph α η :=
    (graph.mk (tset.mk (A 𝕏 C) (composition_term F G) (WF.composition F G)))
    (begin
      split,
      apply all_intro,
      simp,
      rw imp_iff_ent,
      rw elem_tset_prod,
      convert (hyp_of_iff _ _ (all_elim (comp _))).2 _, apply_rules WF_rules; refl,
      simp [-lift_add],
      apply ex_ent_ex_of_var,
      apply ex_ent_ex_of_var,
      apply and_intro,
        { apply and_hyp_right, WF_prover; refl,
          apply ex_intro,
          apply and_hyp_left, WF_prover; refl,
          apply cut (⟪↑2,↑0⟫ ∈ ^^^^(α 𝕏 β)),
          apply elem_of_elem_subset _ (^^^^↑↑F),
          apply all_intro,
          rw lift_top,
          rw imp_iff_ent,
          -- WF_prover; refl,
          -- constructor,
          -- constructor, refl,
          -- constructor, refl,
          -- simp,
          -- apply elem_prod_of_elem_graph, 
          },






    
    end)

  /- (F ∘ G) ∘ H ≃ F ∘ (G ∘ H) -/
  def associativity (F : graph α β) (G : graph β η) (H : graph η δ) :
      ⊨ (composition (composition F G) H ≃[𝒫 (A 𝕏 D)] composition F (composition G H)) 
    := sorry

  /- F ∘ Δ_β ≃ F -/
  def comp_id (F : graph α β) : ⊨ composition F (diagonal β) ≃ F
    := sorry

  /- Δ_α ∘ F ≃ F -/
  def id_comp (F : graph α β) : ⊨ composition (diagonal α) F ≃ F
    := sorry

end


end TT

namespace category_theory

/- The category of tsets
  Objects : Dependent pairs ⟨A,α⟩ : (Σ A : TT.type, TT.tset A)
            with (A : TT.type) and (α : TT.tset A)
  Morphisms : Graphs between tsets (with id_graph as identity)
 -/
instance TT.category : small_category (Σ A : TT.type, TT.tset A) :=
{ hom := λ X Y, TT.graph X.2 Y.2,
  id := λ X, TT.diagonal X.2,
  comp := λ _ _ _ F G, TT.composition F G,
  id_comp' := sorry,
  comp_id' := sorry,
  assoc' := sorry
  }

end category_theory