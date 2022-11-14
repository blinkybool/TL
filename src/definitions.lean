/-
Definitions of a type theory

Author: Billy Price
-/
import data.finset
import tactic.induction
import tactic.tidy
import tactic.linarith
namespace TT

inductive type : Type
| Unit | Omega | Prod (A B : type) | Pow (A : type)

notation `Ω` := type.Omega
notation `𝟙` := type.Unit
infix `𝕏`:max := type.Prod
notation `𝒫`A :max := type.Pow A

inductive term : Type
| star : term
| top  : term
| bot  : term
| and  : term → term → term
| or   : term → term → term
| imp  : term → term → term
| elem : type → term → term → term
| pair : term → term → term
| var  : ℕ → term
| comp : type → term → term
| all  : type → term → term
| ex   : type → term → term

open term

-- * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * 
-- Notation and derived operators 
-- * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * 

instance nat_coe_var : has_coe ℕ term := ⟨term.var⟩

@[simp] lemma var_simp {n : ℕ} : ↑n = (term.var n) := rfl

notation `⁎` := term.star    -- input \asterisk
notation `⊤` := term.top     --       \top
notation `⊥` := term.bot     -- input \bot
infixr ` ⟹ `:60 := term.imp -- input \==>
infixr ` ⋀ ` :70 := term.and -- input \And or \bigwedge
infixr ` ⋁ ` :59 := term.or  -- input \Or or \bigvee

def not (p : term) := p ⟹ ⊥
instance term_has_neg : has_neg term := ⟨not⟩

def iff (p q: term) := (p ⟹ q) ⋀ (q ⟹ p)
infix ` ⇔ `:60 := iff -- input \<=>

notation a ` ∈[` A `] ` α := term.elem A a α
notation `⟦ ` A ` | ` φ ` ⟧` := term.comp A φ

notation `⟪` a `,` b `⟫` := term.pair a b 

notation `∀'` := term.all
notation `∃'` := term.ex

notation `∀[` Q:(foldr `,` (A q, λ p : term, ∀' A (q p)) id) `]` := Q
notation `∃[` Q:(foldr `,` (A q, λ p : term, ∃' A (q p)) id) `]` := Q

@[simp]
def lift (d : ℕ) : ℕ → term → term
| k ⁎          := ⁎
| k ⊤          := ⊤
| k ⊥          := ⊥
| k (p ⋀ q)    := (lift k p) ⋀ (lift k q)
| k (p ⋁ q)    := (lift k p) ⋁ (lift k q)
| k (p ⟹ q)   := (lift k p) ⟹ (lift k q)
| k (a ∈[A] α)    := (lift k a) ∈[A] (lift k α)
| k ⟪a,b⟫      := ⟪lift k a, lift k b⟫
| k (var m)    := if m≥k then var (m+d) else var m
| k ⟦A | φ⟧  :=   ⟦A | lift (k+1) φ⟧
| k (∀' A φ)   := ∀' A $ lift (k+1) φ
| k (∃' A φ)   := ∃' A $ lift (k+1) φ

@[reducible]
def lift_unit := lift 1 0
prefix `^`:max := lift_unit

section substitution
  variables {x p q a α b φ : term}
  variable {A : type}

  @[simp] lemma lift_star : ^⁎ = ⁎ := rfl
  @[simp] lemma lift_top : ^⊤ = ⊤ := rfl
  @[simp] lemma lift_bot : ^⊥ = ⊥ := rfl
  @[simp] lemma lift_and : ^(p ⋀ q) = ^p ⋀ ^q := rfl
  @[simp] lemma lift_or : ^(p ⋁ q) = ^p ⋁ ^q := rfl
  @[simp] lemma lift_imp : ^(p ⟹ q) = ^p ⟹ ^q := rfl
  @[simp] lemma lift_elem : ^(a ∈[A] α) = (^a ∈[A] ^α) := rfl
  @[simp] lemma lift_pair : ^(⟪a,b⟫) = ⟪^a,^b⟫ := rfl
  @[simp] lemma lift_var {n : ℕ} : ^(term.var n) = term.var (n+1) := rfl
  
  @[simp] lemma lift_zero {k : ℕ} {a : term} : lift 0 k a = a :=
  by induction a generalizing k; simp *

  @[simp] lemma lift_add {k a} {d t} : lift t k (lift d k a) = lift (d+t) k a :=
  begin
    induction' a; simp *,
    by_cases (k ≤ n),
      { rw [if_pos, if_pos],
        simp,
        rw [if_pos, add_assoc],
        iterate 3 {linarith} },
      { rw [if_neg, if_neg], simp, rw [if_neg], tidy}
  end

  @[simp]
  def subst : ℕ → term → term → term
  | n x ⁎          := ⁎
  | n x ⊤          := ⊤
  | n x ⊥          := ⊥
  | n x (p ⋀ q)    := (subst n x p) ⋀ (subst n x q)
  | n x (p ⋁ q)    := (subst n x p) ⋁ (subst n x q)
  | n x (p ⟹ q)  := (subst n x p) ⟹ (subst n x q)
  | n x (a ∈[A] α)    := (subst n x a) ∈[A] (subst n x α)
  | n x ⟪a,b⟫      := ⟪subst n x a, subst n x b⟫
  | n x (var m)    := if n=m then x else if m > n then var (m-1) else var m
  | n x ⟦ A | φ ⟧   := ⟦A | subst (n+1) (^ x) φ⟧
  | n x (∀' A φ)   := ∀' A (subst (n+1) (^ x) φ)
  | n x (∃' A φ)   := ∃' A (subst (n+1) (^ x) φ)

  notation  φ`⁅`:max b // n`⁆` := subst n b φ
  notation  φ`⁅`:max b `⁆` := φ⁅ b // 0⁆

  @[simp] lemma subst_var_eq {n : ℕ} {x : term} : (term.var n)⁅x // n⁆ = x := by simp

  @[simp] lemma subst_var {n} {m : ℕ} {x} : ↑m⁅x // n⁆ = (var m)⁅x // n⁆ := rfl

  lemma subst_var_less {n m} {x} : m < n → m⁅x // n⁆ = m :=
  begin
    intro hm,
    simp,
    rw [if_neg, if_neg],
    all_goals {linarith}
  end

  lemma subst_var_more {n m} {x} : m > n → m⁅x // n⁆ = var (m-1) :=
  begin
    intro hm,
    simp,
    rw if_neg, rw if_pos,
    all_goals {linarith}
  end

  @[simp] lemma subst_iff {n x p q} : subst n x (p ⇔ q) = subst n x p ⇔ subst n x q := rfl

  @[simp]
  lemma sub_lift {d n k} {a b : term} {hn : n < d} : (lift d k a)⁅b // n+k⁆ = lift (d-1) k a :=
  begin
    induction' a; simp,
    any_goals {tidy},
    case var :
      { split_ifs,
          { simp, rw if_neg, rw if_pos, cases hn; refl, all_goals { linarith }},
          { simp, rw if_neg, rw if_neg, all_goals { linarith }}
        },
    all_goals { rw add_assoc n k 1, apply ih, tidy},
  end

  @[simp] lemma sub_k_lift_k {d k} {a b : term} {hd : d ≥ 1} : (lift d k a)⁅b // k⁆ = lift (d-1) k a :=
  begin
    have : (lift d k a)⁅b//k⁆ = (lift d k a)⁅b//0+k⁆, simp, rw this, apply sub_lift, tidy,
  end 

  @[simp]
  lemma sub_lift_zero {d n} {a b : term} {hd : d ≥ 1} {hn : n < d} : (lift d 0 a)⁅b // n⁆ = lift (d-1) 0 a :=
  by rw ←add_zero n; refine sub_lift; tidy
  
  @[simp]
  lemma sub_lift_id {k} {a b : term} : (lift 1 k a)⁅b // k⁆ = a := by simp

end substitution

def term_eq (A:type) (a₁ a₂ : term) : term := ∀' (𝒫 A) $ ((^ a₁) ∈[A] ↑0) ⇔ ((^ a₂) ∈[A] ↑0)
notation a ` ≃[`:max A `] `:0 b := term_eq A a b

@[simp] lemma subst_eq {A} {n x a₁ a₂} : subst n x (a₁ ≃[A] a₂) = a₁⁅x // n⁆ ≃[A] a₂⁅x // n⁆ := sorry
-- begin
--   unfold term_eq, simp,
--   suffices : ∀ {a x n} (d), (lift 1 d a)⁅lift (d+1) 0 x // n+1+d⁆ = lift 1 d (lift d 0 a⁅lift d 0 x//n+d⁆),
--     { simp [this 0], refl },
--   intro a,
--   induction' a; simp * at *,
--   case term.var : {
--     intros x n,
--     split_ifs with h₁ h₂,
--       { intro, rw h₁, split_ifs,
--         { cases h, simp, split_ifs, induction' x; simp * at *, repeat {sorry}},
--         { sorry} },
--       { simp, cases h₂;sorry},
--       sorry,
--   },
--   repeat {sorry}
-- end

def term_singleton (A : type) (a : term) := ⟦A | (^ a) ≃[A] ↑0⟧
 
def ex_unique (A : type) (φ : term) : term :=
  ∃' A (⟦ A | φ ⟧ ≃[𝒫 A] (term_singleton A ↑0))
prefix `∃!'`:2 := ex_unique

def term_subset (A : type) (α : term) (β : term) : term :=
  ∀' A $ (↑0 ∈[A] (^ α)) ⟹ (↑0 ∈[A] (^ β))
notation a ` ⊆[`:max A `] `:0 b := term_subset A a b

def term_prod (A B : type) (α β : term) : term :=
  ⟦ A 𝕏 B | ∃[A,B] ((↑1 ∈[A] ^^^α) ⋀ (↑0 ∈[B] ^^^β) ⋀ (↑2 ≃[A 𝕏 B] ⟪↑1,↑0⟫))⟧

-- * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
open list

def context := list type

instance context_has_append : has_append context := ⟨list.append⟩

inductive WF : context → type → term → Prop
| star {Γ}         : WF Γ 𝟙 ⁎
| top  {Γ}         : WF Γ Ω ⊤
| bot  {Γ}         : WF Γ Ω ⊥
| and  {Γ p q}     : WF Γ Ω p → WF Γ Ω q → WF Γ Ω (p ⋀ q)
| or   {Γ p q}     : WF Γ Ω p → WF Γ Ω q → WF Γ Ω (p ⋁ q)
| imp  {Γ p q}     : WF Γ Ω p → WF Γ Ω q → WF Γ Ω (p ⟹ q)
| elem {Γ A a α}   : WF Γ A a → WF Γ (𝒫 A) α → WF Γ Ω (a ∈[A] α)
| pair {Γ A B a b} : WF Γ A a → WF Γ B b → WF Γ (A 𝕏 B) ⟪a,b⟫
| var  {Γ A n}     : list.nth Γ n = some A → WF Γ A (var n)
| comp {Γ A φ}     : WF (A::Γ) Ω φ → WF Γ (𝒫 A) ⟦A | φ⟧
| all  {Γ A φ}     : WF (A::Γ) Ω φ → WF Γ Ω (∀' A φ)
| ex   {Γ A φ}     : WF (A::Γ) Ω φ → WF Γ Ω (∃' A φ)

def closed : type → term → Prop := WF list.nil

/-! ### entails -/

inductive entails : context → term → term → Prop
| axm          {Γ} {p}     : WF Γ Ω p → entails Γ p p
| vac          {Γ} {p}     : WF Γ Ω p → entails Γ p ⊤
| abs          {Γ} {p}     : WF Γ Ω p → entails Γ ⊥ p
| and_intro    {Γ} {p q r} : entails Γ p q → entails Γ p r → entails Γ p (q ⋀ r)
| and_left     {Γ} {p q r} : entails Γ p (q ⋀ r) → entails Γ p q
| and_right    {Γ} {p q r} : entails Γ p (q ⋀ r) → entails Γ p r
| hyp_or       {Γ} {p q r} : entails Γ p r → entails Γ q r → entails Γ (p ⋁ q) r
| hyp_or_left  {Γ} {p q r} : entails Γ (p ⋁ q) r → entails Γ p r
| hyp_or_right {Γ} {p q r} : entails Γ (p ⋁ q) r → entails Γ q r
| imp_to_and {Γ} {p q r}   : entails Γ p (q ⟹ r) → entails Γ (p ⋀ q) r
| and_to_imp {Γ} {p q r}   : entails Γ (p ⋀ q) r → entails Γ p (q ⟹ r)
| weakening  {p q} (K Δ Γ) : entails (K ++ Γ) p q → entails (K ++ Δ ++ Γ) (lift Δ.length K.length p) (lift Δ.length K.length q)
| cut        {Γ} {p q} (c) : entails Γ p c → entails Γ c q → entails Γ p q
| all_elim   {Γ} {p φ A}   : entails Γ p (∀' A φ) → entails (A::Γ) (^ p) φ
| all_intro  {Γ} {p φ A}   : entails (A::Γ) (^ p) φ → entails Γ p (∀' A φ)
| ex_elim    {Γ} {p φ A}   : entails Γ (∃' A φ) p → entails (A::Γ) φ (^ p)
| ex_intro   {Γ} {p φ A}   : entails (A::Γ) φ (^ p) → entails Γ (∃' A φ) p
| extensionality {A}       : entails [] ⊤ $ ∀[𝒫 A, 𝒫 A] $ (∀' A $ (↑0 ∈[A] ↑2) ⇔ (↑0 ∈[A] ↑1)) ⟹ (↑1 ≃[𝒫 A] ↑0)
| prop_ext                 : entails [] ⊤ $ ∀[Ω,Ω] $ (↑1 ⇔ ↑0) ⟹ (↑1 ≃[Ω] ↑0)
| star_unique              : entails [] ⊤ $ ∀[𝟙] (↑0 ≃[𝟙] ⁎)
| pair_rep      {A B}      : entails [] ⊤ $ ∀[A 𝕏 B] $ ∃[A,B] $ ↑2 ≃[A 𝕏 B] ⟪↑1,↑0⟫
| pair_distinct {A B}      : entails [] ⊤ $ ∀[A,B,A,B] $ (⟪↑3,↑2⟫ ≃[A 𝕏 B] ⟪↑1,↑0⟫) ⟹ ((↑3 ≃[A] ↑1) ⋀ (↑2 ≃[B] ↑0))
| sub      {Γ} {p q b} (B) : WF Γ B b → entails (B::Γ) p q → entails Γ (p⁅b⁆) (q⁅b⁆)
| comp     {Γ} {A φ}       : WF (A::Γ) Ω φ → entails Γ ⊤ (∀' A $ (↑0 ∈[A] (^ ⟦A | φ⟧)) ⇔ φ)

prefix `⊨`:1 := entails [] ⊤
infix ` ⊨ `:50 := entails []
notation φ ` ⊨[` Γ:(foldr `,` (h t, list.cons h t) list.nil) `] ` ψ := entails Γ φ ψ
notation `⊨[` Γ:(foldr `,` (h t, list.cons h t) list.nil) `] ` ψ := entails Γ ⊤ ψ

end TT