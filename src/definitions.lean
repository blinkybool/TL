/-
Definitions of a type theory

Author: Billy Price
-/
import data.finset
import tactic
namespace TT

inductive type : Type
| Unit | Omega | Prod (A B : type)| Pow (A : type)

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
| elem : term → term → term
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

notation `⁎` := term.star    -- input \asterisk
notation `⊤` := term.top     --       \top
notation `⊥` := term.bot     -- input \bot
infixr ` ⟹ `:60 := term.imp -- input \==>
infixr ` ⋀ ` :70 := term.and -- input \And or \bigwedge
infixr ` ⋁ ` :59 := term.or  -- input \Or or \bigvee

def not (p : term) := p ⟹ ⊥
prefix `∼`:max := not -- input \~

def iff (p q: term) := (p ⟹ q) ⋀ (q ⟹ p)
infix ` ⇔ `:60 := iff -- input \<=>

infix ∈ := term.elem
infix ∉ := λ a α, not (term.elem a α)
notation `⟦ ` A ` | ` φ ` ⟧` := term.comp A φ

notation `⟪` a `,` b `⟫` := term.pair a b 

notation `∀'` := term.all
notation `∃'` := term.ex

notation `∀[` Q:(foldr `,` (A q, λ p : term, ∀' A (q p)) id) `]` := Q
notation `∃[` Q:(foldr `,` (A q, λ p : term, ∃' A (q p)) id) `]` := Q

section substitution

  @[simp]
  def lift (d : ℕ) : ℕ → term → term
  | k ⁎          := ⁎
  | k ⊤          := ⊤
  | k ⊥          := ⊥
  | k (p ⋀ q)    := (lift k p) ⋀ (lift k q)
  | k (p ⋁ q)    := (lift k p) ⋁ (lift k q)
  | k (p ⟹ q)   := (lift k p) ⟹ (lift k q)
  | k (a ∈ α)    := (lift k a) ∈ (lift k α)
  | k ⟪a,b⟫      := ⟪lift k a, lift k b⟫
  | k (var m)    := if m≥k then var (m+d) else var m
  | k ⟦A | φ⟧  :=   ⟦A | lift (k+1) φ⟧
  | k (∀' A φ)   := ∀' A $ lift (k+1) φ
  | k (∃' A φ)   := ∃' A $ lift (k+1) φ
  
  notation `^` := lift 1 0

  @[simp]
  def subst : ℕ → term → term → term
  | n x ⁎          := ⁎
  | n x ⊤          := ⊤
  | n x ⊥          := ⊥
  | n x (p ⋀ q)    := (subst n x p) ⋀ (subst n x q)
  | n x (p ⋁ q)    := (subst n x p) ⋁ (subst n x q)
  | n x (p ⟹ q)  := (subst n x p) ⟹ (subst n x q)
  | n x (a ∈ α)    := (subst n x a) ∈ (subst n x α)
  | n x ⟪a,b⟫      := ⟪subst n x a, subst n x b⟫
  | n x (var m)    := if n=m then x else var m
  | n x ⟦ A | φ ⟧   := ⟦A | subst (n+1) (^ x) φ⟧
  | n x (∀' A φ)   := ∀' A (subst (n+1) (^ x) φ)
  | n x (∃' A φ)   := ∃' A (subst (n+1) (^ x) φ)

  @[simp]
  lemma subst_id {a : term} {n : ℕ} : subst n (↑n) a = a :=
  begin
    induction a generalizing n;simp * at *,
    case term.var : m {split_ifs, rw h, refl, refl},
    all_goals {exact a_ih}
  end

  notation  `⁅` φ ` // `  b `⁆` := subst 0 b φ

  #reduce ⁅ ↑0 // ⊤ ⋀ ⊥⁆
  #reduce ⁅ ↑1 // ⊤ ⋀ ⊥⁆

  def FV : term → finset ℕ
  | ⁎          := ∅
  | ⊤          := ∅
  | ⊥          := ∅
  | (p ⋀ q)    := FV p ∪ FV q
  | (p ⋁ q)    := FV p ∪ FV q
  | (p ⟹ q)  := FV p ∪ FV q
  | (a ∈ α)    := FV a ∪ FV α
  | ⟪a,b⟫      := FV a ∪ FV b
  | (var n)    := {n}
  | ⟦ A | φ ⟧   := ((FV φ).erase 0).image nat.pred
  | (∀' A φ)   := ((FV φ).erase 0).image nat.pred
  | (∃' A φ)   := ((FV φ).erase 0).image nat.pred

end substitution

def term_eq (A:type) (a₁ a₂ : term) : term := ∀' (𝒫 A) $ ((^ a₁) ∈ ↑0) ⇔ ((^ a₂) ∈ ↑0)
notation a ` ≃[`:max A `] `:0 b := term_eq A a b

#reduce ↑0 ≃[𝟙] ↑2

def term_singleton (A : type) (a : term) := ⟦A | (^ a) ≃[A] ↑0⟧
 
def ex_unique (A : type) (φ : term) : term :=
  ∃' A (⟦ A | φ ⟧ ≃[𝒫 A] (term_singleton A ↑0))
prefix `∃!'`:2 := ex_unique

def term_subset (A : type) (α : term) (β : term) : term :=
  ∀' A $ (↑0 ∈ (^ α)) ⟹ (↑0 ∈ (^ β))
notation a ` ⊆[`:max A `] `:0 b := term_subset A a b

def term_prod (A B : type) (α β : term) : term :=
  ⟦ A 𝕏 B | ∃[A,B] ((↑1 ∈ α) ⋀ (↑0 ∈ β) ⋀ (↑2 ≃[A 𝕏 B] ⟪↑1,↑0⟫))⟧

-- * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
open list
local notation l₁ ++ l₂ := list.append l₁ l₂

def context := list type

inductive WF : context → type → term → Prop
| star {Γ}         : WF Γ 𝟙 ⁎
| top  {Γ}         : WF Γ Ω ⊤
| bot  {Γ}         : WF Γ Ω ⊥
| and  {Γ p q}     : WF Γ Ω p → WF Γ Ω q → WF Γ Ω (p ⋀ q)
| or   {Γ p q}     : WF Γ Ω p → WF Γ Ω q → WF Γ Ω (p ⋁ q)
| imp  {Γ p q}     : WF Γ Ω p → WF Γ Ω q → WF Γ Ω (p ⟹ q)
| elem {Γ A a α}   : WF Γ A a → WF Γ (𝒫 A) α → WF Γ Ω (a ∈ α)
| pair {Γ A B a b} : WF Γ A a → WF Γ B b → WF Γ (A 𝕏 B) ⟪a,b⟫
| var  {Γ A n}     : list.nth Γ n = some A → WF Γ A (var n)
| comp {Γ A φ}     : WF (A::Γ) Ω φ → WF Γ (𝒫 A) ⟦A | φ⟧
| all  {Γ A φ}     : WF (A::Γ) Ω φ → WF Γ Ω (∀' A φ)
| ex   {Γ A φ}     : WF (A::Γ) Ω φ → WF Γ Ω (∃' A φ)

def closed : type → term → Prop := WF list.nil

/-! ### entails -/

inductive entails : context → term → term → Prop
| axm        {Γ} {p}       : WF Γ Ω p → entails Γ p p
| vac        {Γ} {p}       : WF Γ Ω p → entails Γ p ⊤
| abs        {Γ} {p}       : WF Γ Ω p → entails Γ ⊥ p
| and_intro  {Γ} {p q r}   : entails Γ p q → entails Γ p r → entails Γ p (q ⋀ r)
| and_left   {Γ} (p q r)   : entails Γ p (q ⋀ r) → entails Γ p q
| and_right  {Γ} (p q r)   : entails Γ p (q ⋀ r) → entails Γ p r
| or_intro   {Γ} {p q r}   : entails Γ p r → entails Γ q r → entails Γ (p ⋁ q) r
| or_left    {Γ} (p q r)   : entails Γ (p ⋁ q) r → entails Γ p r
| or_right   {Γ} (p q r)   : entails Γ (p ⋁ q) r → entails Γ q r
| imp_to_and {Γ} {p q r}   : entails Γ p (q ⟹ r) → entails Γ (p ⋀ q) r
| and_to_imp {Γ} {p q r}   : entails Γ (p ⋀ q) r → entails Γ p (q ⟹ r)
| weakening  {Γ} {p q} (Δ) : entails Γ p q → entails (list.append Γ Δ) p q
| cut        {Γ} (p c q)   : entails Γ p c → entails Γ c q → entails Γ p q
| all_elim   {Γ} {p φ A}   : entails Γ p (∀' A φ) → entails (A::Γ) (^ p) φ
| all_intro  {Γ} {p φ} (A) : entails (A::Γ) (^ p) φ → entails Γ p (∀' A φ)
| ex_elim    {Γ} {p φ A}   : entails Γ p (∃' A φ) → entails (A::Γ) (^ p) φ
| ex_intro   {Γ} {p φ} (A) : entails (A::Γ) (^ p) φ → entails Γ p (∃' A φ)
| extensionality {A}       : entails [] ⊤ $ ∀[𝒫 A, 𝒫 A] $ (∀' A $ (↑0 ∈ ↑2) ⇔ (↑0 ∈ ↑1)) ⟹ (↑1 ≃[𝒫 A] ↑0)
| prop_ext                 : entails [] ⊤ $ ∀[Ω,Ω] $ (↑1 ⇔ ↑0) ⟹ (↑1 ≃[Ω] ↑0)
| star_unique              : entails [] ⊤ $ ∀[𝟙] (↑0 ≃[𝟙] ⁎)
| pair_rep      {A B}      : entails [] ⊤ $ ∀[A 𝕏 B] $ ∃[A,B] $ ↑2 ≃[A 𝕏 B] ⟪↑1,↑0⟫
| pair_distinct {A B}      : entails [] ⊤ $ ∀[A,B,A,B] $ (⟪↑3,↑2⟫ ≃[A 𝕏 B] ⟪↑1,↑0⟫) ⟹ ((↑3 ≃[A] ↑1) ⋀ (↑2 ≃[B] ↑0))
| sub      {Γ} (B) (b p q) : WF Γ B b → entails (B::Γ) p q → entails Γ (⁅p // b⁆) (⁅q // b⁆)
| comp     {Γ} (A) (φ)     : WF (A::Γ) Ω φ → entails Γ ⊤ (∀' A $ (↑0 ∈ (^ ⟦A | φ⟧)) ⇔ φ)

prefix `⊨`:1 := entails [] ⊤
infix ` ⊨ `:50 := entails []
notation φ ` ⊨[` Γ:(foldr `,` (h t, list.cons h t) list.nil) `] ` ψ := entails Γ φ ψ
notation `⊨[` Γ:(foldr `,` (h t, list.cons h t) list.nil) `] ` ψ := entails Γ ⊤ ψ

section
  variables p q φ ψ : term

  #reduce   ⊨ (p ⋁ ∼p)  -- entails [] ⊤ (or p (imp p ⊥))
  #reduce q ⊨ (p ⋁ ∼p)  -- entails [] q (or p (imp p ⊥))
  #reduce   ⊨[Ω,𝟙] p -- entails [Ω,⁎] ⊤ p
  #reduce q ⊨[Ω,𝟙] p -- entails [Ω,⁎] q p
end 


end TT