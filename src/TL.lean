namespace TT

inductive type : Type
| One | Omega | Prod (A B : type)| Pow (A : type)

notation `Ω` := type.Omega
notation `𝟙` := type.One
infix `××`:max := type.Prod
prefix 𝒫 :max := type.Pow

def context := list type

inductive term : Type
| star : term
| top  : term
| bot  : term
| and  : term → term → term
| or   : term → term → term
| imp  : term → term → term
| var  : ℕ → term
| comp : term → term
| all  : term → term
| ex   : term → term
| elem : term → term → term
| prod : term → term → term

open term

-- * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * 
-- Notation and derived operators 
-- * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * 

notation `<0>` := var 0
notation `<1>` := var 1
notation `<2>` := var 2
notation `<3>` := var 3
notation `<4>` := var 4
notation `<5>` := var 5
notation `<6>` := var 6
notation `<7>` := var 7
notation `<8>` := var 8
notation `<9>` := var 9

notation `⁎` := star    -- input \asterisk
notation `⊤` := top     --       \top
notation `⊥` := bot     -- input \bot
infixr ` ⟹ `:60 := imp -- input \==>
infixr ` ⊓ ` :70 := and -- input \glb or \sqcap
infixr ` ⊔ ` :59 := or  -- input \lub or ⊔

def not (p : term) := p ⟹ ⊥
prefix `∼`:max := not -- input \~, the ASCII character ~ has too low precedence

def biimp (p q: term) := (p ⟹ q) ⊓ (q ⟹ p)
infix ` ⇔ `:60 := biimp -- input \<=>

infix ∈ := elem
infix ∉ := λ a, λ α, not (elem a α)
notation `⟦` φ `⟧` := comp φ

infix `××` :max := prod

prefix `∀'`:1 := all 
prefix `∃'`:2 := ex

def eq (a : term) (a' : term) : term := ∀' (a ∈ <0>) ⇔ (a' ∈ <0>)
infix `≃` :50 := eq

def singleton (a : term) := ⟦a ≃ (<0>)⟧

def ex_unique (φ : term) : term :=
  ∃' ⟦φ⟧ ≃ singleton (<3>)
prefix `∃!'`:2 := ex_unique

def subseteq (α : term) (β : term) : term :=
  ∀' (<0> ∈ α) ⟹ (<0> ∈ β)
infix ⊆ := subseteq

-- * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *

inductive WF : context → term → type → Prop
| star {Γ}           : WF Γ term.star 𝟙
| top  {Γ}           : WF Γ term.top Ω
| bot  {Γ}           : WF Γ term.bot Ω
| and  {Γ e₁ e₂}     : WF Γ e₁ Ω → WF Γ e₁ Ω → WF Γ (e₁ ⊓ e₂) Ω
| or   {Γ e₁ e₂}     : WF Γ e₁ Ω → WF Γ e₁ Ω → WF Γ (e₁ ⊔ e₂) Ω
| imp  {Γ e₁ e₂}     : WF Γ e₁ Ω → WF Γ e₁ Ω → WF Γ (e₁ ⟹ e₂) Ω
| var  {Γ n A}       : list.nth Γ n = some A → WF Γ (var n) A
| comp {Γ e A}       : WF (A::Γ) e Ω → WF Γ ⟦e⟧ (𝒫 A)
| all  {Γ e A}       : WF (A::Γ) e Ω → WF Γ (∀' e) Ω
| ex   {Γ e A}       : WF (A::Γ) e Ω → WF Γ (∃' e) Ω
| elem {Γ e₁ e₂ A}   : WF Γ e₁ A → WF Γ e₂ (𝒫 A) → WF Γ (e₁ ∈ e₂) Ω
| prod {Γ e₁ e₂ A B} : WF Γ e₁ A → WF Γ e₂ B → WF Γ (prod e₁ e₂) (A ×× B)

def subst_nth (b:term) : ℕ → term → term
| n star       := star
| n top        := top
| n bot        := bot
| n (p ⊓ q)    := (subst_nth n p) ⊓ (subst_nth n q)
| n (p ⊔ q)    := (subst_nth n p) ⊔ (subst_nth n q)
| n (p ⟹ q)  := (subst_nth n p) ⟹ (subst_nth n q)
| n (var m)    := if n=m then b else var m
| n ⟦φ⟧        := ⟦subst_nth (n+1) φ⟧
| n (∀' φ)     := ∀' (subst_nth (n+1) φ)
| n (∃' φ)     := ∃' (subst_nth (n+1) φ)
| n (a ∈ α)    := (subst_nth n a) ∈ (subst_nth n α)
| n (prod a b) := prod (subst_nth n a) (subst_nth n b)

def subst (b:term):= subst_nth b 0

def remap_vars : Π k : ℕ, (ℕ → ℕ) → term → term
| k σ top        := top
| k σ star       := star
| k σ bot        := bot
| k σ (p ⊓ q)   := (remap_vars k σ p) ⊓ (remap_vars k σ q)
| k σ (p ⊔ q)   := (remap_vars k σ p) ⊔ (remap_vars k σ q)
| k σ (p ⟹ q)  := (remap_vars k σ p) ⟹ (remap_vars k σ q)
| k σ (var m)    := var (σ (m+k))
| k σ ⟦φ⟧         := ⟦remap_vars (k+1) σ φ⟧
| k σ (∀' φ)     := ∀' remap_vars (k+1) σ φ
| k σ (∃' φ)     := ∃' remap_vars (k+1) σ φ
| k σ (a ∈ α)    := (remap_vars k σ a) ∈ (remap_vars k σ α)
| k σ (prod a b) := prod (remap_vars k σ a) (remap_vars k σ b)

inductive proof : context → term → term → Prop
-- c1-3 unecessary?? (because free variables must appear in context)
| axm        {Γ φ}     : WF Γ φ Ω → proof Γ φ φ
| vac        {Γ φ}     : WF Γ φ Ω → proof Γ φ term.top
| abs        {Γ φ}     : WF Γ φ Ω → proof Γ term.bot φ
| cut        {Γ φ ψ γ} : proof Γ φ ψ → proof Γ ψ γ → proof Γ φ γ
| and_intro  {Γ p q r} : proof Γ p q → proof Γ p r → proof Γ p (q ⊓ r)  
| and_left   {Γ p q r} : proof Γ p (q ⊓ r) → proof Γ p q
| and_right  {Γ p q r} : proof Γ p (q ⊓ r) → proof Γ p r
| or_intro   {Γ p q r} : proof Γ p r → proof Γ q r → proof Γ (p ⊔ q) r  
| or_left    {Γ p q r} : proof Γ (p ⊔ q) r → proof Γ p r
| or_right   {Γ p q r} : proof Γ (p ⊔ q) r → proof Γ q r
| imp_to_and {Γ p q r} : proof Γ p (q ⟹ r) → proof Γ (p ⊓ q) r
| and_to_imp {Γ p q r} : proof Γ (p ⊓ q) r → proof Γ p (q ⟹ r)

| apply    {Γ φ ψ b B} :
    WF Γ b B
    → proof (B::Γ) φ ψ
    → proof Γ (subst b φ) (subst b ψ) -- can free vars in b become bound?? (bad)

| all_elim   {Γ p φ B} : proof (B::Γ) p (all φ) → proof Γ p φ
| all_intro  {Γ p φ B} : proof Γ p φ → proof (B::Γ) p (∀' φ)
| ex_elim    {Γ p φ B} : proof (B::Γ) p (∃' φ) → proof Γ p φ
| ex_intro   {Γ p φ B} : proof Γ p φ → proof (B::Γ) p (∃' φ)

| comp       {Γ φ A}   :
    WF (A::A::Γ) φ Ω
    → proof Γ ⊤
      (∀' (<0> ∈ ⟦φ⟧) ⇔ (subst <0> φ))

| ext                  :
    proof [] ⊤ $ 
      ∀' ∀' (∀' (<0> ∈ <2>) ⇔ (<0> ∈ <1>)) ⟹ (<1> ≃ <0>)

| prop_ext             : proof [] ⊤ ∀' ∀' (<1> ⇔ <0>) ⟹ (<1> ≃ <0>)
| star_unique          : proof [] ⊤ ∀' (<0> ≃ ⁎)
| prod_exists_rep      : proof [] ⊤ ∀' ∃' ∃' (<2> ≃ (prod <1> <0>))

| prod_distinct_rep    :
    proof [] ⊤
      ∀' ∀' ∀' ∀' (prod <3> <1> ≃ prod <2> <0>) ⟹ (<3> ≃ <2> ⊓ <1> ≃ <0>)

example : proof [] ⊤ ⊤ := proof.axm WF.top

lemma proof_WF {Γ : context} {P Q: term} : WF Γ P Ω → proof Γ P Q → WF Γ Q Ω := sorry

variables p q r : term

example {Γ : context}  : proof Γ ⊤ (q ⟹ r) → proof Γ q r := sorry

def FV {Γ : context} {A : type} (a : term): WF Γ a A → context := λ _, Γ

end TT