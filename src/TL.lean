import data.finset
namespace TT

inductive type : Type
| One | Omega | Prod (A B : type)| Pow (A : type)

notation `Ω` := type.Omega
notation `𝟙` := type.One
infix `××` :100 := type.Prod
prefix 𝒫 :101 := type.Pow

inductive term : type → Type
| var  : ℕ → Π A : type, term A
| star : term 𝟙
| top  : term Ω
| bot  : term Ω
| prod : Π {A B : type}, term A → term B → term (A ×× B)
| elem : Π {A : type}, term A → term (𝒫 A) → term Ω
| comp : Π A : type, term Ω → term (𝒫 A)
| and  : term Ω → term Ω → term Ω
| or   : term Ω → term Ω → term Ω
| imp  : term Ω → term Ω → term Ω
| all  : Π A : type, term Ω → term Ω
| ex   : Π A : type, term Ω → term Ω

export term

infix `∶` :max :=  var -- input \:

notation `⁎` := star    -- input \asterisk
notation `⊤` := top     --       \top
notation `⊥` := bot     -- input \bot
infixr ` ⟹ `:60 := imp -- input \==>
infixr ` ∧' ` :70 := and -- input \wedge'
infixr ` ∨' ` :59 := or  -- input \vee'

def not (p : term Ω) := p ⟹ ⊥
prefix `∼`:max := not -- input \~, the ASCII character ~ has too low precedence

def biimp (p q: term Ω) := and (p ⟹ q) (q ⟹ p)
infix ` ⇔ `:60 := biimp -- input \<=>

notation `<` a `,` b `>` := prod a b

notation a ∈ α := elem a α
notation a ∉ α := ∼ (elem a α)
notation `[` A | φ `]` := comp A φ

notation `∀'` := all 
notation `∃'` := ex 

def eq {A : type} (a : term A) (a' : term A) : term Ω :=
  all (𝒫 A) (a ∈ (0∶(𝒫 A))) ⇔ (a' ∈ (0∶(𝒫 A)))
infix `≃` :50 := eq

def singleton {A : type} (a : term A) : term (𝒫 A) := comp A $ a ≃ 0∶A
notation `[` a `]` := singleton a

def ex_unique (A : type) (φ : term Ω) : term Ω :=
  ∃' A $ [A | φ] ≃ [3∶A]
notation `∃!'` := ex_unique

#check ex_unique 𝟙 ⊤

def subseteq {A : type} (α : term 𝒫 A) (β : term 𝒫 A) : term Ω :=
  ∀' A $ (0∶A ∈ α) ⟹ (0∶A ∈ β)
infix ⊆ := subseteq

def lift (d : ℕ) : ℕ → Π {A : type}, term A → term A
| k _ (var n A)  := var (if k ≤ n then (n+d) else n) A
| k _ (comp A φ) := comp A (lift (k+1) φ)
| k _ (∀' A φ)   := ∀' A (lift (k+1) φ)
| k _ (∃' A φ)   := ∃' A (lift (k+1) φ)
-- pass through the rest unchanged
| k _ ⁎          := ⁎
| k _ top        := top
| k _ bot        := bot
| k _ (prod a b) := prod (lift k a) (lift k b)
| k _ (a ∈ α)    := (lift k a) ∈ (lift k α)
| k _ (p ∧' q)   := (lift k p) ∧' (lift k q)
| k _ (p ∨' q)   := (lift k p) ∨' (lift k q)
| k _ (p ⟹ q)  := (lift k p) ⟹ (lift k q)

-- Substitution is hard - how to resolve when A should be S?
-- problem arises because `term` allows ∀' A (var 0 B), which is not well-formed

-- def subst {A S: type} (s : term S) : ℕ → term A → term A
-- | k (var n _) := if n=k then s else (var n _)


def FV : Π {A : type}, term A → finset ℕ
| _ (var n A)  := {n}
| _ ⁎          := ∅
| _ top        := ∅
| _ bot        := ∅
| _ (prod a b) := FV a ∪ FV b
| _ (a ∈ α)    := FV a ∪ FV α
| _ (comp A φ) := ((FV φ).erase 0).image nat.pred
| _ (p ∧' q)   := FV p ∪ FV q
| _ (p ∨' q)   := FV p ∪ FV q
| _ (p ⟹ q)  := FV p ∪ FV q
| _ (∀' A φ)   := ((FV φ).erase 0).image nat.pred
| _ (∃' A φ)   := ((FV φ).erase 0).image nat.pred

inductive entX : finset ℕ → term Ω → term Ω → Type
| axm                {Γ p} : entX Γ p p
| vac                {Γ p} : entX Γ p ⊤
| abs                {Γ p} : entX Γ ⊥ p
| cut            {Γ p q r} : entX Γ p q → entX Γ q r → entX Γ p r
| and_intro      {Γ p q r} : entX Γ r p → entX Γ r q → entX Γ r (p ∧' q) 
| and_elim_left  {Γ p q r} : entX Γ r (p ∧' q) → entX Γ r p 
| and_elim_right {Γ p q r} : entX Γ r (p ∧' q) → entX Γ r q
| or_intro       {Γ p q r} : entX Γ p r → entX Γ q r → entX Γ (p ∨' q) r
| or_elim_left   {Γ p q r} : entX Γ (p ∨' q) r → entX Γ p r
| or_elim_right  {Γ p q r} : entX Γ (p ∨' q) r → entX Γ q r
| imp_to_and     {Γ p q r} : entX Γ p (q ⟹ r) → entX Γ (p ∧' q) r
| and_to_imp     {Γ p q r} : entX Γ (p ∧' q) r → entX Γ p (q ⟹ r)
| con_intro {Γ p q} (n : ℕ)
  : entX (Γ ∪ {n}) p q
| ext {A : type}
  : entX ∅ ⊤ $
    ∀' (𝒫 A) $ ∀' (𝒫 A) $ ∀' A 
      ((0∶A ∈ 2∶(𝒫 A)) ⇔ (0∶A ∈ 1∶(𝒫 A)))
      ⟹ 
      (1∶(𝒫 A) ≃ 0∶(𝒫 A))
| ext_Ω  
  : entX ∅ ⊤ $ ∀' Ω $ ∀' Ω $ ((0∶Ω ⇔ 1∶Ω) ⟹ (0∶Ω ≃ 1∶Ω))
| star_unique : entX ∅ ⊤ $ ∀' 𝟙 (0∶𝟙 ≃ ⁎)
| product_exists_rep {A B : type}
  : entX ∅ ⊤ $ ∀' (A ×× B) $ ∃' A $ ∃' B $ (2∶(A ×× B)) ≃ (prod (1∶A) (0∶B))
| product_distinct_rep {A B : type}
  : entX ∅ ⊤ $ ∀' A $ ∀' A $ ∀' B $ ∀' B $
    ((prod (3∶A) (1∶B)) ≃ (prod (2∶A) (0∶B)))
    ⟹
    ((3∶A ≃ 2∶A) ∧' (1∶B ≃ 0∶B))

def ent := entX ∅
def proofX (X: finset ℕ) := entX X ⊤
def proof := proofX ∅

end TT