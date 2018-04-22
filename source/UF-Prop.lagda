\begin{code}

{-# OPTIONS --without-K --exact-split #-}

module UF-Prop where

open import UF-Base public
open import UF-Subsingletons public
open import UF-Equiv public
open import UF-FunExt public
open import UF-Embedding public
open import UF-Subsingletons-FunExt public

propExt : ∀ U → U ′ ̇ 
propExt U = {P Q : U ̇} → isProp P → isProp Q → (P → Q) → (Q → P) → P ≡ Q

Prop : ∀ {U} → U ′ ̇
Prop {U} = Σ \(P : U ̇) → isProp P 

⊥ ⊤ : Prop
⊥ = 𝟘 , 𝟘-isProp   -- false
⊤ = 𝟙 , 𝟙-isProp   -- true

_holds : ∀ {U} → Prop → U ̇
_holds = pr₁

holdsIsProp : ∀ {U} → (p : Prop {U}) → isProp (p holds)
holdsIsProp = pr₂

PropExt : ∀ {U} → FunExt U U → propExt U → {p q : Prop {U}}
        → (p holds → q holds) → (q holds → p holds) → p ≡ q
PropExt {U} fe pe {p} {q} f g =
        to-Σ-≡'' ((pe (holdsIsProp p) (holdsIsProp q) f g) , isProp-isProp fe _ _)
Prop-isSet : ∀ {U} → FunExt U U → propExt U → isSet (Prop {U})
Prop-isSet {U} fe pe = path-collapsible-isSet pc
 where
  A : (p q : Prop) → U ̇
  A p q = (p holds → q holds) × (q holds → p holds) 
  A-isProp : (p q : Prop) → isProp(A p q)
  A-isProp p q = isProp-closed-under-Σ (isProp-exponential-ideal fe (λ _ → holdsIsProp q)) 
                                       (λ _ → isProp-exponential-ideal fe (λ _ → holdsIsProp p)) 
  g : (p q : Prop) → p ≡ q → A p q
  g p q e = (b , c)
   where
    a : p holds ≡ q holds
    a = ap _holds e
    b : p holds → q holds
    b = transport (λ X → X) a
    c : q holds → p holds
    c = transport (λ X → X) (a ⁻¹)
  h  : (p q : Prop) → A p q → p ≡ q 
  h p q (u , v) = PropExt fe pe u v
  f  : (p q : Prop) → p ≡ q → p ≡ q
  f p q e = h p q (g p q e)
  constant-f : (p q : Prop) (d e : p ≡ q) → f p q d ≡ f p q e 
  constant-f p q d e = ap (h p q) (A-isProp p q (g p q d) (g p q e))
  pc : {p q : Prop} → Σ \(f : p ≡ q → p ≡ q) → constant f
  pc {p} {q} = (f p q , constant-f p q)

neg-isProp : ∀ {U} {X : U ̇} → FunExt U U₀ → isProp(¬ X)
neg-isProp fe u v = funext fe (λ x → 𝟘-elim (u x)) 

disjoint-images : ∀ {U V W} {X : U ̇} {Y : V ̇} {A : W ̇} → (X → A) → (Y → A) → U ⊔ V ⊔ W ̇
disjoint-images f g = ∀ x y → f x ≢ g y

disjoint-cases-embedding : ∀ {U V W} {X : U ̇} {Y : V ̇} {A : W ̇} (f : X → A) (g : Y → A)
                         → isEmbedding f → isEmbedding g → disjoint-images f g
                         → isEmbedding (cases f g)
disjoint-cases-embedding {U} {V} {W} {X} {Y} {A} f g ef eg d = go
  where
   go : (a : A) (σ τ : Σ \(z : X + Y) → cases f g z ≡ a) → σ ≡ τ
   go a (inl x , p) (inl x' , p') = r
     where
       q : x , p ≡ x' , p'
       q = ef a (x , p) (x' , p')
       h : fiber f a → fiber (cases f g) a
       h (x , p) = inl x , p
       r : inl x , p ≡ inl x' , p'
       r = ap h q
   go a (inl x , p) (inr y  , q) = 𝟘-elim (d x y (p ∙ q ⁻¹))
   go a (inr y , q) (inl x  , p) = 𝟘-elim (d x y (p ∙ q ⁻¹))
   go a (inr y , q) (inr y' , q') = r
     where
       p : y , q ≡ y' , q'
       p = eg a (y , q) (y' , q')
       h : fiber g a → fiber (cases f g) a
       h (y , q) = inr y , q
       r : inr y , q ≡ inr y' , q'
       r = ap h p

\end{code}
