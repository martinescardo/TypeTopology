Tom de Jong, 8 March 2020

Minor updates on 28 January 2022

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT hiding (J)

open import UF-FunExt
open import UF-PropTrunc
open import UF-Subsingletons

module IdealCompletion-Properties
        (pt : propositional-truncations-exist)
        (fe : ∀ {𝓤} {𝓥} → funext 𝓤 𝓥)
        (pe : ∀ {𝓤} → propext 𝓤)
        (𝓥 : Universe) -- universe where the index types for directedness
                        -- completeness live
       where

open import Dcpo pt fe 𝓥
open import DcpoMiscelanea pt fe 𝓥

-- open import DcpoAlgebraic pt fe 𝓥
open import DcpoWayBelow pt fe 𝓥
-- open import DcpoBasis pt fe 𝓥

open import DcpoBases pt pe fe 𝓥
open import DcpoContinuous pt fe 𝓥


open import IdealCompletion pt fe pe 𝓥

open import UF-Equiv
open import UF-Powerset

open PropositionalTruncation pt

module _
        {X : 𝓤 ̇ }
        (_≺_ : X → X → 𝓣 ̇ )
       where

 reflexivity-implies-INT₀ : ({x : X} → x ≺ x) → (x : X) → ∃ y ꞉ X , y ≺ x
 reflexivity-implies-INT₀ r x = ∣ x , r ∣

 reflexivity-implies-INT₂ : ({x : X} → x ≺ x) → {y₀ y₁ x : X} → y₀ ≺ x → y₁ ≺ x
                          → ∃ z ꞉ X , y₀ ≺ z × y₁ ≺ z × z ≺ x
 reflexivity-implies-INT₂ r {y₀} {y₁} {x} l m = ∣ x , l , m , r ∣

module Idl-Properties
        {X : 𝓤 ̇ }
        (_≺_ : X → X → 𝓥 ⊔ 𝓣 ̇ )
        (≺-prop-valued : {x y : X} → is-prop (x ≺ y))
        (INT₂ : {y₀ y₁ x : X} → y₀ ≺ x → y₁ ≺ x
              → ∃ z ꞉ X , y₀ ≺ z × y₁ ≺ z × z ≺ x)
        (INT₀ : (x : X) → ∃ y ꞉ X , y ≺ x)
        (≺-trans : {x y z : X} → x ≺ y → y ≺ z → x ≺ z)
       where

 open Ideals {𝓤} {𝓥 ⊔ 𝓣} {X} _≺_ ≺-prop-valued INT₂ INT₀ ≺-trans

 roundedness : (I : Idl) {x : X} → (x ∈ᵢ I) → ∃ y ꞉ X , y ∈ᵢ I × x ≺ y
 roundedness I {x} xI = ∥∥-functor γ h
  where
   h : ∃ y ꞉ X , y ∈ᵢ I × x ≺ y × x ≺ y
   h = directed-sets-are-semidirected (carrier I)
       (ideals-are-directed-sets (carrier I) (ideality I))
       x x xI xI
   γ : (Σ y ꞉ X , y ∈ᵢ I × x ≺ y × x ≺ y)
     → Σ y ꞉ X , y ∈ᵢ I × x ≺ y
   γ (y , yI , l , _) = y , yI , l

 ↓_ : X → Idl
 ↓ x = (λ (y : X) → (y ≺ x) , ≺-prop-valued) ,
       ls , inh , δ
  where
   ls : is-lower-set (λ y → (y ≺ x) , ≺-prop-valued)
   ls x y = ≺-trans
   inh : ∃ y ꞉ X , y ≺ x
   inh = INT₀ x
   δ : is-semidirected-set (λ y → (y ≺ x) , ≺-prop-valued)
   δ y₁ y₂ l₁ l₂ = ∥∥-functor γ (INT₂ l₁ l₂)
    where
     γ : (Σ z ꞉ X , y₁ ≺ z × y₂ ≺ z × z ≺ x)
       → (Σ z ꞉ X , z ≺ x × y₁ ≺ z × y₂ ≺ z)
     γ (z , m₁ , m₂ , n) = z , n , m₁ , m₂

 ↓-is-monotone : {x y : X} → x ≺ y → (↓ x) ⊑⟨ Idl-DCPO ⟩ (↓ y)
 ↓-is-monotone {x} {y} l _ m = ≺-trans m l

\end{code}

\begin{code}

module SmallIdeals
        {X : 𝓥 ̇ }
        (_≺_ : X → X → 𝓥 ̇ )
        (≺-prop-valued : {x y : X} → is-prop (x ≺ y))
        (INT₂ : {y₀ y₁ x : X} → y₀ ≺ x → y₁ ≺ x
              → ∃ z ꞉ X , y₀ ≺ z × y₁ ≺ z × z ≺ x)
        (INT₀ : (x : X) → ∃ y ꞉ X , y ≺ x)
        (≺-trans : {x y z : X} → x ≺ y → y ≺ z → x ≺ z)
       where

 open Ideals {𝓥} {𝓥} {X} _≺_ ≺-prop-valued INT₂ INT₀ ≺-trans
 open Idl-Properties {𝓥} {𝓥} {X} _≺_ ≺-prop-valued INT₂ INT₀ ≺-trans

 ↓-of-ideal : (I : Idl) → 𝕋 (carrier I) → Idl
 ↓-of-ideal I (i , _) = ↓ i

 ↓-of-ideal-is-directed : (I : Idl) → is-Directed Idl-DCPO (↓-of-ideal I)
 ↓-of-ideal-is-directed (I , ι) = inh , ε
  where
   δ : is-semidirected-set I
   δ = directed-sets-are-semidirected I (ideals-are-directed-sets I ι)
   inh : ∥ 𝕋 I ∥
   inh = directed-sets-are-inhabited I (ideals-are-directed-sets I ι)
   ε : is-semidirected _⊑_ (↓-of-ideal (I , ι))
   ε (i , p) (j , q) = ∥∥-functor γ (δ i j p q)
    where
     γ : (Σ x ꞉ X , x ∈ I × i ≺ x × j ≺ x)
       → Σ k ꞉ 𝕋 I , (↓-of-ideal (I , ι) (i , p) ⊑ ↓-of-ideal (I , ι) k)
                   × (↓-of-ideal (I , ι) (j , q) ⊑ ↓-of-ideal (I , ι) k)
     γ (x , xI , lᵢ , lⱼ) = (x , xI) , (u , v)
      where
       u : ↓-of-ideal (I , ι) (i , p) ⊑ ↓-of-ideal (I , ι) (x , xI)
       u y mᵢ = ≺-trans mᵢ lᵢ
       v : ↓-of-ideal (I , ι) (j , q) ⊑ ↓-of-ideal (I , ι) (x , xI)
       v y m = ≺-trans m lⱼ

 Idl-∐-≡ : (I : Idl)
         → I ≡ ∐ Idl-DCPO {_} {↓-of-ideal I} (↓-of-ideal-is-directed I)
 Idl-∐-≡ I = antisymmetry Idl-DCPO I (∐ Idl-DCPO {_} {α} δ) l₁ l₂
  where
   α : 𝕋 (carrier I) → Idl
   α = ↓-of-ideal I
   δ : is-Directed Idl-DCPO α
   δ = ↓-of-ideal-is-directed I
   l₁ : I ⊑⟨ Idl-DCPO ⟩ ∐ Idl-DCPO {_} {α} δ
   l₁ i p = ∥∥-functor γ (roundedness I p)
    where
     γ : (Σ j ꞉ X , j ∈ᵢ I × i ≺ j)
       → Σ a ꞉ 𝕋 (carrier I) , i ∈ᵢ α a
     γ (j , q , m) = (j , q) , m
   l₂ : ∐ Idl-DCPO {_} {α} δ ⊑⟨ Idl-DCPO ⟩ I
   l₂ i p = ∥∥-rec (∈-is-prop (carrier I) i) γ p
    where
     γ : (Σ j ꞉ 𝕋 (carrier I) , i ≺ pr₁ j) → i ∈ carrier I
     γ ((j , q) , m) = ideals-are-lower-sets (carrier I) (ideality I)
                           i j m q

 Idl-≪-in-terms-of-⊑ : (I J : Idl) → I ≪⟨ Idl-DCPO ⟩ J
                     → ∃ x ꞉ X , x ∈ᵢ J × I ⊑⟨ Idl-DCPO ⟩ (↓ x)
 Idl-≪-in-terms-of-⊑ I J u = ∥∥-functor γ g
  where
   γ : (Σ j ꞉ 𝕋 (carrier J) , I ⊑⟨ Idl-DCPO ⟩ (↓-of-ideal J j))
     → Σ x ꞉ X , x ∈ᵢ J × I ⊑⟨ Idl-DCPO ⟩ (↓ x)
   γ ((j , p) , l) = j , (p , l)
   g : ∃ j ꞉ 𝕋 (carrier J) , I ⊑⟨ Idl-DCPO ⟩ (↓-of-ideal J j)
   g = u (𝕋 (carrier J)) (↓-of-ideal J) (↓-of-ideal-is-directed J)
       (≡-to-⊑ Idl-DCPO (Idl-∐-≡ J))

 Idl-≪-in-terms-of-⊑₂ : (I J : Idl) → I ≪⟨ Idl-DCPO ⟩ J
                      → ∃ x ꞉ X , Σ y ꞉ X , x ≺ y
                                          × I ⊑⟨ Idl-DCPO ⟩ (↓ x)
                                          × (↓ x) ⊑⟨ Idl-DCPO ⟩ (↓ y)
                                          × (↓ y) ⊑⟨ Idl-DCPO ⟩ J
 Idl-≪-in-terms-of-⊑₂ I J u = ∥∥-rec ∥∥-is-prop γ (Idl-≪-in-terms-of-⊑ I J u)
  where
   γ : (Σ x ꞉ X , x ∈ᵢ J × I ⊑⟨ Idl-DCPO ⟩ (↓ x))
     → ∃ x ꞉ X , Σ y ꞉ X , x ≺ y
               × I ⊑⟨ Idl-DCPO ⟩ (↓ x)
               × (↓ x) ⊑⟨ Idl-DCPO ⟩ (↓ y)
               × (↓ y) ⊑⟨ Idl-DCPO ⟩ J
   γ (x , xJ , s) = ∥∥-functor g (roundedness J xJ)
    where
     g : (Σ y ꞉ X , y ∈ᵢ J × x ≺ y)
       → Σ x ꞉ X , Σ y ꞉ X , x ≺ y
                 × I ⊑⟨ Idl-DCPO ⟩ (↓ x)
                 × (↓ x) ⊑⟨ Idl-DCPO ⟩ (↓ y)
                 × (↓ y) ⊑⟨ Idl-DCPO ⟩ J
     g (y , yJ , l) = x , y , l , s , t , r
      where
       t : (↓ x) ⊑⟨ Idl-DCPO ⟩ (↓ y)
       t = ↓-is-monotone l
       r : (↓ y) ⊑⟨ Idl-DCPO ⟩ J
       r z m = ideals-are-lower-sets (carrier J) (ideality J) z y m yJ

 Idl-≪-in-terms-of-⊑' : (I J : Idl)
                      → ∃ x ꞉ X , x ∈ᵢ J × I ⊑⟨ Idl-DCPO ⟩ (↓ x)
                      → I ≪⟨ Idl-DCPO ⟩ J
 Idl-≪-in-terms-of-⊑' I J = ∥∥-rec (≪-is-prop-valued Idl-DCPO {I} {J}) γ
  where
   γ : (Σ x ꞉ X , x ∈ᵢ J × I ⊑⟨ Idl-DCPO ⟩ (↓ x))
     → I ≪⟨ Idl-DCPO ⟩ J
   γ (x , xJ , s) 𝓐 α δ t = ∥∥-functor g (t x xJ)
    where
     g : (Σ a ꞉ 𝓐 , x ∈ᵢ α a)
       → Σ a ꞉ 𝓐 , I ⊑⟨ Idl-DCPO ⟩ α a
     g (a , xa) = a , r
      where
       r : I ⊑⟨ Idl-DCPO ⟩ α a
       r = transitivity Idl-DCPO I (↓ x) (α a) s q
        where
         q : (↓ x) ⊑⟨ Idl-DCPO ⟩ α a
         q y l = ideals-are-lower-sets (carrier (α a)) (ideality (α a)) y x l xa

 Idl-≪-in-terms-of-⊑₂' : (I J : Idl)
                       → ∃ x ꞉ X , Σ y ꞉ X , x ≺ y
                                 × I ⊑⟨ Idl-DCPO ⟩ (↓ x)
                                 × (↓ x) ⊑⟨ Idl-DCPO ⟩ (↓ y)
                                 × (↓ y) ⊑⟨ Idl-DCPO ⟩ J
                       → I ≪⟨ Idl-DCPO ⟩ J
 Idl-≪-in-terms-of-⊑₂' I J = ∥∥-rec (≪-is-prop-valued Idl-DCPO {I} {J}) γ
  where
   γ : (Σ x ꞉ X , Σ y ꞉ X , x ≺ y
                × I ⊑⟨ Idl-DCPO ⟩ (↓ x)
                × (↓ x) ⊑⟨ Idl-DCPO ⟩ (↓ y)
                × (↓ y) ⊑⟨ Idl-DCPO ⟩ J)
     → I ≪⟨ Idl-DCPO ⟩ J
   γ (x , y , l , s , _ , r) 𝓐 α δ m = ∥∥-functor g (m x (r x l))
    where
     g : (Σ a ꞉ 𝓐 , x ∈ᵢ α a)
       → Σ a ꞉ 𝓐 , I ⊑⟨ Idl-DCPO ⟩ α a
     g (a , xa) = a , h
      where
       h : I ⊑⟨ Idl-DCPO ⟩ α a
       h = transitivity Idl-DCPO I (↓ x) (α a) s s'
        where
         s' : (↓ x) ⊑⟨ Idl-DCPO ⟩ α a
         s' z n = ideals-are-lower-sets (carrier (α a)) (ideality (α a)) z x n xa

\end{code}

\begin{code}

 Idl-mediating-directed : (𝓓 : DCPO {𝓤} {𝓣})
                        → (f : X → ⟨ 𝓓 ⟩)
                        → ({x  y : X} → x ≺ y → f x ⊑⟨ 𝓓 ⟩ f y)
                        → (I : Idl)
                        → is-Directed 𝓓 {𝕋 (carrier I)} (f ∘ pr₁)
 Idl-mediating-directed 𝓓 f m I =
  (directed-sets-are-inhabited (carrier I) Idir) , ε
   where
    ι : 𝕋 (carrier I) → ⟨ 𝓓 ⟩
    ι = f ∘ pr₁
    Idir : is-directed-set (carrier I)
    Idir = ideals-are-directed-sets (carrier I) (ideality I)
    ε : is-semidirected (underlying-order 𝓓) ι
    ε (x , xI) (y , yI) = ∥∥-functor γ g
     where
      γ : (Σ z ꞉ X , z ∈ᵢ I × x ≺ z × y ≺ z)
        → Σ i ꞉ 𝕋 (carrier I) , (ι (x , xI) ⊑⟨ 𝓓 ⟩ ι i)
                              × (ι (y , yI) ⊑⟨ 𝓓 ⟩ ι i)
      γ (z , zI , lx , ly) = (z , zI) , m lx , m ly
      g : ∃ z ꞉ X , z ∈ᵢ I × x ≺ z × y ≺ z
      g = directed-sets-are-semidirected (carrier I) Idir x y xI yI

 Idl-mediating-map : (𝓓 : DCPO {𝓤} {𝓣})
                   → (f : X → ⟨ 𝓓 ⟩)
                   → ({x  y : X} → x ≺ y → f x ⊑⟨ 𝓓 ⟩ f y)
                   → Idl → ⟨ 𝓓 ⟩
 Idl-mediating-map 𝓓 f m I = ∐ 𝓓 (Idl-mediating-directed 𝓓 f m I)

 Idl-mediating-map-commutes : (𝓓 : DCPO {𝓤} {𝓣})
                            → (f : X → ⟨ 𝓓 ⟩)
                            → (m : {x  y : X} → x ≺ y → f x ⊑⟨ 𝓓 ⟩ f y)
                            → ({x : X} → x ≺ x)
                            → Idl-mediating-map 𝓓 f m ∘ ↓_ ∼ f
 Idl-mediating-map-commutes 𝓓 f m ρ x = γ
  where
   δ : is-Directed 𝓓 (f ∘ pr₁)
   δ = Idl-mediating-directed 𝓓 f m (↓ x)
   γ : ∐ 𝓓 δ ≡ f x
   γ = antisymmetry 𝓓 (∐ 𝓓 δ) (f x) a b
    where
     a : ∐ 𝓓 δ ⊑⟨ 𝓓 ⟩ f x
     a = ∐-is-lowerbound-of-upperbounds 𝓓 δ (f x) g
      where
       g : (y : Σ z ꞉ X , z ∈ᵢ (↓ x))
         → f (pr₁ y) ⊑⟨ 𝓓 ⟩ f x
       g (y , l) = m l
     b : f x ⊑⟨ 𝓓 ⟩ ∐ 𝓓 δ
     b = ∐-is-upperbound 𝓓 δ (x , ρ)

 Idl-mediating-map-is-continuous : (𝓓 : DCPO {𝓤} {𝓣})
                                 → (f : X → ⟨ 𝓓 ⟩)
                                 → (m : {x  y : X} → x ≺ y → f x ⊑⟨ 𝓓 ⟩ f y)
                                 → is-continuous Idl-DCPO 𝓓
                                   (Idl-mediating-map 𝓓 f m)
 Idl-mediating-map-is-continuous 𝓓 f m 𝓐 α δ = ub , lb
  where
   f' : Idl → ⟨ 𝓓 ⟩
   f' = Idl-mediating-map 𝓓 f m
   ε : (I : Idl) → is-Directed 𝓓 (f ∘ pr₁)
   ε = Idl-mediating-directed 𝓓 f m
   ub : (a : 𝓐) → f' (α a) ⊑⟨ 𝓓 ⟩ f' (∐ Idl-DCPO {𝓐} {α} δ)
   ub a = ∐-is-lowerbound-of-upperbounds 𝓓 (ε (α a))
          (f' (∐ Idl-DCPO {𝓐} {α} δ)) γ
    where
     γ : (y : (Σ x ꞉ X , x ∈ᵢ α a))
       → f (pr₁ y) ⊑⟨ 𝓓 ⟩ f' (∐ Idl-DCPO {𝓐} {α} δ)
     γ (x , p) = ∐-is-upperbound 𝓓 (ε (∐ Idl-DCPO {𝓐} {α} δ)) g
      where
       g : Σ y ꞉ X , y ∈ᵢ (∐ Idl-DCPO {𝓐} {α} δ)
       g = x , ∣ a , p ∣
   lb : is-lowerbound-of-upperbounds (underlying-order 𝓓)
         (f' (∐ Idl-DCPO {𝓐} {α} δ))
         (λ a → f' (α a))
   lb d u = ∐-is-lowerbound-of-upperbounds 𝓓 (ε (∐ Idl-DCPO {𝓐} {α} δ)) d γ
    where
     γ : (x : (Σ y ꞉ X , y ∈ᵢ ∐ Idl-DCPO {𝓐} {α} δ))
       → f (pr₁ x) ⊑⟨ 𝓓 ⟩ d
     γ (x , p) = ∥∥-rec (prop-valuedness 𝓓 (f x) d) g p
      where
       g : (Σ a ꞉ 𝓐 , x ∈ᵢ α a) → f x ⊑⟨ 𝓓 ⟩ d
       g (a , q) = f x      ⊑⟨ 𝓓 ⟩[ ∐-is-upperbound 𝓓 (ε (α a)) (x , q) ]
                   f' (α a) ⊑⟨ 𝓓 ⟩[ u a ]
                   d        ∎⟨ 𝓓 ⟩

\end{code}

\begin{code}

 ↓≪-characterization : {I : Idl} {x : X}
                     → (↓ x) ≪⟨ Idl-DCPO ⟩ I ≃ x ∈ᵢ I
 ↓≪-characterization {I} {x} = logically-equivalent-props-are-equivalent {!!} {!!} ⦅⇒⦆ {!!}
  where
   ⦅⇒⦆ : (↓ x) ≪⟨ Idl-DCPO ⟩ I → x ∈ᵢ I
   ⦅⇒⦆ ↓x-way-below-I = ∥∥-rec (∈-is-prop (carrier I) x) h (Idl-≪-in-terms-of-⊑ (↓ x) I ↓x-way-below-I)
    where
     h : Σ (λ x₁ → (x₁ ∈ᵢ I) × underlying-order Idl-DCPO (↓ x) (↓ x₁)) →
           x ∈ carrier I
     h (y , ↓x-below-↓y) = {!!}

 ι : (I : Idl) → (Σ x ꞉ X , (↓ x) ≪⟨ Idl-DCPO ⟩ I) → Idl
 ι I = ↓_ ∘ pr₁

{-

↓ x ≪ I
↓ y ⋘ I

↝ (in-terms-of...)

↓ x ⊑ ↓ bˣ and bˣ ∈ I
↓ x ⊑ ↓ bʸ and bʸ ∈ I

↝ (I semidirected set)

↓ x , ↓ y   ⊑   ↓ b   and   b ∈ I  and   bˣ ≺ b   and   bʸ ≺ b

↝

Do we have ↓ b ≪ I ? (Yes, as b ∈ I ?)

-}

 ι-is-directed : (I : Idl) → is-Directed (Idl-DCPO) (ι I)
 ι-is-directed I = {!!}

{-
 Idl-≪-in-terms-of-⊑' : (I J : Idl)
                      → ∃ x ꞉ X , x ∈ᵢ J × I ⊑⟨ Idl-DCPO ⟩ (↓ x)
                      → I ≪⟨ Idl-DCPO ⟩ J
-}

{- inh , semidir
  where
   inh : ∥ domain (ι I) ∥
   inh = ∥∥-rec ∥∥-is-prop f
          (directed-sets-are-inhabited (carrier I)
            (ideals-are-directed-sets (carrier I) (ideality I)))
    where
     f : (Σ x ꞉ X , x ∈ᵢ I) → ∥ domain (ι I) ∥
     f (x , x-in-I) = ∥∥-functor g (INT₀ x)
      where
       g : (Σ y ꞉ X , y ≺ x) → domain (ι I)
       g (y , y-below-x) =
        (y , Idl-≪-in-terms-of-⊑' (↓ y) I ∣ x , x-in-I , ↓-is-monotone y-below-x ∣)
   semidir : is-semidirected _⊑_ (ι I)
   semidir (x , ↓x-way-below-I) (y , ↓y-way-below-I) =
    ∥∥-rec₂ ∃-is-prop f (Idl-≪-in-terms-of-⊑₂ (↓ x) I ↓x-way-below-I)
                        (Idl-≪-in-terms-of-⊑₂ (↓ y) I ↓y-way-below-I)
     where
      f : (Σ bˣ ꞉ X , Σ cˣ ꞉ X , (bˣ ≺ cˣ)
                               × (↓ x)  ⊑ (↓ bˣ)
                               × (↓ bˣ) ⊑ (↓ cˣ)
                               × (↓ cˣ) ⊑ I)
        → (Σ bʸ ꞉ X , Σ cʸ ꞉ X , (bʸ ≺ cʸ)
                               × (↓ y)  ⊑ (↓ bʸ)
                               × (↓ bʸ) ⊑ (↓ cʸ)
                               × (↓ cʸ) ⊑ I)
        → (∃ k ꞉ (domain (ι I)) , ((↓ x) ⊑ ι I k) × ((↓ y) ⊑ ι I k))
      f (bˣ , cˣ , lˣ , uˣ , vˣ , wˣ) (bʸ , cʸ , lʸ , uʸ , vʸ , wʸ) = ∥∥-functor {!!} (INT₂ {!!} lʸ)
-}

 ↓-is-a-basis-of-Idl : is-small-basis Idl-DCPO ↓_
 ↓-is-a-basis-of-Idl = record {
   ≪ᴮ-is-small    = λ I x → ((↓ x) ≪ₛ I) , e (↓ x) I;
   ↡ᴮ-is-directed = δ;
   ↡ᴮ-is-sup      = λ I → transport (is-sup _⊑_ I) {!Idl-∐-≡!} {!!}
  }
   where
    _≪ₛ_ : Idl → Idl → 𝓥 ̇
    I ≪ₛ J = ∃ x ꞉ X , (x ∈ᵢ J) × I ⊑⟨ Idl-DCPO ⟩ (↓ x)
    e : (I J : Idl) → I ≪ₛ J ≃ I ≪⟨ Idl-DCPO ⟩ J
    e I J = logically-equivalent-props-are-equivalent
             ∃-is-prop (≪-is-prop-valued Idl-DCPO {I} {J})
             (Idl-≪-in-terms-of-⊑' I J)
             (Idl-≪-in-terms-of-⊑ I J)
    δ : (I : ⟨ Idl-DCPO ⟩) → is-Directed Idl-DCPO (ι I)
    δ I = {!!}

{-
 Idl-≪-in-terms-of-⊑' : (I J : Idl)
                      → ∃ x ꞉ X , x ∈ᵢ J × I ⊑⟨ Idl-DCPO ⟩ (↓ x)
                      → I ≪⟨ Idl-DCPO ⟩ J
-}



{-
 ↓-is-a-basis-of-Idl : is-a-basis Idl-DCPO ↓_
 ↓-is-a-basis-of-Idl = s , γ
  where
   ≺' : X → X → 𝓥 ̇
   ≺' x y = ∃ z ꞉ X , z ≺ y × (↓ x) ⊑⟨ Idl-DCPO ⟩ (↓ z)
   s : ≪-small-on-B Idl-DCPO ↓_
   s x y = ≺' x y , e
    where
     e : ≺' x y ≃ (↓ x) ≪⟨ Idl-DCPO ⟩ (↓ y)
     e = logically-equivalent-props-are-equivalent
         ∥∥-is-prop
         (≪-is-prop-valued Idl-DCPO {↓ x} {↓ y})
         (Idl-≪-in-terms-of-⊑' (↓ x ) (↓ y))
         (Idl-≪-in-terms-of-⊑ (↓ x) (↓ y))
   γ : (I : Idl)
     → ∃ 𝓐 ꞉ 𝓥 ̇ , Σ α ꞉ (𝓐 → X) ,
         ((a : 𝓐) → (↓ (α a)) ≪⟨ Idl-DCPO ⟩ I)
       × (Σ δ ꞉ is-Directed Idl-DCPO (↓_ ∘ α) ,
           ∐ Idl-DCPO {𝓐} {↓_ ∘ α} δ ≡ I)
   γ I = ∣ 𝕋 (carrier I) , pr₁ , g , δ , ((Idl-∐-≡ I) ⁻¹) ∣
    where
     g : (i : 𝕋 (carrier I)) → (↓ pr₁ i) ≪⟨ Idl-DCPO ⟩ I
     g (i , p) = Idl-≪-in-terms-of-⊑' (↓ i) I
                 ∣ i , p , reflexivity Idl-DCPO (↓ i) ∣
     δ : is-Directed Idl-DCPO (↓-of-ideal I)
     δ = ↓-of-ideal-is-directed I

 Idl-is-continuous : is-a-continuous-dcpo (Idl-DCPO)
 Idl-is-continuous = ∣ X , ↓_ , ↓-is-a-basis-of-Idl ∣
-}

\end{code}

\begin{code}

{-
 Idl-is-algebraic-if-order-is-reflexive : ((x : X) → x ≺ x)
                                        → is-an-algebraic-dcpo Idl-DCPO
 Idl-is-algebraic-if-order-is-reflexive ρ = ∣ X , ↓_ , ↓-is-a-basis-of-Idl , κ ∣
  where
   κ : (x : X) → is-compact Idl-DCPO (↓ x)
   κ x = Idl-≪-in-terms-of-⊑' (↓ x) (↓ x) γ
    where
     γ : ∃ y ꞉ X , y ∈ᵢ (↓ x) × (↓ x) ⊑⟨ Idl-DCPO ⟩ (↓ y)
     γ = ∣ x , ρ x , reflexivity Idl-DCPO (↓ x) ∣
-}

\end{code}
