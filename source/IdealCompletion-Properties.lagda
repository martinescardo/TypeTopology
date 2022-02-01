Tom de Jong, 8 March 2020

TODO: Minor updates on 28 January 2022

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
   ls : is-lowerset (λ y → (y ≺ x) , ≺-prop-valued)
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
     γ ((j , q) , m) = ideals-are-lowersets (carrier I) (ideality I)
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
       r z m = ideals-are-lowersets (carrier J) (ideality J) z y m yJ

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
         q y l = ideals-are-lowersets (carrier (α a)) (ideality (α a)) y x l xa

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
         s' z n = ideals-are-lowersets (carrier (α a)) (ideality (α a)) z x n xa

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

 -- TODO: Move elsewhere?
 ↓≪-criterion : (I : Idl) (x : X)
              → x ∈ᵢ I → (↓ x) ≪⟨ Idl-DCPO ⟩ I
 ↓≪-criterion I x x-in-I =
  Idl-≪-in-terms-of-⊑' (↓ x) I ∣ x , x-in-I , reflexivity Idl-DCPO (↓ x) ∣

 ↓⊑-criterion : (I : Idl) (x : X)
              → x ∈ᵢ I → (↓ x) ⊑ I
 ↓⊑-criterion I x x-in-I = ≪-to-⊑ Idl-DCPO {↓ x} {I} (↓≪-criterion I x x-in-I)


 ι : (I : Idl) → (Σ x ꞉ X , (↓ x) ≪⟨ Idl-DCPO ⟩ I) → Idl
 ι I = ↓_ ∘ pr₁

 ι-is-directed : (I : Idl) → is-Directed (Idl-DCPO) (ι I)
 ι-is-directed I = inh , semidir
  where
   inh : ∥ domain (ι I) ∥
   inh = ∥∥-functor h (directed-sets-are-inhabited (carrier I)
                     (ideals-are-directed-sets (carrier I) (ideality I)))
    where
     h : 𝕋 (carrier I) → domain (ι I)
     h (x , x-in-I) = (x , ↓≪-criterion I x x-in-I)
   semidir : is-semidirected _⊑_ (ι I)
   semidir (x , ↓x-way-below-I) (y , ↓y-way-below-I) =
    ∥∥-rec₂ ∃-is-prop f
           (Idl-≪-in-terms-of-⊑ (↓ x) I ↓x-way-below-I)
           (Idl-≪-in-terms-of-⊑ (↓ y) I ↓y-way-below-I)
     where
      f : (Σ x' ꞉ X , x' ∈ᵢ I × (↓ x) ⊑ (↓ x'))
        → (Σ y' ꞉ X , y' ∈ᵢ I × (↓ y) ⊑ (↓ y'))
        → ∃ k ꞉ domain (ι I) , ((↓ x) ⊑ ι I k) × ((↓ y) ⊑ ι I k)
      f (x' , x'-in-I , ↓x-below-↓x') (y' , y'-in-I , ↓y-below-↓y') =
       ∥∥-functor g (directed-sets-are-semidirected
                        (carrier I)
                        (ideals-are-directed-sets (carrier I) (ideality I))
                        x' y' x'-in-I y'-in-I)
        where
         g : (Σ z ꞉ X , z ∈ᵢ I × (x' ≺ z) × (y' ≺ z))
           → Σ k ꞉ domain (ι I) , ((↓ x) ⊑ ι I k) × ((↓ y) ⊑ ι I k)
         g (z , z-in-I , x'-below-z , y'-below-z) =
          (z , ↓≪-criterion I z z-in-I) , (u , v)
           where
            u : (↓ x) ⊑ (↓ z)
            u = transitivity Idl-DCPO (↓ x) (↓ x') (↓ z)
                 ↓x-below-↓x' (↓-is-monotone x'-below-z)
            v : (↓ y) ⊑ (↓ z)
            v = transitivity Idl-DCPO (↓ y) (↓ y') (↓ z)
                 ↓y-below-↓y' (↓-is-monotone y'-below-z)

 ι-sup : (I : Idl) → is-sup _⊑_ I (ι I)
 ι-sup I = ub , lb-of-ubs
  where
   ub : is-upperbound _⊑_ I (ι I)
   ub (x , ↓x-way-below-I) y y-below-x = s y y-below-x
    where
     s : (↓ x) ⊑ I
     s = ≪-to-⊑ Idl-DCPO {↓ x} {I} ↓x-way-below-I
   lb-of-ubs : is-lowerbound-of-upperbounds _⊑_ I (ι I)
   lb-of-ubs J J-is-ub x x-in-I = ∥∥-rec (∈-is-prop (carrier J) x) h
                                        (roundedness I x-in-I)
    where
     h : (Σ y ꞉ X , y ∈ᵢ I × x ≺ y) → x ∈ᵢ J
     h (y , y-in-I , x-below-y) = J-is-ub (y , lem) x x-below-y
      where
       lem : (↓ y) ≪⟨ Idl-DCPO ⟩ I
       lem = ↓≪-criterion I y y-in-I

 ↓-is-small-basis : is-small-basis Idl-DCPO ↓_
 ↓-is-small-basis = record {
   ≪ᴮ-is-small    = λ I x → ((↓ x) ≪ₛ I) , e (↓ x) I;
   ↡ᴮ-is-directed = ι-is-directed;
   ↡ᴮ-is-sup      = ι-sup
  }
   where
    _≪ₛ_ : Idl → Idl → 𝓥 ̇
    I ≪ₛ J = ∃ x ꞉ X , (x ∈ᵢ J) × I ⊑⟨ Idl-DCPO ⟩ (↓ x)
    e : (I J : Idl) → I ≪ₛ J ≃ I ≪⟨ Idl-DCPO ⟩ J
    e I J = logically-equivalent-props-are-equivalent
             ∃-is-prop (≪-is-prop-valued Idl-DCPO {I} {J})
             (Idl-≪-in-terms-of-⊑' I J)
             (Idl-≪-in-terms-of-⊑ I J)

 Idl-has-specified-small-basis : has-specified-small-basis Idl-DCPO
 Idl-has-specified-small-basis = (X , ↓_ , ↓-is-small-basis)

 Idl-structurally-continuous : structurally-continuous Idl-DCPO
 Idl-structurally-continuous = structurally-continuous-if-specified-small-basis
  Idl-DCPO Idl-has-specified-small-basis

 Idl-is-continuous-dcpo : is-continuous-dcpo Idl-DCPO
 Idl-is-continuous-dcpo = ∣ Idl-structurally-continuous ∣


\end{code}

\begin{code}

 module _
         (≺-is-reflexive : (x : X) → x ≺ x)
        where

  ↓⊑-criterion-converse : (I : Idl) (x : X)
                        → (↓ x) ⊑ I → x ∈ᵢ I
  ↓⊑-criterion-converse I x ↓x-below-I = ↓x-below-I x (≺-is-reflexive x)

  κ : (I : Idl) → (Σ x ꞉ X , (↓ x) ⊑ I) → Idl
  κ I = ↓_ ∘ pr₁

  κ-is-directed : (I : Idl) → is-Directed Idl-DCPO (κ I)
  κ-is-directed I = inh , semidir
   where
    inh : ∥ domain (κ I) ∥
    inh = ∥∥-functor h (directed-sets-are-inhabited (carrier I)
                        (ideals-are-directed-sets (carrier I) (ideality I)))
     where
      h : 𝕋 (carrier I) → domain (κ I)
      h (x , x-in-I) = (x , ↓⊑-criterion I x x-in-I)
    semidir : is-semidirected _⊑_ (κ I)
    semidir (x , ↓x-below-I) (y , ↓y-below-I) =
     ∥∥-functor h (directed-sets-are-semidirected (carrier I)
                      (ideals-are-directed-sets (carrier I) (ideality I))
                      x y (↓⊑-criterion-converse I x ↓x-below-I)
                          (↓⊑-criterion-converse I y ↓y-below-I))
      where
       h : (Σ z ꞉ X , z ∈ᵢ I × (x ≺ z) × (y ≺ z))
         → Σ k ꞉ domain (κ I) , ((↓ x) ⊑ κ I k) × ((↓ y) ⊑ κ I k)
       h (z , z-in-I , x-below-z , y-below-z) =
        (z , ↓⊑-criterion I z z-in-I) , (↓-is-monotone x-below-z) ,
                                        (↓-is-monotone y-below-z)

  κ-sup : (I : Idl) → is-sup _⊑_ I (κ I)
  κ-sup I = ub , lb-of-ubs
   where
    ub : is-upperbound _⊑_ I (κ I)
    ub (x , ↓x-below-I) y y-below-x = ↓x-below-I y y-below-x
    lb-of-ubs : is-lowerbound-of-upperbounds _⊑_ I (κ I)
    lb-of-ubs J J-is-ub x x-in-I =
     J-is-ub (x , ↓⊑-criterion I x x-in-I) x (≺-is-reflexive x)

  ↓-is-compact : (x : X) → is-compact Idl-DCPO (↓ x)
  ↓-is-compact x 𝓘 α δ x-below-∐α =
   ∥∥-functor h (x-below-∐α x (≺-is-reflexive x))
    where
     h : (Σ i ꞉ 𝓘 , x ∈ᵢ α i)
       → Σ i ꞉ 𝓘 , (↓ x) ⊑ α i
     h (i , x-in-αᵢ) = (i , ↓⊑-criterion (α i) x x-in-αᵢ)

  ↓-if-compact : (I : Idl) → is-compact Idl-DCPO I
               → ∃ x ꞉ X , ↓ x ≡ I
  ↓-if-compact I c =
   ∥∥-functor h (c (𝕋 (carrier I))
                     (↓-of-ideal I)
                     (↓-of-ideal-is-directed I)
                     (≡-to-⊑ Idl-DCPO (Idl-∐-≡ I)))
    where
     h : (Σ i ꞉ 𝕋 (carrier I) , I ⊑ (↓ pr₁ i))
       → Σ x ꞉ X , ↓ x ≡ I
     h ((x , x-in-I) , I-below-↓x ) =
      (x , antisymmetry Idl-DCPO (↓ x) I (↓⊑-criterion I x x-in-I) I-below-↓x)

  ↓-is-small-compact-basis : is-small-compact-basis Idl-DCPO ↓_
  ↓-is-small-compact-basis = record {
    basis-is-compact = ↓-is-compact;
    ⊑ᴮ-is-small      = λ I x → ((↓ x) ⊑ I) , (≃-refl ((↓ x) ⊑ I));
    ↓ᴮ-is-directed   = κ-is-directed;
    ↓ᴮ-is-sup        = κ-sup
   }

  Idl-has-specified-small-compact-basis : has-specified-small-compact-basis Idl-DCPO
  Idl-has-specified-small-compact-basis = (X , ↓_ , ↓-is-small-compact-basis)

  Idl-structurally-algebraic : structurally-algebraic Idl-DCPO
  Idl-structurally-algebraic =
   structurally-algebraic-if-specified-small-compact-basis
    Idl-DCPO Idl-has-specified-small-compact-basis

  Idl-is-algebraic-dcpo : is-algebraic-dcpo Idl-DCPO
  Idl-is-algebraic-dcpo = ∣ Idl-structurally-algebraic ∣

\end{code}

Dcpos with a small basis are continuous retracts (in fact, e-p pair...) of
algebraic dcpos.

\begin{code}

module _
        (𝓓 : DCPO {𝓤} {𝓣})
        {B : 𝓥 ̇  }
        (β : B → ⟨ 𝓓 ⟩)
        (β-is-small-basis : is-small-basis 𝓓 β)
       where

 open is-small-basis β-is-small-basis

 _⊑ₛ_ : ⟨ 𝓓 ⟩ → ⟨ 𝓓 ⟩ → 𝓥 ̇
 _⊑ₛ_ = pr₁ (locally-small-if-small-basis 𝓓 β β-is-small-basis)

 _⊑ᴮ_ : B → B → 𝓥 ̇
 b ⊑ᴮ b' = β b ⊑ₛ β b'

 ⊑ᴮ-≃-⊑ : {b b' : B} → (b ⊑ᴮ b') ≃ (β b ⊑⟨ 𝓓 ⟩ β b')
 ⊑ᴮ-≃-⊑ {b} {b'} = (b ⊑ᴮ b')         ≃⟨ ⦅1⦆ ⟩
                   (β b ⊑ₛ β b')     ≃⟨ ⦅2⦆ ⟩
                   (β b ⊑⟨ 𝓓 ⟩ β b') ■
  where
   ⦅1⦆ = ≃-refl (b ⊑ᴮ b')
   ⦅2⦆ = pr₂ (locally-small-if-small-basis 𝓓 β β-is-small-basis) (β b) (β b')

 ⊑ᴮ-is-prop-valued : {b b' : B} → is-prop (b ⊑ᴮ b')
 ⊑ᴮ-is-prop-valued = equiv-to-prop ⊑ᴮ-≃-⊑ (prop-valuedness 𝓓 _ _)

 ⊑ᴮ-is-reflexive : {b : B} → b ⊑ᴮ b
 ⊑ᴮ-is-reflexive = ⌜ ⊑ᴮ-≃-⊑ ⌝⁻¹ (reflexivity 𝓓 _)

 ⊑ᴮ-is-transitive : {b b' b'' : B} → b ⊑ᴮ b' → b' ⊑ᴮ b'' → b ⊑ᴮ b''
 ⊑ᴮ-is-transitive u v = ⌜ ⊑ᴮ-≃-⊑ ⌝⁻¹
                         (transitivity 𝓓 _ _ _ (⌜ ⊑ᴮ-≃-⊑ ⌝ u) (⌜ ⊑ᴮ-≃-⊑ ⌝ v))

 -- TODO: Rework this?
 open Ideals {𝓥} {𝓥} {B} _⊑ᴮ_
             ⊑ᴮ-is-prop-valued
             (reflexivity-implies-INT₂ _⊑ᴮ_ ⊑ᴮ-is-reflexive)
             (reflexivity-implies-INT₀ _⊑ᴮ_ ⊑ᴮ-is-reflexive)
             ⊑ᴮ-is-transitive
 open SmallIdeals {B} _⊑ᴮ_
                  ⊑ᴮ-is-prop-valued
                  (reflexivity-implies-INT₂ _⊑ᴮ_ ⊑ᴮ-is-reflexive)
                  (reflexivity-implies-INT₀ _⊑ᴮ_ ⊑ᴮ-is-reflexive)
                  ⊑ᴮ-is-transitive
 open Idl-Properties {𝓥} {𝓥} {B} _⊑ᴮ_
                     ⊑ᴮ-is-prop-valued
                     (reflexivity-implies-INT₂ _⊑ᴮ_ ⊑ᴮ-is-reflexive)
                     (reflexivity-implies-INT₀ _⊑ᴮ_ ⊑ᴮ-is-reflexive)
                     ⊑ᴮ-is-transitive

 to-Idl : ⟨ 𝓓 ⟩ → Idl
 to-Idl x = Bₓ , (Bₓ-is-lowerset , Bₓ-is-directed-set)
  where
   Bₓ : 𝓟 B
   Bₓ b = (b ≪ᴮₛ x , ≪ᴮₛ-is-prop-valued)
   Bₓ-is-lowerset : is-lowerset Bₓ
   Bₓ-is-lowerset b c b-below-c c-in-Bₓ =
    ⌜ ≪ᴮₛ-≃-≪ᴮ ⌝⁻¹ (⊑-≪-to-≪ 𝓓 (⌜ ⊑ᴮ-≃-⊑ ⌝ b-below-c)
                                 (⌜ ≪ᴮₛ-≃-≪ᴮ ⌝ c-in-Bₓ))
   Bₓ-is-inhabited : ∥ 𝕋 Bₓ ∥
   Bₓ-is-inhabited = inhabited-if-Directed 𝓓 (↡ιₛ x) (↡ᴮₛ-is-directed x)
   Bₓ-is-semidirected-set : is-semidirected-set Bₓ
   Bₓ-is-semidirected-set b₁ b₂ b₁-in-Bₓ b₂-in-Bₓ =
    ∥∥-functor (λ ((b , b-in-Bₓ) , u , v)
               → (b , b-in-Bₓ , ⌜ ⊑ᴮ-≃-⊑ ⌝⁻¹ u , ⌜ ⊑ᴮ-≃-⊑ ⌝⁻¹ v))
              (semidirected-if-Directed 𝓓 (↡ιₛ x) (↡ᴮₛ-is-directed x)
                (b₁ , b₁-in-Bₓ) (b₂ , b₂-in-Bₓ))
   Bₓ-is-directed-set : is-directed-set Bₓ
   Bₓ-is-directed-set = (Bₓ-is-inhabited , Bₓ-is-semidirected-set)


 ideals-are-directed : (I : Idl)
                     → is-Directed 𝓓 (β ∘ 𝕋-to-carrier (carrier I))
 ideals-are-directed I = inh , semidir
  where
   δ : is-directed-set (carrier I)
   δ = ideals-are-directed-sets (carrier I) (ideality I)
   inh : ∥ 𝕋 (carrier I) ∥
   inh = directed-sets-are-inhabited (carrier I) δ
   semidir : is-semidirected (underlying-order 𝓓) (β ∘ 𝕋-to-carrier (carrier I))
   semidir (b₁ , b₁-in-I) (b₂ , b₂-in-I) =
    ∥∥-functor (λ (b , b-in-I , u , v)
               → ((b , b-in-I) , ⌜ ⊑ᴮ-≃-⊑ ⌝ u , ⌜ ⊑ᴮ-≃-⊑ ⌝ v))
              (directed-sets-are-semidirected (carrier I) δ b₁ b₂ b₁-in-I b₂-in-I)

 from-Idl : Idl → ⟨ 𝓓 ⟩
 from-Idl I = ∐ 𝓓 (ideals-are-directed I)

 open import UF-Retracts

 Idl-retract : retract ⟨ 𝓓 ⟩ of Idl
 Idl-retract = (r , s , γ)
  where
   s : ⟨ 𝓓 ⟩ → Idl
   s = to-Idl
   r : Idl → ⟨ 𝓓 ⟩
   r = from-Idl
   γ : r ∘ s ∼ id
   γ x = antisymmetry 𝓓 (r (s x)) x ⦅1⦆ ⦅2⦆
    where
     ⦅2⦆ : x ⊑⟨ 𝓓 ⟩ r (s x)
     ⦅2⦆ = transport (λ - → - ⊑⟨ 𝓓 ⟩ r (s x)) (↡ᴮₛ-∐-≡ x) lemma
      where
       lemma : ∐ 𝓓 (↡ᴮₛ-is-directed x) ⊑⟨ 𝓓 ⟩ r (s x)
       lemma = ∐-is-lowerbound-of-upperbounds 𝓓 (↡ᴮₛ-is-directed x) (r (s x))
                (∐-is-upperbound 𝓓 (ideals-are-directed (s x)))
     ⦅1⦆ : r (s x) ⊑⟨ 𝓓 ⟩ x
     ⦅1⦆ = ∐-is-lowerbound-of-upperbounds 𝓓 (ideals-are-directed (s x)) x ub
      where
       ub : is-upperbound (underlying-order 𝓓) x
             (β ∘ 𝕋-to-carrier (carrier (s x)))
       ub (b , b-way-below-sx) = ≪-to-⊑ 𝓓 (⌜ ≪ᴮₛ-≃-≪ᴮ ⌝ b-way-below-sx)

 Idl-deflation : (I : Idl) → to-Idl (from-Idl I) ⊑⟨ Idl-DCPO ⟩ I
 Idl-deflation 𝕀@(I , I-is-ideal) b b-way-below-∐I =
  ∥∥-rec (∈-is-prop I b) h
        (⌜ ≪ᴮₛ-≃-≪ᴮ ⌝ b-way-below-∐I (𝕋 I) (β ∘ pr₁)
          (ideals-are-directed 𝕀) (reflexivity 𝓓 (from-Idl 𝕀)))
   where
    h : (Σ i ꞉ 𝕋 I , β b ⊑⟨ 𝓓 ⟩ (β (pr₁ i))) → b ∈ I
    h ((i , i-in-I) , u) = ideals-are-lowersets I I-is-ideal b i
                            (⌜ ⊑ᴮ-≃-⊑ ⌝⁻¹ u) i-in-I

 to-Idl-is-monotone : is-monotone 𝓓 Idl-DCPO to-Idl
 to-Idl-is-monotone x y x-below-y b b-way-below-x =
  ⌜ ≪ᴮₛ-≃-≪ᴮ ⌝⁻¹ (≪-⊑-to-≪ 𝓓 (⌜ ≪ᴮₛ-≃-≪ᴮ ⌝ b-way-below-x) x-below-y)

 to-Idl-is-continuous : is-continuous 𝓓 Idl-DCPO to-Idl
 to-Idl-is-continuous = continuity-criterion' 𝓓 Idl-DCPO to-Idl
                         to-Idl-is-monotone γ
  where
   γ : (𝓐 : 𝓥 ̇) (α : 𝓐 → ⟨ 𝓓 ⟩) (δ : is-Directed 𝓓 α)
     → is-lowerbound-of-upperbounds _⊑_ (to-Idl (∐ 𝓓 δ)) (to-Idl ∘ α)
   γ 𝓐 α δ (I , I-is-ideal) I-is-ub b b-way-below-∐α =
    ∥∥-rec (∈-is-prop I b) claim lemma
     where
      lemma : ∃ c ꞉ B , (β b ≪⟨ 𝓓 ⟩ β c) × (β c ≪⟨ 𝓓 ⟩ ∐ 𝓓 δ)
      lemma = small-basis-unary-interpolation 𝓓 β β-is-small-basis
               (⌜ ≪ᴮₛ-≃-≪ᴮ ⌝ b-way-below-∐α)
      claim : (Σ c ꞉ B , (β b ≪⟨ 𝓓 ⟩ β c) × (β c ≪⟨ 𝓓 ⟩ ∐ 𝓓 δ))
            → b ∈ I
      claim (c , b-way-below-c , c-way-below-∐α) =
       ∥∥-rec (∈-is-prop I b) h (c-way-below-∐α 𝓐 α δ (reflexivity 𝓓 (∐ 𝓓 δ)))
        where
         h : (Σ a ꞉ 𝓐 , β c ⊑⟨ 𝓓 ⟩ α a) → b ∈ I
         h (a , c-below-αa) = I-is-ub a b (⌜ ≪ᴮₛ-≃-≪ᴮ ⌝⁻¹ wb)
          where
           wb : β b ≪⟨ 𝓓 ⟩ α a
           wb = ≪-⊑-to-≪ 𝓓 b-way-below-c c-below-αa

 -- TODO: Reconsider opening this?
 open Ind-completion 𝓓

 from-Idl-is-monotone : is-monotone Idl-DCPO 𝓓 from-Idl
 from-Idl-is-monotone I J I-below-J =
  ∐-map-is-monotone 𝕀 𝕁 γ
   where
    𝕀 : Ind
    𝕀 = (𝕋 (carrier I) , β ∘ pr₁ , ideals-are-directed I)
    𝕁 : Ind
    𝕁 = (𝕋 (carrier J) , β ∘ pr₁ , ideals-are-directed J)
    γ : 𝕀 ≲ 𝕁
    γ (b , b-in-I) = ∣ (b , (I-below-J b b-in-I)) , (reflexivity 𝓓 (β b)) ∣

 from-Idl-is-continuous : is-continuous Idl-DCPO 𝓓 from-Idl
 from-Idl-is-continuous = continuity-criterion' Idl-DCPO 𝓓 from-Idl
                           from-Idl-is-monotone γ
  where
   γ : (𝓐 : 𝓥 ̇) (α : 𝓐 → ⟨ Idl-DCPO ⟩) (δ : is-Directed Idl-DCPO α)
     → is-lowerbound-of-upperbounds (underlying-order 𝓓)
        (from-Idl (∐ Idl-DCPO {𝓐} {α} δ)) (from-Idl ∘ α)
   γ 𝓐 α δ x x-is-ub = ∐-is-lowerbound-of-upperbounds 𝓓
                        (ideals-are-directed (∐ Idl-DCPO {𝓐} {α} δ)) x ub
    where
     ub : is-upperbound (underlying-order 𝓓) x
           (β ∘ 𝕋-to-carrier (carrier (∐ Idl-DCPO {𝓐} {α} δ)))
     ub (b , b-in-⋃) = ∥∥-rec (prop-valuedness 𝓓 (β b) x) h b-in-⋃
      where
       h : (Σ a ꞉ 𝓐 , b ∈ᵢ α a) → β b ⊑⟨ 𝓓 ⟩ x
       h (a , b-in-αa) = β b            ⊑⟨ 𝓓 ⟩[ ⦅1⦆ ]
                         from-Idl (α a) ⊑⟨ 𝓓 ⟩[ ⦅2⦆ ]
                         x              ∎⟨ 𝓓 ⟩
        where
         ⦅1⦆ = ∐-is-upperbound 𝓓 (ideals-are-directed (α a)) (b , b-in-αa)
         ⦅2⦆ = x-is-ub a

 Idl-continuous-retract : 𝓓 continuous-retract-of Idl-DCPO
 Idl-continuous-retract =
  record
   { s = to-Idl
   ; r = from-Idl
   ; r-s-equation = retract-condition Idl-retract
   ; s-is-continuous = to-Idl-is-continuous
   ; r-is-continuous = from-Idl-is-continuous
   }

 -- TODO:
 {-
  ∗ (e-p pair) ; define first
 -}

 Idl-is-algebraic : is-algebraic-dcpo Idl-DCPO
 Idl-is-algebraic = Idl-is-algebraic-dcpo (λ b → ⊑ᴮ-is-reflexive)

\end{code}

TODO: D ≅ Idl (B , ≺)

\begin{code}

\end{code}
