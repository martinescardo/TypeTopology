Tom de Jong, 8 March 2020

TODO: Minor updates on 28 January 2022;
      major updates 31 January - 4 February 2022.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --experimental-lossy-unification #-}

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

open import DcpoBases pt fe 𝓥
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

 Idl-sups-from-powerset : {𝓐 : 𝓥 ̇  } (α : 𝓐 → Idl) (I : Idl)
                        → is-sup _⊆_ (carrier I) (carrier ∘ α)
                        → is-sup _⊑_ I α
 Idl-sups-from-powerset {𝓐} α I I-is-sup = (ub , lb-of-ubs)
  where
   ub : is-upperbound _⊑_ I α
   ub = sup-is-upperbound _⊆_ {𝓥} {𝓐} {carrier I} {carrier ∘ α} I-is-sup
   lb-of-ubs : is-lowerbound-of-upperbounds _⊑_ I α
   lb-of-ubs J J-is-ub = sup-is-lowerbound-of-upperbounds _⊆_ {𝓥} {𝓐}
                          {carrier I} {carrier ∘ α}
                          I-is-sup (carrier J) J-is-ub

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

 open Ideals {𝓥} {𝓥} {X} _≺_ ≺-prop-valued INT₂ INT₀ ≺-trans public
 open Idl-Properties {𝓥} {𝓥} {X} _≺_ ≺-prop-valued INT₂ INT₀ ≺-trans public

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

 module Idl-mediating
         (𝓓 : DCPO {𝓤} {𝓣})
         (f : X → ⟨ 𝓓 ⟩)
         (f-is-monotone : {x y : X} → x ≺ y → f x ⊑⟨ 𝓓 ⟩ f y)
        where

  Idl-mediating-directed : (I : Idl)
                         → is-Directed 𝓓 {𝕋 (carrier I)} (f ∘ pr₁)
  Idl-mediating-directed I =
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
       γ (z , zI , lx , ly) = (z , zI) , f-is-monotone lx , f-is-monotone ly
       g : ∃ z ꞉ X , z ∈ᵢ I × x ≺ z × y ≺ z
       g = directed-sets-are-semidirected (carrier I) Idir x y xI yI

  Idl-mediating-map : Idl → ⟨ 𝓓 ⟩
  Idl-mediating-map I = ∐ 𝓓 (Idl-mediating-directed I)

  -- TODO: Use continuity-criterion' instead?
  Idl-mediating-map-is-continuous : is-continuous Idl-DCPO 𝓓 Idl-mediating-map
  Idl-mediating-map-is-continuous 𝓐 α δ = ub , lb
   where
    f' : Idl → ⟨ 𝓓 ⟩
    f' = Idl-mediating-map
    ε : (I : Idl) → is-Directed 𝓓 (f ∘ pr₁)
    ε = Idl-mediating-directed
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

  Idl-mediating-map-commutes : ({x : X} → x ≺ x)
                             → Idl-mediating-map ∘ ↓_ ∼ f
  Idl-mediating-map-commutes ρ x = γ
   where
    δ : is-Directed 𝓓 (f ∘ pr₁)
    δ = Idl-mediating-directed (↓ x)
    γ : ∐ 𝓓 δ ≡ f x
    γ = antisymmetry 𝓓 (∐ 𝓓 δ) (f x) a b
     where
      a : ∐ 𝓓 δ ⊑⟨ 𝓓 ⟩ f x
      a = ∐-is-lowerbound-of-upperbounds 𝓓 δ (f x) g
       where
        g : (y : Σ z ꞉ X , z ∈ᵢ (↓ x))
          → f (pr₁ y) ⊑⟨ 𝓓 ⟩ f x
        g (y , l) = f-is-monotone l
      b : f x ⊑⟨ 𝓓 ⟩ ∐ 𝓓 δ
      b = ∐-is-upperbound 𝓓 δ (x , ρ)

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

TODO: We should do some of the below on the level of powersets so as to avoid
duplication of code/proofs.

\begin{code}

module Idl-common -- TODO: Rethink module name
        (𝓓 : DCPO {𝓤} {𝓣})
        {B : 𝓥 ̇  }
        (β : B → ⟨ 𝓓 ⟩)
        (β-is-small-basis : is-small-basis 𝓓 β)
       where

 open is-small-basis β-is-small-basis

 ↡ᴮ-subset : (x : ⟨ 𝓓 ⟩) → 𝓟 B
 ↡ᴮ-subset x = (λ b → (b ≪ᴮₛ x , ≪ᴮₛ-is-prop-valued))

 ↡ᴮ-subset-is-inhabited : (x : ⟨ 𝓓 ⟩) → ∥ 𝕋 (↡ᴮ-subset x) ∥
 ↡ᴮ-subset-is-inhabited x = inhabited-if-Directed 𝓓 (↡ιₛ x) (↡ᴮₛ-is-directed x)

 ↡ᴮ-is-monotone : (x y : ⟨ 𝓓 ⟩) → x ⊑⟨ 𝓓 ⟩ y → ↡ᴮ-subset x ⊆ ↡ᴮ-subset y
 ↡ᴮ-is-monotone x y x-below-y b b-way-below-x =
  ⌜ ≪ᴮₛ-≃-≪ᴮ ⌝⁻¹ (≪-⊑-to-≪ 𝓓 (⌜ ≪ᴮₛ-≃-≪ᴮ ⌝ b-way-below-x) x-below-y)

 ↡ᴮ-is-continuous : {I : 𝓥 ̇  } {α : I → ⟨ 𝓓 ⟩} (δ : is-Directed 𝓓 α)
                  → is-sup _⊆_ (↡ᴮ-subset (∐ 𝓓 δ)) (↡ᴮ-subset ∘ α)
 ↡ᴮ-is-continuous {I} {α} δ = (ub , lb-of-ubs)
  where
   ub : is-upperbound _⊆_ (↡ᴮ-subset (∐ 𝓓 δ)) (↡ᴮ-subset ∘ α)
   ub i b b-way-below-αᵢ =
    ⌜ ≪ᴮₛ-≃-≪ᴮ ⌝⁻¹ (≪-⊑-to-≪ 𝓓 (⌜ ≪ᴮₛ-≃-≪ᴮ ⌝ b-way-below-αᵢ)
                                 (∐-is-upperbound 𝓓 δ i))
   lb-of-ubs : is-lowerbound-of-upperbounds _⊆_
                (↡ᴮ-subset (∐ 𝓓 δ)) (↡ᴮ-subset ∘ α)
   lb-of-ubs S S-is-ub b b-way-below-∐α =
    ∥∥-rec (∈-is-prop S b) lemma₁ claim₁
     where
      claim₁ : ∃ c ꞉ B , (β b ≪⟨ 𝓓 ⟩ β c) × (β c ≪⟨ 𝓓 ⟩ (∐ 𝓓 δ))
      claim₁ = small-basis-unary-interpolation 𝓓 β β-is-small-basis
               (⌜ ≪ᴮₛ-≃-≪ᴮ ⌝ b-way-below-∐α)
      lemma₁ : (Σ c ꞉ B , (β b ≪⟨ 𝓓 ⟩ β c) × (β c ≪⟨ 𝓓 ⟩ (∐ 𝓓 δ)))
             → b ∈ S
      lemma₁ (c , b-way-below-c , c-way-below-∐α) =
       ∥∥-rec (∈-is-prop S b) lemma₂ claim₂
        where
         claim₂ : ∃ i ꞉ I , β c ⊑⟨ 𝓓 ⟩ α i
         claim₂ = c-way-below-∐α I α δ (reflexivity 𝓓 (∐ 𝓓 δ))
         lemma₂ : (Σ i ꞉ I , β c ⊑⟨ 𝓓 ⟩ α i) → b ∈ S
         lemma₂ (i , c-below-αᵢ) =
          S-is-ub i b (⌜ ≪ᴮₛ-≃-≪ᴮ ⌝⁻¹ (≪-⊑-to-≪ 𝓓 b-way-below-c c-below-αᵢ))

 ∐-of-directed-subset : (I : 𝓟 B)
                      → is-Directed 𝓓 (β ∘ 𝕋-to-carrier I)
                      → ⟨ 𝓓 ⟩
 ∐-of-directed-subset I δ = ∐ 𝓓 δ

 -- TODO: Swap ↡ᴮ and ∐?
 ↡ᴮ-∐-retract : (x : ⟨ 𝓓 ⟩) (δ : is-Directed 𝓓 (↡ιₛ x))
              → ∐-of-directed-subset (↡ᴮ-subset x) δ ≡ x
 ↡ᴮ-∐-retract x δ = ∐ 𝓓 δ ≡⟨ ⦅1⦆ ⟩
                    ∐ 𝓓 ε ≡⟨ ⦅2⦆ ⟩
                    x     ∎
  where
   ε : is-Directed 𝓓 (↡ιₛ x)
   ε = ↡ᴮₛ-is-directed x
   ⦅1⦆ = ∐-independent-of-directedness-witness 𝓓 δ ε
   ⦅2⦆ = ↡ᴮₛ-∐-≡ x

 -- TODO: Swap ↡ᴮ and ∐?
 ∐-↡ᴮ-deflation : (I : 𝓟 B) {δ : is-Directed 𝓓 (β ∘ 𝕋-to-carrier I)}
                → ((b c : B) → β b ⊑⟨ 𝓓 ⟩ β c → c ∈ I → b ∈ I)
                → ↡ᴮ-subset (∐-of-directed-subset I δ) ⊆ I
 ∐-↡ᴮ-deflation I {δ} I-lowerset b b-way-below-sup =
  ∥∥-rec (∈-is-prop I b) lemma claim
   where
    claim : ∃ i ꞉ 𝕋 I , β b ⊑⟨ 𝓓 ⟩ β ((𝕋-to-carrier I) i)
    claim = ⌜ ≪ᴮₛ-≃-≪ᴮ ⌝ b-way-below-sup (𝕋 I) (β ∘ 𝕋-to-carrier I) δ
             (reflexivity 𝓓 (∐ 𝓓 δ))
    lemma : (Σ i ꞉ 𝕋 I , β b ⊑⟨ 𝓓 ⟩ β ((𝕋-to-carrier I) i))
          → b ∈ I
    lemma ((c , c-in-I) , b-below-c) = I-lowerset b c b-below-c c-in-I

 ∐-↡ᴮ-inflation : (I : 𝓟 B) {δ : is-Directed 𝓓 (β ∘ 𝕋-to-carrier I)}
                → ((b : B) → b ∈ I → ∃ c ꞉ B , (c ∈ I) × (β b ≪⟨ 𝓓 ⟩ β c))
                → I ⊆ ↡ᴮ-subset (∐-of-directed-subset I δ)
 ∐-↡ᴮ-inflation I {δ} I-rounded b b-in-I = ∥∥-rec ≪ᴮₛ-is-prop-valued lemma claim
  where
   claim : ∃ c ꞉ B , (c ∈ I) × (β b ≪⟨ 𝓓 ⟩ β c)
   claim = I-rounded b b-in-I
   lemma : (Σ c ꞉ B , (c ∈ I) × (β b ≪⟨ 𝓓 ⟩ β c))
         → b ≪ᴮₛ ∐-of-directed-subset I δ
   lemma (c , c-in-I , b-way-below-c) =
    ⌜ ≪ᴮₛ-≃-≪ᴮ ⌝⁻¹ (≪-⊑-to-≪ 𝓓 b-way-below-c (∐-is-upperbound 𝓓 δ (c , c-in-I)))

 ∐-↡ᴮ-retract : (I : 𝓟 B) {δ : is-Directed 𝓓 (β ∘ 𝕋-to-carrier I)}
              → ((b c : B) → β b ⊑⟨ 𝓓 ⟩ β c → c ∈ I → b ∈ I)
              → ((b : B) → b ∈ I → ∃ c ꞉ B , (c ∈ I) × (β b ≪⟨ 𝓓 ⟩ β c))
              → ↡ᴮ-subset (∐-of-directed-subset I δ) ≡ I
 ∐-↡ᴮ-retract I {δ} cond₁ cond₂ =
  subset-extensionality pe fe (∐-↡ᴮ-deflation I cond₁) (∐-↡ᴮ-inflation I cond₂)

 module _
         (_≺_ : B → B → 𝓥 ̇  )
        where

  ↡ᴮ-lowerset-criterion : (x : ⟨ 𝓓 ⟩)
                        → ((b c : B) → b ≺ c → β b ⊑⟨ 𝓓 ⟩ β c)
                        → (b c : B) → b ≺ c → c ∈ ↡ᴮ-subset x → b ∈ ↡ᴮ-subset x
  ↡ᴮ-lowerset-criterion x β-mon b c b-below-c c-way-below-x =
   ⌜ ≪ᴮₛ-≃-≪ᴮ ⌝⁻¹ (⊑-≪-to-≪ 𝓓 (β-mon b c b-below-c) (⌜ ≪ᴮₛ-≃-≪ᴮ ⌝ c-way-below-x))

  ↡ᴮ-semidirected-set-criterion : (x : ⟨ 𝓓 ⟩)
                                → ((b c : B) → β b ≪⟨ 𝓓 ⟩ β c → b ≺ c)
                                → (a b : B) → a ∈ ↡ᴮ-subset x → b ∈ ↡ᴮ-subset x
                                → ∃ c ꞉ B , c ∈ ↡ᴮ-subset x × (a ≺ c) × (b ≺ c)
  ↡ᴮ-semidirected-set-criterion x β-mon a b a-way-below-x b-way-below-x =
   ∥∥-functor h (small-basis-binary-interpolation 𝓓 β β-is-small-basis
                 (⌜ ≪ᴮₛ-≃-≪ᴮ ⌝ a-way-below-x)
                 (⌜ ≪ᴮₛ-≃-≪ᴮ ⌝ b-way-below-x))
    where
     h : (Σ c ꞉ B , (β a ≪⟨ 𝓓 ⟩ β c) × (β b ≪⟨ 𝓓 ⟩ β c) × (β c ≪⟨ 𝓓 ⟩ x))
       → (Σ c ꞉ B , c ∈ ↡ᴮ-subset x × (a ≺ c) × (b ≺ c))
     h (c , a-way-below-c , b-way-below-c , c-way-below-x) =
      (c , ⌜ ≪ᴮₛ-≃-≪ᴮ ⌝⁻¹ c-way-below-x , β-mon a c a-way-below-c
                                        , β-mon b c b-way-below-c)

\end{code}

Dcpos with a small basis are continuous retracts (in fact, e-p pair...) of
algebraic dcpos.

\begin{code}

module Idl-algebraic -- TODO: Rethink module name
        (𝓓 : DCPO {𝓤} {𝓣})
        {B : 𝓥 ̇  }
        (β : B → ⟨ 𝓓 ⟩)
        (β-is-small-basis : is-small-basis 𝓓 β)
       where

 open is-small-basis β-is-small-basis
 open is-locally-small (locally-small-if-small-basis 𝓓 β β-is-small-basis)

 _⊑ᴮ_ : B → B → 𝓥 ̇
 b ⊑ᴮ b' = β b ⊑ₛ β b'

 ⊑ᴮ-≃-⊑ : {b b' : B} → (b ⊑ᴮ b') ≃ (β b ⊑⟨ 𝓓 ⟩ β b')
 ⊑ᴮ-≃-⊑ {b} {b'} = ⊑ₛ-≃-⊑

 ⊑ᴮ-is-prop-valued : {b b' : B} → is-prop (b ⊑ᴮ b')
 ⊑ᴮ-is-prop-valued = equiv-to-prop ⊑ᴮ-≃-⊑ (prop-valuedness 𝓓 _ _)

 ⊑ᴮ-is-reflexive : {b : B} → b ⊑ᴮ b
 ⊑ᴮ-is-reflexive = ⌜ ⊑ᴮ-≃-⊑ ⌝⁻¹ (reflexivity 𝓓 _)

 ⊑ᴮ-is-transitive : {b b' b'' : B} → b ⊑ᴮ b' → b' ⊑ᴮ b'' → b ⊑ᴮ b''
 ⊑ᴮ-is-transitive u v = ⌜ ⊑ᴮ-≃-⊑ ⌝⁻¹
                         (transitivity 𝓓 _ _ _ (⌜ ⊑ᴮ-≃-⊑ ⌝ u) (⌜ ⊑ᴮ-≃-⊑ ⌝ v))

 open SmallIdeals {B} _⊑ᴮ_
                  ⊑ᴮ-is-prop-valued
                  (reflexivity-implies-INT₂ _⊑ᴮ_ ⊑ᴮ-is-reflexive)
                  (reflexivity-implies-INT₀ _⊑ᴮ_ ⊑ᴮ-is-reflexive)
                  ⊑ᴮ-is-transitive
      public
 open Idl-common 𝓓 β β-is-small-basis public
 open Idl-mediating 𝓓 β ⌜ ⊑ᴮ-≃-⊑ ⌝ public

 to-Idl : ⟨ 𝓓 ⟩ → Idl
 to-Idl x = (Bₓ , Bₓ-is-lowerset , Bₓ-is-directed-set)
  where
   Bₓ : 𝓟 B
   Bₓ = ↡ᴮ-subset x
   Bₓ-is-lowerset : is-lowerset Bₓ
   Bₓ-is-lowerset = ↡ᴮ-lowerset-criterion _⊑ᴮ_ x (λ b c → ⌜ ⊑ᴮ-≃-⊑ ⌝)
   Bₓ-is-semidirected-set : is-semidirected-set Bₓ
   Bₓ-is-semidirected-set =
    ↡ᴮ-semidirected-set-criterion _⊑ᴮ_ x
     (λ b c b-way-below-c → ⌜ ⊑ᴮ-≃-⊑ ⌝⁻¹ (≪-to-⊑ 𝓓 b-way-below-c))
   Bₓ-is-directed-set : is-directed-set Bₓ
   Bₓ-is-directed-set = (↡ᴮ-subset-is-inhabited x , Bₓ-is-semidirected-set)

 from-Idl : Idl → ⟨ 𝓓 ⟩
 from-Idl I = Idl-mediating-map I

 open import UF-Retracts

 Idl-retract : retract ⟨ 𝓓 ⟩ of Idl
 Idl-retract = (r , s , γ)
  where
   s : ⟨ 𝓓 ⟩ → Idl
   s = to-Idl
   r : Idl → ⟨ 𝓓 ⟩
   r = from-Idl
   γ : (x : ⟨ 𝓓 ⟩) → r (s x) ≡ x
   γ x = ↡ᴮ-∐-retract x (Idl-mediating-directed (s x))

 Idl-deflation : (I : Idl) → to-Idl (from-Idl I) ⊑⟨ Idl-DCPO ⟩ I
 Idl-deflation 𝕀@(I , I-is-ideal) = ∐-↡ᴮ-deflation I γ
  where
   γ : (b c : B) → β b ⊑⟨ 𝓓 ⟩ β c → c ∈ I → b ∈ I
   γ b c b-below-c c-in-I = ideals-are-lowersets I I-is-ideal b c claim c-in-I
    where
     claim : b ⊑ᴮ c
     claim = ⌜ ⊑ᴮ-≃-⊑ ⌝⁻¹ b-below-c

 to-Idl-is-continuous : is-continuous 𝓓 Idl-DCPO to-Idl
 to-Idl-is-continuous I α δ =
  Idl-sups-from-powerset (to-Idl ∘ α) (to-Idl (∐ 𝓓 δ)) (↡ᴮ-is-continuous δ)

 from-Idl-is-continuous : is-continuous Idl-DCPO 𝓓 from-Idl
 from-Idl-is-continuous = Idl-mediating-map-is-continuous

 Idl-continuous-retract : 𝓓 continuous-retract-of Idl-DCPO
 Idl-continuous-retract =
  record
   { s = to-Idl
   ; r = from-Idl
   ; s-section-of-r = retract-condition Idl-retract
   ; s-is-continuous = to-Idl-is-continuous
   ; r-is-continuous = from-Idl-is-continuous
   }

 Idl-embedding-projection-pair : embedding-projection-pair-between 𝓓 Idl-DCPO
 Idl-embedding-projection-pair =
  record
    { e = to-Idl
    ; p = from-Idl
    ; e-section-of-p = retract-condition Idl-retract
    ; e-p-deflation = Idl-deflation
    ; e-is-continuous = to-Idl-is-continuous
    ; p-is-continuous = from-Idl-is-continuous
    }

 Idl-is-algebraic : is-algebraic-dcpo Idl-DCPO
 Idl-is-algebraic = Idl-is-algebraic-dcpo (λ b → ⊑ᴮ-is-reflexive)

\end{code}

D ≅ Idl (B , ≺)

\begin{code}

module Idl-continuous
        (𝓓 : DCPO {𝓤} {𝓣})
        {B : 𝓥 ̇  }
        (β : B → ⟨ 𝓓 ⟩)
        (β-is-small-basis : is-small-basis 𝓓 β)
       where

 open is-small-basis β-is-small-basis

 _≺_ : B → B → 𝓥 ̇
 b ≺ b' = b ≪ᴮₛ β b'

 ≺-≃-≪ : {b b' : B} → (b ≺ b') ≃ (β b ≪⟨ 𝓓 ⟩ β b')
 ≺-≃-≪ {b} {b'} = ≪ᴮₛ-≃-≪ᴮ

 ≺-is-prop-valued : {b b' : B} → is-prop (b ≺ b')
 ≺-is-prop-valued = equiv-to-prop ≺-≃-≪ (≪-is-prop-valued 𝓓)

 ≺-is-transitive : {b b' b'' : B} → b ≺ b' → b' ≺ b'' → b ≺ b''
 ≺-is-transitive u v =
  ⌜ ≺-≃-≪ ⌝⁻¹ (≪-is-transitive 𝓓 (⌜ ≺-≃-≪ ⌝ u) (⌜ ≺-≃-≪ ⌝ v))

 ≺-INT₀ : (b : B) → ∃ c ꞉ B , c ≺ b
 ≺-INT₀ b = ∥∥-functor h
             (small-basis-nullary-interpolation 𝓓 β β-is-small-basis (β b))
  where
   h : (Σ c ꞉ B , β c ≪⟨ 𝓓 ⟩ β b) → (Σ c ꞉ B , c ≺ b)
   h (c , c-way-below-b) = (c , ⌜ ≺-≃-≪ ⌝⁻¹ c-way-below-b)

 ≺-INT₂ : {b₁ b₂ b : B} → b₁ ≺ b → b₂ ≺ b
        → ∃ c ꞉ B , (b₁ ≺ c) × (b₂ ≺ c) × (c ≺ b)
 ≺-INT₂ {b₁} {b₂} {b} b₁-below-b b₂-below-b =
  ∥∥-functor h (small-basis-binary-interpolation 𝓓 β β-is-small-basis
                (⌜ ≺-≃-≪ ⌝ b₁-below-b) (⌜ ≺-≃-≪ ⌝ b₂-below-b))
   where
    h : (Σ c ꞉ B , (β b₁ ≪⟨ 𝓓 ⟩ β c)
                 × (β b₂ ≪⟨ 𝓓 ⟩ β c)
                 × (β c ≪⟨ 𝓓 ⟩ β b))
      → (Σ c ꞉ B , (b₁ ≺ c) × (b₂ ≺ c) × (c ≺ b))
    h (c , u , v , w) = (c , ⌜ ≺-≃-≪ ⌝⁻¹ u , ⌜ ≺-≃-≪ ⌝⁻¹ v , ⌜ ≺-≃-≪ ⌝⁻¹ w)

 open SmallIdeals {B}  _≺_
                  ≺-is-prop-valued
                  ≺-INT₂
                  ≺-INT₀
                  ≺-is-transitive

 open Idl-common 𝓓 β β-is-small-basis
 open Idl-mediating 𝓓 β (≪-to-⊑ 𝓓 ∘ ⌜ ≺-≃-≪ ⌝)

 to-Idl : ⟨ 𝓓 ⟩ → Idl
 to-Idl x = (Bₓ , Bₓ-is-lowerset , Bₓ-is-directed-set)
  where
   Bₓ : 𝓟 B
   Bₓ = ↡ᴮ-subset x
   Bₓ-is-lowerset : is-lowerset Bₓ
   Bₓ-is-lowerset = ↡ᴮ-lowerset-criterion _≺_ x
                     (λ b c b-below-c → ≪-to-⊑ 𝓓 (⌜ ≺-≃-≪ ⌝ b-below-c))
   Bₓ-is-semidirected-set : is-semidirected-set Bₓ
   Bₓ-is-semidirected-set = ↡ᴮ-semidirected-set-criterion _≺_ x
                             (λ b c → ⌜ ≺-≃-≪ ⌝⁻¹)
   Bₓ-is-directed-set : is-directed-set Bₓ
   Bₓ-is-directed-set = (↡ᴮ-subset-is-inhabited x , Bₓ-is-semidirected-set)

 from-Idl : Idl → ⟨ 𝓓 ⟩
 from-Idl I = Idl-mediating-map I

 -- TODO: Rename
 Idl-iso₁ : from-Idl ∘ to-Idl ∼ id
 Idl-iso₁ x = ↡ᴮ-∐-retract x (Idl-mediating-directed (to-Idl x))

 -- TODO: Rename
 Idl-iso₂ : to-Idl ∘ from-Idl ∼ id
 Idl-iso₂ 𝕀@(I , I-is-ideal) =
  to-subtype-≡ (λ J → being-ideal-is-prop J) (∐-↡ᴮ-retract I claim₁ claim₂)
   where
    claim₁ : (b c : B) → β b ⊑⟨ 𝓓 ⟩ β c → c ∈ I → b ∈ I
    claim₁ b c b-below-c c-in-I = ∥∥-rec (∈-is-prop I b) h (roundedness 𝕀 c-in-I)
     where
      h : (Σ c' ꞉ B , c' ∈ I × (c ≺ c')) → b ∈ I
      h (c' , c'-in-I , c-way-below-c') =
       ideals-are-lowersets I I-is-ideal b c' l c'-in-I
        where
         l : b ≺ c'
         l = (⌜ ≪ᴮₛ-≃-≪ᴮ ⌝⁻¹
               (⊑-≪-to-≪ 𝓓 b-below-c (⌜ ≪ᴮₛ-≃-≪ᴮ ⌝ c-way-below-c')))
    claim₂ : (b : B) → b ∈ I → ∃ c ꞉ B , c ∈ I × β b ≪⟨ 𝓓 ⟩ β c
    claim₂ b b-in-I = ∥∥-functor h (roundedness 𝕀 b-in-I)
     where
      h : (Σ c ꞉ B , c ∈ I × b ≺ c)
        → (Σ c ꞉ B , c ∈ I × β b ≪⟨ 𝓓 ⟩ β c)
      h (c , c-in-I , b-below-c) = (c , c-in-I , ⌜ ≺-≃-≪ ⌝ b-below-c)

 to-Idl-is-continuous : is-continuous 𝓓 Idl-DCPO to-Idl
 to-Idl-is-continuous I α δ =
  Idl-sups-from-powerset (to-Idl ∘ α) (to-Idl (∐ 𝓓 δ)) (↡ᴮ-is-continuous δ)

 from-Idl-is-continuous : is-continuous Idl-DCPO 𝓓 from-Idl
 from-Idl-is-continuous = Idl-mediating-map-is-continuous

 Idl-≃ : 𝓓 ≃ᵈᶜᵖᵒ Idl-DCPO
 Idl-≃ = (to-Idl , from-Idl , Idl-iso₁ , Idl-iso₂ ,
          to-Idl-is-continuous , from-Idl-is-continuous)

\end{code}

𝓓 ≃ Idl (B , ⊑ᴮ) where B is a small compact basis for 𝓓

\begin{code}

module Idl-algebraic' -- TODO: Rename
        (𝓓 : DCPO {𝓤} {𝓣})
        {B : 𝓥 ̇  }
        (β : B → ⟨ 𝓓 ⟩)
        (β-is-small-compact-basis : is-small-compact-basis 𝓓 β)
       where

 open is-small-compact-basis β-is-small-compact-basis
 open Idl-algebraic 𝓓 β (compact-basis-is-basis 𝓓 β β-is-small-compact-basis)

 open import UF-Retracts

 Idl-≃ : 𝓓 ≃ᵈᶜᵖᵒ Idl-DCPO
 Idl-≃ = (to-Idl , from-Idl , retract-condition Idl-retract , γ ,
          to-Idl-is-continuous , from-Idl-is-continuous)
  where
   -- This is where we use --experimental-lossy-unification
   γ : (I : ⟨ Idl-DCPO ⟩) → to-Idl (from-Idl I) ≡ I
   γ I = antisymmetry Idl-DCPO (to-Idl (from-Idl I)) I ⦅1⦆ ⦅2⦆
    where
     ⦅1⦆ : to-Idl (from-Idl I) ⊑⟨ Idl-DCPO ⟩ I
     ⦅1⦆ = ∐-↡ᴮ-deflation (carrier I) claim
      where
       claim : (b c : B) → β b ⊑⟨ 𝓓 ⟩ β c → c ∈ᵢ I → b ∈ᵢ I
       claim b c b-below-c c-in-I =
        ideals-are-lowersets (carrier I) (ideality I) b c
         (⌜ ⊑ᴮ-≃-⊑ ⌝⁻¹ b-below-c) c-in-I
     ⦅2⦆ : I ⊑⟨ Idl-DCPO ⟩ to-Idl (from-Idl I)
     ⦅2⦆ = ∐-↡ᴮ-inflation (carrier I) claim
      where
       claim : (b : B) → b ∈ᵢ I → ∃ c ꞉ B , c ∈ᵢ I × (β b ≪⟨ 𝓓 ⟩ β c)
       claim b b-in-I = ∥∥-functor h (roundedness I b-in-I)
        where
         h : (Σ c ꞉ B , c ∈ᵢ I × b ⊑ᴮ c)
           → (Σ c ꞉ B , c ∈ᵢ I × (β b ≪⟨ 𝓓 ⟩ β c))
         h (c , c-in-I , b-below-c) = (c , c-in-I , lem)
          where
           lem : β b ≪⟨ 𝓓 ⟩ β c
           lem = ≪-⊑-to-≪ 𝓓 (basis-is-compact b) (⌜ ⊑ᴮ-≃-⊑ ⌝ b-below-c)

\end{code}
