Martin Escardo, 3 February 2021.

We consider one special kind of Church-Rosser property motivated by
our applications of this module to the contruction of free groups
without higher-inductive types other than propositional truncation.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan

module Relations.ChurchRosser
         {𝓤 𝓥 : Universe}
         {X : 𝓤 ̇ }
         (_▷_ : X → X → 𝓤 ̇ )
       where

open import Relations.SRTclosure
open import UF.PropTrunc
open import UF.Subsingletons

infix 1 _◁▷_
infix 1 _◁▷[_]_
infix 1 _▷⋆_
infix 1 _▷[_]_
infix 1 _∿_

_◁▷_ : X → X → 𝓤 ̇
_◁▷_ = s-closure _▷_

_◁▷[_]_ : X → ℕ → X → 𝓤 ̇
x ◁▷[ n ] y = iteration _◁▷_ n x y

_∿_ : X → X → 𝓤 ̇
_∿_ = srt-closure _▷_

_▷⋆_ : X → X → 𝓤 ̇
_▷⋆_ = rt-closure _▷_

_▷[_]_ : X → ℕ → X → 𝓤 ̇
x ▷[ n ] y = iteration _▷_ n x y

to-∿ : (x y : X)
     → (Σ z ꞉ X , (x ▷⋆ z) × (y ▷⋆ z))
     → x ∿ y
to-∿ x y (z , r , s) = srt-transitive _▷_ x z y
                        (rt-gives-srt _▷_ x z r)
                        (srt-symmetric _▷_ y z (rt-gives-srt _▷_ y z s))

module _ (Church-Rosser : (x y₀ y₁ : X)
                        → x ▷ y₀
                        → x ▷ y₁
                        → (y₀ ＝ y₁) + (Σ y ꞉ X , (y₀ ▷ y) × (y₁ ▷ y)))
       where

 Church-Rosser⋆ : (x y₀ y₁ : X)
                → x ▷⋆ y₀
                → x ▷  y₁
                → Σ y ꞉ X , (y₀ ▷⋆ y) × (y₁ ▷⋆ y)
 Church-Rosser⋆ x y₀ y₁ (m , i) b = f m x y₀ y₁ i b
  where
   f : (m : ℕ) (x y₀ y₁ : X)
     → x ▷[ m ] y₀
     → x ▷  y₁
     → Σ y ꞉ X , (y₀ ▷⋆ y) × (y₁ ▷⋆ y)
   f 0        x x  y₁ refl        e = y₁ , rt-extension _▷_ x y₁ e , rt-reflexive _▷_ y₁
   f (succ m) x y₀ y₁ (t , d , i) e = γ c
    where
     c : (y₁ ＝ t) + (Σ y ꞉ X , (y₁ ▷ y) × (t ▷ y))
     c = Church-Rosser x y₁ t e d

     γ : type-of c → Σ u ꞉ X , (y₀ ▷⋆ u) × (y₁ ▷⋆ u)
     γ (inl refl) = y₀ , rt-reflexive _▷_ y₀ , m , i
     γ (inr (y , a , b)) = δ IH
      where
       IH : Σ u ꞉ X , (y₀ ▷⋆ u) × (y ▷⋆ u)
       IH = f m t y₀ y i b

       δ : type-of IH → Σ u ꞉ X , (y₀ ▷⋆ u) × (y₁ ▷⋆ u)
       δ (u , b , n , j) = u , b , succ n , y , a , j

 from-∿ : (x y : X) → x ∿ y → Σ z ꞉ X , (x ▷⋆ z) × (y ▷⋆ z)
 from-∿ x y (m , e) = f m x y e
  where
   f : (m : ℕ) (x y : X) → x ◁▷[ m ] y → Σ z ꞉ X , (x ▷⋆ z) × (y ▷⋆ z)
   f 0        x x refl        = x , rt-reflexive _▷_ x , rt-reflexive _▷_ x
   f (succ m) x y (z , d , i) = γ IH d
    where
     IH : Σ t ꞉ X , (z ▷⋆ t) × (y ▷⋆ t)
     IH = f m z y i

     γ : type-of IH → x ◁▷ z → Σ u ꞉ X , (x ▷⋆ u) × (y ▷⋆ u)
     γ (t , (n , i) , a) (inl c) = t , (succ n , z , c , i) , a
     γ (t , (n , i) , a) (inr c) = δ σ
      where
       σ : Σ u ꞉ X , (t ▷⋆ u) × (x ▷⋆ u)
       σ = Church-Rosser⋆ z t x (n , i) c

       δ : type-of σ → Σ u ꞉ X , (x ▷⋆ u) × (y ▷⋆ u)
       δ (u , d , e) = u , e , rt-transitive _▷_ y t u a d

\end{code}
