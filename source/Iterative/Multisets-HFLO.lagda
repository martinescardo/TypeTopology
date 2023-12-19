Martin Escardo and Tom de Jong, 9th December 2023.

We discuss "hereditarily finitely linearly ordered iterative
multisets". Notice that this is data, rather then property.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (_^_)
open import UF.Sets-Properties
open import UF.Univalence
open import UF.Universes

module Iterative.Multisets-HFLO
        (ua : Univalence)
        (𝓤 : Universe)
       where

open import Iterative.Multisets 𝓤
open import Iterative.Multisets-Addendum ua 𝓤
open import UF.Base
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.Subsingletons
open import UF.UA-FunExt
open import W.Type

private
 𝓤⁺ : Universe
 𝓤⁺ = 𝓤 ⁺

 fe : Fun-Ext
 fe = Univalence-gives-Fun-Ext ua

 fe' : FunExt
 fe' 𝓤 𝓥 = fe {𝓤} {𝓥}

open import Fin.Bishop
open import Fin.Type

hflo-data : 𝕄 → 𝓤 ̇
hflo-data (ssup X φ) = finite-linear-order X
                     × ((x : X) → hflo-data (φ x))

hflo-data-gives-finite-linear-order
 : (M : 𝕄)
 → hflo-data M
 → finite-linear-order (𝕄-root M)
hflo-data-gives-finite-linear-order (ssup x φ) = pr₁

𝕄-subtrees-have-hflo-data
 : (M : 𝕄)
 → hflo-data M
 → (x : 𝕄-root M) → hflo-data (𝕄-forest M x)
𝕄-subtrees-have-hflo-data (ssup x φ) = pr₂

ℍ : 𝓤⁺ ̇
ℍ = Σ M ꞉ 𝕄 , hflo-data M

ℍ-underlying-mset : ℍ → 𝕄
ℍ-underlying-mset = pr₁

hflo-structure : (H : ℍ) → hflo-data (ℍ-underlying-mset H)
hflo-structure = pr₂

\end{code}

Examples. We will use the superscript H to indicate elements of the
type ℍ.

\begin{code}

𝟘ᴹ-hflo-data : hflo-data 𝟘ᴹ
𝟘ᴹ-hflo-data = (0 , f) , (λ (x : 𝟘) → 𝟘-elim x)
 where
  f : 𝟘 {𝓤} ≃ 𝟘 {𝓤₀}
  f = one-𝟘-only

𝟘ᴴ : ℍ
𝟘ᴴ = 𝟘ᴹ , 𝟘ᴹ-hflo-data

open import UF.Equiv-FunExt

𝟘ᴴ-equality : (H : ℍ)
            → is-empty (𝕄-root (ℍ-underlying-mset H))
            → 𝟘ᴴ ＝ H
𝟘ᴴ-equality (ssup X φ , (0 , f) , δ) e =
 to-Σ-＝
  ((to-𝕄-＝
     (eqtoid (ua 𝓤) 𝟘 X (≃-sym (f ● one-𝟘-only)) ,
      dfunext fe (λ (x : 𝟘) → 𝟘-elim x))) ,
    I)
 where
  I : {d : hflo-data (ssup X φ)} → d ＝ (zero , f) , δ
  I {(zero , f') , δ'} =
    to-Σ-＝
     (to-Σ-＝
       (refl ,
        to-subtype-＝
         (being-equiv-is-prop fe')
         (dfunext fe (λ x → 𝟘-elim (⌜ f ⌝ x)))) ,
      dfunext fe (λ x → 𝟘-elim (⌜ f ⌝ x)))
  I {(succ n' , f') , δ'} = 𝟘-elim (e (⌜ f' ⌝⁻¹ 𝟎))
𝟘ᴴ-equality (ssup X φ , (succ n , f) , δ) e = 𝟘-elim (e (⌜ f ⌝⁻¹ 𝟎))

𝟙ᴹ-hflo-data : hflo-data 𝟙ᴹ
𝟙ᴹ-hflo-data = (1 , f) , (λ ⋆ → 𝟘ᴹ-hflo-data)
 where
  f : 𝟙 {𝓤} ≃ 𝟘 {𝓤₀} + 𝟙 {𝓤₀}
  f = 𝟘-lneutral''

𝟙ᴴ : ℍ
𝟙ᴴ = 𝟙ᴹ , 𝟙ᴹ-hflo-data

𝟚ᴹ-hflo-data : hflo-data 𝟚ᴹ
𝟚ᴹ-hflo-data = 𝟙+𝟙-natural-finite-linear-order ,
               dep-cases (λ _ → 𝟘ᴹ-hflo-data) (λ _ → 𝟙ᴹ-hflo-data)

𝟚ᴴ : ℍ
𝟚ᴴ = 𝟚ᴹ , 𝟚ᴹ-hflo-data

open import Fin.ArithmeticViaEquivalence

Σᴹ-hflo-data : {X : 𝓤 ̇ }
               (A : X → 𝕄)
             → finite-linear-order X
             → ((x : X) → hflo-data (A x))
             → hflo-data (Σᴹ A)
Σᴹ-hflo-data {X} A (n , f) A-hflo = (∑ a , h) , δ
 where
  u : (x : X) → Σ m ꞉ ℕ , 𝕄-root (A x) ≃ Fin m
  u x = hflo-data-gives-finite-linear-order (A x) (A-hflo x)

  a : Fin n → ℕ
  a i = pr₁ (u (⌜ f ⌝⁻¹ i))

  b : (i : Fin n) → 𝕄-root (A (⌜ f ⌝⁻¹ i)) ≃ Fin (a i)
  b i = pr₂ (u (⌜ f ⌝⁻¹ i))

  h = (Σ x ꞉ X , 𝕄-root (A x))               ≃⟨ h₀ ⟩
      (Σ i ꞉ Fin n , 𝕄-root (A (⌜ f ⌝⁻¹ i))) ≃⟨ h₁ ⟩
      (Σ i ꞉ Fin n , Fin (a i))              ≃⟨ h₂ ⟩
      Fin (∑ a)                              ■
       where
        h₀ = ≃-sym (Σ-change-of-variable-≃ (λ x → 𝕄-root (A x)) (≃-sym f))
        h₁ = Σ-cong b
        h₂ = ≃-sym (∑-property a)

  δ : ((x , y) : Σ x ꞉ X , 𝕄-root (A x)) → hflo-data (𝕄-forest (A x) y)
  δ (x , y) = 𝕄-subtrees-have-hflo-data (A x) (A-hflo x) y

Πᴹ-hflo-data : {X : 𝓤 ̇ }
               (A : X → 𝕄)
             → finite-linear-order X
             → ((x : X) → hflo-data (A x))
             → hflo-data (Πᴹ A)
Πᴹ-hflo-data {X} A (n , f) A-hflo = (∏ fe a , h) , δ
 where
  u : (x : X) → Σ m ꞉ ℕ , 𝕄-root (A x) ≃ Fin m
  u x = hflo-data-gives-finite-linear-order (A x) (A-hflo x)

  a : Fin n → ℕ
  a i = pr₁ (u (⌜ f ⌝⁻¹ i))

  b : (i : Fin n) → 𝕄-root (A (⌜ f ⌝⁻¹ i)) ≃ Fin (a i)
  b i = pr₂ (u (⌜ f ⌝⁻¹ i))

  h = (Π x ꞉ X , 𝕄-root (A x))               ≃⟨ h₀ ⟩
      (Π i ꞉ Fin n , 𝕄-root (A (⌜ f ⌝⁻¹ i))) ≃⟨ h₁ ⟩
      (Π i ꞉ Fin n , Fin (a i))              ≃⟨ h₂ ⟩
      Fin (∏ fe a)                              ■
       where
        h₀ = ≃-sym (Π-change-of-variable-≃ fe' (λ x → 𝕄-root (A x)) (≃-sym f))
        h₁ = Π-cong fe fe b
        h₂ = ≃-sym (∏-property fe a)

  v : (x : X) (y : 𝕄-root (A x)) → hflo-data (𝕄-forest (A x) y)
  v x = 𝕄-subtrees-have-hflo-data (A x) (A-hflo x)

  δ : (g : Π x ꞉ X , 𝕄-root (A x)) → hflo-data (Σᴹ (λ x → 𝕄-forest (A x) (g x)))
  δ g = Σᴹ-hflo-data (λ x → 𝕄-forest (A x) (g x)) (n , f) (λ x → v x (g x))

+ᴹ-hflo-data : (M N : 𝕄)
             → hflo-data M
             → hflo-data N
             → hflo-data (M +ᴹ N)
+ᴹ-hflo-data M N h k =
 Σᴹ-hflo-data (cases (λ _ → M) (λ _ → N))
  𝟙+𝟙-natural-finite-linear-order
  (dep-cases (λ _ → h) (λ _ → k))

×ᴹ-hflo-data : (M N : 𝕄)
             → hflo-data M
             → hflo-data N
             → hflo-data (M ×ᴹ N)
×ᴹ-hflo-data M N h k =
 Πᴹ-hflo-data (cases (λ _ → M) (λ _ → N))
  𝟙+𝟙-natural-finite-linear-order
  (dep-cases (λ _ → h) (λ _ → k))

×ᴹ'-hflo-data : (M N : 𝕄)
             → hflo-data M
             → hflo-data N
             → hflo-data (M ×ᴹ' N)
×ᴹ'-hflo-data (ssup X φ) (ssup Y γ) ((n , f) , u) ((m , g) , v) = (n ×' m ,
  (X × Y        ≃⟨ ×-cong f g ⟩
  Fin n × Fin m ≃⟨ ≃-sym (Fin×homo n m) ⟩
  Fin (n ×' m)  ■)) ,
  (λ (x , y) → ×ᴹ'-hflo-data (φ x) (γ y) (u x) (v y))

_+ᴴ_ _×ᴴ_ _×ᴴ'_ : ℍ → ℍ → ℍ
(M , h) +ᴴ (N , k) = M +ᴹ N , +ᴹ-hflo-data M N h k
(M , h) ×ᴴ (N , k) = M ×ᴹ N , ×ᴹ-hflo-data M N h k
(M , h) ×ᴴ' (N , k) = M ×ᴹ' N , ×ᴹ'-hflo-data M N h k

\end{code}

TODO. Define Σᴴ and Πᴴ. (Boilerplate.)

We now develop a representation of elements of ℍ for the sake of being
able to exhibit examples explicitly and visually.

\begin{code}

data _^_ (X : 𝓥 ̇ ) : ℕ → 𝓥 ̇ where
 ·   : X ^ 0
 _,_ : {n : ℕ} → X → X ^ n → X ^ (succ n)

data 𝕊 : 𝓤 ̇ where
 [_] : {n : ℕ} → 𝕊 ^ n → 𝕊

to-vector : (n : ℕ) → (Fin n → 𝕊) → 𝕊 ^ n
to-vector 0        f = ·
to-vector (succ n) f = f 𝟎 , to-vector n (f ∘ suc)

to-𝕊-curried : (M : 𝕄) → hflo-data M → 𝕊
to-𝕊-curried (ssup X φ) ((n , f) , δ) =
 [ to-vector n (λ (i : Fin n) → to-𝕊-curried (φ (⌜ f ⌝⁻¹ i)) (δ (⌜ f ⌝⁻¹ i))) ]

to-𝕊 : ℍ → 𝕊
to-𝕊 = uncurry to-𝕊-curried

\end{code}

Examples.

\begin{code}

private
 s = to-𝕊

𝟛ᴴ 𝟛ᴴ' : ℍ
𝟛ᴴ  = 𝟙ᴴ +ᴴ 𝟚ᴴ
𝟛ᴴ' = 𝟚ᴴ +ᴴ 𝟙ᴴ

𝟘ˢ 𝟙ˢ 𝟚ˢ 𝟛ˢ 𝟛ˢ' : 𝕊
𝟘ˢ  = s 𝟘ᴴ
𝟙ˢ  = s 𝟙ᴴ
𝟚ˢ  = s 𝟚ᴴ
𝟛ˢ  = s 𝟛ᴴ
𝟛ˢ' = s 𝟛ᴴ'

examplesˢ
 : ( 𝟘ˢ  ＝ [ · ]                                           )
 × ( 𝟙ˢ  ＝ [ 𝟘ˢ , · ]                                      )
 × ( 𝟚ˢ  ＝ [ 𝟘ˢ , 𝟙ˢ , · ]                                 )
 × ( 𝟛ˢ  ＝ [ 𝟘ˢ , 𝟙ˢ , 𝟘ˢ , · ]                            )
 × ( 𝟛ˢ' ＝ [ 𝟘ˢ , 𝟘ˢ , 𝟙ˢ , · ]                            )
 × ( s (𝟚ᴴ ×ᴴ 𝟚ᴴ) ＝ [ 𝟘ˢ , 𝟙ˢ , 𝟙ˢ , [ 𝟘ˢ , 𝟘ˢ , · ] , · ] )
 × ( s (𝟚ᴴ ×ᴴ' 𝟚ᴴ) ＝ [ 𝟘ˢ , 𝟘ˢ , 𝟘ˢ , 𝟙ˢ , · ]             )
 × ( s (𝟘ᴴ +ᴴ 𝟙ᴴ) ＝ 𝟙ˢ                                     )
 × ( s (𝟙ᴴ +ᴴ 𝟘ᴴ) ＝ 𝟙ˢ                                     )
 × ( s (𝟙ᴴ +ᴴ 𝟙ᴴ) ＝ [ 𝟘ˢ , 𝟘ˢ , · ]                        )
 × ( s (𝟛ᴴ +ᴴ 𝟛ᴴ) ＝ [ 𝟘ˢ , 𝟙ˢ , 𝟘ˢ , 𝟘ˢ , 𝟙ˢ , 𝟘ˢ , · ]    )
 × ( s (𝟛ᴴ ×ᴴ 𝟛ᴴ) ＝ [ 𝟘ˢ , 𝟙ˢ , 𝟘ˢ , 𝟙ˢ ,
                      [ 𝟘ˢ , 𝟘ˢ , · ] ,
                      𝟙ˢ , 𝟘ˢ , 𝟙ˢ , 𝟘ˢ , · ]               )
 × ( s (𝟛ᴴ ×ᴴ' 𝟛ᴴ) ＝ [ 𝟘ˢ , 𝟘ˢ , 𝟘ˢ , 𝟘ˢ ,
                        𝟙ˢ , 𝟘ˢ , 𝟘ˢ , 𝟘ˢ , 𝟘ˢ , · ]        )
 × ( s (𝟛ᴴ' ×ᴴ 𝟛ᴴ') ＝ [ 𝟘ˢ , 𝟘ˢ , 𝟙ˢ , 𝟘ˢ ,
                         𝟘ˢ , 𝟙ˢ , 𝟙ˢ , 𝟙ˢ ,
                         [ 𝟘ˢ , 𝟘ˢ , · ] , · ]              )
examplesˢ = refl , refl , refl , refl , refl , refl , refl ,
            refl , refl , refl , refl , refl , refl , refl

\end{code}
