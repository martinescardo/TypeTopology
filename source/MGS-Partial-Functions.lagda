Martin Escardo 1st May 2020.

This is ported from the Midlands Graduate School 2019 lecture notes

 https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html
 https://github.com/martinescardo/HoTT-UF-Agda-Lecture-Notes

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module MGS-Partial-Functions where

open import MGS-More-FunExt-Consequences public

Πₚ : {X : 𝓤 ̇ } → (X → 𝓥 ̇ ) → 𝓤 ⊔ (𝓥 ⁺) ̇
Πₚ {𝓤} {𝓥} {X} A = Σ R ꞉ ((x : X) → A x → 𝓥 ̇ )
                       , ((x : X) → is-subsingleton (Σ a ꞉ A x , R x a))

_⇀_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ (𝓥 ⁺) ̇
X ⇀ Y = Πₚ (λ (_ : X) → Y)

is-defined : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } → Πₚ A → X → 𝓥 ̇
is-defined (R , σ) x = Σ a ꞉ _ , R x a

being-defined-is-subsingleton : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } (f : Πₚ A) (x : X)
                              → is-subsingleton (is-defined f x)

being-defined-is-subsingleton (R , σ) x = σ x

_[_,_] :  {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } (f : Πₚ A) (x : X) → is-defined f x → A x
(R , s) [ x , (a , r)] = a

_≡ₖ_ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } → Πₚ A → Πₚ A → 𝓤 ⊔ 𝓥 ̇
f ≡ₖ g = ∀ x → (is-defined f x ⇔ is-defined g x)
             × ((i : is-defined f x) (j : is-defined g x) → f [ x , i ] ≡ g [ x , j ])

module μ-operator (fe : dfunext 𝓤₀ 𝓤₀) where

 open basic-arithmetic-and-order

 being-minimal-root-is-subsingleton : (f : ℕ → ℕ) (m : ℕ)
                                    → is-subsingleton (is-minimal-root f m)

 being-minimal-root-is-subsingleton f m = ×-is-subsingleton
                                           (ℕ-is-set (f m) 0)
                                           (Π-is-subsingleton fe
                                              (λ _ → Π-is-subsingleton fe
                                              (λ _ → Π-is-subsingleton fe
                                              (λ _ → 𝟘-is-subsingleton))))

 minimal-root-is-subsingleton : (f : ℕ → ℕ)
                              → is-subsingleton (minimal-root f)

 minimal-root-is-subsingleton f (m , p , φ) (m' , p' , φ') =
   to-subtype-≡
    (being-minimal-root-is-subsingleton f)
    (at-most-one-minimal-root f m m' (p , φ) (p' , φ'))

 μ : (ℕ → ℕ) ⇀ ℕ
 μ = is-minimal-root , minimal-root-is-subsingleton

 μ-property₀ : (f : ℕ → ℕ) → (Σ n ꞉ ℕ , f n ≡ 0) → is-defined μ f
 μ-property₀ = root-gives-minimal-root

 μ-property₁ : (f : ℕ → ℕ) (i : is-defined μ f)
             → (f (μ [ f , i ]) ≡ 0)
             × ((n : ℕ) → n < μ [ f , i ] → f n ≢ 0)

 μ-property₁ f = pr₂

is-total : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } → Πₚ A → 𝓤 ⊔ 𝓥 ̇
is-total f = ∀ x → is-defined f x

infix  30 _[_,_]

\end{code}
