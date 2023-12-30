Martin Escardo, December 2020

A notion of disconnectedness. This is different from homotopy
disconnectedness in the sense of the HoTT book. It is based on the
topological, rather than homotopical, interpretation of types.

A discussion of such models is in

  M.H. Escardo and Chuangjie Xu. A constructive manifestation of the
  Kleene-Kreisel continuous functionals. Annals of Pure and Applied
  Logic, 2016.

and

  M.H. Escardo and Thomas Streicher. Annals of Pure and Applied Logic,
  2016.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module TypeTopology.DisconnectedTypes where

open import MLTT.Spartan
open import MLTT.Two-Properties
open import Naturals.Properties
open import UF.DiscreteAndSeparated
open import UF.Equiv
open import UF.Hedberg
open import UF.Retracts

\end{code}

The following notions of disconnectedness are data rather than
property.

\begin{code}

is-disconnected₀ : 𝓤 ̇ → 𝓤 ̇
is-disconnected₀ X = retract 𝟚 of X

is-disconnected₁ : 𝓤 ̇ → 𝓤 ̇
is-disconnected₁ X = Σ p ꞉ (X → 𝟚) , fiber p ₀ × fiber p ₁

is-disconnected₂ : 𝓤 ̇ → 𝓤 ⁺ ̇
is-disconnected₂ {𝓤} X = Σ X₀ ꞉ 𝓤 ̇ , Σ X₁ ꞉ 𝓤 ̇ , X₀ × X₁ × (X ≃ X₀ + X₁)

is-disconnected₃ : 𝓤 ̇ → 𝓤 ⁺ ̇
is-disconnected₃ {𝓤} X = Σ X₀ ꞉ 𝓤 ̇ , Σ X₁ ꞉ 𝓤 ̇ , X₀ × X₁ × (retract (X₀ + X₁) of X)

is-disconnected-eq : (X : 𝓤 ̇ )
                → (is-disconnected₀ X → is-disconnected₁ X)
                × (is-disconnected₁ X → is-disconnected₂ X)
                × (is-disconnected₂ X → is-disconnected₃ X)
                × (is-disconnected₃ X → is-disconnected₀ X)

is-disconnected-eq {𝓤} X = (f , g , h , k)
 where
  f : (Σ p ꞉ (X → 𝟚) , Σ s ꞉ (𝟚 → X) , p ∘ s ∼ id)
    → Σ p ꞉ (X → 𝟚) , (Σ x ꞉ X , p x ＝ ₀) × (Σ x ꞉ X , p x ＝ ₁)
  f (p , s , e) = p , (s ₀ , e ₀) , (s ₁ , e ₁)

  g : (Σ p ꞉ (X → 𝟚) , (Σ x ꞉ X , p x ＝ ₀) × (Σ x ꞉ X , p x ＝ ₁))
    → Σ X₀ ꞉ 𝓤 ̇ , Σ X₁ ꞉ 𝓤 ̇ , X₀ × X₁ × (X ≃ X₀ + X₁)
  g (p , (x₀ , e₀) , (x₁ , e₁)) = (Σ x ꞉ X , p x ＝ ₀) ,
                                  (Σ x ꞉ X , p x ＝ ₁) ,
                                  (x₀ , e₀) ,
                                  (x₁ , e₁) ,
                                  qinveq ϕ (γ , γϕ , ϕγ)
   where
    ϕ : X → (Σ x ꞉ X , p x ＝ ₀) + (Σ x ꞉ X , p x ＝ ₁)
    ϕ x = 𝟚-equality-cases
           (λ (r₀ : p x ＝ ₀) → inl (x , r₀))
           (λ (r₁ : p x ＝ ₁) → inr (x , r₁))

    γ : (Σ x ꞉ X , p x ＝ ₀) + (Σ x ꞉ X , p x ＝ ₁) → X
    γ (inl (x , r₀)) = x
    γ (inr (x , r₁)) = x

    ϕγ : ϕ ∘ γ ∼ id
    ϕγ (inl (x , r₀)) = 𝟚-equality-cases₀ r₀
    ϕγ (inr (x , r₁)) = 𝟚-equality-cases₁ r₁

    γϕ : γ ∘ ϕ ∼ id
    γϕ x = 𝟚-equality-cases
           (λ (r₀ : p x ＝ ₀) → ap γ (𝟚-equality-cases₀ r₀))
           (λ (r₁ : p x ＝ ₁) → ap γ (𝟚-equality-cases₁ r₁))

  h : (Σ X₀ ꞉ 𝓤 ̇ , Σ X₁ ꞉ 𝓤 ̇ , X₀ × X₁ × (X ≃ X₀ + X₁))
    → (Σ X₀ ꞉ 𝓤 ̇ , Σ X₁ ꞉ 𝓤 ̇ , X₀ × X₁ × (retract (X₀ + X₁) of X))
  h (X₀ , X₁ , x₀ , x₁ , (γ , (ϕ , γϕ) , _)) = (X₀ , X₁ , x₀ , x₁ , (γ , ϕ , γϕ))

  k : (Σ X₀ ꞉ 𝓤 ̇ , Σ X₁ ꞉ 𝓤 ̇ , X₀ × X₁ × (retract (X₀ + X₁) of X))
    → Σ p ꞉ (X → 𝟚) , Σ s ꞉ (𝟚 → X) , p ∘ s ∼ id
  k (X₀ , X₁ , x₀ , x₁ , (γ , ϕ , γϕ)) = p , s , ps
   where
    p : X → 𝟚
    p x = Cases (γ x) (λ _ → ₀) (λ _ → ₁)

    s : 𝟚 → X
    s ₀ = ϕ (inl x₀)
    s ₁ = ϕ (inr x₁)

    ps : p ∘ s ∼ id
    ps ₀ = ap (cases (λ _ → ₀) (λ _ → ₁)) (γϕ (inl x₀))
    ps ₁ = ap (cases (λ _ → ₀) (λ _ → ₁)) (γϕ (inr x₁))

\end{code}

The following is our official notion of disconnectedness (logically
equivalent to the other ones):

\begin{code}

is-disconnected : 𝓤 ̇ → 𝓤 ̇
is-disconnected = is-disconnected₀

\end{code}

Some examples:

\begin{code}

𝟚-is-disconnected : is-disconnected 𝟚
𝟚-is-disconnected = identity-retraction

ℕ-is-disconnected : is-disconnected ℕ
ℕ-is-disconnected = (r , s , rs)
 where
  r : ℕ → 𝟚
  r zero     = ₀
  r (succ n) = ₁

  s : 𝟚 → ℕ
  s ₀ = zero
  s ₁ = succ zero

  rs : (n : 𝟚) → r (s n) ＝ n
  rs ₀ = refl
  rs ₁ = refl

types-with-isolated-point-different-from-another-point-are-disconnected :

    {Y : 𝓥 ̇ }
  → (Σ y₀ ꞉ Y , Σ y₁ ꞉ Y , (y₀ ≠ y₁) × is-isolated y₀ )
  → is-disconnected Y

types-with-isolated-point-different-from-another-point-are-disconnected (y₀ , y₁ , ne , i) =
  𝟚-retract-of-non-trivial-type-with-isolated-point ne i

discrete-types-with-two-different-points-are-disconnected :

    {Y : 𝓥 ̇ }
  → (Σ y₀ ꞉ Y , Σ y₁ ꞉ Y , y₀ ≠ y₁)
  → is-discrete Y
  → is-disconnected Y

discrete-types-with-two-different-points-are-disconnected (y₀ , y₁ , ne) d =
  types-with-isolated-point-different-from-another-point-are-disconnected
   (y₀ , y₁ , ne , d y₀)


ℕ-is-disconnected' : is-disconnected ℕ
ℕ-is-disconnected' = discrete-types-with-two-different-points-are-disconnected
                     (0 , 1 , succ-no-fp 0)
                     ℕ-is-discrete

retract-is-disconnected : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                        → retract X of Y
                        → is-disconnected X
                        → is-disconnected Y
retract-is-disconnected = retracts-compose

\end{code}

TODO. Define totally disconnected. Then maybe for compact types the
notions of total disconnectedness and total separatedness agree.

The negation of disconnectedness can be expressed positively in
various equivalent ways.

\begin{code}

open import TypeTopology.TotallySeparated
open import UF.Base
open import UF.FunExt
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

is-connected₀ : 𝓤 ̇ → 𝓤 ̇
is-connected₀ X = (f : X → 𝟚) → wconstant f

is-connected₁ : 𝓤 ̇ → 𝓤 ̇
is-connected₁ X = (x y : X) → x ＝₂ y

is-connected₂ : 𝓤 ̇ → 𝓤 ̇
is-connected₂ X = ¬ is-disconnected X


connected₀-types-are-connected₁ : {X : 𝓤 ̇ } → is-connected₀ X → is-connected₁ X
connected₀-types-are-connected₁ i x y p = i p x y

connected₁-types-are-connected₀ : {X : 𝓤 ̇ } → is-connected₁ X → is-connected₀ X
connected₁-types-are-connected₀ ϕ f x y = ϕ x y f

connected₀-types-are-connected₂ : {X : 𝓤 ̇ } → is-connected₀ X → is-connected₂ X
connected₀-types-are-connected₂ c (r , s , rs) = n (c r)
 where
  n : ¬ wconstant r
  n κ = zero-is-not-one (₀       ＝⟨ (rs ₀)⁻¹ ⟩
                         r (s ₀) ＝⟨ κ (s ₀) (s ₁) ⟩
                         r (s ₁) ＝⟨ rs ₁ ⟩
                         ₁       ∎)

disconnected-types-are-not-connected : {X : 𝓤 ̇ }
                                     → is-disconnected X
                                     → ¬ is-connected₀ X
disconnected-types-are-not-connected c d = connected₀-types-are-connected₂ d c

connected₂-types-are-is-connected₀ : {X : 𝓤 ̇ }
                                   → is-connected₂ X
                                   → is-connected₀ X
connected₂-types-are-is-connected₀ {𝓤} {X} n f x y =
 𝟚-is-¬¬-separated (f x) (f y) ϕ
 where
  ϕ : ¬¬ (f x ＝ f y)
  ϕ u = n (f , s , fs)
   where
    s : 𝟚 → X
    s ₀ = 𝟚-equality-cases
           (λ (p₀ : f x ＝ ₀) → x)
           (λ (p₁ : f x ＝ ₁) → y)
    s ₁ = 𝟚-equality-cases
           (λ (p₀ : f x ＝ ₀) → y)
           (λ (p₁ : f x ＝ ₁) → x)

    a : f x ＝ ₁ → f y ＝ ₀
    a p = different-from-₁-equal-₀ (λ (q : f y ＝ ₁) → u (p ∙ (q ⁻¹)))

    b : f x ＝ ₀ → f y ＝ ₁
    b p = different-from-₀-equal-₁ (λ (q : f y ＝ ₀) → u (p ∙ q ⁻¹))

    fs : f ∘ s ∼ id
    fs ₀ = 𝟚-equality-cases
           (λ (p₀ : f x ＝ ₀) → f (s ₀) ＝⟨ ap f (𝟚-equality-cases₀ p₀) ⟩
                               f x      ＝⟨ p₀ ⟩
                               ₀        ∎)
           (λ (p₁ : f x ＝ ₁) → f (s ₀) ＝⟨ ap f (𝟚-equality-cases₁ p₁) ⟩
                               f y      ＝⟨ a p₁ ⟩
                               ₀        ∎)
    fs ₁ = 𝟚-equality-cases
           (λ (p₀ : f x ＝ ₀) → f (s ₁) ＝⟨ ap f (𝟚-equality-cases₀ p₀) ⟩
                               f y      ＝⟨ b p₀ ⟩
                               ₁        ∎)
           (λ (p₁ : f x ＝ ₁) → f (s ₁) ＝⟨ ap f (𝟚-equality-cases₁ p₁) ⟩
                               f x      ＝⟨ p₁ ⟩
                               ₁        ∎)

is-connected : 𝓤 ̇ → 𝓤 ̇
is-connected = is-connected₀

being-connected-is-prop : {X : 𝓤 ̇ } → Fun-Ext → is-prop (is-connected X)
being-connected-is-prop fe = Π₃-is-prop fe (λ f x y → 𝟚-is-set)

\end{code}
