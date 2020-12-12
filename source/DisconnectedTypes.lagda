Martin Escardo, December 2020

A notion of disconnectedness. This is different from homotopy
disconnectedness in the sense of the HoTT book.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module DisconnectedTypes where

open import SpartanMLTT
open import Two-Properties
open import NaturalNumbers-Properties
open import DiscreteAndSeparated
open import UF-Retracts
open import UF-Equiv

disconnected₀ : 𝓤 ̇ → 𝓤 ̇
disconnected₀ X = retract 𝟚 of X

disconnected₁ : 𝓤 ̇ → 𝓤 ̇
disconnected₁ X = Σ p ꞉ (X → 𝟚) , fiber p ₀ × fiber p ₁

disconnected₂ : 𝓤 ̇ → 𝓤 ⁺ ̇
disconnected₂ {𝓤} X = Σ X₀ ꞉ 𝓤 ̇ , Σ X₁ ꞉ 𝓤 ̇ , X₀ × X₁ × (X ≃ X₀ + X₁)

disconnected₃ : 𝓤 ̇ → 𝓤 ⁺ ̇
disconnected₃ {𝓤} X = Σ X₀ ꞉ 𝓤 ̇ , Σ X₁ ꞉ 𝓤 ̇ , X₀ × X₁ × (retract (X₀ + X₁) of X)

disconnected-eq : (X : 𝓤 ̇ )
                → (disconnected₀ X → disconnected₁ X)
                × (disconnected₁ X → disconnected₂ X)
                × (disconnected₂ X → disconnected₃ X)
                × (disconnected₃ X → disconnected₀ X)

disconnected-eq {𝓤} X = (f , g , h , k)
 where
  f : (Σ p ꞉ (X → 𝟚) , Σ s ꞉ (𝟚 → X) , p ∘ s ∼ id)
    → Σ p ꞉ (X → 𝟚) , (Σ x ꞉ X , p x ≡ ₀) × (Σ x ꞉ X , p x ≡ ₁)
  f (p , s , e) = p , (s ₀ , e ₀) , (s ₁ , e ₁)

  g : (Σ p ꞉ (X → 𝟚) , (Σ x ꞉ X , p x ≡ ₀) × (Σ x ꞉ X , p x ≡ ₁))
    → Σ X₀ ꞉ 𝓤 ̇ , Σ X₁ ꞉ 𝓤 ̇ , X₀ × X₁ × (X ≃ X₀ + X₁)
  g (p , (x₀ , e₀) , (x₁ , e₁)) = (Σ x ꞉ X , p x ≡ ₀) ,
                                  (Σ x ꞉ X , p x ≡ ₁) ,
                                  (x₀ , e₀) ,
                                  (x₁ , e₁) ,
                                  qinveq ϕ (γ , γϕ , ϕγ)
   where
    ϕ : X → (Σ x ꞉ X , p x ≡ ₀) + (Σ x ꞉ X , p x ≡ ₁)
    ϕ x = 𝟚-equality-cases
           (λ (r₀ : p x ≡ ₀) → inl (x , r₀))
           (λ (r₁ : p x ≡ ₁) → inr (x , r₁))

    γ : (Σ x ꞉ X , p x ≡ ₀) + (Σ x ꞉ X , p x ≡ ₁) → X
    γ (inl (x , r₀)) = x
    γ (inr (x , r₁)) = x

    ϕγ : ϕ ∘ γ ∼ id
    ϕγ (inl (x , r₀)) = 𝟚-equality-cases₀ r₀
    ϕγ (inr (x , r₁)) = 𝟚-equality-cases₁ r₁

    γϕ : γ ∘ ϕ ∼ id
    γϕ x = 𝟚-equality-cases
           (λ (r₀ : p x ≡ ₀) → ap γ (𝟚-equality-cases₀ r₀))
           (λ (r₁ : p x ≡ ₁) → ap γ (𝟚-equality-cases₁ r₁))

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

disconnected : 𝓤 ̇ → 𝓤 ̇
disconnected = disconnected₀

\end{code}

Some examples:

\begin{code}

𝟚-disconnected : disconnected 𝟚
𝟚-disconnected = identity-retraction

ℕ-disconnected : disconnected ℕ
ℕ-disconnected = (r , s , rs)
 where
  r : ℕ → 𝟚
  r zero     = ₀
  r (succ n) = ₁

  s : 𝟚 → ℕ
  s ₀ = zero
  s ₁ = succ zero

  rs : (n : 𝟚) → r (s n) ≡ n
  rs ₀ = refl
  rs ₁ = refl

non-trivial-with-isolated-point-gives-disconnected : {Y : 𝓥 ̇ }
                                                   → (Σ y₀ ꞉ Y , Σ y₁ ꞉ Y , (y₀ ≢ y₁) × is-isolated y₀ )
                                                   → disconnected Y
non-trivial-with-isolated-point-gives-disconnected (y₀ , y₁ , ne , i) =
  𝟚-retract-of-non-trivial-type-with-isolated-point ne i

non-trivial-discrete-gives-disconnected : {Y : 𝓥 ̇ }
                                        → (Σ y₀ ꞉ Y , Σ y₁ ꞉ Y , y₀ ≢ y₁)
                                        → is-discrete Y
                                        → disconnected Y
non-trivial-discrete-gives-disconnected (y₀ , y₁ , ne) d =
  non-trivial-with-isolated-point-gives-disconnected (y₀ , y₁ , ne , d y₀)


ℕ-disconnected' : disconnected ℕ
ℕ-disconnected' = non-trivial-discrete-gives-disconnected (0 , 1 , succ-no-fp 0) ℕ-is-discrete

disconnected-retract : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                     → retract X of Y
                     → disconnected X
                     → disconnected Y
disconnected-retract = retracts-compose

\end{code}

TODO. Define totally disconnected. Then maybe for compact types the
notions of total disconnectedness and total separatedness agree.

\begin{code}

open import TotallySeparated
open import UF-Base
open import UF-FunExt
open import UF-Subsingletons
open import UF-Subsingletons-FunExt
open import UF-Miscelanea

is-connected₀ : 𝓤 ̇ → 𝓤 ̇
is-connected₀ X = (f : X → 𝟚) → wconstant f

is-connected₁ : 𝓤 ̇ → 𝓤 ̇
is-connected₁ X = (x y : X) → x ≡₂ y

is-connected₂ : 𝓤 ̇ → 𝓤 ̇
is-connected₂ X = ¬ disconnected X


is-connected₀-gives-is-connected₁ : {X : 𝓤 ̇ } → is-connected₀ X → is-connected₁ X
is-connected₀-gives-is-connected₁ i x y p = i p x y

is-connected₁-gives-is-connected₀ : {X : 𝓤 ̇ } → is-connected₁ X → is-connected₀ X
is-connected₁-gives-is-connected₀ ϕ f x y = ϕ x y f

is-connected₀-gives-is-connected₂ : {X : 𝓤 ̇ } → is-connected₀ X → is-connected₂ X
is-connected₀-gives-is-connected₂ c (r , s , rs) = n (c r)
 where
  n : ¬ wconstant r
  n κ = zero-is-not-one (₀       ≡⟨ (rs ₀)⁻¹ ⟩
                         r (s ₀) ≡⟨ κ (s ₀) (s ₁) ⟩
                         r (s ₁) ≡⟨ rs ₁ ⟩
                         ₁       ∎)

disconnected-types-are-not-connected : {X : 𝓤 ̇ } → disconnected X → ¬ is-connected₀ X
disconnected-types-are-not-connected c d = is-connected₀-gives-is-connected₂ d c

is-connected₂-gives-is-connected₀ : {X : 𝓤 ̇ } → is-connected₂ X → is-connected₀ X
is-connected₂-gives-is-connected₀ {𝓤} {X} n f x y = 𝟚-is-separated (f x) (f y) ϕ
 where
  ϕ : ¬¬ (f x ≡ f y)
  ϕ u = n (f , s , fs)
   where
    s : 𝟚 → X
    s ₀ = 𝟚-equality-cases
           (λ (p₀ : f x ≡ ₀) → x)
           (λ (p₁ : f x ≡ ₁) → y)
    s ₁ = 𝟚-equality-cases
           (λ (p₀ : f x ≡ ₀) → y)
           (λ (p₁ : f x ≡ ₁) → x)

    a : f x ≡ ₁ → f y ≡ ₀
    a p = different-from-₁-equal-₀ (λ (q : f y ≡ ₁) → u (p ∙ (q ⁻¹)))

    b : f x ≡ ₀ → f y ≡ ₁
    b p = different-from-₀-equal-₁ (λ (q : f y ≡ ₀) → u (p ∙ q ⁻¹))

    fs : f ∘ s ∼ id
    fs ₀ = 𝟚-equality-cases
           (λ (p₀ : f x ≡ ₀) → f (s ₀) ≡⟨ ap f (𝟚-equality-cases₀ p₀) ⟩
                               f x     ≡⟨ p₀ ⟩
                               ₀       ∎)
           (λ (p₁ : f x ≡ ₁) → f (s ₀) ≡⟨ ap f (𝟚-equality-cases₁ p₁) ⟩
                               f y     ≡⟨ a p₁ ⟩
                               ₀       ∎)
    fs ₁ = 𝟚-equality-cases
           (λ (p₀ : f x ≡ ₀) → f (s ₁) ≡⟨ ap f (𝟚-equality-cases₀ p₀) ⟩
                               f y     ≡⟨ b p₀ ⟩
                               ₁       ∎)
           (λ (p₁ : f x ≡ ₁) → f (s ₁) ≡⟨ ap f (𝟚-equality-cases₁ p₁) ⟩
                               f x     ≡⟨ p₁ ⟩
                               ₁       ∎)


is-connected : 𝓤 ̇ → 𝓤 ̇
is-connected = is-connected₀

being-connected-is-prop : {X : 𝓤 ̇ } → Fun-Ext → is-prop (is-connected X)
being-connected-is-prop {𝓤} {X} fe = Π₃-is-prop fe (λ f x y → 𝟚-is-set)

\end{code}

Tentative definition of total disconnecteness mimicking the classical
topological case:

\begin{code}

connected-component : {X : 𝓤 ̇ } → X → 𝓤 ̇
connected-component {𝓤} {X} x = Σ y ꞉ X , x ≡₂ y

connected-component-pointed : {X : 𝓤 ̇ } (x : X) → connected-component x
connected-component-pointed {𝓤} {X} x = (x , λ p → refl)

\end{code}

We should have the following, but at the moment I don't see how to prove it:

\begin{code}

{-

connected-component-is-connected : {X : 𝓤 ̇ } (x : X) → is-connected (connected-component x)
connected-component-is-connected {𝓤} {X} x f (y , a) (z , b) = γ
 where
  c : y ≡₂ z
  c p = (a p)⁻¹ ∙ b p

  γ : f (y , a) ≡ f (z , b)
  γ = {!!}
-}

\end{code}

Our tentative definition is the following:

\begin{code}

is-totally-disconnected : 𝓤 ̇ → 𝓤 ̇
is-totally-disconnected X = (x : X) → is-prop (connected-component x)

totally-separated-types-are-totally-disconnected : {X : 𝓤 ̇ } → funext 𝓤 𝓤 → funext 𝓤 𝓤₀
                                                 → is-totally-separated X
                                                 → is-totally-disconnected X
totally-separated-types-are-totally-disconnected {𝓤} {X} fe fe₀ ts x (y , a) (z , b) = γ
 where
  c : y ≡₂ z
  c p = (a p)⁻¹ ∙ b p

  q : y ≡ z
  q = ts c

  γ : (y , a) ≡ (z , b)
  γ = to-subtype-≡ (≡₂-is-prop-valued fe fe₀ X x) q

\end{code}

In the classical topological case, the following theorem requires the
assumption that X be compact. So perhaps we haven't got our definition
of total disconnectedness right (the potential culprit is our
definition of connected component).

\begin{code}

totally-disconnected-types-are-totally-separated : {X : 𝓤 ̇ }
                                                         → is-totally-disconnected X
                                                         → is-totally-separated X
totally-disconnected-types-are-totally-separated {𝓤} {X} td {x} {y} ϕ = γ
 where
  a b : connected-component x
  a = x , λ p → refl
  b = y , ϕ

  e : a ≡ b
  e = td x a b

  γ : x ≡ y
  γ = ap pr₁ e

\end{code}
