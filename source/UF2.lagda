Martin Escardo, based on files

\begin{code}

module UF2 where

open import UF
open import DecidableAndDetachable

decidable-is-collapsible : ∀ {U} {X : U ̇} → decidable X → collapsible X
decidable-is-collapsible (inl x) = inhabited-is-collapsible x
decidable-is-collapsible (inr u) = isEmpty-is-collapsible u

open import DiscreteAndSeparated

discrete-is-path-collapsible : ∀ {U} {X : U ̇} → discrete X → path-collapsible X
discrete-is-path-collapsible d = decidable-is-collapsible (d _ _)

discrete-isSet : ∀ {U} {X : U ̇} → discrete X → isSet X
discrete-isSet d = path-collapsible-isSet(discrete-is-path-collapsible d)

dd-sum : ∀ {U} {X : U ̇} → {Y : X → U ̇}
       → discrete X → ((x : X) → discrete(Y x)) → discrete(Σ Y)
dd-sum {U} {X} {Y} d e (x , y) (x' , y') = g (d x x')
  where
   g : decidable(x ≡ x') → decidable(x , y ≡ x' , y')
   g (inl p) = f (e x' (transport Y p y) y')
     where
       f : decidable(transport Y p y ≡ y') → decidable((x , y) ≡ (x' , y'))
       f (inl q) = inl (to-Σ-≡ x x' y y' p q)
       f (inr ψ) = inr c
         where
           c : x , y ≡ x' , y' → 𝟘
           c r = ψ q
            where
              p' : x ≡ x'
              p' = ap pr₁ r
              q' : transport Y p' y ≡ y'
              q' = from-Σ-≡ (x , y) (x' , y') r
              s : p ≡ p'
              s = discrete-isSet d p p'
              q : transport Y p y ≡ y'
              q = ap (λ p → transport Y p y) s ∙ q'
   g (inr φ) = inr (λ q → φ (ap pr₁ q))

open import Two

𝟚-isSet : isSet 𝟚
𝟚-isSet = discrete-isSet 𝟚-discrete

open import Naturals

ℕ-isSet : isSet ℕ
ℕ-isSet = discrete-isSet ℕ-discrete

nonempty : ∀ {U} → U ̇ → U ̇
nonempty X = isEmpty(isEmpty X)

stable : ∀ {U} → U ̇ → U ̇
stable X = nonempty X → X
 
decidable-is-stable : ∀ {U} {X : U ̇} → decidable X → stable X
decidable-is-stable (inl x) φ = x
decidable-is-stable (inr u) φ = unique-from-𝟘(φ u)

stable-is-collapsible : ∀ {U} → FunExt U U₀ → {X : U ̇} → stable X → collapsible X 
stable-is-collapsible {U} fe {X} s = (f , g)
 where
  f : X → X
  f x = s(λ u → u x)
  claim₀ : (x y : X) → (u : isEmpty X) → u x ≡ u y
  claim₀ x y u = unique-from-𝟘(u x)
  claim₁ : (x y : X) → (λ u → u x) ≡ (λ u → u y)
  claim₁ x y = funext fe (claim₀ x y) 
  g : (x y : X) → f x ≡ f y
  g x y = ap s (claim₁ x y)

separated-is-path-collapsible : ∀ {U} → FunExt U U₀ → {X : U ̇} → separated X → path-collapsible X
separated-is-path-collapsible fe s = stable-is-collapsible fe (s _ _)

separated-isSet : ∀ {U} → FunExt U U₀ → {X : U ̇} → separated X → isSet X
separated-isSet fe s = path-collapsible-isSet (separated-is-path-collapsible fe s) 

isProp-separated : ∀ {U} → FunExt U U → FunExt U U₀ → {X : U ̇} → isProp(separated X)
isProp-separated fe fe₀ {X} = iisProp-isProp f
 where
  f : separated X → isProp(separated X)
  f s = isProp-exponential-ideal fe
          (λ _ → isProp-exponential-ideal fe
                    (λ _ → isProp-exponential-ideal fe
                              (λ _ → separated-isSet fe₀ s)))


\end{code}

