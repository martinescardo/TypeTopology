Martin Escardo, 15 August 2014.

There is some repetition with the module UF. Moreover, this module is
incomplete (it has what we've needed so far).

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UF hiding (⊤)

module SubtypeClassifier (fe : ∀ {U V} → FunExt U V) where

open import SpartanMLTT

U = U₀ -- For the moment.

Ω = Σ \(P : U ̇) → isProp P

⊤ : Ω
⊤ = (𝟙 , 𝟙-isProp)

prop-univalence : U ′ ̇
prop-univalence = {P Q : U ̇} → (P → Q) → (Q → P) → P ≡ Q

equal-⊤-is-true : (P : U ̇) (hp : isProp P)
               → (P , hp) ≡ ⊤ → P
equal-⊤-is-true P hp r = f *
 where
  s : 𝟙 ≡ P
  s = (ap pr₁ r)⁻¹
  f : 𝟙 → P
  f = transport id s

true-is-equal-⊤ : prop-univalence → (P : U ̇) (hp : isProp P)
                → P → (P , hp) ≡ ⊤
true-is-equal-⊤ hpu P hp x = 
 to-Σ-≡ P 𝟙 hp 𝟙-isProp 
     (hpu unique-to-𝟙 (λ _ → x)) 
     (isProp-isProp fe (transport isProp (hpu unique-to-𝟙 (λ _ → x)) hp)
                  𝟙-isProp)

Ω-univalence : U ′ ̇
Ω-univalence = {p q : Ω} 
             → (p ≡ ⊤ → q ≡ ⊤) → (q ≡ ⊤ → p ≡ ⊤) → p ≡ q

Ω-from-prop-univalence : prop-univalence → Ω-univalence
Ω-from-prop-univalence hpu {(P , hpP)} {(Q , hpQ)} f g = 
 to-Σ-≡ P Q hpP hpQ (hpu I II) (isProp-isProp fe (transport _ (hpu I II) hpP) hpQ)
 where
  I : P → Q
  I x = equal-⊤-is-true Q hpQ (f (true-is-equal-⊤ hpu P hpP x))
  II : Q → P
  II y = equal-⊤-is-true P hpP (g (true-is-equal-⊤ hpu Q hpQ y))
  
\end{code}

Should add more stuff, such as the proof that Ω classifies (univalent) embeddings.
