Martin Escardo and Tom de Jong, August 2024

Moved from the file InjectiveTypes.CounterExamples on 12 September 2024.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.PropTrunc

module Apartness.Properties
        (pt : propositional-truncations-exist)
       where

open import MLTT.Spartan
open import Apartness.Definition
open import UF.ClassicalLogic
open import UF.FunExt
open import UF.Size
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

open Apartness pt
open PropositionalTruncation pt

\end{code}

We define an apartness relation to be nontrivial if it tells two points apart.

\begin{code}

has-two-points-apart : {X : 𝓤 ̇ } → Apartness X 𝓥 → 𝓥 ⊔ 𝓤 ̇
has-two-points-apart {𝓤} {𝓥} {X} (_♯_ , α) = Σ (x , y) ꞉ X × X , (x ♯ y)

Nontrivial-Apartness : 𝓤 ̇ → (𝓥 : Universe) → 𝓥 ⁺ ⊔ 𝓤 ̇
Nontrivial-Apartness X 𝓥 = Σ a ꞉ Apartness X 𝓥 , has-two-points-apart a

\end{code}

Assuming weak excluded middle, every type with two distinct points can be
equipped with a nontrivial apartness relation.

\begin{code}

WEM-gives-that-type-with-two-distinct-points-has-nontrivial-apartness
 : funext 𝓤 𝓤₀
 → {X : 𝓤 ̇ }
 → has-two-distinct-points X
 → typal-WEM 𝓤
 → Nontrivial-Apartness X 𝓤
WEM-gives-that-type-with-two-distinct-points-has-nontrivial-apartness
 {𝓤} fe {X} htdp wem = γ
 where
  s : (x y z : X) → x ≠ y → (x ≠ z) + (y ≠ z)
  s x y z d =
   Cases (wem (x ≠ z))
    (λ (a : ¬ (x ≠ z))  → inr (λ {refl → a d}))
    (λ (b : ¬¬ (x ≠ z)) → inl (three-negations-imply-one b))

  c : is-cotransitive _≠_
  c x y z d = ∣ s x y z d ∣

  γ : Nontrivial-Apartness X 𝓤
  γ = (_≠_ ,
      ((λ x y → negations-are-props fe) ,
       ≠-is-irrefl ,
       (λ x y → ≠-sym) , c)) ,
      htdp

WEM-gives-that-type-with-two-distinct-points-has-nontrivial-apartness⁺
 : funext 𝓤 𝓤₀
 → {X : 𝓤 ⁺ ̇ }
 → is-locally-small X
 → has-two-distinct-points X
 → typal-WEM 𝓤
 → Nontrivial-Apartness X 𝓤
WEM-gives-that-type-with-two-distinct-points-has-nontrivial-apartness⁺
 {𝓤} fe {X} ls ((x₀ , x₁) , d) wem = γ
 where
  _♯_ : X → X → 𝓤 ̇
  x ♯ y = x ≠⟦ ls ⟧ y

  s : (x y z : X) → x ♯ y → (x ♯ z) + (y ♯ z)
  s x y z a = Cases (wem (x ♯ z)) (inr ∘ f) (inl ∘ g)
   where
    f : ¬ (x ♯ z) → y ♯ z
    f = contrapositive
         (λ (e : y ＝⟦ ls ⟧ z) → transport (x ♯_) (＝⟦ ls ⟧-gives-＝ e) a)

    g : ¬¬ (x ♯ z) → x ♯ z
    g = three-negations-imply-one

  c : is-cotransitive _♯_
  c x y z d = ∣ s x y z d ∣

  γ : Nontrivial-Apartness X 𝓤
  γ = (_♯_ ,
       (λ x y → negations-are-props fe) ,
       (λ x → ≠⟦ ls ⟧-irrefl) ,
       (λ x y → ≠⟦ ls ⟧-sym) ,
       c) ,
      (x₀ , x₁) , ≠-gives-≠⟦ ls ⟧ d

\end{code}

In particular, weak excluded middle yields a nontrivial apartness relation on
any universe.

\begin{code}

WEM-gives-non-trivial-apartness-on-universe
 : funext (𝓤 ⁺) 𝓤₀
 → typal-WEM (𝓤 ⁺)
 → Nontrivial-Apartness (𝓤 ̇ ) (𝓤 ⁺)
WEM-gives-non-trivial-apartness-on-universe fe =
 WEM-gives-that-type-with-two-distinct-points-has-nontrivial-apartness
  fe
  universe-has-two-distinct-points

\end{code}

Further properties of apartness relations can be found in the following file
InjectiveTypes.CounterExamples. In particular, it is shown that the universe
can't have any nontrivial apartness unless weak excluded middle holds.

Added 31 January 2025 by Tom de Jong and Martin Escardo.

\begin{code}

EM-gives-tight-apartness-is-≠ : DNE 𝓥
                              → (X : 𝓤 ̇  )
                              → ((_♯_ , _ , _) : Tight-Apartness X 𝓥)
                              → ((x y : X) → x ♯ y ↔ x ≠ y)
EM-gives-tight-apartness-is-≠ dne X (_♯_ , ♯-is-apartness , ♯-is-tight) x y = III
 where
  I : x ♯ y → x ≠ y
  I = not-equal-if-apart _♯_ ♯-is-apartness
  II : x ≠ y → x ♯ y
  II ν = dne (x ♯ y)
             (apartness-is-prop-valued _♯_ ♯-is-apartness x y)
             (contrapositive (♯-is-tight x y) ν)
  III : x ♯ y ↔ x ≠ y
  III = I , II

\end{code}
