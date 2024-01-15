Martin Escardo, January 2018, May 2020

Based on joint work with Cory Knapp.
http://www.cs.bham.ac.uk/~mhe/papers/partial-elements-and-recursion.pdf

Convention:

  * 𝓣 is the universe where the dominant truth values live.

  * 𝓚 is the universe where the knowledge they are dominant lives.

  * A dominance is given by a function d : 𝓣 ̇ → 𝓚 ̇ subject to suitable
    properties.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.Equiv
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.FunExt

module Dominance.Definition where

module _ {𝓣 𝓚 : Universe} where

 D2 : (𝓣 ̇ → 𝓚 ̇ ) → 𝓣 ⁺ ⊔ 𝓚 ̇
 D2 d = (X : 𝓣 ̇ ) → is-prop (d X)

 D3 : (𝓣 ̇ → 𝓚 ̇ ) → 𝓣 ⁺ ⊔ 𝓚 ̇
 D3 d = (X : 𝓣 ̇ ) → d X → is-prop X

 D4 : (𝓣 ̇ → 𝓚 ̇ ) → 𝓚 ̇
 D4 d = d 𝟙

 D5 : (𝓣 ̇ → 𝓚 ̇ ) → 𝓣 ⁺ ⊔ 𝓚 ̇
 D5 d = (P : 𝓣 ̇ ) (Q : P → 𝓣 ̇ ) → d P → ((p : P) → d (Q p)) → d (Σ Q)

\end{code}

condition D5 is more conceptual and often what we need in practice,
and condition D5' below is easier to check:

\begin{code}

 D5' : (𝓣 ̇ → 𝓚 ̇ ) → 𝓣 ⁺ ⊔ 𝓚 ̇
 D5' d = (P Q' : 𝓣 ̇ ) → d P → (P → d Q') → d (P × Q')

 D5-gives-D5' : (d : 𝓣 ̇ → 𝓚 ̇ ) → D5 d → D5' d
 D5-gives-D5' d d5 P Q' i j = d5 P (λ p → Q') i j

 D3-and-D5'-give-D5 : propext 𝓣
                    → (d : 𝓣 ̇ → 𝓚 ̇ )
                    → D3 d
                    → D5' d
                    → D5 d
 D3-and-D5'-give-D5 pe d d3 d5' P Q i j = w
  where
   Q' : 𝓣 ̇
   Q' = Σ Q

   k : is-prop P
   k = d3 P i

   l : (p : P) → is-prop (Q p)
   l p = d3 (Q p) (j p)

   m : is-prop Q'
   m = Σ-is-prop k l

   n : (p : P) → Q p ＝ Q'
   n p = pe (l p) m (λ q        → (p , q))
                    (λ (p' , q) → transport Q (k p' p) q)

   j' : P → d Q'
   j' p = transport d (n p) (j p)

   u : d (P × Q')
   u = d5' P Q' i j'

   v : P × Q' ＝ Σ Q
   v = pe (×-is-prop k m) m (λ (p , p' , q) → (p' , q))
                            (λ (p' , q)     → (p' , p' , q))
   w : d (Σ Q)
   w = transport d v u

 is-dominance : (𝓣 ̇ → 𝓚 ̇ ) → 𝓣 ⁺ ⊔ 𝓚 ̇
 is-dominance d = D2 d × D3 d × D4 d × D5 d

 Dominance : (𝓣 ⊔ 𝓚)⁺ ̇
 Dominance = Σ d ꞉ (𝓣 ̇ → 𝓚 ̇ ) , is-dominance d

 is-dominant : (D : Dominance) → 𝓣 ̇ → 𝓚 ̇
 is-dominant (d , _) = d

 being-dominant-is-prop : (D : Dominance) → (X : 𝓣 ̇ ) → is-prop (is-dominant D X)
 being-dominant-is-prop (_ , (isp , _)) = isp

 dominant-types-are-props : (D : Dominance) → (X : 𝓣 ̇ ) → is-dominant D X → is-prop X
 dominant-types-are-props (_ , (_ , (disp , _))) = disp

 dominant-prop : Dominance → 𝓣 ⁺ ⊔ 𝓚 ̇
 dominant-prop D = Σ P ꞉ 𝓣 ̇ , is-dominant D P


 𝟙-is-dominant : (D : Dominance) → is-dominant D 𝟙
 𝟙-is-dominant (_ , (_ , (_ , (oisd , _)))) = oisd

 dominant-closed-under-Σ : (D : Dominance) → (P : 𝓣 ̇ ) (Q : P → 𝓣 ̇ )
                         → is-dominant D P
                         → ((p : P)
                         → is-dominant D (Q p))
                         → is-dominant D (Σ Q)
 dominant-closed-under-Σ (_ , (_ , (_ , (_ , cus)))) = cus

 being-dominance-is-prop : Fun-Ext → (d : 𝓣 ̇ → 𝓚 ̇ ) → is-prop (is-dominance d)
 being-dominance-is-prop fe d = prop-criterion lemma
  where
   lemma : is-dominance d → is-prop (is-dominance d)
   lemma i = Σ-is-prop
               (Π-is-prop fe (λ _ → being-prop-is-prop fe))
                (λ _ → ×₃-is-prop
                         (Π₂-is-prop fe (λ _ _ → being-prop-is-prop fe))
                         (being-dominant-is-prop (d , i) 𝟙)
                         (Π₄-is-prop fe λ _ Q _ _ → being-dominant-is-prop (d , i) (Σ Q)))

\end{code}

TODO. Define a dominance to be a function Ω → Ω and prove the
equivalence with the above definition. But keep the above definition.
