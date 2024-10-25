Martin Escardo, January 2018, May 2020, July 2024

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

 being-dominant-is-prop : (D : Dominance) (X : 𝓣 ̇ )
                        → is-prop (is-dominant D X)
 being-dominant-is-prop (_ , (isp , _)) = isp

 dominant-types-are-props : (D : Dominance) (X : 𝓣 ̇ )
                          → is-dominant D X → is-prop X
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
                        (Π₄-is-prop fe λ _ Q _ _ → being-dominant-is-prop
                                                    (d , i)
                                                    (Σ Q)))

\end{code}

Added 1st July 2024.

We now define, alternatively, a dominance to be a function Ω → Ω and
prove the equivalence with the above definition, assuming function
extensionality and propositional extensionality. The equivalence
requires the universe 𝓚 to be above the universe 𝓣, which in practice
means that we replace 𝓚 by 𝓚 ⊔ 𝓣.

\begin{code}

module _ (fe : Fun-Ext) where

 open import UF.SubtypeClassifier
 open import UF.Logic
 open Universal fe
 open Implication fe

 module _ {𝓣 𝓚 : Universe} where

  d4 : (Ω 𝓣  → Ω 𝓚) → Ω 𝓚
  d4 d = d ⊤

  d5 : (Ω 𝓣  → Ω 𝓚) → Ω (𝓣 ⁺ ⊔ 𝓚)
  d5 d = Ɐ p ꞉ Ω 𝓣
       , Ɐ q ꞉ (p holds → Ω 𝓣)
       , d p
       ⇒ (Ɐ h ꞉ p holds , d (q h))
       ⇒ d (ΣΩ h ꞉ p , q h)

  is-dominance' : (Ω 𝓣 → Ω 𝓚) → 𝓣 ⁺ ⊔ 𝓚 ̇
  is-dominance' d = d4 d holds × d5 d holds

  Dominance' : (𝓣 ⊔ 𝓚)⁺ ̇
  Dominance' = Σ d ꞉ (Ω 𝓣 → Ω 𝓚) , is-dominance' d

  being-dominance'-is-prop : (d : Ω 𝓣 → Ω 𝓚) → is-prop (is-dominance' d)
  being-dominance'-is-prop d = ×-is-prop
                                (holds-is-prop (d4 d))
                                (holds-is-prop (d5 d))

 Dominance'-gives-Dominance : {𝓣 𝓚 : Universe}
                            → Dominance' {𝓣} {𝓚}
                            → Dominance {𝓣} {𝓣 ⊔ 𝓚}
 Dominance'-gives-Dominance {𝓣} {𝓚} (d , IV , V) = (d' , II , III , IV' , V')
  where
   d' : 𝓣 ̇ → 𝓣 ⊔ 𝓚 ̇
   d' X = Σ i ꞉ is-prop X , d (X , i) holds

   II : D2 d'
   II X = Σ-is-prop
           (being-prop-is-prop fe)
           (λ i → holds-is-prop (d (X , i)))

   III : D3 d'
   III X (i , h) = i

   IV' : d' 𝟙
   IV' = 𝟙-is-prop , IV

   V' : D5 d'
   V' P Q (i , h) a = Σ-is-prop i (λ p → pr₁ (a p)) ,
                      V (P , i) (λ p → Q p , pr₁ (a p)) h (λ p → pr₂ (a p))

 Dominance-gives-Dominance' : {𝓣 𝓚 : Universe}
                            → Dominance {𝓣} {𝓚}
                            → Dominance' {𝓣} {𝓚}
 Dominance-gives-Dominance' {𝓣} {𝓚} (d' , II , III , IV' , V') = (d , IV' , V)
  where
   d : Ω 𝓣 → Ω 𝓚
   d p = d' (p holds) , II (p holds)

   V : d5 d holds
   V p q = V' (p holds) (λ h → q h holds )

 definitions-equivalence : {𝓣 𝓚 : Universe}
                         → Prop-Ext
                         → Dominance' {𝓣} {𝓣 ⊔ 𝓚} ≃ Dominance {𝓣} {𝓣 ⊔ 𝓚}
 definitions-equivalence {𝓣} {𝓚} pe = qinveq f (g , η , ε)
  where
   f = Dominance'-gives-Dominance
   g = Dominance-gives-Dominance'

   η : g ∘ f ∼ id {_} {Dominance' {𝓣} {𝓣 ⊔ 𝓚}}
   η (d , IV , V) =
    to-subtype-＝
     being-dominance'-is-prop
     (dfunext fe (λ p → to-Ω-＝ fe (lemma p)))
      where
       lemma : (p : Ω 𝓣)
             → (Σ j ꞉ is-prop (p holds) , d (p holds , j) holds) ＝ d p holds
       lemma p@(P , i) = pe
                          (Σ-is-prop
                            (being-prop-is-prop fe)
                            (λ j → holds-is-prop (d (P , j))))
                          (holds-is-prop (d p))
                          (λ (j , h) → transport
                                        (λ - → d (P , -) holds)
                                        (being-prop-is-prop fe j i)
                                        h)
                          (λ h → i , h)

   ε : f ∘ g ∼ id {_} {Dominance {𝓣} {𝓣 ⊔ 𝓚}}
   ε (d' , II , III , IV' , V') =
    to-subtype-＝
     (being-dominance-is-prop fe)
     (dfunext fe lemma)
    where
     lemma : (P : 𝓣 ̇ ) → is-prop P × d' P ＝ d' P
     lemma P = pe
                (×-is-prop (being-prop-is-prop fe) (II P))
                (II P)
                (λ (i , h) → h)
                (λ δ → III P δ , δ)
\end{code}
