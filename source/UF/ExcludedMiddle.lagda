Martin Escardo.

Excluded middle related things. Notice that this file doesn't
postulate excluded middle. It only defines what the principle of
excluded middle is.

In the Curry-Howard interpretation, excluded middle say that every
type has an inhabitant or os empty. In univalent foundations, where
one works with propositions as subsingletons, excluded middle is the
principle that every subsingleton type is inhabited or empty.

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

module UF.ExcludedMiddle where

open import MLTT.Spartan

open import UF.Base
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Equiv
open import UF.Embeddings
open import UF.PropTrunc
open import UF.FunExt
open import UF.UniverseEmbedding

\end{code}

Excluded middle (EM) is not provable or disprovable. However, we do
have that there is no truth value other than false (⊥) or true (⊤),
which we refer to as the density of the decidable truth values.

\begin{code}

EM : ∀ 𝓤 → 𝓤 ⁺ ̇
EM 𝓤 = (P : 𝓤 ̇ ) → is-prop P → P + ¬ P

excluded-middle = EM

lower-EM : ∀ 𝓥 → EM (𝓤 ⊔ 𝓥) → EM 𝓤
lower-EM 𝓥 em P P-is-prop = f d
 where
  d : Lift 𝓥 P + ¬ Lift 𝓥 P
  d = em (Lift 𝓥 P) (equiv-to-prop (Lift-is-universe-embedding 𝓥 P) P-is-prop)

  f : Lift 𝓥 P + ¬ Lift 𝓥 P → P + ¬ P
  f (inl p) = inl (lower p)
  f (inr ν) = inr (λ p → ν (lift 𝓥 p))

Excluded-Middle : 𝓤ω
Excluded-Middle = ∀ {𝓤} → EM 𝓤

EM-is-prop : FunExt → is-prop (EM 𝓤)
EM-is-prop {𝓤} fe = Π₂-is-prop
                     (λ {𝓤} {𝓥} → fe 𝓤 𝓥)
                     (λ _ → decidability-of-prop-is-prop (fe 𝓤 𝓤₀))

LEM : ∀ 𝓤 → 𝓤 ⁺ ̇
LEM 𝓤 = (p : Ω 𝓤) → p holds + ¬ (p holds)

EM-gives-LEM : EM 𝓤 → LEM 𝓤
EM-gives-LEM em p = em (p holds) (holds-is-prop p)

LEM-gives-EM : LEM 𝓤 → EM 𝓤
LEM-gives-EM lem P i = lem (P , i)

WEM : ∀ 𝓤 → 𝓤 ⁺ ̇
WEM 𝓤 = (P : 𝓤 ̇ ) → is-prop P → ¬ P + ¬¬ P

WEM-is-prop : FunExt → is-prop (WEM 𝓤)
WEM-is-prop {𝓤} fe = Π₂-is-prop (λ {𝓤} {𝓥} → fe 𝓤 𝓥)
                      (λ _ _ → decidability-of-prop-is-prop (fe 𝓤 𝓤₀)
                                (negations-are-props (fe 𝓤 𝓤₀)))

\end{code}

Double negation elimination is equivalent to excluded middle.

\begin{code}

DNE : ∀ 𝓤 → 𝓤 ⁺ ̇
DNE 𝓤 = (P : 𝓤 ̇ ) → is-prop P → ¬¬ P → P

EM-gives-DNE : EM 𝓤 → DNE 𝓤
EM-gives-DNE em P i φ = cases id (λ u → 𝟘-elim (φ u)) (em P i)

double-negation-elim : EM 𝓤 → DNE 𝓤
double-negation-elim = EM-gives-DNE

fake-¬¬-EM : {X : 𝓤 ̇ } → ¬¬ (X + ¬ X)
fake-¬¬-EM u = u (inr (λ p → u (inl p)))

DNE-gives-EM : funext 𝓤 𝓤₀ → DNE 𝓤 → EM 𝓤
DNE-gives-EM fe dne P isp = dne (P + ¬ P)
                             (decidability-of-prop-is-prop fe isp)
                             fake-¬¬-EM

De-Morgan : ∀ 𝓤 → 𝓤 ⁺ ̇
De-Morgan 𝓤 = (P Q : 𝓤 ̇ )
           → is-prop P
           → is-prop Q
           → ¬ (P × Q) → ¬ P + ¬ Q

EM-gives-De-Morgan : EM 𝓤
                   → De-Morgan 𝓤
EM-gives-De-Morgan em A B i j n = Cases (em A i)
                                   (λ a → Cases (em B j)
                                           (λ b → 𝟘-elim (n (a , b)))
                                           inr)
                                   inl

\end{code}

But already weak excluded middle gives De Morgan:

\begin{code}

WEM-gives-De-Morgan : WEM 𝓤 → De-Morgan 𝓤
WEM-gives-De-Morgan wem A B i j =
 λ (n : ¬ (A × B)) →
 Cases (wem A i)
  inl
  (λ (ϕ : ¬¬ A)
        → Cases (wem B j)
           inr
           (λ (γ : ¬¬ B) → 𝟘-elim (ϕ (λ (a : A) → γ (λ (b : B) → n (a , b))))))

De-Morgan-gives-WEM : funext 𝓤 𝓤₀ → De-Morgan 𝓤 → WEM 𝓤
De-Morgan-gives-WEM fe d P i = d P (¬ P) i (negations-are-props fe) (λ (p , ν) → ν p)

fe-and-em-give-propositional-truncations : FunExt
                                         → Excluded-Middle
                                         → propositional-truncations-exist
fe-and-em-give-propositional-truncations fe em =
 record {
  ∥_∥          = λ X → ¬¬ X ;
  ∥∥-is-prop   = Π-is-prop (fe _ _) (λ _ → 𝟘-is-prop) ;
  ∣_∣         = λ x u → u x ;
  ∥∥-rec       = λ i u φ → EM-gives-DNE em _ i (¬¬-functor u φ)
  }

module _ (pt : propositional-truncations-exist) where

 open PropositionalTruncation pt

 truncated-De-Morgan : ∀ 𝓤 → 𝓤 ⁺ ̇
 truncated-De-Morgan 𝓤 = (P Q : 𝓤 ̇ )
                      → is-prop P
                      → is-prop Q
                      → ¬ (P × Q) → ¬ P ∨ ¬ Q

 De-Morgan-gives-truncated-De-Morgan : De-Morgan 𝓤 → truncated-De-Morgan 𝓤
 De-Morgan-gives-truncated-De-Morgan d P Q i j ν = ∣ d P Q i j ν ∣

\end{code}

See https://ncatlab.org/nlab/show/De%20Morgan%20laws for the
following, which is attributed to this author.

\begin{code}

 truncated-De-Morgan-gives-WEM : FunExt → truncated-De-Morgan 𝓤 → WEM 𝓤
 truncated-De-Morgan-gives-WEM {𝓤} fe t P i = III
  where
   I : ¬ (P × ¬ P) → ¬ P ∨ ¬ (¬ P)
   I = t P (¬ P) i (negations-are-props (fe 𝓤 𝓤₀))

   II : ¬ P ∨ ¬¬ P
   II = I (λ (p , ν) → ν p)

   III : ¬ P + ¬¬ P
   III = exit-∥∥
          (decidability-of-prop-is-prop (fe 𝓤 𝓤₀)
          (negations-are-props (fe 𝓤 𝓤₀)))
          II

 truncated-De-Morgan-gives-De-Morgan : FunExt → truncated-De-Morgan 𝓤 → De-Morgan 𝓤
 truncated-De-Morgan-gives-De-Morgan fe t P Q i j ν =
  WEM-gives-De-Morgan (truncated-De-Morgan-gives-WEM fe t) P Q i j ν

\end{code}

The above shows that weak excluded middle, De Morgan amd truncated De
Morgan are logically equivalent.

\begin{code}


 double-negation-is-truncation-gives-DNE : ((X : 𝓤 ̇ ) → ¬¬ X → ∥ X ∥) → DNE 𝓤
 double-negation-is-truncation-gives-DNE f P i u = ∥∥-rec i id (f P u)

 non-empty-is-inhabited : EM 𝓤 → {X : 𝓤 ̇ } → ¬¬ X → ∥ X ∥
 non-empty-is-inhabited em {X} φ =
  cases
   (λ s → s)
   (λ u → 𝟘-elim (φ (contrapositive ∣_∣ u))) (em ∥ X ∥ ∥∥-is-prop)

 ∃-not+Π : EM (𝓤 ⊔ 𝓥)
         → {X : 𝓤 ̇ }
         → (A : X → 𝓥 ̇ )
         → ((x : X) → is-prop (A x))
         → (∃ x ꞉ X , ¬ (A x)) + (Π x ꞉ X , A x)
 ∃-not+Π {𝓤} {𝓥} em {X} A is-prop-valued =
  Cases (em (∃ x ꞉ X , ¬ (A x)) ∃-is-prop)
   inl
   (λ (u : ¬ (∃ x ꞉ X , ¬ (A x)))
         → inr (λ (x : X) → EM-gives-DNE
                              (lower-EM (𝓤 ⊔ 𝓥) em)
                              (A x)
                              (is-prop-valued x)
                              (λ (v : ¬ A x) → u ∣ (x , v) ∣)))

 ∃+Π-not : EM (𝓤 ⊔ 𝓥)
         → {X : 𝓤 ̇ }
         → (A : X → 𝓥 ̇ )
         → ((x : X) → is-prop (A x))
         → (∃ x ꞉ X , A x) + (Π x ꞉ X , ¬ (A x))
 ∃+Π-not {𝓤} {𝓥} em {X} A is-prop-valued =
  Cases (em (∃ x ꞉ X , A x) ∃-is-prop)
   inl
   (λ (u : ¬ (∃ x ꞉ X , A x))
         → inr (λ (x : X) (v : A x) → u ∣ x , v ∣))

 not-Π-implies-∃-not : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
                     → EM (𝓤 ⊔ 𝓥)
                     → ((x : X) → is-prop (A x))
                     → ¬ ((x : X) → A x)
                     → ∃ x ꞉ X , ¬ A x
 not-Π-implies-∃-not {𝓤} {𝓥} {X} {A} em i f =
  Cases (em E ∃-is-prop)
   id
   (λ (u : ¬ E)
         → 𝟘-elim (f (λ (x : X) → EM-gives-DNE
                                    (lower-EM 𝓤 em)
                                    (A x)
                                    (i x)
                                    (λ (v : ¬ A x) → u ∣ x , v ∣))))
  where
   E = ∃ x ꞉ X , ¬ A x

\end{code}

Added by Tom de Jong in August 2021.

\begin{code}

 not-Π-not-implies-∃ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
                     → EM (𝓤 ⊔ 𝓥)
                     → ¬ ((x : X) → ¬ A x)
                     → ∃ x ꞉ X , A x
 not-Π-not-implies-∃ {𝓤} {𝓥} {X} {A} em f = EM-gives-DNE em (∃ A) ∥∥-is-prop γ
   where
    γ : ¬¬ (∃ A)
    γ g = f (λ x a → g ∣ x , a ∣)

\end{code}

Added by Martin Escardo 26th April 2022.

\begin{code}

Global-Choice' : ∀ 𝓤 → 𝓤 ⁺ ̇
Global-Choice' 𝓤 = (X : 𝓤 ̇ ) → is-nonempty X → X

Global-Choice : ∀ 𝓤 → 𝓤 ⁺ ̇
Global-Choice 𝓤 = (X : 𝓤 ̇ ) → X + is-empty X

Global-Choice-gives-Global-Choice' : Global-Choice 𝓤 → Global-Choice' 𝓤
Global-Choice-gives-Global-Choice' gc X φ = cases id (λ u → 𝟘-elim (φ u)) (gc X)

Global-Choice'-gives-Global-Choice : Global-Choice' 𝓤 → Global-Choice 𝓤
Global-Choice'-gives-Global-Choice gc X = gc (X + ¬ X)
                                             (λ u → u (inr (λ p → u (inl p))))
\end{code}

Global choice contradicts univalence.

TODO. Show that weak excluded middle is equivalent to De Morgan's Law.
https://ncatlab.org/nlab/show/De+Morgan+duality
