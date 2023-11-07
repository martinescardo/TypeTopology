Martin Escardo.

Excluded middle related things. Notice that this file doesn't
postulate excluded middle. It only defines what the principle of
excluded middle is.

In the Curry-Howard interpretation, excluded middle say that every
type has an inhabitant or os empty. In univalent foundations, where
one works with propositions as subsingletons, excluded middle is the
principle that every subsingleton type is inhabited or empty.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module UF.ExcludedMiddle where

open import MLTT.Spartan

open import UF.Base
open import UF.Embeddings
open import UF.Equiv
open import UF.FunExt
open import UF.PropTrunc
open import UF.SubtypeClassifier
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
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

all-props-negative-gives-DNE : funext 𝓤 𝓤₀
                            → ((P : 𝓤 ̇ ) → is-prop P → Σ Q ꞉ 𝓤 ̇ , (P ↔ ¬ Q))
                            → DNE 𝓤
all-props-negative-gives-DNE {𝓤} fe ϕ P P-is-prop = I (ϕ P P-is-prop)
 where
  I : (Σ Q ꞉ 𝓤 ̇ , (P ↔ ¬ Q)) → ¬¬ P → P
  I (Q , f , g) ν = g (three-negations-imply-one (double-contrapositive f ν))

all-props-negative-gives-EM : funext 𝓤 𝓤₀
                            → ((P : 𝓤 ̇ ) → is-prop P → Σ Q ꞉ 𝓤 ̇ , (P ↔ ¬ Q))
                            → EM 𝓤
all-props-negative-gives-EM {𝓤} fe ϕ = DNE-gives-EM fe
                                        (all-props-negative-gives-DNE fe ϕ)

fe-and-em-give-propositional-truncations : FunExt
                                         → Excluded-Middle
                                         → propositional-truncations-exist
fe-and-em-give-propositional-truncations fe em =
 record {
  ∥_∥          = λ X → ¬¬ X ;
  ∥∥-is-prop   = Π-is-prop (fe _ _) (λ _ → 𝟘-is-prop) ;
  ∣_∣          = λ x u → u x ;
  ∥∥-rec       = λ i u φ → EM-gives-DNE em _ i (¬¬-functor u φ)
  }

De-Morgan : ∀ 𝓤 → 𝓤 ⁺ ̇
De-Morgan 𝓤 = (P Q : 𝓤 ̇ )
             → is-prop P
             → is-prop Q
             → ¬ (P × Q) → ¬ P + ¬ Q

EM-gives-De-Morgan : EM 𝓤
                   → De-Morgan 𝓤
EM-gives-De-Morgan em A B i j =
 λ (ν : ¬ (A × B)) →
      Cases (em A i)
       (λ (a : A) → Cases (em B j)
                     (λ (b : B) → 𝟘-elim (ν (a , b)))
                     inr)
       inl

\end{code}

But already weak excluded middle gives De Morgan:

\begin{code}

non-contradiction : {X : 𝓤 ̇ } → ¬ (X × ¬ X)
non-contradiction (x , ν) = ν x

WEM-gives-De-Morgan : WEM 𝓤 → De-Morgan 𝓤
WEM-gives-De-Morgan wem A B i j =
 λ (ν : ¬ (A × B)) →
      Cases (wem A i)
       inl
       (λ (ϕ : ¬¬ A)
             → Cases (wem B j)
                inr
                (λ (γ : ¬¬ B) → 𝟘-elim (ϕ (λ (a : A) → γ (λ (b : B) → ν (a , b))))))

De-Morgan-gives-WEM : funext 𝓤 𝓤₀ → De-Morgan 𝓤 → WEM 𝓤
De-Morgan-gives-WEM fe d P i = d P (¬ P) i (negations-are-props fe) non-contradiction

\end{code}

Is the above De Morgan Law a proposition? If it doesn't hold, it is
vacuously a proposition. But if it does hold, it is not a
proposition. We prove this by modifying any given δ : De-Mordan 𝓤 to a
different δ' : De-Morgan 𝓤. Then we also consider a truncated version
of De-Morgan that is a proposition and is logically equivalent to
De-Morgan. So De-Morgan 𝓤 is not necessarily a proposition, but it
always has split support (it has a proposition as a retract).

\begin{code}

De-Morgan-is-prop : ¬ De-Morgan 𝓤 → is-prop (De-Morgan 𝓤)
De-Morgan-is-prop ν δ = 𝟘-elim (ν δ)

De-Morgan-is-not-prop : funext 𝓤 𝓤₀ → De-Morgan 𝓤 → ¬ is-prop (De-Morgan 𝓤)
De-Morgan-is-not-prop {𝓤} fe δ = IV
 where
  open import MLTT.Plus-Properties

  wem : WEM 𝓤
  wem = De-Morgan-gives-WEM fe δ

  g : (P Q : 𝓤 ̇ )
      (i : is-prop P) (j : is-prop Q)
      (ν : ¬ (P × Q))
      (a : ¬ P + ¬¬ P)
      (b : ¬ Q + ¬¬ Q)
      (c : ¬ P + ¬ Q)
    → ¬ P + ¬ Q
  g P Q i j ν (inl _) (inl v) (inl _) = inr v
  g P Q i j ν (inl u) (inl _) (inr _) = inl u
  g P Q i j ν (inl _) (inr _) _       = δ P Q i j ν
  g P Q i j ν (inr _) _       _       = δ P Q i j ν

  δ' : De-Morgan 𝓤
  δ' P Q i j ν = g P Q i j ν (wem P i) (wem Q j) (δ P Q i j ν)

  I : (i : is-prop 𝟘) (h : ¬ 𝟘) → wem 𝟘 i ＝ inl h
  I i h = I₀ (wem 𝟘 i) refl
   where
    I₀ : (a : ¬ 𝟘 + ¬¬ 𝟘) → wem 𝟘 i ＝ a → wem 𝟘 i ＝ inl h
    I₀ (inl u) p = transport (λ - → wem 𝟘 i ＝ inl -) (negations-are-props fe u h) p
    I₀ (inr ϕ) p = 𝟘-elim (ϕ h)

  ν : ¬ (𝟘 × 𝟘)
  ν (p , q) = 𝟘-elim p

  II : (i j : is-prop 𝟘) → δ' 𝟘 𝟘 i j ν ≠ δ 𝟘 𝟘 i j ν
  II i j = II₃
   where
    m n : ¬ 𝟘 + ¬ 𝟘
    m = δ 𝟘 𝟘 i j ν
    n = g 𝟘 𝟘 i j ν (inl 𝟘-elim) (inl 𝟘-elim) m

    II₁ : δ' 𝟘 𝟘 i j ν ＝ n
    II₁ = ap₂ (λ -₁ -₂ → g 𝟘 𝟘 i j ν -₁ -₂ m)
              (I i 𝟘-elim)
              (I j 𝟘-elim)

    II₂ : (m' : ¬ 𝟘 + ¬ 𝟘)
        → m ＝ m'
        → g 𝟘 𝟘 i j ν (inl 𝟘-elim) (inl 𝟘-elim) m' ≠ m
    II₂ (inl x) p q = +disjoint
                       (inl x      ＝⟨ p ⁻¹ ⟩
                        m          ＝⟨ q ⁻¹ ⟩
                        inr 𝟘-elim ∎)
    II₂ (inr x) p q = +disjoint
                       (inl 𝟘-elim ＝⟨ q ⟩
                        m          ＝⟨ p ⟩
                        inr x      ∎)

    II₃ : δ' 𝟘 𝟘 i j ν ≠ m
    II₃ = transport (_≠ m) (II₁ ⁻¹) (II₂ m refl)

  III : δ' ≠ δ
  III e = II 𝟘-is-prop 𝟘-is-prop III₀
   where
    III₀ : δ' 𝟘 𝟘 𝟘-is-prop 𝟘-is-prop ν ＝ δ 𝟘 𝟘 𝟘-is-prop 𝟘-is-prop ν
    III₀ = ap (λ - → - 𝟘 𝟘 𝟘-is-prop 𝟘-is-prop ν) e

  IV : ¬ is-prop (De-Morgan 𝓤)
  IV i = III (i δ' δ)

module _ (pt : propositional-truncations-exist) where

 open PropositionalTruncation pt

 truncated-De-Morgan : ∀ 𝓤 → 𝓤 ⁺ ̇
 truncated-De-Morgan 𝓤 = (P Q : 𝓤 ̇ )
                       → is-prop P
                       → is-prop Q
                       → ¬ (P × Q) → ¬ P ∨ ¬ Q

 truncated-De-Morgan-is-prop : FunExt → is-prop (truncated-De-Morgan 𝓤)
 truncated-De-Morgan-is-prop fe = Π₅-is-prop (λ {𝓤} {𝓥} → fe 𝓤 𝓥)
                                   (λ P Q i j ν → ∨-is-prop)

 De-Morgan-gives-truncated-De-Morgan : De-Morgan 𝓤 → truncated-De-Morgan 𝓤
 De-Morgan-gives-truncated-De-Morgan d P Q i j ν = ∣ d P Q i j ν ∣

 truncated-De-Morgan-gives-WEM : FunExt → truncated-De-Morgan 𝓤 → WEM 𝓤
 truncated-De-Morgan-gives-WEM {𝓤} fe t P i = III
  where
   I : ¬ (P × ¬ P) → ¬ P ∨ ¬¬ P
   I = t P (¬ P) i (negations-are-props (fe 𝓤 𝓤₀))

   II : ¬ P ∨ ¬¬ P
   II = I non-contradiction

   III : ¬ P + ¬¬ P
   III = exit-∥∥
          (decidability-of-prop-is-prop (fe 𝓤 𝓤₀)
          (negations-are-props (fe 𝓤 𝓤₀)))
          II

 truncated-De-Morgan-gives-De-Morgan : FunExt → truncated-De-Morgan 𝓤 → De-Morgan 𝓤
 truncated-De-Morgan-gives-De-Morgan fe t P Q i j ν =
  WEM-gives-De-Morgan (truncated-De-Morgan-gives-WEM fe t) P Q i j ν

\end{code}

The above shows that weak excluded middle, De Morgan and truncated De
Morgan are logically equivalent (https://ncatlab.org/nlab/show/De%20Morgan%20laws).

\begin{code}

 double-negation-is-truncation-gives-DNE : ((X : 𝓤 ̇ ) → ¬¬ X → ∥ X ∥) → DNE 𝓤
 double-negation-is-truncation-gives-DNE f P i u = exit-∥∥ i (f P u)

 non-empty-is-inhabited : EM 𝓤 → {X : 𝓤 ̇ } → ¬¬ X → ∥ X ∥
 non-empty-is-inhabited em {X} φ =
  cases
   (λ (s : ∥ X ∥)
         → s)
   (λ (u : ¬ ∥ X ∥)
         → 𝟘-elim (φ (contrapositive ∣_∣ u))) (em ∥ X ∥ ∥∥-is-prop)

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
