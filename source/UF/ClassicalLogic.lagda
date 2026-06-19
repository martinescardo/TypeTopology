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

module UF.ClassicalLogic where

open import MLTT.Spartan

open import UF.Base
open import UF.Equiv
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier
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

\end{code}

Added by Martin Escardo and Tom de Jong 29th August 2024. Originally
we worked with WEM. But it turns out that it is not necessary to
assume that P is a proposition, and so we now work with the new
definition typal-WEM, which removes this assumption.

\begin{code}

WEM : ∀ 𝓤 → 𝓤 ⁺ ̇
WEM 𝓤 = (P : 𝓤 ̇ ) → is-prop P → ¬ P + ¬¬ P

typal-WEM : ∀ 𝓤 → 𝓤 ⁺ ̇
typal-WEM 𝓤 = (A : 𝓤 ̇ ) → ¬ A + ¬¬ A

WEM-gives-typal-WEM : funext 𝓤 𝓤₀ → WEM 𝓤 → typal-WEM 𝓤
WEM-gives-typal-WEM fe wem' A =
 Cases (wem' (¬ A) (negations-are-props fe))
  inr
  (inl ∘ three-negations-imply-one)

typal-WEM-gives-WEM : typal-WEM 𝓤 → WEM 𝓤
typal-WEM-gives-WEM wem P P-is-prop = wem P

typal-WEM-is-prop : FunExt → is-prop (typal-WEM 𝓤)
typal-WEM-is-prop {𝓤} fe = Π-is-prop (fe (𝓤 ⁺) 𝓤)
                            (λ _ → decidability-of-prop-is-prop (fe 𝓤 𝓤₀)
                                    (negations-are-props (fe 𝓤 𝓤₀)))

WEM-is-prop : FunExt → is-prop (WEM 𝓤)
WEM-is-prop {𝓤} fe = Π₂-is-prop (λ {𝓥} {𝓦} → fe 𝓥 𝓦)
                       (λ _ _ → decidability-of-prop-is-prop (fe 𝓤 𝓤₀)
                                 (negations-are-props (fe 𝓤 𝓤₀)))

\end{code}

End of addition.

Double negation elimination is equivalent to excluded middle.

\begin{code}

DNE : ∀ 𝓤 → 𝓤 ⁺ ̇
DNE 𝓤 = (P : 𝓤 ̇ ) → is-prop P → ¬¬ P → P

EM-gives-DNE : EM 𝓤 → DNE 𝓤
EM-gives-DNE em P i φ = cases id (λ u → 𝟘-elim (φ u)) (em P i)

double-negation-elim : EM 𝓤 → DNE 𝓤
double-negation-elim = EM-gives-DNE

double-negation-of-decision : {X : 𝓤 ̇ } → ¬¬ (X + ¬ X)
double-negation-of-decision u = u (inr (λ p → u (inl p)))

DNE-gives-EM : funext 𝓤 𝓤₀ → DNE 𝓤 → EM 𝓤
DNE-gives-EM fe dne P isp = dne (P + ¬ P)
                             (decidability-of-prop-is-prop fe isp)
                             double-negation-of-decision

all-props-negative-gives-DNE : funext 𝓤 𝓤₀
                            → ((P : 𝓤 ̇ ) → is-prop P → Σ Q ꞉ 𝓤 ̇ , (P ↔ ¬ Q))
                            → DNE 𝓤
all-props-negative-gives-DNE {𝓤} fe ϕ P P-is-prop = I (ϕ P P-is-prop)
 where
  I : (Σ Q ꞉ 𝓤 ̇ , (P ↔ ¬ Q)) → ¬¬ P → P
  I (Q , f , g) ν = g (three-negations-imply-one (double-contrapositive f ν))

all-props-negative-gives-EM
 : funext 𝓤 𝓤₀
 → ((P : 𝓤 ̇ ) → is-prop P → Σ Q ꞉ 𝓤 ̇ , (P ↔ ¬ Q))
 → EM 𝓤
all-props-negative-gives-EM {𝓤} fe ϕ
 = DNE-gives-EM fe (all-props-negative-gives-DNE fe ϕ)

fe-and-em-give-propositional-truncations
 : FunExt
 → Excluded-Middle
 → propositional-truncations-exist
fe-and-em-give-propositional-truncations fe em =
 record {
  ∥_∥          = λ X → ¬¬ X ;
  ∥∥-is-prop   = Π-is-prop (fe _ _) (λ _ → 𝟘-is-prop) ;
  ∣_∣          = λ x u → u x ;
  ∥∥-rec       = λ i u φ → EM-gives-DNE em _ i (¬¬-functor u φ)
 }

\end{code}

We now consider various logically equivalent formulations of De Morgan
Law.

\begin{code}

untruncated-De-Morgan : ∀ 𝓤 → 𝓤 ⁺ ̇
untruncated-De-Morgan 𝓤 = (P Q : 𝓤 ̇ )
                        → is-prop P
                        → is-prop Q
                        → ¬ (P × Q) → ¬ P + ¬ Q

EM-gives-untruncated-De-Morgan : EM 𝓤
                               → untruncated-De-Morgan 𝓤
EM-gives-untruncated-De-Morgan em A B i j =
 λ (ν : ¬ (A × B)) →
      Cases (em A i)
       (λ (a : A) → Cases (em B j)
                     (λ (b : B) → 𝟘-elim (ν (a , b)))
                     inr)
       inl

\end{code}

But already weak excluded middle gives De Morgan.

Added/modified by Martin Escardo and Tom de Jong 29th August 2024. A typal
version of De Morgan.

\begin{code}

non-contradiction : {X : 𝓤 ̇ } → ¬ (X × ¬ X)
non-contradiction (x , ν) = ν x

untruncated-typal-De-Morgan : ∀ 𝓤 → 𝓤 ⁺ ̇
untruncated-typal-De-Morgan 𝓤 = (P Q : 𝓤 ̇ ) → ¬ (P × Q) → ¬ P + ¬ Q

untruncated-typal-De-Morgan-gives-untruncated-De-Morgan
 : untruncated-typal-De-Morgan 𝓤
 → untruncated-De-Morgan 𝓤
untruncated-typal-De-Morgan-gives-untruncated-De-Morgan d' P Q i j = d' P Q

\end{code}

Originally the following was proved with WEM.

\begin{code}

typal-WEM-gives-untruncated-typal-De-Morgan : typal-WEM 𝓤
                                            → untruncated-typal-De-Morgan 𝓤
typal-WEM-gives-untruncated-typal-De-Morgan wem A B =
 λ (ν : ¬ (A × B)) →
      Cases (wem A)
       inl
       (λ (ϕ : ¬¬ A)
             → Cases (wem B)
                inr
                (λ (γ : ¬¬ B) → 𝟘-elim
                                 (ϕ (λ (a : A) → γ (λ (b : B) → ν (a , b))))))

typal-WEM-gives-untruncated-De-Morgan : typal-WEM 𝓤 → untruncated-De-Morgan 𝓤
typal-WEM-gives-untruncated-De-Morgan =
 untruncated-typal-De-Morgan-gives-untruncated-De-Morgan
 ∘ typal-WEM-gives-untruncated-typal-De-Morgan

untruncated-De-Morgan-gives-WEM : funext 𝓤 𝓤₀
                                → untruncated-De-Morgan 𝓤
                                → WEM 𝓤
untruncated-De-Morgan-gives-WEM fe d P i =
 d P (¬ P) i (negations-are-props fe) non-contradiction

untruncated-De-Morgan-gives-typal-WEM : funext 𝓤 𝓤₀
                                      → untruncated-De-Morgan 𝓤
                                      → typal-WEM 𝓤
untruncated-De-Morgan-gives-typal-WEM fe =
 WEM-gives-typal-WEM fe ∘ untruncated-De-Morgan-gives-WEM fe

untruncated-De-Morgan-gives-untruncated-typal-De-Morgan
 : funext 𝓤 𝓤₀
 → untruncated-De-Morgan 𝓤
 → untruncated-typal-De-Morgan 𝓤
untruncated-De-Morgan-gives-untruncated-typal-De-Morgan fe =
 typal-WEM-gives-untruncated-typal-De-Morgan
 ∘ untruncated-De-Morgan-gives-typal-WEM fe

\end{code}

End of addition/modification.

Is the above untruncated De Morgan Law a proposition? Not in
general. If it doesn't hold, it is vacuously a proposition. But if it
does hold, it is not a proposition. We prove this by modifying any
given δ : De-Mordan 𝓤 to a different δ' : untruncated-De-Morgan
𝓤. Then we also consider a truncated version of untruncated-De-Morgan
that is a proposition and is logically equivalent to
untruncated-De-Morgan. So untruncated-De-Morgan 𝓤 is not necessarily a
proposition, but it always has split support (it has a proposition as
a retract).

\begin{code}

untruncated-De-Morgan-is-prop
 : ¬ untruncated-De-Morgan 𝓤
 → is-prop (untruncated-De-Morgan 𝓤)
untruncated-De-Morgan-is-prop ν δ = 𝟘-elim (ν δ)

untruncated-typal-De-Morgan-has-two-witnesses-if-it-has-one
 : funext 𝓤 𝓤₀
 → (δ : untruncated-typal-De-Morgan 𝓤)
 → Σ δ' ꞉ untruncated-typal-De-Morgan 𝓤 , δ' ≠ δ
untruncated-typal-De-Morgan-has-two-witnesses-if-it-has-one {𝓤} fe δ
 = (δ' , III)
 where
  open import MLTT.Plus-Properties

  wem : typal-WEM 𝓤
  wem = untruncated-De-Morgan-gives-typal-WEM fe
         (untruncated-typal-De-Morgan-gives-untruncated-De-Morgan δ)

  g : (P Q : 𝓤 ̇ )
      (ν : ¬ (P × Q))
      (a : ¬ P + ¬¬ P)
      (b : ¬ Q + ¬¬ Q)
      (c : ¬ P + ¬ Q)
    → ¬ P + ¬ Q
  g P Q ν (inl _) (inl v) (inl _) = inr v
  g P Q ν (inl u) (inl _) (inr _) = inl u
  g P Q ν (inl _) (inr _) _       = δ P Q ν
  g P Q ν (inr _) _       _       = δ P Q ν

  δ' : untruncated-typal-De-Morgan 𝓤
  δ' P Q ν = g P Q ν (wem P) (wem Q) (δ P Q ν)

  I : (h : ¬ 𝟘) → wem 𝟘 ＝ inl h
  I h = I₀ (wem 𝟘) refl
   where
    I₀ : (a : ¬ 𝟘 + ¬¬ 𝟘) → wem 𝟘 ＝ a → wem 𝟘 ＝ inl h
    I₀ (inl u) = transport
                  (λ - → wem 𝟘 ＝ inl -)
                  (negations-are-props fe u h)
    I₀ (inr ϕ) p = 𝟘-elim (ϕ h)

  ν : ¬ (𝟘 × 𝟘)
  ν (p , q) = 𝟘-elim p

  II : δ' 𝟘 𝟘 ν ≠ δ 𝟘 𝟘 ν
  II = II₃
   where
    m n : ¬ 𝟘 + ¬ 𝟘
    m = δ 𝟘 𝟘 ν
    n = g 𝟘 𝟘 ν (inl 𝟘-elim) (inl 𝟘-elim) m

    II₁ : δ' 𝟘 𝟘 ν ＝ n
    II₁ = ap₂ (λ -₁ -₂ → g 𝟘 𝟘 ν -₁ -₂ m)
              (I 𝟘-elim)
              (I 𝟘-elim)

    II₂ : (m' : ¬ 𝟘 + ¬ 𝟘)
        → m ＝ m'
        → g 𝟘 𝟘 ν (inl 𝟘-elim) (inl 𝟘-elim) m' ≠ m
    II₂ (inl x) p q = +disjoint
                       (inl x      ＝⟨ p ⁻¹ ⟩
                        m          ＝⟨ q ⁻¹ ⟩
                        inr 𝟘-elim ∎)
    II₂ (inr x) p q = +disjoint
                       (inl 𝟘-elim ＝⟨ q ⟩
                        m          ＝⟨ p ⟩
                        inr x      ∎)

    II₃ : δ' 𝟘 𝟘 ν ≠ m
    II₃ = transport (_≠ m) (II₁ ⁻¹) (II₂ m refl)

  III : δ' ≠ δ
  III e = II III₀
   where
    III₀ : δ' 𝟘 𝟘 ν ＝ δ 𝟘 𝟘 ν
    III₀ = ap (λ - → - 𝟘 𝟘 ν) e

untruncated-typal-De-Morgan-is-not-prop
 : funext 𝓤 𝓤₀
 → untruncated-typal-De-Morgan 𝓤
 → ¬ is-prop (untruncated-typal-De-Morgan 𝓤)
untruncated-typal-De-Morgan-is-not-prop {𝓤} fe δ
 = IV (untruncated-typal-De-Morgan-has-two-witnesses-if-it-has-one fe δ)
 where
  IV : (Σ δ' ꞉ untruncated-typal-De-Morgan 𝓤 , δ' ≠ δ)
    → ¬ is-prop (untruncated-typal-De-Morgan 𝓤)
  IV (δ' , III) i = III (i δ' δ)

\end{code}

We repeat the above proof adding more information.

TODO. Is it possible to prove the following from the above, or
vice-versa, to avoid the repetition?

\begin{code}

untruncated-De-Morgan-has-at-least-two-witnesses-if-it-has-one
 : funext 𝓤 𝓤₀
 → (δ : untruncated-De-Morgan 𝓤)
 → Σ δ' ꞉ untruncated-De-Morgan 𝓤 , δ' ≠ δ
untruncated-De-Morgan-has-at-least-two-witnesses-if-it-has-one {𝓤} fe δ
 = (δ' , III)
 where
  open import MLTT.Plus-Properties

  wem : typal-WEM 𝓤
  wem = untruncated-De-Morgan-gives-typal-WEM fe δ

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

  δ' : untruncated-De-Morgan 𝓤
  δ' P Q i j ν = g P Q i j ν (wem P) (wem Q) (δ P Q i j ν)

  I : (i : is-prop 𝟘) (h : ¬ 𝟘) → wem 𝟘 ＝ inl h
  I i h = I₀ (wem 𝟘) refl
   where
    I₀ : (a : ¬ 𝟘 + ¬¬ 𝟘) → wem 𝟘 ＝ a → wem 𝟘 ＝ inl h
    I₀ (inl u) = transport
                  (λ - → wem 𝟘 ＝ inl -)
                  (negations-are-props fe u h)
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

untruncated-De-Morgan-is-not-prop
 : funext 𝓤 𝓤₀
 → untruncated-De-Morgan 𝓤
 → ¬ is-prop (untruncated-De-Morgan 𝓤)
untruncated-De-Morgan-is-not-prop {𝓤} fe δ
 = IV (untruncated-De-Morgan-has-at-least-two-witnesses-if-it-has-one fe δ)
 where
  IV : (Σ δ' ꞉ untruncated-De-Morgan 𝓤 , δ' ≠ δ)
    → ¬ is-prop (untruncated-De-Morgan 𝓤)
  IV (δ' , III) i = III (i δ' δ)

untruncated-De-Morgan-curiousity : funext 𝓤 𝓤₀
                                 → ¬¬ is-prop (untruncated-De-Morgan 𝓤)
                                 → is-prop (untruncated-De-Morgan 𝓤)
untruncated-De-Morgan-curiousity fe =
 untruncated-De-Morgan-is-prop
 ∘ contrapositive (untruncated-De-Morgan-is-not-prop fe)

module _ (pt : propositional-truncations-exist) where

 open PropositionalTruncation pt

 typal-De-Morgan : ∀ 𝓤 → 𝓤 ⁺ ̇
 typal-De-Morgan 𝓤 = (P Q : 𝓤 ̇ ) → ¬ (P × Q) → ¬ P ∨ ¬ Q

 De-Morgan : ∀ 𝓤 → 𝓤 ⁺ ̇
 De-Morgan 𝓤 = (P Q : 𝓤 ̇ )
             → is-prop P
             → is-prop Q
             → ¬ (P × Q) → ¬ P ∨ ¬ Q

 typal-De-Morgan-is-prop : FunExt
                         → is-prop (typal-De-Morgan 𝓤)
 typal-De-Morgan-is-prop fe = Π₃-is-prop (λ {𝓤} {𝓥} → fe 𝓤 𝓥)
                                         (λ P Q ν → ∨-is-prop)

 De-Morgan-is-prop : FunExt → is-prop (De-Morgan 𝓤)
 De-Morgan-is-prop fe = Π₅-is-prop (λ {𝓤} {𝓥} → fe 𝓤 𝓥)
                                   (λ P Q i j ν → ∨-is-prop)

 untruncated-De-Morgan-gives-De-Morgan : untruncated-De-Morgan 𝓤
                                       → De-Morgan 𝓤
 untruncated-De-Morgan-gives-De-Morgan d P Q i j ν = ∣ d P Q i j ν ∣

 De-Morgan-gives-WEM : funext 𝓤 𝓤₀
                     → De-Morgan 𝓤
                     → WEM 𝓤
 De-Morgan-gives-WEM {𝓤} fe dm P i = III
  where
   I : ¬ (P × ¬ P) → ¬ P ∨ ¬¬ P
   I = dm P (¬ P) i (negations-are-props fe)

   II : ¬ P ∨ ¬¬ P
   II = I non-contradiction

   III : ¬ P + ¬¬ P
   III = exit-∥∥
          (decidability-of-prop-is-prop fe (negations-are-props fe))
          II

 De-Morgan-gives-typal-WEM : funext 𝓤 𝓤₀ → De-Morgan 𝓤 → typal-WEM 𝓤
 De-Morgan-gives-typal-WEM {𝓤} fe =
  WEM-gives-typal-WEM fe ∘ De-Morgan-gives-WEM fe

 De-Morgan-gives-untruncated-De-Morgan : funext 𝓤 𝓤₀
                                       → De-Morgan 𝓤
                                       → untruncated-De-Morgan 𝓤
 De-Morgan-gives-untruncated-De-Morgan fe t P Q i j ν =
  typal-WEM-gives-untruncated-De-Morgan
   (De-Morgan-gives-typal-WEM fe t)
   P Q i j ν

 typal-De-Morgan-gives-De-Morgan : typal-De-Morgan 𝓤 → De-Morgan 𝓤
 typal-De-Morgan-gives-De-Morgan d P Q i j = d P Q

 untruncated-typal-De-Morgan-gives-typal-De-Morgan
  : untruncated-typal-De-Morgan 𝓤
  → typal-De-Morgan 𝓤
 untruncated-typal-De-Morgan-gives-typal-De-Morgan d P Q ν =
  ∣ d P Q ν ∣

 De-Morgan-gives-typal-De-Morgan : funext 𝓤 𝓤₀
                                 → De-Morgan 𝓤
                                 → typal-De-Morgan 𝓤
 De-Morgan-gives-typal-De-Morgan {𝓤} fe d A B ν =
  ∣ typal-WEM-gives-untruncated-typal-De-Morgan
     (De-Morgan-gives-typal-WEM fe d)
     A B ν ∣

\end{code}

The above shows that weak excluded middle, De Morgan and truncated De
Morgan are logically equivalent, all in their two (proposional and
typal) versions, so in a total of six logically equivalent statements.

Here is a diagram with the main implications, summarized below in
Agda:

     1 ----> 2
     ^        \
     |         \
     |          \
     |           \
     |            \
     |             \
     |              v
     3 <-- 5 <----- 6
      ^            /
       \          /
        \        /
         \      /
          \    /
           \  v
             4

\begin{code}

 module _ (𝓤 : Universe) where

  private
   ⦅1⦆ = WEM 𝓤
   ⦅2⦆ = typal-WEM 𝓤
   ⦅3⦆ = De-Morgan 𝓤
   ⦅4⦆ = typal-De-Morgan 𝓤
   ⦅5⦆ = untruncated-De-Morgan 𝓤
   ⦅6⦆ = untruncated-typal-De-Morgan 𝓤

  De-Morgan-WEM-diagram
   : funext 𝓤 𝓤₀
   → (⦅1⦆ → ⦅2⦆)
   × (⦅2⦆ → ⦅6⦆)
   × (⦅3⦆ → ⦅1⦆)
   × (⦅4⦆ → ⦅3⦆)
   × (⦅5⦆ → ⦅3⦆)
   × (⦅6⦆ → ⦅4⦆)
   × (⦅6⦆ → ⦅5⦆)
  De-Morgan-WEM-diagram fe =
   WEM-gives-typal-WEM fe ,
   typal-WEM-gives-untruncated-typal-De-Morgan ,
   De-Morgan-gives-WEM fe ,
   typal-De-Morgan-gives-De-Morgan ,
   untruncated-De-Morgan-gives-De-Morgan ,
   untruncated-typal-De-Morgan-gives-typal-De-Morgan ,
   untruncated-typal-De-Morgan-gives-untruncated-De-Morgan

\end{code}

That weak excluded middle and De Morgan are equivalent is long known
and now part of the folklore. We don't know who proved this first,
but, for example, it is in Johnstone's papers on topos theory and his
Elephant two-volume book.

Mike Shulman asked in the HoTT mailing list [1] whether truncated De
Morgan implies untruncated De Morgan, and Martin Escardo offered a proof
as an answer [2], which Mike Shulman added to the nLab [3].

[1] Mike Shulman. de Morgan's Law.
    https://groups.google.com/g/homotopytypetheory/c/Azq6GVU98II/m/qEp8TeInYgAJ
    1st September 2014.

[2] Martin Escardo. de Morgan's Law.
    https://groups.google.com/g/homotopytypetheory/c/Azq6GVU98II/m/bXMixO9s1boJ
    2nd September 2014

[3] Added to the nLab by Mike Shulman.
    https://ncatlab.org/nlab/show/De%20Morgan%20laws.
    2nd September 2014

Here we have added, to both typal-WEM and De Morgan, truncated or not, the
discussion of whether the types in question need to be propositions or
not for them to be all equivalent, and the answer is that it doesn't
matter whether we assume that the types in question are all
propositions.

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

 ¬¬Σ→∃ : {𝓤 𝓣 : Universe} {X : 𝓤 ̇ } → {A : X → 𝓣 ̇ }
       → DNE (𝓤 ⊔ 𝓣)
       → ¬¬ (Σ x ꞉ X , A x )
       → (∃ x ꞉ X , A x)
 ¬¬Σ→∃ {𝓤} {A} {X} {A₁} dn ¬¬Σ = dn _ ∥∥-is-prop (¬¬-functor ∣_∣ ¬¬Σ)

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

TODO. Global choice contradicts univalence. This is already present in
the directory MGS.
