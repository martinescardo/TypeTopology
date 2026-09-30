Tom de Jong, 1 and 4 April 2022.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Ordinals.Taboos where

open import MLTT.Plus-Properties
open import MLTT.Spartan hiding (𝟚 ; ₀ ; ₁)
open import Ordinals.Equivalence
open import Ordinals.Maps
open import Ordinals.Notions
open import Ordinals.Type
open import Ordinals.Underlying
open import UF.DiscreteAndSeparated hiding (𝟚-is-discrete)
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.ClassicalLogic
open import UF.FunExt
open import UF.PropTrunc
open import UF.Size
open import UF.Subsingletons
open import UF.UA-FunExt
open import UF.Univalence

\end{code}

We show that two classically true statements about ordinals are constructively
unacceptable, because each of them implies excluded middle.

The first statement is that every discrete ordinal is trichotomous. Classically,
this is trivial, because every ordinal is trichotomous (and discrete).
Constructively, the converse (trichotomous implies discrete) *does* hold.

The second statement is that the supremum of a family of trichotomous ordinals
indexed by a discrete type is again discrete.

\begin{code}

Every-Discrete-Ordinal-Is-Trichotomous : (𝓤 : Universe) → 𝓤 ⁺ ̇
Every-Discrete-Ordinal-Is-Trichotomous 𝓤 =
 ((α : Ordinal 𝓤) → is-discrete ⟨ α ⟩
                  → is-trichotomous-order (underlying-order α))

module suprema-of-ordinals-assumptions
        (pt : propositional-truncations-exist)
        (sr : Set-Replacement pt)
        (ua : Univalence)
       where

 open import Ordinals.OrdinalOfOrdinalsSuprema ua
 open suprema pt sr public

 Sups-Of-Discretely-Indexed-Trichotomous-Ordinals-Are-Discrete :
  (𝓤 : Universe) → 𝓤 ⁺ ̇
 Sups-Of-Discretely-Indexed-Trichotomous-Ordinals-Are-Discrete 𝓤 =
  (I : 𝓤 ̇ ) → is-discrete I → (α : I → Ordinal 𝓤)
             → ((i : I) → is-trichotomous-order (underlying-order (α i)))
             → is-discrete ⟨ sup α ⟩

\end{code}

In showing that the first statement implies excluded middle, the two-element
type in some fixed but arbitrary universe 𝓤 will be useful.

\begin{code}

module _ {𝓤 : Universe} where

 𝟚 : 𝓤 ̇
 𝟚 = 𝟙 {𝓤} + 𝟙 {𝓤}

 pattern ₀ = inl ⋆
 pattern ₁ = inr ⋆

 𝟚-is-discrete : is-discrete 𝟚
 𝟚-is-discrete = +-is-discrete 𝟙-is-discrete 𝟙-is-discrete

\end{code}

We now work towards proving that excluded middle follows from the assertion that
every discrete ordinal is trichotomous.

The outline of the proof is given here:
(1) Fix a type P and construct a transitive and well-founded relation ≺ on 𝟚
    involving P.
(2) If P is a proposition, then ≺ is prop-valued.
(3) If ¬¬ P holds, then ≺ is extensional.
(4) Hence, if P is a proposition such that ¬¬ P holds, then (𝟚 , ≺) is a
    (discrete) ordinal.
(5) The order ≺ is trichotomous if and only if P holds.

Hence, if every discrete ordinal is trichotomous, then ¬¬ P → P for every
proposition P, which is equivalent to excluded middle.

\begin{code}

module discrete-trichotomous-taboo-construction
        (P : 𝓤 ̇ )
       where

 _≺_ : 𝟚 {𝓤} → 𝟚 {𝓤} → 𝓤 ̇
 ₀ ≺ ₀ = 𝟘
 ₀ ≺ ₁ = P
 ₁ ≺ ₀ = 𝟘
 ₁ ≺ ₁ = 𝟘

 ≺-is-prop-valued : is-prop P → is-prop-valued _≺_
 ≺-is-prop-valued i ₀ ₀ = 𝟘-is-prop
 ≺-is-prop-valued i ₀ ₁ = i
 ≺-is-prop-valued i ₁ ₀ = 𝟘-is-prop
 ≺-is-prop-valued i ₁ ₁ = 𝟘-is-prop

 ≺-is-transitive : transitive _≺_
 ≺-is-transitive ₀ ₀ z u v = 𝟘-elim u
 ≺-is-transitive ₀ ₁ ₀ u v = v
 ≺-is-transitive ₀ ₁ ₁ u v = u
 ≺-is-transitive ₁ ₀ z u v = 𝟘-elim u
 ≺-is-transitive ₁ ₁ z u v = 𝟘-elim u

 ≺-well-founded-lemma : (y : 𝟚) → y ≺ ₀ → is-accessible _≺_ y
 ≺-well-founded-lemma ₀ l = 𝟘-elim l
 ≺-well-founded-lemma ₁ l = 𝟘-elim l

 ≺-is-well-founded : is-well-founded _≺_
 ≺-is-well-founded ₀ = acc ≺-well-founded-lemma
 ≺-is-well-founded ₁ = acc γ
  where
   γ : (y : 𝟚) → y ≺ ₁ → is-accessible _≺_ y
   γ ₀ l = acc ≺-well-founded-lemma
   γ ₁ l = 𝟘-elim l

 ≺-is-extensional : ¬¬ P → is-extensional _≺_
 ≺-is-extensional h ₀ ₀ u v = refl
 ≺-is-extensional h ₁ ₁ u v = refl
 ≺-is-extensional h ₀ ₁ u v = 𝟘-elim (h γ)
  where
   γ : ¬ P
   γ p = 𝟘-elim (v ₀ p)
 ≺-is-extensional h ₁ ₀ u v = 𝟘-elim (h γ)
  where
   γ : ¬ P
   γ p = 𝟘-elim (u ₀ p)

 𝟚≺-ordinal : is-prop P → ¬¬ P → Ordinal 𝓤
 𝟚≺-ordinal i h = 𝟚 , _≺_ , ≺-is-prop-valued i   , ≺-is-well-founded
                          , ≺-is-extensional h , ≺-is-transitive

 ≺-trichotomous-characterization : is-trichotomous-order _≺_ ↔ P
 ≺-trichotomous-characterization = ⦅⇒⦆ , ⦅⇐⦆
  where
   ⦅⇐⦆ : P → is-trichotomous-order _≺_
   ⦅⇐⦆ p ₀ ₀ = inr (inl refl)
   ⦅⇐⦆ p ₀ ₁ = inl p
   ⦅⇐⦆ p ₁ ₀ = inr (inr p)
   ⦅⇐⦆ p ₁ ₁ = inr (inl refl)
   ⦅⇒⦆ : is-trichotomous-order _≺_ → P
   ⦅⇒⦆ t = lemma (t ₀ ₁)
    where
     lemma : (₀ ≺ ₁) + (₀ ＝ ₁) + (₁ ≺ ₀) → P
     lemma (inl p)       = p
     lemma (inr (inl e)) = 𝟘-elim (+disjoint e)
     lemma (inr (inr l)) = 𝟘-elim l

\end{code}

The above construction quickly yields the first promised result.

\begin{code}

DNE-if-Every-Discrete-Ordinal-Is-Trichotomous :
   Every-Discrete-Ordinal-Is-Trichotomous 𝓤
 → DNE 𝓤
DNE-if-Every-Discrete-Ordinal-Is-Trichotomous h P P-is-prop not-not-P =
 lr-implication ≺-trichotomous-characterization
                  (h (𝟚≺-ordinal P-is-prop not-not-P) (𝟚-is-discrete))
  where
   open discrete-trichotomous-taboo-construction P

EM-if-Every-Discrete-Ordinal-Is-Trichotomous :
   funext 𝓤 𝓤₀
 → Every-Discrete-Ordinal-Is-Trichotomous 𝓤
 → EM 𝓤
EM-if-Every-Discrete-Ordinal-Is-Trichotomous fe h =
 DNE-gives-EM fe (DNE-if-Every-Discrete-Ordinal-Is-Trichotomous h)

\end{code}

It is somewhat more involved to get a taboo from the assertion that
discretely-indexed suprema of trichotomous ordinals are discrete.

The first step is fairly straightforward however and once again involves
constructing an ordinal that depends on a proposition P. What matters is that:
(1) the constructed ordinal is trichotomous;
(2) an initial segment of the ordinal is equivalent to P.

\begin{code}

module _
        (fe : FunExt)
       where

 open import Ordinals.Arithmetic fe
 open import Ordinals.WellOrderArithmetic

 module discrete-sup-taboo-construction-I
         (P : 𝓤 ̇ )
         (P-is-prop : is-prop P)
        where

  P' : Ordinal 𝓤
  P' = prop-ordinal P P-is-prop +ₒ 𝟙ₒ

  P'-is-trichotomous : is-trichotomous-order (underlying-order P')
  P'-is-trichotomous = trichotomy-preservation (prop.trichotomous P P-is-prop)
                                               (prop.trichotomous 𝟙 𝟙-is-prop)
   where
    open plus (prop.order P P-is-prop) (prop.order 𝟙 𝟙-is-prop)

\end{code}

Next, we turn to the second part of our construction, which defines a
discretely-indexed family of trichotomous ordinals. To work with (suprema of)
ordinals, we need additional assumptions and imports.

\begin{code}

module _
        (pt : propositional-truncations-exist)
        (sr : Set-Replacement pt)
        (ua : Univalence)
       where

 open suprema-of-ordinals-assumptions pt sr ua

 private
  fe : FunExt
  fe = Univalence-gives-FunExt ua

 open import NotionsOfDecidability.Decidable

 open import Ordinals.Arithmetic fe
 open import Ordinals.OrdinalOfOrdinals ua
 open import Ordinals.WellOrderArithmetic

 open import UF.Embeddings
 open import UF.ImageAndSurjection pt

 module discrete-sup-taboo-construction-II
          (P : 𝓤 ̇ )
          (P-is-prop : is-prop P)
         where

  open discrete-sup-taboo-construction-I fe P P-is-prop

  I : 𝓤 ̇
  I = 𝟚 {𝓤}

  α : I → Ordinal 𝓤
  α ₀ = P'
  α ₁ = 𝟙ₒ +ₒ 𝟙ₒ

  α-is-trichotomous : (i : I) → is-trichotomous-order (underlying-order (α i))
  α-is-trichotomous ₀ = P'-is-trichotomous
  α-is-trichotomous ₁ = trichotomy-preservation trichotomous trichotomous
   where
    open prop 𝟙 𝟙-is-prop
    open plus (underlying-order 𝟙ₒ) (underlying-order 𝟙ₒ)

\end{code}

We will derive decidability of P from the assumption that the supremum of α is
discrete.

The idea of the proof is captured by NB₁ and NB₂ below. We will decide P by
deciding whether (α ₀ ↓ inr ⋆) and (α ₁ ↓ inr ⋆) are equivalent ordinals.

This, in turn, is decidable, because both ordinals are images of an embedding
e : ⟨ sup α ⟩ → Ordinal 𝓤 and ⟨ sup α ⟩ is discrete by assumption.

\begin{code}

  fact-I : ⟨ α ₀ ↓ inr ⋆ ⟩ → P
  fact-I (inl p , _) = p
  fact-I (inr ⋆ , l) = 𝟘-elim l

  NB₁ : ⟨ α ₀ ↓ inr ⋆ ⟩ ≃ P
  NB₁ = qinveq f (g , η , ε)
   where
    f : ⟨ α ₀ ↓ ₁ ⟩ → P
    f = fact-I
    g : P → ⟨ α ₀ ↓ ₁ ⟩
    g p = (inl p , ⋆)
    η : g ∘ f ∼ id
    η (inl p , _) = to-subtype-＝ (λ x → Prop-valuedness P' x ₁) refl
    η (inr ⋆ , l) = 𝟘-elim l
    ε : f ∘ g ∼ id
    ε p = P-is-prop (f (g p)) p

  NB₂ : ⟨ α ₁ ↓ inr ⋆ ⟩ ≃ 𝟙{𝓤}
  NB₂ = singleton-≃-𝟙 (x , c)
   where
    x : ⟨ α ₁ ↓ inr ⋆ ⟩
    x = (inl ⋆ , ⋆)
    c : is-central (⟨ α ₁ ↓ inr ⋆ ⟩) (₀ , ⋆)
    c (inl ⋆ , ⋆) = refl
    c (inr ⋆ , l) = 𝟘-elim l

  fact-II : P → (α ₀ ↓ inr ⋆) ≃ₒ (α ₁ ↓ inr ⋆)
  fact-II p = f , (f-order-pres , f-is-equiv , g-order-pres)
   where
    f : ⟨ α ₀ ↓ inr ⋆ ⟩ → ⟨ α ₁ ↓ inr ⋆ ⟩
    f _ = inl ⋆ , ⋆
    g : ⟨ α ₁ ↓ inr ⋆ ⟩ → ⟨ α ₀ ↓ inr ⋆ ⟩
    g _ = inl p , ⋆
    f-order-pres : is-order-preserving (α ₀ ↓ inr ⋆) (α ₁ ↓ inr ⋆) f
    f-order-pres (inl p , _) (inl q , _) l = 𝟘-elim l
    f-order-pres (inl p , _) (inr ⋆ , m) l = 𝟘-elim m
    f-order-pres (inr ⋆ , m)  y          l = 𝟘-elim m
    g-order-pres : is-order-preserving (α ₁ ↓ inr ⋆) (α ₀ ↓ inr ⋆) g
    g-order-pres (inl ⋆ , _) (inl ⋆ , _) l = 𝟘-elim l
    g-order-pres (inl ⋆ , _) (inr ⋆ , m) l = 𝟘-elim m
    g-order-pres (inr ⋆ , m)  y          l = 𝟘-elim m
    f-is-equiv : is-equiv f
    f-is-equiv = qinvs-are-equivs f (g , η , ε)
     where
      ε : f ∘ g ∼ id
      ε (inl ⋆ , _) = refl
      ε (inr ⋆ , l) = 𝟘-elim l
      η : g ∘ f ∼ id
      η (inl q , _) = to-subtype-＝ (λ x → Prop-valuedness P' x ₁)
                                   (ap inl (P-is-prop p q))
      η (inr ⋆ , l) = 𝟘-elim l

  fact-III : (α ₀ ↓ inr ⋆) ≃ₒ (α ₁ ↓ inr ⋆) → P
  fact-III e = fact-I (≃ₒ-to-fun⁻¹ (α ₀ ↓ inr ⋆) (α ₁ ↓ inr ⋆) e (inl ⋆ , ⋆))

  decidability-if-sup-of-α-discrete : is-discrete ⟨ sup α ⟩ → is-decidable P
  decidability-if-sup-of-α-discrete δ = decidable-↔ (fact-III , fact-II) dec
   where
    r : image (sum-to-ordinals α) → Ordinal 𝓤
    r = restriction (sum-to-ordinals α)
    c : (Σ i ꞉ I , ⟨ α i ⟩) → image (sum-to-ordinals α)
    c = corestriction (sum-to-ordinals α)

    φ : ⟨ sup α ⟩ ≃ image (sum-to-ordinals α)
    φ = sup-is-image-of-sum-to-ordinals α
    f : (Σ i ꞉ I , ⟨ α i ⟩) → ⟨ sup α ⟩
    f = ⌜ φ ⌝⁻¹ ∘ c
    e : ⟨ sup α ⟩ → Ordinal 𝓤
    e = r ∘ ⌜ φ ⌝

    e-is-embedding : is-embedding e
    e-is-embedding =
     ∘-is-embedding (equivs-are-embeddings ⌜ φ ⌝ (⌜⌝-is-equiv φ))
                    (restrictions-are-embeddings (sum-to-ordinals α))
    e-after-f-lemma : e ∘ f ∼ sum-to-ordinals α
    e-after-f-lemma (i , x) =
     (r ∘ ⌜ φ ⌝ ∘ ⌜ φ ⌝⁻¹ ∘ c) (i , x) ＝⟨ h    ⟩
     r (c (i , x))                     ＝⟨refl⟩
     sum-to-ordinals α (i , x)         ∎
      where
       h = ap r (inverses-are-sections ⌜ φ ⌝ (⌜⌝-is-equiv φ) (c (i , x)))

    dec : is-decidable ((α ₀ ↓ inr ⋆) ≃ₒ (α ₁ ↓ inr ⋆))
    dec = decidable-cong γ (δ (f (₀ , inr ⋆)) (f (₁ , inr ⋆)))
     where
      γ = (f (₀ , inr ⋆)     ＝  f (₁ , inr ⋆))     ≃⟨ ⦅1⦆ ⟩
          (e (f (₀ , inr ⋆)) ＝  e (f (₁ , inr ⋆))) ≃⟨ ⦅2⦆ ⟩
          ((α ₀ ↓ inr ⋆)     ＝  (α ₁ ↓ inr ⋆))     ≃⟨ ⦅3⦆ ⟩
          ((α ₀ ↓ inr ⋆)     ≃ₒ (α ₁ ↓ inr ⋆))     ■
       where
        ⦅1⦆ = ≃-sym (embedding-criterion-converse e e-is-embedding
                      (f (₀ , inr ⋆)) (f (₁ , inr ⋆)))
        ⦅2⦆ = ＝-cong _ _ (e-after-f-lemma (₀ , inr ⋆))
                         (e-after-f-lemma (₁ , inr ⋆))
        ⦅3⦆ = UAₒ-≃ (ua 𝓤) (fe _ _) (α ₀ ↓ inr ⋆) (α ₁ ↓ inr ⋆)

\end{code}

Finally, we derive excluded middle from the assumption that discretely-indexed
suprema of trichotomous ordinals are discrete, as announced at the top of this
file.

\begin{code}

 EM-if-Sups-Of-Discretely-Indexed-Trichotomous-Ordinals-Are-Discrete :
  Sups-Of-Discretely-Indexed-Trichotomous-Ordinals-Are-Discrete 𝓤
  → EM 𝓤
 EM-if-Sups-Of-Discretely-Indexed-Trichotomous-Ordinals-Are-Discrete h P i =
  decidability-if-sup-of-α-discrete γ
   where
    open discrete-sup-taboo-construction-II P i
    γ : is-discrete ⟨ sup α ⟩
    γ = h 𝟚 𝟚-is-discrete α α-is-trichotomous

\end{code}
