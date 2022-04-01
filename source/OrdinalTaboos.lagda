Tom de Jong, 1 April 2022.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module OrdinalTaboos where

open import DiscreteAndSeparated hiding (𝟚-is-discrete)
open import SpartanMLTT hiding (𝟚 ; ₀ ; ₁)
open import Plus-Properties

open import OrdinalNotions
open import OrdinalsType

open import UF-Equiv
open import UF-ExcludedMiddle
open import UF-FunExt
open import UF-Subsingletons

-----
-- TODO: MOVE THIS

open import UF-EquivalenceExamples

subtype-≃ : {X : 𝓤 ̇  } {Y : X → 𝓥 ̇  }
          → ((x : X) → is-prop (Y x))
          → {x x' : X} {y : Y x} {y' : Y x'}
          → ((x , y) ≡ (x' , y')) ≃ (x ≡ x')
subtype-≃ {𝓤} {𝓥} {X} {Y} i {x} {x'} {y} {y'} =
 ((x , y) ≡ (x' , y'))                   ≃⟨ Σ-≡-≃      ⟩
 (Σ e ꞉ (x ≡ x') , transport Y e y ≡ y') ≃⟨ Σ-cong φ   ⟩
 (x ≡ x') × 𝟙{𝓤}                         ≃⟨ 𝟙-rneutral ⟩
 (x ≡ x')                                ■
  where
   φ : (e : x ≡ x') → (transport Y e y ≡ y') ≃ 𝟙
   φ e = logically-equivalent-props-are-equivalent
          (props-are-sets (i x')) 𝟙-is-prop
          (λ _ → ⋆)
          (λ _ → i x' (transport Y e y) y')

-----

module _ {𝓤 : Universe} where

 𝟚 : 𝓤 ̇
 𝟚 = 𝟙 {𝓤} + 𝟙 {𝓤}

 pattern ₀ = inl ⋆
 pattern ₁ = inr ⋆

 𝟚-is-discrete : is-discrete 𝟚
 𝟚-is-discrete = +-is-discrete 𝟙-is-discrete 𝟙-is-discrete

module ordinal-construction
        (P : 𝓤 ̇  )
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
 ≺-is-transitive ₀ ₁ ₀ u v = v
 ≺-is-transitive ₀ ₁ ₁ u v = u
 ≺-is-transitive ₁ ₀ z u v = 𝟘-elim u
 ≺-is-transitive ₁ ₁ z u v = 𝟘-elim u

 ≺-well-founded-lemma : (y : 𝟚) → y ≺ ₀ → is-accessible _≺_ y
 ≺-well-founded-lemma ₀ l = 𝟘-elim l
 ≺-well-founded-lemma ₁ l = 𝟘-elim l

 ≺-is-well-founded : is-well-founded _≺_
 ≺-is-well-founded ₀ = next ₀ ≺-well-founded-lemma
 ≺-is-well-founded ₁ = next ₁ γ
  where
   γ : (y : 𝟚) → y ≺ ₁ → is-accessible _≺_ y
   γ ₀ l = next ₀ ≺-well-founded-lemma

 ≺-is-extensional : ¬¬ P → is-extensional _≺_
 ≺-is-extensional nnp ₀ ₀ u v = refl
 ≺-is-extensional nnp ₀ ₁ u v = 𝟘-elim (nnp γ)
  where
   γ : ¬ P
   γ p = 𝟘-elim (v ₀ p)
 ≺-is-extensional nnp ₁ ₀ u v = 𝟘-elim (nnp γ)
  where
   γ : ¬ P
   γ p = 𝟘-elim (u ₀ p)
 ≺-is-extensional nnp ₁ ₁ u v = refl

 𝟚≺-ordinal : is-prop P → ¬¬ P → Ordinal 𝓤
 𝟚≺-ordinal i nnp = 𝟚 , _≺_ , ≺-is-prop-valued i   , ≺-is-well-founded
                             , ≺-is-extensional nnp , ≺-is-transitive

 ≺-trichotomous-characterization : is-trichotomous _≺_ ⇔ P
 ≺-trichotomous-characterization = ⦅⇒⦆ , ⦅⇐⦆
  where
   ⦅⇒⦆ : is-trichotomous _≺_ → P
   ⦅⇒⦆ t = lemma (t ₀ ₁)
    where
     lemma : (₀ ≺ ₁) + (₀ ≡ ₁) + (₁ ≺ ₀) → P
     lemma (inl p) = p
     lemma (inr (inl e)) = 𝟘-elim (+disjoint e)
     lemma (inr (inr l)) = 𝟘-elim l
   ⦅⇐⦆ : P → is-trichotomous _≺_
   ⦅⇐⦆ p ₀ ₀ = inr (inl refl)
   ⦅⇐⦆ p ₀ ₁ = inl p
   ⦅⇐⦆ p ₁ ₀ = inr (inr p)
   ⦅⇐⦆ p ₁ ₁ = inr (inl refl)

Every-Discrete-Ordinal-Is-Trichotomous : (𝓤 : Universe) → 𝓤 ⁺ ̇
Every-Discrete-Ordinal-Is-Trichotomous 𝓤 =
   ((α : Ordinal 𝓤) → is-discrete ⟨ α ⟩
                    → is-trichotomous (underlying-order α))

DNE-if-Every-Discrete-Ordinal-Is-Trichotomous :
   Every-Discrete-Ordinal-Is-Trichotomous 𝓤
 → DNE 𝓤
DNE-if-Every-Discrete-Ordinal-Is-Trichotomous h P P-is-prop not-not-P =
 lr-implication ≺-trichotomous-characterization
                  (h (𝟚≺-ordinal P-is-prop not-not-P) (𝟚-is-discrete))
  where
   open ordinal-construction P

EM-if-Every-Discrete-Ordinal-Is-Trichotomous :
   funext 𝓤 𝓤₀
 → Every-Discrete-Ordinal-Is-Trichotomous 𝓤
 → EM 𝓤
EM-if-Every-Discrete-Ordinal-Is-Trichotomous fe h =
 DNE-gives-EM fe (DNE-if-Every-Discrete-Ordinal-Is-Trichotomous h)

------

module ordinal-construction' -- TODO: Rename
        (P : 𝓤 ̇  )
       where

 P' : 𝓤 ̇
 P' = P + 𝟙{𝓤}

 _≺_ : P' → P' → 𝓤 ̇
 inl p ≺ inl q = 𝟘
 inl p ≺ inr ⋆ = 𝟙
 inr ⋆ ≺ inl q = 𝟘
 inr ⋆ ≺ inr ⋆ = 𝟘

 ≺-is-prop-valued : is-prop-valued _≺_
 ≺-is-prop-valued (inl p) (inl q) = 𝟘-is-prop
 ≺-is-prop-valued (inl p) (inr ⋆) = 𝟙-is-prop
 ≺-is-prop-valued (inr ⋆) (inl q) = 𝟘-is-prop
 ≺-is-prop-valued (inr ⋆) (inr ⋆) = 𝟘-is-prop

 ≺-is-transitive : is-transitive _≺_
 ≺-is-transitive (inl p) (inr ⋆) (inl q) u v = v
 ≺-is-transitive (inl p) (inr ⋆) (inr ⋆) u v = ⋆
 ≺-is-transitive (inr ⋆) (inl q) z       u v = 𝟘-elim u
 ≺-is-transitive (inr ⋆) (inr ⋆) z       u v = 𝟘-elim u

 ≺-is-well-founded : is-well-founded _≺_
 ≺-is-well-founded x = next x (IH x)
  where
   IH : (x y : P') → y ≺ x → is-accessible _≺_ y
   IH (inl p) (inl q) l = 𝟘-elim l
   IH (inl p) (inr ⋆) l = 𝟘-elim l
   IH (inr ⋆) (inl q) l = next (inl q) IH'
    where
     IH' : (y : P') → y ≺ inl q → is-accessible _≺_ y
     IH' (inl p) k = 𝟘-elim k
     IH' (inr ⋆) k = 𝟘-elim k

 ≺-is-extensional : is-prop P → is-extensional _≺_
 ≺-is-extensional i (inl p) (inl q) u v = ap inl (i p q)
 ≺-is-extensional i (inl p) (inr ⋆) u v = 𝟘-elim (v (inl p) ⋆)
 ≺-is-extensional i (inr ⋆) (inl q) u v = 𝟘-elim (u (inl q) ⋆)
 ≺-is-extensional i (inr ⋆) (inr ⋆) u v = refl

 P'-ordinal : is-prop P → Ordinal 𝓤
 P'-ordinal i = P' , _≺_ , ≺-is-prop-valued   , ≺-is-well-founded
                         , ≺-is-extensional i , ≺-is-transitive

 ≺-is-trichotomous : is-prop P → is-trichotomous _≺_
 ≺-is-trichotomous i (inl p) (inl q) = inr (inl (ap inl (i p q)))
 ≺-is-trichotomous i (inl p) (inr ⋆) = inl ⋆
 ≺-is-trichotomous i (inr ⋆) (inl q) = inr (inr ⋆)
 ≺-is-trichotomous i (inr ⋆) (inr ⋆) = inr (inl refl)

---

-- TODO: Move to OrdinalsWellOrderArithmetic
module _
        {𝓤 𝓥 𝓦}
        {X : 𝓤 ̇ }
        {Y : 𝓥 ̇ }
        (_<_ : X → X → 𝓦 ̇ )
        (_≺_ : Y → Y → 𝓦 ̇ )
       where

 open import OrdinalsWellOrderArithmetic
 open plus _<_ _≺_

 private
  _⊏_ = order

 +₀-preserves-trichotomy : is-trichotomous _<_
                         → is-trichotomous _≺_
                         → is-trichotomous order
 +₀-preserves-trichotomy s t (inl x) (inl x') = lemma (s x x')
  where
   lemma : (x < x') + (x ≡ x') + (x' < x)
         → inl x ⊏ inl x' + (inl x ≡ inl x') + inl x' ⊏ inl x
   lemma (inl l)       = inl l
   lemma (inr (inl e)) = inr (inl (ap inl e))
   lemma (inr (inr k)) = inr (inr k)
 +₀-preserves-trichotomy s t (inl x) (inr y ) = inl ⋆
 +₀-preserves-trichotomy s t (inr y) (inl x ) = inr (inr ⋆)
 +₀-preserves-trichotomy s t (inr y) (inr y') = lemma (t y y')
  where
   lemma : (y ≺ y') + (y ≡ y') + (y' ≺ y)
         → inr y ⊏ inr y' + (inr y ≡ inr y') + inr y' ⊏ inr y
   lemma (inl l)       = inl l
   lemma (inr (inl e)) = inr (inl (ap inr e))
   lemma (inr (inr k)) = inr (inr k)

open import UF-PropTrunc
open import UF-UA-FunExt
open import UF-Univalence



module _
        (pt  : propositional-truncations-exist)
        (ua : Univalence)
       where

 private
  fe : FunExt
  fe = Univalence-gives-FunExt ua

  fe' : Fun-Ext
  fe' {𝓤} {𝓥} = fe 𝓤 𝓥

  pe : PropExt
  pe = Univalence-gives-PropExt ua

  pe' : Prop-Ext
  pe' {𝓤} = pe 𝓤

 open PropositionalTruncation pt

 open import OrdinalOfOrdinalsSuprema pt ua
 open import OrdinalArithmetic fe
 open import OrdinalOfOrdinals ua

 open import UF-Quotient pt fe' pe'
 open import UF-ImageAndSurjection
 open ImageAndSurjection pt

 module ordinal-construction'' -- TODO: rename
          {𝓤 : Universe}
          (ssq : Small-Set-Quotients 𝓤)
          (P : 𝓤 ̇  )
          (P-is-prop : is-prop P)
         where

   open ordinal-construction' P

   I : 𝓤 ̇
   I = 𝟚 {𝓤}

   α : I → Ordinal 𝓤
   α ₀ = P'-ordinal P-is-prop
   α ₁ = 𝟙ₒ +ₒ 𝟙ₒ

   --TODO: Move and generalize to any proposition?
   𝟙ₒ-is-trichotomous : is-trichotomous {𝓤} {𝓤} (underlying-order 𝟙ₒ)
   𝟙ₒ-is-trichotomous ⋆ ⋆ = inr (inl refl)

   𝟙ₒ+ₒ𝟙ₒ-trichotomous : is-trichotomous {𝓤} {𝓤} (underlying-order (𝟙ₒ +ₒ 𝟙ₒ))
   𝟙ₒ+ₒ𝟙ₒ-trichotomous = +₀-preserves-trichotomy (underlying-order 𝟙ₒ)
                                                 (underlying-order 𝟙ₒ)
                                                 𝟙ₒ-is-trichotomous
                                                 𝟙ₒ-is-trichotomous

   α-is-trichotomous : (i : I) → is-trichotomous (underlying-order (α i))
   α-is-trichotomous ₀ = ≺-is-trichotomous P-is-prop
   α-is-trichotomous ₁ = 𝟙ₒ+ₒ𝟙ₒ-trichotomous

   sup-of-α : Ordinal 𝓤
   sup-of-α = supremum ssq α

   open import UF-Embeddings
   open import DecidableAndDetachable

   -- TODO: Move
   ≺-lemma : (p : P') → p ≺ inr ⋆ → P
   ≺-lemma (inl p) l = p

   -- TODO: Clean up
   decidability-if-sup-of-α-discrete : is-discrete ⟨ sup-of-α ⟩
                                     → decidable P
   decidability-if-sup-of-α-discrete δ = γ
    where
     open construction-using-image α hiding (_≺_ ; ≺-is-prop-valued) -- TODO: Remove this and make σ visible
     x : Ordinal 𝓤
     x = α ₀ ↓ inr ⋆
     y : Ordinal 𝓤
     y = α ₁ ↓ ₁
     x-y-key : P → x ≃ₒ y
     x-y-key p = f , f-op , qinvs-are-equivs f (g , η , ε) , g-op
      where
       f : ⟨ x ⟩ → ⟨ y ⟩
       f _ = (inl ⋆ , ⋆)
       f-op : is-order-preserving x y f
       f-op (inl p , k) (inl q , l) m = 𝟘-elim m
       g : ⟨ y ⟩ → ⟨ x ⟩
       g _ = (inl p , ⋆)
       η : g ∘ f ∼ id
       η (inl q , ⋆) = to-subtype-≡ (λ _ → ≺-is-prop-valued _ _) (ap inl (P-is-prop p q))
       ε : f ∘ g ∼ id
       ε (inl ⋆ , ⋆) = refl
       g-op : is-order-preserving y x g
       g-op (inl ⋆ , ⋆) (inl ⋆ , ⋆) l = 𝟘-elim l
     φ : ⟨ sup-of-α ⟩ ≃ image σ
     φ = supremum-is-image-of-Σ ssq α
     x' : ⟨ sup-of-α ⟩
     x' = ⌜ φ ⌝⁻¹ (corestriction σ (₀ , inr ⋆))
     y' : ⟨ sup-of-α ⟩
     y' = ⌜ φ ⌝⁻¹ (corestriction σ (₁ , ₁))
     foo : (x' ≡ y') ≃ (x ≡ y)
     foo = (x' ≡ y') ≃⟨ embedding-criterion-converse ⌜ φ ⌝⁻¹ (equivs-are-embeddings ⌜ φ ⌝⁻¹ (⌜⌝⁻¹-is-equiv φ)) (corestriction σ (₀ , ₁)) (corestriction σ (₁ , ₁)) ⟩
           (corestriction σ (₀ , inr ⋆) ≡ corestriction σ (₁ , ₁)) ≃⟨ subtype-≃ (λ β → being-in-the-image-is-prop β σ) ⟩
           (x ≡ y) ■
     key : decidable (x ≡ y)
     key = decidable-cong foo (δ x' y')
     point : decidable (x ≡ y) → decidable P
     point (inl  e) = inl (≺-lemma fff ggg)
      where
       a : ⟨ x ⟩
       a = idtofun ⟨ y ⟩ ⟨ x ⟩ (ap ⟨_⟩ (e ⁻¹)) (inl ⋆ , ⋆)
       fff : ⟨ α ₀ ⟩
       fff = pr₁ a
       ggg : fff ≺ inr ⋆
       ggg = pr₂ a
     point (inr ne) = inr (λ p → ne (eqtoidₒ x y (x-y-key p)))
     γ : decidable P
     γ = point key

open import UF-Univalence

module _
        (pt  : propositional-truncations-exist)
        (ua : Univalence)
       where

 private
  fe : FunExt
  fe = Univalence-gives-FunExt ua

  fe' : Fun-Ext
  fe' {𝓤} {𝓥} = fe 𝓤 𝓥

  pe : PropExt
  pe = Univalence-gives-PropExt ua

  pe' : Prop-Ext
  pe' {𝓤} = pe 𝓤

 open import UF-Quotient pt fe' pe'

 open import OrdinalOfOrdinalsSuprema pt ua

 Sups-Of-Discretely-Indexed-Trichotomous-Ordinals-Are-Discrete :
  (𝓤 : Universe) → Small-Set-Quotients 𝓤 → 𝓤 ⁺ ̇
 Sups-Of-Discretely-Indexed-Trichotomous-Ordinals-Are-Discrete 𝓤 ssq =
  (I : 𝓤 ̇  ) → is-discrete I → (α : I → Ordinal 𝓤)
             → ((i : I) → is-trichotomous (underlying-order (α i)))
             → is-discrete ⟨ supremum ssq α ⟩

 EM-if-Sups-Of-Discretely-Indexed-Trichotomous-Ordinals-Are-Discrete :
    (ssq : Small-Set-Quotients 𝓤)
  → Sups-Of-Discretely-Indexed-Trichotomous-Ordinals-Are-Discrete 𝓤 ssq
  → EM 𝓤
 EM-if-Sups-Of-Discretely-Indexed-Trichotomous-Ordinals-Are-Discrete ssq h P i =
  decidability-if-sup-of-α-discrete γ
   where
    open ordinal-construction'' pt ua ssq P i
    γ : is-discrete ⟨ supremum ssq α ⟩
    γ = h 𝟚 𝟚-is-discrete α α-is-trichotomous

\end{code}
