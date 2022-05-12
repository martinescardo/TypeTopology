Tom de Jong 22nd May 2019

Various lemmas for working with partial elements of a type.
Includes an alternative partial order on the lifting of a type without relying
on full univalence.

Moreover, there are some lemmas on the Kleisli extension for the lifting monad.
In particular, (η ∘ f) ♯ is pointwise equal to 𝓛̇ f.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import SpartanMLTT
open import UF-FunExt
open import UF-Subsingletons

module LiftingMiscelanea-PropExt-FunExt
        (𝓣 : Universe)
        (pe : propext 𝓣)
        (fe : Fun-Ext)
       where

open import UF-Base
open import UF-Equiv
open import UF-Retracts
open import UF-Subsingletons-FunExt

open import Lifting 𝓣
open import LiftingIdentityViaSIP 𝓣
open import LiftingMiscelanea 𝓣
open import LiftingMonad 𝓣

\end{code}

Assuming propositional extensionality for 𝓣 and function extensionality, we can
prove that the lifting of a set is again a set.

\begin{code}

module _ {𝓤 : Universe}
         {X : 𝓤 ̇ }
       where

 open import LiftingUnivalentPrecategory 𝓣 X

 lifting-of-set-is-set : is-set X → is-set (𝓛 X)
 lifting-of-set-is-set i {l} {m} p q  = retract-of-prop r j p q
  where
   r : Σ has-section
   r = (to-Σ-≡ , from-Σ-≡ , tofrom-Σ-≡)
   j : is-prop (Σ (λ p₁ → transport (λ P → (P → X) × is-prop P)
                p₁ (pr₂ l) ≡ pr₂ m))
   j = Σ-is-prop
        (identifications-of-props-are-props pe fe (is-defined m)
         (being-defined-is-prop m) (is-defined l))
        (λ d → ×-is-set (Π-is-set fe λ _ → i)
                        (props-are-sets (being-prop-is-prop fe)))

 \end{code}

 We prefer to work with ⊑' as it yields identifications, which can be transported
 and allow for equational reasoning with ≡⟨ ⟩.
 Moreover, it has the right universe level for use in the Scott model of PCF.

 This duplicates some material from LiftingUnivalentPrecategory. However, we only
 assume propositional extensionality and function extensionality here. We do not
 rely on full univalence.

 \begin{code}

 _⊑'_ : (l m : 𝓛 X) → 𝓤 ⊔ 𝓣 ⁺ ̇
 l ⊑' m = is-defined l → l ≡ m

 ⊑-to-⊑' : {l m : 𝓛 X} → l ⊑ m → l ⊑' m
 ⊑-to-⊑' {l} {m} a d = ⊑-anti pe fe fe (a , b) where
  b : m ⊑ l
  b = c , v where
   c : is-defined m → is-defined l
   c = λ _ → d
   v : (e : is-defined m) → value m e ≡ value l d
   v e = value m e         ≡⟨ ap (value m)
                             (being-defined-is-prop m e (pr₁ a d)) ⟩
         value m (pr₁ a d) ≡⟨ g ⁻¹ ⟩
         value l d         ∎ where
    h : is-defined l → is-defined m
    h = pr₁ a
    g : value l d ≡ value m (pr₁ a d)
    g = pr₂ a d

 ⊑'-to-⊑ : {l m : 𝓛 X} → l ⊑' m → l ⊑ m
 ⊑'-to-⊑ {l} {m} a = ⌜ e ⌝⁻¹ g where
  e : (l ⊑ m) ≃ (is-defined l → l ⊑ m)
  e = ⊑-open fe fe l m
  g : is-defined l → l ⊑ m
  g d = transport (_⊑_ l) (a d) (𝓛-id l)

 ⊑'-is-reflexive : {l : 𝓛 X} → l ⊑' l
 ⊑'-is-reflexive {l} d = refl

 ⊑'-is-transitive : {l m n : 𝓛 X} → l ⊑' m → m ⊑' n → l ⊑' n
 ⊑'-is-transitive {l} {m} {n} a b d = l ≡⟨ a d ⟩
                                      m ≡⟨ b (≡-to-is-defined (a d) d) ⟩
                                      n ∎

 ⊑'-is-antisymmetric : {l m : 𝓛 X} → l ⊑' m → m ⊑' l → l ≡ m
 ⊑'-is-antisymmetric a b = ⊑-anti pe fe fe (⊑'-to-⊑ a , ⊑'-to-⊑ b)

 ⊑'-prop-valued : is-set X → {l m : 𝓛 X} → is-prop (l ⊑' m)
 ⊑'-prop-valued s {l} {m} =
  Π-is-prop fe λ (d : is-defined l) → lifting-of-set-is-set s

 is-defined-η-≡ : {l : 𝓛 X} (d : is-defined l) → l ≡ η (value l d)
 is-defined-η-≡ {l} d =
  ⊑-to-⊑' ((λ _ → ⋆) , λ (e : is-defined l) → value-is-constant l e d) d

 ⋍-to-≡ : {l m : 𝓛 X} → l ⋍ m → l ≡ m
 ⋍-to-≡ {l} {m} (deq , veq) = ⊑-anti pe fe fe (a , b)
  where
   a : l ⊑ m
   a = ⌜ deq ⌝ , happly veq
   b : m ⊑ l
   b = (⌜ deq ⌝⁻¹ , h)
    where
     h : (d : is-defined m) → value m d ≡ value l (⌜ deq ⌝⁻¹ d)
     h d = value m d  ≡⟨ value-is-constant m d d' ⟩
           value m d' ≡⟨ (happly veq e)⁻¹ ⟩
           value l e  ∎
      where
       e : is-defined l
       e = ⌜ deq ⌝⁻¹ d
       d' : is-defined m
       d' = ⌜ deq ⌝ e

module _ {𝓤 : Universe}
         {X : 𝓤 ̇ }
         {𝓥 : Universe}
         {Y : 𝓥 ̇ }
       where

 ♯-is-defined : (f : X → 𝓛 Y) (l : 𝓛 X) → is-defined ((f ♯) l) → is-defined l
 ♯-is-defined f l = pr₁

 ♯-on-total-element : (f : X → 𝓛 Y) {l : 𝓛 X} (d : is-defined l)
                    → (f ♯) l ≡ f (value l d)
 ♯-on-total-element f {l} d =
  (f ♯) l               ≡⟨ ap (f ♯) (is-defined-η-≡ d) ⟩
  (f ♯) (η (value l d)) ≡⟨ ⋍-to-≡ (Kleisli-Law₁ f (value l d)) ⟩
  f (value l d)         ∎

 open import LiftingUnivalentPrecategory 𝓣 Y

 𝓛̇-♯-∼ : (f : X → Y) → (η ∘ f) ♯ ∼ 𝓛̇ f
 𝓛̇-♯-∼ f l = ⊑-anti pe fe fe (a , b)
  where
   a : ((η ∘ f) ♯) l ⊑ (𝓛̇ f) l
   a = p , q
    where
     p : is-defined (((η ∘ f) ♯) l) → is-defined (𝓛̇ f l)
     p = ♯-is-defined (η ∘ f) l
     q : (d : is-defined (((η ∘ f) ♯) l))
       → value (((η ∘ f) ♯) l) d ≡ value (𝓛̇ f l) (♯-is-defined (η ∘ f) l d)
     q d = refl
   b : (𝓛̇ f) l ⊑ ((η ∘ f) ♯) l
   b = r , s
    where
     r : is-defined (𝓛̇ f l) → is-defined (((η ∘ f) ♯) l)
     r d = d , ⋆
     s : (d : is-defined (𝓛̇ f l))
       → value (𝓛̇ f l) d ≡ value (((η ∘ f) ♯) l) (r d)
     s d = refl

\end{code}
