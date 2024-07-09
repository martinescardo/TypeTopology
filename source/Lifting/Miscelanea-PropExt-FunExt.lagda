Tom de Jong 22nd May 2019

Various lemmas for working with partial elements of a type.
Includes an alternative partial order on the lifting of a type without relying
on full univalence.

Moreover, there are some lemmas on the Kleisli extension for the lifting monad.
In particular, (η ∘ f) ♯ is pointwise equal to 𝓛̇ f.

Added 22 June 2024.
Excluded middle holds if and only if the lifting discretely adds a single point,
viz. 𝓛 X ≃ 𝟙 + X.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.Subsingletons

module Lifting.Miscelanea-PropExt-FunExt
        (𝓣 : Universe)
        (pe : propext 𝓣)
        (fe : Fun-Ext)
       where

open import Lifting.Construction 𝓣
open import Lifting.IdentityViaSIP 𝓣
open import Lifting.Miscelanea 𝓣
open import Lifting.Monad 𝓣

open import NotionsOfDecidability.DecidableClassifier

open import UF.Base
open import UF.ClassicalLogic
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.Retracts
open import UF.Sets
open import UF.Sets-Properties
open import UF.Subsingletons-FunExt
open import UF.Subsingletons-Properties
open import UF.SubtypeClassifier hiding (⊥)

\end{code}

Assuming propositional extensionality for 𝓣 and function extensionality, we can
prove that the lifting of a set is again a set.

\begin{code}

module _ {𝓤 : Universe}
         {X : 𝓤 ̇ }
       where

 open import Lifting.UnivalentPrecategory 𝓣 X

 lifting-of-set-is-set : is-set X → is-set (𝓛 X)
 lifting-of-set-is-set i {l} {m} p q  = retract-of-prop r j p q
  where
   r : Σ has-section
   r = (to-Σ-＝ , from-Σ-＝ , tofrom-Σ-＝)
   j : is-prop (Σ (λ p₁ → transport (λ P → (P → X) × is-prop P)
                p₁ (pr₂ l) ＝ pr₂ m))
   j = Σ-is-prop
        (identifications-with-props-are-props pe fe (is-defined m)
         (being-defined-is-prop m) (is-defined l))
        (λ d → ×-is-set (Π-is-set fe λ _ → i)
                        (props-are-sets (being-prop-is-prop fe)))

 \end{code}

 We prefer to work with ⊑' as it yields identifications, which can be transported
 and allow for equational reasoning with ＝⟨ ⟩.
 Moreover, it has the right universe level for use in the Scott model of PCF.

 This duplicates some material from LiftingUnivalentPrecategory. However, we only
 assume propositional extensionality and function extensionality here. We do not
 rely on full univalence.

 \begin{code}

 _⊑'_ : (l m : 𝓛 X) → 𝓤 ⊔ 𝓣 ⁺ ̇
 l ⊑' m = is-defined l → l ＝ m

 ⊑-to-⊑' : {l m : 𝓛 X} → l ⊑ m → l ⊑' m
 ⊑-to-⊑' {l} {m} a d = ⊑-anti pe fe fe (a , b) where
  b : m ⊑ l
  b = c , v where
   c : is-defined m → is-defined l
   c = λ _ → d
   v : (e : is-defined m) → value m e ＝ value l d
   v e = value m e         ＝⟨ ap (value m)
                             (being-defined-is-prop m e (pr₁ a d)) ⟩
         value m (pr₁ a d) ＝⟨ g ⁻¹ ⟩
         value l d         ∎ where
    h : is-defined l → is-defined m
    h = pr₁ a
    g : value l d ＝ value m (pr₁ a d)
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
 ⊑'-is-transitive {l} {m} {n} a b d = l ＝⟨ a d ⟩
                                      m ＝⟨ b (＝-to-is-defined (a d) d) ⟩
                                      n ∎

 ⊑'-is-antisymmetric : {l m : 𝓛 X} → l ⊑' m → m ⊑' l → l ＝ m
 ⊑'-is-antisymmetric a b = ⊑-anti pe fe fe (⊑'-to-⊑ a , ⊑'-to-⊑ b)

 ⊑'-prop-valued : is-set X → {l m : 𝓛 X} → is-prop (l ⊑' m)
 ⊑'-prop-valued s {l} {m} =
  Π-is-prop fe λ (d : is-defined l) → lifting-of-set-is-set s

 not-defined-⊥-＝ : {l : 𝓛 X} → ¬ (is-defined l) → l ＝ ⊥
 not-defined-⊥-＝ {l} nd =
  ⊑-anti pe fe fe
         (((λ d → 𝟘-elim (nd d)) , (λ d → 𝟘-elim (nd d))) ,
         𝟘-elim , 𝟘-induction)

 is-defined-η-＝ : {l : 𝓛 X} (d : is-defined l) → l ＝ η (value l d)
 is-defined-η-＝ {l} d =
  ⊑-to-⊑' ((λ _ → ⋆) , λ (e : is-defined l) → value-is-constant l e d) d

 ＝-to-⋍ : {l m : 𝓛 X} → l ＝ m → l ⋍ m
 ＝-to-⋍ {l} {m} refl = ≃-refl (is-defined l) , refl

 ⋍-to-＝ : {l m : 𝓛 X} → l ⋍ m → l ＝ m
 ⋍-to-＝ {l} {m} (deq , veq) = ⊑-anti pe fe fe (a , b)
  where
   a : l ⊑ m
   a = ⌜ deq ⌝ , happly veq
   b : m ⊑ l
   b = (⌜ deq ⌝⁻¹ , h)
    where
     h : (d : is-defined m) → value m d ＝ value l (⌜ deq ⌝⁻¹ d)
     h d = value m d  ＝⟨ value-is-constant m d d' ⟩
           value m d' ＝⟨ (happly veq e)⁻¹ ⟩
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
                    → (f ♯) l ＝ f (value l d)
 ♯-on-total-element f {l} d =
  (f ♯) l               ＝⟨ ap (f ♯) (is-defined-η-＝ d) ⟩
  (f ♯) (η (value l d)) ＝⟨ ⋍-to-＝ (Kleisli-Law₁ f (value l d)) ⟩
  f (value l d)         ∎

 open import Lifting.UnivalentPrecategory 𝓣 Y

 𝓛̇-♯-∼ : (f : X → Y) → (η ∘ f) ♯ ∼ 𝓛̇ f
 𝓛̇-♯-∼ f l = ⊑-anti pe fe fe (a , b)
  where
   a : ((η ∘ f) ♯) l ⊑ (𝓛̇ f) l
   a = p , q
    where
     p : is-defined (((η ∘ f) ♯) l) → is-defined (𝓛̇ f l)
     p = ♯-is-defined (η ∘ f) l
     q : (d : is-defined (((η ∘ f) ♯) l))
       → value (((η ∘ f) ♯) l) d ＝ value (𝓛̇ f l) (♯-is-defined (η ∘ f) l d)
     q d = refl
   b : (𝓛̇ f) l ⊑ ((η ∘ f) ♯) l
   b = r , s
    where
     r : is-defined (𝓛̇ f l) → is-defined (((η ∘ f) ♯) l)
     r d = d , ⋆
     s : (d : is-defined (𝓛̇ f l))
       → value (𝓛̇ f l) d ＝ value (((η ∘ f) ♯) l) (r d)
     s d = refl

\end{code}

Added 22 June 2024.
Excluded middle holds if and only if the lifting discretely adds a single point,
viz. 𝓛 X ≃ 𝟙 + X.

\begin{code}

lifting-of-𝟙-is-Ω : 𝓛 (𝟙{𝓤}) ≃ Ω 𝓣
lifting-of-𝟙-is-Ω =
 𝓛 𝟙                         ≃⟨ Σ-cong (λ P → ×-cong (→𝟙 fe) 𝕚𝕕) ⟩
 (Σ P ꞉ 𝓣 ̇  , 𝟙 × is-prop P) ≃⟨ Σ-cong (λ P → 𝟙-lneutral) ⟩
 Ω 𝓣                         ■

EM-gives-classical-lifting : (X : 𝓤 ̇  ) → EM 𝓣 → 𝓛 X ≃ (𝟙{𝓤} + X)
EM-gives-classical-lifting {𝓤} X em =
 𝓛 X                                 ≃⟨ I   ⟩
 (Σ P ꞉ 𝓣 ̇  , is-prop P × (P → X))   ≃⟨ II  ⟩
 (Σ P ꞉ Ω 𝓣 , (P holds → X))         ≃⟨ III ⟩
 (Σ b ꞉ 𝟚 , (ι b holds → X))         ≃⟨ IV  ⟩
 (Σ b ꞉ 𝟙 + 𝟙 , (ι (e b) holds → X)) ≃⟨ V   ⟩
 (𝟙 × (𝟘 → X)) + (𝟙 × (𝟙 → X))       ≃⟨ VI  ⟩
 (𝟘 → X) + (𝟙 → X)                   ≃⟨ VII ⟩
 (𝟙 + X)                             ■
  where
   ι : 𝟚 → Ω 𝓣
   ι = inclusion-of-booleans
   e : 𝟙{𝓤} + 𝟙{𝓤} → 𝟚
   e = ⌜ 𝟚-≃-𝟙+𝟙 ⌝⁻¹

   I   = Σ-cong (λ _ → ×-comm)
   II  = ≃-sym Σ-assoc
   III = ≃-sym (Σ-change-of-variable-≃ _
                 (EM-gives-𝟚-is-the-type-of-propositions fe pe em))
   IV  = ≃-sym (Σ-change-of-variable-≃ _ (≃-sym 𝟚-≃-𝟙+𝟙))
   V   = ≃-sym (Σ+-split 𝟙 𝟙 (λ b → ι (e b) holds → X))
   VI  = +-cong 𝟙-lneutral 𝟙-lneutral
   VII = +-cong (≃-sym (𝟘→ fe)) (≃-sym (𝟙→ fe))

classical-lifting-of-𝟙-gives-EM : 𝓛 (𝟙{𝓤}) ≃ (𝟙{𝓤} + 𝟙{𝓤}) → EM 𝓣
classical-lifting-of-𝟙-gives-EM e =
 𝟚-is-the-type-of-propositions-gives-EM fe pe I
  where
   I = 𝟚     ≃⟨ 𝟚-≃-𝟙+𝟙 ⟩
       𝟙 + 𝟙 ≃⟨ ≃-sym e ⟩
       𝓛 𝟙   ≃⟨ lifting-of-𝟙-is-Ω ⟩
       Ω 𝓣   ■

classical-lifting-gives-EM : ((X : 𝓤 ̇  ) → 𝓛 X ≃ 𝟙{𝓤} + X) → EM 𝓣
classical-lifting-gives-EM h = classical-lifting-of-𝟙-gives-EM (h 𝟙)

\end{code}
