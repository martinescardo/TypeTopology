Tom de Jong, May 2019.
Refactored January 2020, December 2021.
February 2022: Show that pointed dcpos have semidirected and subsingleton
               suprema.

We define dcpos with a least element, typically denoted by ⊥, which are called
pointed dcpos. A map between pointed dcpos is called strict if it preserves
least elements. We show that every isomorphism of dcpos is strict.

Finally, we show that pointed dcpos have semidirected and subsingleton suprema
and that these are preserved by maps that are both strict and Scott continuous.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc

module DomainTheory.Basics.Pointed
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (𝓥 : Universe)
       where

open PropositionalTruncation pt hiding (_∨_)

open import UF.Subsingletons

open import DomainTheory.Basics.Dcpo pt fe 𝓥
open import DomainTheory.Basics.Miscelanea pt fe 𝓥

module _ {𝓤 𝓣 : Universe} where

 DCPO⊥ : (𝓥 ⁺) ⊔ (𝓤 ⁺) ⊔ (𝓣 ⁺) ̇
 DCPO⊥ = Σ 𝓓 ꞉ DCPO {𝓤} {𝓣} , has-least (underlying-order 𝓓)

 _⁻ : DCPO⊥ → DCPO
 _⁻ = pr₁

 ⟪_⟫ : DCPO⊥ → 𝓤 ̇
 ⟪ 𝓓 ⟫ = ⟨ 𝓓 ⁻ ⟩

 underlying-order⊥ : (𝓓 : DCPO⊥) → ⟪ 𝓓 ⟫ → ⟪ 𝓓 ⟫ → 𝓣 ̇
 underlying-order⊥ 𝓓 = underlying-order (𝓓 ⁻)

 syntax underlying-order⊥ 𝓓 x y = x ⊑⟪ 𝓓 ⟫ y

 ⊥ : (𝓓 : DCPO⊥) → ⟨ 𝓓 ⁻ ⟩
 ⊥ (𝓓 , x , p) = x

 ⊥-is-least : (𝓓 : DCPO⊥) → is-least (underlying-order (𝓓 ⁻)) (⊥ 𝓓)
 ⊥-is-least (𝓓 , x , p) = p

 transitivity'' : (𝓓 : DCPO⊥) (x : ⟪ 𝓓 ⟫) {y z : ⟪ 𝓓 ⟫}
               → x ⊑⟪ 𝓓 ⟫ y → y ⊑⟪ 𝓓 ⟫ z → x ⊑⟪ 𝓓 ⟫ z
 transitivity'' 𝓓 = transitivity' (𝓓 ⁻)

 reflexivity' : (𝓓 : DCPO⊥) → reflexive (underlying-order (𝓓 ⁻))
 reflexivity' (D , _) = reflexivity D

 syntax transitivity'' 𝓓 x u v = x ⊑⟪ 𝓓 ⟫[ u ] v
 infixr 0 transitivity''

 syntax reflexivity' 𝓓 x = x ∎⟪ 𝓓 ⟫
 infix 1 reflexivity'

is-a-non-trivial-pointed-dcpo : (𝓓 : DCPO⊥ {𝓤} {𝓣}) → 𝓤 ̇
is-a-non-trivial-pointed-dcpo 𝓓 = ∃ x ꞉ ⟪ 𝓓 ⟫ , x ≠ ⊥ 𝓓

＝-to-⊥-criterion : (𝓓 : DCPO⊥ {𝓤} {𝓣}) {x : ⟪ 𝓓 ⟫} → x ⊑⟪ 𝓓 ⟫ ⊥ 𝓓 → x ＝ ⊥ 𝓓
＝-to-⊥-criterion 𝓓 {x} x-below-⊥ =
 antisymmetry (𝓓 ⁻) x (⊥ 𝓓) x-below-⊥ (⊥-is-least 𝓓 x)

DCPO⊥[_,_] : DCPO⊥ {𝓤} {𝓣} → DCPO⊥ {𝓤'} {𝓣'} → (𝓥 ⁺) ⊔ 𝓤 ⊔ 𝓣 ⊔ 𝓤' ⊔ 𝓣' ̇
DCPO⊥[ 𝓓 , 𝓔 ] = DCPO[ 𝓓 ⁻ , 𝓔 ⁻ ]

is-strict : (𝓓 : DCPO⊥ {𝓤} {𝓣}) (𝓔 : DCPO⊥ {𝓤'} {𝓣'})
          → (⟪ 𝓓 ⟫ → ⟪ 𝓔 ⟫)
          → 𝓤' ̇
is-strict 𝓓 𝓔 f = f (⊥ 𝓓) ＝ ⊥ 𝓔

∘-is-strict : {𝓤'' 𝓣'' : Universe}
              (𝓓 : DCPO⊥ {𝓤} {𝓣}) (𝓔 : DCPO⊥ {𝓤'} {𝓣'})
              (𝓔' : DCPO⊥ {𝓤''} {𝓣''})
              (f : ⟪ 𝓓 ⟫ → ⟪ 𝓔 ⟫) (g : ⟪ 𝓔 ⟫ → ⟪ 𝓔' ⟫)
            → is-strict 𝓓 𝓔 f
            → is-strict 𝓔 𝓔' g
            → is-strict 𝓓 𝓔' (g ∘ f)
∘-is-strict 𝓓 𝓔 𝓔' f g sf sg = ap g sf ∙ sg

being-strict-is-prop : (𝓓 : DCPO⊥ {𝓤} {𝓣}) (𝓔 : DCPO⊥ {𝓤'} {𝓣'})
                       (f : ⟪ 𝓓 ⟫ → ⟪ 𝓔 ⟫)
                     → is-prop (is-strict 𝓓 𝓔 f)
being-strict-is-prop 𝓓 𝓔 f = sethood (𝓔 ⁻)

strictness-criterion : (𝓓 : DCPO⊥ {𝓤} {𝓣}) (𝓔 : DCPO⊥ {𝓤'} {𝓣'})
                       (f : ⟪ 𝓓 ⟫ → ⟪ 𝓔 ⟫)
                     → f (⊥ 𝓓) ⊑⟪ 𝓔 ⟫ ⊥ 𝓔
                     → is-strict 𝓓 𝓔 f
strictness-criterion 𝓓 𝓔 f crit =
 antisymmetry (𝓔 ⁻) (f (⊥ 𝓓)) (⊥ 𝓔) crit (⊥-is-least 𝓔 (f (⊥ 𝓓)))

\end{code}

Defining isomorphisms of pointed dcpos and showing that every isomorphism of
dcpos is automatically strict.

\begin{code}

_≃ᵈᶜᵖᵒ⊥_ : (𝓓 : DCPO⊥ {𝓤} {𝓣}) (𝓔 : DCPO⊥ {𝓤'} {𝓣'}) → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ⊔ 𝓤' ⊔ 𝓣' ̇
𝓓 ≃ᵈᶜᵖᵒ⊥ 𝓔 = Σ f ꞉ (⟨ 𝓓 ⁻ ⟩ → ⟨ 𝓔 ⁻ ⟩) , Σ g ꞉ (⟨ 𝓔 ⁻ ⟩ → ⟨ 𝓓 ⁻ ⟩) ,
                ((d : ⟨ 𝓓 ⁻ ⟩) → g (f d) ＝ d)
               × ((e : ⟨ 𝓔 ⁻ ⟩) → f (g e) ＝ e)
               × is-continuous (𝓓 ⁻) (𝓔 ⁻) f
               × is-continuous (𝓔 ⁻) (𝓓 ⁻) g
               × is-strict 𝓓 𝓔 f
               × is-strict 𝓔 𝓓 g

≃ᵈᶜᵖᵒ⊥-to-≃ᵈᶜᵖᵒ : (𝓓 : DCPO⊥ {𝓤} {𝓣}) (𝓔 : DCPO⊥ {𝓤'} {𝓣'})
                → 𝓓 ≃ᵈᶜᵖᵒ⊥ 𝓔 → (𝓓 ⁻) ≃ᵈᶜᵖᵒ (𝓔 ⁻)
≃ᵈᶜᵖᵒ⊥-to-≃ᵈᶜᵖᵒ 𝓓 𝓔 (f , g , s , r , cf , cg , sf , sg) =
 f , g , s , r , cf , cg

≃ᵈᶜᵖᵒ-to-≃ᵈᶜᵖᵒ⊥ : (𝓓 : DCPO⊥ {𝓤} {𝓣}) (𝓔 : DCPO⊥ {𝓤'} {𝓣'})
                → (𝓓 ⁻) ≃ᵈᶜᵖᵒ (𝓔 ⁻) → 𝓓 ≃ᵈᶜᵖᵒ⊥ 𝓔
≃ᵈᶜᵖᵒ-to-≃ᵈᶜᵖᵒ⊥ 𝓓 𝓔 (f , g , gf , fg , cf , cg) =
 f , g , gf , fg , cf , cg , sf , sg
  where
   sf : is-strict 𝓓 𝓔 f
   sf = antisymmetry (𝓔 ⁻) (f (⊥ 𝓓)) (⊥ 𝓔) γ (⊥-is-least 𝓔 (f (⊥ 𝓓)))
    where
     γ = f (⊥ 𝓓)     ⊑⟨ 𝓔 ⁻ ⟩[ l₁ ]
         f (g (⊥ 𝓔)) ⊑⟨ 𝓔 ⁻ ⟩[ l₂ ]
         ⊥ 𝓔         ∎⟨ 𝓔 ⁻ ⟩
      where
       l₁ = monotone-if-continuous (𝓓 ⁻) (𝓔 ⁻) (f , cf) (⊥ 𝓓) (g (⊥ 𝓔))
             (⊥-is-least 𝓓 (g (⊥ 𝓔)))
       l₂ = ＝-to-⊑ (𝓔 ⁻) (fg (⊥ 𝓔))
   sg : is-strict 𝓔 𝓓 g
   sg = antisymmetry (𝓓 ⁻) (g (⊥ 𝓔)) (⊥ 𝓓) γ (⊥-is-least 𝓓 (g (⊥ 𝓔)))
    where
     γ = g (⊥ 𝓔)     ⊑⟨ 𝓓 ⁻ ⟩[ l₁ ]
         g (f (⊥ 𝓓)) ⊑⟨ 𝓓 ⁻ ⟩[ l₂ ]
         ⊥ 𝓓         ∎⟨ 𝓓 ⁻ ⟩
      where
       l₁ = monotone-if-continuous (𝓔 ⁻) (𝓓 ⁻) (g , cg) (⊥ 𝓔) (f (⊥ 𝓓))
             (⊥-is-least 𝓔 (f (⊥ 𝓓)))
       l₂ = ＝-to-⊑ (𝓓 ⁻) (gf (⊥ 𝓓))

\end{code}

Pointed dcpos have semidirected & subsingleton suprema and these are preserved
by maps that are both strict and continuous.

This is used to prove (in DomainTheory.Lifting.LiftingSet.lagda) that the
lifting yields the free pointed dcpo on a set.

\begin{code}

add-⊥ : (𝓓 : DCPO⊥ {𝓤} {𝓣}) {I : 𝓥 ̇ } (α : I → ⟪ 𝓓 ⟫)
      → (𝟙{𝓥} + I) → ⟪ 𝓓 ⟫
add-⊥ 𝓓 α (inl ⋆) = ⊥ 𝓓
add-⊥ 𝓓 α (inr i) = α i

add-⊥-is-directed : (𝓓 : DCPO⊥ {𝓤} {𝓣}) {I : 𝓥 ̇ } {α : I → ⟪ 𝓓 ⟫}
                  → is-semidirected (underlying-order (𝓓 ⁻)) α
                  → is-Directed (𝓓 ⁻) (add-⊥ 𝓓 α)
add-⊥-is-directed 𝓓 {I} {α} σ = ∣ inl ⋆ ∣ , δ
 where
  δ : is-semidirected (underlying-order (𝓓 ⁻)) (add-⊥ 𝓓 α)
  δ (inl ⋆) a       = ∣ a , ⊥-is-least 𝓓 (add-⊥ 𝓓 α a) ,
                            reflexivity (𝓓 ⁻) (add-⊥ 𝓓 α a) ∣
  δ (inr i) (inl ⋆) = ∣ (inr i) , reflexivity (𝓓 ⁻) (α i)
                                , ⊥-is-least 𝓓 (α i)        ∣
  δ (inr i) (inr j) = ∥∥-functor (λ (k , u , v) → (inr k , u , v)) (σ i j)

adding-⊥-preserves-sup : (𝓓 : DCPO⊥ {𝓤} {𝓣}) {I : 𝓥 ̇ }
                         (α : I → ⟪ 𝓓 ⟫) (x : ⟪ 𝓓 ⟫)
                       → is-sup (underlying-order (𝓓 ⁻)) x α
                       → is-sup (underlying-order (𝓓 ⁻)) x (add-⊥ 𝓓 α)
adding-⊥-preserves-sup 𝓓 {I} α x x-is-sup = x-is-ub , x-is-lb-of-ubs
 where
  x-is-ub : (i : 𝟙 + I) → add-⊥ 𝓓 α i ⊑⟪ 𝓓 ⟫ x
  x-is-ub (inl ⋆) = ⊥-is-least 𝓓 x
  x-is-ub (inr i) = sup-is-upperbound (underlying-order (𝓓 ⁻)) x-is-sup i
  x-is-lb-of-ubs : is-lowerbound-of-upperbounds (underlying-order (𝓓 ⁻))
                    x (add-⊥ 𝓓 α)
  x-is-lb-of-ubs y y-is-ub = sup-is-lowerbound-of-upperbounds
                              (underlying-order (𝓓 ⁻)) x-is-sup y
                              (λ i → y-is-ub (inr i))

adding-⊥-reflects-sup : (𝓓 : DCPO⊥ {𝓤} {𝓣}) {I : 𝓥 ̇ }
                        (α : I → ⟪ 𝓓 ⟫) (x : ⟪ 𝓓 ⟫)
                      → is-sup (underlying-order (𝓓 ⁻)) x (add-⊥ 𝓓 α)
                      → is-sup (underlying-order (𝓓 ⁻)) x α
adding-⊥-reflects-sup 𝓓 {I} α x x-is-sup = x-is-ub , x-is-lb-of-ubs
 where
  x-is-ub : (i : I) → α i ⊑⟪ 𝓓 ⟫ x
  x-is-ub i = sup-is-upperbound (underlying-order (𝓓 ⁻)) x-is-sup (inr i)
  x-is-lb-of-ubs : is-lowerbound-of-upperbounds (underlying-order (𝓓 ⁻)) x α
  x-is-lb-of-ubs y y-is-ub = sup-is-lowerbound-of-upperbounds
                              (underlying-order (𝓓 ⁻)) x-is-sup y
                              h
   where
    h : is-upperbound (underlying-order (𝓓 ⁻)) y (add-⊥ 𝓓 α)
    h (inl ⋆) = ⊥-is-least 𝓓 y
    h (inr i) = y-is-ub i

semidirected-complete-if-pointed : (𝓓 : DCPO⊥ {𝓤} {𝓣}) {I : 𝓥 ̇ } {α : I → ⟪ 𝓓 ⟫}
                                 → is-semidirected (underlying-order (𝓓 ⁻)) α
                                 → has-sup (underlying-order (𝓓 ⁻)) α
semidirected-complete-if-pointed 𝓓 {I} {α} σ = x , x-is-sup
 where
  δ : is-Directed (𝓓 ⁻) (add-⊥ 𝓓 α)
  δ = add-⊥-is-directed 𝓓 σ
  x : ⟪ 𝓓 ⟫
  x = ∐ (𝓓 ⁻) δ
  x-is-sup : is-sup (underlying-order (𝓓 ⁻)) x α
  x-is-sup = adding-⊥-reflects-sup 𝓓 α x (∐-is-sup (𝓓 ⁻) δ)

pointed-if-semidirected-complete : (𝓓 : DCPO {𝓤} {𝓣})
                                 → ({I : 𝓥 ̇ } {α : I → ⟨ 𝓓 ⟩}
                                       → is-semidirected (underlying-order 𝓓) α
                                       → has-sup (underlying-order 𝓓) α)
                                 → has-least (underlying-order 𝓓)
pointed-if-semidirected-complete 𝓓 c = x , x-is-least
 where
  α : 𝟘 → ⟨ 𝓓 ⟩
  α = 𝟘-elim
  σ : is-semidirected (underlying-order 𝓓) α
  σ = 𝟘-induction
  x : ⟨ 𝓓 ⟩
  x = the-sup (underlying-order 𝓓) (c σ)
  x-is-least : is-least (underlying-order 𝓓) x
  x-is-least y =
   sup-is-lowerbound-of-upperbounds
    (underlying-order 𝓓)
    (sup-property (underlying-order 𝓓) (c σ))
    y 𝟘-induction

∐ˢᵈ : (𝓓 : DCPO⊥ {𝓤} {𝓣}) {I : 𝓥 ̇ } {α : I → ⟪ 𝓓 ⟫}
    → is-semidirected (underlying-order (𝓓 ⁻)) α → ⟪ 𝓓 ⟫
∐ˢᵈ 𝓓 {I} {α} σ = pr₁ (semidirected-complete-if-pointed 𝓓 σ)

∐ˢᵈ-in-terms-of-∐ : (𝓓 : DCPO⊥ {𝓤} {𝓣}) {I : 𝓥 ̇ } {α : I → ⟪ 𝓓 ⟫}
                    (σ : is-semidirected (underlying-order (𝓓 ⁻)) α)
                  → ∐ˢᵈ 𝓓 σ ＝ ∐ (𝓓 ⁻) (add-⊥-is-directed 𝓓 σ)
∐ˢᵈ-in-terms-of-∐ 𝓓 {I} {α} σ = refl

preserves-semidirected-sups-if-continuous-and-strict :
   (𝓓 : DCPO⊥ {𝓤} {𝓣}) (𝓔 : DCPO⊥ {𝓤'} {𝓣'})
   (f : ⟪ 𝓓 ⟫ → ⟪ 𝓔 ⟫)
 → is-continuous (𝓓 ⁻) (𝓔 ⁻) f
 → is-strict 𝓓 𝓔 f
 → {I : 𝓥 ̇ } {α : I → ⟪ 𝓓 ⟫}
 → (σ : is-semidirected (underlying-order (𝓓 ⁻)) α)
 → is-sup (underlying-order (𝓔 ⁻)) (f (∐ˢᵈ 𝓓 σ)) (f ∘ α)
preserves-semidirected-sups-if-continuous-and-strict 𝓓 𝓔 f con str {I} {α} σ =
 ub , lb-of-ubs
 where
  δ : is-Directed (𝓓 ⁻) (add-⊥ 𝓓 α)
  δ = add-⊥-is-directed 𝓓 σ
  claim₁ : is-sup (underlying-order (𝓔 ⁻)) (f (∐ (𝓓 ⁻) δ))
            (f ∘ add-⊥ 𝓓 α)
  claim₁ = con (𝟙 + I) (add-⊥ 𝓓 α) (add-⊥-is-directed 𝓓 σ)
  claim₂ : is-sup (underlying-order (𝓔 ⁻)) (f (∐ˢᵈ 𝓓 σ))
            (f ∘ add-⊥ 𝓓 α)
  claim₂ = transport⁻¹
            (λ - → is-sup (underlying-order (𝓔 ⁻)) (f -) (f ∘ (add-⊥ 𝓓 α)))
            (∐ˢᵈ-in-terms-of-∐ 𝓓 σ) claim₁
  ub : (i : I) → f (α i) ⊑⟪ 𝓔 ⟫ f (∐ˢᵈ 𝓓 σ)
  ub i = sup-is-upperbound (underlying-order (𝓔 ⁻)) claim₂ (inr i)
  lb-of-ubs : is-lowerbound-of-upperbounds (underlying-order (𝓔 ⁻)) (f (∐ˢᵈ 𝓓 σ))
                (f ∘ α)
  lb-of-ubs y y-is-ub = sup-is-lowerbound-of-upperbounds (underlying-order (𝓔 ⁻))
                         claim₂ y h
   where
    h : is-upperbound (underlying-order (𝓔 ⁻)) y (f ∘ add-⊥ 𝓓 α)
    h (inl ⋆) = f (⊥ 𝓓) ⊑⟪ 𝓔 ⟫[ ＝-to-⊑ (𝓔 ⁻) str ]
                ⊥ 𝓔     ⊑⟪ 𝓔 ⟫[ ⊥-is-least 𝓔 y ]
                y       ∎⟪ 𝓔 ⟫
    h (inr i) = y-is-ub i

subsingleton-indexed-is-semidirected : (𝓓 : DCPO {𝓤} {𝓣})
                                       {I : 𝓥 ̇ } (α : I → ⟨ 𝓓 ⟩)
                                     → is-prop I
                                     → is-semidirected (underlying-order 𝓓) α
subsingleton-indexed-is-semidirected 𝓓 α ρ i j = ∣ i , r , r' ∣
  where
   r : α i ⊑⟨ 𝓓 ⟩ α i
   r = reflexivity 𝓓 (α i)
   r' : α j ⊑⟨ 𝓓 ⟩ α i
   r' = transport (λ k → α k ⊑⟨ 𝓓 ⟩ α i) (ρ i j) r

subsingleton-complete-if-pointed : (𝓓 : DCPO⊥ {𝓤} {𝓣}) {I : 𝓥 ̇ } (α : I → ⟪ 𝓓 ⟫)
                                 → is-prop I
                                 → has-sup (underlying-order (𝓓 ⁻)) α
subsingleton-complete-if-pointed 𝓓 α ρ =
 semidirected-complete-if-pointed 𝓓 σ
  where
   σ : is-semidirected (underlying-order (𝓓 ⁻)) α
   σ = subsingleton-indexed-is-semidirected (𝓓 ⁻) α ρ

∐ˢˢ : (𝓓 : DCPO⊥ {𝓤} {𝓣}) {I : 𝓥 ̇ } (α : I → ⟪ 𝓓 ⟫)
    → is-prop I → ⟪ 𝓓 ⟫
∐ˢˢ 𝓓 {I} α ρ = pr₁ (subsingleton-complete-if-pointed 𝓓 α ρ)

∐ˢˢ-in-terms-of-∐ˢᵈ : (𝓓 : DCPO⊥ {𝓤} {𝓣}) {I : 𝓥 ̇ } {α : I → ⟪ 𝓓 ⟫}
                      (ρ : is-prop I)
                    → ∐ˢˢ 𝓓 α ρ
                    ＝ ∐ˢᵈ 𝓓
                       (subsingleton-indexed-is-semidirected (𝓓 ⁻) α ρ)
∐ˢˢ-in-terms-of-∐ˢᵈ 𝓓 {I} {α} σ = refl

preserves-subsingleton-sups-if-continuous-and-strict :
   (𝓓 : DCPO⊥ {𝓤} {𝓣}) (𝓔 : DCPO⊥ {𝓤'} {𝓣'})
   (f : ⟪ 𝓓 ⟫ → ⟪ 𝓔 ⟫)
 → is-continuous (𝓓 ⁻) (𝓔 ⁻) f
 → is-strict 𝓓 𝓔 f
 → {I : 𝓥 ̇ } (α : I → ⟪ 𝓓 ⟫)
 → (ρ : is-prop I)
 → is-sup (underlying-order (𝓔 ⁻)) (f (∐ˢˢ 𝓓 α ρ)) (f ∘ α)
preserves-subsingleton-sups-if-continuous-and-strict 𝓓 𝓔 f con str α ρ =
 preserves-semidirected-sups-if-continuous-and-strict 𝓓 𝓔 f con str
  (subsingleton-indexed-is-semidirected (𝓓 ⁻) α ρ)

∐ˢˢ-is-upperbound : (𝓓 : DCPO⊥ {𝓤} {𝓣}) {I : 𝓥 ̇ } (α : I → ⟪ 𝓓 ⟫)
                    (ρ : is-prop I)
                  → is-upperbound
                     (underlying-order (𝓓 ⁻)) (∐ˢˢ 𝓓 α ρ) α
∐ˢˢ-is-upperbound 𝓓 {I} α ρ i = ∐-is-upperbound (𝓓 ⁻) δ (inr i)
 where
  δ : is-Directed (𝓓 ⁻) (add-⊥ 𝓓 α)
  δ = add-⊥-is-directed 𝓓 (subsingleton-indexed-is-semidirected (𝓓 ⁻) α ρ)

∐ˢˢ-is-lowerbound-of-upperbounds : (𝓓 : DCPO⊥ {𝓤} {𝓣}) {I : 𝓥 ̇ } (α : I → ⟪ 𝓓 ⟫)
                                   (ρ : is-prop I)
                                 → is-lowerbound-of-upperbounds
                                    (underlying-order (𝓓 ⁻)) (∐ˢˢ 𝓓 α ρ) α
∐ˢˢ-is-lowerbound-of-upperbounds 𝓓 {I} α ρ y y-is-ub =
 ∐-is-lowerbound-of-upperbounds (𝓓 ⁻) δ y h
  where
   δ : is-Directed (𝓓 ⁻) (add-⊥ 𝓓 α)
   δ = add-⊥-is-directed 𝓓 (subsingleton-indexed-is-semidirected (𝓓 ⁻) α ρ)
   h : (i : 𝟙 + I) → add-⊥ 𝓓 α i ⊑⟪ 𝓓 ⟫ y
   h (inl ⋆) = ⊥-is-least 𝓓 y
   h (inr i) = y-is-ub i

∐ˢˢ-is-sup : (𝓓 : DCPO⊥ {𝓤} {𝓣}) {I : 𝓥 ̇ } (α : I → ⟪ 𝓓 ⟫) (ρ : is-prop I)
           → is-sup (underlying-order (𝓓 ⁻)) (∐ˢˢ 𝓓 α ρ) α
∐ˢˢ-is-sup 𝓓 α ρ = ∐ˢˢ-is-upperbound 𝓓 α ρ
                 , ∐ˢˢ-is-lowerbound-of-upperbounds 𝓓 α ρ

∐ˢˢ-＝-if-continuous-and-strict : (𝓓 : DCPO⊥ {𝓤} {𝓣}) (𝓔 : DCPO⊥ {𝓤'} {𝓣'})
                                 (f : ⟪ 𝓓 ⟫ → ⟪ 𝓔 ⟫)
                               → is-continuous (𝓓 ⁻) (𝓔 ⁻) f
                               → is-strict 𝓓 𝓔 f
                               → {I : 𝓥 ̇ } (α : I → ⟪ 𝓓 ⟫)
                               → (ρ : is-prop I)
                               → f (∐ˢˢ 𝓓 α ρ) ＝ ∐ˢˢ 𝓔 (f ∘ α) ρ
∐ˢˢ-＝-if-continuous-and-strict 𝓓 𝓔 f con str α ρ =
 sups-are-unique
  (underlying-order (𝓔 ⁻))
  (pr₁ (axioms-of-dcpo (𝓔 ⁻))) (f ∘ α)
  (preserves-subsingleton-sups-if-continuous-and-strict 𝓓 𝓔 f con str α ρ)
  (∐ˢˢ-is-sup 𝓔 (f ∘ α) ρ)

∐ˢˢ-family-＝ : (𝓓 : DCPO⊥ {𝓤} {𝓣}) {I : 𝓥 ̇ } {α β : I → ⟪ 𝓓 ⟫} (ρ : is-prop I)
             → α ＝ β
             → ∐ˢˢ 𝓓 α ρ ＝ ∐ˢˢ 𝓓 β ρ
∐ˢˢ-family-＝ 𝓓 ρ refl = refl

∐ˢˢ-＝-if-domain-holds : (𝓓 : DCPO⊥ {𝓤} {𝓣}) {I : 𝓥 ̇ }
                         {α : I → ⟪ 𝓓 ⟫} (ρ : is-prop I)
                       → (i : I) → ∐ˢˢ 𝓓 α ρ ＝ α i
∐ˢˢ-＝-if-domain-holds 𝓓 {I} {α} ρ i =
 antisymmetry (𝓓 ⁻) (∐ˢˢ 𝓓 α ρ) (α i)
  (∐ˢˢ-is-lowerbound-of-upperbounds 𝓓 α ρ (α i) l)
  (∐ˢˢ-is-upperbound 𝓓 α ρ i)
   where
    l : (j : I) → α j ⊑⟪ 𝓓 ⟫ α i
    l j = transport (λ - → α - ⊑⟪ 𝓓 ⟫ α i) (ρ i j) (reflexivity (𝓓 ⁻) (α i))

\end{code}
