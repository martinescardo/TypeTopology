Tom de Jong, 28 October 2022 - 7 November 2022

In collaboration with Nicolai Kraus, Fredrik Norvall Forsberg and Chuangjie Xu.

TO DO: Add pointers to literature on ordinals in constructive set theory (Aczel─Rathjen, Powell'75)

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline --experimental-lossy-unification #-}

open import MLTT.Spartan

open import UF.PropTrunc
open import UF.Univalence

module Ordinals.CumulativeHierarchy
        (pt : propositional-truncations-exist)
        (ua : Univalence)
        (𝓤 : Universe)
       where

open PropositionalTruncation pt

open import UF.Base hiding (_≈_)
open import UF.Equiv
open import UF.FunExt
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.UA-FunExt

private
 fe : Fun-Ext
 fe = Univalence-gives-Fun-Ext ua

 fe' : FunExt
 fe' _ _ = fe

 pe : Prop-Ext
 pe = Univalence-gives-Prop-Ext ua

open import Ordinals.Notions
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.Type hiding (Ord)

open import UF.CumulativeHierarchy pt fe pe

module _
        (ch : cumulative-hierarchy-exists 𝓤)
       where

 open cumulative-hierarchy-exists ch

 is-transitive-set : 𝕍 → 𝓤 ⁺ ̇
 is-transitive-set x = (u : 𝕍) (v : 𝕍) → u ∈ x → v ∈ u → v ∈ x

 being-transitive-set-is-prop : {x : 𝕍} → is-prop (is-transitive-set x)
 being-transitive-set-is-prop = Π₄-is-prop fe (λ _ _ _ _ → ∈-is-prop-valued)

 is-set-theoretic-ordinal : 𝕍 → 𝓤 ⁺ ̇
 is-set-theoretic-ordinal x = is-transitive-set x
                            × ((y : 𝕍) → y ∈ x → is-transitive-set y)

 being-set-theoretic-ordinal-is-prop : {x : 𝕍} → is-prop (is-set-theoretic-ordinal x)
 being-set-theoretic-ordinal-is-prop =
  ×-is-prop being-transitive-set-is-prop
            (Π₂-is-prop fe (λ _ _ → being-transitive-set-is-prop))

 transitive-set-if-set-theoretic-ordinal : {x : 𝕍}
                                         → is-set-theoretic-ordinal x
                                         → is-transitive-set x
 transitive-set-if-set-theoretic-ordinal = pr₁

 transitive-set-if-element-of-set-theoretic-ordinal : {x : 𝕍}
                                                    → is-set-theoretic-ordinal x
                                                    → {y : 𝕍} → y ∈ x
                                                    → is-transitive-set y
 transitive-set-if-element-of-set-theoretic-ordinal σ {y} m = pr₂ σ y m

 being-set-theoretic-ordinal-is-hereditary : {x : 𝕍} → is-set-theoretic-ordinal x
                                           → {y : 𝕍}
                                           → y ∈ x → is-set-theoretic-ordinal y
 being-set-theoretic-ordinal-is-hereditary {x} (t , τ) {y} m =
  τ y m , (λ z n → τ z (t y z m n))

 𝕍ᵒʳᵈ : 𝓤 ⁺ ̇
 𝕍ᵒʳᵈ = Σ x ꞉ 𝕍 , is-set-theoretic-ordinal x

 𝕍ᵒʳᵈ-is-subtype : {x y : 𝕍ᵒʳᵈ} → pr₁ x ＝ pr₁ y → x ＝ y
 𝕍ᵒʳᵈ-is-subtype = to-subtype-＝ (λ _ → being-set-theoretic-ordinal-is-prop)

 _∈ᵒʳᵈ_ : 𝕍ᵒʳᵈ → 𝕍ᵒʳᵈ → 𝓤 ⁺  ̇
 _∈ᵒʳᵈ_ (x , _) (y , _) = x ∈ y

 ∈ᵒʳᵈ-is-extensional : is-extensional _∈ᵒʳᵈ_
 ∈ᵒʳᵈ-is-extensional (x , u) (y , v) s t =
  𝕍ᵒʳᵈ-is-subtype
   (∈-extensionality
     x y
     (λ z m → s (z , being-set-theoretic-ordinal-is-hereditary u m) m)
     (λ z m → t (z , being-set-theoretic-ordinal-is-hereditary v m) m))

 ∈ᵒʳᵈ-is-transitive : is-transitive _∈ᵒʳᵈ_
 ∈ᵒʳᵈ-is-transitive (x , _) (y , _) (z , τ) x-in-y y-in-z =
  transitive-set-if-set-theoretic-ordinal τ y x y-in-z x-in-y

 ∈-is-well-founded : is-well-founded _∈_
 ∈-is-well-founded = ∈-induction (is-accessible _∈_)
                                 (λ x → accessibility-is-prop _∈_ fe' x)
                                 (λ x IH → step IH)

 ∈ᵒʳᵈ-is-well-founded : is-well-founded _∈ᵒʳᵈ_
 ∈ᵒʳᵈ-is-well-founded = transfinite-induction-converse _∈ᵒʳᵈ_ W
  where
   W : Well-founded _∈ᵒʳᵈ_
   W P IH = (λ (x , σ) → Q-holds-everywhere x σ)
    where
     Q : 𝕍 → 𝓤 ⁺ ̇
     Q x = (σ : is-set-theoretic-ordinal x) → P (x , σ)
     Q-holds-everywhere : (x : 𝕍) → Q x
     Q-holds-everywhere = transfinite-induction _∈_ ∈-is-well-founded Q f
      where
       f : (x : 𝕍) → ((y : 𝕍) → y ∈ x → Q y) → Q x
       f x IH' σ = IH (x , σ) g
        where
         g : (y : 𝕍ᵒʳᵈ) → y ∈ᵒʳᵈ (x , σ) → P y
         g (y , τ) y-in-x = IH' y y-in-x τ

 𝕍ᴼᴿᴰ : Ordinal (𝓤 ⁺)
 𝕍ᴼᴿᴰ = 𝕍ᵒʳᵈ , _∈ᵒʳᵈ_
             , (λ x y → ∈-is-prop-valued)
             , ∈ᵒʳᵈ-is-well-founded
             , ∈ᵒʳᵈ-is-extensional
             , ∈ᵒʳᵈ-is-transitive

 private
  Ord : 𝓤 ⁺ ̇
  Ord = Ordinal 𝓤

 Ord-to-𝕍 : Ord → 𝕍
 Ord-to-𝕍 = transfinite-recursion-on-OO 𝕍 (λ α f → 𝕍-set f)

 Ord-to-𝕍-behaviour : (α : Ord) → Ord-to-𝕍 α ＝ 𝕍-set (λ a → Ord-to-𝕍 (α ↓ a))
 Ord-to-𝕍-behaviour = transfinite-recursion-on-OO-behaviour 𝕍 (λ a f → 𝕍-set f)

 ∈-of-Ord-to-𝕍 : (α : Ord) (x : 𝕍)
                → x ∈ Ord-to-𝕍 α ＝ (∃ a ꞉ ⟨ α ⟩ , Ord-to-𝕍 (α ↓ a) ＝ x)
 ∈-of-Ord-to-𝕍 α x =
  x ∈ Ord-to-𝕍 α                        ＝⟨ ap (x ∈_) (Ord-to-𝕍-behaviour α) ⟩
  x ∈ 𝕍-set (λ a → Ord-to-𝕍 (α ↓ a))    ＝⟨ ∈-for-𝕍-sets x _ ⟩
  (∃ a ꞉ ⟨ α ⟩ , Ord-to-𝕍 (α ↓ a) ＝ x) ∎

 to-∈-of-Ord-to-𝕍 : (α : Ord) {x : 𝕍}
                  → (∃ a ꞉ ⟨ α ⟩ , Ord-to-𝕍 (α ↓ a) ＝ x) → x ∈ Ord-to-𝕍 α
 to-∈-of-Ord-to-𝕍 α {x} = back-Idtofun (∈-of-Ord-to-𝕍 α x)

 from-∈-of-Ord-to-𝕍 : (α : Ord) {x : 𝕍}
                    → x ∈ Ord-to-𝕍 α → (∃ a ꞉ ⟨ α ⟩ , Ord-to-𝕍 (α ↓ a) ＝ x)
 from-∈-of-Ord-to-𝕍 α {x} = Idtofun (∈-of-Ord-to-𝕍 α x)

 Ord-to-𝕍-preserves-strict-order : (α β : Ord) → α ⊲ β → Ord-to-𝕍 α ∈ Ord-to-𝕍 β
 Ord-to-𝕍-preserves-strict-order α β (b , refl) = to-∈-of-Ord-to-𝕍 β ∣ b , refl ∣

 Ord-to-𝕍-preserves-weak-order : (α β : Ord) → α ⊴ β → Ord-to-𝕍 α ⊆ Ord-to-𝕍 β
 Ord-to-𝕍-preserves-weak-order α β l x m = to-∈-of-Ord-to-𝕍 β m'
  where
   l' : (a : ⟨ α ⟩) → Σ b ꞉ ⟨ β ⟩ , α ↓ a ＝ β ↓ b
   l' = from-≼ (⊴-gives-≼ α β l)
   m' : ∃ b ꞉ ⟨ β ⟩ , Ord-to-𝕍 (β ↓ b) ＝ x
   m' = ∥∥-functor h (from-∈-of-Ord-to-𝕍 α m)
    where
     h : (Σ a ꞉ ⟨ α ⟩ , Ord-to-𝕍 (α ↓ a) ＝ x)
       → (Σ b ꞉ ⟨ β ⟩ , Ord-to-𝕍 (β ↓ b) ＝ x)
     h (a , refl) = (b , ap Ord-to-𝕍 (e ⁻¹))
      where
       b : ⟨ β ⟩
       b = pr₁ (l' a)
       e : α ↓ a ＝ β ↓ b
       e = pr₂ (l' a)

 Ord-to-𝕍-is-left-cancellable : (α β : Ord) → Ord-to-𝕍 α ＝ Ord-to-𝕍 β → α ＝ β
 Ord-to-𝕍-is-left-cancellable = transfinite-induction-on-OO _ f
  where
   f : (α : Ord)
     → ((a : ⟨ α ⟩) (β : Ord) → Ord-to-𝕍 (α ↓ a) ＝ Ord-to-𝕍 β → (α ↓ a) ＝ β)
     → (β : Ord) → Ord-to-𝕍 α ＝ Ord-to-𝕍 β → α ＝ β
   f α IH β e = ⊴-antisym α β (to-⊴ α β g₁) (to-⊴ β α g₂)
    where
     g₁ : (a : ⟨ α ⟩) → (α ↓ a) ⊲ β
     g₁ a = ∥∥-rec (⊲-is-prop-valued (α ↓ a) β) h (from-∈-of-Ord-to-𝕍 β m)
      where
       h : (Σ b ꞉ ⟨ β ⟩ , Ord-to-𝕍 (β ↓ b) ＝ Ord-to-𝕍 (α ↓ a)) → (α ↓ a) ⊲ β
       h (b , e) = (b , (IH a (β ↓ b) (e ⁻¹)))
       m : Ord-to-𝕍 (α ↓ a) ∈ Ord-to-𝕍 β
       m = transport (Ord-to-𝕍 (α ↓ a) ∈_) e
                     (to-∈-of-Ord-to-𝕍 α ∣ a , refl ∣)
     g₂ : (b : ⟨ β ⟩) → (β ↓ b) ⊲ α
     g₂ b = ∥∥-rec (⊲-is-prop-valued (β ↓ b) α) h (from-∈-of-Ord-to-𝕍 α m)
      where
       h : (Σ a ꞉ ⟨ α ⟩ , Ord-to-𝕍 (α ↓ a) ＝ Ord-to-𝕍 (β ↓ b)) → (β ↓ b) ⊲ α
       h (a , e) = (a , ((IH a (β ↓ b) e) ⁻¹))
       m : Ord-to-𝕍 (β ↓ b) ∈ Ord-to-𝕍 α
       m = transport (Ord-to-𝕍 (β ↓ b) ∈_) (e ⁻¹)
                     (to-∈-of-Ord-to-𝕍 β ∣ b , refl ∣)

 Ord-to-𝕍-reflects-strict-order : (α β : Ord) → Ord-to-𝕍 α ∈ Ord-to-𝕍 β → α ⊲ β
 Ord-to-𝕍-reflects-strict-order α β m = ∥∥-rec (⊲-is-prop-valued α β) h m'
  where
   h : (Σ b ꞉ ⟨ β ⟩ , Ord-to-𝕍 (β ↓ b) ＝ Ord-to-𝕍 α) → α ⊲ β
   h (b , e) = (b , ((Ord-to-𝕍-is-left-cancellable (β ↓ b) α e) ⁻¹))
   m' : ∃ b ꞉ ⟨ β ⟩ , Ord-to-𝕍 (β ↓ b) ＝ Ord-to-𝕍 α
   m' = from-∈-of-Ord-to-𝕍 β m

 Ord-to-𝕍-reflects-weak-order : (α β : Ord) → Ord-to-𝕍 α ⊆ Ord-to-𝕍 β → α ⊴ β
 Ord-to-𝕍-reflects-weak-order α β s = to-⊴ α β h
  where
   h : (a : ⟨ α ⟩) → (α ↓ a) ⊲ β
   h a = Ord-to-𝕍-reflects-strict-order (α ↓ a) β m
    where
     m : Ord-to-𝕍 (α ↓ a) ∈ Ord-to-𝕍 β
     m = s (Ord-to-𝕍 (α ↓ a)) (to-∈-of-Ord-to-𝕍 α ∣ a , refl ∣)

 Ord-to-𝕍ᵒʳᵈ : Ord → 𝕍ᵒʳᵈ
 Ord-to-𝕍ᵒʳᵈ α = (Ord-to-𝕍 α , ρ α)
  where
   τ : (β : Ord) → is-transitive-set (Ord-to-𝕍 β)
   τ β x y x-in-β y-in-x = to-∈-of-Ord-to-𝕍 β (∥∥-rec ∃-is-prop lemma x-in-β')
    where
     x-in-β' : ∃ b ꞉ ⟨ β ⟩ , Ord-to-𝕍 (β ↓ b) ＝ x
     x-in-β' = from-∈-of-Ord-to-𝕍 β x-in-β
     lemma : (Σ b ꞉ ⟨ β ⟩ , Ord-to-𝕍 (β ↓ b) ＝ x)
           → ∃ c ꞉ ⟨ β ⟩ , Ord-to-𝕍 (β ↓ c) ＝ y
     lemma (b , refl) = ∥∥-functor h y-in-β↓b
      where
       h : (Σ c ꞉ ⟨ β ↓ b ⟩ , Ord-to-𝕍 ((β ↓ b) ↓ c) ＝ y)
         → Σ d ꞉ ⟨ β ⟩ , Ord-to-𝕍 (β ↓ d) ＝ y
       h ((c , l) , refl) = (c , ap Ord-to-𝕍 ((iterated-↓ β b c l) ⁻¹))
       y-in-β↓b : ∃ c ꞉ ⟨ β ↓ b ⟩ , Ord-to-𝕍 ((β ↓ b) ↓ c) ＝ y
       y-in-β↓b = from-∈-of-Ord-to-𝕍 (β ↓ b) y-in-x

   ρ : (β : Ord) → is-set-theoretic-ordinal (Ord-to-𝕍 β)
   ρ = transfinite-induction-on-OO
        (λ - → is-set-theoretic-ordinal (Ord-to-𝕍 -))
        ρ'
    where
     ρ' : (β : Ord)
        → ((b : ⟨ β ⟩) → is-set-theoretic-ordinal (Ord-to-𝕍 (β ↓ b)))
        → is-set-theoretic-ordinal (Ord-to-𝕍 β)
     ρ' β IH = (τ β , τ')
      where
       τ' : (y : 𝕍) → y ∈ Ord-to-𝕍 β → is-transitive-set y
       τ' y m = ∥∥-rec being-transitive-set-is-prop h (from-∈-of-Ord-to-𝕍 β m)
        where
         h : (Σ b ꞉ ⟨ β ⟩ , Ord-to-𝕍 (β ↓ b) ＝ y) → is-transitive-set y
         h (b , refl) = τ (β ↓ b)

 Ord-to-𝕍ᵒʳᵈ-is-left-cancellable : {α β : Ord}
                                 → Ord-to-𝕍ᵒʳᵈ α ＝ Ord-to-𝕍ᵒʳᵈ β → α ＝ β
 Ord-to-𝕍ᵒʳᵈ-is-left-cancellable {α} {β} e =
  Ord-to-𝕍-is-left-cancellable α β (ap pr₁ e)

\end{code}

\begin{code}

 open import Ordinals.Arithmetic fe'
 open import Ordinals.Arithmetic-Properties ua
 open import Ordinals.OrdinalOfOrdinalsSuprema ua

 open import UF.Quotient

 module _
         (sq : set-quotients-exist)
        where

  open suprema pt (set-replacement-from-set-quotients sq pt)

  private
   𝕍-to-Ord-aux : {A : 𝓤 ̇ } → (A → 𝕍) → (A → Ord) → Ord
   𝕍-to-Ord-aux _ r = sup (λ a → r a +ₒ 𝟙ₒ)

   𝕍-to-Ord-packaged : Σ ϕ ꞉ (𝕍 → Ord) , ({A : 𝓤 ̇} (f : A → 𝕍)
                                          (r : A → Ordinal 𝓤)
                                       → ϕ (𝕍-set f) ＝ 𝕍-to-Ord-aux f r)
   𝕍-to-Ord-packaged =
    𝕍-recursion-with-computation the-type-of-ordinals-is-a-set ρ τ
    where
     ρ = 𝕍-to-Ord-aux
     monotone-lemma : {A B : 𝓤 ̇} (f : A → 𝕍) (g : B → 𝕍)
                    → (r₁ : A → Ord) (r₂ : B → Ord)
                    → ((a : A) → ∥ Σ b ꞉ B , Σ p ꞉ f a ＝ g b , r₁ a ＝ r₂ b ∥)
                    → ρ f r₁ ⊴ ρ g r₂
     monotone-lemma {A} {B} f g r₁ r₂ e =
      sup-is-lower-bound-of-upper-bounds (λ a → r₁ a +ₒ 𝟙ₒ) (ρ g r₂) ϕ
       where
        ϕ : (a : A) → (r₁ a +ₒ 𝟙ₒ) ⊴ ρ g r₂
        ϕ a = ∥∥-rec (⊴-is-prop-valued _ _) ψ (e a)
         where
          ψ : (Σ b ꞉ B , Σ p ꞉ f a ＝ g b , r₁ a ＝ r₂ b)
            → (r₁ a +ₒ 𝟙ₒ) ⊴ ρ g r₂
          ψ (b , _ , q) = ⊴-trans _ (r₂ b +ₒ 𝟙ₒ) _ k l
           where
            k : (r₁ a +ₒ 𝟙ₒ) ⊴ (r₂ b +ₒ 𝟙ₒ)
            k = ≃ₒ-to-⊴ _ _ (idtoeqₒ _ _ (ap (_+ₒ 𝟙ₒ) q))
            l : (r₂ b +ₒ 𝟙ₒ) ⊴ ρ g r₂
            l = sup-is-upper-bound _ b

     τ : {A B : 𝓤 ̇} (f : A → 𝕍) (g : B → 𝕍)
       → (r₁ : A → Ord) (r₂ : B → Ord)
       → ((a : A) → ∥ Σ b ꞉ B , Σ p ꞉ f a ＝ g b , r₁ a ＝ r₂ b ∥)
       → ((b : B) → ∥ Σ a ꞉ A , Σ p ꞉ g b ＝ f a , r₂ b ＝ r₁ a ∥)
       → f ≈ g
       → ρ f r₁ ＝ ρ g r₂
     τ {A} {B} f g r₁ r₂ e₁ e₂ _ =
      ⊴-antisym (ρ f r₁) (ρ g r₂)
                (monotone-lemma f g r₁ r₂ e₁)
                (monotone-lemma g f r₂ r₁ e₂)

  𝕍-to-Ord : 𝕍 → Ord
  𝕍-to-Ord = pr₁ (𝕍-to-Ord-packaged)

  𝕍-to-Ord-behaviour-on-𝕍-sets :
     {A : 𝓤 ̇ } (f : A → 𝕍)
   → 𝕍-to-Ord (𝕍-set f) ＝ sup (λ a → 𝕍-to-Ord (f a) +ₒ 𝟙ₒ)
  𝕍-to-Ord-behaviour-on-𝕍-sets f = pr₂ 𝕍-to-Ord-packaged f (λ a → 𝕍-to-Ord (f a))

  𝕍ᵒʳᵈ-to-Ord : 𝕍ᵒʳᵈ → Ord
  𝕍ᵒʳᵈ-to-Ord = 𝕍-to-Ord ∘ pr₁

  -- TO DO: Move elsewhere and rename
  +ₒ-𝟙ₒ-lemma : (α : Ord) → (α +ₒ 𝟙ₒ) ↓ inr ⋆ ＝ α
  +ₒ-𝟙ₒ-lemma α =
   eqtoidₒ ((α +ₒ 𝟙ₒ) ↓ inr ⋆) α (f , f-mon
                                  , ((qinvs-are-equivs f (g , (η , ε)))
                                  , g-mon))
    where
     f : ⟨ (α +ₒ 𝟙ₒ) ↓ inr ⋆ ⟩ → ⟨ α ⟩
     f (inl x , l) = x
     f-mon : is-order-preserving ((α +ₒ 𝟙ₒ) ↓ inr ⋆) α f
     f-mon (inl x , _) (inl y , _) l = l
     g : ⟨ α ⟩ → ⟨ (α +ₒ 𝟙ₒ) ↓ inr ⋆ ⟩
     g x = (inl x , ⋆)
     g-mon : is-order-preserving α ((α +ₒ 𝟙ₒ) ↓ inr ⋆) g
     g-mon x y l = l
     η : g ∘ f ∼ id
     η (inl _ , _) = refl
     ε : f ∘ g ∼ id
     ε _ = refl

  -- TO DO: Clean this up
  𝕍-to-Ord-is-section-of-Ord-to-𝕍 : (x : 𝕍)
                                  → is-set-theoretic-ordinal x
                                  → Ord-to-𝕍 (𝕍-to-Ord x) ＝ x
  𝕍-to-Ord-is-section-of-Ord-to-𝕍 =
   𝕍-prop-induction _ (λ x → Π-is-prop fe (λ _ → 𝕍-is-set)) ρ
    where
     ρ : {A : 𝓤 ̇} (f : A → 𝕍)
       → ((a : A) → is-set-theoretic-ordinal (f a)
                  → Ord-to-𝕍 (𝕍-to-Ord (f a)) ＝ f a)
       → is-set-theoretic-ordinal (𝕍-set f)
       → Ord-to-𝕍 (𝕍-to-Ord (𝕍-set f)) ＝ 𝕍-set f
     ρ {A} f IH σ =
      Ord-to-𝕍 (𝕍-to-Ord (𝕍-set f))  ＝⟨ ap Ord-to-𝕍 (𝕍-to-Ord-behaviour-on-𝕍-sets f) ⟩
      Ord-to-𝕍 s                     ＝⟨ Ord-to-𝕍-behaviour s ⟩
      𝕍-set (λ y → Ord-to-𝕍 (s ↓ y)) ＝⟨ 𝕍-set-ext _ _ (e₁ , e₂) ⟩
      𝕍-set f                        ∎
       where
        s : Ord
        s = sup (λ a → 𝕍-to-Ord (f a) +ₒ 𝟙ₒ)
        c : (a : A) → Ord
        c a = 𝕍-to-Ord (f a) +ₒ 𝟙ₒ

        abstract -- For performance
         u : (a : A) → ⟨ 𝕍-to-Ord (f a) +ₒ 𝟙ₒ ⟩  → ⟨ s ⟩
         u a = pr₁ (sup-is-upper-bound _ a)

         IH' : (a : A) → Ord-to-𝕍 (𝕍-to-Ord (f a)) ＝ f a
         IH' a = IH a (being-set-theoretic-ordinal-is-hereditary σ
                        (to-∈-of-𝕍-set ∣ a , refl ∣))

         lemma' : (a : A) → Ord-to-𝕍 (c a ↓ inr ⋆) ＝ f a
         lemma' a = Ord-to-𝕍 (c a ↓ inr ⋆)     ＝⟨ ap Ord-to-𝕍 ⦅e⦆ ⟩
                    Ord-to-𝕍 (𝕍-to-Ord (f a)) ＝⟨ IH' a            ⟩
                    f a ∎
          where
           ⦅e⦆ : c a ↓ inr ⋆ ＝ 𝕍-to-Ord (f a)
           ⦅e⦆ = +ₒ-𝟙ₒ-lemma (𝕍-to-Ord (f a))

         lemma : (a : A) → Ord-to-𝕍 (s ↓ u a (inr ⋆)) ＝ f a
         lemma a = Ord-to-𝕍 (s ↓ u a (inr ⋆)) ＝⟨ ap Ord-to-𝕍 ⦅e⦆ ⟩
                   Ord-to-𝕍 (c a ↓ inr ⋆)     ＝⟨ lemma' a ⟩
                   f a                        ∎
          where
           ⦅e⦆ : s ↓ u a (inr ⋆) ＝ c a ↓ inr ⋆
           ⦅e⦆ = initial-segment-of-sup-at-component _ a (inr ⋆)

        e₂ : f ≲ (λ y → Ord-to-𝕍 (s ↓ y))
        e₂ a = ∣ u a (inr ⋆) , lemma a ∣

        e₁ : (λ y → Ord-to-𝕍 (s ↓ y)) ≲ f
        e₁ y =
         ∥∥-rec ∃-is-prop h
          (initial-segment-of-sup-is-initial-segment-of-some-component _ y)
          where
           h : (Σ a ꞉ A , Σ x ꞉ ⟨ c a ⟩ , s ↓ y ＝ c a ↓ x)
             → ∃ a ꞉ A , f a ＝ Ord-to-𝕍 (s ↓ y)
           h (a , inr ⋆ , e) = ∣ a , ((ap Ord-to-𝕍 e ∙ lemma' a ) ⁻¹) ∣
           h (a , inl x , e) = goal
            where
             fact : c a ↓ inl x ＝ 𝕍-to-Ord (f a) ↓ x
             fact = +ₒ-↓-left x ⁻¹
             claim : Ord-to-𝕍 (𝕍-to-Ord (f a) ↓ x) ∈ f a
             claim = transport (Ord-to-𝕍 (𝕍-to-Ord (f a) ↓ x) ∈_)
                                (IH' a)
                                (Ord-to-𝕍-preserves-strict-order
                                  (𝕍-to-Ord (f a) ↓ x)
                                  (𝕍-to-Ord (f a))
                                  (x , refl))
             claim' : Ord-to-𝕍 (𝕍-to-Ord (f a) ↓ x) ∈ 𝕍-set f
             claim' = transitive-set-if-set-theoretic-ordinal σ
                        (f a)
                        (Ord-to-𝕍 (𝕍-to-Ord (f a) ↓ x))
                        (to-∈-of-𝕍-set ∣ a , refl ∣)
                        claim
             suffices : ∃ a' ꞉ A , f a' ＝ Ord-to-𝕍 (𝕍-to-Ord (f a) ↓ x)
             suffices = from-∈-of-𝕍-set claim'
             goal : ∃ a' ꞉ A , f a' ＝ Ord-to-𝕍 (s ↓ y)
             goal = ∥∥-functor (λ (a' , p) → a' , (p ∙ ap Ord-to-𝕍 (fact ⁻¹ ∙ e ⁻¹))) suffices

  𝕍ᵒʳᵈ-to-Ord-is-section-of-Ord-to-𝕍ᵒʳᵈ : Ord-to-𝕍ᵒʳᵈ ∘ 𝕍ᵒʳᵈ-to-Ord ∼ id
  𝕍ᵒʳᵈ-to-Ord-is-section-of-Ord-to-𝕍ᵒʳᵈ (x , σ) =
   𝕍ᵒʳᵈ-is-subtype (𝕍-to-Ord-is-section-of-Ord-to-𝕍 x σ)

  𝕍ᵒʳᵈ-isomorphic-to-Ord : OO 𝓤 ≃ₒ 𝕍ᴼᴿᴰ
  𝕍ᵒʳᵈ-isomorphic-to-Ord =
   Ord-to-𝕍ᵒʳᵈ , order-preserving-reflecting-equivs-are-order-equivs
                  (OO 𝓤) 𝕍ᴼᴿᴰ Ord-to-𝕍ᵒʳᵈ
                  (lc-split-surjections-are-equivs
                    Ord-to-𝕍ᵒʳᵈ Ord-to-𝕍ᵒʳᵈ-is-left-cancellable
                    (λ x → 𝕍ᵒʳᵈ-to-Ord x
                         , 𝕍ᵒʳᵈ-to-Ord-is-section-of-Ord-to-𝕍ᵒʳᵈ x))
                  Ord-to-𝕍-preserves-strict-order
                  Ord-to-𝕍-reflects-strict-order

\end{code}
