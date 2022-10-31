Tom de Jong, 28 October 2022 - ...

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
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.FunExt
open import UF.UA-FunExt

private
 fe : Fun-Ext
 fe = Univalence-gives-Fun-Ext ua

 pe : Prop-Ext
 pe = Univalence-gives-Prop-Ext ua

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

 𝕍ᵒʳᵈ : 𝓤 ⁺ ̇
 𝕍ᵒʳᵈ = Σ x ꞉ 𝕍 , is-set-theoretic-ordinal x

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

\end{code}

\begin{code}

 open import Ordinals.Arithmetic (λ _ _ → fe)
 open import Ordinals.OrdinalOfOrdinalsSuprema ua

 open import UF.Quotient

 module _
         (sq : set-quotients-exist)
        where

  open suprema pt (set-replacement-from-set-quotients sq pt)

  𝕍-to-Ord : 𝕍 → Ord
  𝕍-to-Ord = 𝕍-recursion the-type-of-ordinals-is-a-set ρ τ
   where
    ρ : {A : 𝓤 ̇ } → (A → 𝕍) → (A → Ord) → Ord
    ρ _ r = sup (λ a → r a +ₒ 𝟙ₒ)

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

\end{code}
