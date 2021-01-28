Tom de Jong, 28 January 2020
\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-Base
open import Integers

open import UF-Embeddings
open import UF-Equiv hiding (_≅_)
open import UF-EquivalenceExamples
open import UF-FunExt
open import UF-Lower-FunExt
open import UF-Subsingletons
open import UF-Subsingletons-FunExt
open import UF-Retracts

open import UF-PropTrunc
open import UF-Univalence
open import UF-UA-FunExt

open import UF-SIP -- Maybe use MGS-SIP?

module Circle
        (pt : propositional-truncations-exist)
        (ua : is-univalent 𝓤₀)
       where

 -- TO DO: Move this somewhere

 ∙-is-equiv₁ : {X : 𝓤 ̇ } {x y : X} (p : x ≡ x)
             → is-equiv (λ (q : x ≡ y) → p ∙ q)
 ∙-is-equiv₁ {𝓤} {X} {x} {y} p =
  qinvs-are-equivs (λ q → p ∙ q) ((λ q → p ⁻¹ ∙ q) , η , ε)
   where
    ε : (q : x ≡ y) → p ∙ (p ⁻¹ ∙ q) ≡ q
    ε q = p ∙ (p ⁻¹ ∙ q) ≡⟨ (∙assoc p (p ⁻¹) q) ⁻¹                  ⟩
          (p ∙ p ⁻¹) ∙ q ≡⟨ ap (λ - → - ∙ q) ((right-inverse p) ⁻¹) ⟩
          refl ∙ q       ≡⟨ refl-left-neutral                       ⟩
          q              ∎
    η : (q : x ≡ y) → p ⁻¹ ∙ (p ∙ q) ≡ q
    η q = p ⁻¹ ∙ (p ∙ q) ≡⟨ (∙assoc (p ⁻¹) p q) ⁻¹            ⟩
          (p ⁻¹ ∙ p) ∙ q ≡⟨ ap (λ - → - ∙ q) (left-inverse p) ⟩
          refl ∙ q       ≡⟨ refl-left-neutral                 ⟩
          q              ∎

 open PropositionalTruncation pt
 open sip
 open sip-with-axioms

 Tℤ : 𝓤₁ ̇
 Tℤ = Σ X ꞉ 𝓤₀ ̇ , Σ f ꞉ (X → X) , ∥ (X , f) ≡ (ℤ , succ-ℤ) ∥

 base : Tℤ
 base = (ℤ , succ-ℤ , ∣ refl ∣)

 Tℤ-structure : 𝓤₀ ̇ → 𝓤₀ ̇
 Tℤ-structure X = X → X

 Tℤ⁻ : 𝓤₁ ̇
 Tℤ⁻ = Σ X ꞉ 𝓤₀ ̇ , Tℤ-structure X

 sns-data : SNS Tℤ-structure 𝓤₀
 sns-data = (ι , ρ , θ)
  where
   ι : (X Y : Tℤ⁻) → ⟨ X ⟩ ≃ ⟨ Y ⟩ → 𝓤₀ ̇
   ι (X , f) (Y , g) (e , _) = e ∘ f ≡ g ∘ e
   ρ : (X : Tℤ⁻) → ι X X (≃-refl ⟨ X ⟩)
   ρ (X , f) = refl
   h : {X : 𝓤₀ ̇ } {f g : Tℤ-structure X}
     → canonical-map ι ρ f g ∼ id {𝓤₀} {f ≡ g}
   h refl = refl
   θ : {X : 𝓤₀ ̇} (f g : Tℤ-structure X)
     → is-equiv (canonical-map ι ρ f g)
   θ f g = equiv-closed-under-∼ _ _ (id-is-equiv (f ≡ g)) h

 _≃[Tℤ]_ : Tℤ → Tℤ → 𝓤₀ ̇
 (X , f , _) ≃[Tℤ] (Y , g , _) = Σ e ꞉ (X → Y) , is-equiv e
                                               × (e ∘ f ≡ g ∘ e)

 _≅_ : Tℤ → Tℤ → 𝓤₀ ̇
 (X , f , _) ≅ (Y , g , _) = Σ e ꞉ (X → Y) , is-equiv e
                                           × (e ∘ f ∼ g ∘ e)

 characterization-of-Tℤ-≡' : (X Y : Tℤ)
                           → (X ≡ Y) ≃ (X ≃[Tℤ] Y)
 characterization-of-Tℤ-≡' =
  characterization-of-≡-with-axioms ua
   sns-data
   (λ X f → ∥ (X , f) ≡ (ℤ , succ-ℤ) ∥)
   (λ X f → ∥∥-is-prop)

 characterization-of-Tℤ-≡ : (X Y : Tℤ)
                           → (X ≡ Y) ≃ (X ≅ Y)
 characterization-of-Tℤ-≡ X Y = (X ≡ Y)     ≃⟨ characterization-of-Tℤ-≡' X Y ⟩
                                (X ≃[Tℤ] Y) ≃⟨ γ ⟩
                                (X ≅ Y)     ■
  where
   γ = Σ-cong (λ h → ×-cong (≃-refl (is-equiv h))
                     (≃-funext (univalence-gives-funext ua) _ _))

 to-Tℤ-≡ : (X Y : Tℤ) → X ≅ Y → X ≡ Y
 to-Tℤ-≡ X Y = ⌜ ≃-sym (characterization-of-Tℤ-≡ X Y) ⌝

 to-Tℤ-≡' : (X Y : Tℤ) → X ≃[Tℤ] Y → X ≡ Y
 to-Tℤ-≡' X Y = ⌜ ≃-sym (characterization-of-Tℤ-≡' X Y) ⌝

 _≃[Tℤ⁻]_ : Tℤ⁻ → Tℤ⁻ → 𝓤₀ ̇
 (X , f) ≃[Tℤ⁻] (Y , g) = Σ e ꞉ (X → Y) , is-equiv e
                                   × (e ∘ f ≡ g ∘ e)

 loop : base ≡ base
 loop = to-Tℤ-≡' base base (succ-ℤ , ⌜⌝-is-equiv succ-ℤ-≃ , refl)

 yyy : {X Y : Tℤ} (p : X ≡ Y)
     → idtoeq ⟨ X ⟩ ⟨ Y ⟩ (ap ⟨_⟩ p) ≡ pr₁ (⌜ characterization-of-Tℤ-≡' X Y ⌝ p) , pr₁ (pr₂ (⌜ characterization-of-Tℤ-≡' X Y ⌝ p))
 yyy refl = refl

 xxx : {(X , f , t) (Y , g , s) : Tℤ}
       (e : X → Y) (i : is-equiv e) (h : e ∘ f ≡ g ∘ e)
     → ap ⟨_⟩ (to-Tℤ-≡' (X , f , t) (Y , g , s) (e , i , h)) ≡ eqtoid ua X Y (e , i)
 xxx {(X , f , t)} {(Y , g , s)} e i h = {!!}

 module _
         {A : 𝓤 ̇ }
         (fe : funext 𝓤 𝓤)
         {a : A}
         (p : a ≡ a)
        where

  Qₚ : {X : 𝓤₀ ̇ } → (X → X) → 𝓤 ̇
  Qₚ {X} f = Σ a' ꞉ A , Σ h ꞉ (X → a ≡ a') , ((x : X) → h (f x) ≡ p ∙ h x)

  {-
  Qₚ-of-succ-ℤ-is-singleton : is-singleton (Qₚ succ-ℤ)
  Qₚ-of-succ-ℤ-is-singleton =
   equiv-to-singleton ϕ (singleton-types-are-singletons a)
    where
     ϕ : Qₚ succ-ℤ ≃ singleton-type a
     ϕ = Σ-cong ψ
      where
       ψ : (a' : A)
         → (Σ h ꞉ (ℤ → a ≡ a') , ((z : ℤ) → h (succ-ℤ z) ≡ p ∙ h z))
         ≃ (a ≡ a')
       ψ a' = ℤ-symmetric-induction (lower-funext 𝓤 𝓤 fe)
               (λ (_ : ℤ) → a ≡ a') (λ (_ : ℤ) → g)
        where
         g : (a ≡ a') ≃ (a ≡ a')
         g = (λ q → p ∙ q) , (∙-is-equiv₁ p)
  -}

  ∥∥-rec-foo : {𝓤 𝓥 : Universe} {X : 𝓤 ̇ } {P : 𝓥 ̇ }
               (i : is-prop P) (f : X → P) (x : X)
             → ∥∥-rec i f ∣ x ∣ ≡ f x
  ∥∥-rec-foo i f x = i (∥∥-rec i f ∣ x ∣) (f x)

  Qₚ-is-singleton : {X : 𝓤₀ ̇ } (f : X → X)
                  → ∥ (X , f) ≡ (ℤ , succ-ℤ) ∥
                  → is-singleton (Qₚ f)
  Qₚ-is-singleton {X} f t = ∥∥-rec (being-singleton-is-prop fe) γ t
   where
    γ : (X , f) ≡ (ℤ , succ-ℤ) → is-singleton (Qₚ f)
    γ refl = equiv-to-singleton ϕ (singleton-types-are-singletons a)
     where
      ϕ : Qₚ succ-ℤ ≃ (Σ a' ꞉ A , a ≡ a')
      ϕ = Σ-cong (λ a' → ℤ-symmetric-induction (lower-funext 𝓤 𝓤 fe)
                          (λ _ → a ≡ a') (g a'))
       where
        g : (a' : A) → (z : ℤ) → (a ≡ a') ≃ (a ≡ a')
        g a' _ = (λ q → p ∙ q) , (∙-is-equiv₁ p)

  Tℤ-recursion : Tℤ → A
  Tℤ-recursion (X , f , t) = pr₁ (center (Qₚ-is-singleton f t))

  Tℤ-recursion-on-base : Tℤ-recursion base ≡ a
  Tℤ-recursion-on-base =
   Tℤ-recursion base                               ≡⟨ I    ⟩
   pr₁ (center (singleton-types-are-singletons a)) ≡⟨ refl ⟩
   a                                               ∎
    where
     I = ap (pr₁ ∘ center) (∥∥-rec-foo (being-singleton-is-prop fe) _ refl)

  cₚ : ((X , f , t) : Tℤ)
     → X → a ≡ Tℤ-recursion (X , f , t)
  cₚ (X , f , t) = pr₁ (pr₂ (center (Qₚ-is-singleton f t)))

  cₚ-on-base : cₚ base ∼ (λ z → p ∙ cₚ base (pred-ℤ z))
  cₚ-on-base 𝟎 = {!!}
  cₚ-on-base (pos n) = {!!}
  cₚ-on-base (neg n) = {!!}

  lemma : {X Y : Tℤ} (e : X ≡ Y) (x : ⟨ X ⟩)
        → ap Tℤ-recursion e
        ≡ (cₚ X x) ⁻¹ ∙ cₚ Y (⌜ idtoeq ⟨ X ⟩ ⟨ Y ⟩ (ap ⟨_⟩ e) ⌝ x)
  lemma {X} {Y} refl x =
   ap Tℤ-recursion refl                       ≡⟨ refl ⟩
   refl                                       ≡⟨ left-inverse (cₚ X x) ⁻¹ ⟩
   (cₚ X x) ⁻¹ ∙ cₚ X x                       ≡⟨ refl ⟩
   (cₚ X x) ⁻¹ ∙ cₚ X (⌜ idtoeq _ _ refl ⌝ x) ∎

  lemma' : ap Tℤ-recursion loop ≡
             (cₚ base 𝟎) ⁻¹ ∙
             cₚ base (⌜ idtoeq ⟨ base ⟩ ⟨ base ⟩ (ap ⟨_⟩ loop) ⌝ 𝟎)
  lemma' = lemma loop 𝟎

  lemma'' : cₚ base (pos 0) ≡ p ∙ cₚ base 𝟎
  lemma'' = cₚ base (pos 0) ≡⟨ {!!} ⟩
            {!!} ≡⟨ {!!} ⟩
            {!!} ≡⟨ {!!} ⟩
            p ∙ cₚ base 𝟎 ∎
{-
--  yyy :


  zzz : ap ⟨_⟩ loop ≡ eqtoid ua ℤ ℤ succ-ℤ-≃
  zzz = ap ⟨_⟩ (to-Tℤ-≡ base base (succ-ℤ , ⌜⌝-is-equiv succ-ℤ-≃ , (λ z → refl))) ≡⟨ {!!} ⟩
        {!!} ≡⟨ {!!} ⟩
        {!!} ∎

  lemma'' : ⌜ idtoeq ⟨ base ⟩ ⟨ base ⟩ (ap ⟨_⟩ loop) ⌝ 𝟎 ≡ succ-ℤ 𝟎
  lemma'' = {!!}

  Tℤ-recursion-on-loop : ap (Tℤ-recursion) loop ≡ back-transport (λ - → - ≡ -) (Tℤ-recursion-on-base) p
    -- Tℤ-recursion-on-base ∙ (p ∙ Tℤ-recursion-on-base ⁻¹)
  Tℤ-recursion-on-loop = {!!}
-}

\end{code}
