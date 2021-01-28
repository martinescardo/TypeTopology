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

{-
 _≃[Tℤ]_ : Tℤ → Tℤ → 𝓤₀ ̇
 (X , f , _) ≃[Tℤ] (Y , g , _) = Σ e ꞉ (X → Y) , is-equiv e
                                               × (e ∘ f ≡ g ∘ e)
-}

 _≅_ : Tℤ → Tℤ → 𝓤₀ ̇
 (X , f , _) ≅ (Y , g , _) = Σ e ꞉ (X → Y) , is-equiv e
                                           × (e ∘ f ≡ g ∘ e)

{-
 characterization-of-Tℤ-≡' : (X Y : Tℤ)
                           → (X ≡ Y) ≃ (X ≃[Tℤ] Y)
 characterization-of-Tℤ-≡' =
  characterization-of-≡-with-axioms ua
   sns-data
   (λ X f → ∥ (X , f) ≡ (ℤ , succ-ℤ) ∥)
   (λ X f → ∥∥-is-prop)
-}

 characterization-of-Tℤ-≡ : (X Y : Tℤ)
                          → (X ≡ Y) ≃ (X ≅ Y)
 characterization-of-Tℤ-≡ =
  characterization-of-≡-with-axioms ua
   sns-data
   (λ X f → ∥ (X , f) ≡ (ℤ , succ-ℤ) ∥)
   (λ X f → ∥∥-is-prop)

 to-Tℤ-≡ : (X Y : Tℤ) → X ≅ Y → X ≡ Y
 to-Tℤ-≡ X Y = ⌜ ≃-sym (characterization-of-Tℤ-≡ X Y) ⌝

{-
 to-Tℤ-≡' : (X Y : Tℤ) → X ≃[Tℤ] Y → X ≡ Y
 to-Tℤ-≡' X Y = ⌜ ≃-sym (characterization-of-Tℤ-≡' X Y) ⌝

 _≃[Tℤ⁻]_ : Tℤ⁻ → Tℤ⁻ → 𝓤₀ ̇
 (X , f) ≃[Tℤ⁻] (Y , g) = Σ e ꞉ (X → Y) , is-equiv e
                                   × (e ∘ f ≡ g ∘ e)
-}

 loop : base ≡ base
 loop = to-Tℤ-≡ base base (succ-ℤ , ⌜⌝-is-equiv succ-ℤ-≃ , refl)

 Tℤ-≡-to-≃-of-carriers : {X Y : Tℤ} → X ≡ Y → ⟨ X ⟩ ≃ ⟨ Y ⟩
 Tℤ-≡-to-≃-of-carriers p = pr₁ c , pr₁ (pr₂ c)
  where
   c = ⌜ characterization-of-Tℤ-≡ _ _ ⌝ p

 yyy : {X Y : Tℤ} (p : X ≡ Y)
     → idtoeq ⟨ X ⟩ ⟨ Y ⟩ (ap ⟨_⟩ p) ≡ Tℤ-≡-to-≃-of-carriers p
 yyy refl = refl

 xxx : idtoeq ℤ ℤ (ap ⟨_⟩ loop) ≡ succ-ℤ-≃
 xxx = idtoeq ℤ ℤ (ap ⟨_⟩ loop) ≡⟨ yyy loop ⟩
       Tℤ-≡-to-≃-of-carriers loop ≡⟨ refl ⟩
        pr₁ (ϕ loop) , pr₁ (pr₂ (ϕ loop)) ≡⟨ refl ⟩
        pr₁ (ϕ (ψ l)) , pr₁ (pr₂ (ϕ (ψ l))) ≡⟨ ap (λ - → pr₁ - , pr₁ (pr₂ -)) (s l) ⟩
        pr₁ l , pr₁ (pr₂ l) ∎
  where
   ϕ : base ≡ base → base ≅ base
   ϕ = ⌜ characterization-of-Tℤ-≡ base base ⌝
   ψ : base ≅ base → base ≡ base
   ψ = ⌜ ≃-sym (characterization-of-Tℤ-≡ base base) ⌝
   s : ϕ ∘ ψ ∼ id
   s = inverses-are-sections ϕ (⌜⌝-is-equiv (characterization-of-Tℤ-≡ base base))
   l : base ≅ base
   l = (succ-ℤ , ⌜⌝-is-equiv succ-ℤ-≃ , refl)

 module _
         {A : 𝓤 ̇ }
         (fe : funext 𝓤 𝓤)
         {a : A}
         (p : a ≡ a)
        where

  Qₚ : (Σ X ꞉ 𝓤₀ ̇ , (X → X)) → 𝓤 ̇
  Qₚ (X , f) = Σ a' ꞉ A , Σ h ꞉ (X → a ≡ a') , ((x : X) → h (f x) ≡ p ∙ h x)

  Qₚ-base : 𝓤 ̇
  Qₚ-base = Qₚ (ℤ , succ-ℤ)

  Qₚ-base-is-singleton : is-singleton Qₚ-base
  Qₚ-base-is-singleton = equiv-to-singleton ϕ (singleton-types-are-singletons a)
   where
    ϕ : Qₚ-base ≃ singleton-type a
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

  cₚ-base : Qₚ-base
  cₚ-base = center (Qₚ-base-is-singleton)

  cₚ¹-base : A
  cₚ¹-base = pr₁ cₚ-base

  cₚ²-base : ℤ → a ≡ cₚ¹-base
  cₚ²-base = pr₁ (pr₂ (cₚ-base))

  cₚ³-base : (z : ℤ) → cₚ²-base (succ-ℤ z) ≡ p ∙ cₚ²-base z
  cₚ³-base = pr₂ (pr₂ (cₚ-base))

  ∥∥-rec-comp : {𝓤 𝓥 : Universe} {X : 𝓤 ̇ } {P : 𝓥 ̇ }
                (i : is-prop P) (f : X → P) (x : X)
              → ∥∥-rec i f ∣ x ∣ ≡ f x
  ∥∥-rec-comp i f x = i (∥∥-rec i f ∣ x ∣) (f x)

  Qₚ-is-singleton : ((X , f , t) : Tℤ)
                  → is-singleton (Qₚ (X , f))
  Qₚ-is-singleton (X , f , t) = ∥∥-rec (being-singleton-is-prop fe) γ t
   where
    γ : (X , f) ≡ (ℤ , succ-ℤ) → is-singleton (Qₚ (X , f))
    γ refl = Qₚ-base-is-singleton

  cₚ : ((X , f , _) : Tℤ) → Qₚ (X , f)
  cₚ (X , f , t) =
   ∥∥-rec (singletons-are-props (Qₚ-is-singleton (X , f , t)))
    (λ e → back-transport Qₚ e cₚ-base) t

  cₚ-on-base : cₚ base ≡ cₚ-base
  cₚ-on-base = ∥∥-rec-comp (singletons-are-props (Qₚ-is-singleton base))
   (λ e → back-transport Qₚ e cₚ-base) refl

  cₚ¹ : Tℤ → A
  cₚ¹ X = pr₁ (cₚ X)

  cₚ¹-on-base : cₚ¹ base ≡ cₚ¹-base
  cₚ¹-on-base = ap pr₁ cₚ-on-base

  cₚ² : (X : Tℤ) → (⟨ X ⟩ → a ≡ cₚ¹ X)
  cₚ² X = pr₁ (pr₂ (cₚ X))

{-
  cₚ²-on-base : cₚ² base ≡ back-transport (λ - → ℤ → a ≡ -) cₚ¹-on-base cₚ²-base
  cₚ²-on-base = {!!}
-}

  ⟨_⟩₂ : (X : Tℤ) → ⟨ X ⟩ → ⟨ X ⟩
  ⟨ (X , f , _) ⟩₂ = f

  cₚ³ : (X : Tℤ) → (x : ⟨ X ⟩)
      → cₚ² X (⟨ X ⟩₂ x) ≡ p ∙ cₚ² X x
  cₚ³ X = pr₂ (pr₂ (cₚ X))

  lemma : {X Y : Tℤ} (e : X ≡ Y) (x : ⟨ X ⟩)
        → ap cₚ¹ e
        ≡ (cₚ² X x) ⁻¹ ∙ cₚ² Y (⌜ idtoeq ⟨ X ⟩ ⟨ Y ⟩ (ap ⟨_⟩ e) ⌝ x)
  lemma {X} {Y} refl x =
   ap cₚ¹ refl                                  ≡⟨ refl ⟩
   refl                                         ≡⟨ left-inverse (cₚ² X x) ⁻¹ ⟩
   (cₚ² X x) ⁻¹ ∙ cₚ² X x                       ≡⟨ refl ⟩
   (cₚ² X x) ⁻¹ ∙ cₚ² X (⌜ idtoeq _ _ refl ⌝ x) ∎

  lemma' : ap cₚ¹ loop ≡
             (cₚ² base 𝟎) ⁻¹ ∙
             cₚ² base (⌜ idtoeq ⟨ base ⟩ ⟨ base ⟩ (ap ⟨_⟩ loop) ⌝ 𝟎)
  lemma' = lemma loop 𝟎

  kkk : ap cₚ¹ loop ≡ (cₚ² base 𝟎) ⁻¹ ∙ (p ∙ (cₚ² base 𝟎))
  kkk = ap cₚ¹ loop ≡⟨ lemma' ⟩
        cₚ² base 𝟎 ⁻¹ ∙
          cₚ² base (⌜ idtoeq ⟨ base ⟩ ⟨ base ⟩ (ap ⟨_⟩ loop) ⌝ 𝟎) ≡⟨ ap (λ - → cₚ² base 𝟎 ⁻¹ ∙ cₚ² base -) lemma'' ⟩
        cₚ² base 𝟎 ⁻¹ ∙ cₚ² base (succ-ℤ 𝟎) ≡⟨ ap (λ - → cₚ² base 𝟎 ⁻¹ ∙ -) (cₚ³ base 𝟎) ⟩
        cₚ² base 𝟎 ⁻¹ ∙ (p ∙ cₚ² base 𝟎) ∎
   where
    lemma'' : ⌜ idtoeq ⟨ base ⟩ ⟨ base ⟩ (ap ⟨_⟩ loop) ⌝ 𝟎 ≡ succ-ℤ 𝟎
    lemma'' = ap (λ - → ⌜ - ⌝ 𝟎) xxx

  lll : {X : 𝓤 ̇ } {x y : X} (q : x ≡ y) (p : x ≡ x)
      → transport (λ - → - ≡ -) q p ≡ q ⁻¹ ∙ (p ∙ q)
  lll refl p = (refl ⁻¹ ∙ (p ∙ refl) ≡⟨ refl              ⟩
                refl ⁻¹ ∙ p          ≡⟨ refl-left-neutral ⟩
                p                    ∎                     ) ⁻¹

  mmm : ap cₚ¹ loop ≡ transport (λ - → - ≡ -) (cₚ² base 𝟎) p
  mmm = ap cₚ¹ loop                            ≡⟨ kkk ⟩
        cₚ² base 𝟎 ⁻¹ ∙ (p ∙ cₚ² base 𝟎)       ≡⟨ (lll (cₚ² base 𝟎) p) ⁻¹ ⟩
        transport (λ - → - ≡ -) (cₚ² base 𝟎) p ∎

\end{code}
