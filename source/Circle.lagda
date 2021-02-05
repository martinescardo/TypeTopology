Tom de Jong, 28 January 2020
\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-Base
open import Integers

open import UF-Embeddings
open import UF-Equiv hiding (_≅_)
open import UF-EquivalenceExamples
open import UF-Equiv-FunExt
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
Tℤ = Σ X ꞉ 𝓤₀ ̇ , Σ f ꞉ (X → X) , ∥ (ℤ , succ-ℤ) ≡ (X , f) ∥

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



(base ≡ base) ≃ Σ e ꞉ (ℤ → ℤ) , is-equiv e
                             × (e ∘ succ-ℤ ≡ succ-ℤ e)
             ≃  Σ e ꞉ (ℤ → ℤ) , is-equiv e
                             × (e ∼ λ x → e 𝟎 +ℤ x)
             ≃  Σ e ꞉ (ℤ → ℤ) , is-equiv e
                             × (e ≡ λ x → e 𝟎 +ℤ x)
             ≃  Σ e ꞉ (ℤ → ℤ) , (e ∼ λ x → e 𝟎 +ℤ x)
             ≃ ℤ

-}

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
  (λ X f → ∥ (ℤ , succ-ℤ) ≡ (X , f) ∥)
  (λ X f → ∥∥-is-prop)

to-Tℤ-≡ : (X Y : Tℤ) → X ≅ Y → X ≡ Y
to-Tℤ-≡ X Y = ⌜ characterization-of-Tℤ-≡ X Y ⌝⁻¹

to-≃-of-⟨⟩ : (X Y : Tℤ) → X ≡ Y → ⟨ X ⟩ ≃ ⟨ Y ⟩
to-≃-of-⟨⟩ X Y q = pr₁ h , pr₁ (pr₂ h)
 where
  h : X ≅ Y
  h = (⌜ characterization-of-Tℤ-≡ X Y ⌝ q)

⟨_⟩₂ : (X : Tℤ) → ⟨ X ⟩ → ⟨ X ⟩
⟨ (X , f , _) ⟩₂ = f

⟨⟩-≃-commutes : (X Y : Tℤ) (q : X ≡ Y)
              → ⌜ to-≃-of-⟨⟩ X Y q ⌝ ∘ ⟨ X ⟩₂ ≡ ⟨ Y ⟩₂ ∘ ⌜ to-≃-of-⟨⟩ X Y q ⌝
⟨⟩-≃-commutes X Y q = pr₂ (pr₂ h)
 where
  h : X ≅ Y
  h = (⌜ characterization-of-Tℤ-≡ X Y ⌝ q)

{-
to-Tℤ-≡' : (X Y : Tℤ) → X ≃[Tℤ] Y → X ≡ Y
to-Tℤ-≡' X Y = ⌜ characterization-of-Tℤ-≡' X Y ⌝⁻¹

_≃[Tℤ⁻]_ : Tℤ⁻ → Tℤ⁻ → 𝓤₀ ̇
(X , f) ≃[Tℤ⁻] (Y , g) = Σ e ꞉ (X → Y) , is-equiv e
                                  × (e ∘ f ≡ g ∘ e)
-}

loop : base ≡ base
loop = to-Tℤ-≡ base base (succ-ℤ , succ-ℤ-is-equiv , refl)


\end{code}

\begin{code}

fundamental-group-of-circle-is-ℤ : (base ≡ base) ≃ ℤ
fundamental-group-of-circle-is-ℤ =
 (base ≡ base)                                            ≃⟨ I   ⟩
 (Σ e ꞉ (ℤ → ℤ) , is-equiv e × (e ∘ succ-ℤ ≡ succ-ℤ ∘ e)) ≃⟨ II  ⟩
 (Σ e ꞉ (ℤ → ℤ) , is-equiv e × (e ∘ succ-ℤ ∼ succ-ℤ ∘ e)) ≃⟨ III ⟩
 (Σ e ꞉ (ℤ → ℤ) , (e ∘ succ-ℤ ∼ succ-ℤ ∘ e) × is-equiv e) ≃⟨ IV  ⟩
 (Σ e ꞉ (ℤ → ℤ) , (e ∘ succ-ℤ ∼ succ-ℤ ∘ e))              ≃⟨ V   ⟩
 ℤ                                                        ■
  where
   fe : funext 𝓤₀ 𝓤₀
   fe = univalence-gives-funext ua
   I   = characterization-of-Tℤ-≡ base base
   II  = Σ-cong (λ e → ×-cong (≃-refl (is-equiv e))
                              (≃-funext fe (e ∘ succ-ℤ) (succ-ℤ ∘ e)))
   III = Σ-cong (λ e → ×-comm)
   IV  = Σ-cong γ
    where
     γ : (e : ℤ → ℤ)
       → (e ∘ succ-ℤ ∼ succ-ℤ ∘ e) × is-equiv e
       ≃ (e ∘ succ-ℤ ∼ succ-ℤ ∘ e)
     γ e = qinveq pr₁ (ϕ , η , ε)
      where
       ϕ : e ∘ succ-ℤ ∼ succ-ℤ ∘ e
         → (e ∘ succ-ℤ ∼ succ-ℤ ∘ e) × is-equiv e
       ϕ c = (c , commute-with-succ-ℤ-equiv e c)
       η : ϕ ∘ pr₁ ∼ id
       η (i , c) = to-subtype-≡ (λ _ → being-equiv-is-prop' fe fe fe fe e) refl
       ε : pr₁ ∘ ϕ ∼ id
       ε _ = refl
   V   = ℤ-symmetric-induction fe (λ _ → ℤ) (λ _ → succ-ℤ-≃)

\end{code}

\begin{code}

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
  ψ = ⌜ characterization-of-Tℤ-≡ base base ⌝⁻¹
  s : ϕ ∘ ψ ∼ id
  s = inverses-are-sections ϕ (⌜⌝-is-equiv (characterization-of-Tℤ-≡ base base))
  l : base ≅ base
  l = (succ-ℤ , succ-ℤ-is-equiv , refl)

module Tℤ-rec
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
   γ :  (ℤ , succ-ℤ) ≡ (X , f) → is-singleton (Qₚ (X , f))
   γ refl = Qₚ-base-is-singleton

 cₚ : ((X , f , _) : Tℤ) → Qₚ (X , f)
 cₚ (X , f , t) =
  ∥∥-rec (singletons-are-props (Qₚ-is-singleton (X , f , t)))
   (λ e → transport Qₚ e cₚ-base) t

{-
 cₚ-on-base : cₚ base ≡ cₚ-base
 cₚ-on-base = ∥∥-rec-comp (singletons-are-props (Qₚ-is-singleton base))
  (λ e → back-transport Qₚ e cₚ-base) refl
-}

 cₚ¹ : Tℤ → A
 cₚ¹ X = pr₁ (cₚ X)

{-
 cₚ¹-on-base : cₚ¹ base ≡ cₚ¹-base
 cₚ¹-on-base = ap pr₁ cₚ-on-base
-}

 cₚ² : (X : Tℤ) → (⟨ X ⟩ → a ≡ cₚ¹ X)
 cₚ² X = pr₁ (pr₂ (cₚ X))

{-
 cₚ²-on-base : cₚ² base ≡ back-transport (λ - → ℤ → a ≡ -) cₚ¹-on-base cₚ²-base
 cₚ²-on-base = {!!}
-}

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

 kkkk : ap cₚ¹ loop ≡ (cₚ² base 𝟎) ⁻¹ ∙ (p ∙ (cₚ² base 𝟎))
 kkkk = ap cₚ¹ loop ≡⟨ lemma' ⟩
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
 mmm = ap cₚ¹ loop                            ≡⟨ kkkk ⟩
       cₚ² base 𝟎 ⁻¹ ∙ (p ∙ cₚ² base 𝟎)       ≡⟨ (lll (cₚ² base 𝟎) p) ⁻¹ ⟩
       transport (λ - → - ≡ -) (cₚ² base 𝟎) p ∎

\end{code}

\begin{code}

module _
        -- {A : 𝓤 ̇ }
        -- (fe  : funext 𝓤  𝓤)
        (fe₀ : funext 𝓤₀ 𝓤₀)
        -- (fe₁ : funext 𝓤₁ 𝓤)
       where

 ⟨⟩₂-is-equiv : (X : Tℤ) → is-equiv ⟨ X ⟩₂
 ⟨⟩₂-is-equiv (X , f , t) = ∥∥-rec (being-equiv-is-prop' fe₀ fe₀ fe₀ fe₀ f) γ t
  where
   γ : (ℤ , succ-ℤ) ≡ (X , f) → is-equiv f
   γ refl = succ-ℤ-is-equiv

 ⟨⟩₂-≃ : (X : Tℤ) → ⟨ X ⟩ ≃ ⟨ X ⟩
 ⟨⟩₂-≃ X = (⟨ X ⟩₂ , ⟨⟩₂-is-equiv X)

 ⟨_⟩₂⁻¹ : (X : Tℤ) → ⟨ X ⟩ → ⟨ X ⟩
 ⟨ X ⟩₂⁻¹ = ⌜ ⟨⟩₂-≃ X ⌝⁻¹

 ⟨⟩₂-of-base-is-succ-ℤ : ⟨ base ⟩₂ ≡ succ-ℤ
 ⟨⟩₂-of-base-is-succ-ℤ = refl

 ⟨⟩₂⁻¹-of-base-is-pred-ℤ : ⟨ base ⟩₂⁻¹ ≡ pred-ℤ
 ⟨⟩₂⁻¹-of-base-is-pred-ℤ = ap ⌜_⌝⁻¹ γ
  where
   γ : ⟨⟩₂-≃ base ≡ succ-ℤ-≃
   γ = to-subtype-≡ (being-equiv-is-prop' fe₀ fe₀ fe₀ fe₀) refl

 ⟨⟩-≃-commutes⁻¹ : (X Y : Tℤ) (q : X ≡ Y)
                 → ⌜ to-≃-of-⟨⟩ X Y q ⌝⁻¹ ∘ ⟨ Y ⟩₂⁻¹
                 ≡ ⟨ X ⟩₂⁻¹ ∘ ⌜ to-≃-of-⟨⟩ X Y q ⌝⁻¹
 ⟨⟩-≃-commutes⁻¹ X Y q = γ
  where
   t : ⟨ X ⟩ ≃ ⟨ Y ⟩
   t = to-≃-of-⟨⟩ X Y q
   γ : ⌜ t ⌝⁻¹ ∘ ⟨ Y ⟩₂⁻¹ ≡ ⟨ X ⟩₂⁻¹ ∘ ⌜ t ⌝⁻¹
   γ = ⌜ t ⌝⁻¹ ∘ ⟨ Y ⟩₂⁻¹ ≡⟨ refl ⟩
       ⌜ ≃-comp t (⟨⟩₂-≃ Y) ⌝⁻¹ ≡⟨ ap ⌜_⌝⁻¹ ψ ⟩
       ⌜ ≃-comp (⟨⟩₂-≃ X) t ⌝⁻¹ ≡⟨ refl ⟩
       ⟨ X ⟩₂⁻¹ ∘ ⌜ t ⌝⁻¹ ∎
    where
     ψ : ≃-comp t (⟨⟩₂-≃ Y) ≡ ≃-comp (⟨⟩₂-≃ X) t
     ψ = to-subtype-≡ (being-equiv-is-prop' fe₀ fe₀ fe₀ fe₀)
          ((⟨⟩-≃-commutes X Y q) ⁻¹)

 ⟨⟩-is-set : (X : Tℤ) → is-set ⟨ X ⟩
 ⟨⟩-is-set (X , f , t) = ∥∥-rec (being-set-is-prop fe₀) γ t
  where
   γ : (ℤ , succ-ℤ) ≡ (X , f) → is-set X
   γ refl = ℤ-is-set

 Tℤ-action : (X : Tℤ) → ⟨ X ⟩ → ℤ → ⟨ X ⟩
 Tℤ-action X x 𝟎       = x
 Tℤ-action X x (pos n) = (⟨ X ⟩₂   ^ (succ n)) x
 Tℤ-action X x (neg n) = (⟨ X ⟩₂⁻¹ ^ (succ n)) x

 Tℤ-action-lemma : (X : Tℤ) (q : base ≡ X) (x : ⟨ X ⟩) (z : ℤ)
                 → Tℤ-action X x z
                 ≡ (⌜ to-≃-of-⟨⟩ base X q ⌝
                   ∘ succᶻ z
                   ∘ ⌜ to-≃-of-⟨⟩ base X q ⌝⁻¹) x
 Tℤ-action-lemma X q x 𝟎       = (≃-sym-is-rinv (to-≃-of-⟨⟩ base X q) x) ⁻¹
 Tℤ-action-lemma X q x (pos n) = γ n
  where
   t : ℤ ≃ ⟨ X ⟩
   t = to-≃-of-⟨⟩ base X q
   γ : (n : ℕ)
     → Tℤ-action X x (pos n) ≡ (⌜ t ⌝ ∘ (succ-ℤ ^ (succ n)) ∘ ⌜ t ⌝⁻¹) x
   γ zero     = ⟨ X ⟩₂ x                     ≡⟨ I  ⟩
                (⟨ X ⟩₂ ∘ ⌜ t ⌝ ∘ ⌜ t ⌝⁻¹) x ≡⟨ II ⟩
                (⌜ t ⌝ ∘ succ-ℤ ∘ ⌜ t ⌝⁻¹) x ∎
    where
     I  = ap ⟨ X ⟩₂ (≃-sym-is-rinv t x) ⁻¹
     II = happly ((⟨⟩-≃-commutes base X q) ⁻¹) (⌜ t ⌝⁻¹ x)
   γ (succ n) = (⟨ X ⟩₂ ∘ (⟨ X ⟩₂ ^ (succ n))) x                 ≡⟨ I  ⟩
                (⟨ X ⟩₂ ∘ ⌜ t ⌝ ∘ succ-ℤ ^ (succ n) ∘ ⌜ t ⌝⁻¹) x ≡⟨ II ⟩
                (⌜ t ⌝ ∘ (succ-ℤ ^ succ (succ n)) ∘ ⌜ t ⌝⁻¹) x ∎
    where
     I  = ap ⟨ X ⟩₂ (γ n)
     II = happly ((⟨⟩-≃-commutes base X q) ⁻¹)
           (((succ-ℤ ^ (succ n)) ∘ ⌜ t ⌝⁻¹) x)
 Tℤ-action-lemma X q x (neg n) = γ n x
  where
   t : ℤ ≃ ⟨ X ⟩
   t = to-≃-of-⟨⟩ base X q
   γ : (n : ℕ) (x : ⟨ X ⟩)
     → Tℤ-action X x (neg n) ≡ (⌜ t ⌝ ∘ (pred-ℤ ^ (succ n)) ∘ ⌜ t ⌝⁻¹) x
   γ zero x    = I ∙ (II ∙ III)
    {-
       The equational reasoning below is very slow to typecheck. I suspect it is
       because one of the types is equal to, but not quite what Agda expects to
       see, triggering some huge normalization procedure. I also suspect that
       adding the --experimental-lossy-unification flags speeds up the
       typechecking.

       ⟨ X ⟩₂⁻¹                        x ≡⟨ I   ⟩
       (⌜ t ⌝ ∘ ⌜ t ⌝⁻¹ ∘ ⟨ X ⟩₂⁻¹)    x ≡⟨ II  ⟩
       (⌜ t ⌝ ∘ ⟨ base ⟩₂⁻¹ ∘ ⌜ t ⌝⁻¹) x ≡⟨ III ⟩
       (⌜ t ⌝ ∘ pred-ℤ ∘ ⌜ t ⌝⁻¹)      x ∎
    -}
    where
     I   = (≃-sym-is-rinv t (⟨ X ⟩₂⁻¹ x)) ⁻¹
     II  = ap (λ - → (⌜ t ⌝ ∘ -) x) (⟨⟩-≃-commutes⁻¹ _ _ q)
     III = ap ⌜ t ⌝ (happly ⟨⟩₂⁻¹-of-base-is-pred-ℤ (⌜ t ⌝⁻¹ x))
   γ (succ n) x = I ∙ (II ∙ (III ∙ (IV ∙ V)))
    {-
       (⟨ X ⟩₂⁻¹ ∘ (⟨ X ⟩₂⁻¹ ^ (succ n)))                  x ≡⟨ I   ⟩
       ((⟨ X ⟩₂⁻¹ ^ (succ n)) ∘ ⟨ X ⟩₂⁻¹)                  x ≡⟨ II  ⟩
       (⌜ t ⌝ ∘ pred-ℤ ^ (succ n) ∘ ⌜ t ⌝⁻¹ ∘ ⟨ X ⟩₂⁻¹)    x ≡⟨ III ⟩
       (⌜ t ⌝ ∘ pred-ℤ ^ (succ n) ∘ ⟨ base ⟩₂⁻¹ ∘ ⌜ t ⌝⁻¹) x ≡⟨ IV  ⟩
       (⌜ t ⌝ ∘ pred-ℤ ^ (succ n) ∘ pred-ℤ ∘ ⌜ t ⌝⁻¹)      x ≡⟨ V   ⟩
       (⌜ t ⌝ ∘ (pred-ℤ ^ succ (succ n)) ∘ ⌜ t ⌝⁻¹)        x ∎
    -}
    where
     I   = commute-with-iterated-function ⟨ X ⟩₂⁻¹ ⟨ X ⟩₂⁻¹
            (λ _ → refl) (succ n) x
     II  = γ n (⟨ X ⟩₂⁻¹ x)
     III = ap (λ - → (⌜ t ⌝ ∘ pred-ℤ ^ (succ n) ∘ -) x) (⟨⟩-≃-commutes⁻¹ _ _ q)
     IV  = ap (⌜ t ⌝ ∘ pred-ℤ ^ (succ n))
            (happly ⟨⟩₂⁻¹-of-base-is-pred-ℤ (⌜ t ⌝⁻¹ x))
     V   = ap ⌜ t ⌝
            ((commute-with-iterated-function pred-ℤ pred-ℤ (λ _ → refl) (succ n)
               (⌜ t ⌝⁻¹ x)) ⁻¹)

 Tℤ-action-is-equiv : (X : Tℤ) (x : ⟨ X ⟩)
                           → is-equiv (Tℤ-action X x)
 Tℤ-action-is-equiv (X , f , t) x =
  ∥∥-rec (being-equiv-is-prop' fe₀ fe₀ fe₀ fe₀
   (Tℤ-action (X , f , t) x)) γ t
   where
    γ : (ℤ , succ-ℤ) ≡ (X , f)
      → is-equiv (Tℤ-action (X , f , t) x)
    γ refl = {!ψ x!}
     where
      ψ : (z : ℤ) → is-equiv (Tℤ-action base z)
      ψ 𝟎 = equiv-closed-under-∼ id (Tℤ-action base 𝟎) (id-is-equiv ℤ) rrr
       where
        rrr : Tℤ-action base 𝟎 ∼ id
        rrr 𝟎 = refl
        rrr (pos n) = (pos-succ-ℤ-iterated n) ⁻¹
        rrr (neg n) = (neg-pred-ℤ-iterated n ∙
                       happly (ap (λ - → - ^ succ n)
                        (⟨⟩₂⁻¹-of-base-is-pred-ℤ ⁻¹)) 𝟎) ⁻¹
      ψ (pos n) = {!!}
       where
        rrr : Tℤ-action base (pos n) ∼ (succ-ℤ ^ (succ n))
        rrr 𝟎 = pos-succ-ℤ-iterated n
        rrr (pos m) = {!!}
        rrr (neg m) = {!!}

{-
 Tℤ-action-is-equiv : (X : Tℤ) (x : ⟨ X ⟩)
                           → is-equiv (Tℤ-action X x)
 Tℤ-action-is-equiv (X , f , t) x =
  ∥∥-rec (being-equiv-is-prop' fe₀ fe₀ fe₀ fe₀
   (Tℤ-action (X , f , t) x)) γ t
   where
    γ : (ℤ , succ-ℤ) ≡ (X , f)
      → is-equiv (Tℤ-action (X , f , t) x)
    γ q = qinvs-are-equivs (Tℤ-action (X , f , t) x) (φ , η , ε)
     where
      q⁺ : base ≡ (X , f , t)
      q⁺ = ap ⌜ Σ-assoc ⌝ (to-subtype-≡ (λ _ → ∥∥-is-prop) q)
      e : ℤ ≃ X
      e = to-≃-of-⟨⟩ base (X , f , t) q⁺
      φ : X → ℤ
      φ y = succᶻ⁻¹ (⌜ e ⌝⁻¹ x) (⌜ e ⌝⁻¹ y) -- succᶻ⁻¹ (⌜ e ⌝⁻¹ y) (⌜ e ⌝⁻¹ x)
      η : φ ∘ (Tℤ-action (X , f , t) x) ∼ id
      η z = φ (Tℤ-action (X , f , t) x z) ≡⟨ ap φ (Tℤ-action-lemma (X , f , t) q⁺ x z) ⟩
            φ ((⌜ e ⌝ ∘ succᶻ z ∘ ⌜ e ⌝⁻¹) x) ≡⟨ refl ⟩
            succᶻ⁻¹ (⌜ e ⌝⁻¹ x) ((⌜ e ⌝⁻¹ ∘ ⌜ e ⌝ ∘ succᶻ z ∘ ⌜ e ⌝⁻¹) x) ≡⟨ {!!} ⟩
            succᶻ⁻¹ (⌜ e ⌝⁻¹ x) (succᶻ z (⌜ e ⌝⁻¹ x)) ≡⟨ succᶻ⁻¹-retraction-of-succᶻ {!!} {!!} ⟩
            {!!} ≡⟨ {!!} ⟩
            {!!} ∎
      {-
      η 𝟎 = φ ((Tℤ-action (X , f , t) x) 𝟎) ≡⟨ ap φ (Tℤ-action-lemma (X , f , t) q⁺ x 𝟎) ⟩
            (φ ∘ ⌜ e ⌝ ∘ ⌜ e ⌝⁻¹) x ≡⟨ refl ⟩
            succᶻ⁻¹ (⌜ e ⌝⁻¹ (⌜ e ⌝ (⌜ e ⌝⁻¹ x))) (⌜ e ⌝⁻¹ x) ≡⟨ {!!} ⟩
            {!!} ≡⟨ {!!} ⟩
            id 𝟎 ∎ -}
      ε : (λ x₁ → Tℤ-action (X , f , t) x (φ x₁)) ∼ (λ x₁ → x₁)
      ε = {!!}
-}

{-

                 → Tℤ-action X x z
                 ≡ (⌜ to-≃-of-⟨⟩ base X q ⌝
                   ∘ succᶻ z
                   ∘ ⌜ to-≃-of-⟨⟩ base X q ⌝⁻¹) x

-}

 generalized-loop-≅ : (X : Tℤ) → ⟨ X ⟩ → base ≅ X
 generalized-loop-≅ (X , f , t) x = e , i , {!!}
  where
   f⁻¹ : X → X
   f⁻¹ = inverse f (⟨⟩₂-is-equiv (X , f , t))
   e : ℤ → X
   e 𝟎       =           x
   e (pos n) = (f   ^ n) x
   e (neg n) = (f⁻¹ ^ n) x
   e⁻¹ : X → ℤ
   e⁻¹ y = {!!}
   i : is-equiv e
   i = qinvs-are-equivs (λ z → e z) {!!}

\end{code}

 module _
         (f : Tℤ → A)
        where

  open Tℤ-rec {𝓤} {A} fe (ap f loop)

  lift-to-Qₚ : (Y : Tℤ) → Qₚ (⟨ Y ⟩ , ⟨ Y ⟩₂)
  lift-to-Qₚ (Y , g , t) = (f (Y , g , t)) , ({!!} , {!!})

\end{code}

module _
        {A : 𝓤 ̇ }
        (fe  : funext 𝓤  𝓤)
        (fe₁ : funext 𝓤₁ 𝓤)
       where

 open Tℤ-rec {𝓤} {A} fe

 szzz : (X : Tℤ) → ⟨ X ⟩ → base ≡ X
 szzz (X , f , t) x = to-Tℤ-≡ base (X , f , t) γ
  where
   γ : (ℤ , succ-ℤ , ∣ refl ∣) ≅ (X , f , t)
   γ = e , {!!} , {!!}
    where
     f⁻¹ : X → X
     f⁻¹ = {!!}
     e : ℤ → X
     e 𝟎       = f x
     e (pos n) = (f ^ (succ n)) x

 -- Lemma 4.9
 qqqq : ((X , f , t) : Tℤ) (x : X)
      → szzz (X , f , t) (f x) ≡ loop ∙ szzz (X , f , t) x
 qqqq (X , f , t) x = {!!}

 universal-property : (Tℤ → A) ≃ (Σ a ꞉ A , a ≡ a)
 universal-property = qinveq ϕ (ψ , η , ε)
  where
   ϕ : (Tℤ → A) → (Σ a ꞉ A , a ≡ a)
   ϕ f = f base , ap f loop
   ψ : (Σ a ꞉ A , a ≡ a) → Tℤ → A
   ψ (a , p) = cₚ¹ p
   ε : ϕ ∘ ψ ∼ id
   ε (a , p) = (cₚ¹ p base , ap (cₚ¹ p) loop)                          ≡⟨ to-Σ-≡ (refl , (mmm p)) ⟩
               (cₚ¹ p base , transport (λ - → - ≡ -) (cₚ² p base 𝟎) p) ≡⟨ (to-Σ-≡ ((cₚ² p base 𝟎) , refl)) ⁻¹ ⟩
               (a , p)                                                 ∎
   η : ψ ∘ ϕ ∼ id
   -- We need Lemma 6.2.8 (uniqueness principle) of the HoTT Book here, which is proved using the induction principle.
   -- We won't prove the induction principle, but instead just prove this instance using the techniques of
   -- Bezem, Buchholtz, Grayson and Shulman.
   -- After all, the induction principle will have propositional computation rules which involve lots of transport.
   -- So, the universal property seems nicer anyway. Besides, according to the HoTT Book it is possible to derive
   -- the induction principle (with propositional computation rules) from the universal property. (We hope to do this with
   -- an abstract proof that avoids the complications of Tℤ and Bezem et al.)
   η f = dfunext fe₁ γ
    where
     γ : (Y : Tℤ) → cₚ¹ (ap f loop) Y ≡ f Y
     γ Y = ap pr₁ (singletons-are-props (Qₚ-is-singleton (ap f loop) Y) (cₚ (ap f loop) Y) f⁺)
      where
       f⁺ : Qₚ (ap f loop) (pr₁ Y , pr₁ (pr₂ Y))
       f⁺ = (f Y) , (e , tsss)
        where
         e : ⟨ Y ⟩ → f base ≡ f Y
         e y = ap f (szzz Y y)
         g : ⟨ Y ⟩ → ⟨ Y ⟩
         g = pr₁ (pr₂ Y)
         tsss : (y : ⟨ Y ⟩) → e (g y) ≡ ap f loop ∙ e y
         tsss y = e (g y)                     ≡⟨ refl ⟩
                  ap f (szzz Y (g y))         ≡⟨ ap (ap f) (qqqq Y y) ⟩
                  ap f (loop ∙ (szzz Y y))    ≡⟨ ap-∙ f loop (szzz Y y) ⟩
                  ap f loop ∙ ap f (szzz Y y) ≡⟨ refl ⟩
                  ap f loop ∙ e y             ∎

\end{code}
