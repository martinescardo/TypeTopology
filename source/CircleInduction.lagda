Tom de Jong, 1 March 2021
\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-Base

open import UF-Equiv
open import UF-Subsingletons

module CircleInduction
        (𝕊¹ : 𝓤 ̇ )
        (base : 𝕊¹)
        (loop : base ≡ base)
       where

𝕊¹-universal-map : (A : 𝓥 ̇ )
                  → (𝕊¹ → A) → (Σ a ꞉ A , a ≡ a)
𝕊¹-universal-map A f = (f base) , (ap f loop)

module _
        (𝕊¹-universal-property : {𝓥 : Universe} (A : 𝓥 ̇ )
                               → is-equiv (𝕊¹-universal-map A))
       where

 𝕊¹-uniqueness-principle : {A : 𝓥 ̇ } (a : A) (p : a ≡ a)
                         → ∃! r ꞉ (𝕊¹ → A) , (r base , ap r loop) ≡ (a , p)
 𝕊¹-uniqueness-principle {𝓥} {A} a p =
   equivs-are-vv-equivs (𝕊¹-universal-map A)
                        (𝕊¹-universal-property A) (a , p)

 𝕊¹-uniqueness-principle-≡ : {A : 𝓥 ̇ } (f g : 𝕊¹ → A)
                           → (f base , ap f loop)
                           ≡[ Σ a ꞉ A , a ≡ a ] (g base , ap g loop)
                           → f ≡ g
 𝕊¹-uniqueness-principle-≡ {𝓥} {A} f g p =
  ap pr₁ (singletons-are-props (𝕊¹-uniqueness-principle ( f base) (ap f loop))
                                                        (f , refl) (g , (p ⁻¹)))

 --TO DO: DUPLICATION
 transport-along-≡-dup : {X : 𝓤 ̇ } {x y : X} (q : x ≡ y) (p : x ≡ x)
                       → transport (λ - → - ≡ -) q p ≡ q ⁻¹ ∙ (p ∙ q)
 transport-along-≡-dup refl p = (refl ⁻¹ ∙ (p ∙ refl) ≡⟨ refl              ⟩
                                 refl ⁻¹ ∙ p          ≡⟨ refl-left-neutral ⟩
                                 p                    ∎                     ) ⁻¹

 𝕊¹-induction : (A : 𝕊¹ → 𝓤 ̇ )
              → (a : A base)
              → transport A loop a ≡ a
              → (x : 𝕊¹) → A x
 𝕊¹-induction A a l x = transport A (happly lemma x) (pr₂ (r x))
  where
   χ : (𝕊¹ → Σ A) ≃ (Σ y ꞉ (Σ A) , y ≡ y)
   χ = 𝕊¹-universal-map (Σ A) , 𝕊¹-universal-property (Σ A)
   l⁺ : Σ y ꞉ (Σ A) , y ≡ y
   l⁺ = ((base , a) , to-Σ-≡ (loop , l))
   r : 𝕊¹ → Σ A
   r = ⌜ χ ⌝⁻¹ l⁺
   lemma : pr₁ ∘ r ≡ id
   lemma = 𝕊¹-uniqueness-principle-≡ (pr₁ ∘ r) id γ
    where
     γ : ((pr₁ ∘ r) base , ap (pr₁ ∘ r) loop) ≡ (base , ap id loop)
     γ = to-Σ-≡ (d₁ , ϕ)
      where
       c : r base , ap r loop ≡ l⁺
       c = r base , ap r loop ≡⟨ refl ⟩
           ⌜ χ ⌝ r            ≡⟨ refl ⟩
           ⌜ χ ⌝ (⌜ χ ⌝⁻¹ l⁺) ≡⟨ σ    ⟩
           l⁺                 ∎
        where
         σ = inverses-are-sections ⌜ χ ⌝ (⌜⌝-is-equiv χ) l⁺
       c₁ : r base ≡ pr₁ l⁺
       c₁ = pr₁ (from-Σ-≡ c)
       d₁ : pr₁ (r base) ≡ pr₁ (pr₁ l⁺)
       d₁ = ap pr₁ c₁
       ϕ = transport (λ - → - ≡ -) d₁ (ap (pr₁ ∘ r) loop)  ≡⟨ I    ⟩
           d₁ ⁻¹ ∙ (ap (pr₁ ∘ r) loop ∙ d₁)                ≡⟨ II   ⟩
           d₁ ⁻¹ ∙ (ap pr₁ (ap r loop) ∙ d₁)               ≡⟨ refl ⟩
           d₁ ⁻¹ ∙ (ap pr₁ (ap r loop) ∙ (ap pr₁ c₁))      ≡⟨ III  ⟩
           d₁ ⁻¹ ∙ ap pr₁ (ap r loop ∙ c₁)                 ≡⟨ refl ⟩
           (ap pr₁ c₁) ⁻¹ ∙ ap pr₁ (ap r loop ∙ c₁)        ≡⟨ IV   ⟩
           ap pr₁ (c₁ ⁻¹) ∙ ap pr₁ (ap r loop ∙ c₁)        ≡⟨ V    ⟩
           ap pr₁ (c₁ ⁻¹ ∙ (ap r loop ∙ c₁))               ≡⟨ VI   ⟩
           ap pr₁ (transport (λ - → - ≡ -) c₁ (ap r loop)) ≡⟨ VII  ⟩
           ap pr₁ (pr₂ l⁺)                                 ≡⟨ refl ⟩
           ap pr₁ (to-Σ-≡ (loop , l))                      ≡⟨ VIII ⟩
           loop                                            ≡⟨ IX   ⟩
           ap id loop                                      ∎
        where
         I    = transport-along-≡-dup d₁ (ap (pr₁ ∘ r) loop)
         II   = ap (λ - → d₁ ⁻¹ ∙ (- ∙ d₁)) ((ap-ap r pr₁ loop) ⁻¹)
         III  = ap (λ - → d₁ ⁻¹ ∙ -) ((ap-∙ pr₁ (ap r loop) c₁) ⁻¹)
         IV   = ap (λ - → - ∙ ap pr₁ (ap r loop ∙ c₁)) (ap-sym pr₁ c₁)
         V    = (ap-∙ pr₁ (c₁ ⁻¹) (ap r loop ∙ c₁)) ⁻¹
         VI   = ap (ap pr₁) ((transport-along-≡-dup c₁ (ap r loop)) ⁻¹)
         VII  = ap (ap pr₁) (pr₂ (from-Σ-≡ c))
         VIII = ap-pr₁-to-Σ-≡ (loop , l)
         IX   = (ap-id-is-id loop) ⁻¹

\end{code}
