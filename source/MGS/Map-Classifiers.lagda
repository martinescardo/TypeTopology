Martin Escardo 1st May 2020.

This is ported from the Midlands Graduate School 2019 lecture notes

 https://www.cs.bham.ac.uk/~mhe/HoTT-UF.in-Agda-Lecture-Notes/HoTT-UF-Agda.html
 https://github.com/martinescardo/HoTT-UF.Agda-Lecture-Notes

\begin{code}

{-# OPTIONS --safe --without-K #-}

module MGS.Map-Classifiers where

open import MGS.FunExt-from-Univalence public

_/_ : (𝓤 : Universe) → 𝓥 ̇ → 𝓤 ⁺ ⊔ 𝓥 ̇
𝓤 / Y = Σ X ꞉ 𝓤 ̇ , (X → Y)

total-fiber-is-domain : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                      → Σ (fiber f) ≃ X

total-fiber-is-domain {𝓤} {𝓥} {X} {Y} f = invertibility-gives-≃ g (h , η , ε)
 where
  g : (Σ y ꞉ Y , Σ x ꞉ X , f x ＝ y) → X
  g (y , x , p) = x

  h : X → Σ y ꞉ Y , Σ x ꞉ X , f x ＝ y
  h x = (f x , x , refl (f x))

  η : ∀ t → h (g t) ＝ t
  η (_ , x , refl _) = refl (f x , x , refl _)

  ε : (x : X) → g (h x) ＝ x
  ε = refl

χ : (Y : 𝓤 ̇ ) → 𝓤 / Y  → (Y → 𝓤 ̇ )
χ Y (X , f) = fiber f

is-map-classifier : (𝓤 : Universe) → 𝓤 ⁺ ̇
is-map-classifier 𝓤 = (Y : 𝓤 ̇ ) → is-equiv (χ Y)

𝕋 : (Y : 𝓤 ̇ ) → (Y → 𝓤 ̇ ) → 𝓤 / Y
𝕋 Y A = Σ A , pr₁

χη : is-univalent 𝓤
   → (Y : 𝓤 ̇ ) (σ : 𝓤 / Y) → 𝕋 Y (χ Y σ) ＝ σ

χη ua Y (X , f) = r
 where
  e : Σ (fiber f) ≃ X
  e = total-fiber-is-domain f

  p : Σ (fiber f) ＝ X
  p = Eq→Id ua (Σ (fiber f)) X e

  observation : ⌜ ≃-sym e ⌝ ＝ (λ x → f x , x , refl (f x))
  observation = refl _

  q = transport (λ - → - → Y) p pr₁ ＝⟨ transport-map-along-≃ ua e pr₁ ⟩
      pr₁ ∘ ⌜ ≃-sym e ⌝             ＝⟨ refl _ ⟩
      f                             ∎

  r : (Σ (fiber f) , pr₁) ＝ (X , f)
  r = to-Σ-＝ (p , q)

χε : is-univalent 𝓤 → dfunext 𝓤 (𝓤 ⁺)
   → (Y : 𝓤 ̇ ) (A : Y → 𝓤 ̇ ) → χ Y (𝕋 Y A) ＝ A

χε ua fe Y A = fe γ
 where
  f : ∀ y → fiber pr₁ y → A y
  f y ((y , a) , refl p) = a

  g : ∀ y → A y → fiber pr₁ y
  g y a = (y , a) , refl y

  η : ∀ y σ → g y (f y σ) ＝ σ
  η y ((y , a) , refl p) = refl ((y , a) , refl p)

  ε : ∀ y a → f y (g y a) ＝ a
  ε y a = refl a

  γ : ∀ y → fiber pr₁ y ＝ A y
  γ y = Eq→Id ua _ _ (invertibility-gives-≃ (f y) (g y , η y , ε y))

universes-are-map-classifiers : is-univalent 𝓤 → dfunext 𝓤 (𝓤 ⁺)
                              → is-map-classifier 𝓤

universes-are-map-classifiers ua fe Y = invertibles-are-equivs (χ Y)
                                         (𝕋 Y , χη ua Y , χε ua fe Y)

map-classification : is-univalent 𝓤 → dfunext 𝓤 (𝓤 ⁺)
                   → (Y : 𝓤 ̇ ) → 𝓤 / Y ≃ (Y → 𝓤 ̇ )

map-classification ua fe Y = χ Y , universes-are-map-classifiers ua fe Y

\end{code}
