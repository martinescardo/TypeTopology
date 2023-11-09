Martin Escardo 1st May 2020.

This is ported from the Midlands Graduate School 2019 lecture notes

 https://www.cs.bham.ac.uk/~mhe/HoTT-UF.in-Agda-Lecture-Notes/HoTT-UF-Agda.html
 https://github.com/martinescardo/HoTT-UF.Agda-Lecture-Notes

\begin{code}

{-# OPTIONS --safe --without-K #-}

module MGS.Classifiers where

open import MGS.Map-Classifiers  public
open import MGS.Embeddings       public
open import MGS.Powerset         public
open import MGS.Universe-Lifting public

Subtypes : 𝓤 ̇ → 𝓤 ⁺ ̇
Subtypes {𝓤} Y = Σ X ꞉ 𝓤 ̇ , X ↪ Y

_/[_]_ : (𝓤 : Universe) → (𝓤 ̇ → 𝓥 ̇ ) → 𝓤 ̇ → 𝓤 ⁺ ⊔ 𝓥 ̇
𝓤 /[ P ] Y = Σ X ꞉ 𝓤 ̇ , Σ f ꞉ (X → Y) , ((y : Y) → P (fiber f y))

χ-special : (P : 𝓤 ̇ → 𝓥 ̇ ) (Y : 𝓤 ̇ ) → 𝓤 /[ P ] Y  → (Y → Σ P)
χ-special P Y (X , f , φ) y = fiber f y , φ y

is-special-map-classifier : (𝓤 ̇ → 𝓥 ̇ ) → 𝓤 ⁺ ⊔ 𝓥 ̇
is-special-map-classifier {𝓤} P = (Y : 𝓤 ̇ ) → is-equiv (χ-special P Y)

mc-gives-sc : is-map-classifier 𝓤
            → (P : 𝓤 ̇ → 𝓥 ̇ ) → is-special-map-classifier P

mc-gives-sc {𝓤} s P Y = γ
 where
  e = (𝓤 /[ P ] Y)                               ≃⟨ ≃-sym a ⟩
      (Σ σ ꞉ 𝓤 / Y , ((y : Y) → P ((χ Y) σ y)))  ≃⟨ ≃-sym b ⟩
      (Σ A ꞉ (Y → 𝓤 ̇ ), ((y : Y) → P (A y)))     ≃⟨ ≃-sym c ⟩
      (Y → Σ P)                                  ■
   where
    a = Σ-assoc
    b = Σ-change-of-variable (λ A → Π (P ∘ A)) (χ Y) (s Y)
    c = ΠΣ-distr-≃

  observation : χ-special P Y ＝ ⌜ e ⌝
  observation = refl _

  γ : is-equiv (χ-special P Y)
  γ = ⌜⌝-is-equiv e

χ-special-is-equiv : is-univalent 𝓤 → dfunext 𝓤 (𝓤 ⁺)
                   → (P : 𝓤 ̇ → 𝓥 ̇ ) (Y : 𝓤 ̇ )
                   → is-equiv (χ-special P Y)

χ-special-is-equiv {𝓤} ua fe P Y = mc-gives-sc (universes-are-map-classifiers ua fe) P Y

special-map-classifier : is-univalent 𝓤 → dfunext 𝓤 (𝓤 ⁺)
                       → (P : 𝓤 ̇ → 𝓥 ̇ ) (Y : 𝓤 ̇ )
                       → 𝓤 /[ P ] Y ≃ (Y → Σ P)

special-map-classifier {𝓤} ua fe P Y = χ-special P Y , χ-special-is-equiv ua fe P Y

Ω-is-subtype-classifier : Univalence
                        → (Y : 𝓤 ̇ ) → Subtypes Y ≃ (Y → Ω 𝓤)

Ω-is-subtype-classifier {𝓤} ua = special-map-classifier (ua 𝓤)
                                  (univalence-gives-dfunext' (ua 𝓤) (ua (𝓤 ⁺)))
                                  is-subsingleton

subtypes-form-set : Univalence → (Y : 𝓤 ̇ ) → is-set (Subtypes Y)
subtypes-form-set {𝓤} ua Y = equiv-to-set
                              (Ω-is-subtype-classifier ua Y)
                              (powersets-are-sets' ua)

𝓢 : (𝓤 : Universe) → 𝓤 ⁺ ̇
𝓢 𝓤 = Σ S ꞉ 𝓤 ̇ , is-singleton S

equiv-classification : Univalence
                     → (Y : 𝓤 ̇ ) → (Σ X ꞉ 𝓤 ̇ , X ≃ Y) ≃ (Y → 𝓢 𝓤)

equiv-classification {𝓤} ua = special-map-classifier (ua 𝓤)
                               (univalence-gives-dfunext' (ua 𝓤) (ua (𝓤 ⁺)))
                               is-singleton

the-singletons-form-a-singleton : propext 𝓤 → dfunext 𝓤 𝓤 → is-singleton (𝓢 𝓤)
the-singletons-form-a-singleton {𝓤} pe fe = c , φ
 where
  i : is-singleton (Lift 𝓤 𝟙)
  i = equiv-to-singleton (Lift-≃ 𝟙) 𝟙-is-singleton

  c : 𝓢 𝓤
  c = Lift 𝓤 𝟙 , i

  φ : (x : 𝓢 𝓤) → c ＝ x
  φ (S , s) = to-subtype-＝ (λ _ → being-singleton-is-subsingleton fe) p
   where
    p : Lift 𝓤 𝟙 ＝ S
    p = pe (singletons-are-subsingletons (Lift 𝓤 𝟙) i)
           (singletons-are-subsingletons S s)
           (λ _ → center S s) (λ _ → center (Lift 𝓤 𝟙) i)

univalence→-again : Univalence
                  → (Y : 𝓤 ̇ ) → is-singleton (Σ X ꞉ 𝓤 ̇ , X ≃ Y)

univalence→-again {𝓤} ua Y = equiv-to-singleton (equiv-classification ua Y) i
 where
  i : is-singleton (Y → 𝓢 𝓤)
  i = univalence-gives-vvfunext' (ua 𝓤) (ua (𝓤 ⁺))
        (λ y → the-singletons-form-a-singleton
                (univalence-gives-propext (ua 𝓤))
                (univalence-gives-dfunext (ua 𝓤)))

\end{code}
