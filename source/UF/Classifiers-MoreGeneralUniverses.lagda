Martin Escardo 11th Sepember 2022

This generalizes some universe levels of UF.Classifiers. Not all
universe levels can be generalized. The file UF.Classifiers should be
kept as is. It has more things, and I also want this as an example of
how, sometimes, it is not trivial to generalize univese levels.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module UF.Classifiers-MoreGeneralUniverses where

open import MLTT.Spartan

open import UF.Base
open import UF.Embeddings
open import UF.Equiv
open import UF.Equiv-FunExt
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.Powerset hiding (𝕋)
open import UF.PropIndexedPiSigma
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.UA-FunExt
open import UF.Univalence
open import UF.Yoneda

_/_ : (𝓤 : Universe) → 𝓥 ̇ → 𝓤 ⁺ ⊔ 𝓥 ̇
𝓤 / Y = Σ X ꞉ 𝓤 ̇ , (X → Y)

_/[_]_ : (𝓤 : Universe) → (𝓤 ⊔ 𝓥 ̇ → 𝓦 ̇ ) → 𝓥 ̇ → 𝓤 ⁺ ⊔ 𝓥 ⊔ 𝓦 ̇
𝓤 /[ P ] Y = Σ X ꞉ 𝓤 ̇ , Σ f ꞉ (X → Y) , ((y : Y) → P (fiber f y))

\end{code}

We now work with two universes 𝓤 ⊑ 𝓑. Because Agda can't express such
inequalities directly, we instead work with universes 𝓤 and 𝓥 and set 𝓑 = 𝓤 ⊔ 𝓥. But then we shouldn't mention 𝓥.

\begin{code}

module general-classifier (𝓤 𝓥 : Universe) where

 𝓑 𝓑⁺ : Universe
 𝓑 = 𝓤 ⊔ 𝓥
 𝓑⁺ = 𝓑 ⁺

 χ : (Y : 𝓤 ̇ ) → 𝓑 / Y  → (Y → 𝓑 ̇ )
 χ Y (X , f) = fiber f

\end{code}

Definition of when the given pair of universes is a map classifier,
more commonly known as an object classifier:

\begin{code}

 is-map-classifier : 𝓑⁺ ̇
 is-map-classifier = (Y : 𝓤 ̇ ) → is-equiv (χ Y)

 𝕋 : (Y : 𝓤 ̇ ) → (Y → 𝓑 ̇ ) → 𝓑 / Y
 𝕋 Y A = Σ A , pr₁

 χη : is-univalent 𝓑
    → (Y : 𝓤 ̇ ) (σ : 𝓑 / Y) → 𝕋 Y (χ Y σ) ＝ σ
 χη ua Y (X , f) = r
  where
   e : Σ (fiber f) ≃ X
   e = total-fiber-is-domain f

   p : Σ (fiber f) ＝ X
   p = eqtoid ua (Σ (fiber f)) X e

   observation : ⌜ e ⌝⁻¹ ＝ (λ x → f x , x , refl)
   observation = refl

   q = transport (λ - → - → Y) p pr₁ ＝⟨ transport-is-pre-comp' ua e pr₁ ⟩
       pr₁ ∘ ⌜ e ⌝⁻¹                 ＝⟨ refl ⟩
       f                             ∎

   r : (Σ (fiber f) , pr₁) ＝ (X , f)
   r = to-Σ-＝ (p , q)

 χε : is-univalent 𝓑
    → funext 𝓤 𝓑⁺
    → (Y : 𝓤 ̇ ) (A : Y → 𝓑 ̇ ) → χ Y (𝕋 Y A) ＝ A
 χε ua fe Y A = dfunext fe γ
  where
   f : ∀ y → fiber pr₁ y → A y
   f y ((y , a) , refl) = a
   g : ∀ y → A y → fiber pr₁ y
   g y a = (y , a) , refl
   η : ∀ y σ → g y (f y σ) ＝ σ
   η y ((y , a) , refl) = refl
   ε : ∀ y a → f y (g y a) ＝ a
   ε y a = refl
   γ : ∀ y → fiber pr₁ y ＝ A y
   γ y = eqtoid ua _ _ (qinveq (f y) (g y , η y , ε y))

 universes-are-map-classifiers : is-univalent 𝓑
                               → funext 𝓤 𝓑⁺
                               → is-map-classifier
 universes-are-map-classifiers ua fe Y = qinvs-are-equivs (χ Y)
                                          (𝕋 Y , χη ua Y , χε ua fe Y)

 map-classification : is-univalent 𝓑
                    → funext 𝓤 𝓑⁺
                    → (Y : 𝓤 ̇ ) → 𝓑 / Y ≃ (Y → 𝓑 ̇ )
 map-classification ua fe Y = χ Y , universes-are-map-classifiers ua fe Y

\end{code}

We now need to assume a further universe 𝓦

\begin{code}

module special-classifier (𝓤 𝓥 𝓦 : Universe) where

 open general-classifier 𝓤 𝓥 public

 χ-special : (P : 𝓑 ̇ → 𝓦 ̇ ) (Y : 𝓤 ̇ ) → 𝓑 /[ P ] Y  → (Y → Σ P)
 χ-special P Y (X , f , φ) y = fiber f y , φ y

 is-special-map-classifier : (𝓑 ̇ → 𝓦 ̇ ) → 𝓑⁺ ⊔ 𝓦 ̇
 is-special-map-classifier P = (Y : 𝓤 ̇ ) → is-equiv (χ-special P Y)

 mc-gives-sc : is-map-classifier
             → (P : 𝓑 ̇ → 𝓦 ̇ ) → is-special-map-classifier P
 mc-gives-sc s P Y = γ
  where
   e = (𝓑 /[ P ] Y)                               ≃⟨ a ⟩
       (Σ σ ꞉ 𝓑 / Y , ((y : Y) → P ((χ Y) σ y)))  ≃⟨ b ⟩
       (Σ A ꞉ (Y → 𝓑 ̇ ), ((y : Y) → P (A y)))     ≃⟨ c ⟩
       (Y → Σ P)                                  ■
    where
     a = ≃-sym Σ-assoc
     b = Σ-change-of-variable (λ A → Π (P ∘ A)) (χ Y) (s Y)
     c = ≃-sym ΠΣ-distr-≃

   observation : χ-special P Y ＝ ⌜ e ⌝
   observation = refl

   γ : is-equiv (χ-special P Y)
   γ = ⌜⌝-is-equiv e

 χ-special-is-equiv : is-univalent 𝓑
                    → funext 𝓤 𝓑⁺
                    → (P : 𝓑 ̇ → 𝓦 ̇ ) (Y : 𝓤 ̇ )
                    → is-equiv (χ-special P Y)
 χ-special-is-equiv ua fe P Y = mc-gives-sc (universes-are-map-classifiers ua fe) P Y

 special-map-classifier : is-univalent 𝓑
                        → funext 𝓤 𝓑⁺
                        → (P : 𝓑 ̇ → 𝓦 ̇ ) (Y : 𝓤 ̇ )
                        → 𝓑 /[ P ] Y ≃ (Y → Σ P)
 special-map-classifier ua fe P Y = χ-special P Y , χ-special-is-equiv ua fe P Y


Ω-is-subtype-classifier : is-univalent (𝓤 ⊔ 𝓥)
                        → funext 𝓤 ((𝓤 ⊔ 𝓥)⁺)
                        → (Y : 𝓤 ̇ )
                        → Subtypes' (𝓤 ⊔ 𝓥) Y ≃ (Y → Ω (𝓤 ⊔ 𝓥))
Ω-is-subtype-classifier {𝓤} {𝓥} ua fe = special-map-classifier ua fe
                                            is-subsingleton
 where
  open special-classifier 𝓤 𝓥 (𝓤 ⊔ 𝓥)

subtypes-form-set : Univalence → (Y : 𝓤 ̇ ) → is-set (Subtypes' (𝓤 ⊔ 𝓥) Y)
subtypes-form-set {𝓤} {𝓥} ua Y =
 equiv-to-set
  (Ω-is-subtype-classifier {𝓤} {𝓥}
    (ua (𝓤 ⊔ 𝓥))
    (univalence-gives-funext' 𝓤 ((𝓤 ⊔ 𝓥)⁺)
      (ua 𝓤)
      (ua ((𝓤 ⊔ 𝓥)⁺)))
    Y)
  (powersets-are-sets''
    (univalence-gives-funext' _ _ (ua 𝓤) (ua ((𝓤 ⊔ 𝓥)⁺)))
    (univalence-gives-funext' _ _ (ua (𝓤 ⊔ 𝓥)) (ua (𝓤 ⊔ 𝓥)))
    (univalence-gives-propext (ua (𝓤 ⊔ 𝓥))))

\end{code}

9th September 2022, with universe levels generalized 11
September. Here is an application of the above.

\begin{code}

Σ-fibers-≃ : {𝓤 𝓥 : Universe}
           → is-univalent (𝓤 ⊔ 𝓥)
           → funext 𝓤 ((𝓤 ⊔ 𝓥)⁺)
           → {X : 𝓤 ⊔ 𝓥 ̇ } {Y : 𝓤 ̇ }
           → (Σ A ꞉ (Y → 𝓤 ⊔ 𝓥 ̇ ) , Σ A ≃ X) ≃ (X → Y)
Σ-fibers-≃ {𝓤} {𝓥} ua fe⁺ {X} {Y} =
  (Σ A ꞉ (Y → 𝓑 ̇ ) , Σ A ≃ X)                            ≃⟨ I ⟩
  (Σ (Z , g) ꞉ (𝓑) / Y , (Σ y ꞉ Y , fiber g y) ≃ X)      ≃⟨ II ⟩
  (Σ Z ꞉ 𝓑 ̇ , Σ g ꞉ (Z → Y) , (Σ y ꞉ Y , fiber g y) ≃ X) ≃⟨ III ⟩
  (Σ Z ꞉ 𝓑 ̇ , (Z → Y) × (Z ≃ X))                         ≃⟨ IV ⟩
  (Σ Z ꞉ 𝓑 ̇ , (Z ≃ X) × (Z → Y))                         ≃⟨ V ⟩
  (Σ Z ꞉ 𝓑 ̇ , (X ≃ Z) × (Z → Y))                         ≃⟨ VI ⟩
  (Σ (Z , _) ꞉ (Σ Z ꞉ 𝓑 ̇ , X ≃ Z) , (Z → Y))             ≃⟨ VII ⟩
  (X → Y)                                                 ■
 where
  open general-classifier 𝓤 𝓥

  fe : funext (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)
  fe = univalence-gives-funext ua

  I   = ≃-sym (Σ-change-of-variable (λ A → Σ A ≃ X) (χ Y)
               (universes-are-map-classifiers ua fe⁺ Y))
  II  = Σ-assoc
  III = Σ-cong (λ Z → Σ-cong (λ g → ≃-cong-left' fe fe fe fe fe
                                     (total-fiber-is-domain g)))
  IV  = Σ-cong (λ Z → ×-comm)
  V   = Σ-cong (λ Z → ×-cong (≃-Sym' fe fe fe fe) (≃-refl (Z → Y)))
  VI  = ≃-sym Σ-assoc
  VII = prop-indexed-sum
         (singletons-are-props
           (univalence-via-singletons→ ua X))
         (X , ≃-refl X)

\end{code}
