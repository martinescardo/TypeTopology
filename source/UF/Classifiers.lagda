Martin Escardo 8th May 2020.

An old version of this file is at UF.Classifiers-Old.

This version is ported from the Midlands Graduate School 2019 lecture notes

 https://www.cs.bham.ac.uk/~mhe/HoTT-UF.in-Agda-Lecture-Notes/HoTT-UF-Agda.html
 https://github.com/martinescardo/HoTT-UF.Agda-Lecture-Notes

but with the universe levels generalized and Σ-fibers added in
September 2022.

   * Universes are map classifiers.
   * Ω 𝓤 is the embedding classifier.
   * The type of pointed types is the retraction classifier.
   * The type inhabited types is the surjection classifier.
   * The fibers of Σ are non-dependent function types.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module UF.Classifiers where

open import MLTT.Spartan
open import UF.Base
open import UF.Embeddings
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.Powerset hiding (𝕋)
open import UF.Retracts
open import UF.Sets
open import UF.Sets-Properties
open import UF.Subsingletons
open import UF.SubtypeClassifier
open import UF.UA-FunExt
open import UF.Univalence

\end{code}

The slice type:

\begin{code}

_/_ : (𝓤 : Universe) → 𝓥 ̇ → 𝓤 ⁺ ⊔ 𝓥 ̇
𝓤 / Y = Σ X ꞉ 𝓤 ̇ , (X → Y)

\end{code}

A modification of the slice type, where P doesn't need to be
proposition-valued and so can add structure. An example is P = id,
which is studied below in connection with retractions.

\begin{code}

_/[_]_ : (𝓤 : Universe) → (𝓤 ⊔ 𝓥 ̇ → 𝓦 ̇ ) → 𝓥 ̇ → 𝓤 ⁺ ⊔ 𝓥 ⊔ 𝓦 ̇
𝓤 /[ P ] Y = Σ X ꞉ 𝓤 ̇ , Σ f ꞉ (X → Y) , ((y : Y) → P (fiber f y))

\end{code}

We first consider the original situation of the MGS development with a
single universe for comparison.

\begin{code}

module classifier-single-universe (𝓤 : Universe) where

 χ : (Y : 𝓤 ̇ ) → 𝓤 / Y  → (Y → 𝓤 ̇ )
 χ Y (X , f) = fiber f

 universe-is-classifier : 𝓤 ⁺ ̇
 universe-is-classifier = (Y : 𝓤 ̇ ) → is-equiv (χ Y)

 𝕋 : (Y : 𝓤 ̇ ) → (Y → 𝓤 ̇ ) → 𝓤 / Y
 𝕋 Y A = Σ A , pr₁

 χη : is-univalent 𝓤
    → (Y : 𝓤 ̇ ) (σ : 𝓤 / Y) → 𝕋 Y (χ Y σ) ＝ σ
 χη ua Y (X , f) = r
  where
   e : Σ (fiber f) ≃ X
   e = total-fiber-is-domain f

   p : Σ (fiber f) ＝ X
   p = eqtoid ua (Σ (fiber f)) X e

   NB : ⌜ e ⌝⁻¹ ＝ (λ x → f x , x , refl)
   NB = refl

   q = transport (λ - → - → Y) p pr₁ ＝⟨ transport-is-pre-comp' ua e pr₁ ⟩
       pr₁ ∘ ⌜ e ⌝⁻¹                 ＝⟨ refl ⟩
       f                             ∎

   r : (Σ (fiber f) , pr₁) ＝ (X , f)
   r = to-Σ-＝ (p , q)

 χε : is-univalent 𝓤
    → funext 𝓤 (𝓤 ⁺)
    → (Y : 𝓤 ̇ ) (A : Y → 𝓤 ̇ ) → χ Y (𝕋 Y A) ＝ A
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

 universes-are-classifiers : is-univalent 𝓤
                           → funext 𝓤 (𝓤 ⁺)
                           → universe-is-classifier
 universes-are-classifiers ua fe Y = qinvs-are-equivs (χ Y)
                                      (𝕋 Y , χη ua Y , χε ua fe Y)

 classification : is-univalent 𝓤
                → funext 𝓤 (𝓤 ⁺)
                → (Y : 𝓤 ̇ ) → 𝓤 / Y ≃ (Y → 𝓤 ̇ )
 classification ua fe Y = χ Y , universes-are-classifiers ua fe Y

module special-classifier-single-universe (𝓤 : Universe) where

 open classifier-single-universe 𝓤

 χ-special : (P : 𝓤 ̇ → 𝓥 ̇ ) (Y : 𝓤 ̇ ) → 𝓤 /[ P ] Y  → (Y → Σ P)
 χ-special P Y (X , f , φ) y = fiber f y , φ y

 universe-is-special-classifier : (𝓤 ̇ → 𝓥 ̇ ) → 𝓤 ⁺ ⊔ 𝓥 ̇
 universe-is-special-classifier P = (Y : 𝓤 ̇ ) → is-equiv (χ-special P Y)

 classifier-gives-special-classifier : universe-is-classifier
                                     → (P : 𝓤 ̇ → 𝓥 ̇ )
                                     → universe-is-special-classifier P
 classifier-gives-special-classifier s P Y = γ
  where
   e = (𝓤 /[ P ] Y)                               ≃⟨ a ⟩
       (Σ σ ꞉ 𝓤 / Y , ((y : Y) → P ((χ Y) σ y)))  ≃⟨ b ⟩
       (Σ A ꞉ (Y → 𝓤 ̇ ), ((y : Y) → P (A y)))     ≃⟨ c ⟩
       (Y → Σ P)                                  ■
    where
     a = ≃-sym Σ-assoc
     b = Σ-change-of-variable (λ A → Π (P ∘ A)) (χ Y) (s Y)
     c = ≃-sym ΠΣ-distr-≃

   NB : χ-special P Y ＝ ⌜ e ⌝
   NB = refl

   γ : is-equiv (χ-special P Y)
   γ = ⌜⌝-is-equiv e

 χ-special-is-equiv : is-univalent 𝓤
                    → funext 𝓤 (𝓤 ⁺)
                    → (P : 𝓤 ̇ → 𝓥 ̇ ) (Y : 𝓤 ̇ )
                    → is-equiv (χ-special P Y)
 χ-special-is-equiv ua fe P Y = classifier-gives-special-classifier
                                 (universes-are-classifiers ua fe) P Y

 special-classification : is-univalent 𝓤
                        → funext 𝓤 (𝓤 ⁺)
                        → (P : 𝓤 ̇ → 𝓥 ̇ ) (Y : 𝓤 ̇ )
                        → 𝓤 /[ P ] Y ≃ (Y → Σ P)
 special-classification ua fe P Y = χ-special P Y , χ-special-is-equiv ua fe P Y

\end{code}

Some examples of special classifiers follow.

The universe of pointed types classifies retractions:

\begin{code}

module retraction-classifier (𝓤 : Universe) where

 open special-classifier-single-universe 𝓤

 retractions-into : 𝓤 ̇ → 𝓤 ⁺ ̇
 retractions-into Y = Σ X ꞉ 𝓤 ̇ , Y ◁ X

 pointed-types : (𝓤 : Universe) → 𝓤 ⁺ ̇
 pointed-types 𝓤 = Σ X ꞉ 𝓤 ̇ , X

 retraction-classifier : Univalence
                       → (Y : 𝓤 ̇ ) → retractions-into Y ≃ (Y → pointed-types 𝓤)
 retraction-classifier ua Y =
  retractions-into Y                                              ≃⟨ i ⟩
  ((𝓤 /[ id ] Y))                                                 ≃⟨ ii ⟩
  (Y → pointed-types 𝓤)                                           ■
  where
   i  = ≃-sym (Σ-cong (λ X → Σ-cong (λ f → ΠΣ-distr-≃)))
   ii = special-classification (ua 𝓤)
         (univalence-gives-funext' 𝓤 (𝓤 ⁺) (ua 𝓤) (ua (𝓤 ⁺)))
         id Y

\end{code}

The universe of inhabited types classifies surjections:

\begin{code}

module surjection-classifier (𝓤 : Universe) where

 open special-classifier-single-universe 𝓤

 open import UF.PropTrunc

 module _ (pt : propositional-truncations-exist) where

  open PropositionalTruncation pt public
  open import UF.ImageAndSurjection pt public

  surjections-into : 𝓤 ̇ → 𝓤 ⁺ ̇
  surjections-into Y = Σ X ꞉ 𝓤 ̇ , X ↠ Y

  inhabited-types : 𝓤 ⁺ ̇
  inhabited-types = Σ X ꞉ 𝓤 ̇ , ∥ X ∥

  surjection-classification : Univalence
                            → (Y : 𝓤 ̇ )
                            → surjections-into Y ≃ (Y → inhabited-types)
  surjection-classification ua =
   special-classification (ua 𝓤)
     (univalence-gives-funext' 𝓤 (𝓤 ⁺) (ua 𝓤) (ua (𝓤 ⁺)))
     ∥_∥

\end{code}

Added 11th September 2022. We now generalize the universe levels of
the classifier and special classifier modules.

\begin{code}

module classifier (𝓤 𝓥 : Universe) where

 χ : (Y : 𝓤 ̇ ) → (𝓤 ⊔ 𝓥) / Y  → (Y → 𝓤 ⊔ 𝓥 ̇ )
 χ Y (X , f) = fiber f

\end{code}

Definition of when the given pair of universes is a classifier,

\begin{code}

 universe-is-classifier : (𝓤 ⊔ 𝓥)⁺ ̇
 universe-is-classifier = (Y : 𝓤 ̇ ) → is-equiv (χ Y)

 𝕋 : (Y : 𝓤 ̇ ) → (Y → 𝓤 ⊔ 𝓥 ̇ ) → (𝓤 ⊔ 𝓥) / Y
 𝕋 Y A = Σ A , pr₁

 χη : is-univalent (𝓤 ⊔ 𝓥)
    → (Y : 𝓤 ̇ ) (σ : (𝓤 ⊔ 𝓥) / Y) → 𝕋 Y (χ Y σ) ＝ σ
 χη ua Y (X , f) = r
  where
   e : Σ (fiber f) ≃ X
   e = total-fiber-is-domain f

   p : Σ (fiber f) ＝ X
   p = eqtoid ua (Σ (fiber f)) X e

   NB : ⌜ e ⌝⁻¹ ＝ (λ x → f x , x , refl)
   NB = refl

   q = transport (λ - → - → Y) p pr₁ ＝⟨ transport-is-pre-comp' ua e pr₁ ⟩
       pr₁ ∘ ⌜ e ⌝⁻¹                 ＝⟨ refl ⟩
       f                             ∎

   r : (Σ (fiber f) , pr₁) ＝ (X , f)
   r = to-Σ-＝ (p , q)

 χε : is-univalent (𝓤 ⊔ 𝓥)
    → funext 𝓤 ((𝓤 ⊔ 𝓥)⁺)
    → (Y : 𝓤 ̇ ) (A : Y → 𝓤 ⊔ 𝓥 ̇ ) → χ Y (𝕋 Y A) ＝ A
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

 universes-are-classifiers : is-univalent (𝓤 ⊔ 𝓥)
                           → funext 𝓤 ((𝓤 ⊔ 𝓥)⁺)
                           → universe-is-classifier
 universes-are-classifiers ua fe Y = qinvs-are-equivs (χ Y)
                                          (𝕋 Y , χη ua Y , χε ua fe Y)

 classification : is-univalent (𝓤 ⊔ 𝓥)
                → funext 𝓤 ((𝓤 ⊔ 𝓥)⁺)
                → (Y : 𝓤 ̇ ) → (𝓤 ⊔ 𝓥) / Y ≃ (Y → 𝓤 ⊔ 𝓥 ̇ )
 classification ua fe Y = χ Y , universes-are-classifiers ua fe Y

\end{code}

In the case of special classifiers we now need to assume a further
universe 𝓦.

\begin{code}

module special-classifier (𝓤 𝓥 𝓦 : Universe) where

 open classifier 𝓤 𝓥 public

 χ-special : (P : 𝓤 ⊔ 𝓥 ̇ → 𝓦 ̇ ) (Y : 𝓤 ̇ ) → (𝓤 ⊔ 𝓥) /[ P ] Y  → (Y → Σ P)
 χ-special P Y (X , f , φ) y = fiber f y , φ y

 universe-is-special-classifier : (𝓤 ⊔ 𝓥 ̇ → 𝓦 ̇ ) → (𝓤 ⊔ 𝓥)⁺ ⊔ 𝓦 ̇
 universe-is-special-classifier P = (Y : 𝓤 ̇ ) → is-equiv (χ-special P Y)

 classifier-gives-special-classifier : universe-is-classifier
                                     → (P : 𝓤 ⊔ 𝓥 ̇ → 𝓦 ̇ )
                                     → universe-is-special-classifier P
 classifier-gives-special-classifier s P Y = γ
  where
   e = ((𝓤 ⊔ 𝓥) /[ P ] Y)                               ≃⟨ a ⟩
       (Σ σ ꞉ (𝓤 ⊔ 𝓥) / Y , ((y : Y) → P ((χ Y) σ y)))  ≃⟨ b ⟩
       (Σ A ꞉ (Y → 𝓤 ⊔ 𝓥 ̇ ), ((y : Y) → P (A y)))       ≃⟨ c ⟩
       (Y → Σ P)                                        ■
    where
     a = ≃-sym Σ-assoc
     b = Σ-change-of-variable (λ A → Π (P ∘ A)) (χ Y) (s Y)
     c = ≃-sym ΠΣ-distr-≃

   NB : χ-special P Y ＝ ⌜ e ⌝
   NB = refl

   γ : is-equiv (χ-special P Y)
   γ = ⌜⌝-is-equiv e

 χ-special-is-equiv : is-univalent (𝓤 ⊔ 𝓥)
                    → funext 𝓤 ((𝓤 ⊔ 𝓥)⁺)
                    → (P : 𝓤 ⊔ 𝓥 ̇ → 𝓦 ̇ ) (Y : 𝓤 ̇ )
                    → is-equiv (χ-special P Y)
 χ-special-is-equiv ua fe P Y = classifier-gives-special-classifier
                                 (universes-are-classifiers ua fe) P Y

 special-classification : is-univalent (𝓤 ⊔ 𝓥)
                        → funext 𝓤 ((𝓤 ⊔ 𝓥)⁺)
                        → (P : 𝓤 ⊔ 𝓥 ̇ → 𝓦 ̇ ) (Y : 𝓤 ̇ )
                        → (𝓤 ⊔ 𝓥) /[ P ] Y ≃ (Y → Σ P)
 special-classification ua fe P Y = χ-special P Y , χ-special-is-equiv ua fe P Y

\end{code}

The subtype classifier with general universes:

\begin{code}

Ω-is-subtype-classifier' : is-univalent (𝓤 ⊔ 𝓥)
                         → funext 𝓤 ((𝓤 ⊔ 𝓥)⁺)
                         → (Y : 𝓤 ̇ )
                         → Subtypes' (𝓤 ⊔ 𝓥) Y ≃ (Y → Ω (𝓤 ⊔ 𝓥))
Ω-is-subtype-classifier' {𝓤} {𝓥} ua fe = special-classification ua fe
                                          is-subsingleton
 where
  open special-classifier 𝓤 𝓥 (𝓤 ⊔ 𝓥)

Ω-is-subtype-classifier : is-univalent 𝓤
                        → funext 𝓤 (𝓤 ⁺)
                        → (Y : 𝓤 ̇ )
                        → Subtypes Y ≃ (Y → Ω 𝓤)
Ω-is-subtype-classifier {𝓤} = Ω-is-subtype-classifier' {𝓤} {𝓤}

subtypes-form-set : Univalence → (Y : 𝓤 ̇ ) → is-set (Subtypes' (𝓤 ⊔ 𝓥) Y)
subtypes-form-set {𝓤} {𝓥} ua Y =
 equiv-to-set
  (Ω-is-subtype-classifier' {𝓤} {𝓥}
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
  (Σ A ꞉ (Y → 𝓤 ⊔ 𝓥 ̇ ) , Σ A ≃ X)                            ≃⟨ I ⟩
  (Σ (Z , g) ꞉ (𝓤 ⊔ 𝓥) / Y , (Σ y ꞉ Y , fiber g y) ≃ X)      ≃⟨ II ⟩
  (Σ Z ꞉ 𝓤 ⊔ 𝓥 ̇ , Σ g ꞉ (Z → Y) , (Σ y ꞉ Y , fiber g y) ≃ X) ≃⟨ III ⟩
  (Σ Z ꞉ 𝓤 ⊔ 𝓥 ̇ , (Z → Y) × (Z ≃ X))                         ≃⟨ IV ⟩
  (Σ Z ꞉ 𝓤 ⊔ 𝓥 ̇ , (Z ≃ X) × (Z → Y))                         ≃⟨ V ⟩
  (Σ Z ꞉ 𝓤 ⊔ 𝓥 ̇ , (X ≃ Z) × (Z → Y))                         ≃⟨ VI ⟩
  (Σ (Z , _) ꞉ (Σ Z ꞉ 𝓤 ⊔ 𝓥 ̇ , X ≃ Z) , (Z → Y))             ≃⟨ VII ⟩
  (X → Y)                                                    ■
 where
  open classifier 𝓤 𝓥
  open import UF.Equiv-FunExt
  open import UF.PropIndexedPiSigma
  open import UF.Yoneda

  fe : funext (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)
  fe = univalence-gives-funext ua

  I   = ≃-sym (Σ-change-of-variable (λ A → Σ A ≃ X) (χ Y)
               (universes-are-classifiers ua fe⁺ Y))
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

private
 ∑ : {𝓤 𝓥 : Universe} (X : 𝓤 ̇ ) (Y : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
 ∑ X Y = Σ Y

\end{code}

The use of equality rather than equivalence prevents us from having
more general universes in the following:

\begin{code}

Σ-fibers : is-univalent 𝓤
         → funext 𝓤 (𝓤 ⁺)
         → {X Y : 𝓤 ̇ }
         → fiber (∑ Y) X ≃ (X → Y)
Σ-fibers {𝓤} ua fe⁺ {X} {Y} =
  (Σ A ꞉ (Y → 𝓤 ̇ ) , Σ A ＝ X) ≃⟨ Σ-cong (λ A → univalence-≃ ua (Σ A) X) ⟩
  (Σ A ꞉ (Y → 𝓤 ̇ ) , Σ A ≃ X)  ≃⟨ Σ-fibers-≃ {𝓤} {𝓤} ua fe⁺ ⟩
  (X → Y)                       ■

\end{code}
