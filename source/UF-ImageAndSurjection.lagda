\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module UF-ImageAndSurjection where

open import SpartanMLTT
open import UF-Base
open import UF-Equiv
open import UF-EquivalenceExamples
open import UF-Embeddings
open import UF-Subsingletons
open import UF-PropTrunc
open import UF-Retracts

\end{code}

A main application of propositional truncations is to be able to
define images and surjections:

\begin{code}

module ImageAndSurjection (pt : propositional-truncations-exist) where

 open PropositionalTruncation pt

 _∈image_ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → Y → (X → Y) → 𝓤 ⊔ 𝓥 ̇
 y ∈image f = ∃ x ꞉ domain f , f x ≡ y

 being-in-the-image-is-prop : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (y : Y) (f : X → Y)
                            → is-prop (y ∈image f)
 being-in-the-image-is-prop y f = ∃-is-prop

 image : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
 image f = Σ y ꞉ codomain f , y ∈image f

 restriction : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
             → image f → Y
 restriction f (y , _) = y

 restriction-embedding : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                       → is-embedding (restriction f)
 restriction-embedding f = pr₁-is-embedding (λ y → ∥∥-is-prop)

 corestriction : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
               → X → image f
 corestriction f x = f x , ∣ x , refl ∣

 wconstant-maps-to-sets-have-propositional-images : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                                                  → is-set Y
                                                  → (f : X → Y)
                                                  → wconstant f
                                                  → is-prop (image f)
 wconstant-maps-to-sets-have-propositional-images
  {𝓤} {𝓥} {X} {Y} s f c (y , p) (y' , p') =
   to-subtype-≡ (λ _ → ∥∥-is-prop) (∥∥-rec s q p)
    where
     q : (Σ x ꞉ X , f x ≡ y) → y ≡ y'
     q u = ∥∥-rec s (h u) p'
      where
       h : (Σ x ꞉ X , f x ≡ y) → (Σ x' ꞉ X , f x' ≡ y') → y ≡ y'
       h (x , e) (x' , e') = y    ≡⟨ e ⁻¹ ⟩
                             f x  ≡⟨ c x x' ⟩
                             f x' ≡⟨ e' ⟩
                             y'   ∎

 wconstant-map-to-set-factors-through-truncation-of-domain :
    {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
  → is-set Y
  → (f : X → Y)
  → wconstant f
  → Σ f' ꞉ (∥ X ∥ → Y) , f ∼ f' ∘ ∣_∣
 wconstant-map-to-set-factors-through-truncation-of-domain
  {𝓤} {𝓥} {X} {Y} Y-is-set f f-is-wconstant = f' , h
   where
    p : is-prop (image f)
    p = wconstant-maps-to-sets-have-propositional-images
         Y-is-set f f-is-wconstant
    f'' : ∥ X ∥ → image f
    f'' = ∥∥-rec p (corestriction f)
    f' : ∥ X ∥ → Y
    f' = restriction f ∘ f''
    h : f ∼ f' ∘ ∣_∣
    h x = f x                               ≡⟨ refl ⟩
          restriction f (corestriction f x) ≡⟨ ρ    ⟩
          restriction f (f'' ∣ x ∣)         ≡⟨ refl ⟩
          f' ∣ x ∣                          ∎
     where
      ρ = ap (restriction f) (p (corestriction f x) (f'' ∣ x ∣))

 is-surjection : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
 is-surjection f = ∀ y → y ∈image f

 id-is-surjection : {X : 𝓤 ̇ } → is-surjection (𝑖𝑑 X)
 id-is-surjection = λ y → ∣ y , refl ∣

 _↠_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
 X ↠ Y = Σ f ꞉ (X → Y) , is-surjection f

 ⌞_⌟ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X ↠ Y) → (X → Y)
 ⌞ (f , i) ⌟ = f

 ⌞⌟-is-surjection : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (𝓯 : X ↠ Y) → is-surjection ⌞ 𝓯 ⌟
 ⌞⌟-is-surjection (f , i) = i

 _is-image-of_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
 Y is-image-of X = X ↠ Y

 image-is-set : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
              → (f : X → Y)
              → is-set Y
              → is-set (image f)
 image-is-set f i = subsets-of-sets-are-sets _
                     (λ y → y ∈image f) i
                     (being-in-the-image-is-prop _ f)

 vv-equiv-iff-embedding-and-surjection  :  {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                                        → is-vv-equiv f ⇔ is-embedding f × is-surjection f
 vv-equiv-iff-embedding-and-surjection f = g , h
  where
   g : is-vv-equiv f → is-embedding f × is-surjection f
   g i = (λ y → pr₁ (pr₁ the-singletons-are-the-inhabited-propositions (i y))) ,
         (λ y → pr₂ (pr₁ the-singletons-are-the-inhabited-propositions (i y)))

   h : is-embedding f × is-surjection f → is-vv-equiv f
   h (e , s) = λ y → pr₂ the-singletons-are-the-inhabited-propositions (e y , s y)

 surjective-embeddings-are-vv-equivs : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                                     → is-embedding f → is-surjection f → is-vv-equiv f
 surjective-embeddings-are-vv-equivs f e s = pr₂ (vv-equiv-iff-embedding-and-surjection f) (e , s)

 surjective-embeddings-are-equivs : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                                  → is-embedding f → is-surjection f → is-equiv f
 surjective-embeddings-are-equivs f e s = vv-equivs-are-equivs f (surjective-embeddings-are-vv-equivs f e s)

 corestriction-is-surjection : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                             → is-surjection (corestriction f)
 corestriction-is-surjection f (y , s) = ∥∥-functor g s
  where
   g : (Σ x ꞉ domain f , f x ≡ y) → Σ x ꞉ domain f , corestriction f x ≡ (y , s)
   g (x , p) = x , to-Σ-≡ (p , ∥∥-is-prop _ _)

 pt-is-surjection : {X : 𝓤 ̇ } → is-surjection (λ (x : X) → ∣ x ∣)
 pt-is-surjection t = ∥∥-rec ∥∥-is-prop (λ x → ∣ x , ∥∥-is-prop (∣ x ∣) t ∣) t


 NatΣ-is-surjection : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (B : X → 𝓦 ̇ ) (ζ : Nat A B)
                    → ((x : X) → is-surjection (ζ x))
                    → is-surjection (NatΣ ζ)
 NatΣ-is-surjection A B ζ i (x , b) = γ
  where
   δ : (Σ a ꞉ A x , ζ x a ≡ b)
     → Σ (x' , a) ꞉ Σ A , (x' , ζ x' a) ≡ (x , b)
   δ (a , p) = (x , a) , (ap (x ,_) p)

   γ : ∃ (x' , a) ꞉ Σ A , (x' , ζ x' a) ≡ (x , b)
   γ = ∥∥-functor δ (i x b)

\end{code}

The following was marked as a TODO by Martin:
  A map is an embedding iff its corestriction is an equivalence.
It was done by Tom de Jong on 4 December 2020.

\begin{code}

 corestriction-of-embedding-is-equivalence : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                                           → is-embedding f
                                           → is-equiv (corestriction f)
 corestriction-of-embedding-is-equivalence f e =
  surjective-embeddings-are-equivs f' e' s'
   where
    f' : domain f → image f
    f' = corestriction f
    s' : is-surjection f'
    s' = corestriction-is-surjection f
    e' : is-embedding f'
    e' (y , p) = retract-of-prop γ (e y)
     where
      γ : fiber f' (y , p) ◁ fiber f y
      γ = Σ-retract (λ x → f' x ≡ y , p) (λ x → f x ≡ y) ϕ
       where
        ϕ : (x : domain f) → (f' x ≡ (y , p)) ◁ (f x ≡ y)
        ϕ x = ρ , σ , η
         where
          ρ : f x ≡ y → f' x ≡ (y , p)
          ρ q = to-subtype-≡ (λ y' → ∥∥-is-prop) q
          σ : f' x ≡ (y , p) → f x ≡ y
          σ q' = ap pr₁ q'
          η : ρ ∘ σ ∼ id
          η refl = to-Σ-≡ (refl , q)    ≡⟨ ap (λ - → to-Σ-≡ (refl , -)) h ⟩
                   to-Σ-≡ (refl , refl) ≡⟨ refl ⟩
                   refl                 ∎
           where
            q : ∣ x , refl ∣ ≡ ∣ x , refl ∣
            q = ∥∥-is-prop ∣ x , refl ∣ ∣ x , refl ∣
            h : q ≡ refl
            h = props-are-sets ∥∥-is-prop q refl

 embedding-if-corestriction-is-equivalence : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                                           → is-equiv (corestriction f)
                                           → is-embedding f
 embedding-if-corestriction-is-equivalence f i =
  embedding-closed-under-∼ f' f (∘-is-embedding e₁ e₂) H
   where
    f' : domain f → codomain f
    f' = pr₁ ∘ corestriction f
    H : f ∼ pr₁ ∘ corestriction f
    H x = refl
    e₁ : is-embedding (corestriction f)
    e₁ = equivs-are-embeddings (corestriction f) i
    e₂ : is-embedding pr₁
    e₂ = pr₁-is-embedding (λ y → ∥∥-is-prop)

\end{code}

Surjections can be characterized as follows, modulo size:

\begin{code}

 imageInduction : ∀ {𝓦 𝓤 𝓥} {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ⊔ 𝓦  ⁺ ̇
 imageInduction {𝓦} {𝓤} {𝓥} {X} {Y} f =
                (P : Y → 𝓦 ̇ ) → ((y : Y) → is-prop (P y)) → ((x : X) → P (f x)) → (y : Y) → P y

 surjection-induction : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                      → is-surjection f → imageInduction {𝓦} f
 surjection-induction f is P isp a y = ∥∥-rec (isp y)
                                             (λ σ → transport P (pr₂ σ) (a (pr₁ σ)))
                                             (is y)

 image-surjection-converse : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                           → imageInduction f → is-surjection f
 image-surjection-converse f is' = is' (λ y → ∥ Σ (λ x → f x ≡ y) ∥)
                                       (λ y → ∥∥-is-prop)
                                       (λ x → ∣ x , refl ∣)

 image-induction : ∀ {𝓦} {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                   (f : X → Y) (P : image f → 𝓦 ̇ )
                 → (∀ y' → is-prop (P y'))
                 → (∀ x → P (corestriction f x))
                 → ∀ y' → P y'
 image-induction f = surjection-induction (corestriction f)
                                          (corestriction-is-surjection f)

 retraction-surjection : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                       → has-section f → is-surjection f
 retraction-surjection {𝓤} {𝓥} {X} f φ y = ∣ pr₁ φ y , pr₂ φ y ∣

 pr₁-is-surjection : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ )
                   → ((x : X) → ∥ A x ∥)
                   → is-surjection (λ (σ : Σ A) → pr₁ σ)
 pr₁-is-surjection A s x = γ
  where
   δ : A x → Σ σ ꞉ Σ A , pr₁ σ ≡ x
   δ a = (x , a) , refl

   γ : ∃ σ ꞉ Σ A , pr₁ σ ≡ x
   γ = ∥∥-functor δ (s x)

 pr₁-is-surjection-converse : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ )
                            → is-surjection (λ (σ : Σ A) → pr₁ σ)
                            → ((x : X) → ∥ A x ∥)
 pr₁-is-surjection-converse A s x = γ
  where
   δ : (Σ σ ꞉ Σ A , pr₁ σ ≡ x) → A x
   δ ((.x , a) , refl) = a

   γ : ∥ A x ∥
   γ = ∥∥-functor δ (s x)

\end{code}

Added 13 February 2020 by Tom de Jong.

\begin{code}

 surjection-≃-image : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                    → is-surjection f
                    → image f ≃ Y
 surjection-≃-image {𝓤} {𝓥} {X} {Y} f s =
  image f                       ≃⟨ ≃-refl _ ⟩
  (Σ y ꞉ Y , ∃ x ꞉ X , f x ≡ y) ≃⟨ Σ-cong γ ⟩
  (Σ y ꞉ Y , 𝟙)                 ≃⟨ ≃-refl _ ⟩
  Y × 𝟙                         ≃⟨ 𝟙-rneutral {𝓥} {𝓥} ⟩
  Y                             ■
   where
    γ : (y : Y) → (∃ x ꞉ X , f x ≡ y) ≃ 𝟙
    γ y = singleton-≃-𝟙 (pointed-props-are-singletons (s y) ∥∥-is-prop)

\end{code}

Added 18 December 2020 by Tom de Jong.

\begin{code}

 ∘-is-surjection : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } {f : X → Y} {g : Y → Z}
                 → is-surjection f → is-surjection g → is-surjection (g ∘ f)
 ∘-is-surjection {𝓤} {𝓥} {𝓦} {X} {Y} {Z} {f} {g} σ τ z =
  ∥∥-rec ∥∥-is-prop γ₁ (τ z)
   where
    γ₁ : (Σ y ꞉ Y , g y ≡ z) → ∃ x ꞉ X , (g ∘ f) x ≡ z
    γ₁ (y , q) = ∥∥-functor γ₂ (σ y)
     where
      γ₂ : (Σ x ꞉ X , f x ≡ y) → Σ x ꞉ X , (g ∘ f) x ≡ z
      γ₂ (x , p) = (x , (g (f x) ≡⟨ ap g p ⟩
                         g y     ≡⟨ q ⟩
                         z       ∎))

 equivs-are-surjections : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {f : X → Y}
                        → is-equiv f → is-surjection f
 equivs-are-surjections ((ρ , η) , (σ , ε)) y = ∣ ρ y , η y ∣

\end{code}
