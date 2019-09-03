Martin Escardo, 20th August 2018

We consider type and subtype classifiers, and discuss an obvious
generalization which is left undone for the moment.

 * (Σ \(X : 𝓤 ̇ ) → X → Y) ≃ (Y → 𝓤 ̇ )
 * (Σ \(X : 𝓤 ̇ ) → X ↪ Y) ≃ (Y → Ω 𝓤)

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module UF-Classifiers where

open import SpartanMLTT
open import UF-Subsingletons
open import UF-Subsingletons-FunExt
open import UF-Equiv
open import UF-EquivalenceExamples
open import UF-Equiv-FunExt
open import UF-Base
open import UF-Univalence
open import UF-UA-FunExt
open import UF-FunExt
open import UF-Embeddings

module general-classifier
        {𝓤 : Universe}
        (fe' : funext 𝓤 (𝓤 ⁺))
        (ua : is-univalent 𝓤)
        (Y : 𝓤 ̇ )
        (green : 𝓤 ̇ → 𝓤 ̇ )
       where

 green-map : {X : 𝓤 ̇ } → (X → Y) → 𝓤 ̇
 green-map f = (y : Y) → green (fiber f y)

 Green : 𝓤 ⁺ ̇
 Green = Σ \(X : 𝓤 ̇ ) → green X

 Green-map : 𝓤 ⁺ ̇
 Green-map = Σ \(X : 𝓤 ̇ ) → Σ \(f : X → Y) → green-map f
                                         
 χ : Green-map  → (Y → Green)
 χ (X , f , g) y = (fiber f y) , (g y)

 fiber-equiv-≡ : (A : Y → Green) (y : Y) → pr₁ (A y) ≡ fiber pr₁ y
 fiber-equiv-≡ A y =
  (eqtoid ua (fiber pr₁ y) (pr₁ (A y)) (fiber-equiv {𝓤} {𝓤} {Y} {pr₁ ∘ A} y)) ⁻¹
                      
 T : (Y → Green) → Green-map
 T A = Σ (pr₁ ∘ A) , pr₁ , g
  where
   g : green-map pr₁
   g y = transport green (fiber-equiv-≡ A y) (pr₂ (A y))

 χT : (A : Y → Green) → χ(T A) ≡ A
 χT A = dfunext fe' γ
  where
   γ : (y : Y) → χ (T A) y ≡ A y
   γ y = to-Σ-≡ ((a ⁻¹) , b)
    where
     a : pr₁ (A y) ≡ pr₁ (χ (T A) y)
     a = fiber-equiv-≡ A y
     b = transport green (a ⁻¹) (pr₂ (χ (T A) y))               ≡⟨ refl ⟩
         transport green (a ⁻¹) (transport green a (pr₂ (A y))) ≡⟨ (transport-comp green a (a ⁻¹)) ⁻¹ ⟩
         transport green (a ∙ a ⁻¹) (pr₂ (A y))                 ≡⟨ ap (λ - → transport green - (pr₂ (A y))) (trans-sym' a) ⟩
         transport green refl (pr₂ (A y))                       ≡⟨ refl ⟩
         pr₂ (A y)                                              ∎

 green-maps-are-closed-under-precomp-with-equivs : {X X' : 𝓤 ̇ } (e : X' ≃ X)
                                                   {f : X → Y}
                                                 → green-map f
                                                 → green-map (f ∘ eqtofun e)
 green-maps-are-closed-under-precomp-with-equivs e {f} g y =
  transport green p (g y)
   where
    p : fiber f y ≡ fiber (f ∘ eqtofun e) y
    p = (eqtoid ua _ _ (precomp-with-equiv-fiber-equiv e f y)) ⁻¹       

 precomp-with-≃-refl-green-map : {X : 𝓤 ̇ } (f : X → Y) (g : green-map f)
                           → green-maps-are-closed-under-precomp-with-equivs
                              (≃-refl X) g
                             ≡ g
 precomp-with-≃-refl-green-map {X} f g = dfunext (funext-from-univalence ua) γ
  where
   γ : (y : Y) → green-maps-are-closed-under-precomp-with-equivs (≃-refl X) g y ≡ g y
   γ y = green-maps-are-closed-under-precomp-with-equivs (≃-refl X) g y         ≡⟨ refl ⟩
         transport green ((eqtoid ua _ _ (≃-refl (fiber f y))) ⁻¹) (g y)        ≡⟨ ap (λ - → transport green (- ⁻¹) (g y)) (eqtoid-refl ua (fiber f y)) ⟩
         g y                                                                    ∎

 transport-green-map-eqtoid : {X X' : 𝓤 ̇ } (e : X' ≃ X) (f : X → Y)
                              (g : green-map f)
                            → transport (λ - → Σ \(h : - → Y) → green-map h)
                               ((eqtoid ua X' X e) ⁻¹) (f , g)
                              ≡
                              f ∘ (eqtofun e) ,
                               green-maps-are-closed-under-precomp-with-equivs e g 
 transport-green-map-eqtoid {X} {X'} = JEq ua X' E γ X
  where
   B : 𝓤 ̇ → 𝓤 ̇
   B Z = Σ \(h : Z → Y) → green-map h
   E : (Z : 𝓤 ̇) → X' ≃ Z → 𝓤 ̇
   E Z e = (f : Z → Y) → (g : green-map f)
         → transport B ((eqtoid ua X' Z e) ⁻¹) (f , g)
           ≡ f ∘ (eqtofun e) , green-maps-are-closed-under-precomp-with-equivs e g
   γ : E X' (≃-refl X')
   γ f g = transport B ((eqtoid ua X' X' (≃-refl X')) ⁻¹) (f , g)            ≡⟨ ap (λ - → transport B (- ⁻¹) (f , g)) (eqtoid-refl ua X') ⟩
           f , g                                                             ≡⟨ to-Σ-≡ (refl , ((precomp-with-≃-refl-green-map f g) ⁻¹)) ⟩
           f , green-maps-are-closed-under-precomp-with-equivs (≃-refl X') g ∎

 Tχ : (f : Green-map) → T(χ f) ≡ f
 Tχ (X , f , g) = to-Σ-≡ (a , (to-Σ-≡ (b , c)))
  where
   X' : 𝓤 ̇
   X' = pr₁ (T (χ (X , f , g)))
   f' : X' → Y
   f' = pr₁ (pr₂ (T (χ (X , f , g))))
   g' : green-map f'
   g' = pr₂ (pr₂ (T (χ (X , f , g))))
   e : X ≃ X'
   e = sum-of-fibers X Y f
   a : X' ≡ X
   a = (eqtoid ua X X' e) ⁻¹
   B : 𝓤 ̇ → 𝓤 ̇
   B Z = Σ \(h : Z → Y) → green-map h
   t : transport B a (f' , g') ≡
       (f' ∘ eqtofun e) , (green-maps-are-closed-under-precomp-with-equivs e g')
   t = transport-green-map-eqtoid e f' g'
   t₁ : pr₁ (transport B a (f' , g')) ≡ f' ∘ eqtofun e
   t₁ = pr₁ (from-Σ-≡ t)
   t₂ : transport green-map t₁ (pr₂ (transport B a (f' , g'))) ≡
        green-maps-are-closed-under-precomp-with-equivs e g'
   t₂ = pr₂ (from-Σ-≡ t)
   b : pr₁ (transport B a (f' , g')) ≡ f
   b = pr₁ (transport B a (f' , g')) ≡⟨ t₁ ⟩
       f' ∘ eqtofun e                ≡⟨ refl ⟩
       f                             ∎
   c : transport green-map b (pr₂ (transport B a (f' , g')))  ≡ g
   c = transport green-map b (pr₂ (transport B a (f' , g')))  ≡⟨ refl ⟩
       transport green-map t₁ (pr₂ (transport B a (f' , g'))) ≡⟨ t₂ ⟩
       green-maps-are-closed-under-precomp-with-equivs e g' ≡⟨ dfunext fe u ⟩
       g ∎
    where
     fe : funext 𝓤 𝓤
     fe = funext-from-univalence ua
     u : (y : Y) → green-maps-are-closed-under-precomp-with-equivs e g' y ≡ g y
     u y = green-maps-are-closed-under-precomp-with-equivs e g' y ≡⟨ refl ⟩
           transport green (p ⁻¹) (g' y)                          ≡⟨ refl ⟩
           transport green (p ⁻¹) (transport green (q ⁻¹) (g y))  ≡⟨ (transport-comp green (q ⁻¹) (p ⁻¹)) ⁻¹ ⟩
           transport green (q ⁻¹ ∙ p ⁻¹) (g y)                    ≡⟨ ap (λ - → transport green - (g y)) v ⟩
           g y                                                    ∎
       where
        p : fiber (f' ∘ eqtofun e) y ≡ fiber f' y
        p = eqtoid ua _ _ (precomp-with-equiv-fiber-equiv e f' y)
        q : fiber f' y ≡ fiber f y
        q = eqtoid ua (fiber f' y) (fiber f y) (fiber-equiv y)
        v = q ⁻¹ ∙ p ⁻¹ ≡⟨ ⁻¹-contravariant p q ⟩
            (p ∙ q) ⁻¹  ≡⟨ ap (_⁻¹) w ⟩
            refl        ∎
         where
          w : p ∙ q ≡ refl
          w = eqtoid ua _ _ ϕ ∙ eqtoid ua _ _ ψ ≡⟨ eqtoid-comp ua _ _ ⟩
              eqtoid ua _ _ (ϕ ● ψ)             ≡⟨ ap (eqtoid ua _ _) ϕψ ⟩
              eqtoid ua _ _ (≃-refl _)          ≡⟨ eqtoid-refl ua _ ⟩
              refl                              ∎
           where
            ϕ : fiber (f' ∘ eqtofun e) y ≃ fiber f' y
            ϕ = precomp-with-equiv-fiber-equiv e f' y
            ψ : fiber pr₁ y ≃ pr₁ (χ (X , f , g) y)
            ψ = fiber-equiv y
            ϕψ : ϕ ● ψ ≡ ≃-refl (fiber (f' ∘ eqtofun e) y)
            ϕψ = to-Σ-≡ (dfunext fe ϕψ' ,
                         being-equiv-is-a-prop'' fe id _ (id-is-an-equiv _))
             where
              ϕψ' : (z : fiber (f' ∘ eqtofun e) y)
                 → eqtofun (ϕ ● ψ) z ≡ z
              ϕψ' (x , refl) = refl

 χ-is-equivalence : is-equiv χ
 χ-is-equivalence = (T , χT) , (T , Tχ)

 classification-equivalence : Green-map ≃ (Y → Green)
 classification-equivalence = χ , χ-is-equivalence

module type-classifier
        {𝓤 : Universe}
        (fe' : funext 𝓤 (𝓤 ⁺))
        (ua : is-univalent 𝓤)
        (Y : 𝓤 ̇ )
       where

 open general-classifier fe' ua Y (λ (X : 𝓤 ̇ ) → 𝟙)

 type-classification-equivalence : (Σ \(X : 𝓤 ̇ ) → X → Y) ≃ (Y → 𝓤 ̇ )
 type-classification-equivalence = (Σ \(X : 𝓤 ̇ ) → X → Y) ≃⟨ ϕ ⟩
                                   Green-map ≃⟨ classification-equivalence ⟩
                                   (Y → Green) ≃⟨ ψ ⟩
                                   (Y → 𝓤 ̇ ) ■
  where
   ϕ : (Σ \(X : 𝓤 ̇ ) → X → Y) ≃ Green-map
   ϕ = qinveq α (β , a , b)
    where
     α : (Σ \(X : 𝓤 ̇ ) → X → Y) → Green-map
     α (X , f) = X , (f , (λ y → *))
     β : Green-map → (Σ \(X : 𝓤 ̇ ) → X → Y)
     β (X , f , g) = X , f
     a : (p : Σ (λ X → X → Y)) → β (α p) ≡ p
     a (X , f) = refl
     b : (q : Green-map) → α (β q) ≡ q
     b (X , f , g) = to-Σ-≡ (refl ,
                             to-Σ-≡ (refl ,
                                     dfunext (funext-from-univalence ua)
                                      (λ y → 𝟙-is-prop * (g y))))
   ψ : (Y → Green) ≃ (Y → 𝓤 ̇ )
   ψ = →-cong fe' fe' (≃-refl Y) γ
    where
     γ : Green ≃ 𝓤 ̇
     γ = qinveq pr₁ ((λ X → (X , * )) , c , λ x → refl)
      where
       c : (p : Σ (λ X → 𝟙)) → pr₁ p , * ≡ p
       c (x , *) = refl

module subsingleton-classifier
        {𝓤 : Universe}
        (fe' : funext 𝓤 (𝓤 ⁺))
        (ua : is-univalent 𝓤)
        (Y : 𝓤 ̇ )
       where

 open general-classifier fe' ua Y (λ (X : 𝓤 ̇ ) → is-prop X)

 subsingleton-classification-equivalence : (Σ \(X : 𝓤 ̇ ) → X ↪ Y) ≃ (Y → Ω 𝓤 )
 subsingleton-classification-equivalence = classification-equivalence

module singleton-classifier
        {𝓤 : Universe}
        (fe' : funext 𝓤 (𝓤 ⁺))
        (ua : is-univalent 𝓤)
        (Y : 𝓤 ̇ )
       where

 open general-classifier fe' ua Y (λ (X : 𝓤 ̇ ) → is-singleton X)

 singleton-classification-equivalence : (Σ \(X : 𝓤 ̇ ) → X ≃ Y) ≃ 𝟙 {𝓤}
 singleton-classification-equivalence =
  (Σ \(X : 𝓤 ̇ ) → X ≃ Y)                            ≃⟨ ϕ ⟩
  (Σ \(X : 𝓤 ̇ ) → (Σ \(f : X → Y) → is-vv-equiv f)) ≃⟨ classification-equivalence ⟩
  (Y → (Σ \(X : 𝓤 ̇ ) → is-singleton X))             ≃⟨ →-cong fe fe' (≃-refl Y) ψ ⟩
  (Y → 𝟙)                                           ≃⟨ →𝟙 fe ⟩
  𝟙                                                 ■
   where
    fe : funext 𝓤 𝓤
    fe = funext-from-univalence ua
    ϕ : (Σ \(X : 𝓤 ̇ ) → X ≃ Y) ≃ (Σ \(X : 𝓤 ̇ ) → (Σ \(f : X → Y) → is-vv-equiv f))
    ϕ = Σ-cong (λ (X : 𝓤 ̇ ) → Σ-cong (λ (f : X → Y) →
        logically-equivalent-props-are-equivalent (being-equiv-is-a-prop'' fe f)
                                                  (Π-is-prop fe (λ y → being-a-singleton-is-a-prop fe))
                                                  (equivs-are-vv-equivs f)
                                                  (vv-equivs-are-equivs f)))
    ψ : Σ (λ X → is-singleton X) ≃ 𝟙
    ψ = qinveq unique-to-𝟙 ((λ _ → 𝟙 , 𝟙-is-singleton) , (a , 𝟙-is-prop *))
     where
      a : (p : Σ (λ v → is-singleton v)) → 𝟙 , 𝟙-is-singleton ≡ p
      a (X , s) = to-Σ-≡ ((eqtoid ua 𝟙 X (singleton-≃-𝟙' s)) ,
                          (being-a-singleton-is-a-prop fe _ s))

\end{code}

This generalizes the above
situation. In particular, the case green = contractible is of interest
and describes a previously known situation. Another example is that
surjections X → Y are in bijection with families
Y → Σ (Z : 𝓤 ̇ ) → ∥ Z ∥), that is, families of inhabited types. It is
not necessary that "green" is proposition valued. It can be universe
valued in general. And then of course retractions X → Y are in
bijections with families of pointed types.

