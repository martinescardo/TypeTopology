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

 {-
 left-Id-equiv' : {X : 𝓤 ̇ } {Y : X → 𝓤 ̇ } (x : X) → (Σ \(x' : X) → (x' ≡ x) × Y x') ≃ Y x
 left-Id-equiv' {X} {Y} x = qinveq f (g , gf , fg)
  where
   f : (Σ \(x' : X) → (x' ≡ x) × Y x') → Y x
   f (x' , refl , y) = y
   g : (y : Y x) → Σ (λ x' → (x' ≡ x) × Y x')
   g y = x , refl , y
   gf : (σ : Σ \(x' : X) → (x' ≡ x) × Y x') → g (f σ) ≡ σ
   gf (x' , refl , y) = refl
   fg : (y : Y x) → f (g y) ≡ y
   fg y = refl-}

 fiber-equiv' : {X : 𝓤 ̇ } {Y : X → 𝓤 ̇ } (x : X) → fiber (pr₁ {𝓤} {𝓤} {X} {Y}) x ≃ Y x
 fiber-equiv' {X} {Y} x = fiber-equiv x --α , {!!}
  where
   α : fiber pr₁ x → Y x
   α ((x , y) , p) = transport Y p y

 {-fiber pr₁ x                      ≃⟨ Σ-assoc ⟩
                          (Σ \(x' : X) → Y x' × (x' ≡ x))  ≃⟨ Σ-cong (λ x' → ×-comm) ⟩
                          (Σ \(x' : X) → (x' ≡ x) × Y x')  ≃⟨ left-Id-equiv' x ⟩
                          Y x                              ■            
 -}

 fiber-equiv-≡ : (A : Y → Green) (y : Y) → pr₁ (A y) ≡ fiber pr₁ y
 fiber-equiv-≡ A y =
  (eqtoid ua (fiber pr₁ y) (pr₁ (A y)) (fiber-equiv' {Y} {pr₁ ∘ A} y)) ⁻¹
  -- eqtoid ua (pr₁ (A y)) (fiber pr₁ y) (≃-sym (fiber-equiv {𝓤} {𝓤} {Y} {pr₁ ∘ A} y))
                      
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
     a : pr₁ (A y)  ≡ pr₁ (χ (T A) y)
     a = fiber-equiv-≡ A y
     b = transport green (a ⁻¹) (pr₂ (χ (T A) y))               ≡⟨ refl ⟩
         transport green (a ⁻¹) (transport green a (pr₂ (A y))) ≡⟨ (transport-comp green a (a ⁻¹)) ⁻¹ ⟩
         transport green (a ∙ a ⁻¹) (pr₂ (A y))                 ≡⟨ ap (λ - → transport green - (pr₂ (A y))) (trans-sym' a) ⟩
         transport green refl (pr₂ (A y))                       ≡⟨ refl ⟩
         pr₂ (A y)                                              ∎

 precomp-with-equiv-preserves-being-green : {X X' : 𝓤 ̇ } (e : X' ≃ X) {f : X → Y}
                                         → green-map f
                                         → green-map (f ∘ eqtofun e)
 precomp-with-equiv-preserves-being-green e {f} g y = transport green p (g y)
  where
   p : fiber f y ≡ fiber (f ∘ eqtofun e) y
   p = (eqtoid ua _ _ (precomp-with-equiv-fiber-equiv e f y)) ⁻¹
       -- eqtoid ua _ _ (≃-sym (precomp-with-equiv-fiber-equiv e f y))
       

 precomp-with-≃-refl-green : {X : 𝓤 ̇ } (f : X → Y) (g : green-map f)
                           → precomp-with-equiv-preserves-being-green (≃-refl X) g ≡ g
 precomp-with-≃-refl-green {X} f g = dfunext (funext-from-univalence ua) γ
  where
   γ : (y : Y) → precomp-with-equiv-preserves-being-green (≃-refl X) g y ≡ g y
   γ y = precomp-with-equiv-preserves-being-green (≃-refl X) g y ≡⟨ refl ⟩
         transport green ((eqtoid ua _ _ (≃-refl _)) ⁻¹) (g y)   ≡⟨ ap (λ - → transport green (- ⁻¹) (g y)) (eqtoid-refl ua _) ⟩
         g y ∎
     {-  transport green (eqtoid ua _ _ (≃-refl _)) (g y)        ≡⟨ ap (λ - → transport green - (g y)) (eqtoid-refl ua _) ⟩
         g y                                                     ∎ -}

 transport-green-eqtoid : {X X' : 𝓤 ̇ } (e : X' ≃ X) (f : X → Y) (g : green-map f)
                  → transport (λ - → Σ \(h : - → Y) → green-map h)
                     ((eqtoid ua X' X e) ⁻¹) (f , g)
                    ≡
                    f ∘ (eqtofun e) ,
                     precomp-with-equiv-preserves-being-green e g 
 transport-green-eqtoid {X} {X'} = JEq ua X' E γ X
  where
   B : 𝓤 ̇ → 𝓤 ̇
   B Z = Σ \(h : Z → Y) → green-map h
   E : (Z : 𝓤 ̇) → X' ≃ Z → 𝓤 ̇
   E Z e = (f : Z → Y) → (g : green-map f)
         → transport B ((eqtoid ua X' Z e) ⁻¹) (f , g)
           ≡ f ∘ (eqtofun e) , precomp-with-equiv-preserves-being-green e g
   γ : E X' (≃-refl X')
   γ f g = transport B ((eqtoid ua X' X' (≃-refl X')) ⁻¹) (f , g) ≡⟨ ap (λ - → transport B (- ⁻¹) (f , g)) (eqtoid-refl ua X') ⟩
           f , g ≡⟨ to-Σ-≡ (refl , ((precomp-with-≃-refl-green f g) ⁻¹)) ⟩
           f , precomp-with-equiv-preserves-being-green (≃-refl X') g ∎

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
       -- eqtoid ua X' X (≃-sym e)
   B : 𝓤 ̇ → 𝓤 ̇
   B Z = Σ \(h : Z → Y) → green-map h
   t : transport B a (f' , g') ≡ (f' ∘ eqtofun e) , (precomp-with-equiv-preserves-being-green e g')
   t = transport-green-eqtoid e f' g'
   t₁ : pr₁ (transport B a (f' , g')) ≡ f' ∘ eqtofun e
   t₁ = pr₁ (from-Σ-≡ t)
   t₂ : transport green-map t₁ (pr₂ (transport B a (f' , g')))
          ≡ precomp-with-equiv-preserves-being-green e g'
   t₂ = pr₂ (from-Σ-≡ t)
   b : pr₁ (transport B a (f' , g')) ≡ f
   b = pr₁ (transport B a (f' , g')) ≡⟨ t₁ ⟩
       f' ∘ eqtofun e ≡⟨ refl ⟩
       f ∎
   c : transport green-map b (pr₂ (transport B a (f' , g')))  ≡ g
   c = transport green-map b (pr₂ (transport B a (f' , g')))  ≡⟨ refl ⟩
       transport green-map t₁ (pr₂ (transport B a (f' , g'))) ≡⟨ t₂ ⟩
       precomp-with-equiv-preserves-being-green e g' ≡⟨ dfunext (funext-from-univalence ua) l ⟩
       g ∎
    where
     l : (y : Y) → precomp-with-equiv-preserves-being-green e g' y ≡ g y
     l y = precomp-with-equiv-preserves-being-green e g' y ≡⟨ refl ⟩
           transport green (p ⁻¹) (g' y) ≡⟨ refl ⟩
           transport green (p ⁻¹) (transport green (fiber-equiv-≡ (χ (X , f , g)) y) (g y)) ≡⟨ (transport-comp green (fiber-equiv-≡ (χ (X , f , g)) y) (p ⁻¹)) ⁻¹ ⟩
           transport green (fiber-equiv-≡ (χ (X , f , g)) y ∙ p ⁻¹) (g y) ≡⟨ ap (λ - → transport green - (g y)) k ⟩
           g y ∎
       where
        p : fiber (f' ∘ eqtofun e) y ≡ fiber f' y
        p = eqtoid ua _ _ (precomp-with-equiv-fiber-equiv e f' y)
        k : fiber-equiv-≡ (χ (X , f , g)) y ∙ p ⁻¹ ≡ refl
        k = fiber-equiv-≡ (χ (X , f , g)) y ∙ p ⁻¹ ≡⟨ refl ⟩
            q ⁻¹ ∙ p ⁻¹ ≡⟨ ⁻¹-contravariant p q ⟩
            (p ∙ q) ⁻¹ ≡⟨ ap (_⁻¹) k' ⟩
            refl ∎
         where
          q : fiber f' y ≡ fiber f y
          q = eqtoid ua (fiber f' y) (fiber f y) (fiber-equiv' y)
          k' : p ∙ q ≡ refl
          k' = eqtoid ua _ _ ϕ ∙ eqtoid ua _ _ ψ ≡⟨ eqtoid-comp ua _ _ ⟩
               eqtoid ua _ _ (ϕ ● ψ) ≡⟨ ap (eqtoid ua _ _) ϕψ ⟩
               eqtoid ua _ _ (≃-refl _) ≡⟨ eqtoid-refl ua _ ⟩
               refl ∎
           where
            ϕ : fiber (f' ∘ eqtofun e) y ≃ fiber f' y
            ϕ = precomp-with-equiv-fiber-equiv e f' y
            ψ : fiber pr₁ y ≃ pr₁ (χ (X , f , g) y)
            ψ = fiber-equiv' y
--            α : fiber (pr₁ {𝓤} {𝓤} {Y} {fiber f}) y → pr₁ (χ (X , f , g) y)
--            α ((y , (x , p)) , q) = x , (p ∙ q)
            ϕψ : ϕ ● ψ ≡ ≃-refl (fiber (f' ∘ eqtofun e) y)
            ϕψ = to-Σ-≡ ((dfunext (funext-from-univalence ua) pt) ,
                  being-equiv-is-a-prop' (funext-from-univalence ua) (funext-from-univalence ua) (funext-from-univalence ua) (funext-from-univalence ua)
                  (λ v → v) _ (id-is-an-equiv (pr₁ (χ (X , f , g) y))))
             where
              pt : (xp : fiber (f' ∘ eqtofun e) y)
                 → eqtofun (ϕ ● ψ) xp ≡ xp
              pt (x , refl) = refl
              

\end{code}

TODO. Consider a property "green" of types, and call a map green if
its fibers are all green. Then the maps of Y into green types should
correspond to the green maps X → Y. This generalizes the above
situation. In particular, the case green = contractible is of interest
and describes a previously known situation. Another example is that
surjections X → Y are in bijection with families
Y → Σ (Z : 𝓤 ̇ ) → ∥ Z ∥), that is, families of inhabited types. It is
not necessary that "green" is proposition valued. It can be universe
valued in general. And then of course retractions X → Y are in
bijections with families of pointed types.
