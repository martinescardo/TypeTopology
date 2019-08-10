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

module type-classifier
        {𝓤 : Universe}
        (fe' : funext 𝓤 (𝓤 ⁺))
        (ua : is-univalent 𝓤)
        (Y : 𝓤 ̇ )
       where

 χ : (Σ \(X : 𝓤 ̇ ) → X → Y)  → (Y → 𝓤 ̇ )
 χ (X , f) = fiber f

 T : (Y → 𝓤 ̇ ) → Σ \(X : 𝓤 ̇ ) → X → Y
 T A = Σ A , pr₁

 χT : (A : Y → 𝓤 ̇ ) → χ(T A) ≡ A
 χT A = dfunext fe' γ
  where
   f : ∀ y → (Σ \(σ : Σ A) → pr₁ σ ≡ y) → A y
   f y ((.y , a) , refl) = a
   g : ∀ y → A y → Σ \(σ : Σ A) → pr₁ σ ≡ y
   g y a = (y , a) , refl
   fg : ∀ y a → f y (g y a) ≡ a
   fg y a = refl
   gf : ∀ y σ → g y (f y σ) ≡ σ
   gf y ((.y , a) , refl) = refl
   γ : ∀ y → (Σ \(σ : Σ A) → pr₁ σ ≡ y) ≡ A y
   γ y = eqtoid ua _ _ (f y , ((g y , fg y) , (g y , gf y)))

 transport-map : {X X' Y : 𝓤 ̇ } (e : X ≃ X') (g : X → Y)
               → transport (λ - → - → Y) (eqtoid ua X X' e) g
               ≡ g ∘ eqtofun (≃-sym e)

 transport-map {X} {X'} {Y} e g = τ (eqtoid ua X X' e) refl
  where
   τ : (p : X ≡ X')
     → p ≡ eqtoid ua X X' e
     → transport (λ - → - → Y) p g ≡ g ∘ eqtofun (≃-sym e)
   τ refl q = ap (λ h → g ∘ h) s
    where
     r : idtoeq X X refl ≡ e
     r = idtoeq X X refl              ≡⟨ ap (idtoeq X X) q ⟩
         idtoeq X X (eqtoid ua X X e) ≡⟨ idtoeq-eqtoid ua X X e ⟩
         e                            ∎
     s : id ≡ eqtofun (≃-sym e)
     s = ap (λ - → eqtofun (≃-sym -)) r

 Tχ : (σ : Σ \(X : 𝓤 ̇ ) → X → Y) → T(χ σ) ≡ σ
 Tχ (X , f) = to-Σ-≡ (eqtoid ua _ _ (graph-domain-equiv f) , 
                       transport-map (graph-domain-equiv f) pr₁)

 χ-is-equivalence : is-equiv χ
 χ-is-equivalence = (T , χT) , (T , Tχ)

 classification-equivalence : (Σ \(X : 𝓤 ̇ ) → X → Y) ≃ (Y → 𝓤 ̇ )
 classification-equivalence = χ , χ-is-equivalence


module subtype-classifier
        {𝓤 : Universe}
        (fe' : funext 𝓤 (𝓤 ⁺))
        (ua : is-univalent 𝓤)
        (Y : 𝓤 ̇ )
       where

 fe : funext 𝓤 𝓤
 fe = funext-from-univalence ua

 χ : (Σ \(X : 𝓤 ̇ ) → X ↪ Y)  → (Y → Ω 𝓤)
 χ (X , f , i) y = fiber f y , i y

 T : (Y → Ω 𝓤) → Σ \(X : 𝓤 ̇ ) → X ↪ Y
 T P = (Σ \(y : Y) → P y holds) , pr₁ , pr₁-embedding (λ y → holds-is-prop (P y))

 χT : (P : Y → Ω 𝓤) → χ(T P) ≡ P
 χT P = dfunext fe' γ
  where
   f : ∀ y → χ (T P) y holds → P y holds
   f y ((.y , h) , refl) = h
   g : ∀ y → P y holds → χ (T P) y holds
   g y h = (y , h) , refl
   γ : (y : Y) → χ (T P) y ≡ P y
   γ y = Ω-ext-from-univalence ua (f y) (g y)

 transport-embedding : {X X' Y : 𝓤 ̇ } (e : X ≃ X') (g : X → Y) (i : is-embedding g)
                    → transport (λ - → - ↪ Y) (eqtoid ua X X' e) (g , i)
                    ≡ g ∘ eqtofun (≃-sym e) , comp-embedding
                                                 (equivs-are-embeddings (eqtofun (≃-sym e))
                                                                        (eqtofun-is-an-equiv (≃-sym e))) i
 transport-embedding {X} {X'} {Y} e g i = τ (eqtoid ua X X' e) refl
  where
   τ : (p : X ≡ X')
     → p ≡ eqtoid ua X X' e
     → transport (λ - → - ↪ Y) p (g , i)
     ≡ g ∘ eqtofun (≃-sym e) , comp-embedding
                                  (equivs-are-embeddings (eqtofun (≃-sym e))
                                                         (eqtofun-is-an-equiv (≃-sym e))) i
   τ refl q = to-Σ-≡ (ap (λ h → g ∘ h) s ,
                      being-embedding-is-a-prop fe fe (g ∘ eqtofun (≃-sym e)) _ _)
    where
     r : idtoeq X X refl ≡ e
     r = ap (idtoeq X X) q ∙ idtoeq-eqtoid ua X X e
     s : id ≡ eqtofun (≃-sym e)
     s = ap (λ - → eqtofun (≃-sym -)) r

 Tχ : (σ : Σ \(X : 𝓤 ̇ ) → X ↪ Y) → T(χ σ) ≡ σ
 Tχ (X , f , i) = to-Σ-≡ (eqtoid ua _ _ (graph-domain-equiv f) ,
                          (transport-embedding (graph-domain-equiv f) pr₁ (pr₁-embedding i)
                         ∙ to-Σ-≡' (being-embedding-is-a-prop fe fe f _ _)))

 χ-is-equivalence : is-equiv χ
 χ-is-equivalence = (T , χT) , (T , Tχ)

 classification-equivalence : (Σ \(X : 𝓤 ̇ ) → X ↪ Y) ≃ (Y → Ω 𝓤)
 classification-equivalence = χ , χ-is-equivalence

\end{code}

\begin{code}

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
 fiber-equiv-≡ A y = eqtoid ua (pr₁ (A y)) (fiber pr₁ y)
                      (≃-sym (fiber-equiv {𝓤} {𝓤} {Y} {pr₁ ∘ A} y))

 T : (Y → Green) → Green-map
 T A = Σ (pr₁ ∘ A) , pr₁ , g
  where
   g : green-map pr₁
   g y = transport green (fiber-equiv-≡ A y) (pr₂ (A y))
   
 χT : (A : Y → Green) → χ(T A) ≡ A
 χT A = dfunext fe' γ
  where
   γ : (y : Y) → χ (T A) y ≡ A y
   γ y = to-Σ-≡ ((p ⁻¹) , e)
    where
     p : pr₁ (A y) ≡ fiber pr₁ y
     p = fiber-equiv-≡ A y
     e = transport green (p ⁻¹) (pr₂ (χ (T A) y))               ≡⟨ refl ⟩
         transport green (p ⁻¹) (transport green p (pr₂ (A y))) ≡⟨ (transport-comp green p (p ⁻¹)) ⁻¹ ⟩
         transport green (p ∙ (p ⁻¹)) (pr₂ (A y))               ≡⟨ ap (λ - → transport green - (pr₂ (A y))) (trans-sym' p) ⟩
         transport green refl (pr₂ (A y))                       ≡⟨ refl ⟩
         pr₂ (A y)                                              ∎

 precomp-with-equiv-preserves-being-green : {X X' : 𝓤 ̇ } (e : X' ≃ X) {f : X → Y}
                                         → green-map f
                                         → green-map (f ∘ eqtofun e)
 precomp-with-equiv-preserves-being-green e {f} g y = transport green p (g y)
  where
   p : fiber f y ≡ fiber (f ∘ eqtofun e) y
   p = eqtoid ua _ _ (≃-sym (precomp-with-equiv-fiber-equiv e f y))

 precomp-with-≃-refl-green : {X : 𝓤 ̇ } (f : X → Y) (g : green-map f)
                           → precomp-with-equiv-preserves-being-green (≃-refl X) g ≡ g
 precomp-with-≃-refl-green {X} f g = dfunext (funext-from-univalence ua) γ
  where
   γ : (y : Y) → precomp-with-equiv-preserves-being-green (≃-refl X) g y ≡ g y
   γ y = precomp-with-equiv-preserves-being-green (≃-refl X) g y ≡⟨ refl ⟩
         transport green (eqtoid ua _ _ (≃-refl _)) (g y)        ≡⟨ ap (λ - → transport green - (g y)) (eqtoid-refl ua _) ⟩
         g y                                                     ∎

 transport-green-eqtoid : {X X' : 𝓤 ̇ } (e : X ≃ X') (f : X → Y) (g : green-map f)
                  → transport (λ - → Σ \(h : - → Y) → green-map h)
                     (eqtoid ua X X' e) (f , g)
                    ≡
                    f ∘ (eqtofun (≃-sym e)) ,
                     precomp-with-equiv-preserves-being-green (≃-sym e) g 
 transport-green-eqtoid {X} {X'} e f g = JEq ua X B γ X' e
  where
   B : (X₁ : 𝓤 ̇) → X ≃ X₁ → 𝓤 ̇
   B X₁ e₁ =
    transport (λ - → Σ \(h : - → Y) → green-map h)
     (eqtoid ua X X₁ e₁) (f , g)
    ≡
    f ∘ (eqtofun (≃-sym e₁)) ,
     precomp-with-equiv-preserves-being-green (≃-sym e₁) g
   γ = transport (λ - → Σ \(h : - → Y) → green-map h)
        (eqtoid ua X X (≃-refl X)) (f , g)                            ≡⟨ ap (λ p → (transport (λ - → Σ \(h : - → Y) → green-map h) p (f , g))) (eqtoid-refl ua X) ⟩
       transport (λ - → Σ \(h : - → Y) → green-map h) refl (f , g)    ≡⟨ refl ⟩
       (f , g)                                                        ≡⟨ to-Σ-≡ (refl , h) ⟩
       f ∘ (eqtofun (≃-sym (≃-refl X))) ,
        precomp-with-equiv-preserves-being-green (≃-sym (≃-refl X)) g ∎
    where
     h = transport (λ (h : X → Y) → green-map h) refl g                ≡⟨ refl ⟩
         g                                                             ≡⟨ (precomp-with-≃-refl-green f g) ⁻¹ ⟩
         precomp-with-equiv-preserves-being-green (≃-refl X) g         ≡⟨ refl ⟩
         precomp-with-equiv-preserves-being-green (≃-sym (≃-refl X)) g ∎

 key-lemma : {X : 𝓤 ̇ } (f : X → Y) (g : green-map f) (y : Y)
           → precomp-with-equiv-preserves-being-green (sum-of-fibers X Y f)
              (λ (y' : Y) → transport green (fiber-equiv-≡ (λ (y'' : Y) → (fiber f y'' , g y'')) y') (g y')) y
             ≡ g y
 key-lemma {X} f g y = {!!}

 Tχ : (f : Green-map) → T(χ f) ≡ f
 Tχ (X , f , g) = to-Σ-≡ (a , (to-Σ-≡ (b , c)))
  where
   X' : 𝓤 ̇
   X' = pr₁ (T (χ (X , (f , g))))
   f' : X' → Y
   f' = pr₁ (pr₂ (T (χ (X , f , g))))
   g' : green-map f'
   g' = pr₂ (pr₂ (T (χ (X , f , g))))
   e : X' ≃ X
   e = ≃-sym (sum-of-fibers X Y f)
   a : X' ≡ X
   a = eqtoid ua X' X e
   t : Σ \(h : X → Y) → green-map h
   t = transport (λ - → Σ (λ (h : - → Y) → green-map h)) a (f' , g')
   p : t ≡ f' ∘ eqtofun (≃-sym e) ,
            precomp-with-equiv-preserves-being-green (≃-sym e) g'
   p = transport-green-eqtoid e f' g'
   p₁ : pr₁ t ≡ f' ∘ eqtofun (≃-sym e)
   p₁ = pr₁ (from-Σ-≡ p)
   p₂ : transport green-map p₁ (pr₂ t) ≡ precomp-with-equiv-preserves-being-green (≃-sym e) g'
   p₂ = pr₂ (from-Σ-≡ p)
   b : pr₁ t ≡ f
   b = pr₁ t                  ≡⟨ p₁ ⟩
       f' ∘ eqtofun (≃-sym e) ≡⟨ refl ⟩
       f                      ∎
   c : transport green-map b (pr₂ t) ≡ g
   c = transport green-map b (pr₂ t)                         ≡⟨ p₂ ⟩
       precomp-with-equiv-preserves-being-green (≃-sym e) g' ≡⟨ {!!} ⟩ --ap (λ - → precomp-with-equiv-preserves-being-green {!-!} {!!}) (≃-sym-involutive {!!} e) ⟩
       precomp-with-equiv-preserves-being-green (sum-of-fibers X Y f) g' ≡⟨ dfunext (funext-from-univalence ua) (key-lemma f g) ⟩
       g                                                     ∎

{-precomp-with-equiv-preserves-being-green (sum-of-fibers X Y f) g' y  ≡⟨ refl ⟩
            transport green ((q y) ⁻¹) (g' y)                        ≡⟨ refl ⟩
            transport green ((q y) ⁻¹) (transport green (r y) (g y)) ≡⟨ (transport-comp green (r y) ((q y) ⁻¹)) ⁻¹ ⟩
            transport green ((r y) ∙ ((q y) ⁻¹)) (g y)               ≡⟨ ap (λ - → transport green - (g y)) (u y) ⟩
            transport green refl (g y)                               ≡⟨ refl ⟩            
            g y                                                      ∎
      where
       q : (y : Y) → fiber (f' ∘ eqtofun (sum-of-fibers X Y f)) y ≡ fiber f' y
       q y = eqtoid ua _ _ (precomp-with-equiv-fiber-equiv (≃-sym e) f' y)
       r : (y : Y) → fiber f y ≡ fiber f' y
       r y = fiber-equiv-≡ (λ (y' : Y) → fiber f y' , g y') y
       u : (y : Y) → (r y) ∙ (q y) ⁻¹ ≡ refl
       u y = (r y) ∙ (q y) ⁻¹                                   ≡⟨ refl ⟩
             eqtoid ua _ _ (≃-sym (fiber-equiv y)) ∙ (q y) ⁻¹ ≡⟨ ap (λ - → eqtoid ua _ _ (≃-sym (fiber-equiv y)) ∙ -) (eqtoid-inverse ua (precomp-with-equiv-fiber-equiv (≃-sym e) f' y)) ⟩
             eqtoid ua _ _ (≃-sym (fiber-equiv y)) ∙ eqtoid ua _ _ (≃-sym (precomp-with-equiv-fiber-equiv (≃-sym e) f' y)) ≡⟨ eqtoid-comp ua _ _ ⟩
             eqtoid ua _ _ ((≃-sym (fiber-equiv y)) ● (≃-sym (precomp-with-equiv-fiber-equiv (≃-sym e) f' y))) ≡⟨ ap (λ - → eqtoid ua _ _ -) v ⟩
             eqtoid ua _ _ (≃-refl (fiber f y))         ≡⟨ eqtoid-refl ua (fiber f y) ⟩
             refl         ∎
        where
         v : ≃-sym (fiber-equiv y) ● ≃-sym (precomp-with-equiv-fiber-equiv (≃-sym e) f' y)
             ≡ ≃-refl (fiber f y)
         v = {!!} -- w ⁻¹ ∙ (ap ≃-sym z)
          where
           w : ≃-sym
                 (precomp-with-equiv-fiber-equiv (≃-sym e) f' y ● fiber-equiv y)
                 ≡
                 ≃-sym (fiber-equiv y) ●
                 ≃-sym (precomp-with-equiv-fiber-equiv (≃-sym e) f' y)
           w = ≃-comp-sym' fe (precomp-with-equiv-fiber-equiv (≃-sym e) f' y) (fiber-equiv y)
           z : precomp-with-equiv-fiber-equiv (≃-sym e) f' y ● fiber-equiv y ≡ ≃-refl (fiber f y)
           z = to-Σ-≡ ((dfunext fe z') , {!--being-equiv-is-a-prop''!})
            where
             z' : (xp : fiber (f' ∘ eqtofun (≃-sym e)) y)
                → eqtofun (precomp-with-equiv-fiber-equiv (≃-sym e) f' y ● fiber-equiv y) xp
                  ≡ xp
             z' (x , ϕ) = eqtofun (precomp-with-equiv-fiber-equiv (≃-sym e) f' y ● fiber-equiv y) (x , ϕ) ≡⟨ refl ⟩
                          eqtofun (fiber-equiv y) (eqtofun (precomp-with-equiv-fiber-equiv (≃-sym e) f' y) (x , ϕ)) ≡⟨ {!!} ⟩
                          x , ϕ ∎
-}

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
