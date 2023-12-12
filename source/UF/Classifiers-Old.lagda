Martin Escardo, 20th August 2018

We consider type and subtype classifiers, and discuss an obvious
generalization.

 * (Σ X ꞉ 𝓤 ̇ , X → Y) ≃ (Y → 𝓤 ̇ )
 * (Σ X ꞉ 𝓤 ̇ , X ↪ Y) ≃ (Y → Ω 𝓤)

\begin{code}

{-# OPTIONS --safe --without-K #-}

module UF.Classifiers-Old where

open import MLTT.Spartan
open import UF.Subsingletons
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.Equiv-FunExt
open import UF.Base
open import UF.Univalence
open import UF.UA-FunExt
open import UF.FunExt
open import UF.Embeddings
open import UF.SubtypeClassifier

module type-classifier
        {𝓤 : Universe}
        (fe' : funext 𝓤 (𝓤 ⁺))
        (ua : is-univalent 𝓤)
        (Y : 𝓤 ̇ )
       where

 χ : (Σ X ꞉ 𝓤 ̇ , (X → Y))  → (Y → 𝓤 ̇ )
 χ (X , f) = fiber f

 T : (Y → 𝓤 ̇ ) → Σ X ꞉ 𝓤 ̇ , (X → Y)
 T A = Σ A , pr₁

 χT : (A : Y → 𝓤 ̇ ) → χ (T A) ＝ A
 χT A = dfunext fe' γ
  where
   f : ∀ y → (Σ σ ꞉ Σ A , pr₁ σ ＝ y) → A y
   f y ((.y , a) , refl) = a
   g : ∀ y → A y → Σ σ ꞉ Σ A , pr₁ σ ＝ y
   g y a = (y , a) , refl
   fg : ∀ y a → f y (g y a) ＝ a
   fg y a = refl
   gf : ∀ y σ → g y (f y σ) ＝ σ
   gf y ((.y , a) , refl) = refl
   γ : ∀ y → (Σ σ ꞉ Σ A , pr₁ σ ＝ y) ＝ A y
   γ y = eqtoid ua _ _ (f y , ((g y , fg y) , (g y , gf y)))

 transport-map : {X X' Y : 𝓤 ̇ } (e : X ≃ X') (g : X → Y)
               → transport (λ - → - → Y) (eqtoid ua X X' e) g
               ＝ g ∘ eqtofun (≃-sym e)

 transport-map {X} {X'} {Y} e g = τ (eqtoid ua X X' e) refl
  where
   τ : (p : X ＝ X')
     → p ＝ eqtoid ua X X' e
     → transport (λ - → - → Y) p g ＝ g ∘ eqtofun (≃-sym e)
   τ refl q = ap (λ h → g ∘ h) s
    where
     r : idtoeq X X refl ＝ e
     r = idtoeq X X refl              ＝⟨ ap (idtoeq X X) q ⟩
         idtoeq X X (eqtoid ua X X e) ＝⟨ idtoeq-eqtoid ua X X e ⟩
         e                            ∎
     s : id ＝ eqtofun (≃-sym e)
     s = ap (λ - → eqtofun (≃-sym -)) r

 Tχ : (σ : Σ X ꞉ 𝓤 ̇ , (X → Y)) → T (χ σ) ＝ σ
 Tχ (X , f) = to-Σ-＝ (eqtoid ua _ _ (total-fiber-is-domain f) ,
                       transport-map (total-fiber-is-domain f) pr₁)

 χ-is-equivalence : is-equiv χ
 χ-is-equivalence = (T , χT) , (T , Tχ)

 classification-equivalence : (Σ X ꞉ 𝓤 ̇ , (X → Y)) ≃ (Y → 𝓤 ̇ )
 classification-equivalence = χ , χ-is-equivalence


module subtype-classifier
        {𝓤 : Universe}
        (fe' : funext 𝓤 (𝓤 ⁺))
        (ua : is-univalent 𝓤)
        (Y : 𝓤 ̇ )
       where

 fe : funext 𝓤 𝓤
 fe = univalence-gives-funext ua

 χ : (Σ X ꞉ 𝓤 ̇ , X ↪ Y)  → (Y → Ω 𝓤)
 χ (X , f , i) y = fiber f y , i y

 T : (Y → Ω 𝓤) → Σ X ꞉ 𝓤 ̇ , X ↪ Y
 T P = (Σ y ꞉ Y , P y holds) , pr₁ , pr₁-is-embedding (λ y → holds-is-prop (P y))

 χT : (P : Y → Ω 𝓤) → χ (T P) ＝ P
 χT P = dfunext fe' γ
  where
   f : ∀ y → χ (T P) y holds → P y holds
   f y ((.y , h) , refl) = h
   g : ∀ y → P y holds → χ (T P) y holds
   g y h = (y , h) , refl
   γ : (y : Y) → χ (T P) y ＝ P y
   γ y = Ω-ext-from-univalence ua (f y) (g y)

 transport-embedding : {X X' Y : 𝓤 ̇ } (e : X ≃ X') (g : X → Y) (i : is-embedding g)
                    → transport (λ - → - ↪ Y) (eqtoid ua X X' e) (g , i)
                    ＝ g ∘ eqtofun (≃-sym e) , ∘-is-embedding
                                                 (equivs-are-embeddings (eqtofun (≃-sym e))
                                                                        (eqtofun- (≃-sym e))) i
 transport-embedding {X} {X'} {Y} e g i = τ (eqtoid ua X X' e) refl
  where
   τ : (p : X ＝ X')
     → p ＝ eqtoid ua X X' e
     → transport (λ - → - ↪ Y) p (g , i)
     ＝ g ∘ eqtofun (≃-sym e) , ∘-is-embedding
                                  (equivs-are-embeddings (eqtofun (≃-sym e))
                                                         (eqtofun- (≃-sym e))) i
   τ refl q = to-Σ-＝ (ap (λ h → g ∘ h) s ,
                      being-embedding-is-prop fe (g ∘ eqtofun (≃-sym e)) _ _)
    where
     r : idtoeq X X refl ＝ e
     r = ap (idtoeq X X) q ∙ idtoeq-eqtoid ua X X e
     s : id ＝ eqtofun (≃-sym e)
     s = ap (λ - → eqtofun (≃-sym -)) r

 Tχ : (σ : Σ X ꞉ 𝓤 ̇ , X ↪ Y) → T (χ σ) ＝ σ
 Tχ (X , f , i) = to-Σ-＝ (eqtoid ua _ _ (total-fiber-is-domain f) ,
                          (transport-embedding (total-fiber-is-domain f) pr₁ (pr₁-is-embedding i)
                         ∙ to-Σ-＝' (being-embedding-is-prop fe f _ _)))

 χ-is-equivalence : is-equiv χ
 χ-is-equivalence = (T , χT) , (T , Tχ)

 classification-equivalence : (Σ X ꞉ 𝓤 ̇ , X ↪ Y) ≃ (Y → Ω 𝓤)
 classification-equivalence = χ , χ-is-equivalence

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

Tom de Jong, September 2019. I implement the above TODO.

(There is an alternative solution at
https://www.cs.bham.ac.uk/~mhe/HoTT-UF.in-Agda-Lecture-Notes/)

Fix type universes 𝓤 and 𝓥 and a type Y : 𝓤 ̇. Consider a property green : 𝓤 → 𝓥.
If X : 𝓤 ̇ and f : X → Y, then we say that f is a green map if all of its fibers
are green.

The general theorem says that type of green maps to Y is equivalent to the type
of green types: Green-map ≃ (Y → Green).

The examples are obtained by specialising to a specific property green:

 * Every type and map is green.
   (Σ X ꞉ 𝓤 ̇ , X → Y) ≃ (Y → 𝓤 ̇ )

 * A type is green exactly if it is a subsingleton.
   Then a map is green exactly if it is an embedding.
   (Σ X ꞉ 𝓤 ̇ , X ↪ Y) ≃ (Y → Ω 𝓤)

 * A type is green exactly if it is inhabited.
   Then a map is green exactly if it is a surjection.
   (Σ X ꞉ 𝓤 ̇ , (Σ f ꞉ X → Y , is-surjection f )) ≃ (Y → (Σ X ꞉ 𝓤 ̇  , ∥ X ∥))

 * A type is green exactly if it is pointed.
   Then a map is green exactly if it is a retraction.
   (Σ X ꞉ 𝓤 ̇ , Y ◁ X) ≃ (Y → (Σ X ꞉ 𝓤 ̇  , X))

\begin{code}

eqtoid-comp : (ua : is-univalent 𝓤) {X Y Z : 𝓤 ̇ } (f : X ≃ Y) (g : Y ≃ Z)
            → (eqtoid ua X Y f) ∙ (eqtoid ua Y Z g) ＝ eqtoid ua X Z (f ● g)
eqtoid-comp {𝓤} ua {X} {Y} {Z} f =
 JEq ua Y (λ Z g → eqtoid ua X Y f ∙ eqtoid ua Y Z g ＝ eqtoid ua X Z (f ● g)) γ Z
  where
   fe : funext 𝓤 𝓤
   fe = univalence-gives-funext ua
   h : f ＝ f ● ≃-refl Y
   h = (≃-refl-right' fe fe fe f)⁻¹

   γ = eqtoid ua X Y f ∙ eqtoid ua Y Y (≃-refl Y) ＝⟨ ap (λ - → eqtoid ua X Y f ∙ -) (eqtoid-refl ua Y) ⟩
       eqtoid ua X Y f                            ＝⟨ ap (λ - → eqtoid ua X Y -) h ⟩
       eqtoid ua X Y (f ● ≃-refl Y)               ∎

module general-classifier
        {𝓤 𝓥 : Universe}
        (fe : funext 𝓤 𝓥)
        (fe' : funext 𝓤 (𝓤 ⁺ ⊔ 𝓥))
        (ua : is-univalent 𝓤)
        (Y : 𝓤 ̇ )
        (green : 𝓤 ̇ → 𝓥 ̇ )
       where

 green-map : {X : 𝓤 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
 green-map f = (y : Y) → green (fiber f y)

 Green : 𝓤 ⁺ ⊔ 𝓥 ̇
 Green = Σ X ꞉ 𝓤 ̇ , green X

 Green-map : 𝓤 ⁺ ⊔ 𝓥 ̇
 Green-map = Σ X ꞉ 𝓤 ̇ , Σ f ꞉ (X → Y) , green-map f

 χ : Green-map  → (Y → Green)
 χ (X , f , g) y = (fiber f y) , (g y)

 fiber-equiv-＝ : (A : Y → Green) (y : Y) → pr₁ (A y) ＝ fiber pr₁ y
 fiber-equiv-＝ A y =
  (eqtoid ua (fiber pr₁ y) (pr₁ (A y)) (pr₁-fiber-equiv {𝓤} {𝓤} {Y} {pr₁ ∘ A} y)) ⁻¹

 T : (Y → Green) → Green-map
 T A = Σ (pr₁ ∘ A) , pr₁ , g
  where
   g : green-map pr₁
   g y = transport green (fiber-equiv-＝ A y) (pr₂ (A y))

 χT : (A : Y → Green) → χ (T A) ＝ A
 χT A = dfunext fe' γ
  where
   γ : (y : Y) → χ (T A) y ＝ A y
   γ y = to-Σ-＝ ((a ⁻¹) , b)
    where
     a : pr₁ (A y) ＝ pr₁ (χ (T A) y)
     a = fiber-equiv-＝ A y
     b = transport green (a ⁻¹) (pr₂ (χ (T A) y))               ＝⟨ refl ⟩
         transport green (a ⁻¹) (transport green a (pr₂ (A y))) ＝⟨ i ⟩
         transport green (a ∙ a ⁻¹) (pr₂ (A y))                 ＝⟨ ii ⟩
         transport green refl (pr₂ (A y))                       ＝⟨ refl ⟩
         pr₂ (A y)                                              ∎
      where
       i  = (transport-∙ green a (a ⁻¹)) ⁻¹
       ii = ap (λ - → transport green - (pr₂ (A y))) (trans-sym' a)

 green-maps-are-closed-under-precomp-with-equivs : {X X' : 𝓤 ̇ } (e : X' ≃ X)
                                                   {f : X → Y}
                                                 → green-map f
                                                 → green-map (f ∘ eqtofun e)
 green-maps-are-closed-under-precomp-with-equivs e {f} g y =
  transport green p (g y)
   where
    p : fiber f y ＝ fiber (f ∘ eqtofun e) y
    p = (eqtoid ua _ _ (precomposition-with-equiv-does-not-change-fibers e f y)) ⁻¹

 precomp-with-≃-refl-green-map : {X : 𝓤 ̇ } (f : X → Y) (g : green-map f)
                           → green-maps-are-closed-under-precomp-with-equivs
                              (≃-refl X) g
                             ＝ g
 precomp-with-≃-refl-green-map {X} f g = dfunext fe γ
  where
   γ : (y : Y) → green-maps-are-closed-under-precomp-with-equivs (≃-refl X) g y ＝ g y
   γ y = green-maps-are-closed-under-precomp-with-equivs (≃-refl X) g y         ＝⟨ refl ⟩
         transport green ((eqtoid ua _ _ (≃-refl (fiber f y))) ⁻¹) (g y)        ＝⟨ i ⟩
         g y                                                                    ∎
    where
     i = ap (λ - → transport green (- ⁻¹) (g y)) (eqtoid-refl ua (fiber f y))

 transport-green-map-eqtoid : {X X' : 𝓤 ̇ } (e : X' ≃ X) (f : X → Y)
                              (g : green-map f)
                            → transport (λ - → Σ h ꞉ (- → Y) , green-map h)
                               ((eqtoid ua X' X e) ⁻¹) (f , g)
                              ＝
                              f ∘ (eqtofun e) ,
                               green-maps-are-closed-under-precomp-with-equivs e g
 transport-green-map-eqtoid {X} {X'} = JEq ua X' E γ X
  where
   B : 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇
   B Z = Σ h ꞉ (Z → Y) , green-map h
   E : (Z : 𝓤 ̇ ) → X' ≃ Z → 𝓤 ⊔ 𝓥 ̇
   E Z e = (f : Z → Y) → (g : green-map f)
         → transport B ((eqtoid ua X' Z e) ⁻¹) (f , g)
           ＝ f ∘ (eqtofun e) , green-maps-are-closed-under-precomp-with-equivs e g
   γ : E X' (≃-refl X')
   γ f g = transport B ((eqtoid ua X' X' (≃-refl X')) ⁻¹) (f , g)            ＝⟨ i ⟩
           f , g                                                             ＝⟨ ii ⟩
           f , green-maps-are-closed-under-precomp-with-equivs (≃-refl X') g ∎
    where
     i  = ap (λ - → transport B (- ⁻¹) (f , g)) (eqtoid-refl ua X')
     ii = to-Σ-＝ (refl , ((precomp-with-≃-refl-green-map f g) ⁻¹))

 Tχ : (f : Green-map) → T (χ f) ＝ f
 Tχ (X , f , g) = to-Σ-＝ (a , (to-Σ-＝ (b , c)))
  where
   X' : 𝓤 ̇
   X' = pr₁ (T (χ (X , f , g)))
   f' : X' → Y
   f' = pr₁ (pr₂ (T (χ (X , f , g))))
   g' : green-map f'
   g' = pr₂ (pr₂ (T (χ (X , f , g))))
   e : X ≃ X'
   e = domain-is-total-fiber f
   a : X' ＝ X
   a = (eqtoid ua X X' e) ⁻¹
   B : 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇
   B Z = Σ h ꞉ (Z → Y), green-map h
   t : transport B a (f' , g') ＝
       (f' ∘ eqtofun e) , (green-maps-are-closed-under-precomp-with-equivs e g')
   t = transport-green-map-eqtoid e f' g'
   t₁ : pr₁ (transport B a (f' , g')) ＝ f' ∘ eqtofun e
   t₁ = pr₁ (from-Σ-＝ t)
   t₂ : transport green-map t₁ (pr₂ (transport B a (f' , g'))) ＝
        green-maps-are-closed-under-precomp-with-equivs e g'
   t₂ = pr₂ (from-Σ-＝ t)
   b : pr₁ (transport B a (f' , g')) ＝ f
   b = pr₁ (transport B a (f' , g')) ＝⟨ t₁ ⟩
       f' ∘ eqtofun e                ＝⟨ refl ⟩
       f                             ∎
   c : transport green-map b (pr₂ (transport B a (f' , g')))  ＝ g
   c = transport green-map b (pr₂ (transport B a (f' , g')))  ＝⟨ refl ⟩
       transport green-map t₁ (pr₂ (transport B a (f' , g'))) ＝⟨ t₂ ⟩
       green-maps-are-closed-under-precomp-with-equivs e g' ＝⟨ dfunext fe u ⟩
       g ∎
    where
     u : (y : Y) → green-maps-are-closed-under-precomp-with-equivs e g' y ＝ g y
     u y = green-maps-are-closed-under-precomp-with-equivs e g' y ＝⟨ refl ⟩
           transport green (p ⁻¹) (g' y)                          ＝⟨ refl ⟩
           transport green (p ⁻¹) (transport green (q ⁻¹) (g y))  ＝⟨ i ⟩
           transport green (q ⁻¹ ∙ p ⁻¹) (g y)                    ＝⟨ ii ⟩
           g y                                                    ∎
       where
        p : fiber (f' ∘ eqtofun e) y ＝ fiber f' y
        p = eqtoid ua _ _ (precomposition-with-equiv-does-not-change-fibers e f' y)
        q : fiber f' y ＝ fiber f y
        q = eqtoid ua (fiber f' y) (fiber f y) (pr₁-fiber-equiv y)
        i  = (transport-∙ green (q ⁻¹) (p ⁻¹)) ⁻¹
        ii = ap (λ - → transport green - (g y)) v
         where
          v = q ⁻¹ ∙ p ⁻¹ ＝⟨ ⁻¹-contravariant p q ⟩
              (p ∙ q) ⁻¹  ＝⟨ ap (_⁻¹) w ⟩
              refl        ∎
           where
            w : p ∙ q ＝ refl
            w = eqtoid ua _ _ ϕ ∙ eqtoid ua _ _ ψ ＝⟨ eqtoid-comp ua _ _ ⟩
                eqtoid ua _ _ (ϕ ● ψ)             ＝⟨ ap (eqtoid ua _ _) ϕψ ⟩
                eqtoid ua _ _ (≃-refl _)          ＝⟨ eqtoid-refl ua _ ⟩
                refl                              ∎
             where
              ϕ : fiber (f' ∘ eqtofun e) y ≃ fiber f' y
              ϕ = precomposition-with-equiv-does-not-change-fibers e f' y
              ψ : fiber pr₁ y ≃ pr₁ (χ (X , f , g) y)
              ψ = pr₁-fiber-equiv y
              ϕψ : ϕ ● ψ ＝ ≃-refl (fiber (f' ∘ eqtofun e) y)
              ϕψ = to-Σ-＝ (dfunext fe'' ϕψ' ,
                           being-equiv-is-prop'' fe'' id _ (id-is-equiv _))
               where
                ϕψ' : (z : fiber (f' ∘ eqtofun e) y)
                   → eqtofun (ϕ ● ψ) z ＝ z
                ϕψ' (x , refl) = refl
                fe'' : funext 𝓤 𝓤
                fe'' = univalence-gives-funext ua

 χ-is-equivalence : is-equiv χ
 χ-is-equivalence = (T , χT) , (T , Tχ)

 classification-equivalence : Green-map ≃ (Y → Green)
 classification-equivalence = χ , χ-is-equivalence

\end{code}

We now can get type-classifier above as a special case of this more
general situation:

\begin{code}

module type-classifier-bis
        {𝓤 : Universe}
        (fe' : funext 𝓤 (𝓤 ⁺))
        (ua : is-univalent 𝓤)
        (Y : 𝓤 ̇ )
       where

 open general-classifier (univalence-gives-funext ua) fe' ua Y (λ (X : 𝓤 ̇ ) → 𝟙)

 type-classification-equivalence : (Σ X ꞉ 𝓤 ̇ , (X → Y)) ≃ (Y → 𝓤 ̇ )
 type-classification-equivalence = (Σ X ꞉ 𝓤 ̇ , (X → Y)) ≃⟨ ϕ ⟩
                                   Green-map ≃⟨ classification-equivalence ⟩
                                   (Y → Green) ≃⟨ ψ ⟩
                                   (Y → 𝓤 ̇ ) ■
  where
   ϕ : (Σ X ꞉ 𝓤 ̇ , (X → Y)) ≃ Green-map
   ϕ = qinveq α (β , a , b)
    where
     α : (Σ X ꞉ 𝓤 ̇ , (X → Y)) → Green-map
     α (X , f) = X , (f , (λ y → ⋆))
     β : Green-map → (Σ X ꞉ 𝓤 ̇ , (X → Y))
     β (X , f , g) = X , f
     a : (p : Σ (λ X → X → Y)) → β (α p) ＝ p
     a (X , f) = refl
     b : (q : Green-map) → α (β q) ＝ q
     b (X , f , g) = to-Σ-＝ (refl ,
                             to-Σ-＝ (refl ,
                                     dfunext (univalence-gives-funext ua)
                                      (λ y → 𝟙-is-prop ⋆ (g y))))
   ψ : (Y → Green) ≃ (Y → 𝓤 ̇ )
   ψ = →cong fe' fe' (≃-refl Y) γ
    where
     γ : Green ≃ 𝓤 ̇
     γ = qinveq pr₁ ((λ X → (X , ⋆ )) , c , λ x → refl)
      where
       c : (p : Σ (λ X → 𝟙)) → pr₁ p , ⋆ ＝ p
       c (x , ⋆) = refl

\end{code}

And we also get the other examples in the TODO:

\begin{code}

module subsingleton-classifier
        {𝓤 : Universe}
        (fe' : funext 𝓤 (𝓤 ⁺))
        (ua : is-univalent 𝓤)
        (Y : 𝓤 ̇ )
       where

 open general-classifier (univalence-gives-funext ua) fe' ua Y
                         (λ (X : 𝓤 ̇ ) → is-prop X)

 subsingleton-classification-equivalence : (Σ X ꞉ 𝓤 ̇ , X ↪ Y) ≃ (Y → Ω 𝓤 )
 subsingleton-classification-equivalence = classification-equivalence

module singleton-classifier
        {𝓤 : Universe}
        (fe' : funext 𝓤 (𝓤 ⁺))
        (ua : is-univalent 𝓤)
        (Y : 𝓤 ̇ )
       where

 open import UF.Subsingletons-FunExt
 open general-classifier (univalence-gives-funext ua) fe' ua Y
                         (λ (X : 𝓤 ̇ ) → is-singleton X)

 singleton-classification-equivalence : (Σ X ꞉ 𝓤 ̇ , X ≃ Y) ≃ 𝟙 {𝓤}
 singleton-classification-equivalence =
  (Σ X ꞉ 𝓤 ̇ , X ≃ Y)                            ≃⟨ i ⟩
  (Σ X ꞉ 𝓤 ̇ , (Σ f ꞉ (X → Y), is-vv-equiv f)) ≃⟨ ii ⟩
  (Y → (Σ X ꞉ 𝓤 ̇ , is-singleton X))             ≃⟨ iii ⟩
  (Y → 𝟙)                                             ≃⟨ →𝟙 fe ⟩
  𝟙                                                   ■
   where
    fe : funext 𝓤 𝓤
    fe = univalence-gives-funext ua

    i   = Σ-cong (λ (X : 𝓤 ̇ ) → Σ-cong (λ (f : X → Y) →
           logically-equivalent-props-are-equivalent
            (being-equiv-is-prop'' fe f)
            (Π-is-prop fe (λ y → being-singleton-is-prop fe))
            (equivs-are-vv-equivs f)
            (vv-equivs-are-equivs f)))
    ii  = classification-equivalence
    iii = →cong fe fe' (≃-refl Y) ψ
     where
      ψ : Σ (λ X → is-singleton X) ≃ 𝟙
      ψ = qinveq unique-to-𝟙 ((λ _ → 𝟙 , 𝟙-is-singleton) , (a , 𝟙-is-prop ⋆))
       where
       a : (p : Σ (λ v → is-singleton v)) → 𝟙 , 𝟙-is-singleton ＝ p
       a (X , s) = to-Σ-＝ (eqtoid ua 𝟙 X (singleton-≃-𝟙' s) ,
                           being-singleton-is-prop fe _ s)

open import UF.PropTrunc

module inhabited-classifier
        {𝓤 : Universe}
        (fe' : funext 𝓤 (𝓤 ⁺))
        (ua : is-univalent 𝓤)
        (Y : 𝓤 ̇ )
        (pt : propositional-truncations-exist)
       where

 open import UF.ImageAndSurjection pt
 open PropositionalTruncation pt
 open general-classifier (univalence-gives-funext ua) fe' ua Y
                         (λ (X : 𝓤 ̇ ) → ∥ X ∥)

 inhabited-classification-equivalence :
  (Σ X ꞉ 𝓤 ̇ , (Σ f ꞉ (X → Y), is-surjection f )) ≃
   (Y → (Σ X ꞉ 𝓤 ̇ , ∥ X ∥))
 inhabited-classification-equivalence = classification-equivalence

module pointed-classifier
        {𝓤 : Universe}
        (fe' : funext 𝓤 (𝓤 ⁺))
        (ua : is-univalent 𝓤)
        (Y : 𝓤 ̇ )
       where

 open import UF.Retracts
 open general-classifier (univalence-gives-funext ua) fe' ua Y (λ (X : 𝓤 ̇ ) → X)

 pointed-classification-equivalence :
  (Σ X ꞉ 𝓤 ̇ , Y ◁ X) ≃ (Y → (Σ X ꞉ 𝓤 ̇  , X))
 pointed-classification-equivalence =
  (Σ X ꞉ 𝓤 ̇ , Y ◁ X)                                  ≃⟨ i ⟩
  (Σ X ꞉ 𝓤 ̇ , (Σ f ꞉ (X → Y) , ((y : Y) → fiber f y))) ≃⟨ ii ⟩
  (Y → (Σ X ꞉ 𝓤 ̇ , X))                                ■
   where
    i  = Σ-cong (λ (X : 𝓤 ̇ ) → Σ-cong (λ (f : X → Y) → retract-pointed-fibers))
    ii = classification-equivalence

\end{code}
