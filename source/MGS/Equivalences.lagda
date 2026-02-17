Martin Escardo 1st May 2020.

This is ported from the Midlands Graduate School 2019 lecture notes

 https://www.cs.bham.ac.uk/~mhe/HoTT-UF.in-Agda-Lecture-Notes/HoTT-UF-Agda.html
 https://github.com/martinescardo/HoTT-UF.Agda-Lecture-Notes

\begin{code}

{-# OPTIONS --safe --without-K #-}

module MGS.Equivalences where

open import MGS.Retracts public

invertible : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
invertible f = Σ g ꞉ (codomain f → domain f) , (g ∘ f ∼ id) × (f ∘ g ∼ id)

fiber : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) → Y → 𝓤 ⊔ 𝓥 ̇
fiber f y = Σ x ꞉ domain f , f x ＝ y

fiber-point : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {f : X → Y} {y : Y}
            → fiber f y → X

fiber-point (x , p) = x

fiber-identification : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {f : X → Y} {y : Y}
                     → (w : fiber f y) → f (fiber-point w) ＝ y

fiber-identification (x , p) = p

is-equiv : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
is-equiv f = (y : codomain f) → is-singleton (fiber f y)

inverse : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) → is-equiv f → (Y → X)
inverse f e y = fiber-point (center (fiber f y) (e y))

inverses-are-sections : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) (e : is-equiv f)
                      → f ∘ inverse f e ∼ id

inverses-are-sections f e y = fiber-identification (center (fiber f y) (e y))

inverse-centrality : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                     (f : X → Y) (e : is-equiv f) (y : Y) (t : fiber f y)
                   → (inverse f e y , inverses-are-sections f e y) ＝ t

inverse-centrality f e y = centrality (fiber f y) (e y)

inverses-are-retractions : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) (e : is-equiv f)
                         → inverse f e ∘ f ∼ id

inverses-are-retractions f e x = ap fiber-point p
 where
  p : inverse f e (f x) , inverses-are-sections f e (f x) ＝ x , refl (f x)
  p = inverse-centrality f e (f x) (x , (refl (f x)))

equivs-are-invertible : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                      → is-equiv f → invertible f

equivs-are-invertible f e = inverse f e ,
                            inverses-are-retractions f e ,
                            inverses-are-sections f e

invertibles-are-equivs : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                       → invertible f → is-equiv f

invertibles-are-equivs {𝓤} {𝓥} {X} {Y} f (g , η , ε) y₀ = iii
 where
  i : (y : Y) → (f (g y) ＝ y₀) ◁ (y ＝ y₀)
  i y =  r , s , transport-is-section (_＝ y₀) (ε y)
   where
    s : f (g y) ＝ y₀ → y ＝ y₀
    s = transport (_＝ y₀) (ε y)

    r : y ＝ y₀ → f (g y) ＝ y₀
    r = transport (_＝ y₀) ((ε y)⁻¹)

  ii : fiber f y₀ ◁ singleton-type y₀
  ii = (Σ x ꞉ X , f x ＝ y₀)     ◁⟨ Σ-reindexing-retract g (f , η) ⟩
       (Σ y ꞉ Y , f (g y) ＝ y₀) ◁⟨ Σ-retract i ⟩
       (Σ y ꞉ Y , y ＝ y₀)       ◀

  iii : is-singleton (fiber f y₀)
  iii = retract-of-singleton ii (singleton-types-are-singletons Y y₀)

inverses-are-equivs : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) (e : is-equiv f)
                    → is-equiv (inverse f e)

inverses-are-equivs f e = invertibles-are-equivs
                           (inverse f e)
                           (f , inverses-are-sections f e , inverses-are-retractions f e)

inversion-involutive : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) (e : is-equiv f)
                     → inverse (inverse f e) (inverses-are-equivs f e) ＝ f

inversion-involutive f e = refl f

id-invertible : (X : 𝓤 ̇ ) → invertible (𝑖𝑑 X)
id-invertible X = 𝑖𝑑 X , refl , refl

∘-invertible : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } {f : X → Y} {f' : Y → Z}
             → invertible f' → invertible f → invertible (f' ∘ f)

∘-invertible {𝓤} {𝓥} {𝓦} {X} {Y} {Z} {f} {f'} (g' , gf' , fg') (g , gf , fg) =
  g ∘ g' , η , ε
 where
  η = λ x → g (g' (f' (f x))) ＝⟨ ap g (gf' (f x)) ⟩
            g (f x)           ＝⟨ gf x ⟩
            x                 ∎

  ε = λ z → f' (f (g (g' z))) ＝⟨ ap f' (fg (g' z)) ⟩
            f' (g' z)         ＝⟨ fg' z ⟩
            z                 ∎

id-is-equiv : (X : 𝓤 ̇ ) → is-equiv (𝑖𝑑 X)
id-is-equiv = singleton-types-are-singletons

∘-is-equiv : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } {f : X → Y} {g : Y → Z}
           → is-equiv g → is-equiv f → is-equiv (g ∘ f)

∘-is-equiv {𝓤} {𝓥} {𝓦} {X} {Y} {Z} {f} {g} i j = γ
 where
  abstract
   γ : is-equiv (g ∘ f)
   γ = invertibles-are-equivs (g ∘ f)
         (∘-invertible (equivs-are-invertible g i)
         (equivs-are-invertible f j))

inverse-of-∘ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
               (f : X → Y) (g : Y → Z)
               (i : is-equiv f) (j : is-equiv g)
             → inverse f i ∘ inverse g j ∼ inverse (g ∘ f) (∘-is-equiv j i)

inverse-of-∘ f g i j z =

  f' (g' z)             ＝⟨ (ap (f' ∘ g') (s z))⁻¹ ⟩
  f' (g' (g (f (h z)))) ＝⟨ ap f' (inverses-are-retractions g j (f (h z))) ⟩
  f' (f (h z))          ＝⟨ inverses-are-retractions f i (h z) ⟩
  h z                   ∎

 where
  f' = inverse f i
  g' = inverse g j
  h  = inverse (g ∘ f) (∘-is-equiv j i)

  s : g ∘ f ∘ h ∼ id
  s = inverses-are-sections (g ∘ f) (∘-is-equiv j i)

_≃_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
X ≃ Y = Σ f ꞉ (X → Y), is-equiv f

Eq→fun ⌜_⌝ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → X ≃ Y → X → Y
Eq→fun (f , i) = f
⌜_⌝            = Eq→fun

Eq→fun-is-equiv ⌜⌝-is-equiv : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (e : X ≃ Y) → is-equiv (⌜ e ⌝)
Eq→fun-is-equiv (f , i) = i
⌜⌝-is-equiv             = Eq→fun-is-equiv

invertibility-gives-≃ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                      → invertible f → X ≃ Y

invertibility-gives-≃ f i = f , invertibles-are-equivs f i

Σ-induction-≃ : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {A : Σ Y → 𝓦 ̇ }
              → ((x : X) (y : Y x) → A (x , y)) ≃ ((z : Σ Y) → A z)

Σ-induction-≃ = invertibility-gives-≃ Σ-induction (curry , refl , refl)

Σ-flip : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : X → Y → 𝓦 ̇ }
       → (Σ x ꞉ X , Σ y ꞉ Y , A x y) ≃ (Σ y ꞉ Y , Σ x ꞉ X , A x y)

Σ-flip = invertibility-gives-≃ (λ (x , y , p) → (y , x , p))
          ((λ (y , x , p) → (x , y , p)) , refl , refl)

×-comm : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
       → (X × Y) ≃ (Y × X)

×-comm = invertibility-gives-≃ (λ (x , y) → (y , x))
          ((λ (y , x) → (x , y)) , refl , refl)

id-≃ : (X : 𝓤 ̇ ) → X ≃ X
id-≃ X = 𝑖𝑑 X , id-is-equiv X

_●_ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } → X ≃ Y → Y ≃ Z → X ≃ Z
(f , d) ● (f' , e) = f' ∘ f , ∘-is-equiv e d

≃-sym : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → X ≃ Y → Y ≃ X
≃-sym (f , e) = inverse f e , inverses-are-equivs f e

_≃⟨_⟩_ : (X : 𝓤 ̇ ) {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } → X ≃ Y → Y ≃ Z → X ≃ Z
_ ≃⟨ d ⟩ e = d ● e

_■ : (X : 𝓤 ̇ ) → X ≃ X
_■ = id-≃

transport-is-equiv : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) {x y : X} (p : x ＝ y)
                   → is-equiv (transport A p)

transport-is-equiv A (refl x) = id-is-equiv (A x)

Σ-＝-≃ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } (σ τ : Σ A)
      → (σ ＝ τ) ≃ (Σ p ꞉ pr₁ σ ＝ pr₁ τ , transport A p (pr₂ σ) ＝ pr₂ τ)

Σ-＝-≃ {𝓤} {𝓥} {X} {A}  σ τ = invertibility-gives-≃ from-Σ-＝ (to-Σ-＝ , η , ε)
 where
  η : (q : σ ＝ τ) → to-Σ-＝ (from-Σ-＝ q) ＝ q
  η (refl σ) = refl (refl σ)

  ε : (w : Σ p ꞉ pr₁ σ ＝ pr₁ τ , transport A p (pr₂ σ) ＝ pr₂ τ)
    → from-Σ-＝ (to-Σ-＝ w) ＝ w

  ε (refl p , refl q) = refl (refl p , refl q)

to-×-＝ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {z t : X × Y}
       → (pr₁ z ＝ pr₁ t) × (pr₂ z ＝ pr₂ t) → z ＝ t

to-×-＝ (refl x , refl y) = refl (x , y)

from-×-＝ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {z t : X × Y}
         → z ＝ t → (pr₁ z ＝ pr₁ t) × (pr₂ z ＝ pr₂ t)

from-×-＝ {𝓤} {𝓥} {X} {Y} (refl (x , y)) = (refl x , refl y)

×-＝-≃ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (z t : X × Y)
      → (z ＝ t) ≃ (pr₁ z ＝ pr₁ t) × (pr₂ z ＝ pr₂ t)

×-＝-≃ {𝓤} {𝓥} {X} {Y} z t = invertibility-gives-≃ from-×-＝ (to-×-＝ , η , ε)
 where
  η : (p : z ＝ t) → to-×-＝ (from-×-＝ p) ＝ p
  η (refl z) = refl (refl z)

  ε : (q : (pr₁ z ＝ pr₁ t) × (pr₂ z ＝ pr₂ t)) → from-×-＝ (to-×-＝ q) ＝ q
  ε (refl x , refl y) = refl (refl x , refl y)

ap-pr₁-to-×-＝ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {z t : X × Y}
              → (p₁ : pr₁ z ＝ pr₁ t)
              → (p₂ : pr₂ z ＝ pr₂ t)
              → ap pr₁ (to-×-＝ (p₁ , p₂)) ＝ p₁

ap-pr₁-to-×-＝ (refl x) (refl y) = refl (refl x)

ap-pr₂-to-×-＝ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {z t : X × Y}
              → (p₁ : pr₁ z ＝ pr₁ t)
              → (p₂ : pr₂ z ＝ pr₂ t)
              → ap pr₂ (to-×-＝ (p₁ , p₂)) ＝ p₂

ap-pr₂-to-×-＝ (refl x) (refl y) = refl (refl y)

Σ-cong : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {B : X → 𝓦 ̇ }
       → ((x : X) → A x ≃ B x) → Σ A ≃ Σ B

Σ-cong {𝓤} {𝓥} {𝓦} {X} {A} {B} φ =
  invertibility-gives-≃ (NatΣ f) (NatΣ g , NatΣ-η , NatΣ-ε)
 where
  f : (x : X) → A x → B x
  f x = ⌜ φ x ⌝

  g : (x : X) → B x → A x
  g x = inverse (f x) (⌜⌝-is-equiv (φ x))

  η : (x : X) (a : A x) → g x (f x a) ＝ a
  η x = inverses-are-retractions (f x) (⌜⌝-is-equiv (φ x))

  ε : (x : X) (b : B x) → f x (g x b) ＝ b
  ε x = inverses-are-sections (f x) (⌜⌝-is-equiv (φ x))

  NatΣ-η : (w : Σ A) → NatΣ g (NatΣ f w) ＝ w
  NatΣ-η (x , a) = x , g x (f x a) ＝⟨ to-Σ-＝' (η x a) ⟩
                   x , a           ∎

  NatΣ-ε : (t : Σ B) → NatΣ f (NatΣ g t) ＝ t
  NatΣ-ε (x , b) = x , f x (g x b) ＝⟨ to-Σ-＝' (ε x b) ⟩
                   x , b           ∎

≃-gives-◁ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → X ≃ Y → X ◁ Y
≃-gives-◁ (f , e) = (inverse f e , f , inverses-are-retractions f e)

≃-gives-▷ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → X ≃ Y → Y ◁ X
≃-gives-▷ (f , e) = (f , inverse f e , inverses-are-sections f e)

equiv-to-singleton : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                   → X ≃ Y → is-singleton Y → is-singleton X

equiv-to-singleton e = retract-of-singleton (≃-gives-◁ e)

infix  10 _≃_
infixl 30 _●_
infixr  0 _≃⟨_⟩_
infix   1 _■

\end{code}
