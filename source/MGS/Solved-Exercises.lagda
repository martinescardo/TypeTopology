Martin Escardo 1st May 2020.

This is ported from the Midlands Graduate School 2019 lecture notes

 https://www.cs.bham.ac.uk/~mhe/HoTT-UF.in-Agda-Lecture-Notes/HoTT-UF-Agda.html
 https://github.com/martinescardo/HoTT-UF.Agda-Lecture-Notes

\begin{code}

{-# OPTIONS --safe --without-K #-}

module MGS.Solved-Exercises where

open import MGS.Equivalences public

subsingleton-criterion : {X : 𝓤 ̇ }
                       → (X → is-singleton X)
                       → is-subsingleton X

subsingleton-criterion' : {X : 𝓤 ̇ }
                        → (X → is-subsingleton X)
                        → is-subsingleton X

retract-of-subsingleton : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                        → Y ◁ X → is-subsingleton X → is-subsingleton Y

left-cancellable : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
left-cancellable f = {x x' : domain f} → f x ＝ f x' → x ＝ x'

lc-maps-reflect-subsingletons : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                              → left-cancellable f
                              → is-subsingleton Y
                              → is-subsingleton X

has-retraction : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
has-retraction s = Σ r ꞉ (codomain s → domain s), r ∘ s ∼ id

sections-are-lc : {X : 𝓤 ̇ } {A : 𝓥 ̇ } (s : X → A)
                → has-retraction s → left-cancellable s

equivs-have-retractions : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                        → is-equiv f → has-retraction f

equivs-have-sections : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                     → is-equiv f → has-section f

equivs-are-lc : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
              → is-equiv f → left-cancellable f

equiv-to-subsingleton : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                      → X ≃ Y
                      → is-subsingleton Y
                      → is-subsingleton X

comp-inverses : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
                (f : X → Y) (g : Y → Z)
                (i : is-equiv f) (j : is-equiv g)
                (f' : Y → X) (g' : Z → Y)
              → f' ∼ inverse f i
              → g' ∼ inverse g j
              → f' ∘ g' ∼ inverse (g ∘ f) (∘-is-equiv j i)

equiv-to-set : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
             → X ≃ Y
             → is-set Y
             → is-set X

sections-closed-under-∼ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f g : X → Y)
                        → has-retraction f
                        → g ∼ f
                        → has-retraction g

retractions-closed-under-∼ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f g : X → Y)
                           → has-section f
                           → g ∼ f
                           → has-section g

is-joyal-equiv : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
is-joyal-equiv f = has-section f × has-retraction f

one-inverse : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ )
              (f : X → Y) (r s : Y → X)
            → (r ∘ f ∼ id)
            → (f ∘ s ∼ id)
            → r ∼ s

joyal-equivs-are-invertible : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                            → is-joyal-equiv f → invertible f

joyal-equivs-are-equivs : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                        → is-joyal-equiv f → is-equiv f

invertibles-are-joyal-equivs : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                             → invertible f → is-joyal-equiv f

equivs-are-joyal-equivs : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                        → is-equiv f → is-joyal-equiv f

equivs-closed-under-∼ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {f g : X → Y}
                      → is-equiv f
                      → g ∼ f
                      → is-equiv g

equiv-to-singleton' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                    → X ≃ Y → is-singleton X → is-singleton Y

subtypes-of-sets-are-sets' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (m : X → Y)
                          → left-cancellable m → is-set Y → is-set X

pr₁-lc : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
       → ((x : X) → is-subsingleton (A x))
       → left-cancellable (λ (t : Σ A) → pr₁ t)

subsets-of-sets-are-sets : (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ )
                         → is-set X
                         → ((x : X) → is-subsingleton (A x))
                         → is-set (Σ x ꞉ X , A x)

to-subtype-＝ : {X : 𝓦 ̇ } {A : X → 𝓥 ̇ }
               {x y : X} {a : A x} {b : A y}
             → ((x : X) → is-subsingleton (A x))
             → x ＝ y
             → (x , a) ＝ (y , b)

pr₁-equiv : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
          → ((x : X) → is-singleton (A x))
          → is-equiv (λ (t : Σ A) → pr₁ t)

pr₁-≃ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
      → ((x : X) → is-singleton (A x))
      → Σ A ≃ X

pr₁-≃ i = pr₁ , pr₁-equiv i

ΠΣ-distr-≃ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {P : (x : X) → A x → 𝓦 ̇ }
           → (Π x ꞉ X , Σ a ꞉ A x , P x a)
           ≃ (Σ f ꞉ Π A , Π x ꞉ X , P x (f x))

Σ-assoc : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {Z : Σ Y → 𝓦 ̇ }
        → Σ Z ≃ (Σ x ꞉ X , Σ y ꞉ Y x , Z (x , y))

⁻¹-≃ : {X : 𝓤 ̇ } (x y : X) → (x ＝ y) ≃ (y ＝ x)

singleton-types-≃ : {X : 𝓤 ̇ } (x : X) → singleton-type' x ≃ singleton-type x

singletons-≃ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
             → is-singleton X → is-singleton Y → X ≃ Y

maps-of-singletons-are-equivs : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                              → is-singleton X → is-singleton Y → is-equiv f

logically-equivalent-subsingletons-are-equivalent : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ )
                                                  → is-subsingleton X
                                                  → is-subsingleton Y
                                                  → X ↔ Y
                                                  → X ≃ Y

singletons-are-equivalent : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ )
                          → is-singleton X
                          → is-singleton Y
                          → X ≃ Y

NatΣ-fiber-equiv : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (B : X → 𝓦 ̇ ) (φ : Nat A B)
                   (x : X) (b : B x)
                 → fiber (φ x) b ≃ fiber (NatΣ φ) (x , b)

NatΣ-equiv-gives-fiberwise-equiv : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {B : X → 𝓦 ̇ }
                                   (φ : Nat A B)
                                 → is-equiv (NatΣ φ)
                                 → ((x : X) → is-equiv (φ x))

Σ-is-subsingleton : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
                  → is-subsingleton X
                  → ((x : X) → is-subsingleton (A x))
                  → is-subsingleton (Σ A)

×-is-singleton : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                  → is-singleton X
                  → is-singleton Y
                  → is-singleton (X × Y)

×-is-subsingleton : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                  → is-subsingleton X
                  → is-subsingleton Y
                  → is-subsingleton (X × Y)

×-is-subsingleton' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                   → ((Y → is-subsingleton X) × (X → is-subsingleton Y))
                   → is-subsingleton (X × Y)

×-is-subsingleton'-back : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                        → is-subsingleton (X × Y)
                        → (Y → is-subsingleton X) × (X → is-subsingleton Y)

ap₂ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } (f : X → Y → Z) {x x' : X} {y y' : Y}
    → x ＝ x' → y ＝ y' → f x y ＝ f x' y'

subsingleton-criterion = sol
 where
  sol : {X : 𝓤 ̇ } → (X → is-singleton X) → is-subsingleton X
  sol f x = singletons-are-subsingletons (domain f) (f x) x

subsingleton-criterion' = sol
 where
  sol : {X : 𝓤 ̇ } → (X → is-subsingleton X) → is-subsingleton X
  sol f x y = f x x y

retract-of-subsingleton = sol
 where
  sol : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
      → Y ◁ X → is-subsingleton X → is-subsingleton Y
  sol (r , s , η) i =  subsingleton-criterion
                        (λ x → retract-of-singleton (r , s , η)
                                (pointed-subsingletons-are-singletons
                                  (codomain s) (s x) i))

lc-maps-reflect-subsingletons = sol
 where
  sol : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
      → left-cancellable f → is-subsingleton Y → is-subsingleton X
  sol f l s x x' = l (s (f x) (f x'))

sections-are-lc = sol
 where
  sol : {X : 𝓤 ̇ } {A : 𝓥 ̇ } (s : X → A)
      → has-retraction s → left-cancellable s
  sol s (r , ε) {x} {y} p = x       ＝⟨ (ε x)⁻¹ ⟩
                            r (s x) ＝⟨ ap r p ⟩
                            r (s y) ＝⟨ ε y ⟩
                            y       ∎

equivs-have-retractions = sol
 where
  sol : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) → is-equiv f → has-retraction f
  sol f e = (inverse f e , inverses-are-retractions f e)

equivs-have-sections = sol
 where
  sol : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) → is-equiv f → has-section f
  sol f e = (inverse f e , inverses-are-sections f e)

equivs-are-lc = sol
 where
  sol : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) → is-equiv f → left-cancellable f
  sol f e = sections-are-lc f (equivs-have-retractions f e)

equiv-to-subsingleton = sol
 where
  sol : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → X ≃ Y → is-subsingleton Y → is-subsingleton X
  sol (f , i) = lc-maps-reflect-subsingletons f (equivs-are-lc f i)

comp-inverses = sol
 where
  sol : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
        (f : X → Y) (g : Y → Z)
        (i : is-equiv f) (j : is-equiv g)
        (f' : Y → X) (g' : Z → Y)
      → f' ∼ inverse f i
      → g' ∼ inverse g j
      → f' ∘ g' ∼ inverse (g ∘ f) (∘-is-equiv j i)
  sol f g i j f' g' h k z =
   f' (g' z)                          ＝⟨ h (g' z) ⟩
   inverse f i (g' z)                 ＝⟨ ap (inverse f i) (k z) ⟩
   inverse f i (inverse g j z)        ＝⟨ inverse-of-∘ f g i j z ⟩
   inverse (g ∘ f) (∘-is-equiv j i) z ∎

equiv-to-set = sol
 where
  sol : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → X ≃ Y → is-set Y → is-set X
  sol e = subtypes-of-sets-are-sets' ⌜ e ⌝ (equivs-are-lc ⌜ e ⌝ (⌜⌝-is-equiv e))

sections-closed-under-∼ = sol
 where
  sol : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f g : X → Y)
      → has-retraction f → g ∼ f → has-retraction g
  sol f g (r , rf) h = (r ,
                        λ x → r (g x) ＝⟨ ap r (h x) ⟩
                              r (f x) ＝⟨ rf x ⟩
                              x       ∎)

retractions-closed-under-∼ = sol
 where
  sol : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f g : X → Y)
      → has-section f → g ∼ f → has-section g
  sol f g (s , fs) h = (s ,
                        λ y → g (s y) ＝⟨ h (s y) ⟩
                              f (s y) ＝⟨ fs y ⟩
                              y ∎)

one-inverse = sol
 where
  sol : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ )
        (f : X → Y) (r s : Y → X)
      → (r ∘ f ∼ id)
      → (f ∘ s ∼ id)
      → r ∼ s
  sol X Y f r s h k y = r y         ＝⟨ ap r ((k y)⁻¹) ⟩
                        r (f (s y)) ＝⟨ h (s y) ⟩
                        s y         ∎

joyal-equivs-are-invertible = sol
 where
  sol : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
      → is-joyal-equiv f → invertible f
  sol f ((s , ε) , (r , η)) = (s , sf , ε)
   where
    sf = λ (x : domain f) → s (f x)       ＝⟨ (η (s (f x)))⁻¹ ⟩
                            r (f (s (f x))) ＝⟨ ap r (ε (f x)) ⟩
                            r (f x)       ＝⟨ η x ⟩
                            x            ∎

joyal-equivs-are-equivs = sol
 where
  sol : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
      → is-joyal-equiv f → is-equiv f
  sol f j = invertibles-are-equivs f (joyal-equivs-are-invertible f j)

invertibles-are-joyal-equivs = sol
 where
  sol : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
      → invertible f → is-joyal-equiv f
  sol f (g , η , ε) = ((g , ε) , (g , η))

equivs-are-joyal-equivs = sol
 where
  sol : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
      → is-equiv f → is-joyal-equiv f
  sol f e = invertibles-are-joyal-equivs f (equivs-are-invertible f e)

equivs-closed-under-∼ = sol
 where
  sol : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {f g : X → Y}
      → is-equiv f → g ∼ f → is-equiv g
  sol {𝓤} {𝓥} {X} {Y} {f} {g} e h = joyal-equivs-are-equivs g
                                      (retractions-closed-under-∼ f g
                                       (equivs-have-sections f e) h ,
                                      sections-closed-under-∼ f g
                                       (equivs-have-retractions f e) h)

equiv-to-singleton' = sol
 where
  sol : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
      → X ≃ Y → is-singleton X → is-singleton Y
  sol e = retract-of-singleton (≃-gives-▷ e)

subtypes-of-sets-are-sets' = sol
 where
  sol : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (m : X → Y)
      → left-cancellable m → is-set Y → is-set X
  sol {𝓤} {𝓥} {X} m i h = types-with-wconstant-＝-endomaps-are-sets X c
   where
    f : (x x' : X) → x ＝ x' → x ＝ x'
    f x x' r = i (ap m r)

    κ : (x x' : X) (r s : x ＝ x') → f x x' r ＝ f x x' s
    κ x x' r s = ap i (h (m x) (m x') (ap m r) (ap m s))

    c : wconstant-＝-endomaps X
    c x x' = f x x' , κ x x'

pr₁-lc = sol
 where
  sol : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
      → ((x : X) → is-subsingleton (A x))
      → left-cancellable  (λ (t : Σ A) → pr₁ t)
  sol i p = to-Σ-＝ (p , i _ _ _)

subsets-of-sets-are-sets = sol
 where
  sol : (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ )
     → is-set X
     → ((x : X) → is-subsingleton (A x))
     → is-set (Σ x ꞉ X , A x)
  sol X A h p = subtypes-of-sets-are-sets' pr₁ (pr₁-lc p) h

to-subtype-＝ = sol
 where
  sol : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
        {x y : X} {a : A x} {b : A y}
      → ((x : X) → is-subsingleton (A x))
      → x ＝ y
      → (x , a) ＝ (y , b)
  sol {𝓤} {𝓥} {X} {A} {x} {y} {a} {b} s p = to-Σ-＝ (p , s y (transport A p a) b)

pr₁-equiv = sol
 where
  sol : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
      → ((x : X) → is-singleton (A x))
      → is-equiv (λ (t : Σ A) → pr₁ t)
  sol {𝓤} {𝓥} {X} {A} s = invertibles-are-equivs pr₁ (g , η , ε)
   where
    g : X → Σ A
    g x = x , pr₁ (s x)

    ε : (x : X) → pr₁ (g x) ＝ x
    ε x = refl (pr₁ (g x))

    η : (σ : Σ A) → g (pr₁ σ) ＝ σ
    η (x , a) = to-subtype-＝ (λ x → singletons-are-subsingletons (A x) (s x)) (ε x)

ΠΣ-distr-≃ = sol
 where
  sol : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {P : (x : X) → A x → 𝓦 ̇ }
      → (Π x ꞉ X , Σ a ꞉ A x , P x a)
      ≃ (Σ f ꞉ Π A , Π x ꞉ X , P x (f x))
  sol {𝓤} {𝓥} {𝓦} {X} {A} {P} = invertibility-gives-≃ φ (γ , η , ε)
   where
    φ : (Π x ꞉ X , Σ a ꞉ A x , P x a)
      → Σ f ꞉ Π A , Π x ꞉ X , P x (f x)
    φ g = ((λ x → pr₁ (g x)) , λ x → pr₂ (g x))

    γ : (Σ f ꞉ Π A , Π x ꞉ X , P x (f x))
      → Π x ꞉ X , Σ a ꞉ A x , P x a
    γ (f , φ) x = f x , φ x

    η : γ ∘ φ ∼ id
    η = refl

    ε : φ ∘ γ ∼ id
    ε = refl

Σ-assoc = sol
 where
  sol : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {Z : Σ Y → 𝓦 ̇ }
      → Σ Z ≃ (Σ x ꞉ X , Σ y ꞉ Y x , Z (x , y))
  sol {𝓤} {𝓥} {𝓦} {X} {Y} {Z} = invertibility-gives-≃ f (g , refl , refl)
   where
    f : Σ Z → Σ x ꞉ X , Σ y ꞉ Y x , Z (x , y)
    f ((x , y) , z) = (x , (y , z))

    g : (Σ x ꞉ X , Σ y ꞉ Y x , Z (x , y)) → Σ Z
    g (x , (y , z)) = ((x , y) , z)

⁻¹-is-equiv : {X : 𝓤 ̇ } (x y : X)
            → is-equiv (λ (p : x ＝ y) → p ⁻¹)
⁻¹-is-equiv x y = invertibles-are-equivs _⁻¹
                   (_⁻¹ , ⁻¹-involutive , ⁻¹-involutive)

⁻¹-≃ = sol
 where
  sol : {X : 𝓤 ̇ } (x y : X) → (x ＝ y) ≃ (y ＝ x)
  sol x y = (_⁻¹ , ⁻¹-is-equiv x y)

singleton-types-≃ = sol
 where
  sol : {X : 𝓤 ̇ } (x : X) → singleton-type' x ≃ singleton-type x
  sol x = Σ-cong (λ y → ⁻¹-≃ x y)

singletons-≃ = sol
 where
  sol : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
      → is-singleton X → is-singleton Y → X ≃ Y
  sol {𝓤} {𝓥} {X} {Y} i j = invertibility-gives-≃ f (g , η , ε)
   where
    f : X → Y
    f x = center Y j

    g : Y → X
    g y = center X i

    η : (x : X) → g (f x) ＝ x
    η = centrality X i

    ε : (y : Y) → f (g y) ＝ y
    ε = centrality Y j

maps-of-singletons-are-equivs = sol
 where
  sol : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
      → is-singleton X → is-singleton Y → is-equiv f

  sol {𝓤} {𝓥} {X} {Y} f i j = invertibles-are-equivs f (g , η , ε)
   where
    g : Y → X
    g y = center X i

    η : (x : X) → g (f x) ＝ x
    η = centrality X i

    ε : (y : Y) → f (g y) ＝ y
    ε y = singletons-are-subsingletons Y j (f (g y)) y

logically-equivalent-subsingletons-are-equivalent = sol
 where
  sol : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ )
      → is-subsingleton X → is-subsingleton Y → X ↔ Y → X ≃ Y
  sol  X Y i j (f , g) = invertibility-gives-≃ f
                          (g ,
                           (λ x → i (g (f x)) x) ,
                           (λ y → j (f (g y)) y))

singletons-are-equivalent = sol
 where
  sol : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ )
      → is-singleton X → is-singleton Y → X ≃ Y
  sol  X Y i j = invertibility-gives-≃ (λ _ → center Y j)
                  ((λ _ → center X i) ,
                   centrality X i ,
                   centrality Y j)

NatΣ-fiber-equiv = sol
 where
  sol : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (B : X → 𝓦 ̇ ) (φ : Nat A B)
        (x : X) (b : B x)
      → fiber (φ x) b ≃ fiber (NatΣ φ) (x , b)
  sol A B φ x b = invertibility-gives-≃ f (g , ε , η)
   where
    f : fiber (φ x) b → fiber (NatΣ φ) (x , b)
    f (a , refl _) = ((x , a) , refl (x , φ x a))

    g : fiber (NatΣ φ) (x , b) → fiber (φ x) b
    g ((x , a) , refl _) = (a , refl (φ x a))

    ε : (w : fiber (φ x) b) → g (f w) ＝ w
    ε (a , refl _) = refl (a , refl (φ x a))

    η : (t : fiber (NatΣ φ) (x , b)) → f (g t) ＝ t
    η ((x , a) , refl _) = refl ((x , a) , refl (NatΣ φ (x , a)))

NatΣ-equiv-gives-fiberwise-equiv = sol
 where
  sol : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {B : X → 𝓦 ̇ } (φ : Nat A B)
      → is-equiv (NatΣ φ) → ((x : X) → is-equiv (φ x))
  sol {𝓤} {𝓥} {𝓦} {X} {A} {B} φ e x b = γ
   where
    d : fiber (φ x) b ≃ fiber (NatΣ φ) (x , b)
    d = NatΣ-fiber-equiv A B φ x b

    s : is-singleton (fiber (NatΣ φ) (x , b))
    s = e (x , b)

    γ : is-singleton (fiber (φ x) b)
    γ = equiv-to-singleton d s

Σ-is-subsingleton = sol
 where
  sol : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
      → is-subsingleton X
      → ((x : X) → is-subsingleton (A x))
      → is-subsingleton (Σ A)
  sol i j (x , _) (y , _) = to-subtype-＝ j (i x y)

×-is-singleton = sol
 where
  sol : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
      → is-singleton X
      → is-singleton Y
      → is-singleton (X × Y)
  sol (x , φ) (y , γ) = (x , y) , δ
   where
    δ : ∀ z → x , y ＝ z
    δ (x' , y' ) = to-×-＝ (φ x' , γ y')

×-is-subsingleton = sol
 where
  sol : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
      → is-subsingleton X → is-subsingleton Y → is-subsingleton (X × Y)
  sol i j = Σ-is-subsingleton i (λ _ → j)

×-is-subsingleton' = sol
 where
  sol : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
      → ((Y → is-subsingleton X) × (X → is-subsingleton Y))
      → is-subsingleton (X × Y)
  sol {𝓤} {𝓥} {X} {Y} (i , j) = k
   where
    k : is-subsingleton (X × Y)
    k (x , y) (x' , y') = to-×-＝ (i y x x' , j x y y')

×-is-subsingleton'-back = sol
 where
  sol : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
      → is-subsingleton (X × Y)
      → (Y → is-subsingleton X) × (X → is-subsingleton Y)
  sol {𝓤} {𝓥} {X} {Y} k = i , j
   where
    i : Y → is-subsingleton X
    i y x x' = ap pr₁ (k (x , y) (x' , y))

    j : X → is-subsingleton Y
    j x y y' = ap pr₂ (k (x , y) (x , y'))

ap₂ = sol
 where
  sol : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } (f : X → Y → Z) {x x' : X} {y y' : Y}
      → x ＝ x' → y ＝ y' → f x y ＝ f x' y'
  sol f (refl x) (refl y) = refl (f x y)

\end{code}
