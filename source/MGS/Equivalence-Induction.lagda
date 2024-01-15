Martin Escardo 1st May 2020.

This is ported from the Midlands Graduate School 2019 lecture notes

 https://www.cs.bham.ac.uk/~mhe/HoTT-UF.in-Agda-Lecture-Notes/HoTT-UF-Agda.html
 https://github.com/martinescardo/HoTT-UF.Agda-Lecture-Notes

\begin{code}

{-# OPTIONS --safe --without-K #-}

module MGS.Equivalence-Induction where

open import MGS.Univalence public
open import MGS.Solved-Exercises public

equiv-singleton-lemma : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } (x : X)
                        (f : (y : X) → x ＝ y → A y)
                      → ((y : X) → is-equiv (f y))
                      → is-singleton (Σ A)

equiv-singleton-lemma {𝓤} {𝓥} {X} {A} x f i = γ
 where
  e : (y : X) → (x ＝ y) ≃ A y
  e y = (f y , i y)

  d : singleton-type' x ≃ Σ A
  d = Σ-cong e

  abstract
   γ : is-singleton (Σ A)
   γ = equiv-to-singleton (≃-sym d) (singleton-types'-are-singletons X x)

singleton-equiv-lemma : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } (x : X)
                        (f : (y : X) → x ＝ y → A y)
                      → is-singleton (Σ A)
                      → (y : X) → is-equiv (f y)

singleton-equiv-lemma {𝓤} {𝓥} {X} {A} x f i = γ
 where
  g : singleton-type' x → Σ A
  g = NatΣ f

  e : is-equiv g
  e = maps-of-singletons-are-equivs g (singleton-types'-are-singletons X x) i

  abstract
   γ : (y : X) → is-equiv (f y)
   γ = NatΣ-equiv-gives-fiberwise-equiv f e

univalence⇒ : is-univalent 𝓤
            → (X : 𝓤 ̇ ) → is-singleton (Σ Y ꞉ 𝓤 ̇ , X ≃ Y)

univalence⇒ ua X = equiv-singleton-lemma X (Id→Eq X) (ua X)

⇒univalence : ((X : 𝓤 ̇ ) → is-singleton (Σ Y ꞉ 𝓤 ̇ , X ≃ Y))
            → is-univalent 𝓤

⇒univalence i X = singleton-equiv-lemma X (Id→Eq X) (i X)

univalence→ : is-univalent 𝓤
            → (X : 𝓤 ̇ ) → is-subsingleton (Σ Y ꞉ 𝓤 ̇ , X ≃ Y)

univalence→ ua X = singletons-are-subsingletons
                    (Σ (X ≃_)) (univalence⇒ ua X)

→univalence : ((X : 𝓤 ̇ ) → is-subsingleton (Σ Y ꞉ 𝓤 ̇ , X ≃ Y))
            → is-univalent 𝓤

→univalence i = ⇒univalence (λ X → pointed-subsingletons-are-singletons
                                    (Σ (X ≃_)) (X , id-≃ X) (i X))

𝔾-≃ : is-univalent 𝓤
    → (X : 𝓤 ̇ ) (A : (Σ Y ꞉ 𝓤 ̇ , X ≃ Y) → 𝓥 ̇ )
    → A (X , id-≃ X) → (Y : 𝓤 ̇ ) (e : X ≃ Y) → A (Y , e)

𝔾-≃ {𝓤} ua X A a Y e = transport A p a
 where
  t : Σ Y ꞉ 𝓤 ̇ , X ≃ Y
  t = (X , id-≃ X)

  p : t ＝ (Y , e)
  p = univalence→ {𝓤} ua X t (Y , e)

𝔾-≃-equation : (ua : is-univalent 𝓤)
             → (X : 𝓤 ̇ ) (A : (Σ Y ꞉ 𝓤 ̇ , X ≃ Y) → 𝓥 ̇ ) (a : A (X , id-≃ X))
             → 𝔾-≃ ua X A a X (id-≃ X) ＝ a

𝔾-≃-equation {𝓤} {𝓥} ua X A a =

  𝔾-≃ ua X A a X (id-≃ X) ＝⟨ refl _ ⟩
  transport A p a         ＝⟨ ap (λ - → transport A - a) q ⟩
  transport A (refl t) a  ＝⟨ refl _ ⟩
  a                       ∎

 where
  t : Σ Y ꞉ 𝓤 ̇ , X ≃ Y
  t = (X , id-≃ X)

  p : t ＝ t
  p = univalence→ {𝓤} ua X t t

  q : p ＝ refl t
  q = subsingletons-are-sets (Σ Y ꞉ 𝓤 ̇ , X ≃ Y)
       (univalence→ {𝓤} ua X) t t p (refl t)

ℍ-≃ : is-univalent 𝓤
    → (X : 𝓤 ̇ ) (A : (Y : 𝓤 ̇ ) → X ≃ Y → 𝓥 ̇ )
    → A X (id-≃ X) → (Y : 𝓤 ̇ ) (e : X ≃ Y) → A Y e

ℍ-≃ ua X A = 𝔾-≃ ua X (Σ-induction A)

ℍ-≃-equation : (ua : is-univalent 𝓤)
             → (X : 𝓤 ̇ ) (A : (Y : 𝓤 ̇ ) → X ≃ Y → 𝓥 ̇ ) (a : A X  (id-≃ X))
             → ℍ-≃ ua X A a X (id-≃ X) ＝ a

ℍ-≃-equation ua X A = 𝔾-≃-equation ua X (Σ-induction A)

𝕁-≃ : is-univalent 𝓤
    → (A : (X Y : 𝓤 ̇ ) → X ≃ Y → 𝓥 ̇ )
    → ((X : 𝓤 ̇ ) → A X X (id-≃ X))
    → (X Y : 𝓤 ̇ ) (e : X ≃ Y) → A X Y e

𝕁-≃ ua A φ X = ℍ-≃ ua X (A X) (φ X)

𝕁-≃-equation : (ua : is-univalent 𝓤)
             → (A : (X Y : 𝓤 ̇ ) → X ≃ Y → 𝓥 ̇ )
             → (φ : (X : 𝓤 ̇ ) → A X X (id-≃ X))
             → (X : 𝓤 ̇ ) → 𝕁-≃ ua A φ X X (id-≃ X) ＝ φ X

𝕁-≃-equation ua A φ X = ℍ-≃-equation ua X (A X) (φ X)

ℍ-equiv : is-univalent 𝓤
        → (X : 𝓤 ̇ ) (A : (Y : 𝓤 ̇ ) → (X → Y) → 𝓥 ̇ )
        → A X (𝑖𝑑 X) → (Y : 𝓤 ̇ ) (f : X → Y) → is-equiv f → A Y f

ℍ-equiv {𝓤} {𝓥} ua X A a Y f i = γ (f , i)
 where
  B : (Y : 𝓤 ̇ ) → X ≃ Y → 𝓥 ̇
  B Y (f , i) = A Y f

  b : B X (id-≃ X)
  b = a

  γ : (e : X ≃ Y) → B Y e
  γ = ℍ-≃ ua X B b Y

𝕁-equiv : is-univalent 𝓤
        → (A : (X Y : 𝓤 ̇ ) → (X → Y) → 𝓥 ̇ )
        → ((X : 𝓤 ̇ ) → A X X (𝑖𝑑 X))
        → (X Y : 𝓤 ̇ ) (f : X → Y) → is-equiv f → A X Y f

𝕁-equiv ua A φ X = ℍ-equiv ua X (A X) (φ X)

𝕁-invertible : is-univalent 𝓤
             → (A : (X Y : 𝓤 ̇ ) → (X → Y) → 𝓥 ̇ )
             → ((X : 𝓤 ̇ ) → A X X (𝑖𝑑 X))
             → (X Y : 𝓤 ̇ ) (f : X → Y) → invertible f → A X Y f

𝕁-invertible ua A φ X Y f i = 𝕁-equiv ua A φ X Y f (invertibles-are-equivs f i)

automatic-equiv-functoriality :

      (F : 𝓤 ̇ → 𝓤 ̇ )
      (𝓕 : {X Y : 𝓤 ̇ }  → (X → Y) → F X → F Y)
      (𝓕-id : {X : 𝓤 ̇ } → 𝓕 (𝑖𝑑 X) ＝ 𝑖𝑑 (F X))
      {X Y Z : 𝓤 ̇ }
      (f : X → Y)
      (g : Y → Z)

    → is-univalent 𝓤 → is-equiv f + is-equiv g → 𝓕 (g ∘ f) ＝ 𝓕 g ∘ 𝓕 f

automatic-equiv-functoriality {𝓤} F 𝓕 𝓕-id {X} {Y} {Z} f g ua = γ
  where
   γ :  is-equiv f + is-equiv g → 𝓕 (g ∘ f) ＝ 𝓕 g ∘ 𝓕 f
   γ (inl i) = ℍ-equiv ua X A a Y f i g
    where
     A : (Y : 𝓤 ̇ ) → (X → Y) → 𝓤 ̇
     A Y f = (g : Y → Z) → 𝓕 (g ∘ f) ＝ 𝓕 g ∘ 𝓕 f

     a : (g : X → Z) → 𝓕 g ＝ 𝓕 g ∘ 𝓕 id
     a g = ap (𝓕 g ∘_) (𝓕-id ⁻¹)

   γ (inr j) = ℍ-equiv ua Y B b Z g j f
    where
     B : (Z : 𝓤 ̇ ) → (Y → Z) → 𝓤 ̇
     B Z g = (f : X → Y) → 𝓕 (g ∘ f) ＝ 𝓕 g ∘ 𝓕 f

     b : (f : X → Y) → 𝓕 f ＝ 𝓕 (𝑖𝑑 Y) ∘ 𝓕 f
     b f = ap (_∘ 𝓕 f) (𝓕-id ⁻¹)

Σ-change-of-variable' : is-univalent 𝓤
                      → {X : 𝓤 ̇ } {Y : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (f : X → Y)
                      → (i : is-equiv f)
                      → (Σ x ꞉ X , A x) ＝ (Σ y ꞉ Y , A (inverse f i y))

Σ-change-of-variable' {𝓤} {𝓥} ua {X} {Y} A f i = ℍ-≃ ua X B b Y (f , i)
 where
   B : (Y : 𝓤 ̇ ) → X ≃ Y →  (𝓤 ⊔ 𝓥)⁺ ̇
   B Y (f , i) = Σ A ＝ (Σ (A ∘ inverse f i))

   b : B X (id-≃ X)
   b = refl (Σ A)

Σ-change-of-variable'' : is-univalent 𝓤
                       → {X : 𝓤 ̇ } {Y : 𝓤 ̇ } (A : Y → 𝓥 ̇ ) (f : X → Y)
                       → is-equiv f
                       → (Σ y ꞉ Y , A y) ＝ (Σ x ꞉ X , A (f x))

Σ-change-of-variable'' ua A f i = Σ-change-of-variable' ua A
                                  (inverse f i)
                                  (inverses-are-equivs f i)

transport-map-along-＝ : {X Y Z : 𝓤 ̇ }
                        (p : X ＝ Y) (g : X → Z)
                      → transport (λ - → - → Z) p g
                      ＝ g ∘ Id→fun (p ⁻¹)

transport-map-along-＝ (refl X) = refl

transport-map-along-≃ : (ua : is-univalent 𝓤) {X Y Z : 𝓤 ̇ }
                        (e : X ≃ Y) (g : X → Z)
                      → transport (λ - → - → Z) (Eq→Id ua X Y e) g
                      ＝ g ∘ ⌜ ≃-sym e ⌝

transport-map-along-≃ {𝓤} ua {X} {Y} {Z} = 𝕁-≃ ua A a X Y
 where
  A : (X Y : 𝓤 ̇ ) → X ≃ Y → 𝓤 ̇
  A X Y e = (g : X → Z) → transport (λ - → - → Z) (Eq→Id ua X Y e) g
                        ＝ g ∘ ⌜ ≃-sym e ⌝
  a : (X : 𝓤 ̇ ) → A X X (id-≃ X)
  a X g = transport (λ - → - → Z) (Eq→Id ua X X (id-≃ X)) g ＝⟨ q ⟩
          transport (λ - → - → Z) (refl X) g                ＝⟨ refl _ ⟩
          g                                                 ∎
    where
     p : Eq→Id ua X X (id-≃ X) ＝ refl X
     p = inverses-are-retractions (Id→Eq X X) (ua X X) (refl X)

     q = ap (λ - → transport (λ - → - → Z) - g) p

\end{code}
