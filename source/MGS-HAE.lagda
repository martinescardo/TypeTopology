Martin Escardo 1st May 2020.

This is ported from the Midlands Graduate School 2019 lecture notes

 https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html
 https://github.com/martinescardo/HoTT-UF-Agda-Lecture-Notes

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module MGS-HAE where

open import MGS-Equivalence-Induction public

is-hae : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
is-hae f = Σ g ꞉ (codomain f → domain f)
         , Σ η ꞉ g ∘ f ∼ id
         , Σ ε ꞉ f ∘ g ∼ id
         , ((x : domain f) → ap f (η x) ≡ ε (f x))

haes-are-invertible : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                    → is-hae f → invertible f

haes-are-invertible f (g , η , ε , τ) = g , η , ε

transport-ap-≃ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                 {x x' : X} (a : x' ≡ x) (b : f x' ≡ f x)
               → (transport (λ - → f - ≡ f x) a b ≡ refl (f x)) ≃ (ap f a ≡ b)

transport-ap-≃ f (refl x) b = γ
 where
  γ : (b ≡ refl (f x)) ≃ (refl (f x) ≡ b)
  γ = ⁻¹-≃ b (refl (f x))

haes-are-equivs : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                → is-hae f → is-equiv f

haes-are-equivs f (g , η , ε , τ) y = γ
 where
  c : (φ : fiber f y) → (g y , ε y) ≡ φ
  c (x , refl .(f x)) = q
   where
    p : transport (λ - → f - ≡ f x) (η x) (ε (f x)) ≡ refl (f x)
    p = ⌜ ≃-sym (transport-ap-≃ f (η x) (ε (f x))) ⌝ (τ x)

    q : (g (f x) , ε (f x)) ≡ (x , refl (f x))
    q = to-Σ-≡ (η x , p)

  γ : is-singleton (fiber f y)
  γ = (g y , ε y) , c

id-is-hae : (X : 𝓤 ̇ ) → is-hae (𝑖𝑑 X)
id-is-hae X = 𝑖𝑑 X , refl , refl , (λ x → refl (refl x))

ua-equivs-are-haes : is-univalent 𝓤
                   → {X Y : 𝓤 ̇ } (f : X → Y)
                   → is-equiv f → is-hae f

ua-equivs-are-haes ua {X} {Y} = 𝕁-equiv ua (λ X Y f → is-hae f) id-is-hae X Y

equivs-are-haes : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                → is-equiv f → is-hae f

equivs-are-haes {𝓤} {𝓥} {X} {Y} f i = (g , η , ε , τ)
 where
  g : Y → X
  g = inverse f i

  η : g ∘ f ∼ id
  η = inverses-are-retractions f i

  ε : f ∘ g ∼ id
  ε = inverses-are-sections f i

  τ : (x : X) → ap f (η x) ≡ ε (f x)
  τ x = γ
   where
    φ : fiber f (f x)
    φ = center (fiber f (f x)) (i (f x))

    by-definition-of-g : g (f x) ≡ fiber-point φ
    by-definition-of-g = refl _

    p : φ ≡ (x , refl (f x))
    p = centrality (fiber f (f x)) (i (f x)) (x , refl (f x))

    a : g (f x) ≡ x
    a = ap fiber-point p

    b : f (g (f x)) ≡ f x
    b = fiber-identification φ

    by-definition-of-η : η x ≡ a
    by-definition-of-η = refl _

    by-definition-of-ε : ε (f x) ≡ b
    by-definition-of-ε = refl _

    q = transport (λ - → f - ≡ f x)       a          b         ≡⟨ refl _ ⟩
        transport (λ - → f - ≡ f x)       (ap pr₁ p) (pr₂ φ)   ≡⟨ t ⟩
        transport (λ - → f (pr₁ -) ≡ f x) p          (pr₂ φ)   ≡⟨ apd pr₂ p ⟩
        refl (f x)                                             ∎
     where
      t = (transport-ap (λ - → f - ≡ f x) pr₁ p b)⁻¹

    γ : ap f (η x) ≡ ε (f x)
    γ = ⌜ transport-ap-≃ f a b ⌝ q

equivs-are-haes' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                 → is-equiv f → is-hae f

equivs-are-haes' f e = (inverse f e ,
                        inverses-are-retractions f e ,
                        inverses-are-sections f e ,
                        τ)
 where
  τ : ∀ x → ap f (inverses-are-retractions f e x) ≡ inverses-are-sections f e (f x)
  τ x = ⌜ transport-ap-≃ f (ap pr₁ p) (pr₂ φ) ⌝ q
   where
    φ : fiber f (f x)
    φ = pr₁ (e (f x))

    p : φ ≡ (x , refl (f x))
    p = pr₂ (e (f x)) (x , refl (f x))

    q : transport (λ - → f - ≡ f x) (ap pr₁ p) (pr₂ φ) ≡ refl (f x)
    q = (transport-ap (λ - → f - ≡ f x) pr₁ p ((pr₂ φ)))⁻¹ ∙ apd pr₂ p

equiv-invertible-hae-factorization : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                                   → equivs-are-invertible f
                                   ∼ haes-are-invertible f ∘ equivs-are-haes f

equiv-invertible-hae-factorization f e = refl (equivs-are-invertible f e)

half-adjoint-condition : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) (e : is-equiv f) (x : X)
                       → ap f (inverses-are-retractions f e x) ≡ inverses-are-sections f e (f x)

half-adjoint-condition f e = pr₂ (pr₂ (pr₂ (equivs-are-haes f e)))

Σ-change-of-variable : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (A : Y → 𝓦 ̇ ) (f : X → Y)
                     → is-equiv f → (Σ y ꞉ Y , A y) ≃ (Σ x ꞉ X , A (f x))

Σ-change-of-variable {𝓤} {𝓥} {𝓦} {X} {Y} A f i = γ
 where
  g = inverse f i
  η = inverses-are-retractions f i
  ε = inverses-are-sections f i
  τ = half-adjoint-condition f i

  φ : Σ A → Σ (A ∘ f)
  φ (y , a) = (g y , transport A ((ε y)⁻¹) a)

  ψ : Σ (A ∘ f) → Σ A
  ψ (x , a) = (f x , a)

  ψφ : (z : Σ A) → ψ (φ z) ≡ z
  ψφ (y , a) = p
   where
    p : (f (g y) , transport A ((ε y)⁻¹) a) ≡ (y , a)
    p = to-Σ-≡ (ε y , transport-is-retraction A (ε y) a)

  φψ : (t : Σ (A ∘ f)) → φ (ψ t) ≡ t
  φψ (x , a) = p
   where
    a' : A (f (g (f x)))
    a' = transport A ((ε (f x))⁻¹) a

    q = transport (A ∘ f) (η x)  a' ≡⟨ transport-ap A f (η x) a' ⟩
        transport A (ap f (η x)) a' ≡⟨ ap (λ - → transport A - a') (τ x) ⟩
        transport A (ε (f x))    a' ≡⟨ transport-is-retraction A (ε (f x)) a ⟩
        a                          ∎

    p : (g (f x) , transport A ((ε (f x))⁻¹) a) ≡ (x , a)
    p = to-Σ-≡ (η x , q)

  γ : Σ A ≃ Σ (A ∘ f)
  γ = invertibility-gives-≃ φ (ψ , ψφ , φψ)

~-naturality : {X : 𝓤 ̇ } {A : 𝓥 ̇ }
               (f g : X → A) (H : f ∼ g) {x y : X} {p : x ≡ y}
             → H x ∙ ap g p ≡ ap f p ∙ H y

~-naturality f g H {x} {_} {refl a} = refl-left ⁻¹

~-naturality' : {X : 𝓤 ̇ } {A : 𝓥 ̇ }
                (f g : X → A) (H : f ∼ g) {x y : X} {p : x ≡ y}
              → H x ∙ ap g p ∙ (H y)⁻¹ ≡ ap f p

~-naturality' f g H {x} {x} {refl x} = ⁻¹-right∙ (H x)

~-id-naturality : {X : 𝓤 ̇ }
                  (h : X → X) (η : h ∼ id) {x : X}
                → η (h x) ≡ ap h (η x)

~-id-naturality h η {x} =

   η (h x)                         ≡⟨ refl _ ⟩
   η (h x) ∙ refl (h x)            ≡⟨ i ⟩
   η (h x) ∙ (η x ∙ (η x)⁻¹)       ≡⟨ ii ⟩
   η (h x) ∙ η x ∙ (η x)⁻¹         ≡⟨ iii ⟩
   η (h x) ∙ ap id (η x) ∙ (η x)⁻¹ ≡⟨ iv ⟩
   ap h (η x)                      ∎

 where
  i   = ap (η(h x) ∙_) ((⁻¹-right∙ (η x))⁻¹)
  ii  = (∙assoc (η (h x)) (η x) (η x ⁻¹))⁻¹
  iii = ap (λ - → η (h x) ∙ - ∙ η x ⁻¹) ((ap-id (η x))⁻¹)
  iv  = ~-naturality' h id η {h x} {x} {η x}

invertibles-are-haes : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                     → invertible f → is-hae f

invertibles-are-haes f (g , η , ε) = g , η , ε' , τ
 where
  ε' = λ y → f (g y)         ≡⟨ (ε (f (g y)))⁻¹ ⟩
             f (g (f (g y))) ≡⟨ ap f (η (g y)) ⟩
             f (g y)         ≡⟨ ε y ⟩
             y               ∎

  module _ (x : domain f) where

   p = η (g (f x))       ≡⟨ ~-id-naturality (g ∘ f) η ⟩
       ap (g ∘ f) (η x)  ≡⟨ ap-∘ f g (η x) ⟩
       ap g (ap f (η x)) ∎

   q = ap f (η (g (f x))) ∙ ε (f x)          ≡⟨ by-p ⟩
       ap f (ap g (ap f (η x))) ∙ ε (f x)    ≡⟨ by-ap-∘ ⟩
       ap (f ∘ g) (ap f (η x))  ∙ ε (f x)    ≡⟨ by-~-naturality ⟩
       ε (f (g (f x))) ∙ ap id (ap f (η x))  ≡⟨ by-ap-id ⟩
       ε (f (g (f x))) ∙ ap f (η x)          ∎
    where
     by-p            = ap (λ - → ap f - ∙ ε (f x)) p
     by-ap-∘         = ap (_∙ ε (f x)) ((ap-∘ g f (ap f (η x)))⁻¹)
     by-~-naturality = (~-naturality (f ∘ g) id ε {f (g (f x))} {f x} {ap f (η x)})⁻¹
     by-ap-id        = ap (ε (f (g (f x))) ∙_) (ap-id (ap f (η x)))

   τ = ap f (η x)                                           ≡⟨ refl-left ⁻¹ ⟩
       refl (f (g (f x)))                     ∙ ap f (η x)  ≡⟨ by-⁻¹-left∙ ⟩
       (ε (f (g (f x))))⁻¹ ∙  ε (f (g (f x))) ∙ ap f (η x)  ≡⟨ by-∙assoc ⟩
       (ε (f (g (f x))))⁻¹ ∙ (ε (f (g (f x))) ∙ ap f (η x)) ≡⟨ by-q ⟩
       (ε (f (g (f x))))⁻¹ ∙ (ap f (η (g (f x))) ∙ ε (f x)) ≡⟨ refl _ ⟩
       ε' (f x)                                             ∎
    where
     by-⁻¹-left∙ = ap (_∙ ap f (η x)) ((⁻¹-left∙ (ε (f (g (f x)))))⁻¹)
     by-∙assoc   = ∙assoc ((ε (f (g (f x))))⁻¹) (ε (f (g (f x)))) (ap f (η x))
     by-q        = ap ((ε (f (g (f x))))⁻¹ ∙_) (q ⁻¹)

\end{code}
