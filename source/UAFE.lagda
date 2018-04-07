Cory Knapp and Martin Escardo, Dec 2014
Adapted from https://github.com/cmknapp/analysis

A generalization of the fact that univalence implies funext.

We abstract from Voevodsky's original proof as presented by Gambino, Kapulkin and
Lumsdaine in http://www.math.uwo.ca/faculty/kapulkin/notes/ua_implies_fe.pdf.

\begin{code}

{-# OPTIONS --without-K --exact-split #-}

module UAFE where

open import UF

\end{code}

The following maps are considered in the original proof that
univalence implies function extensionality by Voevodsky:

\begin{code}

Δ : ∀ {U} → U ̇ → U ̇
Δ X = Σ \(x : X) → Σ \(y : X) → x ≡ y

δ : ∀ {U} {X : U ̇} → X → Δ X
δ x = (x , x , refl)

π₁ : ∀ {U} {X : U ̇} → Δ X → X
π₁ (x , _ , _) = x

π₂ : ∀ {U} {X : U ̇} → Δ X → X
π₂ (_ , y , _) = y

δ-isEquiv : ∀ {U} {X : U ̇} → isEquiv (δ {U} {X})
δ-isEquiv {U} {X} = (π₁ , η) , (π₁ , ε)
 where
  η : (d : Δ X) → δ (π₁ d) ≡ d
  η (x , x , refl) = refl
  ε : (x : X) → π₁ (δ x) ≡ x
  ε x = refl

πδ : ∀ {U} (X : U ̇) → π₁ ∘ δ ≡ π₂ ∘ δ
πδ {U} X = refl {U} {X → X}

path-to-fun : ∀ {U} {X Y : U ̇} → X ≡ Y → X → Y
path-to-fun = transport id

back-transport-is-pre-comp : ∀ {U} {X X' Y : U ̇} (p : X ≡ X') (g : X' → Y)
                          → back-transport (λ Z → Z → Y) p g ≡ g ∘ path-to-fun p
back-transport-is-pre-comp refl g = refl

\end{code}

We generalize "isEquiv" to an arbitrary "isE" in the following
development, and then assume the identity and δ satisfy this, and that
things that satisfy this are closed under homotopy. Then if univalence
holds for this abstract notion of equivalence, function extensionlity
follows.

At the end we apply this to equivalences, to get that univalence
implies function extensionality.

\begin{code}

module AbstractUAFE
  (isE : ∀ {U V} {X : U ̇} {Y : V ̇} → (X → Y) → U ⊔ V ̇)
  (I : ∀ {U} {X : U ̇} → isE (id {U} {X}))
  (D : ∀ {U} {X : U ̇} → isE (δ {U} {X}))
  (H : ∀ {U V} {X : U ̇} {Y : V ̇} {f g : X → Y} → isE f → f ∼ g → isE g)
 where
  
 _⋍_ : ∀ {U V} → U ̇ → V ̇ → U ⊔ V ̇
 X ⋍ Y = Σ \(f : X → Y) → isE f

 transport-isE : ∀ {U V} {X : U ̇} {A : X → V ̇} {x y : X} (p : x ≡ y) → isE (transport A p)
 transport-isE refl = I

 back-transport-isE : ∀ {U V} {X : U ̇} {A : X → V ̇} {x y : X} (p : x ≡ y) → isE (back-transport A p)
 back-transport-isE p = transport-isE (p ⁻¹)

 idtoE : ∀ {U} (X Y : U ̇) → X ≡ Y → X ⋍ Y
 idtoE X Y p = (path-to-fun p , transport-isE p)

 module AbstractUAFE2 (U : Universe)
                      (Etoid : (X Y : U ̇) → X ⋍ Y → X ≡ Y)
                      (wua : (X Y : U ̇) → (Etoid X Y) isSectionOf (idtoE X Y))
  where

  Γ : {X Y : U ̇} (e : X ⋍ Y) → pr₁ (idtoE X Y (Etoid X Y e)) ≡ pr₁ e 
  Γ {X} {Y} e = ap pr₁ (wua X Y e) 

  E-induction : ∀ {V} {X Y : U ̇} (A : {X Y : U ̇} → (X → Y) → V ̇)
              → ({X : U ̇} → (A (id {U} {X})))
              → (f : X → Y) → isE f → A f
  E-induction {V} {X} {Y} A g f e = transport A η Φ
   where
    φ : {X Y : U ̇} (p : X ≡ Y) → A (path-to-fun p)
    φ refl = g
    p : X ≡ Y
    p = Etoid X Y (f , e)
    Φ : A (path-to-fun p)
    Φ = φ p
    η : path-to-fun p ≡ f
    η = Γ (f , e)

  isE-lc : {X Y : U ̇} (f : X → Y) → isE f → left-cancellable f
  isE-lc = E-induction left-cancellable (λ {X} {x} {x'} (p : id x ≡ id x') → p)

  back-transport-is-pre-comp' : {X X' Y : U ̇} (e : X ⋍ X') (g : X' → Y)
                              → back-transport (λ Z → Z → Y) (Etoid X X' e) g ≡ g ∘ pr₁ e 
  back-transport-is-pre-comp' {X} {X'} e g = back-transport-is-pre-comp (Etoid X X' e) g ∙ η
   where
    f = pr₁ e
    η : g ∘ path-to-fun (Etoid X X' e) ≡ g ∘ f
    η = ap (λ h → g ∘ h) (Γ e) 

  preComp-isE : {X X' Y : U ̇} (e : X ⋍ X') → isE (λ (g : X' → Y) → g ∘ (pr₁ e))
  preComp-isE {X} {X'} e = H (back-transport-isE (Etoid X X' e)) (back-transport-is-pre-comp' e)

  preCompδ-isE : {X Y : U ̇} → isE (λ(g : Δ X → Y) → g ∘ δ)
  preCompδ-isE = preComp-isE (δ , D)

  π₁-equals-π₂ : {X : U ̇} → π₁ ≡ π₂
  π₁-equals-π₂ {X} = isE-lc (λ(g : Δ X → X) → g ∘ δ) preCompδ-isE (πδ X)

  fe : ∀ {V} {X : V ̇} {Y : U ̇} (f₁ f₂ : X → Y) → f₁ ∼ f₂ → f₁ ≡ f₂
  fe {V} {X} {Y} f₁ f₂ h = f₁            ≡⟨ refl ⟩
                           (λ x → f₁ x)  ≡⟨ refl ⟩ 
                           π₁ ∘ f        ≡⟨ ap (λ(π : Δ Y → Y) → π ∘ f) π₁-equals-π₂ ⟩
                           π₂ ∘ f        ≡⟨ refl ⟩
                           (λ x → f₂ x) ≡⟨ refl ⟩ 
                           f₂     ∎
   where
    f : X → Δ Y
    f x = (f₁ x , f₂ x , h x)

\end{code}

We specialize this to get that univalence implies function extensionality:

\begin{code}

UAFE : ∀ {U} → isUnivalent U → ∀ {V} {X : V ̇} {Y : U ̇} (f g : X → Y) → f ∼ g → f ≡ g
UAFE {U} ua {V} {X} {Y} = fe 
 where
  open AbstractUAFE isEquiv
                    (λ {U} {X} → ((id , idp) , (id , idp)))
                    δ-isEquiv
                    (λ ise h → equiv-closed-under-∼ _ _ ise (λ x → ( h x )⁻¹))

  h : (X Y : U ̇) → idtoE X Y ∼ idtoeq X Y
  h X X refl = refl

  f : (X Y : U ̇) → idtoE X Y ∘ eqtoid ua X Y ∼ id
  f X Y e = h X Y (eqtoid ua X Y e) ∙ idtoeq-eqtoid {U} ua X Y e

  open AbstractUAFE2 U (eqtoid ua) f 

\end{code}
