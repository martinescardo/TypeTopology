\begin{code}

{-# OPTIONS --without-K --exact-split #-}

module UF-Equiv where

open import UF-Base
open import UF-Subsingletons
open import UF-Retracts
open import UF-Subsingletons-Retracts

\end{code}

We take Joyal's version of the notion of equivalence as the primary
one because it is more symmetrical.

\begin{code}

isEquiv : ∀ {U V} {X : U ̇} {Y : V ̇} → (X → Y) → U ⊔ V ̇
isEquiv f = hasSection f × hasRetraction f 

_≃_ : ∀ {U V} → U ̇ → V ̇ → U ⊔ V ̇
X ≃ Y = Σ \(f : X → Y) → isEquiv f

ideq : ∀ {U} (X : U ̇) → X ≃ X
ideq X = id , ((id , idp) , (id , idp))

≃-trans : ∀ {U V W} {X : U ̇} {Y : V ̇} {Z : W ̇} → X ≃ Y → Y ≃ Z → X ≃ Z
≃-trans {U} {V} {W} {X} {Y} {Z} (f , (g , fg) , (h , hf)) (f' , (g' , fg') , (h' , hf'))  =
  f' ∘ f , (g ∘ g' , fg'') , (h ∘ h' , hf'')
 where
    fg'' : (z : Z) → f' (f (g (g' z))) ≡ z
    fg'' z =  ap f' (fg (g' z)) ∙ fg' z
    hf'' : (x : X) → h(h'(f'(f x))) ≡ x
    hf'' x = ap h (hf' (f x)) ∙ hf x

_≃⟨_⟩_ : ∀ {U V W} (X : U ̇) {Y : V ̇} {Z : W ̇} → X ≃ Y → Y ≃ Z → X ≃ Z
_ ≃⟨ d ⟩ e = ≃-trans d e

_■ : ∀ {U} (X : U ̇) → X ≃ X
_■ = ideq

Eq : ∀ {U V} → U ̇ → V ̇ → U ⊔ V ̇
Eq = _≃_

eqtofun : ∀ {U V} (X : U ̇) (Y : V ̇) → X ≃ Y → X → Y
eqtofun X Y (f , _) = f

idtoeq : ∀ {U} (X Y : U ̇) → X ≡ Y → X ≃ Y
idtoeq X Y p = transport (Eq X) p (ideq X)

idtoeq-traditional : ∀ {U} (X Y : U ̇) → X ≡ Y → X ≃ Y
idtoeq-traditional X _ refl = ideq X

\end{code}

We would have a definitional equality if we had defined the traditional
one using J(based), but because of the idiosyncracies of Agda, we
don't with the current definition:

\begin{code}

eqtoeq-agreement : ∀ {U} (X Y : U ̇) (p : X ≡ Y)
                 → idtoeq X Y p ≡ idtoeq-traditional X Y p
eqtoeq-agreement {U} X _ refl = refl

idtofun : ∀ {U} (X Y : U ̇) → X ≡ Y → X → Y
idtofun X Y p = eqtofun X Y (idtoeq X Y p)

equiv-closed-under-∼ : ∀ {U V} {X : U ̇} {Y : V ̇} (f g : X → Y) → isEquiv f →  g ∼ f  → isEquiv g
equiv-closed-under-∼ {U} {V} {X} {Y} f g (hass , hasr) h = (hasSection-closed-under-∼ f g hass h) ,
                                                            (hasRetraction-closed-under-∼ f g hasr h)

equiv-closed-under-∼' : ∀ {U V} {X : U ̇} {Y : V ̇} {f g : X → Y} → isEquiv f → f ∼ g → isEquiv g
equiv-closed-under-∼' ise h = equiv-closed-under-∼ _ _ ise (λ x → (h x)⁻¹)
  
qinv : {U V : Universe} {X : U ̇} {Y : V ̇} → (X → Y) → U ⊔ V ̇
qinv f = Σ \g → (g ∘ f ∼ id) × (f ∘ g ∼ id)

isEquiv-qinv : {U V : Universe} {X : U ̇} {Y : V ̇} (f : X → Y) → isEquiv f → qinv f
isEquiv-qinv {U} {V} {X} {Y} f ((s , fs) , (r , rf)) = s , (sf , fs)
 where
  sf : (x : X) → s(f x) ≡ x
  sf x = s(f x)       ≡⟨ (rf (s (f x)))⁻¹ ⟩
         r(f(s(f x))) ≡⟨ ap r (fs (f x)) ⟩
         r(f x)       ≡⟨ rf x ⟩
         x            ∎

qinv-isEquiv : {U V : Universe} {X : U ̇} {Y : V ̇} (f : X → Y) → qinv f → isEquiv f
qinv-isEquiv f (g , (gf , fg)) = (g , fg) , (g , gf)

≃-sym : ∀ {U V} {X : U ̇} {Y : V ̇}  → X ≃ Y → Y ≃ X 
≃-sym {U} {V} {X} {Y} (f , e) = (g , d)
 where
  g : Y → X
  g = pr₁(isEquiv-qinv f e)
  q : qinv g
  q = f , pr₂(pr₂(isEquiv-qinv f e)) , pr₁(pr₂(isEquiv-qinv f e))
  d : isEquiv g
  d = qinv-isEquiv g q

equiv-retract-l : ∀ {U V} {X : U ̇} {Y : V ̇} → X ≃ Y → retract X of Y 
equiv-retract-l (f , (g , fg) , (h , hf)) = h , f , hf

equiv-retract-r : ∀ {U V} {X : U ̇} {Y : V ̇} → X ≃ Y → retract Y of X
equiv-retract-r (f , (g , fg) , (h , hf)) = f , g , fg

\end{code}

Equivalence of transports.

\begin{code}

transport-isEquiv : ∀ {U V} {X : U ̇} {A : X → V ̇} {x y : X} (p : x ≡ y) → isEquiv (transport A p)
transport-isEquiv refl =  pr₂ (ideq _)

back-transport-isEquiv : ∀ {U V} {X : U ̇} {A : X → V ̇} {x y : X} (p : x ≡ y) → isEquiv (back-transport A p)
back-transport-isEquiv p = transport-isEquiv (p ⁻¹)

\end{code}

\begin{code}

fiber : ∀ {U V} {X : U ̇} {Y : V ̇} (f : X → Y) → Y → U ⊔ V ̇
fiber f y = Σ \x → f x ≡ y

isVoevodskyEquiv : ∀ {U V} {X : U ̇} {Y : V ̇} → (X → Y) → U ⊔ V ̇
isVoevodskyEquiv f = ∀ y → isSingleton (fiber f y)

isVoevodskyEquiv-isEquiv : ∀ {U V} {X : U ̇} {Y : V ̇} (f : X → Y)
                         → isVoevodskyEquiv f → isEquiv f
isVoevodskyEquiv-isEquiv {U} {V} {X} {Y} f φ = (g , fg) , (g , gf)
 where
  φ' : (y : Y) → Σ \(c : Σ \(x : X) → f x ≡ y) → (σ : Σ \(x : X) → f x ≡ y) → c ≡ σ
  φ' = φ
  c : (y : Y) → Σ \(x : X) → f x ≡ y
  c y = pr₁(φ y)
  d : (y : Y) → (σ : Σ \(x : X) → f x ≡ y) → c y ≡ σ
  d y = pr₂(φ y)
  g : Y → X
  g y = pr₁(c y)
  fg : (y : Y) → f (g y) ≡ y
  fg y = pr₂(c y)
  e : (x : X) → g(f x) , fg (f x) ≡ x , refl
  e x = d (f x) (x , refl)
  gf : (x : X) → g (f x) ≡ x
  gf x = ap pr₁ (e x)

fiber' : ∀ {U V} {X : U ̇} {Y : V ̇} (f : X → Y) → Y → U ⊔ V ̇
fiber' f y = Σ \x → y ≡ f x

fiber-lemma : ∀ {U V} {X : U ̇} {Y : V ̇} (f : X → Y) (y : Y) → fiber f y ≃ fiber' f y
fiber-lemma f y = g , (h , gh) , (h , hg)
 where
  g : fiber f y → fiber' f y
  g (x , p) = x , (p ⁻¹)
  h : fiber' f y → fiber f y
  h (x , p) = x , (p ⁻¹)
  hg : ∀ σ → h(g σ) ≡ σ
  hg (x , refl) = refl
  gh : ∀ τ → g(h τ) ≡ τ
  gh (x , refl) = refl

equiv-can-assume-pointed-codomain : ∀ {U V} {X : U ̇} {Y : V ̇} (f : X → Y)
                                 → (Y → isVoevodskyEquiv f) → isVoevodskyEquiv f
equiv-can-assume-pointed-codomain f φ y = φ y y

maps-to-𝟘-are-equivs : ∀ {U} {X : U ̇} (f : X → 𝟘)
                     → isVoevodskyEquiv f
maps-to-𝟘-are-equivs f = equiv-can-assume-pointed-codomain f 𝟘-elim

isHAE : ∀ {U} {V} {X : U ̇} {Y : V ̇} → (X → Y) → U ⊔ V ̇
isHAE {U} {V} {X} {Y} f = Σ \(g : Y → X) → Σ \(η : g ∘ f ∼ id) → Σ \(ε : f ∘ g ∼ id) → (x : X) → ap f (η x) ≡ ε (f x)

id-homotopies-are-natural : ∀ {U} {X : U ̇} (h : X → X) (η : h ∼ id) {x : X}
                         → η (h x) ≡ ap h (η x)
id-homotopies-are-natural h η {x} =
   η (h x)                          ≡⟨ refl ⟩
   η (h x) ∙ idp (h x)              ≡⟨ ap (λ p → η(h x) ∙ p) ((trans-sym' (η x))⁻¹) ⟩
   η (h x) ∙ (η x ∙ (η x)⁻¹)        ≡⟨ (assoc (η (h x)) (η x) (η x ⁻¹))⁻¹ ⟩
   η (h x) ∙ η x ∙ (η x)⁻¹          ≡⟨ ap (λ q → η (h x) ∙ q ∙ (η x)⁻¹) ((ap-id-is-id (η x))) ⟩
   η (h x) ∙ ap id (η x) ∙ (η x)⁻¹  ≡⟨ homotopies-are-natural' h id η {h x} {x} {η x} ⟩
   ap h (η x)                       ∎

qinv-isHAE : ∀ {U} {V} {X : U ̇} {Y : V ̇} (f : X → Y) → qinv f → isHAE f
qinv-isHAE {U} {V} {X} {Y} f (g , (η , ε)) = g , η , ε' , τ
 where
  ε' : f ∘ g ∼ id
  ε' y = f (g y)         ≡⟨ (ε (f (g y)))⁻¹ ⟩
         f (g (f (g y))) ≡⟨ ap f (η (g y)) ⟩
         f (g y)         ≡⟨ ε y ⟩
         y               ∎

  a : (x : X) → η (g (f x)) ≡ ap g (ap f (η x))
  a x = η (g (f x))       ≡⟨ id-homotopies-are-natural (g ∘ f) η  ⟩
        ap (g ∘ f) (η x)  ≡⟨ (ap-ap f g (η x))⁻¹ ⟩
        ap g (ap f (η x)) ∎
        
  b : (x : X) → ap f (η (g (f x))) ∙ ε (f x) ≡ ε (f (g (f x))) ∙ ap f (η x)
  b x = ap f (η (g (f x))) ∙ ε (f x)         ≡⟨ ap (λ p → p ∙ ε (f x)) (ap (ap f) (a x)) ⟩
        ap f (ap g (ap f (η x))) ∙ ε (f x)   ≡⟨ ap (λ p → p ∙ ε (f x)) (ap-ap g f (ap f (η x))) ⟩
        ap (f ∘ g) (ap f (η x)) ∙ ε (f x)    ≡⟨ (homotopies-are-natural (f ∘ g) id ε {f (g (f x))} {f x} {ap f (η x)})⁻¹ ⟩
        ε (f (g (f x))) ∙ ap id (ap f (η x)) ≡⟨ ap (λ p → ε (f (g (f x))) ∙ p) (ap-ap f id (η x)) ⟩
        ε (f (g (f x))) ∙ ap f (η x)         ∎
        
  τ : (x : X) → ap f (η x) ≡ ε' (f x)
  τ x = ap f (η x)                                           ≡⟨ idp-left-neutral ⁻¹ ⟩
        idp (f (g (f x))) ∙ ap f (η x)                       ≡⟨ ap (λ p → p ∙ ap f (η x)) ((trans-sym (ε (f (g (f x)))))⁻¹) ⟩
        (ε (f (g (f x))))⁻¹ ∙ ε (f (g (f x))) ∙ ap f (η x)   ≡⟨ assoc ((ε (f (g (f x))))⁻¹) (ε (f (g (f x)))) (ap f (η x)) ⟩
        (ε (f (g (f x))))⁻¹ ∙ (ε (f (g (f x))) ∙ ap f (η x)) ≡⟨ ap (λ p → (ε (f (g (f x))))⁻¹ ∙ p) (b x)⁻¹ ⟩        
        (ε (f (g (f x))))⁻¹ ∙ (ap f (η (g (f x))) ∙ ε (f x)) ≡⟨ refl ⟩
        ε' (f x)                                             ∎

\end{code}

The following could be defined by combining functions we already have,
but a proof by path induction is direct:

\begin{code}

paths-in-fibers : ∀ {U} {V} {X : U ̇} {Y : V ̇} (f : X → Y)
                  (y : Y) (x x' : X) (p : f x ≡ y) (p' : f x' ≡ y)
               → (Σ \(γ : x ≡ x') → ap f γ ∙ p' ≡ p) → (x , p) ≡ (x' , p')
paths-in-fibers f .(f x) x .x refl p' (refl , r) = g
 where
  g : x , refl ≡ x , p'
  g = ap (λ p → (x , p)) (r ⁻¹ ∙ idp-left-neutral)

\end{code}

Using this we see that half adjoint equivalence have contractible fibers:

\begin{code}

isHAE-isVoevodsky : ∀ {U} {V} {X : U ̇} {Y : V ̇} (f : X → Y)
                  → isHAE f → isVoevodskyEquiv f
isHAE-isVoevodsky {U} {V} {X} f (g , η , ε , τ) y = (c , λ σ → α (pr₁ σ) (pr₂ σ))
 where
  c : fiber f y
  c = (g y , ε y)
  
  α : (x : X) (p : f x ≡ y) → c ≡ (x , p)
  α x p = φ
   where
    γ : g y ≡ x
    γ = (ap g p)⁻¹ ∙ η x
    q : ap f γ ∙ p ≡ ε y
    q = ap f γ ∙ p                          ≡⟨ refl ⟩
        ap f ((ap g p)⁻¹ ∙ η x) ∙ p         ≡⟨ ap (λ r → r ∙ p) (ap-comp f ((ap g p)⁻¹) (η x)) ⟩
        ap f ((ap g p)⁻¹) ∙ ap f (η x) ∙ p  ≡⟨ ap (λ r → ap f r ∙ ap f (η x) ∙ p) (ap-sym g p) ⟩
        ap f (ap g (p ⁻¹)) ∙ ap f (η x) ∙ p ≡⟨ ap (λ r → ap f (ap g (p ⁻¹)) ∙ r ∙ p) (τ x) ⟩
        ap f (ap g (p ⁻¹)) ∙ ε (f x) ∙ p    ≡⟨ ap (λ r → r ∙ ε (f x) ∙ p) (ap-ap g f (p ⁻¹)) ⟩
        ap (f ∘ g) (p ⁻¹) ∙ ε (f x) ∙ p     ≡⟨ ap (λ r → r ∙ p) (homotopies-are-natural (f ∘ g) id ε {y} {f x} {p ⁻¹})⁻¹ ⟩
        ε y ∙ ap id (p ⁻¹) ∙ p              ≡⟨ ap (λ r → ε y ∙ r ∙ p) (ap-id-is-id (p ⁻¹))⁻¹ ⟩
        ε y ∙ p ⁻¹ ∙ p                      ≡⟨ assoc (ε y) (p ⁻¹) p ⟩
        ε y ∙ (p ⁻¹ ∙ p)                    ≡⟨ ap (λ r → ε y ∙ r) (trans-sym p) ⟩
        ε y ∙ refl ≡⟨ refl ⟩
        ε y ∎

    φ : g y , ε y ≡ x , p
    φ = paths-in-fibers f y (g y) x (ε y) p (γ , q)

\end{code}

Here are some corollaries:

\begin{code}

qinv-isVoevodsky : ∀ {U} {V} {X : U ̇} {Y : V ̇} (f : X → Y)
                 → qinv f → isVoevodskyEquiv f
qinv-isVoevodsky f q = isHAE-isVoevodsky f (qinv-isHAE f q)

isEquiv-isVoevodskyEquiv : ∀ {U V} {X : U ̇} {Y : V ̇} (f : X → Y)
                         → isEquiv f → isVoevodskyEquiv f
isEquiv-isVoevodskyEquiv f ie = qinv-isVoevodsky f (isEquiv-qinv f ie)

\end{code}

The following again could be define by combining functions we already have:

\begin{code}

from-paths-in-fibers : ∀ {U} {V} {X : U ̇} {Y : V ̇} (f : X → Y)
                      (y : Y) (x x' : X) (p : f x ≡ y) (p' : f x' ≡ y)
                    → (x , p) ≡ (x' , p') → Σ \(γ : x ≡ x') → ap f γ ∙ p' ≡ p
from-paths-in-fibers f .(f x) x .x refl .refl refl = refl , refl

η-pif : ∀ {U} {V} {X : U ̇} {Y : V ̇} (f : X → Y)
        (y : Y) (x x' : X) (p : f x ≡ y) (p' : f x' ≡ y)
        (σ : Σ \(γ : x ≡ x') → ap f γ ∙ p' ≡ p)
      → from-paths-in-fibers f y x x' p p' (paths-in-fibers f y x x' p p' σ) ≡ σ
η-pif f .(f x) x .x _ refl (refl , refl) = refl

\end{code}

Then the following follows from natural-section-has-retraction, but
also has a direct proof by path induction:

\begin{code}
ε-pif : ∀ {U} {V} {X : U ̇} {Y : V ̇} (f : X → Y)
        (y : Y) (x x' : X) (p : f x ≡ y) (p' : f x' ≡ y)
        (q : (x , p) ≡ (x' , p'))
      → paths-in-fibers f y x x' p p' (from-paths-in-fibers f y x x' p p' q) ≡ q
ε-pif f .(f x) x .x refl .refl refl = refl

\end{code}

\begin{code}

pr₁-equivalence : ∀ {U V} (X : U ̇) (Y : X → V ̇)
               → ((x : X) → isSingleton (Y x))
               → isEquiv (pr₁ {U} {V} {X} {Y})
pr₁-equivalence {U} {V} X Y iss = (g , prg) , (g , gpr)
 where
  g : X → Σ Y
  g x = x , pr₁(iss x)
  prg : (x : X) → pr₁ (g x) ≡ x
  prg x = refl
  gpr : (σ : Σ Y) → g(pr₁ σ) ≡ σ
  gpr (x , a) = to-Σ-≡'' (prg x , isSingleton-isProp (iss x) _ _)

pr₁-vequivalence : ∀ {U V} (X : U ̇) (Y : X → V ̇)
                → ((x : X) → isSingleton (Y x))
                → isVoevodskyEquiv (pr₁ {U} {V} {X} {Y})
pr₁-vequivalence {U} {V} X Y iss x = g
 where
  c : fiber pr₁ x
  c = (x , pr₁ (iss x)) , refl
  p : (y : Y x) → pr₁ (iss x) ≡ y
  p = pr₂ (iss x)
  f : (w : Σ \(σ : Σ Y) → pr₁ σ ≡ x) → c ≡ w
  f ((.x , y) , refl) = ap (λ y → (x , y) , refl) (p y)
  g : isSingleton (fiber pr₁ x)
  g = c , f

pr₁-vequivalence-converse : ∀ {U V} {X : U ̇} {Y : X → V ̇}
                          → isVoevodskyEquiv (pr₁ {U} {V} {X} {Y})
                          → ((x : X) → isSingleton(Y x))
pr₁-vequivalence-converse {U} {V} {X} {Y} isv x = retract-of-singleton r (s , rs) (isv x)
  where
    f : Σ Y → X
    f = pr₁ {U} {V} {X} {Y}
    s : Y x → fiber f x
    s y = (x , y) , refl
    r : fiber f x → Y x
    r ((x , y) , refl) = y
    rs : (y : Y x) → r(s y) ≡ y
    rs y = refl

\end{code}

\begin{code}

NatΣ-equiv : ∀ {U V W} (X : U ̇) (A : X → V ̇) (B : X → W ̇) (ζ : Nat A B)
           → ((x : X) → isEquiv(ζ x)) → isEquiv(NatΣ ζ)
NatΣ-equiv X A B ζ ise = ((s , ζs), (r , rζ)) 
 where
  s : Σ B → Σ A
  s (x , b) = x , pr₁ (pr₁ (ise x)) b
  ζs : (β : Σ B) → (NatΣ ζ ∘ s) β ≡ β
  ζs (x , b) = ap (λ b → (x , b)) (pr₂ (pr₁ (ise x)) b)
  r : Σ B → Σ A
  r (x , b) = x , (pr₁ (pr₂ (ise x)) b)
  rζ : (α : Σ A) → (r ∘ NatΣ ζ) α ≡ α
  rζ (x , a) = ap (λ a → (x , a)) (pr₂ (pr₂ (ise x)) a)

\end{code}

Associativities and precedences.

\begin{code}

infix  0 _≃_
infix  1 _■
infixr 0 _≃⟨_⟩_

\end{code}
