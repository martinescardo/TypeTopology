\begin{code}

{-# OPTIONS --without-K --exact-split #-}

module UF-Equiv where

open import SpartanMLTT
open import UF-Base
open import UF-Subsingletons
open import UF-Retracts

\end{code}

We take Joyal's version of the notion of equivalence as the primary
one because it is more symmetrical.

\begin{code}

is-equiv : {X : U ̇} {Y : V ̇} → (X → Y) → U ⊔ V ̇
is-equiv f = has-section f × has-retraction f

is-equiv-has-section : {X : U ̇} {Y : V ̇} (f : X → Y)
                     → is-equiv f → has-section f
is-equiv-has-section f = pr₁

is-equiv-has-retraction : {X : U ̇} {Y : V ̇} (f : X → Y)
                        → is-equiv f → has-retraction f
is-equiv-has-retraction f = pr₂

section-retraction-equiv : {X : U ̇} {Y : V ̇} (f : X → Y)
                         → has-section f → has-retraction f → is-equiv f
section-retraction-equiv f hr hs = (hr , hs)

_≃_ : U ̇ → V ̇ → U ⊔ V ̇
X ≃ Y = Σ \(f : X → Y) → is-equiv f

id-is-an-equiv : (X : U ̇) → is-equiv (id {U} {X})
id-is-an-equiv X = (id , λ x → refl) , (id , λ x → refl)

≃-refl : (X : U ̇) → X ≃ X
≃-refl X = id , id-is-an-equiv X

≃-trans : {X : U ̇} {Y : V ̇} {Z : W ̇} → X ≃ Y → Y ≃ Z → X ≃ Z
≃-trans {U} {V} {W} {X} {Y} {Z} (f , (g , fg) , (h , hf)) (f' , (g' , fg') , (h' , hf'))  =
  f' ∘ f , (g ∘ g' , fg'') , (h ∘ h' , hf'')
 where
    fg'' : (z : Z) → f' (f (g (g' z))) ≡ z
    fg'' z =  ap f' (fg (g' z)) ∙ fg' z
    hf'' : (x : X) → h(h'(f'(f x))) ≡ x
    hf'' x = ap h (hf' (f x)) ∙ hf x

_≃⟨_⟩_ : (X : U ̇) {Y : V ̇} {Z : W ̇} → X ≃ Y → Y ≃ Z → X ≃ Z
_ ≃⟨ d ⟩ e = ≃-trans d e

_■ : (X : U ̇) → X ≃ X
_■ = ≃-refl

Eq : U ̇ → V ̇ → U ⊔ V ̇
Eq = _≃_

Eqtofun : (X : U ̇) (Y : V ̇) → X ≃ Y → X → Y
Eqtofun X Y (f , _) = f

eqtofun : {X : U ̇} {Y : V ̇} → X ≃ Y → X → Y
eqtofun (f , _) = f

eqtofun-is-an-equiv : {X : U ̇} {Y : V ̇} (e : X ≃ Y) → is-equiv (eqtofun e)
eqtofun-is-an-equiv = pr₂

back-eqtofun : {X : U ̇} {Y : V ̇} → X ≃ Y → Y → X
back-eqtofun e = pr₁ (pr₁ (pr₂ e))

idtoeq : (X Y : U ̇) → X ≡ Y → X ≃ Y
idtoeq X Y p = transport (Eq X) p (≃-refl X)

idtoeq-traditional : (X Y : U ̇) → X ≡ Y → X ≃ Y
idtoeq-traditional X _ refl = ≃-refl X

\end{code}

We would have a definitional equality if we had defined the traditional
one using J(based), but because of the idiosyncracies of Agda, we
don't with the current definition:

\begin{code}

eqtoeq-agreement : (X Y : U ̇) (p : X ≡ Y)
                 → idtoeq X Y p ≡ idtoeq-traditional X Y p
eqtoeq-agreement {U} X _ refl = refl

idtofun : (X Y : U ̇) → X ≡ Y → X → Y
idtofun X Y p = eqtofun (idtoeq X Y p)

idtofun-agreement : (X Y : U ̇) (p : X ≡ Y) → idtofun X Y p ≡ Idtofun p
idtofun-agreement X Y refl = refl

equiv-closed-under-∼ : {X : U ̇} {Y : V ̇} (f g : X → Y) → is-equiv f →  g ∼ f  → is-equiv g
equiv-closed-under-∼ {U} {V} {X} {Y} f g (hass , hasr) h = (has-section-closed-under-∼ f g hass h) ,
                                                           (has-retraction-closed-under-∼ f g hasr h)

equiv-closed-under-∼' : {X : U ̇} {Y : V ̇} {f g : X → Y} → is-equiv f → f ∼ g → is-equiv g
equiv-closed-under-∼' ise h = equiv-closed-under-∼ _ _ ise (λ x → (h x)⁻¹)

qinv : {U V : Universe} {X : U ̇} {Y : V ̇} → (X → Y) → U ⊔ V ̇
qinv f = Σ \g → (g ∘ f ∼ id) × (f ∘ g ∼ id)

equivs-are-qinvs : {X : U ̇} {Y : V ̇} (f : X → Y) → is-equiv f → qinv f
equivs-are-qinvs {U} {V} {X} {Y} f ((s , fs) , (r , rf)) = s , (sf , fs)
 where
  sf : (x : X) → s(f x) ≡ x
  sf x = s(f x)       ≡⟨ (rf (s (f x)))⁻¹ ⟩
         r(f(s(f x))) ≡⟨ ap r (fs (f x)) ⟩
         r(f x)       ≡⟨ rf x ⟩
         x            ∎

qinvs-are-equivs : {X : U ̇} {Y : V ̇} (f : X → Y) → qinv f → is-equiv f
qinvs-are-equivs f (g , (gf , fg)) = (g , fg) , (g , gf)

qinveq : {X : U ̇} {Y : V ̇} (f : X → Y) → qinv f → X ≃ Y
qinveq f q = (f , qinvs-are-equivs f q)

≃-sym : {X : U ̇} {Y : V ̇}  → X ≃ Y → Y ≃ X
≃-sym {U} {V} {X} {Y} (f , e) = (g , d)
 where
  g : Y → X
  g = pr₁(equivs-are-qinvs f e)
  q : qinv g
  q = f , pr₂(pr₂(equivs-are-qinvs f e)) , pr₁(pr₂(equivs-are-qinvs f e))
  d : is-equiv g
  d = qinvs-are-equivs g q

equiv-retract-l : {X : U ̇} {Y : V ̇} → X ≃ Y → retract X of Y
equiv-retract-l (f , (g , fg) , (h , hf)) = h , f , hf

equiv-retract-r : {X : U ̇} {Y : V ̇} → X ≃ Y → retract Y of X
equiv-retract-r (f , (g , fg) , (h , hf)) = f , g , fg

Id-retract-l : {X Y : U ̇} → X ≡ Y → retract X of Y
Id-retract-l p = equiv-retract-l (idtoeq (lhs p) (rhs p) p)

Id-retract-r : {X Y : U ̇} → X ≡ Y → retract Y of X
Id-retract-r p = equiv-retract-r (idtoeq (lhs p) (rhs p) p)

equiv-to-subsingleton : {X : U ̇} {Y : V ̇}
                      → Y ≃ X
                      → is-subsingleton X
                      → is-subsingleton Y
equiv-to-subsingleton e = retract-of-subsingleton (equiv-retract-l e)

equiv-to-singleton : {X : U ̇} {Y : V ̇}
                   → Y ≃ X
                   → is-singleton X
                   → is-singleton Y
equiv-to-singleton e = retract-of-singleton (equiv-retract-l e)

\end{code}

Equivalence of transports.

\begin{code}

transports-are-equivs : {X : U ̇} {A : X → V ̇} {x y : X} (p : x ≡ y)
                   → is-equiv (transport A p)
transports-are-equivs refl = id-is-an-equiv _

back-transports-are-equivs : {X : U ̇} {A : X → V ̇} {x y : X} (p : x ≡ y)
                        → is-equiv (back-transport A p)
back-transports-are-equivs p = transports-are-equivs (p ⁻¹)

\end{code}

\begin{code}

fiber : {X : U ̇} {Y : V ̇} (f : X → Y) → Y → U ⊔ V ̇
fiber f y = Σ \x → f x ≡ y

is-vv-equiv : {X : U ̇} {Y : V ̇} → (X → Y) → U ⊔ V ̇
is-vv-equiv f = ∀ y → is-singleton (fiber f y)

vv-equivs-are-equivs : {X : U ̇} {Y : V ̇} (f : X → Y)
                     → is-vv-equiv f → is-equiv f
vv-equivs-are-equivs {U} {V} {X} {Y} f φ = (g , fg) , (g , gf)
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

fiber' : {X : U ̇} {Y : V ̇} (f : X → Y) → Y → U ⊔ V ̇
fiber' f y = Σ \x → y ≡ f x

fiber-lemma : {X : U ̇} {Y : V ̇} (f : X → Y) (y : Y) → fiber f y ≃ fiber' f y
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

is-hae : {X : U ̇} {Y : V ̇} → (X → Y) → U ⊔ V ̇
is-hae {U} {V} {X} {Y} f = Σ \(g : Y → X) → Σ \(η : g ∘ f ∼ id) → Σ \(ε : f ∘ g ∼ id)
                            → Π \(x : X) → ap f (η x) ≡ ε (f x)

haes-are-equivs : {X : U ̇} {Y : V ̇} (f : X → Y)
                → is-hae f → is-equiv f
haes-are-equivs {U} {V} {X} f (g , η , ε , τ) = qinvs-are-equivs f (g , η , ε)

id-homotopies-are-natural : {X : U ̇} (h : X → X) (η : h ∼ id) {x : X}
                          → η (h x) ≡ ap h (η x)
id-homotopies-are-natural h η {x} =
   η (h x)                         ≡⟨ refl ⟩
   η (h x) ∙ refl                  ≡⟨ ap (λ - → η(h x) ∙ -) ((trans-sym' (η x))⁻¹) ⟩
   η (h x) ∙ (η x ∙ (η x)⁻¹)       ≡⟨ (assoc (η (h x)) (η x) (η x ⁻¹))⁻¹ ⟩
   η (h x) ∙ η x ∙ (η x)⁻¹         ≡⟨ ap (λ - → η (h x) ∙ - ∙ (η x)⁻¹) ((ap-id-is-id (η x))) ⟩
   η (h x) ∙ ap id (η x) ∙ (η x)⁻¹ ≡⟨ homotopies-are-natural' h id η {h x} {x} {η x} ⟩
   ap h (η x)                      ∎

qinvs-are-haes : {X : U ̇} {Y : V ̇} (f : X → Y) → qinv f → is-hae f
qinvs-are-haes {U} {V} {X} {Y} f (g , (η , ε)) = g , η , ε' , τ
 where
  ε' : f ∘ g ∼ id
  ε' y = f (g y)         ≡⟨ (ε (f (g y)))⁻¹ ⟩
         f (g (f (g y))) ≡⟨ ap f (η (g y)) ⟩
         f (g y)         ≡⟨ ε y ⟩
         y               ∎

  a : (x : X) → η (g (f x)) ≡ ap g (ap f (η x))
  a x = η (g (f x))      ≡⟨ id-homotopies-are-natural (g ∘ f) η  ⟩
        ap (g ∘ f) (η x)  ≡⟨ (ap-ap f g (η x))⁻¹ ⟩
        ap g (ap f (η x)) ∎

  b : (x : X) → ap f (η (g (f x))) ∙ ε (f x) ≡ ε (f (g (f x))) ∙ ap f (η x)
  b x = ap f (η (g (f x))) ∙ ε (f x)         ≡⟨ ap (λ - → - ∙ ε (f x)) (ap (ap f) (a x)) ⟩
        ap f (ap g (ap f (η x))) ∙ ε (f x)   ≡⟨ ap (λ - → - ∙ ε (f x)) (ap-ap g f (ap f (η x))) ⟩
        ap (f ∘ g) (ap f (η x)) ∙ ε (f x)    ≡⟨ (homotopies-are-natural (f ∘ g) id ε {f (g (f x))} {f x} {ap f (η x)})⁻¹ ⟩
        ε (f (g (f x))) ∙ ap id (ap f (η x)) ≡⟨ ap (λ - → ε (f (g (f x))) ∙ -) (ap-ap f id (η x)) ⟩
        ε (f (g (f x))) ∙ ap f (η x)         ∎

  τ : (x : X) → ap f (η x) ≡ ε' (f x)
  τ x = ap f (η x)                                         ≡⟨ refl-left-neutral ⁻¹ ⟩
        refl ∙ ap f (η x)                                   ≡⟨ ap (λ - → - ∙ ap f (η x)) ((trans-sym (ε (f (g (f x)))))⁻¹) ⟩
        (ε (f (g (f x))))⁻¹ ∙ ε (f (g (f x))) ∙ ap f (η x)   ≡⟨ assoc ((ε (f (g (f x))))⁻¹) (ε (f (g (f x)))) (ap f (η x)) ⟩
        (ε (f (g (f x))))⁻¹ ∙ (ε (f (g (f x))) ∙ ap f (η x)) ≡⟨ ap (λ - → (ε (f (g (f x))))⁻¹ ∙ -) (b x)⁻¹ ⟩
        (ε (f (g (f x))))⁻¹ ∙ (ap f (η (g (f x))) ∙ ε (f x)) ≡⟨ refl ⟩
        ε' (f x)                                            ∎

equivs-are-haes : {X : U ̇} {Y : V ̇} (f : X → Y)
                → is-equiv f → is-hae f
equivs-are-haes f e = qinvs-are-haes f (equivs-are-qinvs f e)

\end{code}

The following could be defined by combining functions we already have,
but a proof by path induction is direct:

\begin{code}

identifications-in-fibers : {X : U ̇} {Y : V ̇} (f : X → Y)
                            (y : Y) (x x' : X) (p : f x ≡ y) (p' : f x' ≡ y)
                          → (Σ \(γ : x ≡ x') → ap f γ ∙ p' ≡ p) → (x , p) ≡ (x' , p')
identifications-in-fibers f .(f x) x .x refl p' (refl , r) = g
 where
  g : x , refl ≡ x , p'
  g = ap (λ - → (x , -)) (r ⁻¹ ∙ refl-left-neutral)

\end{code}

Using this we see that half adjoint equivalences have singleton fibers:

\begin{code}

haes-are-vv-equivs : {X : U ̇} {Y : V ̇} (f : X → Y)
                   → is-hae f → is-vv-equiv f
haes-are-vv-equivs {U} {V} {X} f (g , η , ε , τ) y = (c , λ σ → α (pr₁ σ) (pr₂ σ))
 where
  c : fiber f y
  c = (g y , ε y)

  α : (x : X) (p : f x ≡ y) → c ≡ (x , p)
  α x p = φ
   where
    γ : g y ≡ x
    γ = (ap g p)⁻¹ ∙ η x
    q : ap f γ ∙ p ≡ ε y
    q = ap f γ ∙ p                         ≡⟨ refl ⟩
        ap f ((ap g p)⁻¹ ∙ η x) ∙ p         ≡⟨ ap (λ - → - ∙ p) (ap-comp f ((ap g p)⁻¹) (η x)) ⟩
        ap f ((ap g p)⁻¹) ∙ ap f (η x) ∙ p  ≡⟨ ap (λ - → ap f - ∙ ap f (η x) ∙ p) (ap-sym g p) ⟩
        ap f (ap g (p ⁻¹)) ∙ ap f (η x) ∙ p ≡⟨ ap (λ - → ap f (ap g (p ⁻¹)) ∙ - ∙ p) (τ x) ⟩
        ap f (ap g (p ⁻¹)) ∙ ε (f x) ∙ p    ≡⟨ ap (λ - → - ∙ ε (f x) ∙ p) (ap-ap g f (p ⁻¹)) ⟩
        ap (f ∘ g) (p ⁻¹) ∙ ε (f x) ∙ p     ≡⟨ ap (λ - → - ∙ p) (homotopies-are-natural (f ∘ g) id ε {y} {f x} {p ⁻¹})⁻¹ ⟩
        ε y ∙ ap id (p ⁻¹) ∙ p              ≡⟨ ap (λ - → ε y ∙ - ∙ p) (ap-id-is-id (p ⁻¹))⁻¹ ⟩
        ε y ∙ p ⁻¹ ∙ p                      ≡⟨ assoc (ε y) (p ⁻¹) p ⟩
        ε y ∙ (p ⁻¹ ∙ p)                    ≡⟨ ap (λ - → ε y ∙ -) (trans-sym p) ⟩
        ε y ∙ refl ≡⟨ refl ⟩
        ε y ∎

    φ : g y , ε y ≡ x , p
    φ = identifications-in-fibers f y (g y) x (ε y) p (γ , q)

\end{code}

Here are some corollaries:

\begin{code}

qinvs-are-vv-equivs : {X : U ̇} {Y : V ̇} (f : X → Y)
                 → qinv f → is-vv-equiv f
qinvs-are-vv-equivs f q = haes-are-vv-equivs f (qinvs-are-haes f q)

equivs-are-vv-equivs : {X : U ̇} {Y : V ̇} (f : X → Y)
                     → is-equiv f → is-vv-equiv f
equivs-are-vv-equivs f ie = qinvs-are-vv-equivs f (equivs-are-qinvs f ie)

\end{code}

We pause to characterize negation and singletons. Recall that ¬ X and
is-empty X are synonyms for the function type X → 𝟘.

\begin{code}

equiv-can-assume-pointed-codomain : {X : U ̇} {Y : V ̇} (f : X → Y)
                                  → (Y → is-vv-equiv f) → is-vv-equiv f
equiv-can-assume-pointed-codomain f φ y = φ y y

maps-to-𝟘-are-equivs : {X : U ̇} (f : ¬ X) → is-vv-equiv f
maps-to-𝟘-are-equivs f = equiv-can-assume-pointed-codomain f 𝟘-elim

negations-are-equiv-to-𝟘 : {X : U ̇} → is-empty X ⇔ X ≃ 𝟘
negations-are-equiv-to-𝟘 = (λ f → f , vv-equivs-are-equivs f (maps-to-𝟘-are-equivs f)), pr₁

\end{code}

Then with functional and propositional extensionality, which follow
from univalence, we conclude that ¬X = (X ≃ 0) = (X ≡ 0).

And similarly, with similar a observation:

\begin{code}

singletons-are-equiv-to-𝟙 : {X : U ̇} → is-singleton X ⇔ X ≃ 𝟙 {V}
singletons-are-equiv-to-𝟙 {U} {V} {X} = forth , back
 where
  forth : is-singleton X → X ≃ 𝟙
  forth (x₀ , φ) = unique-to-𝟙 , (((λ _ → x₀) , (λ x → (𝟙-all-* x)⁻¹)) , ((λ _ → x₀) , φ))
  back : X ≃ 𝟙 → is-singleton X
  back (f , (s , fs) , (r , rf)) = retract-of-singleton (r , f , rf) 𝟙-is-singleton

\end{code}

The following again could be defined by combining functions we already
have:

\begin{code}

from-identifications-in-fibers : {X : U ̇} {Y : V ̇} (f : X → Y)
                                 (y : Y) (x x' : X) (p : f x ≡ y) (p' : f x' ≡ y)
                               → (x , p) ≡ (x' , p') → Σ \(γ : x ≡ x') → ap f γ ∙ p' ≡ p
from-identifications-in-fibers f .(f x) x .x refl .refl refl = refl , refl

η-pif : {X : U ̇} {Y : V ̇} (f : X → Y)
        (y : Y) (x x' : X) (p : f x ≡ y) (p' : f x' ≡ y)
        (σ : Σ \(γ : x ≡ x') → ap f γ ∙ p' ≡ p)
      → from-identifications-in-fibers f y x x' p p' (identifications-in-fibers f y x x' p p' σ) ≡ σ
η-pif f .(f x) x .x _ refl (refl , refl) = refl

\end{code}

Then the following is a consequence of natural-section-has-retraction,
but also has a direct proof by path induction:

\begin{code}
ε-pif : {X : U ̇} {Y : V ̇} (f : X → Y)
        (y : Y) (x x' : X) (p : f x ≡ y) (p' : f x' ≡ y)
        (q : (x , p) ≡ (x' , p'))
      → identifications-in-fibers f y x x' p p' (from-identifications-in-fibers f y x x' p p' q) ≡ q
ε-pif f .(f x) x .x refl .refl refl = refl

pr₁-is-vv-equiv : (X : U ̇) (Y : X → V ̇)
             → ((x : X) → is-singleton (Y x))
             → is-vv-equiv (pr₁ {U} {V} {X} {Y})
pr₁-is-vv-equiv {U} {V} X Y iss x = g
 where
  c : fiber pr₁ x
  c = (x , pr₁ (iss x)) , refl
  p : (y : Y x) → pr₁ (iss x) ≡ y
  p = pr₂ (iss x)
  f : (w : Σ \(σ : Σ Y) → pr₁ σ ≡ x) → c ≡ w
  f ((.x , y) , refl) = ap (λ - → (x , -) , refl) (p y)
  g : is-singleton (fiber pr₁ x)
  g = c , f

pr₁-is-vv-equiv-converse : {X : U ̇} {A : X → V ̇}
                      → is-vv-equiv (pr₁ {U} {V} {X} {A})
                      → ((x : X) → is-singleton(A x))
pr₁-is-vv-equiv-converse {U} {V} {X} {A} isv x = retract-of-singleton (r , s , rs) (isv x)
  where
    f : Σ A → X
    f = pr₁ {U} {V} {X} {A}
    s : A x → fiber f x
    s a = (x , a) , refl
    r : fiber f x → A x
    r ((x , a) , refl) = a
    rs : (a : A x) → r(s a) ≡ a
    rs a = refl

\end{code}

Associativities and precedences.

\begin{code}

infix  0 _≃_
infix  1 _■
infixr 0 _≃⟨_⟩_

\end{code}
