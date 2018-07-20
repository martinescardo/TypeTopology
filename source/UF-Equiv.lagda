\begin{code}

{-# OPTIONS --without-K --exact-split #-}

module UF-Equiv where

open import SpartanMLTT
open import UF-Base
open import UF-Subsingletons
open import UF-Retracts
open import UF-Subsingletons-Retracts

\end{code}

We take Joyal's version of the notion of equivalence as the primary
one because it is more symmetrical.

\begin{code}

is-equiv : ∀ {U V} {X : U ̇} {Y : V ̇} → (X → Y) → U ⊔ V ̇
is-equiv f = has-section f × has-retraction f

_≃_ : ∀ {U V} → U ̇ → V ̇ → U ⊔ V ̇
X ≃ Y = Σ \(f : X → Y) → is-equiv f

equiv-to-fun : ∀ {U V} {X : U ̇} {Y : V ̇} → X ≃ Y → X → Y
equiv-to-fun = pr₁

ideq : ∀ {U} (X : U ̇) → X ≃ X
ideq X = id , ((id , λ x → refl) , (id , λ x → refl))

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

idtofun-agreement : ∀ {U} (X Y : U ̇) (p : X ≡ Y) → idtofun X Y p ≡ Idtofun p
idtofun-agreement X Y refl = refl

equiv-closed-under-∼ : ∀ {U V} {X : U ̇} {Y : V ̇} (f g : X → Y) → is-equiv f →  g ∼ f  → is-equiv g
equiv-closed-under-∼ {U} {V} {X} {Y} f g (hass , hasr) h = (has-section-closed-under-∼ f g hass h) ,
                                                           (has-retraction-closed-under-∼ f g hasr h)

equiv-closed-under-∼' : ∀ {U V} {X : U ̇} {Y : V ̇} {f g : X → Y} → is-equiv f → f ∼ g → is-equiv g
equiv-closed-under-∼' ise h = equiv-closed-under-∼ _ _ ise (λ x → (h x)⁻¹)

qinv : {U V : Universe} {X : U ̇} {Y : V ̇} → (X → Y) → U ⊔ V ̇
qinv f = Σ \g → (g ∘ f ∼ id) × (f ∘ g ∼ id)

is-equiv-qinv : {U V : Universe} {X : U ̇} {Y : V ̇} (f : X → Y) → is-equiv f → qinv f
is-equiv-qinv {U} {V} {X} {Y} f ((s , fs) , (r , rf)) = s , (sf , fs)
 where
  sf : (x : X) → s(f x) ≡ x
  sf x = s(f x)       ≡⟨ (rf (s (f x)))⁻¹ ⟩
         r(f(s(f x))) ≡⟨ ap r (fs (f x)) ⟩
         r(f x)       ≡⟨ rf x ⟩
         x            ∎

qinv-is-equiv : {U V : Universe} {X : U ̇} {Y : V ̇} (f : X → Y) → qinv f → is-equiv f
qinv-is-equiv f (g , (gf , fg)) = (g , fg) , (g , gf)

≃-sym : ∀ {U V} {X : U ̇} {Y : V ̇}  → X ≃ Y → Y ≃ X
≃-sym {U} {V} {X} {Y} (f , e) = (g , d)
 where
  g : Y → X
  g = pr₁(is-equiv-qinv f e)
  q : qinv g
  q = f , pr₂(pr₂(is-equiv-qinv f e)) , pr₁(pr₂(is-equiv-qinv f e))
  d : is-equiv g
  d = qinv-is-equiv g q

equiv-retract-l : ∀ {U V} {X : U ̇} {Y : V ̇} → X ≃ Y → retract X of Y
equiv-retract-l (f , (g , fg) , (h , hf)) = h , f , hf

equiv-retract-r : ∀ {U V} {X : U ̇} {Y : V ̇} → X ≃ Y → retract Y of X
equiv-retract-r (f , (g , fg) , (h , hf)) = f , g , fg

\end{code}

Equivalence of transports.

\begin{code}

transport-is-equiv : ∀ {U V} {X : U ̇} {A : X → V ̇} {x y : X} (p : x ≡ y) → is-equiv (transport A p)
transport-is-equiv refl =  pr₂ (ideq _)

back-transport-is-equiv : ∀ {U V} {X : U ̇} {A : X → V ̇} {x y : X} (p : x ≡ y) → is-equiv (back-transport A p)
back-transport-is-equiv p = transport-is-equiv (p ⁻¹)

\end{code}

\begin{code}

fiber : ∀ {U V} {X : U ̇} {Y : V ̇} (f : X → Y) → Y → U ⊔ V ̇
fiber f y = Σ \x → f x ≡ y

is-vv-equiv : ∀ {U V} {X : U ̇} {Y : V ̇} → (X → Y) → U ⊔ V ̇
is-vv-equiv f = ∀ y → is-singleton (fiber f y)

is-vv-equiv-is-equiv : ∀ {U V} {X : U ̇} {Y : V ̇} (f : X → Y)
                     → is-vv-equiv f → is-equiv f
is-vv-equiv-is-equiv {U} {V} {X} {Y} f φ = (g , fg) , (g , gf)
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

is-hae : ∀ {U} {V} {X : U ̇} {Y : V ̇} → (X → Y) → U ⊔ V ̇
is-hae {U} {V} {X} {Y} f = Σ \(g : Y → X) → Σ \(η : g ∘ f ∼ id) → Σ \(ε : f ∘ g ∼ id) → (x : X) → ap f (η x) ≡ ε (f x)

is-hae-is-equiv : ∀ {U} {V} {X : U ̇} {Y : V ̇} (f : X → Y)
               → is-hae f → is-equiv f
is-hae-is-equiv {U} {V} {X} f (g , η , ε , τ) = qinv-is-equiv f (g , η , ε)

id-homotopies-are-natural : ∀ {U} {X : U ̇} (h : X → X) (η : h ∼ id) {x : X}
                         → η (h x) ≡ ap h (η x)
id-homotopies-are-natural h η {x} =
   η (h x)                         ≡⟨ refl ⟩
   η (h x) ∙ refl                  ≡⟨ ap (λ - → η(h x) ∙ -) ((trans-sym' (η x))⁻¹) ⟩
   η (h x) ∙ (η x ∙ (η x)⁻¹)        ≡⟨ (assoc (η (h x)) (η x) (η x ⁻¹))⁻¹ ⟩
   η (h x) ∙ η x ∙ (η x)⁻¹          ≡⟨ ap (λ - → η (h x) ∙ - ∙ (η x)⁻¹) ((ap-id-is-id (η x))) ⟩
   η (h x) ∙ ap id (η x) ∙ (η x)⁻¹  ≡⟨ homotopies-are-natural' h id η {h x} {x} {η x} ⟩
   ap h (η x)                      ∎

qinv-is-hae : ∀ {U} {V} {X : U ̇} {Y : V ̇} (f : X → Y) → qinv f → is-hae f
qinv-is-hae {U} {V} {X} {Y} f (g , (η , ε)) = g , η , ε' , τ
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

is-equiv-is-hae : ∀ {U} {V} {X : U ̇} {Y : V ̇} (f : X → Y)
              → is-equiv f → is-hae f
is-equiv-is-hae f e = qinv-is-hae f (is-equiv-qinv f e)

\end{code}

The following could be defined by combining functions we already have,
but a proof by path induction is direct:

\begin{code}

identifications-in-fibers : ∀ {U} {V} {X : U ̇} {Y : V ̇} (f : X → Y)
                   (y : Y) (x x' : X) (p : f x ≡ y) (p' : f x' ≡ y)
                → (Σ \(γ : x ≡ x') → ap f γ ∙ p' ≡ p) → (x , p) ≡ (x' , p')
identifications-in-fibers f .(f x) x .x refl p' (refl , r) = g
 where
  g : x , refl ≡ x , p'
  g = ap (λ - → (x , -)) (r ⁻¹ ∙ refl-left-neutral)

\end{code}

Using this we see that half adjoint equivalences have singleton fibers:

\begin{code}

is-hae-is-vv-equiv : ∀ {U} {V} {X : U ̇} {Y : V ̇} (f : X → Y)
                  → is-hae f → is-vv-equiv f
is-hae-is-vv-equiv {U} {V} {X} f (g , η , ε , τ) y = (c , λ σ → α (pr₁ σ) (pr₂ σ))
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

qinv-is-vv-equiv : ∀ {U} {V} {X : U ̇} {Y : V ̇} (f : X → Y)
                 → qinv f → is-vv-equiv f
qinv-is-vv-equiv f q = is-hae-is-vv-equiv f (qinv-is-hae f q)

is-equiv-is-vv-equiv : ∀ {U V} {X : U ̇} {Y : V ̇} (f : X → Y)
                     → is-equiv f → is-vv-equiv f
is-equiv-is-vv-equiv f ie = qinv-is-vv-equiv f (is-equiv-qinv f ie)

\end{code}

We pause to characterize negation and singletons. Recall that ¬ X and
is-empty X are synonyms for the function type X → 𝟘.

\begin{code}

equiv-can-assume-pointed-codomain : ∀ {U V} {X : U ̇} {Y : V ̇} (f : X → Y)
                                  → (Y → is-vv-equiv f) → is-vv-equiv f
equiv-can-assume-pointed-codomain f φ y = φ y y

maps-to-𝟘-are-equivs : ∀ {U} {X : U ̇} (f : ¬ X) → is-vv-equiv f
maps-to-𝟘-are-equivs f = equiv-can-assume-pointed-codomain f 𝟘-elim

negation-is-equiv-𝟘 : ∀ {U} {X : U ̇} → is-empty X ⇔ X ≃ 𝟘
negation-is-equiv-𝟘 = (λ f → f , is-vv-equiv-is-equiv f (maps-to-𝟘-are-equivs f)), pr₁

\end{code}

Then with functional and propositional extensionality, which follow
from univalence, we conclude that ¬X = (X ≃ 0) = (X ≡ 0).

And similarly, with similar a observation:

\begin{code}

is-singleton-is-equiv-𝟙 : ∀ {U V} {X : U ̇} → is-singleton X ⇔ X ≃ 𝟙 {V}
is-singleton-is-equiv-𝟙 {U} {V} {X} = forth , back
 where
  forth : is-singleton X → X ≃ 𝟙
  forth (x₀ , φ) = unique-to-𝟙 , (((λ _ → x₀) , (λ x → (𝟙-all-* x)⁻¹)) , ((λ _ → x₀) , φ))
  back : X ≃ 𝟙 → is-singleton X
  back (f , (s , fs) , (r , rf)) = retract-of-singleton r (f , rf) 𝟙-is-singleton

\end{code}

The following again could be defined by combining functions we already
have:

\begin{code}

from-identifications-in-fibers : ∀ {U} {V} {X : U ̇} {Y : V ̇} (f : X → Y)
                       (y : Y) (x x' : X) (p : f x ≡ y) (p' : f x' ≡ y)
                     → (x , p) ≡ (x' , p') → Σ \(γ : x ≡ x') → ap f γ ∙ p' ≡ p
from-identifications-in-fibers f .(f x) x .x refl .refl refl = refl , refl

η-pif : ∀ {U} {V} {X : U ̇} {Y : V ̇} (f : X → Y)
        (y : Y) (x x' : X) (p : f x ≡ y) (p' : f x' ≡ y)
        (σ : Σ \(γ : x ≡ x') → ap f γ ∙ p' ≡ p)
      → from-identifications-in-fibers f y x x' p p' (identifications-in-fibers f y x x' p p' σ) ≡ σ
η-pif f .(f x) x .x _ refl (refl , refl) = refl

\end{code}

Then the following is a consequence of natural-section-has-retraction,
but also has a direct proof by path induction:

\begin{code}
ε-pif : ∀ {U} {V} {X : U ̇} {Y : V ̇} (f : X → Y)
        (y : Y) (x x' : X) (p : f x ≡ y) (p' : f x' ≡ y)
        (q : (x , p) ≡ (x' , p'))
      → identifications-in-fibers f y x x' p p' (from-identifications-in-fibers f y x x' p p' q) ≡ q
ε-pif f .(f x) x .x refl .refl refl = refl

pr₁-equivalence : ∀ {U V} (X : U ̇) (A : X → V ̇)
               → ((x : X) → is-singleton (A x))
               → is-equiv (pr₁ {U} {V} {X} {A})
pr₁-equivalence {U} {V} X A iss = (g , prg) , (g , gpr)
 where
  g : X → Σ A
  g x = x , pr₁(iss x)
  prg : (x : X) → pr₁ (g x) ≡ x
  prg x = refl
  gpr : (σ : Σ A) → g(pr₁ σ) ≡ σ
  gpr (x , a) = to-Σ-≡'' (prg x , is-singleton-is-prop (iss x) _ _)

pr₁-vv-equiv : ∀ {U V} (X : U ̇) (Y : X → V ̇)
                → ((x : X) → is-singleton (Y x))
                → is-vv-equiv (pr₁ {U} {V} {X} {Y})
pr₁-vv-equiv {U} {V} X Y iss x = g
 where
  c : fiber pr₁ x
  c = (x , pr₁ (iss x)) , refl
  p : (y : Y x) → pr₁ (iss x) ≡ y
  p = pr₂ (iss x)
  f : (w : Σ \(σ : Σ Y) → pr₁ σ ≡ x) → c ≡ w
  f ((.x , y) , refl) = ap (λ - → (x , -) , refl) (p y)
  g : is-singleton (fiber pr₁ x)
  g = c , f

pr₁-vv-equiv-converse : ∀ {U V} {X : U ̇} {A : X → V ̇}
                     → is-vv-equiv (pr₁ {U} {V} {X} {A})
                     → ((x : X) → is-singleton(A x))
pr₁-vv-equiv-converse {U} {V} {X} {A} isv x = retract-of-singleton r (s , rs) (isv x)
  where
    f : Σ A → X
    f = pr₁ {U} {V} {X} {A}
    s : A x → fiber f x
    s a = (x , a) , refl
    r : fiber f x → A x
    r ((x , a) , refl) = a
    rs : (a : A x) → r(s a) ≡ a
    rs a = refl

NatΣ-equiv : ∀ {U V W} {X : U ̇} (A : X → V ̇) (B : X → W ̇) (ζ : Nat A B)
           → ((x : X) → is-equiv(ζ x)) → is-equiv(NatΣ ζ)
NatΣ-equiv A B ζ ise = ((s , ζs), (r , rζ))
 where
  s : Σ B → Σ A
  s (x , b) = x , pr₁ (pr₁ (ise x)) b
  ζs : (β : Σ B) → (NatΣ ζ ∘ s) β ≡ β
  ζs (x , b) = ap (λ - → (x , -)) (pr₂ (pr₁ (ise x)) b)
  r : Σ B → Σ A
  r (x , b) = x , (pr₁ (pr₂ (ise x)) b)
  rζ : (α : Σ A) → (r ∘ NatΣ ζ) α ≡ α
  rζ (x , a) = ap (λ - → (x , -)) (pr₂ (pr₂ (ise x)) a)

NatΣ-equiv' : ∀ {U V W} {X : U ̇} (A : X → V ̇) (B : X → W ̇)
            → ((x : X) → A x ≃ B x) → Σ A ≃ Σ B
NatΣ-equiv' A B e = NatΣ (λ x → pr₁(e x)) , NatΣ-equiv A B (λ x → pr₁(e x)) (λ x → pr₂(e x))

Σ-change-of-variables' : ∀ {U V W} {X : U ̇} {Y : V ̇} (A : X → W ̇) (g : Y → X)
                       → is-hae g → Σ \(γ : (Σ \(y : Y) → A (g y)) → Σ A) → qinv γ
Σ-change-of-variables' {U} {V} {W} {X} {Y} A g (f , fg , gf , α) = γ , φ , φγ , γφ
 where
  γ : (Σ \(y : Y) → A (g y)) → Σ A
  γ (y , a) = (g y , a)
  φ : Σ A → Σ \(y : Y) → A (g y)
  φ (x , a) = (f x , back-transport A (gf x) a)
  γφ : (σ : Σ A) → γ (φ σ) ≡ σ
  γφ (x , a) = to-Σ-≡'' (gf x , p)
   where
    p : transport A (gf x) (back-transport A (gf x) a) ≡ a
    p = back-and-forth-transport (gf x)
  φγ : (τ : (Σ \(y : Y) → A (g y))) → φ (γ τ) ≡ τ
  φγ (y , a) = to-Σ-≡'' (fg y , q)
   where
    q : transport (λ - → A (g -)) (fg y) (back-transport A (gf (g y)) a) ≡ a
    q = transport (λ - → A (g -)) (fg y) (back-transport A (gf (g y)) a) ≡⟨ transport-ap g (fg y) ⟩
        transport A (ap g (fg y)) (back-transport A (gf (g y)) a)        ≡⟨ ap (λ - → transport A - (back-transport A (gf (g y)) a)) (α y) ⟩
        transport A (gf (g y)) (back-transport A (gf (g y)) a)           ≡⟨ back-and-forth-transport (gf (g y)) ⟩
        a ∎

Σ-change-of-variables : ∀ {U V W} {X : U ̇} {Y : V ̇} (A : X → W ̇) (g : Y → X)
                      → is-equiv g → (Σ \(y : Y) → A (g y)) ≃ Σ A
Σ-change-of-variables {U} {V} {W} {X} {Y} A g e = γ , qinv-is-equiv γ q
 where
  γ :  (Σ \(y : Y) → A (g y)) → Σ A
  γ = pr₁(Σ-change-of-variables' A g (is-equiv-is-hae g e))
  q :  qinv γ
  q = pr₂(Σ-change-of-variables' A g (is-equiv-is-hae g e))

\end{code}

Associativities and precedences.

\begin{code}

infix  0 _≃_
infix  1 _■
infixr 0 _≃⟨_⟩_

\end{code}
