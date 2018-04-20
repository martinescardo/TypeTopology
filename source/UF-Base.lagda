\begin{code}

{-# OPTIONS --without-K --exact-split #-}

module UF-Base where

open import SpartanMLTT public

\end{code}

\begin{code}

idp : ∀ {U} {X : U ̇} (x : X) → x ≡ x
idp _ = refl

pathtofun : ∀ {U} {X Y : U ̇} → X ≡ Y → X → Y
pathtofun = transport id

back-transport-is-pre-comp : ∀ {U} {X X' Y : U ̇} (p : X ≡ X') (g : X' → Y)
                          → back-transport (λ Z → Z → Y) p g ≡ g ∘ pathtofun p
back-transport-is-pre-comp refl g = refl

trans-sym : ∀ {U} {X : U ̇} {x y : X} (r : x ≡ y) → r ⁻¹ ∙ r ≡ refl
trans-sym refl = refl

trans-sym' : ∀ {U} {X : U ̇} {x y : X} (r : x ≡ y) → r ∙ r ⁻¹ ≡ refl
trans-sym' refl = refl

transport-ap : ∀ {U V W} {X : U ̇} {Y : V ̇} {A : Y → W ̇} (f : X → Y) {x x' : X} (p : x ≡ x') {a : A(f x)}
             → transport (A ∘ f) p a ≡ transport A (ap f p) a
transport-ap f refl = refl 

nat-transport : ∀ {U V W} {X : U ̇} {A : X → V ̇} {B : X → W ̇} (f : (x : X) → A x → B x) {x y : X} (p : x ≡ y) {a : A x}
              → f y (transport A p a) ≡ transport B p (f x a)
nat-transport f refl = refl

apd : ∀ {U V} {X : U ̇} {A : X → V ̇} (f : (x : X) → A x) {x y : X}
    (p : x ≡ y) → transport A p (f x) ≡ f y
apd f refl = refl

ap-id-is-id : ∀ {U} {X : U ̇} {x y : X} (p : x ≡ y) → p ≡ ap id p
ap-id-is-id refl = refl

ap-comp : ∀ {U V} {X : U ̇} {Y : V ̇} (f : X → Y) {x y z : X} (p : x ≡ y) (q : y ≡ z)
       → ap f (p ∙ q) ≡ ap f p ∙ ap f q
ap-comp f refl refl = refl       

ap-sym : ∀ {U V} {X : U ̇} {Y : V ̇} (f : X → Y) {x y : X} (p : x ≡ y)
       → (ap f p) ⁻¹ ≡ ap f (p ⁻¹)
ap-sym f refl = refl       

ap-ap : ∀ {U V W} {X : U ̇} {Y : V ̇} {Z : W ̇} (f : X → Y) (g : Y → Z) {x x' : X} (r : x ≡ x')
     → ap g (ap f r) ≡ ap (g ∘ f) r
ap-ap {U} {V} {W} {X} {Y} {Z} f g = J A (λ x → refl)
 where
  A : (x x' : X) → x ≡ x' → W ̇
  A x x' r = ap g (ap f r) ≡ ap (g ∘ f) r

ap₂ : ∀ {U V W} {X : U ̇} {Y : V ̇} {Z : W ̇} (f : X → Y → Z) {x₀ x₁ : X} {y₀ y₁ : Y}
   → x₀ ≡ x₁ → y₀ ≡ y₁ → f x₀ y₀ ≡ f x₁ y₁
ap₂ f refl refl = refl

_∼_ : ∀ {U V} {X : U ̇} {A : X → V ̇} → Π A → Π A → U ⊔ V ̇
f ∼ g = ∀ x → f x ≡ g x

idp-left-neutral : ∀ {U} {X : U ̇} {x y : X} {p : x ≡ y} → idp x ∙ p ≡ p
idp-left-neutral {U} {X} {x} {_} {refl} = refl

assoc : ∀ {U} {X : U ̇} {x y z t : X} (p : x ≡ y) (q : y ≡ z) (r : z ≡ t)
      → (p ∙ q) ∙ r ≡ p ∙ (q ∙ r)
assoc refl refl refl = refl

happly' : ∀ {U V} {X : U ̇} {A : X → V ̇} (f g : Π A) → f ≡ g → f ∼ g
happly' f g p x = ap (λ h → h x) p

happly : ∀ {U V} {X : U ̇} {A : X → V ̇} {f g : Π A} → f ≡ g → f ∼ g
happly = happly' _ _

sym-is-inverse : ∀ {U} {X : U ̇} {x y : X} (p : x ≡ y)
               → refl ≡ p ⁻¹ ∙ p
sym-is-inverse {X} = J (λ x y p → refl ≡ p ⁻¹ ∙ p) (λ x → refl)

refl-left-neutral : ∀ {U} {X : U ̇} {x y : X} {p : x ≡ y} → refl ∙ p ≡ p
refl-left-neutral {U} {X} {x} {_} {refl} = refl 

homotopies-are-natural' : ∀ {U} {V} {X : U ̇} {A : V ̇} (f g : X → A) (H : f ∼ g) {x y : X} {p : x ≡ y}
                      → H x ∙ ap g p ∙ (H y)⁻¹ ≡ ap f p
homotopies-are-natural' f g H {x} {_} {refl} = trans-sym' (H x)

homotopies-are-natural : ∀ {U} {V} {X : U ̇} {A : V ̇} (f g : X → A) (H : f ∼ g) {x y : X} {p : x ≡ y}
                      → H x ∙ ap g p ≡ ap f p ∙ H y
homotopies-are-natural f g H {x} {_} {refl} = refl-left-neutral ⁻¹

×-≡ : ∀ {U V} {X : U ̇} {Y : V ̇} {x x' : X} {y y' : Y}
     → x ≡ x' → y ≡ y' → (x , y) ≡ (x' , y') 
×-≡ refl refl = refl

from-Σ-≡ : ∀ {U V} {X : U ̇} {Y : X → V ̇} (u v : Σ Y) (r : u ≡ v)
          → transport Y (ap pr₁ r) (pr₂ u) ≡ (pr₂ v)
from-Σ-≡ {U} {V} {X} {Y} u v = J A (λ u → refl) {u} {v}
 where
  A : (u v : Σ Y) → u ≡ v → V ̇
  A u v r = transport Y (ap pr₁ r) (pr₂ u) ≡ (pr₂ v)

from-Σ-≡' : ∀ {U V} {X : U ̇} {Y : X → V ̇} (x : X) (y y' : Y x)
           → (r : (x , y) ≡ (x , y')) → transport Y (ap pr₁ r) y ≡ y'
from-Σ-≡' x y y' = from-Σ-≡ (x , y) (x , y')

to-Σ-≡ : ∀ {U V} {X : U ̇} {Y : X → V ̇} (x x' : X) (y : Y x) (y' : Y x')
     → (p : x ≡ x') → transport Y p y ≡ y' → (x , y) ≡ (x' , y') 
to-Σ-≡ .x' x' .y y refl refl = refl

to-Σ-≡'' : ∀ {U V} {X : U ̇} {A : X → V ̇} {σ τ : Σ A}
          → (Σ \(p : pr₁ σ ≡ pr₁ τ) → transport A p (pr₂ σ) ≡ pr₂ τ)
          → σ ≡ τ
to-Σ-≡'' (refl , refl) = refl

to-Σ-≡' : ∀ {U V} {X : U ̇} {Y : X → V ̇} (x : X) (y y' : Y x) 
     → y ≡ y' → _≡_ {_} {Σ Y} (x , y) (x , y') 
to-Σ-≡' x y y' r = ap (λ y → (x , y)) r

\end{code}

We need to find a better place for this:

\begin{code}

_⇒_ : ∀ {U V W} {X : U ̇} → (X → V ̇) → (X → W ̇) → (X → V ⊔ W ̇)
A ⇒ B = λ x → A x → B x

Nat : ∀ {U V W} {X : U ̇} → (X → V ̇) → (X → W ̇) → U ⊔ V ⊔ W ̇
Nat A B = Π(A ⇒ B)

left-cancellable : ∀ {U V} {X : U ̇} {Y : V ̇} → (X → Y) → U ⊔ V ̇
left-cancellable f = ∀ {x x'} → f x ≡ f x' → x ≡ x'

left-cancellable' : ∀ {U V} {X : U ̇} {Y : V ̇} → (X → Y) → U ⊔ V ̇
left-cancellable' f = ∀ x x' → f x ≡ f x' → x ≡ x'

\end{code}

Associativities and precedences.

\begin{code}

infix  4  _∼_

\end{code}
