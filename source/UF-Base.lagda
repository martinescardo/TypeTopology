\begin{code}

{-# OPTIONS --without-K --exact-split #-}

module UF-Base where

open import SpartanMLTT public

pathtofun : ∀ {U} {X Y : U ̇} → X ≡ Y → X → Y
pathtofun = transport id

forth-and-back-transport : ∀ {U V} {X : U ̇} {A : X → V ̇} {x y : X} {a : A x} 
                         → (p : x ≡ y) → back-transport A p (transport A p a) ≡ a
forth-and-back-transport refl = refl

back-and-forth-transport : ∀ {U V} {X : U ̇} {A : X → V ̇} {x y : X} {a : A x} 
                         → (p : y ≡ x) → transport A p (back-transport A p a) ≡ a
back-and-forth-transport refl = refl

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

refl-left-neutral : ∀ {U} {X : U ̇} {x y : X} {p : x ≡ y} → refl ∙ p ≡ p
refl-left-neutral {U} {X} {x} {_} {refl} = refl

refl-right-neutral : ∀ {U} {X : U ̇} {x y : X} (p : x ≡ y) → p ≡ p ∙ refl
refl-right-neutral p = refl

assoc : ∀ {U} {X : U ̇} {x y z t : X} (p : x ≡ y) (q : y ≡ z) (r : z ≡ t)
      → (p ∙ q) ∙ r ≡ p ∙ (q ∙ r)
assoc refl refl refl = refl

happly' : ∀ {U V} {X : U ̇} {A : X → V ̇} (f g : Π A) → f ≡ g → f ∼ g
happly' f g p x = ap (λ h → h x) p

happly : ∀ {U V} {X : U ̇} {A : X → V ̇} {f g : Π A} → f ≡ g → f ∼ g
happly = happly' _ _

sym-is-inverse : ∀ {U} {X : U ̇} {x y : X} (p : x ≡ y)
               → refl ≡ p ⁻¹ ∙ p
sym-is-inverse = J (λ x y p → refl ≡ p ⁻¹ ∙ p) (λ x → refl)

sym-is-inverse' : ∀ {U} {X : U ̇} {x y : X} (p : x ≡ y)
               → refl ≡ p ∙ p ⁻¹
sym-is-inverse' refl = refl

⁻¹-involutive : ∀ {U} {X : U ̇} {x y : X} (p : x ≡ y) → (p ⁻¹)⁻¹ ≡ p
⁻¹-involutive refl = refl

⁻¹-contravariant : ∀ {U} {X : U ̇} {x y : X} (p : x ≡ y) {z : X} (q : y ≡ z)
                → q ⁻¹ ∙ p ⁻¹ ≡ (p ∙ q)⁻¹
⁻¹-contravariant refl refl = refl

left-inverse : ∀ {U} {X : U ̇} {x y : X} (p : x ≡ y) → p ⁻¹ ∙ p ≡ refl
left-inverse {U} {X} {x} {y} refl = refl

right-inverse : ∀ {U} {X : U ̇} {x y : X} (p : x ≡ y) → refl ≡ p ∙ p ⁻¹
right-inverse {U} {X} {x} {y} refl = refl

cancel-left : ∀ {U} {X : U ̇} {x y z : X} {p : x ≡ y} {q r : y ≡ z}
            → p ∙ q ≡ p ∙ r → q ≡ r
cancel-left {U} {X} {x} {y} {z} {p} {q} {r} s = 
       q              ≡⟨ refl-left-neutral ⁻¹ ⟩
       refl ∙ q       ≡⟨ ap (λ t → t ∙ q) ((left-inverse p)⁻¹) ⟩
       (p ⁻¹ ∙ p) ∙ q ≡⟨ assoc (p ⁻¹) p q ⟩
       p ⁻¹ ∙ (p ∙ q) ≡⟨ ap (λ t → p ⁻¹ ∙ t) s ⟩
       p ⁻¹ ∙ (p ∙ r) ≡⟨ (assoc (p ⁻¹) p r)⁻¹ ⟩
       (p ⁻¹ ∙ p) ∙ r ≡⟨ ap (λ t → t ∙ r) (left-inverse p) ⟩
       refl ∙ r       ≡⟨ refl-left-neutral ⟩
       r ∎

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

from-Σ-≡'' : ∀ {U V} {X : U ̇} {Y : X → V ̇} {u v : Σ Y} (r : u ≡ v)
          → Σ \(p : pr₁ u ≡ pr₁ v) → transport Y p (pr₂ u) ≡ (pr₂ v)
from-Σ-≡'' {U} {V} {X} {Y} {u} {v} r = (ap pr₁ r , from-Σ-≡ u v r)

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
