\begin{code}

{-# OPTIONS --without-K --exact-split #-}

module UF-Base where

open import SpartanMLTT

ap-const : {X : 𝓤 ̇} {Y : 𝓥 ̇} (y : Y) {x x' : X} (p : x ≡ x') → ap (λ _ → y) p ≡ refl
ap-const y refl = refl

transport₂ : {X : 𝓤 ̇} {Y : 𝓥 ̇} (A : X → Y → 𝓦 ̇)
             {x x' : X} {y y' : Y}
          → x ≡ x' → y ≡ y' → A x y → A x' y'
transport₂ A refl refl = id

back-transport₂ : {X : 𝓤 ̇} {Y : 𝓥 ̇} (A : X → Y → 𝓦 ̇)
                  {x x' : X} {y y' : Y}
               → x ≡ x' → y ≡ y' → A x' y' → A x y
back-transport₂ A refl refl = id

Idtofun : {X Y : 𝓤 ̇} → X ≡ Y → X → Y
Idtofun = transport id

back-Idtofun : {X Y : 𝓤 ̇} → X ≡ Y → Y → X
back-Idtofun = back-transport id

forth-and-back-transport : {X : 𝓤 ̇} {A : X → 𝓥 ̇} {x y : X} {a : A x}
                         → (p : x ≡ y) → back-transport A p (transport A p a) ≡ a
forth-and-back-transport refl = refl

back-and-forth-transport : {X : 𝓤 ̇} {A : X → 𝓥 ̇} {x y : X} {a : A x}
                         → (p : y ≡ x) → transport A p (back-transport A p a) ≡ a
back-and-forth-transport refl = refl

back-transport-is-pre-comp : {X X' : 𝓤 ̇} {Y : 𝓥 ̇} (p : X ≡ X') (g : X' → Y)
                          → back-transport (λ - → - → Y) p g ≡ g ∘ Idtofun p
back-transport-is-pre-comp refl g = refl

transport-is-pre-comp : {X X' : 𝓤 ̇} {Y : 𝓥 ̇} (p : X ≡ X') (g : X → Y)
                      → transport (λ - → - → Y) p g ≡ g ∘ Idtofun (p ⁻¹)
transport-is-pre-comp refl g = refl

trans-sym : {X : 𝓤 ̇} {x y : X} (r : x ≡ y) → r ⁻¹ ∙ r ≡ refl
trans-sym refl = refl

trans-sym' : {X : 𝓤 ̇} {x y : X} (r : x ≡ y) → r ∙ r ⁻¹ ≡ refl
trans-sym' refl = refl

transport-× : {X : 𝓤 ̇} (A : X → 𝓥 ̇) (B : X → 𝓦 ̇)
                {x y : X} {c : A x × B x} (p : x ≡ y)
            → transport (λ x → A x × B x) p c
            ≡ (transport A p (pr₁ c) , transport B p (pr₂ c))
transport-× A B refl = refl

transport-comp : {X : 𝓤 ̇} (A : X → 𝓥 ̇)
                   {x y z : X} (q : x ≡ y) (p : y ≡ z) {a : A x}
               → transport A  (q ∙ p) a ≡ transport A p (transport A q a)
transport-comp A refl refl = refl

transport-comp' : {X : 𝓤 ̇} (A : X → 𝓥 ̇)
                  {x y z : X} (q : x ≡ y) (p : y ≡ z)
                → transport A  (q ∙ p) ≡ transport A p ∘ transport A q
transport-comp' A refl refl = refl

transport-ap : {X : 𝓤 ̇} {Y : 𝓥 ̇} (A : Y → 𝓦 ̇)
               (f : X → Y) {x x' : X} (p : x ≡ x') {a : A(f x)}
             → transport (A ∘ f) p a ≡ transport A (ap f p) a
transport-ap A f refl = refl

transport-ap' : {X : 𝓤 ̇} {Y : 𝓥 ̇} (A : Y → 𝓦 ̇)
                (f : X → Y) {x x' : X} (p : x ≡ x') {a : A(f x)}
              → transport (A ∘ f) p ≡ transport A (ap f p)
transport-ap' A f refl = refl

nat-transport : {X : 𝓤 ̇} {A : X → 𝓥 ̇} {B : X → 𝓦 ̇}
                (f : (x : X) → A x → B x) {x y : X} (p : x ≡ y) {a : A x}
              → f y (transport A p a) ≡ transport B p (f x a)
nat-transport f refl = refl

transport-fam : {X : 𝓤 ̇} {Y : X → 𝓥 ̇} (P : {x : X} → Y x → 𝓦 ̇)
               (x : X) (y : Y x) → P y → (x' : X) (r : x ≡ x') → P(transport Y r y)
transport-fam P x y p .x refl = p

transport-rel : {X : 𝓤 ̇} {Y : X → 𝓥 ̇} (_≺_ : {x : X} → Y x → Y x → 𝓦 ̇)
              → (a x : X) (b : Y a) (v : Y x) (p : a ≡ x)
              →  v ≺ transport Y p b
              → back-transport Y p v ≺ b
transport-rel _≺_ a .a b v refl = id

transport-rel' : {X : 𝓤 ̇} {Y : X → 𝓥 ̇} (_≺_ : {x : X} → Y x → Y x → 𝓦 ̇)
              → (a x : X) (b : Y a) (v : Y x) (r : x ≡ a)
              → transport Y r v ≺ b
              → v ≺ back-transport Y r b
transport-rel' _≺_ a .a b v refl = id

transport-const : {X : 𝓤 ̇} {Y : 𝓥 ̇} {x x' : X} {y : Y} (p : x ≡ x')
               → transport (λ (_ : X) → Y) p y ≡ y
transport-const refl = refl

apd' : {X : 𝓤 ̇} (A : X → 𝓥 ̇) (f : (x : X) → A x) {x y : X}
    (p : x ≡ y) → transport A p (f x) ≡ f y
apd' A f refl = refl

apd : {X : 𝓤 ̇} {A : X → 𝓥 ̇} (f : (x : X) → A x) {x y : X}
    (p : x ≡ y) → transport A p (f x) ≡ f y
apd = apd' _

ap-id-is-id : {X : 𝓤 ̇} {x y : X} (p : x ≡ y) → p ≡ ap id p
ap-id-is-id refl = refl

ap-comp : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y) {x y z : X} (p : x ≡ y) (q : y ≡ z)
       → ap f (p ∙ q) ≡ ap f p ∙ ap f q
ap-comp f refl refl = refl

ap-sym : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y) {x y : X} (p : x ≡ y)
       → (ap f p) ⁻¹ ≡ ap f (p ⁻¹)
ap-sym f refl = refl

ap-ap : {X : 𝓤 ̇} {Y : 𝓥 ̇} {Z : 𝓦 ̇} (f : X → Y) (g : Y → Z) {x x' : X} (r : x ≡ x')
     → ap g (ap f r) ≡ ap (g ∘ f) r
ap-ap {𝓤} {𝓥} {𝓦} {X} {Y} {Z} f g = J A (λ x → refl)
 where
  A : (x x' : X) → x ≡ x' → 𝓦 ̇
  A x x' r = ap g (ap f r) ≡ ap (g ∘ f) r

ap₂ : {X : 𝓤 ̇} {Y : 𝓥 ̇} {Z : 𝓦 ̇} (f : X → Y → Z) {x₀ x₁ : X} {y₀ y₁ : Y}
   → x₀ ≡ x₁ → y₀ ≡ y₁ → f x₀ y₀ ≡ f x₁ y₁
ap₂ f refl refl = refl

refl-left-neutral : {X : 𝓤 ̇} {x y : X} {p : x ≡ y} → refl ∙ p ≡ p
refl-left-neutral {𝓤} {X} {x} {_} {refl} = refl

refl-right-neutral : {X : 𝓤 ̇} {x y : X} (p : x ≡ y) → p ≡ p ∙ refl
refl-right-neutral p = refl

assoc : {X : 𝓤 ̇} {x y z t : X} (p : x ≡ y) (q : y ≡ z) (r : z ≡ t)
      → (p ∙ q) ∙ r ≡ p ∙ (q ∙ r)
assoc refl refl refl = refl

happly' : {X : 𝓤 ̇} {A : X → 𝓥 ̇} (f g : Π A) → f ≡ g → f ∼ g
happly' f g p x = ap (λ - → - x) p

happly : {X : 𝓤 ̇} {A : X → 𝓥 ̇} {f g : Π A} → f ≡ g → f ∼ g
happly = happly' _ _

sym-is-inverse : {X : 𝓤 ̇} {x y : X} (p : x ≡ y)
               → refl ≡ p ⁻¹ ∙ p
sym-is-inverse = J (λ x y p → refl ≡ p ⁻¹ ∙ p) (λ x → refl)

sym-is-inverse' : {X : 𝓤 ̇} {x y : X} (p : x ≡ y)
               → refl ≡ p ∙ p ⁻¹
sym-is-inverse' refl = refl

⁻¹-involutive : {X : 𝓤 ̇} {x y : X} (p : x ≡ y) → (p ⁻¹)⁻¹ ≡ p
⁻¹-involutive refl = refl

⁻¹-contravariant : {X : 𝓤 ̇} {x y : X} (p : x ≡ y) {z : X} (q : y ≡ z)
                → q ⁻¹ ∙ p ⁻¹ ≡ (p ∙ q)⁻¹
⁻¹-contravariant refl refl = refl

left-inverse : {X : 𝓤 ̇} {x y : X} (p : x ≡ y) → p ⁻¹ ∙ p ≡ refl
left-inverse {𝓤} {X} {x} {y} refl = refl

right-inverse : {X : 𝓤 ̇} {x y : X} (p : x ≡ y) → refl ≡ p ∙ p ⁻¹
right-inverse {𝓤} {X} {x} {y} refl = refl

cancel-left : {X : 𝓤 ̇} {x y z : X} {p : x ≡ y} {q r : y ≡ z}
            → p ∙ q ≡ p ∙ r → q ≡ r
cancel-left {𝓤} {X} {x} {y} {z} {p} {q} {r} s =
       q              ≡⟨ refl-left-neutral ⁻¹ ⟩
       refl ∙ q       ≡⟨ ap (λ - → - ∙ q) ((left-inverse p)⁻¹) ⟩
       (p ⁻¹ ∙ p) ∙ q ≡⟨ assoc (p ⁻¹) p q ⟩
       p ⁻¹ ∙ (p ∙ q) ≡⟨ ap (λ - → p ⁻¹ ∙ -) s ⟩
       p ⁻¹ ∙ (p ∙ r) ≡⟨ (assoc (p ⁻¹) p r)⁻¹ ⟩
       (p ⁻¹ ∙ p) ∙ r ≡⟨ ap (λ - → - ∙ r) (left-inverse p) ⟩
       refl ∙ r       ≡⟨ refl-left-neutral ⟩
       r ∎

homotopies-are-natural' : {X : 𝓤 ̇} {A : 𝓥 ̇} (f g : X → A) (H : f ∼ g) {x y : X} {p : x ≡ y}
                      → H x ∙ ap g p ∙ (H y)⁻¹ ≡ ap f p
homotopies-are-natural' f g H {x} {_} {refl} = trans-sym' (H x)

homotopies-are-natural : {X : 𝓤 ̇} {A : 𝓥 ̇} (f g : X → A) (H : f ∼ g) {x y : X} {p : x ≡ y}
                      → H x ∙ ap g p ≡ ap f p ∙ H y
homotopies-are-natural f g H {x} {_} {refl} = refl-left-neutral ⁻¹

to-×-≡ : {X : 𝓤 ̇} {Y : 𝓥 ̇} {x x' : X} {y y' : Y}
     → x ≡ x' → y ≡ y' → (x , y) ≡ (x' , y')
to-×-≡ refl refl = refl

to-×-≡' : {X : 𝓤 ̇} {Y : 𝓥 ̇} {z z' : X × Y}
     → (pr₁ z ≡ pr₁ z') × (pr₂ z ≡ pr₂ z') → z ≡ z'
to-×-≡' (refl , refl) = refl

from-×-≡' : {X : 𝓤 ̇} {Y : 𝓥 ̇} {z z' : X × Y}
     → z ≡ z' → (pr₁ z ≡ pr₁ z') × (pr₂ z ≡ pr₂ z' )
from-×-≡' refl = (refl , refl)

from-Σ-≡ : {X : 𝓤 ̇} {Y : X → 𝓥 ̇} {σ τ : Σ Y} (r : σ ≡ τ)
          → Σ \(p : pr₁ σ ≡ pr₁ τ) → transport Y p (pr₂ σ) ≡ (pr₂ τ)
from-Σ-≡ refl = refl , refl

from-Σ-≡' : {X : 𝓤 ̇} {Y : X → 𝓥 ̇} {u v : Σ Y} (r : u ≡ v)
          → transport Y (ap pr₁ r) (pr₂ u) ≡ (pr₂ v)
from-Σ-≡' {𝓤} {𝓥} {X} {Y} {u} {v} = J A (λ u → refl) {u} {v}
 where
  A : (u v : Σ Y) → u ≡ v → 𝓥 ̇
  A u v r = transport Y (ap pr₁ r) (pr₂ u) ≡ (pr₂ v)

to-Σ-≡ : {X : 𝓤 ̇} {A : X → 𝓥 ̇} {σ τ : Σ A}
          → (Σ \(p : pr₁ σ ≡ pr₁ τ) → transport A p (pr₂ σ) ≡ pr₂ τ)
          → σ ≡ τ
to-Σ-≡ (refl , refl) = refl

ap-pr₁-to-Σ-≡ : {X : 𝓤 ̇} {A : X → 𝓥 ̇} {σ τ : Σ A}
                (w : Σ \(p : pr₁ σ ≡ pr₁ τ) → transport A p (pr₂ σ) ≡ pr₂ τ)
              → ap pr₁ (to-Σ-≡ w) ≡ pr₁ w
ap-pr₁-to-Σ-≡ (refl , refl) = refl

to-Σ-≡' : {X : 𝓤 ̇} {Y : X → 𝓥 ̇} {x : X} {y y' : Y x}
        → y ≡ y' → _≡_ {_} {Σ Y} (x , y) (x , y')
to-Σ-≡' {𝓤} {𝓥} {X} {Y} {x} = ap (λ - → (x , -))

fromto-Σ-≡ : {X : 𝓤 ̇} {A : X → 𝓥 ̇} {σ τ : Σ A} (w : Σ \(p : pr₁ σ ≡ pr₁ τ) → transport A p (pr₂ σ) ≡ pr₂ τ)
           → from-Σ-≡ (to-Σ-≡ w) ≡ w
fromto-Σ-≡ (refl , refl) = refl

tofrom-Σ-≡ : {X : 𝓤 ̇} {A : X → 𝓥 ̇} {σ τ : Σ A} (r : σ ≡ τ)
           → to-Σ-≡ (from-Σ-≡ r) ≡ r
tofrom-Σ-≡ refl = refl

\end{code}
