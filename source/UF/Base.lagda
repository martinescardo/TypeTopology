Martin Escardo

This file needs reorganization and clean-up.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module UF.Base where

open import MLTT.Spartan

Nat : {X : 𝓤 ̇ } → (X → 𝓥 ̇ ) → (X → 𝓦 ̇ ) → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
Nat A B = ∀ x → A x → B x

Nats-are-natural : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (B : X → 𝓦 ̇ )
                   (τ : Nat A B) {x y : X} (p : x ＝ y)
                 → τ y ∘ transport A p ＝ transport B p ∘ τ x
Nats-are-natural A B τ refl = refl

Nats-are-natural-∼ : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (B : X → 𝓦 ̇ )
                     (τ : Nat A B) {x y : X} (p : x ＝ y)
                   → τ y ∘ transport A p ∼ transport B p ∘ τ x
Nats-are-natural-∼ A B τ refl a = refl

NatΣ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {B : X → 𝓦 ̇ } → Nat A B → Σ A → Σ B
NatΣ ζ (x , a) = (x , ζ x a)

NatΠ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {B : X → 𝓦 ̇ } → Nat A B → Π A → Π B
NatΠ f g x = f x (g x) -- (S combinator from combinatory logic!)

ΠΣ-distr : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {P : (x : X) → A x → 𝓦 ̇ }
         → (Π x ꞉ X , Σ a ꞉ A x , P x a)
         → Σ f ꞉ Π A , Π x ꞉ X , P x (f x)
ΠΣ-distr φ = (λ x → pr₁ (φ x)) , λ x → pr₂ (φ x)

ΠΣ-distr⁻¹ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {P : (x : X) → A x → 𝓦 ̇ }
           → (Σ f ꞉ Π A , Π x ꞉ X , P x (f x))
           → Π x ꞉ X , Σ a ꞉ A x , P x a
ΠΣ-distr⁻¹ (f , φ) x = f x , φ x

_≈_ : {X : 𝓤 ̇ } {x : X} {A : X → 𝓥 ̇ } → Nat (Id x) A → Nat (Id x) A → 𝓤 ⊔ 𝓥 ̇
η ≈ θ = ∀ y → η y ∼ θ y

ap-const : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (y : Y) {x x' : X} (p : x ＝ x')
         → ap (λ _ → y) p ＝ refl
ap-const y refl = refl

transport-fiber : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                  (x x' : X) (y : Y) (p : x ＝ x') (q : f x ＝ y)
                → transport (λ - → f - ＝ y) p q ＝ ap f (p ⁻¹) ∙ q
transport-fiber f x x' y refl refl = refl

transport₂ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (A : X → Y → 𝓦 ̇ )
             {x x' : X} {y y' : Y}
             → x ＝ x' → y ＝ y' → A x y → A x' y'
transport₂ A refl refl = id

transport₃ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } (A : X → Y → Z → 𝓣 ̇ )
             {x x' : X} {y y' : Y} {z z' : Z}
           → x ＝ x' → y ＝ y' → z ＝ z' → A x y z → A x' y' z'
transport₃ A refl refl refl = id

transport₂⁻¹ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (A : X → Y → 𝓦 ̇ )
               {x x' : X} {y y' : Y}
             → x ＝ x' → y ＝ y' → A x' y' → A x y
transport₂⁻¹ A refl refl = id

Idtofun : {X Y : 𝓤 ̇ } → X ＝ Y → X → Y
Idtofun = transport id

Idtofun-retraction : {X Y : 𝓤 ̇ } (p : X ＝ Y) → Idtofun p ∘ Idtofun (p ⁻¹) ∼ id
Idtofun-retraction refl _ = refl

Idtofun-section : {X Y : 𝓤 ̇ } (p : X ＝ Y) → Idtofun (p ⁻¹) ∘ Idtofun p ∼ id
Idtofun-section refl _ = refl

Idtofun⁻¹ : {X Y : 𝓤 ̇ } → X ＝ Y → Y → X
Idtofun⁻¹ = transport⁻¹ id

forth-and-back-transport : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
                           {x y : X} (p : x ＝ y) {a : A x}
                         → transport⁻¹ A p (transport A p a) ＝ a
forth-and-back-transport refl = refl

back-and-forth-transport : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
                           {x y : X} (p : y ＝ x) {a : A x}
                         → transport A p (transport⁻¹ A p a) ＝ a
back-and-forth-transport refl = refl

transport⁻¹-is-pre-comp : {X X' : 𝓤 ̇ } {Y : 𝓥 ̇ } (p : X ＝ X') (g : X' → Y)
                        → transport⁻¹ (λ - → - → Y) p g ＝ g ∘ Idtofun p
transport⁻¹-is-pre-comp refl g = refl

transport-is-pre-comp : {X X' : 𝓤 ̇ } {Y : 𝓥 ̇ } (p : X ＝ X') (g : X → Y)
                      → transport (λ - → - → Y) p g ＝ g ∘ Idtofun (p ⁻¹)
transport-is-pre-comp refl g = refl

trans-sym : {X : 𝓤 ̇ } {x y : X} (r : x ＝ y) → r ⁻¹ ∙ r ＝ refl
trans-sym refl = refl

trans-sym' : {X : 𝓤 ̇ } {x y : X} (r : x ＝ y) → r ∙ r ⁻¹ ＝ refl
trans-sym' refl = refl

transport-× : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (B : X → 𝓦 ̇ )
              {x y : X} {c : A x × B x} (p : x ＝ y)
            → transport (λ x → A x × B x) p c
            ＝ (transport A p (pr₁ c) , transport B p (pr₂ c))
transport-× A B refl = refl

transport-×₄ : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (B : X → 𝓦 ̇ ) (C : X → 𝓣 ̇ ) (D : X → 𝓣' ̇ )
               {x y : X} {(a , b , c , d) : A x × B x × C x × D x} (p : x ＝ y)
             → transport (λ x → A x × B x × C x × D x) p (a , b , c , d)
             ＝ (transport A p a , transport B p b , transport C p c , transport D p d)
transport-×₄ _ _ _ _ refl = refl

transportd : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (B : (x : X) → A x → 𝓦 ̇ )
             {x : X}  (a : A x) {y : X} (p : x ＝ y)
           → B x a
           → B y (transport A p a)
transportd A B a refl = id

transport-Σ : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (B : (x : X) → A x → 𝓦 ̇ )
              {x : X} (y : X) (p : x ＝ y) (a : A x) {b : B x a}
            → transport (λ - → Σ a ꞉ A - , B - a) p (a , b)
            ＝ transport A p a , transportd A B a p b
transport-Σ A B {x} x refl a = refl

transport-∙ : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ )
              {x y z : X} (q : x ＝ y) (p : y ＝ z) {a : A x}
            → transport A (q ∙ p) a ＝ transport A p (transport A q a)
transport-∙ A refl refl = refl

transport-∙' : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ )
               {x y z : X} (q : x ＝ y) (p : y ＝ z)
             → transport A (q ∙ p) ＝ transport A p ∘ transport A q
transport-∙' A refl refl = refl

transport-ap : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (A : Y → 𝓦 ̇ )
               (f : X → Y) {x x' : X} (p : x ＝ x') {a : A(f x)}
             → transport (A ∘ f) p a ＝ transport A (ap f p) a
transport-ap A f refl = refl

transport-ap' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (A : Y → 𝓦 ̇ )
                (f : X → Y) {x x' : X} (p : x ＝ x')
              → transport (A ∘ f) p ＝ transport A (ap f p)
transport-ap' A f refl = refl

nat-transport : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {B : X → 𝓦 ̇ }
                (f : Nat A B) {x y : X} (p : x ＝ y) {a : A x}
              → f y (transport A p a) ＝ transport B p (f x a)
nat-transport f refl = refl

transport-fam : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } (P : {x : X} → Y x → 𝓦 ̇ )
               (x : X) (y : Y x) → P y → (x' : X) (r : x ＝ x') → P (transport Y r y)
transport-fam P x y p x refl = p

transport-left-rel : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } (_≺_ : {x : X} → Y x → Y x → 𝓦 ̇ )
                   → (a x : X) (b : Y a) (v : Y x) (r : x ＝ a)
                   → transport Y r v ≺ b
                   → v ≺ transport⁻¹ Y r b
transport-left-rel _≺_ a a b v refl = id

transport-right-rel : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } (_≺_ : {x : X} → Y x → Y x → 𝓦 ̇ )
                    → (a x : X) (b : Y a) (v : Y x) (p : a ＝ x)
                    →  v ≺ transport Y p b
                    → transport⁻¹ Y p v ≺ b
transport-right-rel _≺_ a a b v refl = id

transport⁻¹-right-rel : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } (_≺_ : {x : X} → Y x → Y x → 𝓦 ̇ )
                      → (a x : X) (b : Y a) (v : Y x) (r : x ＝ a)
                      → v ≺ transport⁻¹ Y r b
                      → transport Y r v ≺ b
transport⁻¹-right-rel _≺_ a a b v refl = id

transport⁻¹-left-rel : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } (_≺_ : {x : X} → Y x → Y x → 𝓦 ̇ )
                     → (a x : X) (b : Y a) (v : Y x) (p : a ＝ x)
                     → transport⁻¹ Y p v ≺ b
                     → v ≺ transport Y p b
transport⁻¹-left-rel _≺_ a a b v refl = id

transport-const : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {x x' : X} {y : Y} (p : x ＝ x')
                → transport (λ (_ : X) → Y) p y ＝ y
transport-const refl = refl

apd' : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (f : (x : X) → A x)
       {x y : X} (p : x ＝ y)
     → transport A p (f x) ＝ f y
apd' A f refl = refl

apd : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } (f : (x : X) → A x)
      {x y : X} (p : x ＝ y)
    → transport A p (f x) ＝ f y
apd = apd' _

ap-id-is-id : {X : 𝓤 ̇ } {x y : X} (p : x ＝ y) → ap id p ＝ p
ap-id-is-id refl = refl

ap-id-is-id' : {X : 𝓤 ̇ } {x y : X} (p : x ＝ y) → p ＝ ap id p
ap-id-is-id' refl = refl

ap-∙ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) {x y z : X} (p : x ＝ y) (q : y ＝ z)
     → ap f (p ∙ q) ＝ ap f p ∙ ap f q
ap-∙ f refl refl = refl

ap-∙' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) {x y : X} (p : x ＝ y)
      → ap f (p ⁻¹) ∙ ap f p ＝ refl
ap-∙' f refl = refl

ap-sym : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) {x y : X} (p : x ＝ y)
       → (ap f p) ⁻¹ ＝ ap f (p ⁻¹)
ap-sym f refl = refl

ap-ap : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } (f : X → Y) (g : Y → Z)
        {x x' : X} (r : x ＝ x')
      → ap g (ap f r) ＝ ap (g ∘ f) r
ap-ap {𝓤} {𝓥} {𝓦} {X} {Y} {Z} f g refl = refl

ap₂ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } (f : X → Y → Z) {x₀ x₁ : X} {y₀ y₁ : Y}
    → x₀ ＝ x₁
    → y₀ ＝ y₁
    → f x₀ y₀ ＝ f x₁ y₁
ap₂ f refl refl = refl

\end{code}

Added by Ettore Aldrovandi, Sun Sep 24 00:35:12 UTC 2023

\begin{code}

ap₂-refl-left : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } (f : X → Y → Z) {x : X} {y₀ y₁ : Y}
                (q : y₀ ＝ y₁)
              → ap₂ f refl q ＝ ap (f x) q
ap₂-refl-left f refl = refl

ap₂-refl-left' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } (f : X → Y → Z) {x : X} {y₀ y₁ : Y}
                 (q : y₀ ＝ y₁)
               → ap (f x) q ＝ ap₂ f refl q
ap₂-refl-left' f refl = refl

ap₂-refl-right : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } (f : X → Y → Z) {x₀ x₁ : X} {y : Y}
                 (p : x₀ ＝ x₁)
               → ap₂ f p refl ＝ ap (λ v → f v y) p
ap₂-refl-right f refl = refl

ap₂-refl-right' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } (f : X → Y → Z) {x₀ x₁ : X} {y : Y}
                  (p : x₀ ＝ x₁)
                → ap (λ v → f v y) p ＝ ap₂ f p refl
ap₂-refl-right' f refl = refl

ap₂-∙ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } (f : X → Y → Z) {x₀ x₁ x₂ : X} {y₀ y₁ y₂ : Y}
        (p₀ : x₀ ＝ x₁) (p₁ : x₁ ＝ x₂)
        (q₀ : y₀ ＝ y₁) (q₁ :  y₁ ＝ y₂)
      → ap₂ f (p₀ ∙ p₁) (q₀ ∙ q₁) ＝ ap₂ f p₀ q₀ ∙ ap₂ f p₁ q₁
ap₂-∙ f refl refl refl refl = refl

\end{code}

\begin{code}

ap₃ : {W : 𝓣 ̇ } {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
      (f : W → X → Y → Z) {w₀ w₁ : W} {x₀ x₁ : X} {y₀ y₁ : Y}
    → w₀ ＝ w₁ → x₀ ＝ x₁ → y₀ ＝ y₁ → f w₀ x₀ y₀ ＝ f w₁ x₁ y₁
ap₃ f refl refl refl = refl

\end{code}

Added by Ettore Aldrovandi, Sun Sep 24 00:35:12 UTC 2023

\begin{code}

ap₃-∙ : {W : 𝓣 ̇ } {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
        (f : W → X → Y → Z) {w₀ w₁ w₂ : W} {x₀ x₁ x₂ : X} {y₀ y₁ y₂ : Y}
        (r₀ : w₀ ＝ w₁) (r₁ : w₁ ＝ w₂)
        (p₀ : x₀ ＝ x₁) (p₁ : x₁ ＝ x₂)
        (q₀ : y₀ ＝ y₁) (q₁ : y₁ ＝ y₂)
      → ap₃ f (r₀ ∙ r₁) (p₀ ∙ p₁) (q₀ ∙ q₁) ＝ ap₃ f r₀ p₀ q₀ ∙ ap₃ f r₁ p₁ q₁
ap₃-∙ f refl refl refl refl refl refl = refl

\end{code}

A variation of the above due to Jakub Opršal.

\begin{code}

ap₃-∙' : {W : 𝓣 ̇ } {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
         (f : W → X → Y → Z) {w₀ w₁ w₂ : W} {x₀ x₁ x₂ : X} {y₀ y₁ y₂ : Y}
         (r₀ : w₀ ＝ w₁) (r₁ : w₁ ＝ w₂) {r₂ : w₀ ＝ w₂}
         (p₀ : x₀ ＝ x₁) (p₁ : x₁ ＝ x₂) {p₂ : x₀ ＝ x₂}
         (q₀ : y₀ ＝ y₁) (q₁ : y₁ ＝ y₂) {q₂ : y₀ ＝ y₂}
         (e₀ : r₂ ＝ r₀ ∙ r₁) (e₁ : p₂ ＝ p₀ ∙ p₁) (e₂ : q₂ ＝ q₀ ∙ q₁)
      → ap₃ f r₂ p₂ q₂ ＝ ap₃ f r₀ p₀ q₀ ∙ ap₃ f r₁ p₁ q₁
ap₃-∙' f r₀ r₁ p₀ p₁ q₀ q₁ refl refl refl = ap₃-∙ f r₀ r₁ p₀ p₁ q₀ q₁

\end{code}

\begin{code}

ap₃-refl-left : {W : 𝓣 ̇ } {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
                (f : W → X → Y → Z) {w : W} {x₀ x₁ : X} {y₀ y₁ : Y}
                (p : x₀ ＝ x₁) (q : y₀ ＝ y₁)
              → ap₃ f refl p q ＝ ap₂ (f w) p q
ap₃-refl-left f refl refl = refl

ap₃-refl-mid : {W : 𝓣 ̇ } {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
               (f : W → X → Y → Z) {w₀ w₁ : W} {x : X} {y₀ y₁ : Y}
               (r : w₀ ＝ w₁) (q : y₀ ＝ y₁)
              → ap₃ f r refl q ＝ ap₂ (λ w y → f w x y) r q
ap₃-refl-mid f refl refl = refl

ap₃-refl-right : {W : 𝓣 ̇ } {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
                 (f : W → X → Y → Z) {w₀ w₁ : W} {x₀ x₁ : X} {y : Y}
                 (r : w₀ ＝ w₁) (p : x₀ ＝ x₁)
               → ap₃ f r p refl ＝ ap₂ (λ w x → f w x y) r p
ap₃-refl-right f refl refl = refl

\end{code}

ap₃ commutes with inverting paths (code due to Jakub Opršal).

\begin{code}

ap₃-⁻¹ : {W : 𝓣 ̇ } {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
         (f : W → X → Y → Z) {w₀ w₁ : W} {x₀ x₁ : X} {y₀ y₁ : Y}
         (r : w₀ ＝ w₁) (p : x₀ ＝ x₁) (q : y₀ ＝ y₁)
       → ap₃ f (r ⁻¹) (p ⁻¹) (q ⁻¹) ＝ (ap₃ f r p q) ⁻¹
ap₃-⁻¹ f refl refl refl = refl

\end{code}

End of addition.

\begin{code}

refl-left-neutral : {X : 𝓤 ̇ } {x y : X} {p : x ＝ y}
                  → refl ∙ p ＝ p
refl-left-neutral {𝓤} {X} {x} {_} {refl} = refl

refl-right-neutral : {X : 𝓤 ̇ } {x y : X} (p : x ＝ y) → p ＝ p ∙ refl
refl-right-neutral p = refl

∙assoc : {X : 𝓤 ̇ } {x y z t : X} (p : x ＝ y) (q : y ＝ z) (r : z ＝ t)
       → (p ∙ q) ∙ r ＝ p ∙ (q ∙ r)
∙assoc refl refl refl = refl

happly' : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } (f g : Π A) → f ＝ g → f ∼ g
happly' f g p x = ap (λ - → - x) p

happly : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {f g : Π A} → f ＝ g → f ∼ g
happly = happly' _ _

implicit-happly : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
                  {f g : {x : X} → A x}
                → (λ {x} → f {x}) ＝ g
                → (x : X) → f {x} ＝ g {x}
implicit-happly {𝓤} {𝓥} {X} {A} {f} {g} p x = ap (λ - → - {x}) p

sym-is-inverse : {X : 𝓤 ̇ } {x y : X} (p : x ＝ y)
               → refl ＝ p ⁻¹ ∙ p
sym-is-inverse refl = refl

sym-is-inverse' : {X : 𝓤 ̇ } {x y : X} (p : x ＝ y)
                → refl ＝ p ∙ p ⁻¹
sym-is-inverse' refl = refl

⁻¹-involutive : {X : 𝓤 ̇ } {x y : X} (p : x ＝ y) → (p ⁻¹)⁻¹ ＝ p
⁻¹-involutive refl = refl

⁻¹-contravariant : {X : 𝓤 ̇ } {x y : X} (p : x ＝ y) {z : X} (q : y ＝ z)
                 → q ⁻¹ ∙ p ⁻¹ ＝ (p ∙ q)⁻¹
⁻¹-contravariant refl refl = refl

left-inverse : {X : 𝓤 ̇ } {x y : X} (p : x ＝ y) → p ⁻¹ ∙ p ＝ refl
left-inverse {𝓤} {X} {x} {y} refl = refl

right-inverse : {X : 𝓤 ̇ } {x y : X} (p : x ＝ y) → refl ＝ p ∙ p ⁻¹
right-inverse {𝓤} {X} {x} {y} refl = refl

cancel-right
 : {X : 𝓤 ̇ } {x y z : X}
 → (p : x ＝ y) (q : x ＝ y) (r : y ＝ z)
 → p ∙ r ＝ q ∙ r
 → p ＝ q
cancel-right refl refl refl refl = refl

cancel-left : {X : 𝓤 ̇ } {x y z : X} {p : x ＝ y} {q r : y ＝ z}
            → p ∙ q ＝ p ∙ r
            → q ＝ r
cancel-left {𝓤} {X} {x} {y} {z} {p} {q} {r} s =
       q              ＝⟨ refl-left-neutral ⁻¹ ⟩
       refl ∙ q       ＝⟨ ap (λ - → - ∙ q) ((left-inverse p)⁻¹) ⟩
       (p ⁻¹ ∙ p) ∙ q ＝⟨ ∙assoc (p ⁻¹) p q ⟩
       p ⁻¹ ∙ (p ∙ q) ＝⟨ ap (λ - → p ⁻¹ ∙ -) s ⟩
       p ⁻¹ ∙ (p ∙ r) ＝⟨ (∙assoc (p ⁻¹) p r)⁻¹ ⟩
       (p ⁻¹ ∙ p) ∙ r ＝⟨ ap (λ - → - ∙ r) (left-inverse p) ⟩
       refl ∙ r       ＝⟨ refl-left-neutral ⟩
       r              ∎

\end{code}

It is shorter to prove the above using pattern matching on refl, of course.

\begin{code}

cancel₄ : {X : 𝓤 ̇ } {x y z : X} (p : x ＝ y) (q : z ＝ y)
        → (p ∙ q ⁻¹) ∙ (q ∙ p ⁻¹) ＝ refl
cancel₄ refl refl = refl

\end{code}

Added 24 February 2020 by Tom de Jong.

\begin{code}

cancel-left-＝ : {X : 𝓤 ̇ } {x y z : X} {p : x ＝ y} {q r : y ＝ z}
              → (p ∙ q ＝ p ∙ r) ＝ (q ＝ r)
cancel-left-＝ {𝓤} {X} {x} {y} {z} {refl} {q} {r} =
 ap₂ (λ u v → u ＝ v) refl-left-neutral refl-left-neutral

\end{code}

End of addition.

\begin{code}

homotopies-are-natural' : {X : 𝓤 ̇ } {A : 𝓥 ̇ }
                          (f g : X → A)
                          (H : f ∼ g)
                          {x y : X}
                          {p : x ＝ y}
                        → H x ∙ ap g p ∙ (H y)⁻¹ ＝ ap f p
homotopies-are-natural' f g H {x} {_} {refl} = trans-sym' (H x)

homotopies-are-natural'' : {X : 𝓤 ̇ } {A : 𝓥 ̇ }
                           (f g : X → A)
                           (H : f ∼ g)
                           {x y : X}
                           {p : x ＝ y}
                         → (H x) ⁻¹ ∙ ap f p ∙ H y ＝ ap g p
homotopies-are-natural'' f g H {x} {_} {refl} = trans-sym (H x)

homotopies-are-natural : {X : 𝓤 ̇ } {A : 𝓥 ̇ }
                         (f g : X → A)
                         (H : f ∼ g)
                         {x y : X}
                         {p : x ＝ y}
                       → H x ∙ ap g p ＝ ap f p ∙ H y
homotopies-are-natural f g H {x} {_} {refl} = refl-left-neutral ⁻¹

to-×-＝ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {x x' : X} {y y' : Y}
         → x ＝ x'
         → y ＝ y'
         → (x , y) ＝ (x' , y')
to-×-＝ refl refl = refl

to-×-＝' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {z z' : X × Y}
          → (pr₁ z ＝ pr₁ z') × (pr₂ z ＝ pr₂ z')
          → z ＝ z'
to-×-＝' (refl , refl) = refl

from-×-＝' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {z z' : X × Y}
            → z ＝ z'
            → (pr₁ z ＝ pr₁ z') × (pr₂ z ＝ pr₂ z' )
from-×-＝' refl = (refl , refl)

tofrom-×-＝ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
              {z z' : X × Y} (p : z ＝ z')
            → p ＝ to-×-＝ (pr₁ (from-×-＝' p)) (pr₂ (from-×-＝' p))
tofrom-×-＝ refl = refl

from-Σ-＝' : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {u v : Σ Y} (r : u ＝ v)
           → transport Y (ap pr₁ r) (pr₂ u) ＝ (pr₂ v)
from-Σ-＝' {𝓤} {𝓥} {X} {Y} {u} {v} refl = refl

from-Σ-＝ : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {σ τ : Σ Y} (r : σ ＝ τ)
          → Σ p ꞉ pr₁ σ ＝ pr₁ τ , transport Y p (pr₂ σ) ＝ (pr₂ τ)
from-Σ-＝ r = (ap pr₁ r , from-Σ-＝' r)

to-Σ-＝ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {σ τ : Σ A}
        → (Σ p ꞉ pr₁ σ ＝ pr₁ τ , transport A p (pr₂ σ) ＝ pr₂ τ)
        → σ ＝ τ
to-Σ-＝ (refl , refl) = refl

ap-pr₁-to-Σ-＝ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {σ τ : Σ A}
                 (w : Σ p ꞉ pr₁ σ ＝ pr₁ τ , transport A p (pr₂ σ) ＝ pr₂ τ)
               → ap pr₁ (to-Σ-＝ w) ＝ pr₁ w
ap-pr₁-to-Σ-＝ (refl , refl) = refl

to-Σ-＝' : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {x : X} {y y' : Y x}
         → y ＝ y'
         → (x , y) ＝[ Σ Y ] (x , y')
to-Σ-＝' {𝓤} {𝓥} {X} {Y} {x} = ap (λ - → (x , -))

fromto-Σ-＝ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
              {σ τ : Σ A}
              (w : Σ p ꞉ pr₁ σ ＝ pr₁ τ , transport A p (pr₂ σ) ＝ pr₂ τ)
            → from-Σ-＝ (to-Σ-＝ w) ＝ w
fromto-Σ-＝ (refl , refl) = refl

tofrom-Σ-＝ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {σ τ : Σ A} (r : σ ＝ τ)
            → to-Σ-＝ (from-Σ-＝ r) ＝ r
tofrom-Σ-＝ refl = refl

ap-pr₁-to-×-＝ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {z t : X × Y}
              → (p₁ : pr₁ z ＝ pr₁ t)
              → (p₂ : pr₂ z ＝ pr₂ t)
              → ap pr₁ (to-×-＝ p₁ p₂) ＝ p₁
ap-pr₁-to-×-＝ refl refl = refl

ap-pr₂-to-×-＝ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {z t : X × Y}
              → (p₁ : pr₁ z ＝ pr₁ t)
              → (p₂ : pr₂ z ＝ pr₂ t)
              → ap pr₂ (to-×-＝ p₁ p₂) ＝ p₂
ap-pr₂-to-×-＝ refl refl = refl

\end{code}

Added by Tom de Jong
22 March 2021:

\begin{code}

ap-pr₁-refl-lemma : {X : 𝓤 ̇ } (Y : X → 𝓥 ̇ )
                    {x : X} {y y' : Y x}
                    (w : (x , y) ＝[ Σ Y ] (x , y'))
                  → ap pr₁ w ＝ refl
                  → y ＝ y'
ap-pr₁-refl-lemma Y {x} {y} {y'} w p = γ (ap pr₁ w) p ∙ h
 where
  γ : (r : x ＝ x) → (r ＝ refl) → y ＝ transport Y r y
  γ r refl = refl
  h : transport Y (ap pr₁ w) y ＝ y'
  h = from-Σ-＝' w

transport-along-＝ : {X : 𝓤 ̇ } {x y : X} (q : x ＝ y) (p : x ＝ x)
                  → transport (λ - → - ＝ -) q p ＝ q ⁻¹ ∙ p ∙ q
transport-along-＝ refl p = (refl ⁻¹ ∙ (p ∙ refl) ＝⟨ refl              ⟩
                            refl ⁻¹ ∙ p          ＝⟨ refl-left-neutral ⟩
                            p                    ∎                     ) ⁻¹

transport-along-→ : {X : 𝓤 ̇ } (Y : X → 𝓥 ̇ ) (Z : X → 𝓦 ̇ )
                    {x y : X}
                    (p : x ＝ y) (f : Y x → Z x)
                  → transport (λ - → (Y - → Z -)) p f
                  ＝ transport Z p ∘ f ∘ transport Y (p ⁻¹)
transport-along-→ Y Z refl f = refl

\end{code}

A variation on the above where we replace the type family Z by just a type,
added 19 June 2026 by Tom de Jong.

\begin{code}

transport-along-→' : {A : 𝓤 ̇ } (B : A → 𝓥 ̇ ) {a₁ a₂ : A} (p : a₁ ＝ a₂) {X : 𝓦 ̇ }
                     (f : B a₁ → X)
                   → transport (λ - → B - → X) p f ＝ f ∘ transport B (p ⁻¹)
transport-along-→' B refl f = refl

\end{code}

Added by Ettore Aldrovandi
September 19, 2022:

\begin{code}

ap-refl : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) {x : X}
        → ap f (𝓻𝓮𝒻𝓵 x) ＝ 𝓻𝓮𝒻𝓵 (f x)
ap-refl f = refl

\end{code}

Added by Ian Ray 18th Jan 2025

\begin{code}

apd-to-ap : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) {x x' : X} (p : x ＝ x')
          → apd f p ＝ transport-const p ∙ ap f p
apd-to-ap f refl = refl

apd-from-ap : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) {x x' : X} (p : x ＝ x')
            → ap f p ＝ transport-const p ⁻¹ ∙ apd f p
apd-from-ap f refl = refl

\end{code}

We will also add some helpful path algebra lemmas. Note that pattern matching
is not helpful here since the path concatenation by definition associates to
the left: l ∙ q ∙ s ≡ (l ∙ q) ∙ s (where ≡ is definitional). So, as you will
see below, we have to reassociate before applying on the left.

\begin{code}

ap-on-left-is-assoc : {X : 𝓤 ̇ } {x y z z' w : X} (l : x ＝ y)
                      {p : y ＝ z} {q : y ＝ z'} {r : z ＝ w} {s : z' ＝ w}
                    → p ∙ r ＝ q ∙ s
                    → (l ∙ p) ∙ r ＝ (l ∙ q) ∙ s
ap-on-left-is-assoc l {p} {q} {r} {s} α = l ∙ p ∙ r   ＝⟨ ∙assoc l p r ⟩
                                          l ∙ (p ∙ r) ＝⟨ ap (l ∙_) α ⟩
                                          l ∙ (q ∙ s) ＝⟨ ∙assoc l q s ⁻¹ ⟩
                                          l ∙ q ∙ s   ∎

ap-on-left-is-assoc' : {X : 𝓤 ̇ } {x y z z' : X} (l : x ＝ y)
                       (p : y ＝ z') (q : y ＝ z) (s : z ＝ z')
                     → p ＝ q ∙ s
                     → l ∙ p ＝ (l ∙ q) ∙ s
ap-on-left-is-assoc' l p q s α = l ∙ p        ＝⟨ ap (l ∙_) α ⟩
                                 l ∙ (q ∙ s)  ＝⟨ ∙assoc l q s ⁻¹ ⟩
                                 l ∙ q ∙ s    ∎

ap-on-left-is-assoc'' : {X : 𝓤 ̇ } {x y z z' : X} (l : x ＝ y)
                        (p : y ＝ z) (q : y ＝ z') (s : z ＝ z')
                      → p ∙ s ＝ q
                      → (l ∙ p) ∙ s ＝ l ∙ q
ap-on-left-is-assoc'' l p q s α =
 ap-on-left-is-assoc' l q p s (α ⁻¹) ⁻¹

ap-left-inverse : {X : 𝓤 ̇ } {x y z : X} (l : x ＝ y)
                  {p : x ＝ z} {q : y ＝ z}
                → p ＝ l ∙ q
                → l ⁻¹ ∙ p ＝ q
ap-left-inverse l {p} {q} α =
 l ⁻¹ ∙ p     ＝⟨ ap-on-left-is-assoc' (l ⁻¹) p l q α ⟩
 l ⁻¹ ∙ l ∙ q ＝⟨ ap (_∙ q) (left-inverse l) ⟩
 refl ∙ q     ＝⟨ refl-left-neutral ⟩
 q            ∎

ap-left-inverse' : {X : 𝓤 ̇ } {x y z : X} (l : x ＝ y)
                   {p : x ＝ z} {q : y ＝ z}
                 → l ⁻¹ ∙ p ＝ q
                 → p ＝ l ∙ q
ap-left-inverse' l {p} {q} α =
 p            ＝⟨ refl-left-neutral ⁻¹ ⟩
 refl ∙ p     ＝⟨ ap (_∙ p) (sym-is-inverse' l) ⟩
 l ∙ l ⁻¹ ∙ p ＝⟨ ap-on-left-is-assoc'' l (l ⁻¹) q p α ⟩
 l ∙ q        ∎

ap-right-inverse : {X : 𝓤 ̇ } {x y z : X} (r : y ＝ z)
                   {p : x ＝ z} {q : x ＝ y}
                 → p ＝ q ∙ r
                 → p ∙ r ⁻¹ ＝ q
ap-right-inverse refl α = α

ap-right-inverse' : {X : 𝓤 ̇ } {x y z : X} (r : y ＝ z)
                    {p : x ＝ z} {q : x ＝ y}
                  → p ∙ r ⁻¹ ＝ q
                  → p ＝ q ∙ r
ap-right-inverse' refl α = α

\end{code}

We will also add a result that says:
given two maps, a path in the domain and a path in the codomain between the
maps at the left endpoint then applying one map to the domain path and
transporting along that path at the codomain path is the same as following the
codomain path and applying the other map to the domain path.
(this may already exist!)

\begin{code}

transport-after-ap
 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {x x' : X}
 → (p : x ＝ x')
 → (s s' : X → Y)
 → (q : s x ＝ s' x)
 → ap s p ∙ transport (λ - → s - ＝ s' -) p q ＝ q ∙ ap s' p
transport-after-ap refl s s' q =
 ap s refl ∙ q  ＝⟨ ap (_∙ q) (ap-refl s) ⟩
 refl ∙ q       ＝⟨ refl-left-neutral ⟩
 q ∙ refl       ＝⟨ ap (q ∙_) (ap-refl s') ⟩
 q ∙ ap s' refl ∎

transport-after-ap'
 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {x x' : X}
 → (p : x ＝ x')
 → (s s' : X → Y)
 → (q : s x ＝ s' x)
 → transport (λ - → s - ＝ s' -) p q ＝ ap s p ⁻¹ ∙ q ∙ ap s' p
transport-after-ap' refl s s' q =
 q                             ＝⟨ refl-left-neutral ⁻¹ ⟩
 refl ∙ q                      ＝⟨refl⟩
 ap s refl ⁻¹ ∙ q ∙ ap s' refl ∎

\end{code}

A version of transport-after-ap' for dependent functions,
added 19 June 2026 by Tom de Jong.

\begin{code}

transport-after-ap'-dependent
 : {X : 𝓤 ̇ } {x₁ x₂ : X} {Y : X → 𝓥 ̇ } (g h : Π Y)
   (p : x₁ ＝ x₂) (q : g x₁ ＝ h x₁)
 → transport (λ - → g - ＝ h -) p q
   ＝ apd g p ⁻¹ ∙ ap (transport Y p) q ∙ apd h p
transport-after-ap'-dependent g h refl q =
 q                              ＝⟨ ap-id-is-id q ⁻¹ ⟩
 ap id q                        ＝⟨refl⟩
 ap id q ∙ refl                 ＝⟨refl⟩
 ap id q ∙ apd h refl           ＝⟨ refl-left-neutral ⁻¹ ⟩
 refl ⁻¹ ∙ ap id q ∙ apd h refl ∎

\end{code}

Moved here (from AlgebraicStructuresForcingSethood)
on 4 June 2026 by Tom de Jong.

Additions, notably the diagrams, from the same place due to Martin Escardo, were
integrated here by Tom de Jong on 8 June 2026.

Transporting along the identity type ＝ establishes that ＝ is a
congruence. Duplicating two of the arguments we obtain conjugation of loops.

The congruence witness enjoys various coherence properties, as shown below.
These are used in several files in the AlgebraicStructuresForcingSethood folder.

`＝-congr h₁ h₂ p` transports a path p : a ＝ b across a commutative
square to obtain a path x ＝ y:

    a ═════ p ════ b
    ║              ║
   h₁              h₂
    ║              ║
    x ════════════ y
           ?

The resulting path is sym h₁ ∙ p ∙ h₂.  Definitionally, when
h₁ = h₂ = refl, the square degenerates and we recover p.

\begin{code}

＝-congr : {A : 𝓤 ̇ } {a b x y : A} → a ＝ x → b ＝ y → a ＝ b → x ＝ y
＝-congr = transport₂ _＝_

conjugate-loop : {A : 𝓤 ̇ } {a b : A} → a ＝ b → a ＝ a → b ＝ b
conjugate-loop p = ＝-congr p p

ap-＝-congr
 : {A : 𝓤 ̇ } {B : 𝓥 ̇ } (f : A → B) {a b x y : A}
 → (α : a ＝ x) (β : b ＝ y) (p : a ＝ b)
 → ap f (＝-congr α β p)
   ＝ ＝-congr (ap f α) (ap f β) (ap f p)
ap-＝-congr f refl refl p = refl

ap-conjugate-loop
 : {A : 𝓤 ̇ } {B : 𝓥 ̇ } (f : A → B) {a b : A}
 → (p : a ＝ b) (l : a ＝ a)
 → ap f (conjugate-loop p l) ＝ conjugate-loop (ap f p) (ap f l)
ap-conjugate-loop f p l = ap-＝-congr f p p l

conjugate-loop-conjugates : {A : 𝓤 ̇ } {a b : A} (p : a ＝ b) (l : a ＝ a)
                          → conjugate-loop p l ＝ p ⁻¹ ∙ l ∙ p
conjugate-loop-conjugates refl = transport-along-＝ refl

conjugate-loop-refl
 : {A : 𝓤 ̇ } {a : A} (p : a ＝ a)
 → conjugate-loop refl p ＝ p
conjugate-loop-refl p =
 p                      ＝⟨ conjugate-loop-conjugates refl p ⟩
 refl ∙ p               ＝⟨ refl ⟩
 refl ⁻¹ ∙ p ∙ refl     ＝⟨ refl-left-neutral ⟩
 conjugate-loop refl p  ∎

\end{code}

When h = refl the square collapses to a point and the loop is unchanged:

    a ═══ p ══ a
    ║          ║
    h          h    ↝   a ══ refl ══ a
    ║          ║
    a ════════ a

\begin{code}

＝-congr-refl : {A : 𝓤 ̇ } {a x : A} (h : a ＝ x) → ＝-congr h h refl ＝ refl
＝-congr-refl refl = refl

\end{code}

Equality congruence distributes over path concatenation:

    a ══ p ══ b ══ q ═══ c
    ║         ║          ║
   h₁        h₂          h₃
    ║         ║          ║
    x ═══════ y ════════ z

\begin{code}

＝-congr-∙ : {A : 𝓤 ̇ } {a b c x y z : A}
             (h₁ : a ＝ x) (h₂ : b ＝ y) (h₃ : c ＝ z)
             (p : a ＝ b) (q : b ＝ c)
           → ＝-congr h₁ h₃ (p ∙ q) ＝ ＝-congr h₁ h₂ p ∙ ＝-congr h₂ h₃ q
＝-congr-∙ refl refl refl p q = refl


\end{code}

Equality congruence by a composite path equals iterated congruence.

\begin{code}

＝-congr-∙'
 : {A : 𝓤 ̇ } {a b u v x y : A}
   (l₁ : a ＝ u) (l₂ : u ＝ x)
   (r₁ : b ＝ v) (r₂ : v ＝ y)
   (p : a ＝ b)
 → ＝-congr (l₁ ∙ l₂) (r₁ ∙ r₂) p ＝ ＝-congr l₂ r₂ (＝-congr l₁ r₁ p)
＝-congr-∙' refl refl refl refl p = refl

\end{code}

We now show that equality congruence is natural.

The cleanest expression is a commutative square whose nodes are
path spaces and whose edges are "apply congruence with":

  (a ＝ b) ══════ congruence with (ha, hb) ══════ (a ＝ b)
     ║                                              ║
congruence with (hax, hby)                  congruence with (hax, hby)
     ║                                              ║
  (x ＝ y) ════ congruence with (ha', hb') ══════ (x ＝ y)

  where  ha' = eq-congr hax hax ha
         hb' = eq-congr hby hby hb.

The geometric intuition is a cube in A, where the top and bottom faces
record the ha/hb loops and their congruences ha'/hb', and the vertical
edges are hax and hby:

        a ══  ha ══ a
       ╱║           ║╲
    hax ║           ║ hax
     ╱  p           p' ╲
    x   ║           ║    x
    ║   b ══  hb ══ b    ║
    ║  ╱             ╲   ║
    ║ hby           hby  ║
    ║╱                 ╲ ║
    y ══════  hb' ══════ y

  where  p  = eq-congr hax hby p      (front face)
         p' = eq-congr hax hby        (back face)
               (eq-congr ha hb p).

Naturality says that the front face and back face of the cube give the
same path x ＝ y.

\begin{code}

＝-congr-nat : {A : 𝓤 ̇ } {a b x y : A}
               (ha : a ＝ a) (hb : b ＝ b) (hax : a ＝ x) (hby : b ＝ y)
               (p : a ＝ b)
             → ＝-congr hax hby (＝-congr ha hb p)
             ＝ ＝-congr
                 (＝-congr hax hax ha)
                 (＝-congr hby hby hb)
                 (＝-congr hax hby p)
＝-congr-nat ha hb refl refl p = refl

＝-congr-nat' : {A : 𝓤 ̇ } {a b x y : A}
                (hab : a ＝ b) (hax : a ＝ x) (hby : b ＝ y)
                (p : a ＝ a)
              → ＝-congr hby hby (＝-congr hab hab p)
                ＝ ＝-congr
                    (＝-congr hax hby hab)
                    (＝-congr hax hby hab)
                    (＝-congr hax hax p)
＝-congr-nat' refl refl refl p = refl

\end{code}

Equality congruence is invertible.

\begin{code}

＝-congr-⁻¹ : {A : 𝓤 ̇ } {a b x y : A}
              {hax : a ＝ x} {hby : b ＝ y}
              {p : a ＝ b} {q : x ＝ y}
            → ＝-congr hax hby p ＝ q
            → p ＝ ＝-congr (hax ⁻¹) (hby ⁻¹) q
＝-congr-⁻¹ {hax = refl} {hby = refl} refl = refl

\end{code}

We now construct a square congruence identity.

Going right-then-down equals going down-then-right:

    a ══ p ══ b
    ║         ║
    q         r
    ║         ║
    x ═══════ y

\begin{code}

＝-congr-sq : {A : 𝓤 ̇ } {a b x y : A}
              (p : a ＝ b) (q : a ＝ x) (r : b ＝ y)
            → q ∙ ＝-congr q r p ＝ p ∙ r
＝-congr-sq refl refl refl = refl

\end{code}

Moved here from Jakub Opršal's
AlgebraicStructuresForcingSethood.WeakNearUnanimity by Tom de Jong
on 8 June 2026.

\begin{code}

＝-congr-cancel : {A : 𝓤 ̇ } {a a' b b' : A} {p q : a ＝ a'}
                → (h₁ : a ＝ b)
                → (h₂ : a' ＝ b')
                → ＝-congr h₁ h₂ p ＝ ＝-congr h₁ h₂ q
                → p ＝ q
＝-congr-cancel refl refl h = h

＝-congr-ap₃
 : {W : 𝓣 ̇ } {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
    (f : W → X → Y → Z)
    {w₀ w₁ w₂ w₃ : W} {x₀ x₁ x₂ x₃ : X} {y₀ y₁ y₂ y₃ : Y}
    (r₀ : w₀ ＝ w₁) (r₁ : w₂ ＝ w₃) (r₂ : w₀ ＝ w₂)
    (p₀ : x₀ ＝ x₁) (p₁ : x₂ ＝ x₃) (p₂ : x₀ ＝ x₂)
    (q₀ : y₀ ＝ y₁) (q₁ : y₂ ＝ y₃) (q₂ : y₀ ＝ y₂)
  → ＝-congr (ap₃ f r₀ p₀ q₀) (ap₃ f r₁ p₁ q₁) (ap₃ f r₂ p₂ q₂)
    ＝ ap₃ f (＝-congr r₀ r₁ r₂) (＝-congr p₀ p₁ p₂) (＝-congr q₀ q₁ q₂)
＝-congr-ap₃ f refl refl r₂ refl refl p₂ refl refl q₂ = refl

\end{code}

\end{code}

Moved here from AlgebraicStructuresForcingSethood.Semilattices by
Tom de Jong on 8 June 2026.
Code and comments authored by Martin Escardo.

The standard Eckmann–Hilton argument shows that two binary operations
on a set that share a unit and interchange with each other must
coincide and be commutative. Here we record one piece of that
argument: if loops p and q commute, then p ∙ p and q ∙ q also commute.

The key calculation rearranges a 2×2 grid of tiles:

  ┌──────┬──────┐     ┌──────┬──────┐
  │  p   │  p   │     │  q   │  q   │
  ├──────┼──────┤  ↝  ├──────┼──────┤
  │  q   │  q   │     │  p   │  p   │
  └──────┴──────┘     └──────┴──────┘

  p∙p∙q∙q = p∙(p∙q)∙q ＝ p∙(q∙p)∙q = (p∙q)∙(p∙q)
          ＝ (q∙p)∙(q∙p) = q∙(p∙q)∙p ＝ q∙(q∙p)∙p = q∙q∙p∙p.

The function assoc₄ handles the repeated reassociation steps.

\begin{code}

assoc₄ : {A : 𝓤 ̇ } {a b c d e : A}
         {p : a ＝ b} {q : b ＝ c} {r : c ＝ d} {s : d ＝ e}
       → (p ∙ q) ∙ (r ∙ s) ＝ p ∙ (q ∙ r) ∙ s
assoc₄ {p = refl} {q = refl} {r = refl} {s = refl} = refl

comm₂ : {A : 𝓤 ̇ } {a : A} {p q : a ＝ a} (h : p ∙ q ＝ q ∙ p)
      → (p ∙ p) ∙ (q ∙ q) ＝ (q ∙ q) ∙ (p ∙ p)
comm₂ {p = p} {q = q} h =
 ＝-congr
  ((assoc₄ {p = p} {q = p} {r = q} {s = q}) ⁻¹)
  ((assoc₄ {p = q} {q = q} {r = p} {s = p}) ⁻¹)
  (＝-congr
    (ap (λ x → p ∙ x ∙ q) (h ⁻¹))
    (ap (λ x → q ∙ x ∙ p) h)
    (＝-congr (assoc₄ {p = p} {q = q} {r = p} {s = q})
              (assoc₄ {p = q} {q = p} {r = q} {s = p})
              (ap (λ x → x ∙ x) h)))

\end{code}