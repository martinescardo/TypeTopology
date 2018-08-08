Martin Escardo, July 2018

Closure properties of some ordinal construnctions.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UF-FunExt

module OrdinalsClosure
        (fe : ∀ U V → funext U V)
       where

open import SpartanMLTT
open import Ordinals fe hiding (order-preserving) hiding (order-reflecting)
open import OrdinalArithmetic fe
open import OrdinalNotions hiding (_≤_)
open import WellOrderArithmetic
open import SearchableTypes
open import UF-Base
open import UF-Equiv
open import UF-Subsingletons
open import GenericConvergentSequence renaming (_≺_ to _≺[ℕ∞]_)
open import NaturalsOrder hiding (_≤_) renaming (_<_ to _≺[ℕ]_)
open import UF-Embedding
open import UF-InjectiveTypes fe
open import SquashedSum fe
open import SquashedCantor fe
open import UF-Retracts
open import InfSearchable
open import LexicographicOrder
open import LexicographicSearch
open import ConvergentSequenceInfSearchable
open import PropInfTychonoff
open import DiscreteAndSeparated
open import UF-SetExamples
open import BinaryNaturals hiding (_+_) hiding (l) hiding (r)

\end{code}

Ordinal-indexed sums of ordinals are closed under searchability:

\begin{code}

∑-searchable : (τ : Ordᵀ) (υ : ⟪ τ ⟫ → Ordᵀ)
            → searchable ⟪ τ ⟫
            → ((x : ⟪ τ ⟫) → searchable ⟪ υ x ⟫)
            → searchable ⟪ ∑ τ υ ⟫
∑-searchable τ υ ε δ = Σ-searchable ε δ

\end{code}

More searchability closure properties are in the module SquashedSum.

The complication of the following proof in the case for addition is
that the ordinal 𝟚ᵒ has underlying set 𝟙+𝟙 rather than 𝟚, and that
(hence) we defined the ordinal +ᵒ as a sum indexed by 𝟙+𝟙 rather than
as a co-product. This saved lots of code elsewhere, but adds labour
here (and in some helper lemmas/constructions that we added in other
modules for this purpose). Notice that +' is the sum indexed by 𝟚,
defined in the module SpartanMLTT. The bulk of the work for the
following construction is performed in the module SquashedCantor.

\begin{code}

+-retract-of-Cantor : (τ : Ordᵀ) (υ : Ordᵀ)
                   → retract ⟪ τ ⟫ of Cantor
                   → retract ⟪ υ ⟫ of Cantor
                   → retract ⟪ τ +ᵒ υ  ⟫ of Cantor
+-retract-of-Cantor τ υ ε δ = retracts-compose d e
 where
  a : retract (Cantor +' Cantor) of (Cantor + Cantor)
  a = +'-retract-of-+
  b : retract (Cantor +' Cantor) of Cantor
  b = retracts-compose +-Cantor-retract a
  c : retract ⟪ τ ⟫ +' ⟪ υ ⟫ of (Cantor +' Cantor)
  c = +'-retract ε δ
  d : retract ⟪ τ ⟫ +' ⟪ υ ⟫ of Cantor
  d = retracts-compose b c
  e : retract ⟪ τ +ᵒ υ ⟫ of (⟪ τ ⟫ +' ⟪ υ ⟫)
  e = transport (λ - → retract ⟪ τ +ᵒ υ ⟫ of (Σ -)) (dfunext (fe U₀ U₁) l) h
   where
    f : 𝟚 → 𝟙 + 𝟙
    f = pr₁ retract-𝟙+𝟙-of-𝟚
    h : retract ⟪ τ +ᵒ υ ⟫ of (Σ \(i : 𝟚) → ⟪ cases (λ _ → τ) (λ _ → υ) (f i) ⟫)
    h = Σ-reindex-retract f (pr₂ retract-𝟙+𝟙-of-𝟚)
    l : (i : 𝟚) → ⟪ cases (λ _ → τ) (λ _ → υ) (f i) ⟫
                ≡ 𝟚-cases ⟪ τ ⟫ ⟪ υ ⟫ i
    l ₀ = refl
    l ₁ = refl

×-retract-of-Cantor : (τ : Ordᵀ) (υ : Ordᵀ)
                   → retract ⟪ τ ⟫ of Cantor
                   → retract ⟪ υ ⟫ of Cantor
                   → retract ⟪ τ ×ᵒ υ  ⟫ of Cantor
×-retract-of-Cantor τ υ ε δ =  retracts-compose a b
 where
  a : retract (Cantor × Cantor) of Cantor
  a = pair-seq-retract fe₀
  b : retract ⟪ τ ⟫ × ⟪ υ ⟫ of (Cantor × Cantor)
  b = ×-retract ε δ

\end{code}

More Cantor-retract properties are in the module SquashedCantor.

\begin{code}

Σ-retract-of-ℕ : ∀ {U V} {X : U ̇} {Y : X → V ̇}
               → retract X of ℕ
               → ((x : X) → retract (Y x) of ℕ)
               → retract (Σ Y) of ℕ
Σ-retract-of-ℕ {U} {V} {X} {Y} ρ R = retracts-compose b a
 where
  a : retract (Σ Y) of (ℕ × ℕ)
  a = Σ-retract₂ ρ R
  b : retract (ℕ × ℕ) of ℕ
  b = equiv-retract-l pairing

Σ₁-ℕ-retract : ∀ {U} {X : ℕ → U ̇}
             → ((n : ℕ) → retract (X n) of ℕ)
             → retract (Σ₁ X) of ℕ
Σ₁-ℕ-retract {U} {X} ρ = retracts-compose c b
 where
  a : (z : ℕ + 𝟙) → retract (X / over) z of ((λ _ → ℕ) / over) z
  a = retract-extension X (λ _ → ℕ) over ρ
  b : retract (Σ₁ X) of Σ₁ (λ _ → ℕ)
  b = Σ-retract (X / over) ((λ _ → ℕ) / over) a
  c : retract Σ₁ (λ _ → ℕ) of ℕ
  c = Σ-retract-of-ℕ
       (equiv-retract-l ℕ-plus-𝟙)
       (λ (z : ℕ + 𝟙) → r z , s z , rs z)
   where
    r : (z : ℕ + 𝟙) → ℕ → ((λ _ → ℕ) / inl) z
    r (inl n) m w = m
    r (inr *) m (k , ())
    s : (z : ℕ + 𝟙) → ((λ _ → ℕ) / inl) z → ℕ
    s (inl n) φ = φ (n , refl)
    s (inr *) φ = 0 -- Any natural number will do here.
    rs : (z : ℕ + 𝟙) (φ : ((λ _ → ℕ) / inl) z) → r z (s z φ) ≡ φ
    rs (inl n) φ = dfunext fe₀ g
     where
      g : (w : fiber inl (inl n)) → r (inl n) (s (inl n) φ) w ≡ φ w
      g (n , refl) = refl
    rs (inr *) φ = dfunext fe₀ g
     where
      g : (w : fiber inl (inr *)) → r (inr *) (s (inr *) φ) w ≡ φ w
      g (k , ())

\end{code}

Preservation of discreteness:

\begin{code}

∑-discrete : (τ : Ordᵀ) (υ : ⟪ τ ⟫ → Ordᵀ)
           → discrete ⟪ τ ⟫
           → ((x : ⟪ τ ⟫) → discrete ⟪ υ x ⟫)
           → discrete ⟪ ∑ τ υ ⟫
∑-discrete τ υ ε δ = Σ-discrete ε δ

\end{code}

Some maps and their order preservation, used to show that the
embedding of the discrete ordinals into the searchable ordinals is
order preserving.

\begin{code}

open import UF-Embedding

order-preserving  order-reflecting  : (τ υ : Ordᵀ) → (⟪ τ ⟫ → ⟪ υ ⟫) → U₀ ̇

order-preserving τ υ f = (x y : ⟪ τ ⟫) → x ≺⟪ τ ⟫ y → f x ≺⟪ υ ⟫ f y
order-reflecting τ υ f = (x y : ⟪ τ ⟫) → f x ≺⟪ υ ⟫ f y → x ≺⟪ τ ⟫ y


comp-order-preserving : (τ υ φ : Ordᵀ)  (f : ⟪ τ ⟫ → ⟪ υ ⟫) (g : ⟪ υ ⟫ → ⟪ φ ⟫)
                      → order-preserving τ υ f
                      → order-preserving υ φ g
                      → order-preserving τ φ (g ∘ f)
comp-order-preserving τ υ φ f g p q x y l = q (f x) (f y) (p x y l)

pair-fun-order-preserving : (τ υ : Ordᵀ) (A : ⟪ τ ⟫ → Ordᵀ) (B : ⟪ υ ⟫ → Ordᵀ)
                            (f : ⟪ τ ⟫ → ⟪ υ ⟫)
                            (g  : (x : ⟪ τ ⟫) → ⟪ A x ⟫ → ⟪ B (f x) ⟫)
                         → order-preserving τ υ f
                         → ((x : ⟪ τ ⟫) → order-preserving (A x) (B (f x)) (g x))
                         → order-preserving (∑ τ A) (∑ υ B) (pair-fun f g)

pair-fun-order-preserving τ υ A B f g φ γ (x , a) (y , b) (inl l) = inl (φ x y l)
pair-fun-order-preserving τ υ A B f g φ γ (x , a) (.x , b) (inr (refl , l)) = inr (refl , γ x a b l)

under𝟙ᵒ : ⟪ succₒ ℕₒ ⟫ → ⟪ ℕ∞ᵒ ⟫
under𝟙ᵒ = under𝟙

under𝟙ᵒ-order-preserving : order-preserving (succₒ ℕₒ) ℕ∞ᵒ under𝟙ᵒ
under𝟙ᵒ-order-preserving (inl n) (inl m) l = under-order-preserving n m l
under𝟙ᵒ-order-preserving (inl n) (inr *) * = n , (refl , refl)
under𝟙ᵒ-order-preserving (inr *) (inl m) ()
under𝟙ᵒ-order-preserving (inr *) (inr *) ()

over-under-map-order-preserving  : (τ : ℕ → Ordᵀ) (z : ℕ + 𝟙)
                                 → order-preserving
                                    ((τ ↗ (over , over-embedding)) z)
                                    ((τ ↗ (under , under-embedding fe₀)) (under𝟙 z))
                                    (over-under-map (λ n → ⟪ τ n ⟫) z)
over-under-map-order-preserving τ (inl n) x y ((.n , refl) , l) = (n , refl) , γ
 where
  γ : over-under-map (λ n → ⟪ τ n ⟫) (inl n) x (n , refl) ≺⟪ τ n ⟫
      over-under-map (λ n → ⟪ τ n ⟫) (inl n) y (n , refl)
  γ = back-transport₂
        (λ a b → a ≺⟪ τ n ⟫ b)
        (over-under-map-left (λ n → ⟪ τ n ⟫) n x)
        (over-under-map-left (λ n → ⟪ τ n ⟫) n y)
        l
over-under-map-order-preserving τ (inr *) x y ((n , ()) , l)

∑-up : (τ : ℕ → Ordᵀ) → ⟪ ∑₁ τ ⟫ → ⟪ ∑¹ τ ⟫
∑-up τ = Σ-up (λ n → ⟪ τ n ⟫)

∑-up-order-preserving : (τ : ℕ → Ordᵀ)
                      → order-preserving (∑₁ τ) (∑¹ τ) (∑-up τ)
∑-up-order-preserving τ  = pair-fun-order-preserving
                            (succₒ ℕₒ)
                            ℕ∞ᵒ
                            (τ ↗ (over , over-embedding))
                            (τ  ↗ (under , under-embedding fe₀))
                            under𝟙ᵒ
                            (over-under-map (λ n → ⟪ τ n ⟫))
                            under𝟙ᵒ-order-preserving
                            (over-under-map-order-preserving τ)

∑↑ : (τ υ : ℕ → Ordᵀ) (f : (n : ℕ) → ⟪ τ n ⟫ → ⟪ υ n ⟫)
   → ⟪ ∑₁ τ ⟫ → ⟪ ∑¹ υ ⟫
∑↑ τ υ = Σ↑ (λ n → ⟪ τ n ⟫) (λ n → ⟪ υ n ⟫)

Overᵒ : (τ υ : ℕ → Ordᵀ) (f : (n : ℕ) → ⟪ τ n ⟫ → ⟪ υ n ⟫)
      → (z : ℕ + 𝟙) → ⟪ (τ ↗ (over , over-embedding)) z ⟫ → ⟪ (υ ↗ (over , over-embedding)) z ⟫
Overᵒ τ υ = Over (λ n → ⟪ τ n ⟫) (λ n → ⟪ υ n ⟫)

Overᵒ-order-preserving : (τ υ : ℕ → Ordᵀ) (f : (n : ℕ) → ⟪ τ n ⟫ → ⟪ υ n ⟫)
   → ((n : ℕ) → order-preserving (τ n) (υ n) (f n))
   → (z : ℕ + 𝟙) → order-preserving
                      ((τ ↗ (over , over-embedding)) z)
                      ((υ ↗ (over , over-embedding)) z)
                      (Overᵒ τ υ f z)
Overᵒ-order-preserving τ υ f p (inl n) x y ((.n , refl) , l) = (n , refl) , p n _ _ l
Overᵒ-order-preserving τ υ f p (inr *) x y ((n , ()) , l)

∑₁-functor : (τ υ : ℕ → Ordᵀ) (f : (n : ℕ) → ⟪ τ n ⟫ → ⟪ υ n ⟫)
           → ⟪ ∑₁ τ ⟫ → ⟪ ∑₁ υ ⟫
∑₁-functor τ ν = Σ₁-functor (λ n → ⟪ τ n ⟫) (λ n → ⟪ ν n ⟫)

∑₁-functor-order-preserving : (τ υ : ℕ → Ordᵀ) (f : (n : ℕ) → ⟪ τ n ⟫ → ⟪ υ n ⟫)
                            → ((n : ℕ) → order-preserving (τ n) (υ n) (f n))
                            → order-preserving (∑₁ τ) (∑₁ υ) (∑₁-functor τ υ f)
∑₁-functor-order-preserving τ υ f p =
 pair-fun-order-preserving
  (succₒ ℕₒ)
  (succₒ ℕₒ)
  (τ ↗ (over , over-embedding))
  (υ ↗ (over , over-embedding))
  id
  (Over (λ n → ⟪ τ n ⟫) (λ n → ⟪ υ n ⟫) f)
  (λ x y l → l)
  (Overᵒ-order-preserving τ υ f p)

∑↑-order-preserving : (τ υ : ℕ → Ordᵀ) (f : (n : ℕ) → ⟪ τ n ⟫ → ⟪ υ n ⟫)
                    → ((n : ℕ) → order-preserving (τ n) (υ n) (f n))
                    → order-preserving (∑₁ τ) (∑¹ υ) (∑↑ τ υ f)
∑↑-order-preserving τ υ f p = comp-order-preserving
                                (∑₁ τ)
                                (∑₁ υ )
                                (∑¹ υ)
                                (Σ₁-functor
                                   (λ n → ⟪ τ n ⟫)
                                   (λ n → ⟪ υ n ⟫)
                                   f)
                                (∑-up υ)
                                (∑₁-functor-order-preserving τ υ f p)
                                (∑-up-order-preserving υ)
\end{code}

And now order reflection.

\begin{code}

open import UF-Embedding

comp-order-reflecting : (τ υ φ : Ordᵀ)  (f : ⟪ τ ⟫ → ⟪ υ ⟫) (g : ⟪ υ ⟫ → ⟪ φ ⟫)
                      → order-reflecting τ υ f
                      → order-reflecting υ φ g
                      → order-reflecting τ φ (g ∘ f)
comp-order-reflecting τ υ φ f g p q x y l = p x y (q (f x) (f y) l)

pair-fun-order-reflecting : (τ υ : Ordᵀ) (A : ⟪ τ ⟫ → Ordᵀ) (B : ⟪ υ ⟫ → Ordᵀ)
                            (f : ⟪ τ ⟫ → ⟪ υ ⟫)
                            (g  : (x : ⟪ τ ⟫) → ⟪ A x ⟫ → ⟪ B (f x) ⟫)
                         → order-reflecting τ υ f
                         → is-embedding f
                         → ((x : ⟪ τ ⟫) → order-reflecting (A x) (B (f x)) (g x))
                         → order-reflecting (∑ τ A) (∑ υ B) (pair-fun f g)

pair-fun-order-reflecting τ υ A B f g φ e γ (x , a) (y , b) (inl l) = inl (φ x y l)
pair-fun-order-reflecting τ υ A B f g φ e γ (x , a) (y , b) (inr (r , l)) = inr (c r , p)
 where
  e' : is-equiv (ap f)
  e' = embedding-embedding' f e x y
  c : f x ≡ f y → x ≡ y
  c = pr₁(pr₁ e')
  η : (q : f x ≡ f y) → ap f (c q) ≡ q
  η = pr₂(pr₁ e')
  i : transport (λ - → ⟪ B (f -) ⟫) (c r) (g x a)
    ≡ transport (λ - → ⟪ B - ⟫) (ap f (c r)) (g x a)
  i = transport-ap (λ - → ⟪ B - ⟫) f (c r)
  j : transport (λ - → ⟪ B - ⟫) (ap f (c r)) (g x a) ≺⟪ B (f y) ⟫ (g y b)
  j = back-transport (λ - → transport (λ - → ⟪ B - ⟫) - (g x a) ≺⟪ B (f y) ⟫ (g y b)) (η r) l
  k : transport (λ - → ⟪ B (f -) ⟫) (c r) (g x a) ≺⟪ B (f y) ⟫ (g y b)
  k = back-transport (λ - → - ≺⟪ B (f y) ⟫ (g y b)) i j
  h : {x y : ⟪ τ ⟫} (s : x ≡ y) {a : ⟪ A x ⟫} {b : ⟪ A y ⟫}
    → transport (λ - → ⟪ B (f -) ⟫) s (g x a) ≺⟪ B (f y) ⟫ (g y b)
    → transport (λ - → ⟪ A - ⟫) s a ≺⟪ A y ⟫ b
  h {x} refl {a} {b} = γ x a b
  p : transport (λ - → ⟪ A - ⟫) (c r) a ≺⟪ A y ⟫ b
  p = h (c r) k

under𝟙ᵒ-order-reflecting : order-reflecting (succₒ ℕₒ) ℕ∞ᵒ under𝟙ᵒ
under𝟙ᵒ-order-reflecting (inl n) (inl m) l = under-order-reflecting n m l
under𝟙ᵒ-order-reflecting (inl n) (inr *) l = *
under𝟙ᵒ-order-reflecting (inr *) (inl m) (n , (p , l)) = 𝟘-elim (∞-is-not-ℕ n p)
under𝟙ᵒ-order-reflecting (inr *) (inr *) (n , (p , l)) = 𝟘-elim (∞-is-not-ℕ n p)

over-under-map-order-reflecting  : (τ : ℕ → Ordᵀ) (z : ℕ + 𝟙)
                                 → order-reflecting
                                     ((τ ↗ (over , over-embedding)) z)
                                     ((τ ↗ (under , under-embedding fe₀)) (under𝟙 z))
                                     (over-under-map (λ n → ⟪ τ n ⟫) z)
over-under-map-order-reflecting τ (inl n) x y ((m , p) , l) = (n , refl) , q
 where
  x' : ⟪ τ n ⟫
  x' = over-under-map (λ n → ⟪ τ n ⟫) (inl n) x (n , refl)
  y' : ⟪ τ n ⟫
  y' = over-under-map (λ n → ⟪ τ n ⟫) (inl n) y (n , refl)
  r : n , refl ≡ m , p
  r = under-embedding fe₀ (under n) (n , refl) (m , p)
  t : ⟪ τ n ⟫ → ⟪ τ m ⟫
  t = transport (λ - → ⟪ τ (pr₁ -) ⟫) r
  tr : {w t : fiber under (under n)} (r : w ≡ t)
     → order-reflecting (τ (pr₁ w)) (τ (pr₁ t)) ((transport (λ - → ⟪ τ (pr₁ -) ⟫) r))
  tr refl x y l = l
  a : t x' ≡ over-under-map (λ n → ⟪ τ n ⟫) (inl n) x (m , p)
  a = apd (over-under-map (λ n → ⟪ τ n ⟫) (inl n) x) r
  b : t y' ≡ over-under-map (λ n → ⟪ τ n ⟫) (inl n) y (m , p)
  b = apd (over-under-map (λ n → ⟪ τ n ⟫) (inl n) y) r
  c : t x' ≺⟪ τ m ⟫ t y'
  c = back-transport₂ (λ a b → a ≺⟪ τ m ⟫ b) a b l
  d : x' ≺⟪ τ n ⟫ y'
  d = tr r _ _ c
  q : x (n , refl) ≺⟪ τ n ⟫ y (n , refl)
  q = transport₂
       (λ a b → a ≺⟪ τ n ⟫ b)
       (over-under-map-left (λ n → ⟪ τ n ⟫) n x)
       (over-under-map-left (λ n → ⟪ τ n ⟫) n y)
       d
over-under-map-order-reflecting τ (inr *) x y ((m , p) , l) = 𝟘-elim (∞-is-not-ℕ m (p ⁻¹))

∑-up-order-reflecting : (τ : ℕ → Ordᵀ)
                      → order-reflecting (∑₁ τ) (∑¹ τ) (∑-up τ)
∑-up-order-reflecting τ  = pair-fun-order-reflecting
                            (succₒ ℕₒ)
                            ℕ∞ᵒ
                            (τ ↗ (over , over-embedding))
                            (τ  ↗ (under , under-embedding fe₀))
                            under𝟙ᵒ
                            (over-under-map (λ n → ⟪ τ n ⟫))
                            under𝟙ᵒ-order-reflecting
                            (under𝟙-embedding fe₀)
                            (over-under-map-order-reflecting τ)

Overᵒ-order-reflecting : (τ υ : ℕ → Ordᵀ) (f : (n : ℕ) → ⟪ τ n ⟫ → ⟪ υ n ⟫)
   → ((n : ℕ) → order-reflecting (τ n) (υ n) (f n))
   → (z : ℕ + 𝟙) → order-reflecting
                      ((τ ↗ (over , over-embedding)) z)
                      ((υ ↗ (over , over-embedding)) z)
                      (Overᵒ τ υ f z)
Overᵒ-order-reflecting τ υ f p (inl n) x y ((.n , refl) , l) = (n , refl) , p n _ _ l
Overᵒ-order-reflecting τ υ f p (inr *) x y ((n , ()) , l)

∑₁-functor-order-reflecting : (τ υ : ℕ → Ordᵀ) (f : (n : ℕ) → ⟪ τ n ⟫ → ⟪ υ n ⟫)
                            → ((n : ℕ) → order-reflecting (τ n) (υ n) (f n))
                            → order-reflecting (∑₁ τ) (∑₁ υ) (∑₁-functor τ υ f)
∑₁-functor-order-reflecting τ υ f p =
 pair-fun-order-reflecting
  (succₒ ℕₒ)
  (succₒ ℕₒ)
  (τ ↗ (over , over-embedding))
  (υ ↗ (over , over-embedding))
  id
  (Over (λ n → ⟪ τ n ⟫) (λ n → ⟪ υ n ⟫) f)
  (λ x y l → l)
  id-is-embedding
  (Overᵒ-order-reflecting τ υ f p)

∑↑-order-reflecting : (τ υ : ℕ → Ordᵀ) (f : (n : ℕ) → ⟪ τ n ⟫ → ⟪ υ n ⟫)
                    → ((n : ℕ) → order-reflecting (τ n) (υ n) (f n))
                    → order-reflecting (∑₁ τ) (∑¹ υ) (∑↑ τ υ f)
∑↑-order-reflecting τ υ f p = comp-order-reflecting
                                 (∑₁ τ)
                                 (∑₁ υ )
                                 (∑¹ υ)
                                 (Σ₁-functor
                                    (λ n → ⟪ τ n ⟫)
                                    (λ n → ⟪ υ n ⟫)
                                    f)
                                 (∑-up υ)
                                 (∑₁-functor-order-reflecting τ υ f p)
                                 (∑-up-order-reflecting υ)
\end{code}

28 July 2018. Inf searchability.

\begin{code}

𝟙ᵒ-inf-searchable : inf-searchable (λ x y → x ≼⟪ 𝟙ᵒ ⟫ y)
𝟙ᵒ-inf-searchable p = * , f , g , h
 where
  f : (Σ \(x : 𝟙) → p x ≡ ₀) → p * ≡ ₀
  f (* , r) = r
  g : (x : 𝟙) → p x ≡ ₀ → * ≼⟪ 𝟙ᵒ ⟫ x
  g * r ()
  h : (x : 𝟙) → root-lower-bound (λ x y → x ≼⟪ 𝟙ᵒ ⟫ y) p x
    → x ≼⟪ 𝟙ᵒ ⟫ *
  h * φ ()

𝟚ᵒ-inf-searchable : inf-searchable (λ x y → x ≼⟪ 𝟚ᵒ ⟫ y)
𝟚ᵒ-inf-searchable p = 𝟚-equality-cases φ γ
 where
  _≤_ : 𝟙 + 𝟙 → 𝟙 + 𝟙 → U₀ ̇
  x ≤ y = x ≼⟪ 𝟚ᵒ ⟫ y
  φ : (r : p (inl *) ≡ ₀) → Σ \(x : 𝟙 + 𝟙) → conditional-root _≤_ p x × roots-infimum _≤_ p x
  φ r = inl * , f , g , h
   where
    f : (Σ \(x : 𝟙 + 𝟙) → p x ≡ ₀) → p (inl *) ≡ ₀
    f (inl * , s) = s
    f (inr * , s) = r
    g : (x : 𝟙 + 𝟙) → p x ≡ ₀ → inl * ≤ x
    g (inl *) s ()
    g (inr *) s ()
    h : (x : 𝟙 + 𝟙) → root-lower-bound _≤_ p x → x ≤ inl *
    h (inl *) φ ()
    h (inr *) φ * = φ (inl *) r *

  γ : (r : p (inl *) ≡ ₁) → Σ \(x : 𝟙 + 𝟙) → conditional-root _≤_ p x × roots-infimum _≤_ p x
  γ r = inr * , f , g , h
   where
    f : (Σ \(x : 𝟙 + 𝟙) → p x ≡ ₀) → p (inr *) ≡ ₀
    f (inl * , s) = 𝟘-elim (zero-is-not-one (s ⁻¹ ∙ r))
    f (inr * , s) = s
    g : (x : 𝟙 + 𝟙) → p x ≡ ₀ → inr * ≤ x
    g (inl *) s l = 𝟘-elim (zero-is-not-one (s ⁻¹ ∙ r))
    g (inr *) s ()
    h : (x : 𝟙 + 𝟙) → root-lower-bound _≤_ p x → x ≤ inr *
    h (inl *) φ ()
    h (inr *) φ ()

\end{code}

It is not necessary to use propositional extensionality to prove the
following, but it is simpler to do so given that we have already
proved the inf-searchability of various types using different,
logically equivalent orders.

\begin{code}

∑-inf-searchable : propext U₀
                → (τ : Ordᵀ) (υ : ⟪ τ ⟫ → Ordᵀ)
                → inf-searchable (λ x y → x ≼⟪ τ ⟫ y)
                → ((x : ⟪ τ ⟫) → inf-searchable (λ a b → a ≼⟪ υ x ⟫ b))
                → inf-searchable (λ z t → z ≼⟪ ∑ τ υ ⟫ t)
∑-inf-searchable pe τ υ ε δ = γ
 where
  _≤_ : ⟪ ∑ τ υ ⟫ → ⟪ ∑ τ υ ⟫ → U₀ ̇
  _≤_ = lex-order (λ x y → x ≼⟪ τ ⟫ y) (λ {x} a b → a ≼⟪ υ x ⟫ b)
  ≤-prop-valued : (z t : ⟪ ∑ τ υ ⟫) → is-prop (z ≤ t)
  ≤-prop-valued (x , a) (y , b) (p , u) (q , v) =
   to-Σ-≡
     (≼-prop-valued τ x y p q ,
     dfunext fe₀ (λ r → ≼-prop-valued (υ y) _ _ _ _))
  φ : inf-searchable _≤_
  φ = Σ-inf-searchable ((λ x y → x ≼⟪ τ ⟫ y)) ((λ {x} a b → a ≼⟪ υ x ⟫ b)) ε δ
  open commutation (tunderlying-order τ) (λ {x} → tunderlying-order (υ x)) (𝟘 {U₀}) hiding (_≤_)
  i : (z t : ⟪ ∑ τ υ ⟫) → z ≤ t → z ≼⟪ ∑ τ υ ⟫ t
  i (x , a) (y , b) = back y x b a
  j : (z t : ⟪ ∑ τ υ ⟫) → z ≼⟪ ∑ τ υ ⟫ t → z ≤ t
  j (x , a) (y , b) = forth y x b a
  k : (z t : ⟪ ∑ τ υ ⟫) → z ≤ t ≡ z ≼⟪ ∑ τ υ ⟫ t
  k z t = pe (≤-prop-valued z t) (≼-prop-valued (∑ τ υ) z t) (i z t) (j z t)
  l : _≤_ ≡ (λ z t → z ≼⟪ ∑ τ υ ⟫ t)
  l = dfunext (fe U₀ U₁) λ z → dfunext (fe U₀ U₁) (k z)
  γ : inf-searchable (λ z t → z ≼⟪ ∑ τ υ ⟫ t)
  γ = transport inf-searchable l φ

∑₁-inf-searchable : propext U₀
                  → (τ : ℕ → Ordᵀ)
                  → ((n : ℕ) → inf-searchable λ x y → x ≼⟪ τ n ⟫ y)
                  → inf-searchable (λ z t → z ≼⟪ ∑¹ τ ⟫ t)
∑₁-inf-searchable pe τ ε = ∑-inf-searchable pe
                            ℕ∞ᵒ
                            (λ (x : ℕ∞) → (τ ↗ (under , under-embedding fe₀)) x)
                            a
                            b
 where
  p : GenericConvergentSequence._≼_ ≡ tunderlying-rorder ℕ∞ᵒ
  p = dfunext (fe U₀ U₁)
       (λ u → dfunext (fe U₀ U₁)
                (λ v → pe (≼-is-prop fe₀ u v)
                          (≼-prop-valued ℕ∞ᵒ u v)
                          (≼-not-≺ u v)
                          (not-≺-≼ fe₀ u v)))
  a : inf-searchable (tunderlying-rorder ℕ∞ᵒ)
  a = transport inf-searchable p (ℕ∞-inf-searchable fe₀)
  b : (x : ⟪ ℕ∞ᵒ ⟫) → inf-searchable
                        (tunderlying-rorder
                        ((τ ↗ (under , under-embedding fe₀)) x))
  b x = prop-inf-tychonoff fe
         (under-embedding fe₀ x)
         (λ {w} x y → x ≺⟪ τ (pr₁ w) ⟫ y)
         (λ w → ε (pr₁ w))

\end{code}
