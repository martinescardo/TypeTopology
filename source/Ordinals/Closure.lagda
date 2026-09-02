Martin Escardo, July 2018

Closure properties of some ordinal constructions.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Ordinals.Closure
        (fe : FunExt)
       where

open import CoNaturals.Type
open import InjectiveTypes.Blackboard fe
open import MLTT.AlternativePlus
open import MLTT.Plus-Properties
open import MLTT.Spartan
open import MLTT.Two-Properties
open import Naturals.Binary hiding (_+_ ; L ; R)
open import Notation.CanonicalMap
open import Ordinals.Arithmetic fe
open import Ordinals.Equivalence
open import Ordinals.InfProperty
open import Ordinals.Injectivity
open import Ordinals.LexicographicCompactness
open import Ordinals.LexicographicOrder
open import Ordinals.ToppedArithmetic fe
open import Ordinals.ToppedType fe
open import Ordinals.Type
open import Ordinals.Underlying
open import Taboos.LPO
open import TypeTopology.CompactTypes
open import TypeTopology.Density
open import TypeTopology.LimitPoints
open import TypeTopology.ConvergentSequenceHasInf
open import TypeTopology.MicroInfTychonoff
open import TypeTopology.SigmaDiscrete
open import TypeTopology.SquashedCantor fe
open import TypeTopology.SquashedSum fe
open import UF.Base
open import UF.DiscreteAndSeparated
open import UF.Embeddings
open import UF.Equiv
open import UF.PairFun
open import UF.Retracts
open import UF.Subsingletons

private
 fe₀ : funext 𝓤₀ 𝓤₀
 fe₀ = fe 𝓤₀ 𝓤₀

\end{code}

Ordinal-indexed sums of topped ordinals are closed under compactness:

\begin{code}

∑-compact∙ : (τ : Ordᵀ) (υ : ⟨ τ ⟩ → Ordᵀ)
           → is-compact∙ ⟨ τ ⟩
           → ((x : ⟨ τ ⟩) → is-compact∙ ⟨ υ x ⟩)
           → is-compact∙ ⟨ ∑ τ υ ⟩
∑-compact∙ τ υ ε δ = Σ-is-compact∙ ε δ

\end{code}

More compactness closure properties are in the module TypeTopology.SquashedSum.

The complication of the following proof in the case for addition is
that the ordinal 𝟚ᵒ has underlying set 𝟙+𝟙 rather than 𝟚, and that
(hence) we defined the ordinal +ᵒ as a sum indexed by 𝟙+𝟙 rather than
as a co-product. This saved lots of code elsewhere, but adds labour
here (and in some helper lemmas/constructions that we added in other
modules for this purpose). Notice that +' is the sum indexed by 𝟚,
defined in the module MLTT.Spartan. The bulk of the work for the
following construction is performed in the module TypeTopology.SquashedCantor.

\begin{code}

+-retract-of-Cantor : (τ : Ordᵀ) (υ : Ordᵀ)
                    → retract ⟨ τ ⟩ of Cantor
                    → retract ⟨ υ ⟩ of Cantor
                    → retract ⟨ τ +ᵒ υ  ⟩ of Cantor
+-retract-of-Cantor τ υ ε δ = retracts-compose d e
 where
  a : retract (Cantor +' Cantor) of (Cantor + Cantor)
  a = +'-retract-of-+

  b : retract (Cantor +' Cantor) of Cantor
  b = retracts-compose +-Cantor-retract a

  c : retract ⟨ τ ⟩ +' ⟨ υ ⟩ of (Cantor +' Cantor)
  c = +'-retract ε δ

  d : retract ⟨ τ ⟩ +' ⟨ υ ⟩ of Cantor
  d = retracts-compose b c

  e : retract ⟨ τ +ᵒ υ ⟩ of (⟨ τ ⟩ +' ⟨ υ ⟩)
  e = transport (λ - → retract ⟨ τ +ᵒ υ ⟩ of (Σ -)) (dfunext (fe 𝓤₀ 𝓤₁) l) h
   where
    f : 𝟚 → 𝟙 + 𝟙
    f = retraction retract-𝟙+𝟙-of-𝟚

    h : retract ⟨ τ +ᵒ υ ⟩ of (Σ i ꞉ 𝟚 , ⟨ cases (λ _ → τ) (λ _ → υ) (f i) ⟩)
    h = Σ-reindex-retract f (retraction-has-section retract-𝟙+𝟙-of-𝟚)

    l : (i : 𝟚) → ⟨ cases (λ _ → τ) (λ _ → υ) (f i) ⟩
                ＝ 𝟚-cases ⟨ τ ⟩ ⟨ υ ⟩ i
    l ₀ = refl
    l ₁ = refl

×-retract-of-Cantor : (τ : Ordᵀ) (υ : Ordᵀ)
                    → retract ⟨ τ ⟩ of Cantor
                    → retract ⟨ υ ⟩ of Cantor
                    → retract ⟨ τ ×ᵒ υ  ⟩ of Cantor
×-retract-of-Cantor τ υ ε δ =  retracts-compose a b
 where
  a : retract (Cantor × Cantor) of Cantor
  a = pair-seq-retract

  b : retract ⟨ τ ⟩ × ⟨ υ ⟩ of (Cantor × Cantor)
  b = ×-retract ε δ

\end{code}

More Cantor-retract properties are in the module TypeTopology.SquashedCantor.

\begin{code}

Σ-retract-of-ℕ : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
               → retract X of ℕ
               → ((x : X) → retract (Y x) of ℕ)
               → retract (Σ Y) of ℕ
Σ-retract-of-ℕ {𝓤} {𝓥} {X} {Y} ρ σ = retracts-compose b a
 where
  a : retract (Σ Y) of (ℕ × ℕ)
  a = Σ-retract₂ ρ σ

  b : retract (ℕ × ℕ) of ℕ
  b = ≃-gives-◁ pairing

∑₁-top-is-over-inr : (τ : ℕ → Ordᵀ) → Σ₁-base (top (∑₁ τ)) ＝ inr ⋆
∑₁-top-is-over-inr τ = refl

∑₁-top-is-isolated : (τ : ℕ → Ordᵀ) → is-isolated (top (∑₁ τ))
∑₁-top-is-isolated τ = Σ₁-inr-is-isolated (λ n → ⟨ τ n ⟩) _

∑¹-top-is-limit-point : (τ : ℕ → Ordᵀ) → is-limit-point (top (∑¹ τ))
∑¹-top-is-limit-point τ = Σ¹-∞-is-limit-point
                           (λ n → ⟨ τ n ⟩) (λ n → top (τ n)) _

Σ₁-ℕ-retract : {X : ℕ → 𝓤 ̇ }
             → ((n : ℕ) → retract (X n) of ℕ)
             → retract (Σ₁ X) of ℕ
Σ₁-ℕ-retract {𝓤} {X} ρ = retracts-compose c b
 where
  a : (z : ℕ + 𝟙) → retract (X / over) z of ((λ _ → ℕ) / over) z
  a = retract-extension X (λ _ → ℕ) over ρ

  b : retract (Σ₁ X) of Σ₁ (λ _ → ℕ)
  b = Σ-retract (X / over) ((λ _ → ℕ) / over) a

  c : retract Σ₁ (λ _ → ℕ) of ℕ
  c = Σ-retract-of-ℕ
       (≃-gives-◁ ℕ-plus-𝟙)
       (λ (z : ℕ + 𝟙) → r z , s z , rs z)
   where
    r : (z : ℕ + 𝟙) → ℕ → ((λ _ → ℕ) / inl) z
    r (inl n) m w = m
    r (inr *) m (k , p) = 𝟘-elim (+disjoint p)
    s : (z : ℕ + 𝟙) → ((λ _ → ℕ) / inl) z → ℕ
    s (inl n) φ = φ (n , refl)
    s (inr *) φ = 0 -- Any natural number will do here.
    rs : (z : ℕ + 𝟙) (φ : ((λ _ → ℕ) / inl) z) → r z (s z φ) ＝ φ
    rs (inl n) φ = dfunext fe₀ g
     where
      g : (w : fiber inl (inl n)) → r (inl n) (s (inl n) φ) w ＝ φ w
      g (n , refl) = refl
    rs (inr *) φ = dfunext fe₀ g
     where
      g : (w : fiber inl (inr *)) → r (inr *) (s (inr *) φ) w ＝ φ w
      g (k , p) = 𝟘-elim (+disjoint p)

\end{code}

Preservation of discreteness:

\begin{code}

∑-is-discrete : (τ : Ordᵀ) (υ : ⟨ τ ⟩ → Ordᵀ)
              → is-discrete ⟨ τ ⟩
              → ((x : ⟨ τ ⟩) → is-discrete ⟨ υ x ⟩)
              → is-discrete ⟨ ∑ τ υ ⟩
∑-is-discrete τ υ ε δ = Σ-is-discrete ε δ

\end{code}

Some maps and their order preservation, used to show that the
embedding of the discrete ordinals into the compact ordinals is order
preserving.

\begin{code}

is-order-preserving  is-order-reflecting  : (τ υ : Ordᵀ) → (⟨ τ ⟩ → ⟨ υ ⟩) → 𝓤₀ ̇

is-order-preserving τ υ f = (x y : ⟨ τ ⟩) → x ≺⟨ τ ⟩ y → f x ≺⟨ υ ⟩ f y
is-order-reflecting τ υ f = (x y : ⟨ τ ⟩) → f x ≺⟨ υ ⟩ f y → x ≺⟨ τ ⟩ y

comp-is-order-preserving : (τ υ φ : Ordᵀ)
                           (f : ⟨ τ ⟩ → ⟨ υ ⟩)
                           (g : ⟨ υ ⟩ → ⟨ φ ⟩)
                         → is-order-preserving τ υ f
                         → is-order-preserving υ φ g
                         → is-order-preserving τ φ (g ∘ f)
comp-is-order-preserving τ υ φ f g p q x y l = q (f x) (f y) (p x y l)

pair-fun-is-order-preserving
 : (τ υ : Ordᵀ)
   (A : ⟨ τ ⟩ → Ordᵀ)
   (B : ⟨ υ ⟩ → Ordᵀ)
   (f : ⟨ τ ⟩ → ⟨ υ ⟩)
   (g : (x : ⟨ τ ⟩) → ⟨ A x ⟩ → ⟨ B (f x) ⟩)
 → is-order-preserving τ υ f
 → ((x : ⟨ τ ⟩) → is-order-preserving (A x) (B (f x)) (g x))
 → is-order-preserving (∑ τ A) (∑ υ B) (pair-fun f g)
pair-fun-is-order-preserving τ υ A B f g φ γ (x , a) (y , b) (inl l) =
 inl (φ x y l)
pair-fun-is-order-preserving τ υ A B f g φ γ (x , a) (x , b) (inr (refl , l)) =
 inr (refl , γ x a b l)

ι𝟙ᵒ : ⟨ succₒ ω ⟩ → ⟨ ℕ∞ᵒ ⟩
ι𝟙ᵒ = ι𝟙

ι𝟙ᵒ-is-order-preserving : is-order-preserving (succₒ ω) ℕ∞ᵒ ι𝟙ᵒ
ι𝟙ᵒ-is-order-preserving (inl n) (inl m) l = ℕ-to-ℕ∞-order-preserving n m l
ι𝟙ᵒ-is-order-preserving (inl n) (inr *) * = n , (refl , refl)
ι𝟙ᵒ-is-order-preserving (inr *) (inl m) l = 𝟘-elim l
ι𝟙ᵒ-is-order-preserving (inr *) (inr *) l = 𝟘-elim l

open topped-ordinals-injectivity fe

over-ι-map-is-order-preserving  : (τ : ℕ → Ordᵀ) (z : ℕ + 𝟙)
                                → is-order-preserving
                                    ((τ ↗ (over , over-embedding)) z)
                                    ((τ ↗ embedding-ℕ-to-ℕ∞ fe₀) (ι𝟙 z))
                                    (over-ι-map (λ n → ⟨ τ n ⟩) z)
over-ι-map-is-order-preserving τ (inl n) x y ((.n , refl) , l) = (n , refl) , γ
 where
  γ : over-ι-map (λ n → ⟨ τ n ⟩) (inl n) x (n , refl) ≺⟨ τ n ⟩
      over-ι-map (λ n → ⟨ τ n ⟩) (inl n) y (n , refl)
  γ = transport₂⁻¹
        (λ a b → a ≺⟨ τ n ⟩ b)
        (over-ι-map-left (λ n → ⟨ τ n ⟩) n x)
        (over-ι-map-left (λ n → ⟨ τ n ⟩) n y)
        l
over-ι-map-is-order-preserving τ (inr *) x y ((n , p) , l) = 𝟘-elim (+disjoint p)

∑-up : (τ : ℕ → Ordᵀ) → ⟨ ∑₁ τ ⟩ → ⟨ ∑¹ τ ⟩
∑-up τ = Σ-up (λ n → ⟨ τ n ⟩)

∑-up-is-order-preserving : (τ : ℕ → Ordᵀ)
                         → is-order-preserving (∑₁ τ) (∑¹ τ) (∑-up τ)
∑-up-is-order-preserving τ  = pair-fun-is-order-preserving
                               (succₒ ω)
                               ℕ∞ᵒ
                               (τ ↗ (over , over-embedding))
                               (τ  ↗ embedding-ℕ-to-ℕ∞ fe₀)
                               ι𝟙ᵒ
                               (over-ι-map (λ n → ⟨ τ n ⟩))
                               ι𝟙ᵒ-is-order-preserving
                               (over-ι-map-is-order-preserving τ)

∑↑ : (τ υ : ℕ → Ordᵀ) (f : (n : ℕ) → ⟨ τ n ⟩ → ⟨ υ n ⟩)
   → ⟨ ∑₁ τ ⟩ → ⟨ ∑¹ υ ⟩
∑↑ τ υ = Σ↑ (λ n → ⟨ τ n ⟩) (λ n → ⟨ υ n ⟩)

Overᵒ : (τ υ : ℕ → Ordᵀ) (f : (n : ℕ) → ⟨ τ n ⟩ → ⟨ υ n ⟩)
      → (z : ℕ + 𝟙) → ⟨ (τ ↗ (over , over-embedding)) z ⟩ → ⟨ (υ ↗ (over , over-embedding)) z ⟩
Overᵒ τ υ = Over (λ n → ⟨ τ n ⟩) (λ n → ⟨ υ n ⟩)

Overᵒ-is-order-preserving : (τ υ : ℕ → Ordᵀ) (f : (n : ℕ) → ⟨ τ n ⟩ → ⟨ υ n ⟩)
                          → ((n : ℕ) → is-order-preserving (τ n) (υ n) (f n))
                          → (z : ℕ + 𝟙) → is-order-preserving
                                            ((τ ↗ (over , over-embedding)) z)
                                            ((υ ↗ (over , over-embedding)) z)
                                            (Overᵒ τ υ f z)
Overᵒ-is-order-preserving τ υ f p (inl n) x y ((.n , refl) , l) =
 (n , refl) , p n _ _ l
Overᵒ-is-order-preserving τ υ f p (inr *) x y ((n , q) , l) =
 𝟘-elim (+disjoint q)

∑₁-functor : (τ υ : ℕ → Ordᵀ) (f : (n : ℕ) → ⟨ τ n ⟩ → ⟨ υ n ⟩)
           → ⟨ ∑₁ τ ⟩ → ⟨ ∑₁ υ ⟩
∑₁-functor τ ν = Σ₁-functor (λ n → ⟨ τ n ⟩) (λ n → ⟨ ν n ⟩)

∑₁-functor-is-order-preserving
 : (τ υ : ℕ → Ordᵀ)
   (f : (n : ℕ) → ⟨ τ n ⟩ → ⟨ υ n ⟩)
 → ((n : ℕ) → is-order-preserving (τ n) (υ n) (f n))
 → is-order-preserving (∑₁ τ) (∑₁ υ) (∑₁-functor τ υ f)
∑₁-functor-is-order-preserving τ υ f p =
 pair-fun-is-order-preserving
  (succₒ ω)
  (succₒ ω)
  (τ ↗ (over , over-embedding))
  (υ ↗ (over , over-embedding))
  id
  (Over (λ n → ⟨ τ n ⟩) (λ n → ⟨ υ n ⟩) f)
  (λ x y l → l)
  (Overᵒ-is-order-preserving τ υ f p)

∑↑-is-order-preserving : (τ υ : ℕ → Ordᵀ)
                         (f : (n : ℕ) → ⟨ τ n ⟩ → ⟨ υ n ⟩)
                       → ((n : ℕ) → is-order-preserving (τ n) (υ n) (f n))
                       → is-order-preserving (∑₁ τ) (∑¹ υ) (∑↑ τ υ f)
∑↑-is-order-preserving τ υ f p = comp-is-order-preserving
                                  (∑₁ τ)
                                  (∑₁ υ )
                                  (∑¹ υ)
                                  (Σ₁-functor
                                     (λ n → ⟨ τ n ⟩)
                                     (λ n → ⟨ υ n ⟩)
                                     f)
                                  (∑-up υ)
                                  (∑₁-functor-is-order-preserving τ υ f p)
                                  (∑-up-is-order-preserving υ)
\end{code}

And now order reflection.

\begin{code}

comp-is-order-reflecting : (τ υ φ : Ordᵀ)
                           (f : ⟨ τ ⟩ → ⟨ υ ⟩)
                           (g : ⟨ υ ⟩ → ⟨ φ ⟩)
                         → is-order-reflecting τ υ f
                         → is-order-reflecting υ φ g
                         → is-order-reflecting τ φ (g ∘ f)
comp-is-order-reflecting τ υ φ f g p q x y l = p x y (q (f x) (f y) l)

pair-fun-is-order-reflecting
 : (τ υ : Ordᵀ)
   (A : ⟨ τ ⟩ → Ordᵀ)
   (B : ⟨ υ ⟩ → Ordᵀ)
   (f : ⟨ τ ⟩ → ⟨ υ ⟩)
   (g  : (x : ⟨ τ ⟩) → ⟨ A x ⟩ → ⟨ B (f x) ⟩)
 → is-order-reflecting τ υ f
 → is-embedding f
 → ((x : ⟨ τ ⟩) → is-order-reflecting (A x) (B (f x)) (g x))
 → is-order-reflecting (∑ τ A) (∑ υ B) (pair-fun f g)
pair-fun-is-order-reflecting τ υ A B f g φ e γ (x , a) (y , b) (inl l) =
 inl (φ x y l)
pair-fun-is-order-reflecting τ υ A B f g φ e γ (x , a) (y , b) (inr (r , l)) =
 inr (c r , p)
 where
  e' : is-equiv (ap f)
  e' = embedding-gives-embedding' f e x y

  c : f x ＝ f y → x ＝ y
  c = inverse (ap f) e'

  η : (q : f x ＝ f y) → ap f (c q) ＝ q
  η = retract-condition (ap f , equivs-have-sections (ap f) e')

  i : transport (λ - → ⟨ B (f -) ⟩) (c r) (g x a)
    ＝ transport (λ - → ⟨ B - ⟩) (ap f (c r)) (g x a)
  i = transport-ap (λ - → ⟨ B - ⟩) f (c r)

  j : transport (λ - → ⟨ B - ⟩) (ap f (c r)) (g x a) ≺⟨ B (f y) ⟩ (g y b)
  j = transport⁻¹
       (λ - → transport (λ - → ⟨ B - ⟩) - (g x a) ≺⟨ B (f y) ⟩ (g y b))
       (η r)
       l

  k : transport (λ - → ⟨ B (f -) ⟩) (c r) (g x a) ≺⟨ B (f y) ⟩ (g y b)
  k = transport⁻¹ (λ - → - ≺⟨ B (f y) ⟩ (g y b)) i j

  h : {x y : ⟨ τ ⟩} (s : x ＝ y) {a : ⟨ A x ⟩} {b : ⟨ A y ⟩}
    → transport (λ - → ⟨ B (f -) ⟩) s (g x a) ≺⟨ B (f y) ⟩ (g y b)
    → transport (λ - → ⟨ A - ⟩) s a ≺⟨ A y ⟩ b
  h {x} refl {a} {b} = γ x a b

  p : transport (λ - → ⟨ A - ⟩) (c r) a ≺⟨ A y ⟩ b
  p = h (c r) k

ι𝟙ᵒ-is-order-reflecting : is-order-reflecting (succₒ ω) ℕ∞ᵒ ι𝟙ᵒ
ι𝟙ᵒ-is-order-reflecting (inl n) (inl m) l =
 ℕ-to-ℕ∞-order-reflecting n m l
ι𝟙ᵒ-is-order-reflecting (inl n) (inr *) l = *
ι𝟙ᵒ-is-order-reflecting (inr *) (inl m) (n , (p , l)) =
 𝟘-elim (∞-is-not-finite n p)
ι𝟙ᵒ-is-order-reflecting (inr *) (inr *) (n , (p , l)) =
 𝟘-elim (∞-is-not-finite n p)

over-ι-map-is-order-reflecting  : (τ : ℕ → Ordᵀ) (z : ℕ + 𝟙)
                                → is-order-reflecting
                                    ((τ ↗ (over , over-embedding)) z)
                                    ((τ ↗ embedding-ℕ-to-ℕ∞ fe₀) (ι𝟙 z))
                                    (over-ι-map (λ n → ⟨ τ n ⟩) z)
over-ι-map-is-order-reflecting τ (inl n) x y ((m , p) , l) = (n , refl) , q
 where
  x' : ⟨ τ n ⟩
  x' = over-ι-map (λ n → ⟨ τ n ⟩) (inl n) x (n , refl)

  y' : ⟨ τ n ⟩
  y' = over-ι-map (λ n → ⟨ τ n ⟩) (inl n) y (n , refl)

  r : n , refl ＝ m , p
  r = ℕ-to-ℕ∞-is-embedding fe₀ (ι n) (n , refl) (m , p)

  t : ⟨ τ n ⟩ → ⟨ τ m ⟩
  t = transport (λ - → ⟨ τ (pr₁ -) ⟩) r

  tr : {w t : fiber ι (ι n)} (r : w ＝ t)
     → is-order-reflecting
        (τ (pr₁ w))
        (τ (pr₁ t))
        (transport (λ - → ⟨ τ (pr₁ -) ⟩) r)
  tr refl x y l = l

  a : t x' ＝ over-ι-map (λ n → ⟨ τ n ⟩) (inl n) x (m , p)
  a = apd (over-ι-map (λ n → ⟨ τ n ⟩) (inl n) x) r

  b : t y' ＝ over-ι-map (λ n → ⟨ τ n ⟩) (inl n) y (m , p)
  b = apd (over-ι-map (λ n → ⟨ τ n ⟩) (inl n) y) r

  c : t x' ≺⟨ τ m ⟩ t y'
  c = transport₂⁻¹ (λ a b → a ≺⟨ τ m ⟩ b) a b l

  d : x' ≺⟨ τ n ⟩ y'
  d = tr r _ _ c

  q : x (n , refl) ≺⟨ τ n ⟩ y (n , refl)
  q = transport₂
       (λ a b → a ≺⟨ τ n ⟩ b)
       (over-ι-map-left (λ n → ⟨ τ n ⟩) n x)
       (over-ι-map-left (λ n → ⟨ τ n ⟩) n y)
       d
over-ι-map-is-order-reflecting τ (inr *) x y ((m , p) , l) =
 𝟘-elim (∞-is-not-finite m (p ⁻¹))

∑-up-is-order-reflecting : (τ : ℕ → Ordᵀ)
                         → is-order-reflecting (∑₁ τ) (∑¹ τ) (∑-up τ)
∑-up-is-order-reflecting τ  = pair-fun-is-order-reflecting
                               (succₒ ω)
                               ℕ∞ᵒ
                               (τ ↗ (over , over-embedding))
                               (τ  ↗ embedding-ℕ-to-ℕ∞ fe₀)
                               ι𝟙ᵒ
                               (over-ι-map (λ n → ⟨ τ n ⟩))
                               ι𝟙ᵒ-is-order-reflecting
                               (ι𝟙-is-embedding fe₀)
                               (over-ι-map-is-order-reflecting τ)

Overᵒ-is-order-reflecting : (τ υ : ℕ → Ordᵀ)
                            (f : (n : ℕ) → ⟨ τ n ⟩ → ⟨ υ n ⟩)
                          → ((n : ℕ) → is-order-reflecting (τ n) (υ n) (f n))
                          → (z : ℕ + 𝟙) → is-order-reflecting
                                           ((τ ↗ (over , over-embedding)) z)
                                           ((υ ↗ (over , over-embedding)) z)
                                           (Overᵒ τ υ f z)
Overᵒ-is-order-reflecting τ υ f p (inl n) x y ((.n , refl) , l) =
 (n , refl) , p n _ _ l
Overᵒ-is-order-reflecting τ υ f p (inr *) x y ((n , q) , l) =
 𝟘-elim (+disjoint q)

∑₁-functor-is-order-reflecting
 : (τ υ : ℕ → Ordᵀ)
   (f : (n : ℕ) → ⟨ τ n ⟩ → ⟨ υ n ⟩)
 → ((n : ℕ) → is-order-reflecting (τ n) (υ n) (f n))
 → is-order-reflecting (∑₁ τ) (∑₁ υ) (∑₁-functor τ υ f)
∑₁-functor-is-order-reflecting τ υ f p =
 pair-fun-is-order-reflecting
  (succₒ ω)
  (succₒ ω)
  (τ ↗ (over , over-embedding))
  (υ ↗ (over , over-embedding))
  id
  (Over (λ n → ⟨ τ n ⟩) (λ n → ⟨ υ n ⟩) f)
  (λ x y l → l)
  id-is-embedding
  (Overᵒ-is-order-reflecting τ υ f p)

∑↑-is-order-reflecting : (τ υ : ℕ → Ordᵀ) (f : (n : ℕ) → ⟨ τ n ⟩ → ⟨ υ n ⟩)
                       → ((n : ℕ) → is-order-reflecting (τ n) (υ n) (f n))
                       → is-order-reflecting (∑₁ τ) (∑¹ υ) (∑↑ τ υ f)
∑↑-is-order-reflecting τ υ f p = comp-is-order-reflecting
                                  (∑₁ τ)
                                  (∑₁ υ )
                                  (∑¹ υ)
                                  (Σ₁-functor
                                    (λ n → ⟨ τ n ⟩)
                                    (λ n → ⟨ υ n ⟩)
                                    f)
                                  (∑-up υ)
                                  (∑₁-functor-is-order-reflecting τ υ f p)
                                  (∑-up-is-order-reflecting υ)
\end{code}

Added August 2026. Some lemmas about Σ↑ of the module
TypeTopology.SquashedSum that are not already available here,
transported to families of topped ordinals, namely density and being
an embedding, the isolatedness and limit-point lemmas, and the
characterization of Σ↑ as an equivalence.

\begin{code}

∑↑-dense : (τ υ : ℕ → Ordᵀ)
           (f : (n : ℕ) → ⟨ τ n ⟩ → ⟨ υ n ⟩)
         → ((n : ℕ) → is-dense (f n))
         → is-dense (∑↑ τ υ f)
∑↑-dense τ υ = Σ↑-dense (λ n → ⟨ τ n ⟩) (λ n → ⟨ υ n ⟩)

∑↑-embedding : (τ υ : ℕ → Ordᵀ)
               (f : (n : ℕ) → ⟨ τ n ⟩ → ⟨ υ n ⟩)
             → ((n : ℕ) → is-embedding (f n))
             → is-embedding (∑↑ τ υ f)
∑↑-embedding τ υ = Σ↑-embedding (λ n → ⟨ τ n ⟩) (λ n → ⟨ υ n ⟩)

∑↑-preserves-isolatedness : (τ υ : ℕ → Ordᵀ)
                            (f : (n : ℕ) → ⟨ τ n ⟩ → ⟨ υ n ⟩)
                            (n : ℕ)
                            (φ : ⟨ (τ ↗ (over , over-embedding)) (inl n) ⟩)
                          → is-isolated (f n (φ (n , refl)))
                          → is-isolated (∑↑ τ υ f (inl n , φ))
∑↑-preserves-isolatedness τ υ = Σ↑-preserves-isolatedness
                                 (λ n → ⟨ τ n ⟩)
                                 (λ n → ⟨ υ n ⟩)

∑↑-reflects-isolatedness : (τ υ : ℕ → Ordᵀ)
                           (f : (n : ℕ) → ⟨ τ n ⟩ → ⟨ υ n ⟩)
                           (n : ℕ)
                           (φ : ⟨ (τ ↗ (over , over-embedding)) (inl n) ⟩)
                         → is-isolated (∑↑ τ υ f (inl n , φ))
                         → is-isolated (f n (φ (n , refl)))
∑↑-reflects-isolatedness τ υ = Σ↑-reflects-isolatedness
                                (λ n → ⟨ τ n ⟩)
                                (λ n → ⟨ υ n ⟩)

∑↑-reflects-weak-isolatedness : (τ υ : ℕ → Ordᵀ)
                                (f : (n : ℕ) → ⟨ τ n ⟩ → ⟨ υ n ⟩)
                                (n : ℕ)
                                (φ : ⟨ (τ ↗ (over , over-embedding)) (inl n) ⟩)
                              → is-weakly-isolated (∑↑ τ υ f (inl n , φ))
                              → is-weakly-isolated (f n (φ (n , refl)))
∑↑-reflects-weak-isolatedness τ υ = Σ↑-reflects-weak-isolatedness
                                     (λ n → ⟨ τ n ⟩)
                                     (λ n → ⟨ υ n ⟩)

∑↑-limit-point : (τ υ : ℕ → Ordᵀ)
                 (f : (n : ℕ) → ⟨ τ n ⟩ → ⟨ υ n ⟩)
               → ((n : ℕ) → is-compact∙ ⟨ υ n ⟩)
               → (φ : ⟨ (τ ↗ (over , over-embedding)) (inr ⋆) ⟩)
               → is-limit-point (∑↑ τ υ f (inr ⋆ , φ))
∑↑-limit-point τ υ = Σ↑-limit-point (λ n → ⟨ τ n ⟩) (λ n → ⟨ υ n ⟩)

∑↑-limit-point⁺ : (τ υ : ℕ → Ordᵀ)
                  (f : (n : ℕ) → ⟨ τ n ⟩ → ⟨ υ n ⟩)
                → ((n : ℕ) → is-compact∙ ⟨ υ n ⟩)
                → (φ : ⟨ (τ ↗ (over , over-embedding)) (inr ⋆) ⟩)
                → is-limit-point⁺ (∑↑ τ υ f (inr ⋆ , φ))
∑↑-limit-point⁺ τ υ = Σ↑-limit-point⁺ (λ n → ⟨ τ n ⟩) (λ n → ⟨ υ n ⟩)

∑↑-is-equiv : is-equiv ι𝟙
            → (τ υ : ℕ → Ordᵀ)
              (f : (n : ℕ) → ⟨ τ n ⟩ → ⟨ υ n ⟩)
            → ((n : ℕ) → is-equiv (f n))
            → is-equiv (∑↑ τ υ f)
∑↑-is-equiv j τ υ = Σ↑-is-equiv j (λ n → ⟨ τ n ⟩) (λ n → ⟨ υ n ⟩)

\end{code}


28 July 2018. Inf property.

\begin{code}

𝟙ᵒ-has-infs-of-complemented-subsets : has-infs-of-complemented-subsets (𝟙ᵒ {𝓤})
𝟙ᵒ-has-infs-of-complemented-subsets p = ⋆ , f , g , h
 where
  f : (Σ x ꞉ 𝟙 , p x ＝ ₀) → p ⋆ ＝ ₀
  f (⋆ , r) = r

  g : (x : 𝟙) → p x ＝ ₀ → ⋆ ≾⟨ 𝟙ᵒ ⟩ x
  g ⋆ r a = 𝟘-elim a

  h : (x : 𝟙) → is-roots-lower-bound (λ x y → x ≾⟨ 𝟙ᵒ ⟩ y) p x → x ≾⟨ 𝟙ᵒ ⟩ ⋆
  h ⋆ φ a = 𝟘-elim a

𝟚ᵒ-has-infs-of-complemented-subsets : has-infs-of-complemented-subsets 𝟚ᵒ
𝟚ᵒ-has-infs-of-complemented-subsets p = 𝟚-equality-cases φ γ
 where
  _≤_ : 𝟙 + 𝟙 → 𝟙 + 𝟙 → 𝓤₀ ̇
  x ≤ y = x ≾⟨ 𝟚ᵒ ⟩ y

  φ : (r : p (inl ⋆) ＝ ₀) → Σ x ꞉ 𝟙 + 𝟙 , is-conditional-root _≤_ p x × is-roots-infimum _≤_ p x
  φ r = inl ⋆ , f , g , h
   where
    f : (Σ x ꞉ 𝟙 + 𝟙 , p x ＝ ₀) → p (inl ⋆) ＝ ₀
    f (inl ⋆ , s) = s
    f (inr ⋆ , s) = r

    g : (x : 𝟙 + 𝟙) → p x ＝ ₀ → inl ⋆ ≤ x
    g (inl ⋆) s l = 𝟘-elim l
    g (inr ⋆) s l = 𝟘-elim l

    h : (x : 𝟙 + 𝟙) → is-roots-lower-bound _≤_ p x → x ≤ inl ⋆
    h (inl ⋆) φ l = 𝟘-elim l
    h (inr ⋆) φ ⋆ = φ (inl ⋆) r ⋆

  γ : (r : p (inl ⋆) ＝ ₁)
    → Σ x ꞉ 𝟙 + 𝟙 , is-conditional-root _≤_ p x × is-roots-infimum _≤_ p x
  γ r = inr ⋆ , f , g , h
   where
    f : (Σ x ꞉ 𝟙 + 𝟙 , p x ＝ ₀) → p (inr ⋆) ＝ ₀
    f (inl ⋆ , s) = 𝟘-elim (zero-is-not-one (s ⁻¹ ∙ r))
    f (inr ⋆ , s) = s

    g : (x : 𝟙 + 𝟙) → p x ＝ ₀ → inr ⋆ ≤ x
    g (inl ⋆) s l = 𝟘-elim (zero-is-not-one (s ⁻¹ ∙ r))
    g (inr ⋆) s l = 𝟘-elim l

    h : (x : 𝟙 + 𝟙) → is-roots-lower-bound _≤_ p x → x ≤ inr ⋆
    h (inl ⋆) φ a = 𝟘-elim a
    h (inr ⋆) φ a = 𝟘-elim a

\end{code}

It is not necessary to use propositional extensionality to prove the
following, but it is simpler to do so given that we have already
proved has-infs-of-complemented-subsets for various types using
different, logically equivalent orders.

TODO. This is a bottleneck. The use of propext here propagates to a
number of files which otherwise wouldn't need to assume propext. Maybe
get rid of this at some point, here and in the other files.

\begin{code}

∑-has-infs-of-complemented-subsets
 : propext 𝓤₀
 → (τ : Ordᵀ) (υ : ⟨ τ ⟩ → Ordᵀ)
 → has-infs-of-complemented-subsets τ
 → ((x : ⟨ τ ⟩) → has-infs-of-complemented-subsets (υ x))
 → has-infs-of-complemented-subsets (∑ τ υ)
∑-has-infs-of-complemented-subsets pe τ υ ε δ = γ
 where
  _≤_ : ⟨ ∑ τ υ ⟩ → ⟨ ∑ τ υ ⟩ → 𝓤₀ ̇
  _≤_ = lex-order (λ x y → x ≾⟨ τ ⟩ y) (λ {x} a b → a ≾⟨ υ x ⟩ b)

  ≤-prop-valued : (z t : ⟨ ∑ τ υ ⟩) → is-prop (z ≤ t)
  ≤-prop-valued (x , a) (y , b) (p , u) (q , v) =
   to-Σ-＝
    (≾-prop-valued τ x y p q ,
    dfunext fe₀ (λ r → ≾-prop-valued (υ y) _ _ _ _))

  φ : has-inf _≤_
  φ = Σ-has-inf ((λ x y → x ≾⟨ τ ⟩ y)) ((λ {x} a b → a ≾⟨ υ x ⟩ b)) ε δ

  open lexicographic-commutation
         (underlying-order τ)
         (λ {x} → underlying-order (υ x))
         (𝟘 {𝓤₀})
       hiding (_≤_)

  i : (z t : ⟨ ∑ τ υ ⟩) → z ≤ t → z ≾⟨ ∑ τ υ ⟩ t
  i (x , a) (y , b) = back y x b a

  j : (z t : ⟨ ∑ τ υ ⟩) → z ≾⟨ ∑ τ υ ⟩ t → z ≤ t
  j (x , a) (y , b) = forth y x b a

  k : (z t : ⟨ ∑ τ υ ⟩) → z ≤ t ＝ z ≾⟨ ∑ τ υ ⟩ t
  k z t = pe (≤-prop-valued z t) (≾-prop-valued (∑ τ υ) z t) (i z t) (j z t)

  l : _≤_ ＝ (λ z t → z ≾⟨ ∑ τ υ ⟩ t)
  l = dfunext (fe 𝓤₀ 𝓤₁) (λ z → dfunext (fe 𝓤₀ 𝓤₁) (k z))

  γ : has-infs-of-complemented-subsets (∑ τ υ)
  γ = transport has-inf l φ

ℕ∞ᵒ-has-infs-of-complemented-subsets : propext 𝓤₀
                                     → has-infs-of-complemented-subsets ℕ∞ᵒ
ℕ∞ᵒ-has-infs-of-complemented-subsets pe = transport has-inf p (ℕ∞-has-inf fe₀)
 where
  p : _≼ℕ∞_ ＝ underlying-weak-order ℕ∞ᵒ
  p = dfunext (fe 𝓤₀ 𝓤₁)
       (λ u → dfunext (fe 𝓤₀ 𝓤₁)
                (λ v → pe (≼-is-prop-valued fe₀ u v)
                          (≾-prop-valued ℕ∞ᵒ u v)
                          (≼-gives-not-≺ u v)
                          (not-≺-gives-≼ fe₀ u v)))


∑¹-has-infs-of-complemented-subsets
 : propext 𝓤₀
 → (τ : ℕ → Ordᵀ)
 → ((n : ℕ) → has-infs-of-complemented-subsets (τ n))
 → has-infs-of-complemented-subsets (∑¹ τ)
∑¹-has-infs-of-complemented-subsets pe τ ε =
 ∑-has-infs-of-complemented-subsets pe
  ℕ∞ᵒ
  (λ (x : ℕ∞) → (τ ↗ embedding-ℕ-to-ℕ∞ fe₀) x)
  (ℕ∞ᵒ-has-infs-of-complemented-subsets pe)
  a
 where
  a : (x : ⟨ ℕ∞ᵒ ⟩) → has-infs-of-complemented-subsets
                       ((τ ↗ embedding-ℕ-to-ℕ∞ fe₀) x)
  a x = micro-inf-tychonoff fe
         (ℕ-to-ℕ∞-is-embedding fe₀ x)
         (λ {w} x y → x ≺⟨ τ (pr₁ w) ⟩ y)
         (λ w → ε (pr₁ w))

\end{code}

Added August 2026.

\begin{code}

∑-≃ₒ : (τ : Ordᵀ) (υ υ' : ⟨ τ ⟩ → Ordᵀ)
     → ((x : ⟨ τ ⟩) → [ υ x ] ≃ₒ [ υ' x ])
     → [ ∑ τ υ ] ≃ₒ [ ∑ τ υ' ]
∑-≃ₒ τ υ υ' g = f ,
                order-preserving-reflecting-equivs-are-order-equivs
                 [ ∑ τ υ ] [ ∑ τ υ' ] f
                 f-is-equiv
                 f-is-order-preserving
                 f-is-order-reflecting
 where
  h : (x : ⟨ τ ⟩) → ⟨ υ x ⟩ → ⟨ υ' x ⟩
  h x = ≃ₒ-to-fun [ υ x ] [ υ' x ] (g x)

  e : (x : ⟨ τ ⟩) → is-order-equiv [ υ x ] [ υ' x ] (h x)
  e x = ≃ₒ-to-fun-is-order-equiv [ υ x ] [ υ' x ] (g x)

  f : ⟨ ∑ τ υ ⟩ → ⟨ ∑ τ υ' ⟩
  f = pair-fun id h

  f-is-equiv : is-equiv f
  f-is-equiv = pair-fun-is-equiv
                id
                h
                (id-is-equiv ⟨ τ ⟩)
                (λ x → order-equivs-are-equivs [ υ x ] [ υ' x ] (e x))

  f-is-order-preserving : is-order-preserving (∑ τ υ) (∑ τ υ') f
  f-is-order-preserving =
   pair-fun-is-order-preserving τ τ υ υ' id h
    (λ x y l → l)
    (λ x → order-equivs-are-order-preserving [ υ x ] [ υ' x ] (e x))

  f-is-order-reflecting : is-order-reflecting (∑ τ υ) (∑ τ υ') f
  f-is-order-reflecting =
   pair-fun-is-order-reflecting τ τ υ υ' id h
    (λ x y l → l)
    id-is-embedding
    (λ x → order-equivs-are-order-reflecting [ υ x ] [ υ' x ] (h x) (e x))

\end{code}

Added August 2026. The extension of the constant family at the
one-point ordinal is again the one-point ordinal, and a sum whose
summands are all one-point ordinals is the index type. Together these
identify the two extended sums of the constant family at 𝟙ᵒ.

\begin{code}

↗-of-𝟙ᵒ : {I J : 𝓤₀ ̇ } (𝓮 : I ↪ J) (j : J)
        → [ ((λ _ → 𝟙ᵒ) ↗ 𝓮) j ] ≃ₒ 𝟙ₒ {𝓤₀}
↗-of-𝟙ᵒ {I} {J} 𝓮 j =
 f ,
 (λ u v (w , l) → 𝟘-elim l) ,
 f-is-equiv ,
 (λ x y l → 𝟘-elim l)
 where
  f : ⟨ ((λ _ → 𝟙ᵒ) ↗ 𝓮) j ⟩ → 𝟙
  f _ = ⋆

  f-is-equiv : is-equiv f
  f-is-equiv = qinvs-are-equivs f
                ((λ _ _ → ⋆) ,
                 (λ u → dfunext (fe 𝓤₀ 𝓤₀) (λ w → 𝟙-is-prop ⋆ (u w))) ,
                 (λ ⋆ → refl))

∑-of-𝟙ᵒ : (τ : Ordᵀ) (υ : ⟨ τ ⟩ → Ordᵀ)
        → ((x : ⟨ τ ⟩) → [ υ x ] ≃ₒ 𝟙ₒ {𝓤₀})
        → [ ∑ τ υ ] ≃ₒ [ τ ]
∑-of-𝟙ᵒ τ υ e =
 f ,
 order-preserving-reflecting-equivs-are-order-equivs
  [ ∑ τ υ ] [ τ ] f
  f-is-equiv f-is-order-preserving f-is-order-reflecting
 where
  f : ⟨ ∑ τ υ ⟩ → ⟨ τ ⟩
  f = pr₁

  s : (x : ⟨ τ ⟩) → is-singleton ⟨ υ x ⟩
  s x = equiv-to-singleton
         (≃ₒ-to-fun [ υ x ] (𝟙ₒ {𝓤₀}) (e x) ,
          ≃ₒ-to-fun-is-equiv [ υ x ] (𝟙ₒ {𝓤₀}) (e x))
         𝟙-is-singleton

  f-is-equiv : is-equiv f
  f-is-equiv = pr₁-is-equiv ⟨ τ ⟩ (λ x → ⟨ υ x ⟩) s

  f-is-order-preserving : is-order-preserving (∑ τ υ) τ f
  f-is-order-preserving (x , y) (x' , y') (inl l) = l
  f-is-order-preserving (x , y) (x , y') (inr (refl , m)) =
   𝟘-elim (order-equivs-are-order-preserving
            [ υ x ] (𝟙ₒ {𝓤₀})
            (≃ₒ-to-fun-is-order-equiv [ υ x ] (𝟙ₒ {𝓤₀}) (e x))
            y y' m)

  f-is-order-reflecting : is-order-reflecting (∑ τ υ) τ f
  f-is-order-reflecting (x , y) (x' , y') l = inl l

∑¹-of-𝟙ᵒ : [ ∑¹ (λ _ → 𝟙ᵒ) ] ≃ₒ [ ℕ∞ᵒ ]
∑¹-of-𝟙ᵒ = ∑-of-𝟙ᵒ
            ℕ∞ᵒ
            ((λ _ → 𝟙ᵒ) ↗ embedding-ℕ-to-ℕ∞ fe₀)
            (↗-of-𝟙ᵒ (embedding-ℕ-to-ℕ∞ fe₀))

∑₁-of-𝟙ᵒ : [ ∑₁ (λ _ → 𝟙ᵒ) ] ≃ₒ [ succₒ ω ]
∑₁-of-𝟙ᵒ = ∑-of-𝟙ᵒ
            (succₒ ω)
            ((λ _ → 𝟙ᵒ) ↗ (over , over-embedding))
            (↗-of-𝟙ᵒ (over , over-embedding))

\end{code}

Added 2nd September 2026.

The least element property for complemented subsets is invariant under
order isomorphism, and for the ordinal ω + 1 it amounts to LPO.

\begin{code}

≃ₒ-gives-has-least-roots : (α : Ordinal 𝓤) (β : Ordinal 𝓥)
                         → α ≃ₒ β
                         → has-least-roots (underlying-weak-order α)
                         → has-least-roots (underlying-weak-order β)
≃ₒ-gives-has-least-roots α β (f , _ , e , iop) h q ν = γ
 where
  g : ⟨ β ⟩ → ⟨ α ⟩
  g = inverse f e

  p : ⟨ α ⟩ → 𝟚
  p = q ∘ f

  p-root : (y : ⟨ β ⟩) → q y ＝ ₀ → p (g y) ＝ ₀
  p-root y d = ap q (inverses-are-sections f e y) ∙ d

  ν' : ¬¬ (Σ x ꞉ ⟨ α ⟩ , p x ＝ ₀)
  ν' u = ν (λ (y , d) → u (g y , p-root y d))

  σ : Σ x₀ ꞉ ⟨ α ⟩ , is-least-root (underlying-weak-order α) p x₀
  σ = h p ν'

  x₀ : ⟨ α ⟩
  x₀ = pr₁ σ

  y₀-is-root : q (f x₀) ＝ ₀
  y₀-is-root = pr₁ (pr₂ σ)

  y₀-is-roots-lower-bound : (y : ⟨ β ⟩) → q y ＝ ₀ → f x₀ ≾⟨ β ⟩ y
  y₀-is-roots-lower-bound y d l = pr₂ (pr₂ σ) (g y) (p-root y d) I
   where
    I : g y ≺⟨ α ⟩ x₀
    I = transport
         (λ - → g y ≺⟨ α ⟩ -)
         (inverses-are-retractions f e x₀)
         (iop y (f x₀) l)

  γ : Σ y₀ ꞉ ⟨ β ⟩ , is-least-root (underlying-weak-order β) q y₀
  γ = f x₀ , y₀-is-root , y₀-is-roots-lower-bound

succₒ-ω-least-roots-gives-LPO
 : has-least-roots-of-complemented-subsets (succₒ ω) → LPO
succₒ-ω-least-roots-gives-LPO h = compact-ℕ-gives-LPO fe₀ c
 where
  c : is-compact ℕ
  c α = γ (h p ν)
   where
    p : ⟨ succₒ ω ⟩ → 𝟚
    p (inl n) = α n
    p (inr ⋆) = ₀

    ν : ¬¬ (Σ x ꞉ ⟨ succₒ ω ⟩ , p x ＝ ₀)
    ν u = u (inr ⋆ , refl)

    γ : (Σ x₀ ꞉ ⟨ succₒ ω ⟩ , is-least-root
                               (underlying-weak-order (succₒ ω))
                               p
                               x₀)
      → (Σ n ꞉ ℕ , α n ＝ ₀) + (Π n ꞉ ℕ , α n ＝ ₁)
    γ (inl n , e , _)  = inl (n , e)
    γ (inr ⋆ , _ , lb) = inr (λ n → different-from-₀-equal-₁ (δ n))
     where
      δ : (n : ℕ) → α n ≠ ₀
      δ n e = lb (inl n) e ⋆

\end{code}
