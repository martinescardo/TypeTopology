Tom de Jong, Nicolai Kraus, Fredrik Nordvall Forsberg, Chuangjie Xu,
13 November 2023.

TEMPORARILY SPLIT UP TO SPEED UP TYPECHECKING

\begin{code}

{-# OPTIONS --safe --without-K --no-exact-split #-}

open import UF.Univalence

module Ordinals.Exponentiation-More
       (ua : Univalence)
       where

open import UF.Base
open import UF.Embeddings hiding (⌊_⌋)
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.ExcludedMiddle
open import UF.FunExt
open import UF.PropTrunc
open import UF.Sets
open import UF.Size
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.UA-FunExt

private
 fe : FunExt
 fe = Univalence-gives-FunExt ua

 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

 pe : PropExt
 pe = Univalence-gives-PropExt ua

open import MLTT.Plus-Properties
open import MLTT.Spartan
open import MLTT.Sigma
-- open import Notation.CanonicalMap
open import Ordinals.Arithmetic fe
open import Ordinals.ArithmeticProperties ua
open import Ordinals.ConvergentSequence ua
open import Ordinals.Equivalence
open import Ordinals.Maps
open import Ordinals.Notions
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.Type
open import Ordinals.Underlying

-- our imports
open import MLTT.List
open import Ordinals.Exponentiation ua

{-

(1 + α)^(⋁ᵢ βᵢ)

= Σ l : List (α × ⋁ᵢ βᵢ) , decreasing-pr2 l
= Σ l : List (⋁ᵢ (α × βᵢ)) , ...
?= ⋁ᵢ (Σ l : List (α × βᵢ) , decreasing-pr2 l)
= ⋁ᵢ (1 + α)^β


(1) Try for general families
(1.5) Try for monotone families
(2) Try for (x ↦ α ↓ x) for α an ordinal

-}

order-reflecting-and-partial-inverse-is-initial-segment : (α β : Ordinal 𝓤)
                                                       (f : ⟨ α ⟩ → ⟨ β ⟩)
                                                     → is-order-reflecting α β f
                                                     → ((a : ⟨ α ⟩)(b : ⟨ β ⟩) → b ≺⟨ β ⟩ f a → Σ a' ꞉ ⟨ α ⟩ , f a' ＝ b)
                                                     → is-initial-segment α β f
order-reflecting-and-partial-inverse-is-initial-segment α β f p i a b m = a' , p' , q'
  where
    q : Σ a' ꞉ ⟨ α ⟩ , f a' ＝ b
    q = i a b m
    a' : ⟨ α ⟩
    a' = pr₁ q
    q' : f a' ＝ b
    q' = pr₂ q

    m' : f a' ≺⟨ β ⟩ f a
    m' = transport⁻¹ (λ - → - ≺⟨ β ⟩ f a) q' m
    p' : a' ≺⟨ α ⟩ a
    p' = p a' a m'

module _ (pt : propositional-truncations-exist)
         (sr : Set-Replacement pt)
       where

 open PropositionalTruncation pt

 open import Ordinals.OrdinalOfOrdinalsSuprema ua
 open suprema pt sr

 open import UF.ImageAndSurjection pt

 surjective-simulation-gives-equality : (α β : Ordinal 𝓤)
                                      → (f : ⟨ α ⟩ → ⟨ β ⟩)
                                      → is-simulation α β f
                                      → is-surjection f
                                      → α ＝ β
 surjective-simulation-gives-equality α β f sim surj = ⊴-antisym α β (f , sim) (h₀ , h₀-sim)
   where
     prp : (b : ⟨ β ⟩) → is-prop (Σ a ꞉ ⟨ α ⟩ , (f a ＝ b))
     prp b (a , p) (a' , p') = to-subtype-＝ (λ a → underlying-type-is-set fe β)
                                            (simulations-are-lc α β f sim (p ∙ p' ⁻¹))

     h : (b : ⟨ β ⟩) → Σ a ꞉ ⟨ α ⟩ , (f a ＝ b)
     h b = ∥∥-rec (prp b) id (surj b)

     h₀ : ⟨ β ⟩ → ⟨ α ⟩
     h₀ b = pr₁ (h b)

     h₀-retract-of-f : (b : ⟨ β ⟩) → f (h₀ b) ＝ b
     h₀-retract-of-f b = pr₂ (h b)

     h₀-is-initial-segment : is-initial-segment β α h₀
     h₀-is-initial-segment b a p = f a , p'' , q
       where
        p' : f a ≺⟨ β ⟩ (f (h₀ b))
        p' = simulations-are-order-preserving α β f sim a (h₀ b) p

        p'' : f a ≺⟨ β ⟩ b
        p'' = transport (λ - → f a ≺⟨ β ⟩ -) (h₀-retract-of-f b) p'

        q : h₀ (f a) ＝ a
        q = simulations-are-lc α β f sim (h₀-retract-of-f (f a))

     h₀-is-order-preserving : is-order-preserving β α h₀
     h₀-is-order-preserving b b' p = p''
       where
         p' : f (h₀ b) ≺⟨ β ⟩ f (h₀ b')
         p' = transport₂⁻¹ (underlying-order β) (h₀-retract-of-f b) (h₀-retract-of-f b') p

         p'' : h₀ b  ≺⟨ α ⟩ (h₀ b')
         p'' = simulations-are-order-reflecting α β f sim (h₀ b) (h₀ b') p'

     h₀-sim : is-simulation β α h₀
     h₀-sim = h₀-is-initial-segment , h₀-is-order-preserving

 module _ {I : 𝓤 ̇  }
          (i₀ : I)
          (β : I → Ordinal 𝓤)
          (α : Ordinal 𝓤)
  where

  {-
  f : ⟨ [𝟙+ α ]^ (sup β) ⟩ → ⟨ sup (λ i → [𝟙+ α ]^ (β i)) ⟩
  f ([] , δ) = sum-to-sup (λ i → [𝟙+ α ]^ β i) (i₀ , ([] , []-decr))
  f ((a , x ∷ l) , δ) = {!!}
  -}

  private
   γ : I → Ordinal 𝓤
   γ i = [𝟙+ α ]^ (β i)

   ι : (ζ : I → Ordinal 𝓤) → {i : I} → ⟨ ζ i ⟩ → ⟨ sup ζ ⟩
   ι ζ {i} = pr₁ (sup-is-upper-bound ζ i)

   ι-is-simulation : (ζ : I → Ordinal 𝓤) → {i : I}
                   → is-simulation (ζ i) (sup ζ ) (ι ζ)
   ι-is-simulation ζ {i} = pr₂ (sup-is-upper-bound ζ i)

   ι-is-order-preserving : (ζ : I → Ordinal 𝓤) {i : I}
                         → is-order-preserving (ζ i) (sup ζ) (ι ζ)
   ι-is-order-preserving ζ {i} = simulations-are-order-preserving (ζ i) (sup ζ) (ι ζ) (ι-is-simulation ζ)

   ι-is-order-reflecting : (ζ : I → Ordinal 𝓤) {i : I}
                         → is-order-reflecting (ζ i) (sup ζ) (ι ζ)
   ι-is-order-reflecting ζ {i} = simulations-are-order-reflecting (ζ i) (sup ζ) (ι ζ) (ι-is-simulation ζ)

   ι-is-lc : (ζ : I → Ordinal 𝓤) {i : I}
           → left-cancellable (ι ζ)
   ι-is-lc ζ {i} = simulations-are-lc (ζ i) (sup ζ) (ι ζ) (ι-is-simulation ζ)

   ι-is-initial-segment : (ζ : I → Ordinal 𝓤) → {i : I}
                        → is-initial-segment (ζ i) (sup ζ ) (ι ζ)
   ι-is-initial-segment ζ {i} = simulations-are-initial-segments (ζ i) (sup ζ) (ι ζ) (ι-is-simulation ζ)

   ι-is-surjective : (ζ : I → Ordinal 𝓤) (s : ⟨ sup ζ ⟩)
                   → ∃ i ꞉ I , Σ x ꞉ ⟨ ζ i ⟩ , ι ζ {i} x ＝ s
   ι-is-surjective = {!!}

   ι-is-surjective⁺ : (ζ : I → Ordinal 𝓤) (s : ⟨ sup ζ ⟩) (i : I) (x : ⟨ ζ i ⟩)
                    → s ≺⟨ sup ζ ⟩ ι ζ x
                    → Σ y ꞉ ⟨ ζ i ⟩ , ι ζ {i} y ＝ s
   ι-is-surjective⁺ ζ s i x p =
    h (simulations-are-initial-segments (ζ i) (sup ζ) (ι ζ) (ι-is-simulation ζ) x s p)
    where
     h : Σ y ꞉ ⟨ ζ i ⟩ , y ≺⟨ ζ i ⟩ x × (ι ζ y ＝ s)
       → Σ y ꞉ ⟨ ζ i ⟩ , ι ζ {i} y ＝ s
     h (y , (_ , q)) = y , q

   module _ (i : I) where
    f₁ : List (⟨ α ×ₒ β i ⟩) → List (⟨ α ×ₒ sup β ⟩)
    f₁ [] = []
    f₁ (a , b ∷ l) = a , ι β b ∷ f₁ l
    f₂ : (l : List (⟨ α ×ₒ β i ⟩))
       → is-decreasing-pr₂ α (β i) l
       → is-decreasing-pr₂ α (sup β) (f₁ l)
    f₂ [] δ = []-decr
    f₂ (a , b ∷ []) δ = sing-decr
    f₂ (a , b ∷ a' , b' ∷ l) (many-decr p δ) =
      many-decr (simulations-are-order-preserving (β i) (sup β)
                  (ι β)
                  (pr₂ (sup-is-upper-bound β i)) b' b p)
                (f₂ (a' , b' ∷ l) δ)
    f : ⟨ γ i ⟩ → ⟨ [𝟙+ α ]^ (sup β) ⟩
    f (l , δ) = f₁ l , f₂ l δ

   f₁-surj-lemma : (a : ⟨ α ⟩) (i : I) (b : ⟨ β i ⟩) (l : List (⟨ α ×ₒ sup β ⟩))
                 → is-decreasing-pr₂ α (sup β) (a , ι β b ∷ l)
                 → Σ l' ꞉ List (⟨ α ×ₒ β i ⟩) , (a , ι β b ∷ l) ＝ f₁ i l'
   f₁-surj-lemma a i b [] δ = (a , b ∷ []) , refl
   f₁-surj-lemma a i b ((a' , s) ∷ l) δ = (a , b ∷ l') , ap (a , ι β b ∷_) (ap (λ - → a' , - ∷ l) ((pr₂ lem) ⁻¹) ∙ pr₂ IH)
    where
     lem : Σ b' ꞉ ⟨ β i ⟩ , ι β b' ＝ s
     lem = ι-is-surjective⁺ β s i b (is-decreasing-heads (underlying-order (sup β)) δ)
     b' : ⟨ β i ⟩
     b' = pr₁ lem
     IH : Σ l' ꞉ List (⟨ α ×ₒ β i ⟩) , (a' , ι β b' ∷ l) ＝ f₁ i l'
     IH = f₁-surj-lemma a' i b' l (transport⁻¹ (λ - → is-decreasing-pr₂ α (sup β) (a' , - ∷ l)) (pr₂ lem) (is-decreasing-tail (underlying-order (sup β)) δ))
     l' = pr₁ IH

   f₁-surj : (l : List (⟨ α ×ₒ sup β ⟩))
           → is-decreasing-pr₂ α (sup β) l
           → ∃ i ꞉ I , Σ l' ꞉ List (⟨ α ×ₒ β i ⟩) , l ＝ f₁ i l'
   f₁-surj [] δ = ∣ i₀ , [] , refl ∣
   f₁-surj (a , s ∷ l) δ = ∥∥-functor h (ι-is-surjective β s)
    where
     h : (Σ i ꞉ I , Σ b ꞉ ⟨ β i ⟩ , ι β b ＝ s)
       → Σ i ꞉ I , Σ l' ꞉ List (⟨ α ×ₒ β i ⟩) , (a , s ∷ l) ＝ f₁ i l'
     h (i , b , refl) = i , (f₁-surj-lemma a i b l δ)

   f-is-order-preserving : (i : I) → is-order-preserving (γ i) ([𝟙+ α ]^ (sup β)) (f i)
   f-is-order-preserving i ([] , δ) (_ , ε) []-lex = []-lex
   f-is-order-preserving i ((a , b ∷ l) , δ) ((a' , b' ∷ l') , ε) (head-lex (inl m)) = head-lex (inl (ι-is-order-preserving β b b' m))
   f-is-order-preserving i ((a , b ∷ l) , δ) ((a' , b' ∷ l') , ε) (head-lex (inr (refl , m))) = head-lex (inr (refl , m))
   f-is-order-preserving i ((_ ∷ l) , δ) ((_ ∷ l') , ε) (tail-lex refl m) =
     tail-lex refl (f-is-order-preserving i (l , is-decreasing-tail (underlying-order (β i)) δ) (l' , is-decreasing-tail (underlying-order (β i)) ε) m)

   f-is-order-reflecting : (i : I) → is-order-reflecting (γ i) ([𝟙+ α ]^ (sup β)) (f i)
   f-is-order-reflecting i ([] , δ) ((a , b ∷ l) , ε) []-lex = []-lex
   f-is-order-reflecting i ((a , b ∷ l) , δ) ((a' , b' ∷ l') , ε) (head-lex (inl m)) = head-lex (inl (ι-is-order-reflecting β b b' m))
   f-is-order-reflecting i ((a , b ∷ l) , δ) ((a' , b' ∷ l') , ε) (head-lex (inr (e , m))) = head-lex (inr (ι-is-lc β e , m))
   f-is-order-reflecting i ((a , b ∷ l) , δ) ((a' , b' ∷ l') , ε) (tail-lex e m) =
    tail-lex (to-×-＝ (ap pr₁ e) (ι-is-lc β (ap pr₂ e)))
    (f-is-order-reflecting i (l , is-decreasing-tail (underlying-order (β i)) δ) (l' , is-decreasing-tail (underlying-order (β i)) ε) m)

   -- We factor out:
   partial-invertibility-lemma : (i : I) -- (a : ⟨ α ⟩) (b : ⟨ β i ⟩)
                               → (l : List (⟨ α ×ₒ β i ⟩))
                               → is-decreasing-pr₂ α (sup β) (f₁ i l) -- (f₁ i (a , b ∷ l))
                               → is-decreasing-pr₂ α (β i) l -- (a , b ∷ l)
   partial-invertibility-lemma i [] ds = []-decr
   partial-invertibility-lemma i ((a , b) ∷ []) ds = sing-decr
   partial-invertibility-lemma i ((a , b) ∷ (a' , b') ∷ l) (many-decr m ds) =
     many-decr (ι-is-order-reflecting β b' b m) (partial-invertibility-lemma i ((a' , b') ∷ l) ds)

   f-is-partially-invertible : (i : I)
                             → (xs : List ⟨ α ×ₒ β i ⟩) → (δ : is-decreasing-pr₂ α (β i) xs)
                             → (ys : List ⟨ α ×ₒ sup β ⟩) → (ε : is-decreasing-pr₂ α (sup β) ys)
                             → (ys , ε) ≺⟨ [𝟙+ α ]^ (sup β) ⟩ f i (xs , δ)
                             → Σ xs' ꞉ ⟨ γ i ⟩ , f i xs' ＝ (ys , ε)
   f-is-partially-invertible i xs δ [] []-decr p = ([] , []-decr) , refl
   f-is-partially-invertible i ((a , b) ∷ xs) δ ((a' , b') ∷ []) ε (head-lex (inl m)) = ((a' , pr₁ ι-sim ∷ []) , sing-decr) , (to-exponential-＝ α (sup β) (ap (λ - → (a' , -) ∷ []) (pr₂ (pr₂ ι-sim))))
     where
       ι-sim = ι-is-initial-segment β b b' m
   f-is-partially-invertible i ((a , b) ∷ xs) δ ((a' , b') ∷ (a₁ , b₁) ∷ ys) (many-decr p ε) (head-lex (inl m)) =
     let IH = f-is-partially-invertible i ((a , b) ∷ xs) δ ((a₁ , b₁) ∷ ys) ε (head-lex (inl (Transitivity (sup β) _ _ _ p m)))
         xs' = pr₁ (pr₁ IH)
         ι-sim = ι-is-initial-segment β b b' m
         b₀ = pr₁ ι-sim
         p₀ = transport⁻¹ (λ - → b₁ ≺⟨ sup β ⟩ -) (pr₂ (pr₂ ι-sim)) p
     in ((a' , b₀ ∷ xs') , partial-invertibility-lemma i ((a' , b₀) ∷ xs') (transport⁻¹ (λ - → is-decreasing-pr₂ α (sup β) ((a' , ι β b₀) ∷ -)) (ap pr₁ (pr₂ IH)) (many-decr p₀ ε)))
       , (to-exponential-＝ α (sup β) (ap₂ (λ x y → (a' , x) ∷ y) (pr₂ (pr₂ ι-sim)) (ap pr₁ (pr₂ IH))))
   f-is-partially-invertible i ((a , b) ∷ xs) δ ((a' , .(ι β b)) ∷ []) ε (head-lex (inr (refl , m))) = ((a' , b ∷ []) , sing-decr) , (to-exponential-＝ α (sup β) refl)
   f-is-partially-invertible i ((a , b) ∷ xs) δ ((a' , .(ι β b)) ∷ (a₁ , b₁) ∷ ys) (many-decr p ε) (head-lex (inr (refl , m))) =
     let IH = f-is-partially-invertible i ((a , b) ∷ xs) δ ((a₁ , b₁) ∷ ys) ε (head-lex (inl p))
         xs' = pr₁ (pr₁ IH)
     in (((a' , b) ∷ xs') , partial-invertibility-lemma i ((a' , b) ∷ xs')
                                                          (transport⁻¹ (λ - → is-decreasing-pr₂ α (sup β) ((a' , ι β b) ∷ -)) (ap pr₁ (pr₂ IH)) (many-decr p ε)))
        , to-exponential-＝ α (sup β) (ap ((a' , ι β b) ∷_) (ap pr₁ (pr₂ IH)))
   f-is-partially-invertible i ((a , b) ∷ xs) δ (.(a , ι β b) ∷ ys) ε (tail-lex refl p) =
     let IH = f-is-partially-invertible i xs (is-decreasing-tail (underlying-order (β i)) δ) ys (is-decreasing-tail (underlying-order (sup β)) ε) p
     in (((a , b) ∷ pr₁ (pr₁ IH)) , partial-invertibility-lemma i ((a , b) ∷ pr₁ (pr₁ IH))
                                                                  (transport⁻¹ (λ - → is-decreasing-pr₂ α (sup β) ((a , ι β b) ∷ -)) (ap pr₁ (pr₂ IH)) ε))
       , to-exponential-＝ α (sup β) (ap ((a , ι β b) ∷_) (ap pr₁ (pr₂ IH)))

   f-is-initial-segment : (i : I) → is-initial-segment (γ i) ([𝟙+ α ]^ (sup β)) (f i)
   f-is-initial-segment i = order-reflecting-and-partial-inverse-is-initial-segment (γ i) ([𝟙+ α ]^ (sup β)) (f i) (f-is-order-reflecting i) g
     where
       g : (xs : ⟨ γ i ⟩) → (ys : ⟨ [𝟙+ α ]^ (sup β) ⟩) → ys ≺⟨ [𝟙+ α ]^ (sup β) ⟩ f i xs → Σ xs' ꞉ ⟨ γ i ⟩ , f i xs' ＝ ys
       g (xs , δ) (ys , ε) = f-is-partially-invertible i xs δ ys ε

  exp-sup-is-upper-bound : (i : I) → γ i ⊴ ([𝟙+ α ]^ (sup β))
  exp-sup-is-upper-bound i = f i , f-is-initial-segment i , f-is-order-preserving i

  exp-sup-simulation : sup (λ i → ([𝟙+ α ]^ (β i))) ⊴ ([𝟙+ α ]^ (sup β))
  exp-sup-simulation = sup-is-lower-bound-of-upper-bounds (λ i → ([𝟙+ α ]^ (β i))) ([𝟙+ α ]^ (sup β)) exp-sup-is-upper-bound

  exp-sup-simulation-surjective : is-surjection (pr₁ exp-sup-simulation)
  exp-sup-simulation-surjective (ys , δ) = {!!}

  sup-spec : sup (λ i → ([𝟙+ α ]^ (β i))) ＝ ([𝟙+ α ]^ (sup β))
  sup-spec = surjective-simulation-gives-equality
               (sup (λ i → ([𝟙+ α ]^ (β i))))
               ([𝟙+ α ]^ (sup β))
               (pr₁ exp-sup-simulation)
               (pr₂ exp-sup-simulation)
               exp-sup-simulation-surjective

  -- Possible strategy
  -- for every i : I, x : [𝟙+ α]^ (β i),
  -- [𝟙+ α]^ (sup β) ↓ (f x) =ₒ [𝟙+ α ]^ (β i) ↓ x
  -- ??


{-
  exp-sup-lemma : (i : I) (a : ⟨ α ⟩) (b : ⟨ β i ⟩) (l : List (⟨ α ×ₒ sup β ⟩))
                → is-decreasing-pr₂ α (sup β) (a , ι β b ∷ l)
                → ⟨ sup γ ⟩
  exp-sup-lemma i a b [] δ = ι γ {i} ([] , []-decr)
  exp-sup-lemma i a b (a' , s ∷ l) (many-decr p δ) = {!!}

-}

\end{code}
