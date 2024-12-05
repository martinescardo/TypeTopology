Tom de Jong, Nicolai Kraus, Fredrik Nordvall Forsberg, Chuangjie Xu,
23 May 2023.

\begin{code}

{-# OPTIONS --safe --without-K --no-exact-split --lossy-unification #-}

open import UF.Univalence
open import UF.PropTrunc
open import UF.Size

module Ordinals.Exponentiation.Equivalence
       (ua : Univalence)
       (pt : propositional-truncations-exist)
       (sr : Set-Replacement pt)
       where

open import UF.Base
-- open import UF.Equiv
-- open import UF.ExcludedMiddle
open import UF.FunExt
-- open import UF.Sets
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.UA-FunExt
-- open import UF.ImageAndSurjection pt

private
 fe : FunExt
 fe = Univalence-gives-FunExt ua

 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

 pe : PropExt
 pe = Univalence-gives-PropExt ua


-- open import Naturals.Order

open import MLTT.Spartan hiding (𝟚; ₀; ₁)
open import MLTT.Plus-Properties
open import MLTT.Sigma
open import MLTT.List

open import Ordinals.Arithmetic fe
open import Ordinals.AdditionProperties ua
open import Ordinals.MultiplicationProperties ua
open import Ordinals.Equivalence
open import Ordinals.Maps
open import Ordinals.Notions
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.Type
open import Ordinals.Underlying
open import Ordinals.OrdinalOfOrdinalsSuprema ua
open import Ordinals.Propositions ua
open import Ordinals.Taboos

open import Ordinals.Exponentiation.DecreasingList ua pt sr
open import Ordinals.Exponentiation.Supremum ua pt sr

open PropositionalTruncation pt
open suprema pt sr
\end{code}

Relating the two definitions of exponentiation.

\begin{code}

is-decreasing-skip-one : {X : 𝓤 ̇  } (R : X → X → 𝓥 ̇  ) → is-transitive R → (x x' : X) → (xs : List X) → is-decreasing R (x' ∷ xs) → R x' x → is-decreasing R (x ∷ xs)
is-decreasing-skip-one R trans x x' [] d r = sing-decr
is-decreasing-skip-one R trans x x' (x'' ∷ xs) (many-decr p' ps) r = many-decr (trans x'' x' x p' r) ps

is-decreasing-less-than-head : {X : 𝓤 ̇  } (R : X → X → 𝓥 ̇  ) → is-transitive R → (x : X) → (xs : List X) → is-decreasing R (x ∷ xs) → (y : X) → member y xs → R y x
is-decreasing-less-than-head R trans x (x' ∷ xs) (many-decr p ps) .x' in-head = p
is-decreasing-less-than-head {X = X} R trans x (x' ∷ xs) (many-decr p ps) y (in-tail m) = is-decreasing-less-than-head R trans x xs (is-decreasing-skip-one R trans x x' xs ps p) y m

decreasing-pr₂-to-more-precise-tail :  (α : Ordinal 𝓤) (β : Ordinal 𝓥) → (a : ⟨ α ⟩)(b : ⟨ β ⟩)(xs : List ⟨ α ×ₒ β ⟩) → is-decreasing-pr₂ α β ((a , b) ∷ xs) → List ⟨ α ×ₒ (β ↓ b) ⟩
decreasing-pr₂-to-more-precise-tail α β a b [] p = []
decreasing-pr₂-to-more-precise-tail α β a b ((a' , b') ∷ xs) ps
  = (a' , (b' , is-decreasing-heads _ ps)) ∷ decreasing-pr₂-to-more-precise-tail α β a b xs (is-decreasing-skip-one (underlying-order β) (Transitivity β) b b' (map pr₂ xs) (is-decreasing-tail _ ps) (is-decreasing-heads _ ps))

decreasing-pr₂-to-more-precise-tail-decreasing : (α : Ordinal 𝓤) (β : Ordinal 𝓥) → (a : ⟨ α ⟩) (b : ⟨ β ⟩) (xs : List ⟨ α ×ₒ β ⟩) → (ps : is-decreasing-pr₂ α β ((a , b) ∷ xs))
                                               → is-decreasing-pr₂ α (β ↓ b) (decreasing-pr₂-to-more-precise-tail α β a b xs ps)
decreasing-pr₂-to-more-precise-tail-decreasing α β a b [] ps = []-decr
decreasing-pr₂-to-more-precise-tail-decreasing α β a b (a' , b' ∷ []) (many-decr p sing-decr) = sing-decr
decreasing-pr₂-to-more-precise-tail-decreasing α β a b (a' , b' ∷ a'' , b'' ∷ xs) (many-decr p (many-decr p' ps))
  = many-decr p' (decreasing-pr₂-to-more-precise-tail-decreasing α β a b ((a'' , b'') ∷ xs) (many-decr (Transitivity β b'' b' b p' p) ps))

more-precise-tail-pair : (α : Ordinal 𝓤) (β : Ordinal 𝓥)
                         (a : ⟨ α ⟩) (b : ⟨ β ⟩) (xs : List ⟨ α ×ₒ β ⟩)
                         (ps : is-decreasing-pr₂ α β ((a , b) ∷ xs))
                       → ⟨ [𝟙+ α ]^ (β ↓ b) ⟩
more-precise-tail-pair α β a b xs ps =
 decreasing-pr₂-to-more-precise-tail α β a b xs ps ,
 decreasing-pr₂-to-more-precise-tail-decreasing α β a b xs ps

more-precise-tail-order-preserving : (α : Ordinal 𝓤) (β : Ordinal 𝓥)
                                     (a₀ : ⟨ α ⟩) (b₀ : ⟨ β ⟩)
                                     (xs : List ⟨ α ×ₒ β ⟩)
                                     (δ : is-decreasing-pr₂ α β ((a₀ , b₀) ∷ xs))
                                     (xs' : List ⟨ α ×ₒ β ⟩)
                                     (δ' : is-decreasing-pr₂ α β ((a₀ , b₀) ∷ xs'))
                                   → xs ≺⟨List (α ×ₒ β) ⟩ xs'
                                   → more-precise-tail-pair α β a₀ b₀ xs δ ≺⟨ ([𝟙+ α ]^ (β ↓ b₀)) ⟩ more-precise-tail-pair α β a₀ b₀ xs' δ'
more-precise-tail-order-preserving α β a₀ b₀ [] ps (x' ∷ xs') ps' q = []-lex
more-precise-tail-order-preserving α β a₀ b₀ ((a , b) ∷ xs) (many-decr p ps) ((a' , b') ∷ xs') (many-decr p' ps') (head-lex (inl q)) = head-lex (inl q)
more-precise-tail-order-preserving α β a₀ b₀ ((a , b) ∷ xs) (many-decr p ps) ((a' , b) ∷ xs') (many-decr p' ps') (head-lex (inr (refl , q))) =
 head-lex (inr (to-subtype-＝ (λ x → Prop-valuedness β x b₀) refl , q))
more-precise-tail-order-preserving α β a₀ b₀ ((a , b) ∷ xs) (many-decr p ps) ((a , b) ∷ xs') (many-decr p' ps') (tail-lex refl q) =
 tail-lex (ap (a ,_) (to-subtype-＝ ((λ x → Prop-valuedness β x b₀)) refl)) (more-precise-tail-order-preserving α β a₀ b₀ xs _ xs' _ q)

\end{code}

Conversely, we can forget more precise bound information to embed back into the original type.

\begin{code}

project₂ : (α : Ordinal 𝓤) (β : Ordinal 𝓥) (b : ⟨ β ⟩) → ⟨ α ×ₒ (β ↓ b) ⟩ → ⟨ α ×ₒ β ⟩
project₂ α β b (a , x) = (a , segment-inclusion β b x)

project₂-preserves-decreasing : (α : Ordinal 𝓤) (β : Ordinal 𝓥) (b : ⟨ β ⟩)
                              → (xs : List ⟨ α ×ₒ (β ↓ b) ⟩) → is-decreasing-pr₂ α (β ↓ b) xs → is-decreasing-pr₂ α β (map (project₂ α β b) xs)
project₂-preserves-decreasing α β b [] _ = []-decr
project₂-preserves-decreasing α β b ((a , x) ∷ []) _ = sing-decr
project₂-preserves-decreasing α β b ((a , x) ∷ (a' , x') ∷ xs) (many-decr p δ) = many-decr p (project₂-preserves-decreasing α β b ((a' , x') ∷ xs) δ)

embed : (α : Ordinal 𝓤) (β : Ordinal 𝓥) (b : ⟨ β ⟩) → ⟨ [𝟙+ α ]^ (β ↓ b) ⟩ → ⟨ [𝟙+ α ]^ β ⟩
embed α β b (xs , δ) = map (project₂ α β b) xs , project₂-preserves-decreasing α β b xs δ

embed-order-preserving : (α : Ordinal 𝓤) (β : Ordinal 𝓥) (b : ⟨ β ⟩) → is-order-preserving ([𝟙+ α ]^ (β ↓ b)) ([𝟙+ α ]^ β) (embed α β b)
embed-order-preserving α β b ([] , pr₃) ((y ∷ ys) , ε) []-lex = []-lex
embed-order-preserving α β b ((x ∷ xs) , δ) ((y ∷ ys) , ε) (head-lex (inl p)) = head-lex (inl p)
embed-order-preserving α β b ((x ∷ xs) , δ) ((y ∷ ys) , ε) (head-lex (inr (refl , p))) = head-lex (inr (refl , p))
embed-order-preserving α β b ((x ∷ xs) , δ) ((y ∷ ys) , ε) (tail-lex refl p) = tail-lex refl (embed-order-preserving α β b (xs , is-decreasing-tail _ δ) (ys , is-decreasing-tail _ ε) p)

embed-below-b : (α : Ordinal 𝓤) (β : Ordinal 𝓥) (b : ⟨ β ⟩) → (xs : ⟨ [𝟙+ α ]^ (β ↓ b) ⟩)
              → (y : ⟨ β ⟩) → member y (map pr₂ (underlying-list α β (embed α β b xs))) → y ≺⟨ β ⟩ b
embed-below-b α β b (((a , (b' , p)) ∷ xs) , δ) y in-head = p
embed-below-b α β b ((x ∷ xs) , δ) y (in-tail m) = embed-below-b α β b (xs , is-decreasing-tail _ δ) y m

embed-below-lists-starting-b : (α : Ordinal 𝓤) (β : Ordinal 𝓥) (a : ⟨ α ⟩) (b : ⟨ β ⟩) → (xs : ⟨ [𝟙+ α ]^ (β ↓ b) ⟩)
                             → (l : List ⟨ α ×ₒ β ⟩) → (δ : is-decreasing-pr₂  α β ((a , b) ∷ l))
                             → embed α β b xs ≺⟨ [𝟙+ α ]^ β ⟩ (((a , b) ∷ l), δ)
embed-below-lists-starting-b α β a b ([] , ε) l δ = []-lex
embed-below-lists-starting-b α β a b (((a' , (b' , p')) ∷ xs) , ε) l δ = head-lex (inl p')

embed-decreasing : (α : Ordinal 𝓤) (β : Ordinal 𝓥) (b : ⟨ β ⟩) → (l : ⟨ [𝟙+ α ]^ (β ↓ b) ⟩) → is-decreasing (underlying-order β) (b ∷ map pr₂ (pr₁ (embed α β b l)))
embed-decreasing α β b ([] , δ) = sing-decr
embed-decreasing α β b (((a' , (b' , p)) ∷ l) , δ) = many-decr p (project₂-preserves-decreasing α β b ((a' , (b' , p)) ∷ l) δ)

embed-more-precise-is-id : (α : Ordinal 𝓤) (β : Ordinal 𝓥)
                           (a : ⟨ α ⟩) (b : ⟨ β ⟩) (l : List ⟨ α ×ₒ β ⟩)
                           (δ : is-decreasing-pr₂ α β ((a , b) ∷ l))
                         → pr₁ (embed α β b (more-precise-tail-pair α β a b l δ)) ＝ l
embed-more-precise-is-id α β a b [] δ = refl
embed-more-precise-is-id α β a b ((a' , b') ∷ l) δ =
 ap ((a' , b') ∷_)
    (embed-more-precise-is-id α β a b l (is-decreasing-skip-one (underlying-order β)
                                                                (Transitivity β)
                                                                b
                                                                b'
                                                                (map pr₂ l)
                                                                (is-decreasing-tail (underlying-order β) δ)
                                                                (is-decreasing-heads (underlying-order β) δ)))


more-precise-embed-is-id : (α : Ordinal 𝓤) (β : Ordinal 𝓥)
                           (a : ⟨ α ⟩) (b : ⟨ β ⟩)
                           (l : List ⟨ α ×ₒ (β ↓ b) ⟩) (ε : is-decreasing-pr₂ α (β ↓ b) l)
                           (δ : is-decreasing-pr₂ α β (a , b ∷ pr₁ (embed α β b (l , ε))))
                         → pr₁ (more-precise-tail-pair α β a b (pr₁ (embed α β b (l , ε))) δ)  ＝ l
more-precise-embed-is-id α β a b [] []-decr δ = refl
more-precise-embed-is-id α β a b ((a' , b' , p') ∷ l) ε δ =
 ap₂ _∷_ (ap (a' ,_) (to-subtype-＝ (λ x → Prop-valuedness β x b) refl)) (more-precise-embed-is-id α β a b l (is-decreasing-tail (underlying-order (β ↓ b)) ε) _)
\end{code}

\begin{code}

open import UF.Equiv

abstract
 [𝟙+]^-↓-lemma : (α : Ordinal 𝓤) (β : Ordinal 𝓤)
                 (a : ⟨ α ⟩) (b : ⟨ β ⟩) (l : List ⟨ α ×ₒ β ⟩)
                 (δ : is-decreasing-pr₂ α β ((a , b) ∷ l))
               → (([𝟙+ α ]^ β) ↓ (((a , b) ∷ l) , δ)) ≃ₒ
                 ((([𝟙+ α ]^ (β ↓ b)) ×ₒ (𝟙ₒ +ₒ (α ↓ a))) +ₒ (([𝟙+ α ]^ (β ↓ b)) ↓ more-precise-tail-pair α β a b l δ))
 [𝟙+]^-↓-lemma α β a b l δ = f , f-is-order-preserving , qinvs-are-equivs f (g , gf-is-id , fg-is-id) , g-is-order-preserving
  where
   f : ⟨ ([𝟙+ α ]^ β) ↓ (((a , b) ∷ l) , δ) ⟩ →
                  ⟨ (([𝟙+ α ]^ (β ↓ b)) ×ₒ (𝟙ₒ +ₒ (α ↓ a))) +ₒ (([𝟙+ α ]^ (β ↓ b)) ↓ more-precise-tail-pair α β a b l δ) ⟩
   f (([] , _) , p) = inl (([] , []-decr) , inl ⋆)
   f ((((a' , b') ∷ l') , ε) , head-lex (inl p)) =
    let
     ε' = is-decreasing-skip-one (underlying-order β) (Transitivity β) b b' (map pr₂ l') ε p
     l'' = more-precise-tail-pair α β a b l' ε'
    in
     inl ((((a' , (b' , p)) ∷ pr₁ l'') , b'l''-decreasing l' a' b' p ε) , (inl ⋆))
    where
     b'l''-decreasing : ∀ l' a' b' p ε → is-decreasing-pr₂ α (β ↓ b) (a' , (b' , p) ∷ pr₁ (more-precise-tail-pair α β a b l' (is-decreasing-skip-one (pr₁ (pr₂ β)) (Transitivity β) b b' (map (λ r → pr₂ r) l') ε p)))
     b'l''-decreasing [] a' b' p ε = sing-decr
     b'l''-decreasing (a'' , b'' ∷ l'') a' b' p (many-decr p'' ε'') = many-decr p'' (b'l''-decreasing l'' a'' b'' (Transitivity β _ _ _ p'' p) ε'')
   f ((((a' , b) ∷ l') , ε) , head-lex (inr (refl , p))) = inl (more-precise-tail-pair α β a b l' ε , inr (a' , p))
   f ((((a , b) ∷ l') , ε) , tail-lex refl p) = inr (more-precise-tail-pair α β a b l' ε , more-precise-tail-order-preserving α β a b l' ε l δ p)

   f-is-order-preserving : is-order-preserving (([𝟙+ α ]^ β) ↓ ((a , b ∷ l) , δ))
                                               ((([𝟙+ α ]^ (β ↓ b)) ×ₒ (𝟙ₒ +ₒ (α ↓ a))) +ₒ (([𝟙+ α ]^ (β ↓ b)) ↓ more-precise-tail-pair α β a b l δ))
                                               f
   f-is-order-preserving (([] , pr₄) , i) (((x ∷ pr₅) , pr₆) , head-lex (inl _)) u = inr (refl , []-lex)
   f-is-order-preserving (([] , pr₄) , i) (((x ∷ pr₅) , pr₆) , head-lex (inr (refl , p))) u = inl ⋆
   f-is-order-preserving (([] , pr₄) , i) (((x ∷ pr₅) , pr₆) , tail-lex refl j) u = ⋆
   f-is-order-preserving (((x ∷ pr₃) , pr₄) , head-lex (inl y)) (((x₁ ∷ pr₅) , pr₆) , head-lex (inl w)) (head-lex (inl v)) = inr (refl , head-lex (inl v))
   f-is-order-preserving (((x ∷ pr₃) , pr₄) , head-lex (inl y)) (((x₁ ∷ pr₅) , pr₆) , head-lex (inl w)) (head-lex (inr (refl , v))) = inr (refl , head-lex (inr (to-subtype-＝ (λ - → Prop-valuedness β - b) refl , v)))
   f-is-order-preserving (((x ∷ pr₃) , pr₄) , head-lex (inl y)) (((x₁ ∷ pr₅) , pr₆) , head-lex (inl w)) (tail-lex refl u) = inr (refl , tail-lex (ap₂ _,_ refl (to-subtype-＝ ((λ - → Prop-valuedness β - b)) refl)) (more-precise-tail-order-preserving α β a b pr₃ _ pr₅ _ u))
   f-is-order-preserving (((x ∷ pr₃) , pr₄) , head-lex (inl y)) (((x₁ ∷ pr₅) , pr₆) , head-lex (inr (refl , q))) u = inl ⋆
   f-is-order-preserving (((x ∷ pr₃) , pr₄) , head-lex (inr (refl , p))) (((x₁ ∷ pr₅) , pr₆) , head-lex (inl w)) (head-lex (inl u)) = 𝟘-elim (irrefl β (pr₂ x) (Transitivity β _ _ _ u w))
   f-is-order-preserving (((x ∷ pr₃) , pr₄) , head-lex (inr (refl , p))) (((x₁ ∷ pr₅) , pr₆) , head-lex (inl w)) (head-lex (inr (refl , v))) = 𝟘-elim (irrefl β _ w)
   f-is-order-preserving (((x ∷ pr₃) , pr₄) , head-lex (inr (refl , p))) (((x₁ ∷ pr₅) , pr₆) , head-lex (inl w)) (tail-lex refl u) = 𝟘-elim (irrefl β _ w)
   f-is-order-preserving (((pr₇ , .(pr₂ x₁) ∷ pr₃) , pr₄) , head-lex (inr (refl , p))) (((x₁ ∷ pr₅) , pr₆) , head-lex (inr (refl , q))) (head-lex (inl u)) = 𝟘-elim (irrefl β _ u)
   f-is-order-preserving (((pr₇ , .(pr₂ x₁) ∷ pr₃) , pr₄) , head-lex (inr (refl , p))) (((x₁ ∷ pr₅) , pr₆) , head-lex (inr (refl , q))) (head-lex (inr (e , v))) = inl v
   f-is-order-preserving (((pr₇ , .(pr₂ x₁) ∷ pr₃) , pr₄) , head-lex (inr (refl , p))) (((x₁ ∷ pr₅) , pr₆) , head-lex (inr (refl , q))) (tail-lex e u) = inr ((ap inr (to-subtype-＝ (λ - → Prop-valuedness α - a) (ap pr₁ e))) , (more-precise-tail-order-preserving α β a b pr₃ _ pr₅ _ u))
   f-is-order-preserving (((x ∷ pr₃) , pr₄) , head-lex (inl y)) (((x₁ ∷ pr₅) , pr₆) , tail-lex refl j) u = ⋆
   f-is-order-preserving (((x ∷ pr₃) , pr₄) , head-lex (inr (refl , p))) (((x₁ ∷ pr₅) , pr₆) , tail-lex refl j) u = ⋆
   f-is-order-preserving (((.(a , b) ∷ pr₃) , pr₄) , tail-lex refl i) (((x₁ ∷ pr₅) , pr₆) , head-lex (inl v)) (head-lex (inl u)) = 𝟘-elim (irrefl β _ (Transitivity β _ _ _ u v))
   f-is-order-preserving (((.(a , b) ∷ pr₃) , pr₄) , tail-lex refl i) (((x₁ ∷ pr₅) , pr₆) , head-lex (inl v)) (head-lex (inr (refl , q))) = 𝟘-elim (irrefl β _ v)
   f-is-order-preserving (((.(a , b) ∷ pr₃) , pr₄) , tail-lex refl i) (((x₁ ∷ pr₅) , pr₆) , head-lex (inl v)) (tail-lex refl u) = 𝟘-elim (irrefl β _ v)
   f-is-order-preserving (((.(a , b) ∷ pr₃) , pr₄) , tail-lex refl i) (((x₁ ∷ pr₅) , pr₆) , head-lex (inr (refl , q))) (head-lex (inl u)) = 𝟘-elim (irrefl β _ u)
   f-is-order-preserving (((.(a , b) ∷ pr₃) , pr₄) , tail-lex refl i) (((x₁ ∷ pr₅) , pr₆) , head-lex (inr (refl , q))) (head-lex (inr (e , r))) = 𝟘-elim (irrefl α _ (Transitivity α _ _ _ q r))
   f-is-order-preserving (((.(a , b) ∷ pr₃) , pr₄) , tail-lex refl i) (((x₁ ∷ pr₅) , pr₆) , head-lex (inr (refl , q))) (tail-lex e u) = 𝟘-elim (irrefl α a (transport⁻¹ (λ - → - ≺⟨ α ⟩ a) (ap pr₁ e) q))
   f-is-order-preserving (((.(a , b) ∷ pr₃) , pr₄) , tail-lex refl i) (((.(a , b) ∷ pr₅) , pr₆) , tail-lex refl j) (head-lex (inl u)) = 𝟘-elim (irrefl β _ u)
   f-is-order-preserving (((.(a , b) ∷ pr₃) , pr₄) , tail-lex refl i) (((.(a , b) ∷ pr₅) , pr₆) , tail-lex refl j) (head-lex (inr (e , q))) = 𝟘-elim (irrefl α _ q)
   f-is-order-preserving (((.(a , b) ∷ pr₃) , pr₄) , tail-lex refl i) (((.(a , b) ∷ pr₅) , pr₆) , tail-lex refl j) (tail-lex _ u) = more-precise-tail-order-preserving α β a b _ _ _ _ u

   g : ⟨ (([𝟙+ α ]^ (β ↓ b)) ×ₒ (𝟙ₒ +ₒ (α ↓ a))) +ₒ (([𝟙+ α ]^ (β ↓ b)) ↓ more-precise-tail-pair α β a b l δ) ⟩
             → ⟨ ([𝟙+ α ]^ β) ↓ (((a , b) ∷ l) , δ) ⟩
   g (inl (l' , inl ⋆)) = embed α β b l' , embed-below-lists-starting-b α β a b l' l δ
   g (inl (l' , inr (a' , q))) = (((a' , b) ∷ pr₁ (embed α β b l')) , embed-decreasing α β b l') , head-lex (inr (refl , q))
   g (inr (l' , l'-below-l)) = (((a , b) ∷ pr₁ (embed α β b l')) , embed-decreasing α β b l') , tail-lex refl embedl'-below-l
    where
     embedl'-below-l : (pr₁ (embed α β b l')) ≺⟨List (α ×ₒ β) ⟩ l
     embedl'-below-l = transport (λ - → (pr₁ (embed α β b l')) ≺⟨List (α ×ₒ β) ⟩ - )
                                 (embed-more-precise-is-id α β a b l δ)
                                 (embed-order-preserving α β b _ (more-precise-tail-pair α β a b l δ) l'-below-l)

   g-is-order-preserving : is-order-preserving ((([𝟙+ α ]^ (β ↓ b)) ×ₒ (𝟙ₒ +ₒ (α ↓ a))) +ₒ (([𝟙+ α ]^ (β ↓ b)) ↓ more-precise-tail-pair α β a b l δ))
                                               (([𝟙+ α ]^ β) ↓ ((a , b ∷ l) , δ))
                                               g
   g-is-order-preserving (inl (l , inl ⋆)) (inl (l' , inl ⋆)) (inr (refl , u)) = embed-order-preserving α β b l l' u
   g-is-order-preserving (inl (l , inl ⋆)) (inl (l' , inr (a' , j))) u = embed-below-lists-starting-b α β a' b l (pr₁ (embed α β b l')) (embed-decreasing α β b l')
   g-is-order-preserving (inl (l , inr (a' , i))) (inl (l' , inl ⋆)) (inr (e , u)) = 𝟘-elim (+disjoint (e ⁻¹))
   g-is-order-preserving (inl (l , inr (a' , i))) (inl (l' , inr (a'' , j))) (inl u) = head-lex (inr (refl , u))
   g-is-order-preserving (inl (l , inr (a' , i))) (inl (l' , inr (a'' , j))) (inr (refl , v)) = tail-lex refl (embed-order-preserving α β b l l' v)
   g-is-order-preserving (inl (l , inl ⋆)) (inr (l' , v)) _ = embed-below-lists-starting-b α β a b l (pr₁ (embed α β b l')) (embed-decreasing α β b l')
   g-is-order-preserving (inl (l , inr (a' , i))) (inr (l' , v)) _ = head-lex (inr (refl , i))
   g-is-order-preserving (inr (l , v)) (inr (l' , v')) u = tail-lex refl (embed-order-preserving α β b l l' u)

   fg-is-id : ∀ x → f (g x) ＝ x
   fg-is-id (inl (([] , []-decr) , inl ⋆)) = refl
   fg-is-id (inl ((((a' , b') ∷ l') , ε) , inl ⋆)) =
    ap (λ z → (inl (z , inl ⋆)))
       (to-exponential-＝ α (β ↓ b) (ap ((a' , b') ∷_)
                                        (more-precise-embed-is-id α β a b l' (is-decreasing-tail (underlying-order (β ↓ b)) ε) _)))
   fg-is-id (inl ((l' , ε') , inr (a' , q))) = ap (λ z → inl (z , inr (a' , q))) (to-exponential-＝ α (β ↓ b) (more-precise-embed-is-id α β a b l' ε' _))
   fg-is-id (inr ((l' , ε') , l'-below-l)) = ap inr (to-subtype-＝ (λ x → Prop-valuedness ([𝟙+ α ]^ (β ↓ b)) x _) (to-exponential-＝ α (β ↓ b) (more-precise-embed-is-id α β a b l' ε' _)))

   gf-is-id : ∀ x → g (f x) ＝ x
   gf-is-id (([] , []-decr) , []-lex) = refl
   gf-is-id ((((a' , b') ∷ l') , ε) , head-lex (inl p)) = to-subtype-＝ (λ x → Prop-valuedness _ x _) (to-exponential-＝ α β (ap ((a' , b') ∷_) (embed-more-precise-is-id α β a b l' _)))
   gf-is-id ((((a' , b) ∷ l') , ε) , head-lex (inr (refl , p))) = to-subtype-＝ (λ x → Prop-valuedness _ x _) (to-exponential-＝ α β ((ap ((a' , b) ∷_) (embed-more-precise-is-id α β a b l' _))))
   gf-is-id ((((a , b) ∷ l') , ε) , tail-lex refl p) = to-subtype-＝ (λ x → Prop-valuedness _ x _) (to-exponential-＝ α β ((ap ((a , b) ∷_) (embed-more-precise-is-id α β a b l' _))))

abstract
 [𝟙+]^-↓-lemma' : (α : Ordinal 𝓤) (β : Ordinal 𝓤)
                 (a : ⟨ α ⟩) (b : ⟨ β ⟩) (l : List ⟨ α ×ₒ (β ↓ b) ⟩)
                 (δ : is-decreasing-pr₂ α (β ↓ b) l)
               → (([𝟙+ α ]^ β) ↓ (((a , b) ∷ pr₁ (embed α β b (l , δ))) , embed-decreasing α β b (l , δ))) ≃ₒ
                 ((([𝟙+ α ]^ (β ↓ b)) ×ₒ (𝟙ₒ +ₒ (α ↓ a))) +ₒ (([𝟙+ α ]^ (β ↓ b)) ↓ (l , δ)))
 [𝟙+]^-↓-lemma' α β a b l δ = III
  where
   l' : List ⟨ α ×ₒ β ⟩
   l' = (a , b) ∷ pr₁ (embed α β b (l , δ))
   δ' : is-decreasing-pr₂ α β l'
   δ' = embed-decreasing α β b (l , δ)
   l⁺ : ⟨ [𝟙+ α ]^ (β ↓ b) ⟩
   l⁺ = more-precise-tail-pair α β a b (pr₁ (embed α β b (l , δ))) δ'
   I : (l , δ) ＝ l⁺
   I = (to-exponential-＝ α (β ↓ b) (more-precise-embed-is-id α β a b l δ δ')) ⁻¹
   II : (([𝟙+ α ]^ β) ↓ (l' , δ')) ≃ₒ
        ((([𝟙+ α ]^ (β ↓ b)) ×ₒ (𝟙ₒ +ₒ (α ↓ a))) +ₒ (([𝟙+ α ]^ (β ↓ b)) ↓ l⁺))
   II = [𝟙+]^-↓-lemma α β a b (pr₁ (embed α β b (l , δ))) δ'
   III : (([𝟙+ α ]^ β) ↓ (l' , δ')) ≃ₒ
         ((([𝟙+ α ]^ (β ↓ b)) ×ₒ (𝟙ₒ +ₒ (α ↓ a))) +ₒ (([𝟙+ α ]^ (β ↓ b)) ↓ (l , δ)))
   III = transport⁻¹ (λ - → (([𝟙+ α ]^ β) ↓ (l' , δ')) ≃ₒ
         ((([𝟙+ α ]^ (β ↓ b)) ×ₒ (𝟙ₒ +ₒ (α ↓ a))) +ₒ (([𝟙+ α ]^ (β ↓ b)) ↓ -))) I II


abstract
 ↓-eq-lemma : (α β : Ordinal 𝓤) (a : ⟨ α ⟩)
              (e : α ＝ β)
            → α ↓ a ＝ β ↓ Idtofun (ap ⟨_⟩ e) a
 ↓-eq-lemma α β a refl = refl

expₗ-⊥ : (α : Ordinal 𝓤) (β : Ordinal 𝓥) → ⟨ [𝟙+ α ]^ β ⟩
expₗ-⊥ α β = [] , []-decr

expₗ-↓-⊥ : (α : Ordinal 𝓤) (β : Ordinal 𝓥)
         → [𝟙+ α ]^ β ↓ expₗ-⊥ α β ＝ 𝟘ₒ
expₗ-↓-⊥ α β = ([𝟙+α]^β-has-least' α β []-decr) ⁻¹

equivalence-of-exponentiation-constructions : (α β : Ordinal 𝓤)
                                            → (𝟙ₒ +ₒ α) ^ₒ β ＝ [𝟙+ α ]^ β
equivalence-of-exponentiation-constructions {𝓤} α =
 transfinite-induction-on-OO (λ β → α⁺ ^ₒ β ＝ [𝟙+ α ]^ β) I
  where
   α⁺ = 𝟙ₒ +ₒ α

   I : (β : Ordinal 𝓤)
     → ((b : ⟨ β ⟩) → α⁺ ^ₒ (β ↓ b) ＝ ([𝟙+ α ]^ (β ↓ b)))
     → α⁺ ^ₒ β ＝ ([𝟙+ α ]^ β)
   I β IH = ⊴-antisym (α⁺ ^ₒ β) ([𝟙+ α ]^ β)
             (to-⊴ (α⁺ ^ₒ β) ([𝟙+ α ]^ β) III)
             (to-⊴ ([𝟙+ α ]^ β) (α⁺ ^ₒ β) II)
    where
     II : (y : ⟨ [𝟙+ α ]^ β ⟩) → [𝟙+ α ]^ β ↓ y ⊲ α⁺ ^ₒ β
     II ([] , δ)            = ^ₒ-⊥ α⁺ β ,
      ([𝟙+ α ]^ β ↓ ([] , δ) ＝⟨ ([𝟙+α]^β-has-least' α β δ) ⁻¹ ⟩
       𝟘ₒ                    ＝⟨ (^ₒ-↓-⊥ α⁺ β) ⁻¹ ⟩
       α⁺ ^ₒ β ↓ ^ₒ-⊥ α⁺ β   ∎)
     II (((a , b) ∷ l) , δ) = e' ,
      ([𝟙+ α ]^ β ↓ ((a , b ∷ l) , δ)                                   ＝⟨ eqtoidₒ (ua 𝓤) fe' ([𝟙+ α ]^ β ↓ ((a , b ∷ l) , δ)) _ ([𝟙+]^-↓-lemma α β a b l δ) ⟩
       [𝟙+ α ]^ (β ↓ b) ×ₒ (𝟙ₒ +ₒ (α ↓ a)) +ₒ (([𝟙+ α ]^ (β ↓ b)) ↓ l') ＝⟨ ap (λ - → - ×ₒ (𝟙ₒ +ₒ (α ↓ a)) +ₒ (([𝟙+ α ]^ (β ↓ b)) ↓ l')) ((IH b) ⁻¹) ⟩
       α⁺ ^ₒ (β ↓ b) ×ₒ (𝟙ₒ +ₒ (α ↓ a)) +ₒ (([𝟙+ α ]^ (β ↓ b)) ↓ l')    ＝⟨ ap (α⁺ ^ₒ (β ↓ b) ×ₒ (𝟙ₒ +ₒ (α ↓ a)) +ₒ_) (↓-eq-lemma ([𝟙+ α ]^ (β ↓ b)) (α⁺ ^ₒ (β ↓ b)) l' ((IH b) ⁻¹)) ⟩
       α⁺ ^ₒ (β ↓ b) ×ₒ (𝟙ₒ +ₒ (α ↓ a)) +ₒ (α⁺ ^ₒ (β ↓ b) ↓ e)          ＝⟨ ap (λ - → α⁺ ^ₒ (β ↓ b) ×ₒ - +ₒ (α⁺ ^ₒ (β ↓ b) ↓ e)) (+ₒ-↓-right a) ⟩
       α⁺ ^ₒ (β ↓ b) ×ₒ (α⁺ ↓ (inr a)) +ₒ (α⁺ ^ₒ (β ↓ b) ↓ e)           ＝⟨ ^ₒ-↓-×ₒ-to-^ₒ α⁺ β ⁻¹ ⟩
       α⁺ ^ₒ β ↓ e'                                                     ∎)
        where
         l' = more-precise-tail-pair α β a b l δ
         e = Idtofun (ap ⟨_⟩ (IH b ⁻¹)) l'
         e' = ×ₒ-to-^ₒ α⁺ β (e , inr a)

     III : (y : ⟨ α⁺ ^ₒ β ⟩) → α⁺ ^ₒ β ↓ y ⊲ [𝟙+ α ]^ β
     III y = ∥∥-rec
              (⊲-is-prop-valued (α⁺ ^ₒ β ↓ y) ([𝟙+ α ]^ β))
              IV
              (^ₒ-↓ α⁺ β)
      where
       IV : (α⁺ ^ₒ β ↓ y ＝ 𝟘ₒ)
           + (Σ b ꞉ ⟨ β ⟩ , Σ e ꞉ ⟨ α⁺ ^ₒ (β ↓ b) ⟩ , Σ x ꞉ ⟨ α⁺ ⟩ ,
               α⁺ ^ₒ β ↓ y ＝ α⁺ ^ₒ (β ↓ b) ×ₒ (α⁺ ↓ x) +ₒ (α⁺ ^ₒ (β ↓ b) ↓ e))
           → α⁺ ^ₒ β ↓ y ⊲ ([𝟙+ α ]^ β)
       IV (inl p)                   = expₗ-⊥ α β ,
        (α⁺ ^ₒ β ↓ y               ＝⟨ p ⟩
         𝟘ₒ                        ＝⟨ (expₗ-↓-⊥ α β) ⁻¹ ⟩
         [𝟙+ α ]^ β ↓ expₗ-⊥ α β ∎)
       IV (inr (b , e , inl ⋆ , p)) = l₂ ,
        (α⁺ ^ₒ β ↓ y                                          ＝⟨ p ⟩
         α⁺ ^ₒ (β ↓ b) ×ₒ (α⁺ ↓ inl ⋆) +ₒ (α⁺ ^ₒ (β ↓ b) ↓ e) ＝⟨ ap (λ - → α⁺ ^ₒ (β ↓ b) ×ₒ - +ₒ (α⁺ ^ₒ (β ↓ b) ↓ e)) ((+ₒ-↓-left ⋆) ⁻¹) ⟩
         α⁺ ^ₒ (β ↓ b) ×ₒ (𝟙ₒ ↓ ⋆) +ₒ (α⁺ ^ₒ (β ↓ b) ↓ e)     ＝⟨ ap (λ - → α⁺ ^ₒ (β ↓ b) ×ₒ - +ₒ (α⁺ ^ₒ (β ↓ b) ↓ e)) 𝟙ₒ-↓ ⟩
         α⁺ ^ₒ (β ↓ b) ×ₒ 𝟘ₒ +ₒ (α⁺ ^ₒ (β ↓ b) ↓ e)           ＝⟨ ap (_+ₒ (α⁺ ^ₒ (β ↓ b) ↓ e)) (×ₒ-𝟘ₒ-right (α⁺ ^ₒ (β ↓ b))) ⟩
         𝟘ₒ +ₒ (α⁺ ^ₒ (β ↓ b) ↓ e)                            ＝⟨ 𝟘ₒ-left-neutral (α⁺ ^ₒ (β ↓ b) ↓ e) ⟩
         α⁺ ^ₒ (β ↓ b) ↓ e                                    ＝⟨ ↓-eq-lemma (α⁺ ^ₒ (β ↓ b)) ([𝟙+ α ]^ (β ↓ b)) e (IH b) ⟩
         ([𝟙+ α ]^ (β ↓ b)) ↓ l₁                              ＝⟨ simulations-preserve-↓ ([𝟙+ α ]^ (β ↓ b)) ([𝟙+ α ]^ β) σ l₁ ⟩
         [𝟙+ α ]^ β ↓ l₂                                      ∎)
        where
         σ : ([𝟙+ α ]^ (β ↓ b)) ⊴ ([𝟙+ α ]^ β)
         σ = ≼-gives-⊴ ([𝟙+ α ]^ (β ↓ b)) ([𝟙+ α ]^ β)
              (monotone-in-exponent α (β ↓ b) β
                (⊲-gives-≼ (β ↓ b) β (b , refl)))
         l₁ = Idtofun (ap ⟨_⟩ (IH b)) e
         l₂ = [ [𝟙+ α ]^ (β ↓ b) , [𝟙+ α ]^ β ]⟨ σ ⟩ l₁
       IV (inr (b , e , inr a , p)) = l₂ ,
        (α⁺ ^ₒ β ↓ y                                                    ＝⟨ p ⟩
         α⁺ ^ₒ (β ↓ b) ×ₒ (α⁺ ↓ inr a) +ₒ (α⁺ ^ₒ (β ↓ b) ↓ e)           ＝⟨ ap (λ - → α⁺ ^ₒ (β ↓ b) ×ₒ - +ₒ (α⁺ ^ₒ (β ↓ b) ↓ e)) ((+ₒ-↓-right a) ⁻¹) ⟩
         α⁺ ^ₒ (β ↓ b) ×ₒ (𝟙ₒ +ₒ (α ↓ a)) +ₒ (α⁺ ^ₒ (β ↓ b) ↓ e)        ＝⟨ ap (α⁺ ^ₒ (β ↓ b) ×ₒ (𝟙ₒ +ₒ (α ↓ a)) +ₒ_) (↓-eq-lemma (α⁺ ^ₒ (β ↓ b)) ([𝟙+ α ]^ (β ↓ b)) e (IH b)) ⟩
         α⁺ ^ₒ (β ↓ b) ×ₒ (𝟙ₒ +ₒ (α ↓ a)) +ₒ ([𝟙+ α ]^ (β ↓ b) ↓ l₁)    ＝⟨ ap (λ - → - ×ₒ (𝟙ₒ +ₒ (α ↓ a)) +ₒ ([𝟙+ α ]^ (β ↓ b) ↓ l₁)) (IH b) ⟩
         [𝟙+ α ]^ (β ↓ b) ×ₒ (𝟙ₒ +ₒ (α ↓ a)) +ₒ ([𝟙+ α ]^ (β ↓ b) ↓ l₁) ＝⟨ eqtoidₒ (ua 𝓤) fe' _ _ (≃ₒ-sym ([𝟙+ α ]^ β ↓ l₂) ([𝟙+ α ]^ (β ↓ b) ×ₒ (𝟙ₒ +ₒ (α ↓ a)) +ₒ ([𝟙+ α ]^ (β ↓ b) ↓ l₁)) ([𝟙+]^-↓-lemma' α β a b (pr₁ l₁) (pr₂ l₁))) ⟩
         [𝟙+ α ]^ β ↓ l₂                                                ∎)
        where
         l₁ = Idtofun (ap ⟨_⟩ (IH b)) e
         l₂ = (a , b ∷ pr₁ (embed α β b (pr₁ l₁ , pr₂ l₁))) , embed-decreasing α β b l₁

-- \end{code}

-- \begin{code}

-- to-alternative : (α : Ordinal 𝓤) (β : Ordinal 𝓥) → ⟨[𝟙+ α ]^ β ⟩ → ⟨ α ^ₒ β ⟩
-- to-alternative α = transfinite-induction-on-OO (λ β → ⟨[𝟙+ α ]^ β ⟩ → ⟨ α ^ₒ β ⟩) g
--  where
--   g : (β : Ordinal 𝓥) → ((b : ⟨ β ⟩) → ⟨[𝟙+ α ]^ β ↓ b ⟩ →  ⟨ α ^ₒ (β ↓ b) ⟩) →
--       ⟨[𝟙+ α ]^ β ⟩ → ⟨ α ^ₒ β ⟩
--   g β ih ([] , ps) = transport⁻¹ ⟨_⟩ (^ₒ-behaviour α β) (pr₁ (sup-is-upper-bound _ (inl ⋆)) ⋆)
--   g β ih (((a , b) ∷ xs) , ps) = transport⁻¹ ⟨_⟩ (^ₒ-behaviour α β)
--                                              (pr₁ (sup-is-upper-bound _ (inr b))
--                                                   (ih b (decreasing-pr₂-to-more-precise-tail α β a b xs ps
--                                                         , decreasing-pr₂-to-more-precise-tail-decreasing α β a b xs ps) , a))


-- \end{code}
