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


-- TODO: Generalize universe levels later (first +ₒ should be made more general)
amazing : (α : Ordinal 𝓤) (β : Ordinal 𝓤) → (𝟙ₒ +ₒ α) ^ₒ β ＝ [𝟙+ α ]^ β
amazing {𝓤} α = transfinite-induction-on-OO _ I
 where
  I : (β : Ordinal 𝓤)
    → ((b : ⟨ β ⟩) → (𝟙ₒ +ₒ α) ^ₒ (β ↓ b) ＝ ([𝟙+ α ]^ (β ↓ b)))
    → (𝟙ₒ +ₒ α) ^ₒ β ＝ ([𝟙+ α ]^ β)
  I β IH = ⊲-is-extensional ((𝟙ₒ +ₒ α) ^ₒ β) ([𝟙+ α ]^ β) II III
   where
    II : (γ : Ordinal 𝓤) → γ ⊲ (𝟙ₒ +ₒ α) ^ₒ β → γ ⊲ ([𝟙+ α ]^ β)
    II _ (e , refl) = ∥∥-rec (⊲-is-prop-valued ((𝟙ₒ +ₒ α) ^ₒ β ↓ e) ([𝟙+ α ]^ β))
                              the-real-thing
                              (sup-is-upper-bound-jointly-surjective (cases {X = 𝟙{𝓤}} (λ _ → 𝟙ₒ) (λ b → (𝟙ₒ +ₒ α) ^ₒ (β ↓ b) ×ₒ (𝟙ₒ +ₒ α)))
                              (Idtofun (ap ⟨_⟩ (^ₒ-behaviour (𝟙ₒ +ₒ α) β)) e))
     where
      the-real-thing : Σ i ꞉ (𝟙 + ⟨ β ⟩) , Σ x ꞉ ⟨ (cases {X = 𝟙{𝓤}} (λ _ → 𝟙ₒ) (λ b → (𝟙ₒ +ₒ α) ^ₒ (β ↓ b) ×ₒ (𝟙ₒ +ₒ α))) i ⟩ ,
                               pr₁ (sup-is-upper-bound _ i) x ＝ Idtofun (ap ⟨_⟩ (^ₒ-behaviour (𝟙ₒ +ₒ α) β)) e
                     → ((𝟙ₒ +ₒ α) ^ₒ β) ↓ e ⊲ [𝟙+ α ]^ β
      the-real-thing (inl _ , ⋆ , p) = _ , foo
       where
        foo = ((𝟙ₒ +ₒ α) ^ₒ β ↓ e) ＝⟨ ↓-eq-lemma ((𝟙ₒ +ₒ α) ^ₒ β) (sup (cases (λ _ → 𝟙ₒ) (λ b₁ → (𝟙ₒ +ₒ α) ^ₒ (β ↓ b₁) ×ₒ (𝟙ₒ +ₒ α)))) e (^ₒ-behaviour (𝟙ₒ +ₒ α) β) ⟩
              (sup (cases (λ _ → 𝟙ₒ) (λ b₁ → (𝟙ₒ +ₒ α) ^ₒ (β ↓ b₁) ×ₒ (𝟙ₒ +ₒ α))) ↓ x) ＝⟨ fact ⟩
              (sup (cases (λ _ → 𝟙ₒ) (λ b₁ → (𝟙ₒ +ₒ α) ^ₒ (β ↓ b₁) ×ₒ (𝟙ₒ +ₒ α))) ↓ y) ＝⟨ initial-segment-of-sup-at-component _ (inl ⋆) ⋆ ⟩
              (𝟙ₒ ↓ ⋆) ＝⟨ prop-ordinal-↓ 𝟙-is-prop ⋆ ⟩
              𝟘ₒ ＝⟨ [𝟙+α]^β-has-least' α β []-decr ⟩
              (([𝟙+ α ]^ β) ↓ ([] , []-decr)) ∎
         where
          x : ⟨ sup (cases (λ _ → 𝟙ₒ) (λ b₁ → (𝟙ₒ +ₒ α) ^ₒ (β ↓ b₁) ×ₒ (𝟙ₒ +ₒ α))) ⟩
          x = Idtofun (ap (λ v → pr₁ v) (^ₒ-behaviour (𝟙ₒ +ₒ α) β)) e
          y : ⟨ sup (cases (λ _ → 𝟙ₒ) (λ b₁ → (𝟙ₒ +ₒ α) ^ₒ (β ↓ b₁) ×ₒ (𝟙ₒ +ₒ α))) ⟩
          y = pr₁ (sup-is-upper-bound _ (inl ⋆)) ⋆
          p-fact : x ＝ y
          p-fact = p ⁻¹
          fact = ap (sup (cases {X = 𝟙{𝓤}} (λ _ → 𝟙ₒ) (λ b₁ → (𝟙ₒ +ₒ α) ^ₒ (β ↓ b₁) ×ₒ (𝟙ₒ +ₒ α))) ↓_) p-fact
      the-real-thing (inr b , (e' , inl ⋆) , p) = _ , foo
       where
        foo = ((𝟙ₒ +ₒ α) ^ₒ β ↓ e) ＝⟨ ↓-eq-lemma ((𝟙ₒ +ₒ α) ^ₒ β) (sup (cases (λ _ → 𝟙ₒ) (λ b₁ → (𝟙ₒ +ₒ α) ^ₒ (β ↓ b₁) ×ₒ (𝟙ₒ +ₒ α)))) e (^ₒ-behaviour (𝟙ₒ +ₒ α) β) ⟩
              (sup (cases (λ _ → 𝟙ₒ) (λ b₁ → (𝟙ₒ +ₒ α) ^ₒ (β ↓ b₁) ×ₒ (𝟙ₒ +ₒ α))) ↓ x) ＝⟨ fact ⟩
              (sup (cases (λ _ → 𝟙ₒ) (λ b₁ → (𝟙ₒ +ₒ α) ^ₒ (β ↓ b₁) ×ₒ (𝟙ₒ +ₒ α))) ↓ y) ＝⟨ initial-segment-of-sup-at-component _ (inr b) (e' , inl ⋆) ⟩
              (((𝟙ₒ +ₒ α) ^ₒ (β ↓ b) ×ₒ (𝟙ₒ +ₒ α)) ↓ (e' , inl ⋆)) ＝⟨ ×ₒ-↓ ((𝟙ₒ +ₒ α) ^ₒ (β ↓ b)) (𝟙ₒ +ₒ α) ⟩
              ((((𝟙ₒ +ₒ α) ^ₒ (β ↓ b)) ×ₒ ((𝟙ₒ +ₒ α) ↓ inl ⋆)) +ₒ ((𝟙ₒ +ₒ α) ^ₒ (β ↓ b) ↓ e')) ＝⟨ calc ⟩
              (𝟘ₒ +ₒ ((𝟙ₒ +ₒ α) ^ₒ (β ↓ b) ↓ e')) ＝⟨ 𝟘ₒ-left-neutral _ ⟩
              ((𝟙ₒ +ₒ α) ^ₒ (β ↓ b) ↓ e') ＝⟨ ↓-eq-lemma ((𝟙ₒ +ₒ α) ^ₒ (β ↓ b)) ([𝟙+ α ]^ (β ↓ b)) e' (IH b) ⟩
              (([𝟙+ α ]^ (β ↓ b)) ↓ e'') ＝⟨ fact' ⟩
              (([𝟙+ α ]^ β) ↓ pr₁ σ e'') ∎
         where
          x : ⟨ sup (cases (λ _ → 𝟙ₒ) (λ b₁ → (𝟙ₒ +ₒ α) ^ₒ (β ↓ b₁) ×ₒ (𝟙ₒ +ₒ α))) ⟩
          x = Idtofun (ap (λ v → pr₁ v) (^ₒ-behaviour (𝟙ₒ +ₒ α) β)) e
          y : ⟨ sup (cases (λ _ → 𝟙ₒ) (λ b₁ → (𝟙ₒ +ₒ α) ^ₒ (β ↓ b₁) ×ₒ (𝟙ₒ +ₒ α))) ⟩
          y = pr₁ (sup-is-upper-bound _ (inr b)) (e' , inl ⋆)
          p-fact : x ＝ y
          p-fact = p ⁻¹
          fact = ap (sup (cases {X = 𝟙{𝓤}} (λ _ → 𝟙ₒ) (λ b₁ → (𝟙ₒ +ₒ α) ^ₒ (β ↓ b₁) ×ₒ (𝟙ₒ +ₒ α))) ↓_) p-fact
          e'' : ⟨ ([𝟙+ α ]^ (β ↓ b)) ⟩
          e'' = Idtofun (ap (λ v → pr₁ v) (IH b)) e'
          σ : ([𝟙+ α ]^ (β ↓ b)) ⊴ ([𝟙+ α ]^ β)
          σ = ≼-gives-⊴ ([𝟙+ α ]^ (β ↓ b)) ([𝟙+ α ]^ β) (monotone-in-exponent α (β ↓ b) β (⊲-gives-≼ (β ↓ b) β (b , refl)))
          fact' = simulations-preserve-↓ ([𝟙+ α ]^ (β ↓ b)) ([𝟙+ α ]^ β) σ e''
          calc = ap (_+ₒ ((𝟙ₒ +ₒ α) ^ₒ (β ↓ b) ↓ e'))
                    (ap (((𝟙ₒ +ₒ α) ^ₒ (β ↓ b)) ×ₒ_) ((+ₒ-↓-left ⋆) ⁻¹ ∙ prop-ordinal-↓ 𝟙-is-prop ⋆)
                                                                        ∙ ×ₒ-𝟘ₒ-right ((𝟙ₒ +ₒ α) ^ₒ (β ↓ b)))
      the-real-thing (inr b , (e' , inr a) , p) = _ , foo
       where
        foo = ((𝟙ₒ +ₒ α) ^ₒ β ↓ e) ＝⟨ ↓-eq-lemma ((𝟙ₒ +ₒ α) ^ₒ β) (sup (cases (λ _ → 𝟙ₒ) (λ b₁ → (𝟙ₒ +ₒ α) ^ₒ (β ↓ b₁) ×ₒ (𝟙ₒ +ₒ α)))) e (^ₒ-behaviour (𝟙ₒ +ₒ α) β) ⟩
              (sup (cases (λ _ → 𝟙ₒ) (λ b₁ → (𝟙ₒ +ₒ α) ^ₒ (β ↓ b₁) ×ₒ (𝟙ₒ +ₒ α))) ↓ x) ＝⟨ fact ⟩
              (sup (cases (λ _ → 𝟙ₒ) (λ b₁ → (𝟙ₒ +ₒ α) ^ₒ (β ↓ b₁) ×ₒ (𝟙ₒ +ₒ α))) ↓ y) ＝⟨ initial-segment-of-sup-at-component _ (inr b) (e' , inr a) ⟩
              (((𝟙ₒ +ₒ α) ^ₒ (β ↓ b) ×ₒ (𝟙ₒ +ₒ α)) ↓ (e' , inr a)) ＝⟨ ×ₒ-↓ ((𝟙ₒ +ₒ α) ^ₒ (β ↓ b)) (𝟙ₒ +ₒ α) ⟩
              ((((𝟙ₒ +ₒ α) ^ₒ (β ↓ b)) ×ₒ ((𝟙ₒ +ₒ α) ↓ inr a)) +ₒ ((𝟙ₒ +ₒ α) ^ₒ (β ↓ b) ↓ e')) ＝⟨ calc ⟩
              ((((𝟙ₒ +ₒ α) ^ₒ (β ↓ b)) ×ₒ ((𝟙ₒ +ₒ (α ↓ a)))) +ₒ ((𝟙ₒ +ₒ α) ^ₒ (β ↓ b) ↓ e')) ＝⟨ ap (λ - → (- ×ₒ ((𝟙ₒ +ₒ (α ↓ a)))) +ₒ ((𝟙ₒ +ₒ α) ^ₒ (β ↓ b) ↓ e')) (IH b) ⟩
              ((([𝟙+ α ]^ (β ↓ b)) ×ₒ (𝟙ₒ +ₒ (α ↓ a))) +ₒ ((𝟙ₒ +ₒ α) ^ₒ (β ↓ b) ↓ e')) ＝⟨ ap ((([𝟙+ α ]^ (β ↓ b)) ×ₒ (𝟙ₒ +ₒ (α ↓ a))) +ₒ_) (↓-eq-lemma _ _ e' (IH b)) ⟩
              ((([𝟙+ α ]^ (β ↓ b)) ×ₒ (𝟙ₒ +ₒ (α ↓ a))) +ₒ (([𝟙+ α ]^ (β ↓ b)) ↓ l)) ＝⟨ eqtoidₒ (ua 𝓤) fe' _ _ (≃ₒ-sym _ _ ([𝟙+]^-↓-lemma' α β a b (pr₁ l) (pr₂ l))) ⟩
              (([𝟙+ α ]^ β) ↓ (((a , b) ∷ pr₁ (embed α β b l)) , embed-decreasing α β b l)) ∎
         where
          x : ⟨ (sup (cases (λ _ → 𝟙ₒ) (λ b₁ → (𝟙ₒ +ₒ α) ^ₒ (β ↓ b₁) ×ₒ (𝟙ₒ +ₒ α)))) ⟩
          x = Idtofun (ap ⟨_⟩ (^ₒ-behaviour (𝟙ₒ +ₒ α) β)) e
          y : ⟨ (sup (cases {X = 𝟙{𝓤}} (λ _ → 𝟙ₒ) (λ b₁ → (𝟙ₒ +ₒ α) ^ₒ (β ↓ b₁) ×ₒ (𝟙ₒ +ₒ α)))) ⟩
          y = pr₁ (sup-is-upper-bound _ (inr b)) (e' , inr a)
          p-fact : x ＝ y
          p-fact = p ⁻¹
          fact = ap (sup (cases {X = 𝟙{𝓤}} (λ _ → 𝟙ₒ) (λ b₁ → (𝟙ₒ +ₒ α) ^ₒ (β ↓ b₁) ×ₒ (𝟙ₒ +ₒ α))) ↓_) p-fact
          l = Idtofun (ap (λ v → pr₁ v) (IH b)) e'
          calc = ap (_+ₒ ((𝟙ₒ +ₒ α) ^ₒ (β ↓ b) ↓ e')) (ap (((𝟙ₒ +ₒ α) ^ₒ (β ↓ b)) ×ₒ_) ((+ₒ-↓-right a) ⁻¹))
    III : (γ : Ordinal 𝓤) → γ ⊲ ([𝟙+ α ]^ β) → γ ⊲ (𝟙ₒ +ₒ α) ^ₒ β
    III _ (([] , δ) , refl) = transport (_⊲ (𝟙ₒ +ₒ α) ^ₒ β) ([𝟙+α]^β-has-least' α β δ) (^ₒ-is-positive (𝟙ₒ +ₒ α) β)
    III _ ((((a , b) ∷ l) , δ) , refl) = _ , foo
     where
      foo = (([𝟙+ α ]^ β) ↓ ((a , b ∷ l) , δ)) ＝⟨ eqtoidₒ (ua 𝓤) fe' _ _ ([𝟙+]^-↓-lemma α β a b l δ) ⟩
            ((([𝟙+ α ]^ (β ↓ b)) ×ₒ (𝟙ₒ +ₒ (α ↓ a))) +ₒ
              (([𝟙+ α ]^ (β ↓ b)) ↓ l')) ＝⟨ ap (λ - → (- ×ₒ (𝟙ₒ +ₒ (α ↓ a))) +ₒ (([𝟙+ α ]^ (β ↓ b)) ↓ l')) ((IH b) ⁻¹) ⟩
            (((𝟙ₒ +ₒ α) ^ₒ (β ↓ b) ×ₒ (𝟙ₒ +ₒ (α ↓ a))) +ₒ
              (([𝟙+ α ]^ (β ↓ b)) ↓ l')) ＝⟨ ap (((𝟙ₒ +ₒ α) ^ₒ (β ↓ b) ×ₒ (𝟙ₒ +ₒ (α ↓ a))) +ₒ_) fact ⟩
            (((𝟙ₒ +ₒ α) ^ₒ (β ↓ b) ×ₒ (𝟙ₒ +ₒ (α ↓ a))) +ₒ ((𝟙ₒ +ₒ α) ^ₒ (β ↓ b) ↓ l'')) ＝⟨ calc ⟩
            (((𝟙ₒ +ₒ α) ^ₒ (β ↓ b) ×ₒ ((𝟙ₒ +ₒ α) ↓ inr a)) +ₒ ((𝟙ₒ +ₒ α) ^ₒ (β ↓ b) ↓ l'')) ＝⟨ fold ⟩
            (((𝟙ₒ +ₒ α) ^ₒ (β ↓ b) ×ₒ (𝟙ₒ +ₒ α)) ↓ (l'' , inr a)) ＝⟨ fact' ⟩
            (sup (cases (λ _ → 𝟙ₒ) (λ b₁ → (𝟙ₒ +ₒ α) ^ₒ (β ↓ b₁) ×ₒ (𝟙ₒ +ₒ α)))
              ↓
              pr₁
              (sup-is-upper-bound _
               (inr b))
              (l'' , inr a)) ＝⟨ ↓-eq-lemma _ ((𝟙ₒ +ₒ α) ^ₒ β) (pr₁ (sup-is-upper-bound _ (inr b)) (l'' , inr a)) ((^ₒ-behaviour (𝟙ₒ +ₒ α) β) ⁻¹) ⟩
            (((𝟙ₒ +ₒ α) ^ₒ β) ↓ _) ∎
       where
        l' = more-precise-tail-pair α β a b l δ
        l'' : ⟨ (𝟙ₒ +ₒ α) ^ₒ (β ↓ b) ⟩
        l'' = Idtofun (ap ⟨_⟩ ((IH b) ⁻¹)) l'
        fact : (([𝟙+ α ]^ (β ↓ b)) ↓ l') ＝ ((𝟙ₒ +ₒ α) ^ₒ (β ↓ b)) ↓ l''
        fact = ↓-eq-lemma ([𝟙+ α ]^ (β ↓ b)) ((𝟙ₒ +ₒ α) ^ₒ (β ↓ b)) l' ((IH b) ⁻¹)
        fold : (((𝟙ₒ +ₒ α) ^ₒ (β ↓ b) ×ₒ ((𝟙ₒ +ₒ α) ↓ inr a)) +ₒ
                  ((𝟙ₒ +ₒ α) ^ₒ (β ↓ b) ↓ l''))
                 ＝ (((𝟙ₒ +ₒ α) ^ₒ (β ↓ b) ×ₒ (𝟙ₒ +ₒ α)) ↓ (l'' , inr a))
        fold = ×ₒ-↓ ((𝟙ₒ +ₒ α) ^ₒ (β ↓ b)) (𝟙ₒ +ₒ α) ⁻¹
        fact' = (initial-segment-of-sup-at-component (cases {X = 𝟙{𝓤}} (λ _ → 𝟙ₒ) (λ b → (𝟙ₒ +ₒ α) ^ₒ (β ↓ b) ×ₒ (𝟙ₒ +ₒ α))) (inr b) (l'' , inr a)) ⁻¹
        calc = ap (_+ₒ ((𝟙ₒ +ₒ α) ^ₒ (β ↓ b) ↓ l'')) (ap (((𝟙ₒ +ₒ α) ^ₒ (β ↓ b)) ×ₒ_) (+ₒ-↓-right a))

-- \end{code}

-- \begin{code}

-- -- An ordinal that can perhaps be useful in deriving constructive taboos

-- {-
-- module _ (P : 𝓤 ̇ ) where

--  _≺𝟚ₚ_ : 𝟚 {𝓤} → 𝟚 {𝓤} → 𝓤 ̇
--  ₀ ≺𝟚ₚ ₀ = 𝟘
--  ₀ ≺𝟚ₚ ₁ = P
--  ₁ ≺𝟚ₚ ₀ = ¬ P
--  ₁ ≺𝟚ₚ ₁ = 𝟘

--  ≺-is-prop-valued : is-prop P → is-prop-valued _≺𝟚ₚ_
--  ≺-is-prop-valued i ₀ ₀ = 𝟘-is-prop
--  ≺-is-prop-valued i ₀ ₁ = i
--  ≺-is-prop-valued i ₁ ₀ = Π-is-prop fe' (λ x → 𝟘-is-prop)
--  ≺-is-prop-valued i ₁ ₁ = 𝟘-is-prop

--  ≺-is-transitive : transitive _≺𝟚ₚ_
--  ≺-is-transitive ₀ ₁ ₀ u v = 𝟘-elim (v u)
--  ≺-is-transitive ₀ ₁ ₁ u v = 𝟘-elim v
--  ≺-is-transitive ₁ ₀ ₁ u v = 𝟘-elim (u v)
--  ≺-is-transitive ₁ ₁ z u v = 𝟘-elim u

--  ≺-is-extensional : is-extensional _≺𝟚ₚ_
--  ≺-is-extensional ₀ ₀ u v = refl
--  ≺-is-extensional ₁ ₁ u v = refl
--  ≺-is-extensional ₀ ₁ u v = 𝟘-elim (δ γ)
--   where
--    γ : ¬ P
--    γ p = 𝟘-elim (v ₀ p)
--    δ : ¬ ¬ P
--    δ np = 𝟘-elim (u ₁ np)
--  ≺-is-extensional ₁ ₀ u v = 𝟘-elim (δ γ)
--   where
--    γ : ¬ P
--    γ p = 𝟘-elim (u ₀ p)
--    δ : ¬ ¬ P
--    δ np = 𝟘-elim (v ₁ np)

--  ≺-is-well-founded : is-well-founded _≺𝟚ₚ_
--  ≺-is-well-founded ₀ = acc ₀-accessible
--   where
--     ₀-accessible : (y : 𝟚) → y ≺𝟚ₚ ₀ → is-accessible _≺𝟚ₚ_ y
--     ₀-accessible ₁ np = acc g
--      where
--       g : (y : 𝟚) → y ≺𝟚ₚ ₁ → is-accessible _≺𝟚ₚ_ y
--       g ₀ p = 𝟘-elim (np p)
--  ≺-is-well-founded ₁ = acc ₁-accessible
--   where
--    ₁-accessible : (y : 𝟚) → y ≺𝟚ₚ ₁ → is-accessible _≺𝟚ₚ_ y
--    ₁-accessible ₀ p = acc g
--     where
--      g : (y : 𝟚) → y ≺𝟚ₚ ₀ → is-accessible _≺𝟚ₚ_ y
--      g ₁ np = 𝟘-elim (np p)

--  ≺𝟚ₚ-ordinal : is-prop P → Ordinal 𝓤
--  ≺𝟚ₚ-ordinal i = 𝟚 , _≺𝟚ₚ_ , ≺-is-prop-valued i , ≺-is-well-founded , ≺-is-extensional , ≺-is-transitive

--  ≺-trichotomous-characterization : is-trichotomous-order _≺𝟚ₚ_ ↔ (P + ¬ P)
--  ≺-trichotomous-characterization = ⦅⇒⦆ , ⦅⇐⦆
--   where
--    ⦅⇐⦆ : (P + ¬ P) → is-trichotomous-order _≺𝟚ₚ_
--    ⦅⇐⦆ p ₀ ₀ = inr (inl refl)
--    ⦅⇐⦆ (inl p) ₀ ₁ = inl p
--    ⦅⇐⦆ (inr np) ₀ ₁ = inr (inr np)
--    ⦅⇐⦆ (inl p) ₁ ₀ = inr (inr p)
--    ⦅⇐⦆ (inr np) ₁ ₀ = inl np
--    ⦅⇐⦆ p ₁ ₁ = inr (inl refl)
--    ⦅⇒⦆ : is-trichotomous-order _≺𝟚ₚ_ → (P + ¬ P)
--    ⦅⇒⦆ t = translate (t ₀ ₁)
--     where
--      translate : (₀ ≺𝟚ₚ ₁) + (₀ ＝ ₁) + (₁ ≺𝟚ₚ ₀) → (P + ¬ P)
--      translate (inl p)       = inl p
--      translate (inr (inl e)) = 𝟘-elim (+disjoint e)
--      translate (inr (inr np)) = inr np
-- -}

-- \end{code}

\end{code}

\begin{code}

to-alternative : (α : Ordinal 𝓤) (β : Ordinal 𝓥) → ⟨[𝟙+ α ]^ β ⟩ → ⟨ α ^ₒ β ⟩
to-alternative α = transfinite-induction-on-OO (λ β → ⟨[𝟙+ α ]^ β ⟩ → ⟨ α ^ₒ β ⟩) g
 where
  g : (β : Ordinal 𝓥) → ((b : ⟨ β ⟩) → ⟨[𝟙+ α ]^ β ↓ b ⟩ →  ⟨ α ^ₒ (β ↓ b) ⟩) →
      ⟨[𝟙+ α ]^ β ⟩ → ⟨ α ^ₒ β ⟩
  g β ih ([] , ps) = transport⁻¹ ⟨_⟩ (^ₒ-behaviour α β) (pr₁ (sup-is-upper-bound _ (inl ⋆)) ⋆)
  g β ih (((a , b) ∷ xs) , ps) = transport⁻¹ ⟨_⟩ (^ₒ-behaviour α β)
                                             (pr₁ (sup-is-upper-bound _ (inr b))
                                                  (ih b (decreasing-pr₂-to-more-precise-tail α β a b xs ps
                                                        , decreasing-pr₂-to-more-precise-tail-decreasing α β a b xs ps) , a))


\end{code}
