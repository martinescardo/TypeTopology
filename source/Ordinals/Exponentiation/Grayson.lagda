Tom de Jong, Nicolai Kraus, Fredrik Nordvall Forsberg, Chuangjie Xu.
April 2025.

We implement Robin Grayson's variant of the decreasing list construction of
exponentials, and a proof that it is not, in general, an ordinal, as this would
imply excluded middle.

Grayson's construction is published as [1] which is essentially Chapter IX of
Grayson's PhD thesis [2].

The "concrete" list-based exponentiation that we consider in
Ordinals.Exponentiation.DecreasingList is essentially Grayson's construction,
except that Grayson does not require the base ordinal α to have a trichotomous
least element. In fact, he does not even require α to have a least element and
consequently restricts to those elements x of α for which there exists an a ≺ x.
We shall refer to this condition as "positively non-minimal" as it is a positive
reformulation of non-minimality.

Unfortunately, Grayson's construction does not always yield an ordinal
constructively as we show by a suitable reduction to excluded middle.

However, if α has a trichotomous least element ⊥, then it is straightforward to
show that x : α is positively non-minimal if and only if ⊥ ≺ x, so that
Grayson's construction coincides with our concrete construction (and hence is
always an ordinal).

Grayson moreover claims that his construction satisfies the recursive equation:
   α ^ₒ β ＝ sup (α ^ₒ (β ↓ b) ×ₒ α) ∨ 𝟙ₒ
which we used to define abstract exponentiation in
Ordinals.Exponentiation.Supremum.
Since this recursive equation uniquely specifies the operation ^ₒ, this implies
that Grayson's construction satisfies the equation precisely when it coincides
with abstract exponentiation.
Now, Grayson's construction is easily to seen have a trichotomous least element,
namely the empty list. But given an ordinal α with a least elements, we show in
Ordinals.Exponentiation.Supremum that if the least element of abstract
exponentiation of α by 𝟙ₒ is trichotomous, then the least element of α must be
too. Hence, the recursive equation cannot hold for Grayson's construction (even
in the very simple case where β ＝ 𝟙ₒ) unless α has a trichotomous least
element, in which case the equation holds indeed, as proved in
Ordinals.Exponentiation.RelatingConstructions.

[1] Robin J. Grayson
    Constructive Well-Orderings
    Mathematical Logic Quarterly
    Volume 28, Issue 33-38
    1982
    Pages 495-504
    https://doi.org/10.1002/malq.19820283304

[2] Robin John Grayson
    Intuitionistic Set Theory
    PhD thesis
    University of Oxford
    1978
    https://doi.org/10.5287/ora-azgxayaor

\begin{code}

{-# OPTIONS --safe --without-K --exact-split --lossy-unification #-}

open import UF.Univalence
open import UF.PropTrunc

module Ordinals.Exponentiation.Grayson
       (ua : Univalence)
       (pt : propositional-truncations-exist)
       where

open import UF.ClassicalLogic
open import UF.FunExt
open import UF.UA-FunExt
open import UF.Subsingletons

private
 fe : FunExt
 fe = Univalence-gives-FunExt ua

 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

 pe : Prop-Ext
 pe = Univalence-gives-Prop-Ext ua

open import MLTT.List
open import MLTT.List-Properties
open import MLTT.Plus-Properties
open import MLTT.Spartan

open import UF.Base
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.Sets
open import UF.Sets-Properties
open import UF.Subsingletons-FunExt

open import Ordinals.Arithmetic fe
open import Ordinals.AdditionProperties ua
open import Ordinals.Equivalence
open import Ordinals.Notions
open import Ordinals.OrdinalOfOrdinals ua renaming (_≼_ to _≼OO_)
open import Ordinals.Propositions ua
open import Ordinals.Type
open import Ordinals.Underlying
open import Ordinals.WellOrderArithmetic
open import Ordinals.WellOrderTransport

open import Ordinals.Exponentiation.TrichotomousLeastElement ua pt
open import Ordinals.Exponentiation.DecreasingList ua pt

open PropositionalTruncation pt

\end{code}

\begin{code}

is-positively-non-minimal : {A : 𝓤 ̇  } (R : A → A → 𝓥 ̇  ) → A → 𝓤 ⊔ 𝓥 ̇
is-positively-non-minimal {A = A} R x = ∃ a ꞉ A ,  R a x

Positively-non-minimal : {A : 𝓤 ̇  } (R : A → A → 𝓥 ̇  ) → 𝓤 ⊔ 𝓥 ̇
Positively-non-minimal R = Σ (is-positively-non-minimal R)

Positively-non-minimal-is-set : {A : 𝓤 ̇  } (R : A → A → 𝓥 ̇  )
                              → is-set A
                              → is-set (Positively-non-minimal R)
Positively-non-minimal-is-set {A = A} R s
 = subsets-of-sets-are-sets A (is-positively-non-minimal R) s ∃-is-prop

Positively-non-minimal-order : {A : 𝓤 ̇  } (R : A → A → 𝓥 ̇  ) → Positively-non-minimal R → Positively-non-minimal R → 𝓥 ̇
Positively-non-minimal-order R (a , _) (a' , _) = R a a'

\end{code}

In an ordinal with a trichotomous least element ⊥, an element x is positively
non-minimal if and only if ⊥ ≺ x.

\begin{code}

is-positively-non-minimal-iff-positive
 : (α : Ordinal 𝓤)
 → ((⊥ , τ) : has-trichotomous-least-element α)
 → (x : ⟨ α ⟩) → is-positively-non-minimal (underlying-order α) x ↔ ⊥ ≺⟨ α ⟩ x
is-positively-non-minimal-iff-positive α (⊥ , τ) x =
 (∥∥-rec (Prop-valuedness α ⊥ x) I) , (λ l → ∣ ⊥ , l ∣)
 where
   I : (Σ a ꞉ ⟨ α ⟩ , a ≺⟨ α ⟩ x)
     → ⊥ ≺⟨ α ⟩ x
   I (a , l) = I' (τ a)
    where
     I' : (⊥ ＝ a) + (⊥ ≺⟨ α ⟩ a) → ⊥ ≺⟨ α ⟩ x
     I' (inl refl) = l
     I' (inr k) = Transitivity α ⊥ a x k l

\end{code}

The type of Grayson lists on ordinals α and β is the type of lists over α ×ₒ β
such that the list is (strictly) decreasing in the second component and such
that all the elements in the first component are positively non-minimal.
That is, an element looks like
   (a₀ , b₀) , (a₁ , b₁) , ... , (aₙ , bₙ)
with bₙ ≺ ... ≺ b₁ ≺ b₀ and each aᵢ is positively non-minimal.

We define it a bit more generally below: instead of two ordinals, we just assume
two types and a binary relations on each of them, imposing additional
assumptions only as we need them.

\begin{code}

module _ {A B : 𝓤 ̇  } (R : A → A → 𝓥 ̇  ) (R' : B → B → 𝓥 ̇  ) where

 is-grayson : List (A × B) → 𝓤 ⊔ 𝓥 ̇
 is-grayson l = is-decreasing R' (map pr₂ l)
              × All (is-positively-non-minimal R) (map pr₁ l)

 is-grayson-is-prop : is-prop-valued R'
                    → is-prop-valued-family is-grayson
 is-grayson-is-prop p' l =
  ×-is-prop (is-decreasing-is-prop R' p' (map pr₂ l))
            (All-is-prop _ (λ x → ∃-is-prop) (map pr₁ l))

 GraysonList : 𝓤 ⊔ 𝓥 ̇
 GraysonList = Σ l ꞉ List (A × B) , is-grayson l

 GraysonList-list : GraysonList → List (A × B)
 GraysonList-list = pr₁

 to-GraysonList-＝ : is-prop-valued R'
                   → {l l' : GraysonList}
                   → GraysonList-list l ＝ GraysonList-list l' → l ＝ l'
 to-GraysonList-＝ p' = to-subtype-＝ (is-grayson-is-prop p')

 Grayson-order : GraysonList → GraysonList → 𝓤 ⊔ 𝓥 ̇
 Grayson-order (l , _) (l' , _) = lex (times.order R R') l l'

 Grayson-order-is-prop : is-set A
                       → is-set B
                       → is-prop-valued R
                       → is-prop-valued R'
                       → is-irreflexive R
                       → is-irreflexive R'
                       → is-prop-valued Grayson-order
 Grayson-order-is-prop s s' p p' i i' (l , _) (l' , _) =
  lex-prop-valued (times.order R R')
                  (×-is-set s s')
                  (times.prop-valued _ _ s' p p' i')
                  irr l l'
   where
    irr : is-irreflexive (times.order R R')
    irr (a , b) (inl q) = i' b q
    irr (a , b) (inr (r , q)) = i a q

 GraysonList-⊥ : GraysonList
 GraysonList-⊥ = [] , ([]-decr , [])

\end{code}

For comparison with Ordinals.Exponentiation.DecreasingList, it is
convenient to reformulate the type of Grayson lists slightly:

\begin{code}

 GraysonList' : 𝓤 ⊔ 𝓥 ̇
 GraysonList' = Σ l ꞉ List (Positively-non-minimal R × B) , is-decreasing R' (map pr₂ l)

 Grayson'-order : GraysonList' → GraysonList' → 𝓤 ⊔ 𝓥 ̇
 Grayson'-order (l , _) (l' , _) = lex (times.order (Positively-non-minimal-order R) R') l l'

 Grayson'-order-is-prop : is-set A
                        → is-set B
                        → is-prop-valued R
                        → is-prop-valued R'
                        → is-irreflexive R
                        → is-irreflexive R'
                        → is-prop-valued Grayson'-order
 Grayson'-order-is-prop s s' p p' i i' (l , _) (l' , _) =
  lex-prop-valued (times.order (Positively-non-minimal-order R) R')
                  (×-is-set (Positively-non-minimal-is-set R s) s')
                  (times.prop-valued _ _ s' (λ (x , _) (x' , _) → p x x') p' i')
                  irr l l'
   where
    irr : is-irreflexive (times.order (Positively-non-minimal-order R) R')
    irr (a , b) (inl q) = i' b q
    irr ((a , _) , b) (inr (r , q)) = i a q

 GraysonList-to-List'
  : (l : List (A × B)) → is-grayson l → List ((Positively-non-minimal R) × B)
 GraysonList-to-List' [] p = []
 GraysonList-to-List' (a , b ∷ l) (δ , (p ∷ ps))
  = ((a , p) , b) ∷ GraysonList-to-List' l (tail-is-decreasing R' δ , ps)

 GraysonList-to-List'-decreasing
  : (l : List (A × B))
  → (g : is-grayson l)
  → is-decreasing R' (map pr₂ (GraysonList-to-List' l g))
 GraysonList-to-List'-decreasing [] g = []-decr
 GraysonList-to-List'-decreasing (a , b ∷ []) (δ , (p ∷ ps)) = sing-decr
 GraysonList-to-List'-decreasing (a , b ∷ (a' , b') ∷ l) (many-decr q δ , (p ∷ p' ∷ ps)) =
  many-decr q (GraysonList-to-List'-decreasing ((a' , b') ∷ l) (δ , (p' ∷ ps)))

 GraysonList-to-GraysonList' : GraysonList → GraysonList'
 GraysonList-to-GraysonList' (l , g) =
  GraysonList-to-List' l g , GraysonList-to-List'-decreasing l g

 GraysonList'-to-List : (l : List ((Positively-non-minimal R) × B))
                      → List (A × B)
 GraysonList'-to-List [] = []
 GraysonList'-to-List (((a , _) , b) ∷ l) = (a , b) ∷ GraysonList'-to-List l

 GraysonList'-to-List-grayson : (l : List ((Positively-non-minimal R) × B))
                              → is-decreasing R' (map pr₂ l)
                              → is-grayson ( GraysonList'-to-List l)
 GraysonList'-to-List-grayson [] δ = δ , []
 GraysonList'-to-List-grayson ((a , p) , b ∷ []) δ = sing-decr , (p ∷ [])
 GraysonList'-to-List-grayson ((a , p) , b ∷ (a' , p') , b' ∷ l) (many-decr q δ) =
  many-decr q (pr₁ (GraysonList'-to-List-grayson ((a' , p') , b' ∷ l) δ)) ,
  (p ∷ pr₂ (GraysonList'-to-List-grayson ((a' , p') , b' ∷ l) δ))

 GraysonList'-to-GraysonList : GraysonList' → GraysonList
 GraysonList'-to-GraysonList (l , δ) =
  GraysonList'-to-List l , GraysonList'-to-List-grayson l δ

 GraysonLists-agree : is-prop-valued R' →  GraysonList ≃ GraysonList'
 GraysonLists-agree R'-is-prop =
  GraysonList-to-GraysonList' ,
  qinvs-are-equivs _ (GraysonList'-to-GraysonList , η , ε)
   where
    η : GraysonList'-to-GraysonList  ∘ GraysonList-to-GraysonList' ∼ id
    η (l , g) = to-subtype-＝ (is-grayson-is-prop R'-is-prop) (η' l g)
     where
      η' : (l : List (A × B))(g : is-grayson l)
         → GraysonList'-to-List (GraysonList-to-List' l g) ＝ l
      η' [] g = refl
      η' (x ∷ []) (δ , (p ∷ [])) = refl
      η' (x ∷ x' ∷ l) (many-decr q δ , (p ∷ p' ∷ ps)) =
       ap (x ∷_) (η' (x' ∷ l) (δ , (p' ∷ ps)))

    ε : GraysonList-to-GraysonList'  ∘ GraysonList'-to-GraysonList ∼ id
    ε (l , δ) = to-subtype-＝ (λ l → is-decreasing-is-prop R' R'-is-prop _) (ε' l δ)
     where
      ε' : (l : List (Positively-non-minimal R × B))(δ : is-decreasing R' (map pr₂ l))
         → GraysonList-to-List' (pr₁ (GraysonList'-to-GraysonList (l , δ))) (pr₂ (GraysonList'-to-GraysonList (l , δ))) ＝ l
      ε' [] δ = refl
      ε' (x ∷ []) δ = refl
      ε' (x ∷ x' ∷ l) (many-decr q δ) = ap (x ∷_) (ε' (x' ∷ l) δ)

 Grayson-orders-agree→ : (l l' : GraysonList)
                  → Grayson-order l l' → (Grayson'-order (GraysonList-to-GraysonList' l) (GraysonList-to-GraysonList' l'))
 Grayson-orders-agree→ l ((x ∷ l') , (δ , (p ∷ ps))) []-lex = []-lex
 Grayson-orders-agree→ ((x ∷ l) , (δ , (p ∷ ps))) ((x' ∷ l') , (δ' , (p' ∷ ps'))) (head-lex q) = head-lex q
 Grayson-orders-agree→ ((x ∷ l) , (δ , (p ∷ ps))) ((x ∷ l') , (δ' , (p' ∷ ps'))) (tail-lex refl q) = tail-lex (to-×-＝ (to-subtype-＝ (λ _ → ∃-is-prop) refl) refl) (Grayson-orders-agree→ (l , (tail-is-decreasing R' δ , ps)) (l' , tail-is-decreasing R' δ' , ps') q)

 Grayson-orders-agree← : (l l' : GraysonList)
                  → (Grayson'-order (GraysonList-to-GraysonList' l) (GraysonList-to-GraysonList' l')) → Grayson-order l l'
 Grayson-orders-agree← ([] , _) ((x ∷ l') , (δ , (p ∷ ps))) []-lex = []-lex
 Grayson-orders-agree← ((x ∷ l) , (δ , (p ∷ ps))) ((x' ∷ l') , (δ' , (p' ∷ ps'))) (head-lex q) = head-lex q
 Grayson-orders-agree← ((x ∷ l) , (δ , (p ∷ ps))) ((x ∷ l') , (δ' , (p' ∷ ps'))) (tail-lex refl q) = tail-lex refl (Grayson-orders-agree← (l , (tail-is-decreasing R' δ , ps)) (l' , tail-is-decreasing R' δ' , ps') q)

 Grayson-orders-agree
  : is-set A
  → is-set B
  → is-prop-valued R
  → is-prop-valued R'
  → is-irreflexive R
  → is-irreflexive R'
  → (l l' : GraysonList)
  → Grayson-order l l' ＝ (Grayson'-order (GraysonList-to-GraysonList' l) (GraysonList-to-GraysonList' l'))
 Grayson-orders-agree s s' p p' i i' l l' = pe (Grayson-order-is-prop s s' p p' i i' l l') (Grayson'-order-is-prop s s' p p' i i' _ _) (Grayson-orders-agree→ l l') (Grayson-orders-agree← l l')

\end{code}

We defined is-trichotomous-least for ordinals only, so we inline that definition
in the following.

\begin{code}

 GraysonList-has-trichotomous-least-element
  : is-prop-valued R'
  → (l : GraysonList) → (GraysonList-⊥ ＝ l) + (Grayson-order GraysonList-⊥ l)
 GraysonList-has-trichotomous-least-element p ([] , g) =
  inl (to-GraysonList-＝ p refl)
 GraysonList-has-trichotomous-least-element p ((_ ∷ l) , g) = inr []-lex

\end{code}

We now fix B = 𝟙ₒ, in order to derive properties on the positively
non-minimal elements of A from properties on GraysonList A B.

\begin{code}

module _ {A : 𝓤 ̇  } (R : A → A → 𝓥 ̇  ) where

 GList : 𝓤 ⊔ 𝓥 ̇
 GList = GraysonList {B = 𝟙} R (λ _ _ → 𝟘)

 A⁺ = Σ a ꞉ A , is-positively-non-minimal R a

 R⁺ : A⁺ → A⁺ → 𝓥 ̇
 R⁺ (a , _) (a' , _) = R a a'

 sing : 𝟙 {𝓤 = 𝓤} + A⁺ → GList
 sing (inl ⋆) = ([] , []-decr , [])
 sing (inr (a , p)) = ([ (a , ⋆) ] , sing-decr , (p ∷ []))

 sing⁻¹ : GList → 𝟙 {𝓤 = 𝓤} + A⁺
 sing⁻¹ ([] , _) = inl ⋆
 sing⁻¹ (((a , ⋆) ∷ _) , (q , (p ∷ _))) = inr (a , p)

 sing-retraction : sing⁻¹ ∘ sing ∼ id
 sing-retraction (inl ⋆) = refl
 sing-retraction (inr (a , p)) = refl

 sing-section : sing ∘ sing⁻¹ ∼ id
 sing-section ([] , []-decr , []) = refl
 sing-section ((a , ⋆ ∷ []) , sing-decr , (p ∷ [])) = refl
 sing-section ((a , ⋆ ∷ a' , ⋆ ∷ l) , many-decr r q , (p ∷ ps)) = 𝟘-elim r

 sing-is-equiv : is-equiv sing
 sing-is-equiv = qinvs-are-equivs sing (sing⁻¹ , sing-retraction , sing-section)

 _≺_ : GList → GList →  𝓤 ⊔ 𝓥 ̇
 _≺_ = Grayson-order {B = 𝟙} R (λ _ _ → 𝟘)

 sing⁺ : (x y : A⁺) → R⁺ x y → sing (inr x) ≺ sing (inr y)
 sing⁺ x y p = head-lex (inr (refl , p))

\end{code}

Assuming that the order on Grayson lists is a well-order, so is the order on A⁺.

\begin{code}

 R⁺-propvalued : is-prop-valued _≺_ → is-prop-valued R⁺
 R⁺-propvalued prop x y p q = ap pr₂ II
  where
   I : head-lex (inr (refl , p)) ＝ head-lex (inr (refl , q))
   I = prop (sing (inr x)) (sing (inr y)) (sing⁺ x y p) (sing⁺ x y q)

   II : (refl , p) ＝ (refl , q)
   II = inr-lc (head-lex-lc _ _ _ I)

 R⁺-wellfounded : is-well-founded _≺_ → is-well-founded R⁺
 R⁺-wellfounded wf x = I x (wf (sing (inr x)))
  where
   I : (x : A⁺) → is-accessible _≺_ (sing (inr x)) → is-accessible R⁺ x
   I x (acc f) = acc (λ y p → I y (f (sing (inr y)) (sing⁺ y x p)))

 R⁺-extensional : is-extensional _≺_ → is-extensional R⁺
 R⁺-extensional ext x y p q = inr-lc III
  where
   I : (x y : A⁺)
     → ((z : A⁺) → R⁺ z x → R⁺ z y)
     → (l : GList) → l ≺ sing (inr x) → l ≺ sing (inr y)
   I x y e l []-lex = []-lex
   I x y e ((a , ⋆ ∷ l') , _ , (q ∷ _)) (head-lex (inr (_ , r))) =
    head-lex (inr (refl , e (a , q) r))

   II : sing (inr x) ＝ sing (inr y)
   II = ext (sing (inr x)) (sing (inr y)) (I x y p) (I y x q)

   III = inr x ＝⟨ sing-retraction (inr x) ⁻¹ ⟩
         sing⁻¹ (sing (inr x)) ＝⟨ ap sing⁻¹ II ⟩
         sing⁻¹ (sing (inr y)) ＝⟨ sing-retraction (inr y) ⟩
         inr y ∎

 R⁺-transitive : is-transitive _≺_ → is-transitive R⁺
 R⁺-transitive trans a₀ a₁ a₂ p q = II I
  where
   I : sing (inr a₀) ≺ sing (inr a₂)
   I = trans (sing (inr a₀)) (sing (inr a₁)) (sing (inr a₂))
             (sing⁺ a₀ a₁ p) (sing⁺ a₁ a₂ q)

   II : sing (inr a₀) ≺ sing (inr a₂) → R⁺ a₀ a₂
   II (head-lex (inr (_ , r))) = r

 R⁺-wellorder : is-well-order _≺_ → is-well-order R⁺
 R⁺-wellorder (p , w , e , t) =
  R⁺-propvalued p , R⁺-wellfounded w , R⁺-extensional e , R⁺-transitive t

\end{code}

However, it is a constructive taboo that the subtype of positively non-minimal
elements is always an ordinal, with essentially the same proof as for
subtype-of-positive-elements-an-ordinal-implies-EM in
Ordinals.Exponentiation.Taboos.
Note that we can even restrict to ordinals with a least element.

\begin{code}

subtype-of-positively-non-minimal-elements-an-ordinal-implies-EM
 : ((α : Ordinal (𝓤 ⁺⁺))
   → has-least α
   → is-well-order
      (subtype-order α (is-positively-non-minimal (underlying-order α))))
 → EM 𝓤
subtype-of-positively-non-minimal-elements-an-ordinal-implies-EM {𝓤} hyp = III
 where
  open import Ordinals.OrdinalOfTruthValues fe 𝓤 pe
  open import UF.DiscreteAndSeparated
  open import UF.SubtypeClassifier

  _<_ = subtype-order (OO (𝓤 ⁺)) (is-positively-non-minimal _⊲_)

  <-is-prop-valued : is-prop-valued _<_
  <-is-prop-valued =
   subtype-order-is-prop-valued (OO (𝓤 ⁺)) (is-positively-non-minimal _⊲_)

  hyp' : is-extensional' _<_
  hyp' = extensional-gives-extensional' _<_
          (extensionality _<_ (hyp (OO (𝓤 ⁺)) (𝟘ₒ , 𝟘ₒ-least)))

  Ord⁺ = Σ α ꞉ Ordinal (𝓤 ⁺) , is-positively-non-minimal _⊲_ α

  Ωₚ : Ord⁺
  Ωₚ = Ωₒ , ∣ 𝟘ₒ , ⊥ , eqtoidₒ (ua (𝓤 ⁺)) fe' 𝟘ₒ (Ωₒ ↓ ⊥)
                               (≃ₒ-trans 𝟘ₒ 𝟘ₒ (Ωₒ ↓ ⊥) II I) ∣
   where
    I : 𝟘ₒ ≃ₒ Ωₒ ↓ ⊥
    I = ≃ₒ-sym (Ωₒ ↓ ⊥) 𝟘ₒ (Ωₒ↓-is-id ua ⊥)

    II : 𝟘ₒ {𝓤 ⁺} ≃ₒ 𝟘ₒ {𝓤}
    II = only-one-𝟘ₒ

  𝟚ₚ : Ord⁺
  𝟚ₚ = 𝟚ₒ , ∣ 𝟘ₒ , inl ⋆ , (prop-ordinal-↓ 𝟙-is-prop ⋆ ⁻¹ ∙ +ₒ-↓-left ⋆) ∣

  I : (γ : Ord⁺) → (γ < Ωₚ ↔ γ < 𝟚ₚ)
  I (γ , p) = ∥∥-rec (↔-is-prop fe' fe' (<-is-prop-valued (γ , p) Ωₚ)
                                        (<-is-prop-valued (γ , p) 𝟚ₚ)) I' p
   where
    I' : Σ (λ a → a ⊲ γ) → ((γ , p) < Ωₚ) ↔ ((γ , p) < 𝟚ₚ)
    I' (.(γ ↓ c') , (c' , refl)) = I₁ , I₂
     where
      I₁ : ((γ , p) < Ωₚ) → ((γ , p) < 𝟚ₚ)
      I₁ (P , refl) =
       (inr ⋆ , eqtoidₒ (ua (𝓤 ⁺)) fe' _ _ (≃ₒ-trans (Ωₒ ↓ P) Pₒ (𝟚ₒ ↓ inr ⋆) e₁ e₂))
        where
         Pₒ = prop-ordinal (P holds) (holds-is-prop P)

         e₁ : (Ωₒ ↓ P) ≃ₒ Pₒ
         e₁ = Ωₒ↓-is-id ua P

         e₂ : Pₒ ≃ₒ 𝟚ₒ ↓ inr ⋆
         e₂ = transport⁻¹ (Pₒ ≃ₒ_) (successor-lemma-right 𝟙ₒ)
                          ((prop-ordinal-≃ₒ (holds-is-prop P) 𝟙-is-prop
                                            (λ _ → ⋆)
                                            (λ _ → ≃ₒ-to-fun (Ωₒ ↓ P) Pₒ e₁ c')))

      I₂ : ((γ , p) < 𝟚ₚ) → ((γ , p) < Ωₚ)
      I₂ l = ⊲-⊴-gives-⊲ γ 𝟚ₒ Ωₒ l (𝟚ₒ-leq-Ωₒ ua)

  II : Ω 𝓤 ＝ ⟨ 𝟚ₒ ⟩
  II = ap (⟨_⟩ ∘ pr₁) (hyp' Ωₚ 𝟚ₚ I)

  III : EM 𝓤
  III = Ω-discrete-gives-EM fe' pe
         (equiv-to-discrete
           (idtoeq (𝟙 + 𝟙) (Ω 𝓤) (II ⁻¹))
           (+-is-discrete 𝟙-is-discrete 𝟙-is-discrete))

\end{code}

Hence, putting everything together, it is also a constructive taboo
that GraysonList α β is an ordinal whenever α and β are.

\begin{code}

GraysonList-always-ordinal-implies-EM
 : ((α β : Ordinal (𝓤 ⁺⁺))
   → has-least α
   → is-well-order (Grayson-order (underlying-order α) (underlying-order β)))
 → EM 𝓤
GraysonList-always-ordinal-implies-EM {𝓤} hyp = II
 where
  I : (α : Ordinal (𝓤 ⁺⁺))
    → has-least α
    → is-well-order
       (subtype-order α (is-positively-non-minimal (underlying-order α)))
  I α h = R⁺-wellorder (underlying-order α) (hyp α 𝟙ₒ h)

  II : EM 𝓤
  II = subtype-of-positively-non-minimal-elements-an-ordinal-implies-EM I

\end{code}

Conversely, under the assumption of excluded middle, GraysonList α β
is always an ordinal, because excluded middle implies either α ＝ 𝟘₀,
or α has a least trichotomous element. And if α has a least
trichotomous element, then the notions of being positive and being
positively non-minimal collapses, hence in this case Grayson lists and
our notion of "concrete" exponention coincides.

\begin{code}

trichotomous-least-implies-positive-and-positively-non-minimal-coincide
 : (α : Ordinal 𝓤)
 → (h : has-trichotomous-least-element α)
 → Positively-non-minimal (underlying-order α) ≃ ⟨ α ⁺[ h ] ⟩
trichotomous-least-implies-positive-and-positively-non-minimal-coincide α (a₀ , p)
 = Σ-cong (λ x → idtoeq _ _ (II x (p x)))
  where
   I : (a : ⟨ α ⟩) → a ≺⟨ α ⟩ a₀ → ((a₀ ＝ a) + a₀ ≺⟨ α ⟩ a) → 𝟘
   I a q (inl refl) = irrefl α a q
   I a q (inr q') = irrefl α a (Transitivity α a a₀ a q q')

   II : (x : ⟨ α ⟩) → ((a₀ ＝ x) + a₀ ≺⟨ α ⟩ x)
      → (∃ a ꞉ ⟨ α ⟩ , a ≺⟨ α ⟩ x) ＝ a₀ ≺⟨ α ⟩ x
   II a₀ (inl refl) =
    pe ∃-is-prop (Prop-valuedness α a₀ a₀)
       (∥∥-rec (Prop-valuedness α a₀ a₀) λ (a , q) → 𝟘-elim (I a q (p a)))
       (λ q → 𝟘-elim (irrefl α a₀ q))
   II x (inr q) = pe ∃-is-prop (Prop-valuedness α a₀ x) (λ _ → q) λ _ → ∣ a₀ , q ∣

GraysonList'-coincides-DecreasingList-for-trichotomous-least-base
 : (α β : Ordinal 𝓤)
 → (h : has-trichotomous-least-element α)
 → GraysonList' (underlying-order α) (underlying-order β) ≃ ⟨ exponentiationᴸ α h β ⟩
GraysonList'-coincides-DecreasingList-for-trichotomous-least-base α β h
 = Σ-bicong (λ l → is-decreasing _≺β_ (map pr₂ l))
            (λ l → is-decreasing _≺β_ (map pr₂ l))
            (map ⌜ f ⌝ ,  map-equiv (⌜⌝-is-equiv f))
            𝕘
 where
  _≺β_ = (underlying-order β)
  αₚ = Positively-non-minimal (underlying-order α)

  f : αₚ × ⟨ β ⟩ ≃ ⟨ α ⁺[ h ] ⟩ × ⟨ β ⟩
  f = ×-cong (trichotomous-least-implies-positive-and-positively-non-minimal-coincide α h)
             (≃-refl ⟨ β ⟩)

  𝕘 : (l : List (αₚ × ⟨ β ⟩ ))
    → is-decreasing _≺β_ (map pr₂ l) ≃ is-decreasing _≺β_ (map pr₂ (map ⌜ f ⌝ l))
  𝕘 l = transport⁻¹ (λ - → is-decreasing _≺β_ (map pr₂ l) ≃ is-decreasing _≺β_ -)
                    (map-comp ⌜ f ⌝ pr₂ l)
                    (≃-refl _)

GraysonList-coincides-DecreasingList-for-trichotomous-least-base
 : (α β : Ordinal 𝓤)
 → (h : has-trichotomous-least-element α)
 → GraysonList (underlying-order α) (underlying-order β) ≃ ⟨ exponentiationᴸ α h β ⟩
GraysonList-coincides-DecreasingList-for-trichotomous-least-base α β h =
 ≃-comp (GraysonLists-agree (underlying-order α) (underlying-order β) (Prop-valuedness β))
        (GraysonList'-coincides-DecreasingList-for-trichotomous-least-base α β h)

Grayson'-order→DecrList-order
 : (α β : Ordinal 𝓤)
 → (h : has-trichotomous-least-element α)
 → (l l' : GraysonList' (underlying-order α) (underlying-order β))
 → (Grayson'-order _ _ l l')
 → underlying-order (exponentiationᴸ α h β) (⌜ GraysonList'-coincides-DecreasingList-for-trichotomous-least-base α β h ⌝ l) (⌜ GraysonList'-coincides-DecreasingList-for-trichotomous-least-base α β h ⌝ l')
Grayson'-order→DecrList-order α β h (l , p) (l' , p') []-lex = []-lex
Grayson'-order→DecrList-order α β h (l , p) (l' , p') (head-lex q) = head-lex q
Grayson'-order→DecrList-order α β h ((x ∷ l) , p) ((x' ∷ l') , p') (tail-lex refl q) =
 tail-lex refl
          (Grayson'-order→DecrList-order α β h (l , tail-is-decreasing _ p)
                                               (l' , tail-is-decreasing _ p') q)

DecrList-order→Grayson'-order
 : (α β : Ordinal 𝓤)
 → (h : has-trichotomous-least-element α)
 → (l l' : GraysonList' (underlying-order α) (underlying-order β))
 → underlying-order (exponentiationᴸ α h β) (⌜ GraysonList'-coincides-DecreasingList-for-trichotomous-least-base α β h ⌝ l) (⌜ GraysonList'-coincides-DecreasingList-for-trichotomous-least-base α β h ⌝ l')
 → (Grayson'-order _ _ l l')
DecrList-order→Grayson'-order α β h ([] , p) ((x ∷ l') , p') q = []-lex
DecrList-order→Grayson'-order α β h ((x ∷ l) , p) ((x' ∷ l') , p') (head-lex q) =
 head-lex q
DecrList-order→Grayson'-order α β h ((x ∷ l) , p) ((x' ∷ l') , p') (tail-lex r q) =
 tail-lex (equivs-are-lc _ (⌜⌝-is-equiv _) r ) (DecrList-order→Grayson'-order α β h (l , tail-is-decreasing _ p) (l' , tail-is-decreasing _ p') q)

GraysonList'-order-coincides-DecreasingList-for-trichotomous-least-base
 : (α β : Ordinal 𝓤)
 → (h : has-trichotomous-least-element α)
 → (l l' : GraysonList' (underlying-order α) (underlying-order β))
 → (Grayson'-order _ _ l l') ＝ underlying-order (exponentiationᴸ α h β) (⌜ GraysonList'-coincides-DecreasingList-for-trichotomous-least-base α β h ⌝ l) (⌜ GraysonList'-coincides-DecreasingList-for-trichotomous-least-base α β h ⌝ l')
GraysonList'-order-coincides-DecreasingList-for-trichotomous-least-base α β h l l' =
 pe (Grayson'-order-is-prop _ _ (underlying-type-is-set fe α)
                                (underlying-type-is-set fe β)
                                (Prop-valuedness α)
                                (Prop-valuedness β)
                                (Irreflexivity α)
                                (Irreflexivity β)
                                _ _)
    (Prop-valuedness (exponentiationᴸ α h β) _ _)
    (Grayson'-order→DecrList-order α β h l l')
    (DecrList-order→Grayson'-order α β h l l')

GraysonList-order-coincides-DecreasingList-for-trichotomous-least-base
 : (α β : Ordinal 𝓤)
 → (h : has-trichotomous-least-element α)
 → (l l' : GraysonList (underlying-order α) (underlying-order β))
 → (Grayson-order _ _ l l') ＝ underlying-order (exponentiationᴸ α h β) (⌜ GraysonList-coincides-DecreasingList-for-trichotomous-least-base α β h ⌝ l) (⌜ GraysonList-coincides-DecreasingList-for-trichotomous-least-base α β h ⌝ l')
GraysonList-order-coincides-DecreasingList-for-trichotomous-least-base α β h l l' =
  Grayson-orders-agree (underlying-order α) (underlying-order β)
                       (underlying-type-is-set fe α) (underlying-type-is-set fe β)
                       (Prop-valuedness α) (Prop-valuedness β)
                       (Irreflexivity α) (Irreflexivity β)
                       l l'
 ∙ GraysonList'-order-coincides-DecreasingList-for-trichotomous-least-base α β h _ _

GraysonList-is-ordinal-if-base-has-trichotomous-least
 : (α β : Ordinal 𝓤)
 → has-trichotomous-least-element α
 → is-well-order (Grayson-order (underlying-order α) (underlying-order β))
GraysonList-is-ordinal-if-base-has-trichotomous-least α β h =
 order-transfer-lemma₄.well-order← fe
  (GraysonList _ _) ⟨ exponentiationᴸ α h β ⟩
  (Grayson-order _ _) (underlying-order (exponentiationᴸ α h β))
  (GraysonList-coincides-DecreasingList-for-trichotomous-least-base α β h)
  (λ l l' → idtoeq _ _ (GraysonList-order-coincides-DecreasingList-for-trichotomous-least-base α β h l l'))
  (is-well-ordered (exponentiationᴸ α h β))

\end{code}

Since GraysonList 𝟘ₒ β ＝ 𝟙, we do have that GraysonList 𝟘ₒ β is an ordinal.

\begin{code}

GraysonList-is-𝟙-if-base-zero
 : (β : Ordinal 𝓤) → GraysonList (underlying-order 𝟘ₒ) (underlying-order β) ≃ 𝟙 {𝓤}
GraysonList-is-𝟙-if-base-zero β = (λ _ → ⋆) , qinvs-are-equivs _ ((λ _ → GraysonList-⊥ _ _) , η , ε)
 where
  η : (λ _ → GraysonList-⊥ _ _) ∼ id
  η ([] , ([]-decr , [])) = refl
  η (((a , b) ∷ l) , _) = 𝟘-elim a

  ε : (λ _ → ⋆) ∼ id
  ε x = refl

GraysonOrder-is-𝟘-if-base-zero
 : (β : Ordinal 𝓤)
 → (l l' : GraysonList (underlying-order 𝟘ₒ) (underlying-order β))
 → Grayson-order (underlying-order 𝟘ₒ) (underlying-order β) l l' ＝ 𝟘 {𝓤}
GraysonOrder-is-𝟘-if-base-zero β l l' =
 pe (Grayson-order-is-prop _ _ (underlying-type-is-set fe 𝟘ₒ) (underlying-type-is-set fe β) (Prop-valuedness 𝟘ₒ) (Prop-valuedness β) (Irreflexivity 𝟘ₒ) (Irreflexivity β) l l')
    𝟘-is-prop
    (η l l')
    𝟘-elim
   where
    η : (l l' : GraysonList (underlying-order 𝟘ₒ) (underlying-order β))
      → Grayson-order (underlying-order 𝟘ₒ) (underlying-order β) l l' → 𝟘
    η ([] , _) ([] , _) p = 𝟘-elim (lex-irreflexive _ (λ x → 𝟘-elim (pr₁ x)) [] p)
    η ([] , _) (((a' , b') ∷ l') , _) p = 𝟘-elim a'
    η (((a' , b) ∷ l) , _) _ p = 𝟘-elim a'

GraysonList-is-ordinal-if-base-zero
 : (β : Ordinal 𝓤)
 → is-well-order (Grayson-order (underlying-order 𝟘ₒ) (underlying-order β))
GraysonList-is-ordinal-if-base-zero β =
  order-transfer-lemma₄.well-order← fe
   (GraysonList _ _) 𝟙
   (Grayson-order (underlying-order 𝟘ₒ) (underlying-order β))
   (underlying-order 𝟙ₒ)
   (GraysonList-is-𝟙-if-base-zero β)
   (λ l l' → idtoeq _ _ (GraysonOrder-is-𝟘-if-base-zero β l l'))
   (is-well-ordered 𝟙ₒ)

\end{code}

We are now in a position to prove the converse of
GraysonList-always-ordinal-implies-EM:

\begin{code}

EM-implies-GraysonList-is-ordinal
 : EM 𝓤
 → (α β : Ordinal 𝓤)
 → is-well-order (Grayson-order (underlying-order α) (underlying-order β))
EM-implies-GraysonList-is-ordinal em α β = I (EM-gives-Has-trichotomous-least-element-or-is-zero em α)
 where
  I : has-trichotomous-least-element-or-is-zero α
    → is-well-order (Grayson-order (underlying-order α) (underlying-order β))
  I (inl h) = GraysonList-is-ordinal-if-base-has-trichotomous-least α β h
  I (inr refl) = GraysonList-is-ordinal-if-base-zero β

\end{code}
