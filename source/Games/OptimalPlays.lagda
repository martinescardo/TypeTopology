Martin Escardo, Paulo Oliva, 27th November 2024 - 14th May 2025

We define optimal moves and optimal plays for sequential games. Then
using the JT monad, with T the monad List⁺ of non-empty lists, we
compute all optimal plays of a game, provided it has ordinary
selection functions.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (𝓤 ; J)
open import UF.FunExt
open import UF.DiscreteAndSeparated

\end{code}

We work with a type of outcomes R with decidable equality (called
discreteness).

\begin{code}

module Games.OptimalPlays
        (fe : Fun-Ext)
        {𝓥 𝓦₀  : Universe}
        (R : 𝓦₀ ̇ )
        (R-is-discrete : is-discrete R)
       where

𝓤 : Universe
𝓤 = 𝓥 ⊔ 𝓦₀

open import Games.FiniteHistoryDependent {𝓤} {𝓦₀} R
open import Games.TypeTrees {𝓤}
open import MLTT.List hiding ([_]) renaming (map to lmap)
open import MonadOnTypes.J-transf-variation
open import MonadOnTypes.JK
open import MonadOnTypes.K
open import MonadOnTypes.List
open import MonadOnTypes.Construction
open import MonadOnTypes.NonEmptyList
open import Notation.CanonicalMap
open import UF.Base
open import UF.Subsingletons

open K-definitions R

\end{code}

The following are the main two notions considered in this file.

\begin{code}

is-optimal-move : {X : 𝓤 ̇ }
                  {Xf : X → 𝑻}
                  (q : (Σ x ꞉ X , Path (Xf x)) → R)
                  (ϕ : K X)
                  (ϕf : (x : X) → 𝓚 (Xf x))
                → X
                → 𝓦₀ ̇
is-optimal-move {X} {Xf} q ϕ ϕf x =
 optimal-outcome (game (X ∷ Xf) q (ϕ :: ϕf))
 ＝ optimal-outcome (game (Xf x) (subpred q x) (ϕf x))

is-optimal-play : {Xt : 𝑻} → 𝓚 Xt → (Path Xt → R) → Path Xt → 𝓦₀ ̇
is-optimal-play {[]}     ⟨⟩        q ⟨⟩        = 𝟙
is-optimal-play {X ∷ Xf} (ϕ :: ϕf) q (x :: xs) =
   is-optimal-move {X} {Xf} q ϕ ϕf x
 × is-optimal-play {Xf x} (ϕf x) (subpred q x) xs

\end{code}

Being an optimal move is a decidable proposition.

\begin{code}

being-optimal-move-is-prop : {X : 𝓤 ̇ }
                             {Xf : X → 𝑻}
                             (q : (Σ x ꞉ X , Path (Xf x)) → R)
                             (ϕ : K X)
                             (ϕf : (x : X) → 𝓚 (Xf x))
                             (x : X)
                           → is-prop (is-optimal-move q ϕ ϕf x)
being-optimal-move-is-prop q ϕ ϕf x = discrete-types-are-sets R-is-discrete

being-optimal-move-is-decidable : {X : 𝓤 ̇ }
                                  {Xf : X → 𝑻}
                                  (q : (Σ x ꞉ X , Path (Xf x)) → R)
                                  (ϕ : K X)
                                  (ϕf : (x : X) → 𝓚 (Xf x))
                                  (x : X)
                                → is-decidable (is-optimal-move q ϕ ϕf x)
being-optimal-move-is-decidable q ϕ ϕf x = R-is-discrete _ _

\end{code}

We now show that the strategic path of a strategy in subgame perfect
equilibrium is an optimal play. We start with a lemma that is
interesting on its own right.

\begin{code}

optimal-play-gives-optimal-outcome
 : {Xt : 𝑻}
   (ϕt : 𝓚 Xt)
   (q : Path Xt → R)
   (xs : Path Xt)
 → is-optimal-play {Xt} ϕt q xs
 → q xs ＝ optimal-outcome (game Xt q ϕt)
optimal-play-gives-optimal-outcome {[]}     ⟨⟩        q ⟨⟩        ⟨⟩ = refl
optimal-play-gives-optimal-outcome {X ∷ Xf} (ϕ :: ϕf) q (x :: xs) (o :: os)
 = subpred q x xs                                     ＝⟨ IH ⟩
   optimal-outcome (game (Xf x) (subpred q x) (ϕf x)) ＝⟨ o ⁻¹ ⟩
   optimal-outcome (game (X ∷ Xf) q (ϕ :: ϕf))        ∎
 where
  IH : subpred q x xs ＝ optimal-outcome (game (Xf x) (subpred q x) (ϕf x))
  IH = optimal-play-gives-optimal-outcome {Xf x} (ϕf x) (subpred q x) xs os

strategic-path-is-optimal-play
 : {Xt : 𝑻}
   (ϕt : 𝓚 Xt)
   (q : Path Xt → R)
   (σ : Strategy Xt)
 → is-in-sgpe ϕt q σ
 → is-optimal-play ϕt q (strategic-path σ)
strategic-path-is-optimal-play {[]} ⟨⟩ q ⟨⟩ ⟨⟩ = ⋆
strategic-path-is-optimal-play {X ∷ Xf} ϕt@(ϕ :: ϕf) q σ@(x₀ :: σf) ot@(o :: os)
 = I , IH x₀
 where
  IH : (x : X) → is-optimal-play (ϕf x) (subpred q x) (strategic-path (σf x))
  IH x = strategic-path-is-optimal-play {Xf x} (ϕf x) (subpred q x) (σf x) (os x)

  I : is-optimal-move q ϕ ϕf x₀
  I = optimal-outcome (game (X ∷ Xf) q (ϕ :: ϕf))                  ＝⟨refl⟩
      sequenceᴷ {X ∷ Xf} (ϕ :: ϕf) q                               ＝⟨refl⟩
      ϕ (λ x → sequenceᴷ (ϕf x) (subpred q x))                     ＝⟨refl⟩
      ϕ (λ x → optimal-outcome (game (Xf x) (subpred q x) (ϕf x))) ＝⟨ I₁ ⟩
      ϕ (λ x → subpred q x (strategic-path (σf x)))                ＝⟨ o ⁻¹ ⟩
      q (strategic-path σ)                                         ＝⟨refl⟩
      subpred q x₀ (strategic-path (σf x₀))                        ＝⟨ I₂ ⟩
      optimal-outcome (game (Xf x₀) (subpred q x₀) (ϕf x₀))        ∎
       where
        I₀ : (x : X)
           → optimal-outcome (game (Xf x) (subpred q x) (ϕf x))
           ＝ subpred q x (strategic-path (σf x))
        I₀ x = (optimal-play-gives-optimal-outcome
                 (ϕf x) (subpred q x) (strategic-path (σf x)) (IH x))⁻¹

        I₁ = ap ϕ (dfunext fe I₀)
        I₂ = optimal-play-gives-optimal-outcome
              (ϕf x₀) (subpred q x₀) (strategic-path (σf x₀)) (IH x₀)

\end{code}

We now proceed to compute the non-empty list of all optimal plays of a
game, under suitable assumptions on the game.

The algebras of the nonempty list monad 𝕃⁺ are the semigroups
(associative magmas). We work with the magma structure on R defined by
x · y = x. Concretely, this amounts to the following construction.

\begin{code}

𝓐 : Algebra 𝕃⁺ R
𝓐 = record {
     structure-map = head⁺ ;
     aunit = u ;
     aassoc = a
    }
 where
  u : head⁺ ∘ η 𝕃⁺ ∼ id
  u r = refl

  a : head⁺ ∘ ext 𝕃⁺ (η 𝕃⁺ ∘ head⁺) ∼ head⁺ ∘ ext 𝕃⁺ id
  a ((((r ∷ _) , _) ∷ _) , _) = refl

open T-definitions 𝕃⁺
open α-definitions 𝕃⁺ R 𝓐
open JT-definitions 𝕃⁺ R 𝓐 fe
open JK R

\end{code}

Ordinary selection functions are of type J X := (X → R) → X. Here we
work with JT defined as follows.

\begin{code}

JT-remark : JT {𝓤} ＝ λ X → (X → R) → List⁺ X
JT-remark = by-definition

\end{code}

Every algebra α of any monad T induces an extension operator α­extᵀ,
which for the case T = List⁺ with the algebra defined above is
characterized as follows.

\begin{code}

α-extᵀ-explicitly : {X : 𝓤 ̇ } (p : X → R) (t : List⁺ X)
                  → α-extᵀ p t ＝ p (head⁺ t)
α-extᵀ-explicitly p ((x ∷ _) :: _) = refl

\end{code}

We now construct a JT-selection function ε⁺ from an ordinary
J-selection function ε that attains a quantifier ϕ, for any listed
type X with at least one element.

Recall that we say that a type is listed⁺ if it has a distinguished
element and a list of all its elements (which will automatically
include the distinguished element).

\begin{code}

module _ (X : 𝓤 ̇ )
         (X-is-listed⁺@(x₀ , xs , μ) : listed⁺ X)
         (ϕ : (X → R) → R)
      where

 private
  A : (X → R) → X → 𝓦₀ ̇
  A p x = p x ＝ ϕ p

  δA : (p : X → R) (x : X) → is-decidable (A p x)
  δA p x = R-is-discrete (p x) (ϕ p)

 εᴸ :  (X → R) → List X
 εᴸ p = filter (A p) (δA p) xs

 εᴸ-property→ : (p : X → R) (x : X) → member x (εᴸ p) → p x ＝ ϕ p
 εᴸ-property→ p x = filter-member→ (A p) (δA p) x xs

 εᴸ-property← : (p : X → R) (x : X) → p x ＝ ϕ p → member x (εᴸ p)
 εᴸ-property← p x e = filter-member← (A p) (δA p) x xs e (μ x)

 module _ (ε : (X → R) → X)
          (ε-attains-ϕ : ε attains ϕ)
        where

  ε-member-of-εᴸ : (p : X → R) → member (ε p) (εᴸ p)
  ε-member-of-εᴸ p = filter-member← (A p) (δA p) (ε p) xs (ε-attains-ϕ p) (μ (ε p))

  εᴸ-is-non-empty : (p : X → R) → is-non-empty (εᴸ p)
  εᴸ-is-non-empty p = lists-with-members-are-non-empty (ε-member-of-εᴸ p)

  ε⁺ : JT X
  ε⁺ p = εᴸ p , εᴸ-is-non-empty p

\end{code}

We now extend this to trees of selection functions that attain
quantifiers.

\begin{code}

𝓙𝓣 : 𝑻 → 𝓤 ̇
𝓙𝓣 = structure JT

εt⁺ : (Xt : 𝑻)
    → structure listed⁺ Xt
    → (ϕt : 𝓚 Xt)
    → (εt : 𝓙 Xt)
    → εt Attains ϕt
    → 𝓙𝓣 Xt
εt⁺ [] ⟨⟩ ⟨⟩ ⟨⟩ ⟨⟩ = ⟨⟩
εt⁺ (X ∷ Xf) (l :: lf) (ϕ :: ϕf) (ε :: εf) (a :: af) =
 ε⁺ X l ϕ ε a :: (λ x → εt⁺ (Xf x) (lf x) (ϕf x) (εf x) (af x))

open List⁺-definitions

\end{code}

We now prove a couple of technical lemmas.

\begin{code}

module _ {X : 𝓤 ̇ } {Xf : X → 𝑻}
         (e⁺ : JT X)
         (d⁺ : (x : X) → JT (Path (Xf x)))
         (q : Path (X ∷ Xf)  → R)
       where

 private
  g : (x : X) → T (Path (Xf x))
  g x = d⁺ x (subpred q x)

  f : X → R
  f x = α-extᵀ (subpred q x) (g x)

  xt : T X
  xt = e⁺ f

  x : X
  x = head⁺ xt

  xs : Path (Xf x)
  xs = head⁺ (g x)

 head⁺-of-⊗ᴶᵀ : head⁺ ((e⁺ ⊗ᴶᵀ d⁺) q) ＝ x :: xs
 head⁺-of-⊗ᴶᵀ =
  head⁺ ((e⁺ ⊗ᴶᵀ d⁺) q)                                         ＝⟨ I ⟩
  head⁺ (xt ⊗ᴸ⁺ g)                                              ＝⟨ II ⟩
  head⁺ (concat⁺ (lmap⁺ (λ x → lmap⁺ (λ y → x :: y) (g x)) xt)) ＝⟨ III ⟩
  head⁺ (head⁺ (lmap⁺ (λ x → lmap⁺ (λ y → x :: y) (g x)) xt))   ＝⟨ IV ⟩
  head⁺ (lmap⁺ (head⁺ xt ::_) (g (head⁺ xt)))                   ＝⟨refl⟩
  head⁺ (lmap⁺ (x ::_) (g x))                                   ＝⟨ V ⟩
  x :: head⁺ (g x)                                              ＝⟨refl⟩
  x :: xs                                                       ∎
   where
    I   = ap head⁺ (⊗ᴶᵀ-in-terms-of-⊗ᵀ e⁺ d⁺ q fe)
    II  = ap head⁺ (⊗ᴸ⁺-explicitly fe (e⁺ f) g)
    III = head⁺-of-concat⁺ (lmap⁺ (λ x → lmap⁺ (λ y → x :: y) (g x)) xt)
    IV  = ap head⁺ (head⁺-of-lmap⁺ (λ x → lmap⁺ (λ y → x :: y) (g x)) xt)
    V   = head⁺-of-lmap⁺ (x ::_) (g x)

JT-in-terms-of-K : (Xt : 𝑻)
                   (ϕt : 𝓚 Xt)
                   (q : Path Xt → R)
                   (εt : 𝓙 Xt)
                   (at : εt Attains ϕt)
                   (lt : structure listed⁺ Xt)
                 → α-extᵀ q (path-sequence 𝕁𝕋 (εt⁺ Xt lt ϕt εt at) q)
                 ＝ path-sequence (𝕂 R) ϕt q
JT-in-terms-of-K [] ϕt q εt at lt = refl
JT-in-terms-of-K Xt@(X ∷ Xf) ϕt@(ϕ :: ϕf) q εt@(ε :: εf) at@(a :: af) lt@(l :: lf) = II
 where
  d⁺ : (x : X) → JT (Path (Xf x))
  d⁺ x = path-sequence 𝕁𝕋 (εt⁺ (Xf x) (lf x) (ϕf x) (εf x) (af x))

  f : (x : X) → List⁺ (Path (Xf x))
  f x = d⁺ x (subpred q x)

  p : X → R
  p x = α-extᵀ (subpred q x) (f x)

  IH : (x : X) → p x ＝ path-sequence (𝕂 R) (ϕf x) (subpred q x)
  IH x = JT-in-terms-of-K (Xf x) (ϕf x) (subpred q x) (εf x) (af x) (lf x)

  e⁺ : JT X
  e⁺ = ε⁺ X l ϕ ε a

  x : X
  x = head⁺ (e⁺ p)

  I : member x (ι (e⁺ p))
  I = head⁺-is-member (e⁺ p)

  II = α-extᵀ q ((e⁺ ⊗ᴶᵀ d⁺) q)                           ＝⟨ II₀ ⟩
       q (head⁺ ((e⁺ ⊗ᴶᵀ d⁺) q))                          ＝⟨ II₁ ⟩
       q (x :: head⁺ (f x))                               ＝⟨ II₂ ⟩
       p x                                                ＝⟨ II₃ ⟩
       ϕ p                                                ＝⟨ II₄ ⟩
       ϕ (λ x → path-sequence (𝕂 R) (ϕf x) (subpred q x)) ＝⟨refl⟩
       (ϕ ⊗[ 𝕂 R ] (λ x → path-sequence (𝕂 R) (ϕf x))) q  ∎
        where
         II₀ = α-extᵀ-explicitly q ((e⁺ ⊗[ 𝕁𝕋 ] d⁺) q)
         II₁ = ap q (head⁺-of-⊗ᴶᵀ e⁺ d⁺ q)
         II₂ = (α-extᵀ-explicitly (subpred q x) (f x))⁻¹
         II₃ = εᴸ-property→ X l ϕ p x I
         II₄ = ap ϕ (dfunext fe IH)

\end{code}

We now show that path-sequence 𝕁𝕋 computes the non-empty list of all
optimal plays.

\begin{code}

main-lemma→ : (Xt : 𝑻)
              (ϕt : 𝓚 Xt)
              (q : Path Xt → R)
              (εt : 𝓙 Xt)
              (at : εt Attains ϕt)
              (lt : structure listed⁺ Xt)
              (xs : Path Xt)
            → member xs (ι (path-sequence 𝕁𝕋 (εt⁺ Xt lt ϕt εt at) q))
            → is-optimal-play ϕt q xs
main-lemma→ [] ⟨⟩ q ⟨⟩ ⟨⟩ ⟨⟩ ⟨⟩ in-head = ⟨⟩
main-lemma→ Xt@(X ∷ Xf) ϕt@(ϕ :: ϕf) q εt@(ε :: εf) at@(a :: af)
            lt@(l :: lf) (x :: xs) m =
 head-is-optimal-move , tail-is-optimal-play
 where
  e⁺ : JT X
  e⁺ = ε⁺ X l ϕ ε a

  d⁺ : (x : X) → JT (Path (Xf x))
  d⁺ x = path-sequence 𝕁𝕋 (εt⁺ (Xf x) (lf x) (ϕf x) (εf x) (af x))

  t : List⁺ X
  t = τ e⁺ d⁺ q

  tf : (x : X) → T (Path (Xf x))
  tf x = d⁺ x (subpred q x)

  p : X → R
  p x = path-sequence (𝕂 R) (ϕf x) (subpred q x)

  p' : X → R
  p' x = α-extᵀ
          (subpred q x)
          (path-sequence 𝕁𝕋
            (εt⁺ (Xf x) (lf x) (ϕf x) (εf x) (af x))
            (subpred q x))

  I : path-sequence 𝕁𝕋 (εt⁺ Xt lt ϕt εt at) q ＝ t ⊗ᴸ⁺ tf
  I = ⊗ᴶᵀ-in-terms-of-⊗ᵀ e⁺ d⁺ q fe

  II : member (x :: xs) (ι (t ⊗ᴸ⁺ tf))
  II = transport (member (x :: xs)) (ap ι I) m

  III : member x (ι t)
  III = pr₁ (split-membership fe x xs t tf II)

  IV : member xs (ι (tf x))
  IV = pr₂ (split-membership fe x xs t tf II)

  V : p' ∼ p
  V x = JT-in-terms-of-K (Xf x) (ϕf x) (subpred q x) (εf x ) (af x) (lf x)

  VI : t ＝ e⁺ p
  VI = ap e⁺ (dfunext fe V)

  VII : member x (ι (e⁺ p))
  VII = transport (λ - → member x (ι -)) VI III

  head-is-optimal-move =
   ϕ p                                      ＝⟨ VIII ⟩
   p x                                      ＝⟨refl⟩
   path-sequence (𝕂 R) (ϕf x) (subpred q x) ∎
    where
     VIII = (εᴸ-property→ X l ϕ p x VII)⁻¹

  IH : member xs (ι (tf x))
     → is-optimal-play (ϕf x) (subpred q x) xs
  IH = main-lemma→ (Xf x) (ϕf x) (subpred q x) (εf x) (af x) (lf x) xs

  tail-is-optimal-play : is-optimal-play (ϕf x) (subpred q x) xs
  tail-is-optimal-play = IH IV

main-lemma← : (Xt : 𝑻)
              (ϕt : 𝓚 Xt)
              (q : Path Xt → R)
              (εt : 𝓙 Xt)
              (at : εt Attains ϕt)
              (lt : structure listed⁺ Xt)
              (xs : Path Xt)
            → is-optimal-play ϕt q xs
            → member xs (ι (path-sequence 𝕁𝕋 (εt⁺ Xt lt ϕt εt at) q))
main-lemma← [] ⟨⟩ q ⟨⟩ ⟨⟩ ⟨⟩ ⟨⟩ ⋆ = in-head
main-lemma← Xt@(X ∷ Xf) ϕt@(ϕ :: ϕf) q εt@(ε :: εf) at@(a :: af)
            lt@(l :: lf) (x :: xs) (om , op) = VI
 where
  p : X → R
  p x = path-sequence (𝕂 R) (ϕf x) (subpred q x)

  e⁺ : JT X
  e⁺ = ε⁺ X l ϕ ε a

  d⁺ : (x : X) → JT (Path (Xf x))
  d⁺ x = path-sequence 𝕁𝕋 (εt⁺ (Xf x) (lf x) (ϕf x) (εf x) (af x))

  t : List⁺ X
  t = τ e⁺ d⁺ q

  tf : (x : X) → T (Path (Xf x))
  tf x = d⁺ x (subpred q x)

  p' : X → R
  p' x = α-extᵀ (subpred q x) (tf x)

  IH : member xs (ι (tf x))
  IH = main-lemma← (Xf x) (ϕf x) (subpred q x) (εf x) (af x) (lf x) xs op

  I : p ＝ p'
  I = dfunext fe
       (λ x → (JT-in-terms-of-K (Xf x) (ϕf x) (subpred q x) (εf x) (af x) (lf x))⁻¹)

  II : p' x ＝ ϕ p'
  II = transport (λ - → - x ＝ ϕ -) I (om ⁻¹)

  III : member x (ι t)
  III = εᴸ-property← X l ϕ p' x II

  IV : member (x :: xs) (ι (t ⊗ᴸ⁺ tf))
  IV = join-membership fe x xs t tf (III , IH)

  V : ι (t ⊗ᴸ⁺ tf) ＝ ι (path-sequence 𝕁𝕋 (εt⁺ Xt lt ϕt εt at) q)
  V = (ap ι (⊗ᴶᵀ-in-terms-of-⊗ᵀ e⁺ d⁺ q fe))⁻¹

  VI : member (x :: xs) (ι (path-sequence 𝕁𝕋 (εt⁺ Xt lt ϕt εt at) q))
  VI = transport (member (x :: xs)) V IV

\end{code}

To conclude, we package the above with a game as a parameter, where
the types of moves are listed, and where we are given attaining
selection functions for the quantifiers.

\begin{code}

module _ (G@(game Xt q ϕt) : Game)
         (Xt-is-listed⁺ : structure listed⁺ Xt)
         (εt : 𝓙 Xt)
         (εt-Attains-ϕt : εt Attains ϕt)
       where

 optimal-plays : List⁺ (Path Xt)
 optimal-plays = path-sequence 𝕁𝕋 (εt⁺ Xt Xt-is-listed⁺ ϕt εt εt-Attains-ϕt) q

 Theorem→ : (xs : Path Xt) → member xs (ι optimal-plays) → is-optimal-play ϕt q xs
 Theorem→ = main-lemma→ Xt ϕt q εt εt-Attains-ϕt Xt-is-listed⁺

 Theorem← : (xs : Path Xt) → is-optimal-play ϕt q xs → member xs (ι optimal-plays)
 Theorem← = main-lemma← Xt ϕt q εt εt-Attains-ϕt Xt-is-listed⁺

\end{code}

This concludes what we wished to construct and prove.

Remark. The assumption Xt-is-listed⁺ implies that the type R of
outcomes has at least one element.

\begin{code}

 r₀ : R
 r₀ = q (head⁺ optimal-plays)

\end{code}

In a previous version of this file, we instead assumed r₀ : R, and we
worked with "listed" instead of "listed⁺", but the listings were
automatically non-empty.

Added 24th September 2025.

\begin{code}

quantifiers-over-empty-types-are-not-attainable
 : {X : 𝓤 ̇ }
 → is-empty X
 → (ϕ : K X)
 → ¬ is-attainable ϕ
quantifiers-over-empty-types-are-not-attainable e ϕ (ε , a)
 = e (ε (unique-from-𝟘 ∘ e))

\end{code}

Added 17th September. We calculate the subtree of the game tree whose
paths are precisely the optimal plays of the original game.

\begin{code}

prune : (Xt : 𝑻)
        (q : Path Xt → R)
        (ϕt : 𝓚 Xt)
      → 𝑻
prune [] q ⟨⟩ = []
prune (X ∷ Xf) q (ϕ :: ϕf) = (Σ x ꞉ X , is-optimal-move q ϕ ϕf x)
                           ∷ (λ (x , o) → prune (Xf x) (subpred q x) (ϕf x))
\end{code}

Notice that it may happen that the pruned tree is non-empty, but all
the nodes in the tree are empty types of moves. So we can't use the
pruned tree to decide whether or not there is an optimal
play. However, if we further assume that the types of moves in the
original tree are listed, we can decide this, and, moreover, get the
list of all optimal plays from the pruned tree *without* assuming that
the quantifiers are attainable (as we did above).

Each path in the pruned tree is a path in the original tree.

\begin{code}

inclusion : {Xt : 𝑻}
            (ϕt : 𝓚 Xt)
            (q : Path Xt → R)
          → Path (prune Xt q ϕt)
          → Path Xt
inclusion {[]} ⟨⟩ q ⟨⟩ = ⟨⟩
inclusion {X ∷ Xf} (ϕ :: ϕf) q ((x , _) :: xos)
 = x :: inclusion {Xf x} (ϕf x) (subpred q x) xos

\end{code}

The predicate q restricts to a predicate in the pruned tree.

\begin{code}

restriction : {Xt : 𝑻}
              (ϕt : 𝓚 Xt)
              (q : Path Xt → R)
            → Path (prune Xt q ϕt) → R
restriction ϕt q = q ∘ inclusion ϕt q

\end{code}

The restriction operation is not very useful, because it gives a
constant predicate with the optimal outcome as its value (see below).

The paths in the pruned tree are precisely the optimals plays in the
original tree.

\begin{code}

lemma→ : {Xt : 𝑻}
         (q : Path Xt → R)
         (ϕt : 𝓚 Xt)
       → (xos : Path (prune Xt q ϕt))
       → is-optimal-play ϕt q (inclusion ϕt q xos)
lemma→ {[]} q ⟨⟩ ⟨⟩ = ⟨⟩
lemma→ {X ∷ Xf} q (ϕ :: ϕf) ((x , o) :: xos)
 = o , lemma→ {Xf x} (subpred q x) (ϕf x) xos

lemma← : {Xt : 𝑻}
         (q : Path Xt → R)
         (ϕt : 𝓚 Xt)
         (xs : Path Xt)
       → is-optimal-play ϕt q xs
       → Σ xos ꞉ Path (prune Xt q ϕt) , inclusion ϕt q xos ＝ xs
lemma← {[]} q ⟨⟩ ⟨⟩ ⟨⟩ = ⟨⟩ , refl
lemma← {X ∷ Xf} q (ϕ :: ϕf) (x :: xs) (o :: os)
 = ((x , o) :: pr₁ IH) , ap (x ::_) (pr₂ IH)
 where
  IH : Σ xos ꞉ Path (prune (Xf x) (subpred q x) (ϕf x))
             , inclusion (ϕf x) (subpred q x) xos ＝ xs
  IH = lemma← {Xf x} (subpred q x) (ϕf x) xs os

\end{code}

This gives an alternative way to calculate the list of optimal plays,
which doesn't use selection functions.

Added 22nd October 2025.

We prove a remark stated above.

\begin{code}

restriction-is-constant
 : {Xt : 𝑻}
   (ϕt : 𝓚 Xt)
   (q : Path Xt → R)
   (xos : Path (prune Xt q ϕt))
 → restriction ϕt q xos ＝ optimal-outcome (game Xt q ϕt)
restriction-is-constant {Xt} ϕt q xos
 = optimal-play-gives-optimal-outcome ϕt q (inclusion ϕt q xos) (lemma→ q ϕt xos)

\end{code}

Added 8th October 2025.

\begin{code}

prune-is-listed : (Xt : 𝑻)
                  (q : Path Xt → R)
                  (ϕt : 𝓚 Xt)
                → structure listed Xt
                → structure listed (prune Xt q ϕt)
prune-is-listed [] q ϕt ⟨⟩ = ⟨⟩
prune-is-listed (X ∷ Xf) q (ϕ :: ϕf) (X-is-listed , Xf-is-listed) =
 X'-is-listed :: Xf'-is-listed
 where
  X' : 𝓤 ̇
  X' = Σ x ꞉ X , is-optimal-move q ϕ ϕf x

  X'-is-listed : listed X'
  X'-is-listed = detachable-subtype-of-listed-type-is-listed
                  (is-optimal-move q ϕ ϕf)
                  (being-optimal-move-is-decidable q ϕ ϕf)
                  (being-optimal-move-is-prop q ϕ ϕf)
                  X-is-listed

  Xf' : X' → 𝑻
  Xf' (x , o) = prune (Xf x) (subpred q x) (ϕf x)

  Xf'-is-listed : (x' : X') → structure listed (Xf' x')
  Xf'-is-listed (x , o) = prune-is-listed
                           (Xf x)
                           (subpred q x)
                           (ϕf x)
                           (Xf-is-listed x)

module _ (G@(game Xt q ϕt) : Game)
         (Xt-is-listed : structure listed Xt)
       where

 optimal-plays' : List (Path Xt)
 optimal-plays' = xss
  where
   Xt' : 𝑻
   Xt' = prune Xt q ϕt

   xss' : List (Path (prune Xt q ϕt))
   xss' = list-of-all-paths Xt' (prune-is-listed Xt q ϕt Xt-is-listed)

   xss : List (Path Xt)
   xss = lmap (inclusion ϕt q) xss'

\end{code}

Added 22nd October 2025. We now prove that optimal-plays' lists
precisely the optimal plays.

\begin{code}

 module _ (xs : Path Xt)
        where

  private
   xss' : List (Path (prune Xt q ϕt))
   xss' = list-of-all-paths
           (prune Xt q ϕt)
           (prune-is-listed Xt q ϕt Xt-is-listed)

  main-lemma'→ : member xs optimal-plays'
               → is-optimal-play ϕt q xs
  main-lemma'→ m = I σ
   where
    have-m : member xs (lmap (inclusion ϕt q) xss')
    have-m = m

    σ : Σ xos ꞉ Path (prune Xt q ϕt) , member xos xss'
                                     × (inclusion ϕt q xos ＝ xs)
    σ = member-of-map← (inclusion ϕt q) xs xss' m

    I : type-of σ → is-optimal-play ϕt q xs
    I (xos , _ , e) = transport (is-optimal-play ϕt q) e (lemma→ q ϕt xos)

  main-lemma'← : is-optimal-play ϕt q xs
               → member xs optimal-plays'
  main-lemma'← o = I σ
   where
    σ : Σ xos ꞉ Path (prune Xt q ϕt) , inclusion ϕt q xos ＝ xs
    σ = lemma← q ϕt xs o

    I : type-of σ → member xs optimal-plays'
    I (xos , e) = I₂
     where
      I₀ : member xos xss'
      I₀ = path-is-member-of-list-of-all-paths
            (prune Xt q ϕt)
            (prune-is-listed Xt q ϕt Xt-is-listed)
            xos

      I₁ : member (inclusion ϕt q xos) (lmap (inclusion ϕt q) xss')
      I₁ = member-of-map→ (inclusion ϕt q) xss' xos I₀

      I₂ : member xs (lmap (inclusion ϕt q) xss')
      I₂ = transport (λ - → member - (lmap (inclusion ϕt q) xss')) e I₁

\end{code}

Notice that this way of computing the optimal plays doesn't need the
assumption that the quantifiers are attainable.

In general, there are games where the quantifiers are not attainable,
so that the "optimal outcome" of a game still exists (the product of
the quantifiers), but there are no strategies which lead to the
optimal outcome, so that the list of optimal plays will be empty.
