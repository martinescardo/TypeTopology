Martin Escardo, Paulo Oliva, 27th November 2024 - 14th May 2025

We define optimal moves and optimal plays for sequential games. Then
using the JT monad, with T the monad List⁺ of non-empty lists, we
compute all optimal plays of a game, provided it has ordinary
selection functions.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (J)
open import UF.FunExt
open import UF.DiscreteAndSeparated

\end{code}

We work with a pointed discrete type R of outcomes.

\begin{code}

module Games.OptimalPlays
        (fe : Fun-Ext)
        (R  : Type)
        (r₀ : R)
        (R-is-discrete : is-discrete R)
       where

open import Games.FiniteHistoryDependent R
open import Games.TypeTrees
open import MLTT.List hiding ([_]) renaming (map to lmap)
open import MonadOnTypes.J-transf-variation
open import MonadOnTypes.JK
open import MonadOnTypes.K
open import MonadOnTypes.List
open import MonadOnTypes.Monad
open import MonadOnTypes.NonEmptyList
open import Notation.CanonicalMap
open import UF.Base

open K-definitions R

\end{code}

The following are the main two notions considered in this file.

\begin{code}

is-optimal-move : {X : Type} {Xf : X → 𝑻}
                  (q : (Σ x ꞉ X , Path (Xf x)) → R)
                  (ϕ : K X)
                  (ϕf : (x : X) → 𝓚 (Xf x))
                → X
                → Type
is-optimal-move {X} {Xf} q ϕ ϕf x =
 sequenceᴷ {X ∷ Xf} (ϕ :: ϕf) q ＝ sequenceᴷ {Xf x} (ϕf x) (subpred q x)

is-optimal-play : {Xt : 𝑻} → 𝓚 Xt → (Path Xt → R) → Path Xt → Type
is-optimal-play {[]}     ⟨⟩        q ⟨⟩ = 𝟙
is-optimal-play Xt@{X ∷ Xf} ϕt@(ϕ :: ϕf) q (x :: xs) =
   is-optimal-move {X} {Xf} q ϕ ϕf x
 × is-optimal-play {Xf x} (ϕf x) (subpred q x) xs

\end{code}


We now proceed to compute the non-empty list of all optimal plays of a
game, under suitable assumptions on the game.

An algebra of the nonempty list monad 𝕃⁺ is an associative magma. We
work with the magma structure on R defined by x · y = x. Concretely,
this amounts to the following construction.

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

JT-remark : JT ＝ λ X → (X → R) → List⁺ X
JT-remark = by-definition

\end{code}

Every algebra α of any monad T induces an extension operator α­extᵀ,
which for the case T = List⁺ with the algebra defined above is
characterized as follows.

\begin{code}

α-extᵀ-explicitly : {X : Type} (p : X → R) (t : List⁺ X)
                  → α-extᵀ p t ＝ p (head⁺ t)
α-extᵀ-explicitly p ((x ∷ _) :: _) = refl

\end{code}

We now construct a JT-selection function ε⁺ from an ordinary
J-selection function ε that attains a quantifier ϕ, for any listed
type X.

\begin{code}

module _ (X : Type)
         (X-is-listed@(xs , μ) : listed X)
         (ϕ : (X → R) → R)
         (ε : (X → R) → X)
         (ε-attains-ϕ : ε attains ϕ)
      where

 private
  x₀ : X
  x₀ = ε (λ _ → r₀)

 X-is-listed⁺ : listed⁺ X
 X-is-listed⁺ = x₀ , X-is-listed

\end{code}

The above is the only use of the distinguished point r₀ of R.

\begin{code}

 private
  A : (X → R) → X → Type
  A p x = p x ＝ ϕ p

  δA : (p : X → R) (x : X) → is-decidable (A p x)
  δA p x = R-is-discrete (p x) (ϕ p)

 εᴸ :  (X → R) → List X
 εᴸ p = filter (A p) (δA p) xs

 ε-member-of-εᴸ : (p : X → R) → member (ε p) (εᴸ p)
 ε-member-of-εᴸ p = filter-member← (A p) (δA p) (ε p) xs (ε-attains-ϕ p) (μ (ε p))

 εᴸ-is-non-empty : (p : X → R) → is-non-empty (εᴸ p)
 εᴸ-is-non-empty p = lists-with-members-are-non-empty (ε-member-of-εᴸ p)

 ε⁺ : JT X
 ε⁺ p = εᴸ p , εᴸ-is-non-empty p

 εᴸ-property→ : (p : X → R) (x : X) → member x (εᴸ p) → p x ＝ ϕ p
 εᴸ-property→ p x = filter-member→ (A p) (δA p) x xs

 εᴸ-property← : (p : X → R) (x : X) → p x ＝ ϕ p → member x (εᴸ p)
 εᴸ-property← p x e = filter-member← (A p) (δA p) x xs e (μ x)

\end{code}

We now extend this to trees of selection functions that attain
quantifiers.

\begin{code}

𝓙𝓣 : 𝑻 → Type
𝓙𝓣 = structure JT

εt⁺ : (Xt : 𝑻)
      (ϕt : 𝓚 Xt)
      (εt : 𝓙 Xt)
    → εt Attains ϕt
    → structure listed Xt
    → 𝓙𝓣 Xt
εt⁺ [] ϕt εt at lt = ⟨⟩
εt⁺ (X ∷ Xf) (ϕ :: ϕf) (ε :: εf) (a :: af) (l :: lf) =
 ε⁺ X l ϕ ε a :: (λ x → εt⁺ (Xf x) (ϕf x) (εf x) (af x) (lf x))

open List⁺-definitions

\end{code}

We now prove a couple of technical lemmas.

\begin{code}

module _ {X : Type} {Xf : X → 𝑻}
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
  head⁺ (lmap⁺ (head⁺ xt ::_) (g (head⁺ xt)))                   ＝⟨ refl ⟩
  head⁺ (lmap⁺ (x ::_) (g x))                                   ＝⟨ V ⟩
  x :: head⁺ (g x)                                              ＝⟨ refl ⟩
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
                   (lt : structure listed Xt)
                 → α-extᵀ q (path-sequence 𝕁𝕋 (εt⁺ Xt ϕt εt at lt) q)
                 ＝ path-sequence (𝕂 R) ϕt q
JT-in-terms-of-K [] ϕt q εt at lt = refl
JT-in-terms-of-K Xt@(X ∷ Xf) ϕt@(ϕ :: ϕf) q εt@(ε :: εf) at@(a :: af) lt@(l :: lf) = II
 where
  d⁺ : (x : X) → JT (Path (Xf x))
  d⁺ x = path-sequence 𝕁𝕋 (εt⁺ (Xf x) (ϕf x) (εf x) (af x) (lf x))

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
       ϕ (λ x → path-sequence (𝕂 R) (ϕf x) (subpred q x)) ＝⟨ refl ⟩
       (ϕ ⊗[ 𝕂 R ] (λ x → path-sequence (𝕂 R) (ϕf x))) q  ∎
        where
         II₀ = α-extᵀ-explicitly q ((e⁺ ⊗[ 𝕁𝕋 ] d⁺) q)
         II₁ = ap q (head⁺-of-⊗ᴶᵀ e⁺ d⁺ q)
         II₂ = (α-extᵀ-explicitly (subpred q x) (f x))⁻¹
         II₃ = εᴸ-property→ X l ϕ ε a p x I
         II₄ = ap ϕ (dfunext fe IH)

\end{code}

We now show that path-sequence 𝕁𝕋 computes the non-empty list of all
optimal plays.

\begin{code}

theorem→ : (Xt : 𝑻)
           (ϕt : 𝓚 Xt)
           (q : Path Xt → R)
           (εt : 𝓙 Xt)
           (at : εt Attains ϕt)
           (lt : structure listed Xt)
           (xs : Path Xt)
         → member xs (ι (path-sequence 𝕁𝕋 (εt⁺ Xt ϕt εt at lt) q))
         → is-optimal-play ϕt q xs
theorem→ [] ⟨⟩ q ⟨⟩ ⟨⟩ ⟨⟩ ⟨⟩ in-head = ⟨⟩
theorem→ Xt@(X ∷ Xf) ϕt@(ϕ :: ϕf) q εt@(ε :: εf) at@(a :: af) lt@(l :: lf) (x :: xs) m =
 head-is-optimal-move , tail-is-optimal-play
 where
  e⁺ : JT X
  e⁺ = ε⁺ X l ϕ ε a

  d⁺ : (x : X) → JT (Path (Xf x))
  d⁺ x = path-sequence 𝕁𝕋 (εt⁺ (Xf x) (ϕf x) (εf x) (af x) (lf x))

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
            (εt⁺ (Xf x) (ϕf x) (εf x) (af x) (lf x))
            (subpred q x))

  I : path-sequence 𝕁𝕋 (εt⁺ Xt ϕt εt at lt) q ＝ t ⊗ᴸ⁺ tf
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
   p x                                      ＝⟨ refl ⟩
   path-sequence (𝕂 R) (ϕf x) (subpred q x) ∎
    where
     VIII = (εᴸ-property→ X l ϕ ε a p x VII)⁻¹

  IH : member xs (ι (tf x))
     → is-optimal-play (ϕf x) (subpred q x) xs
  IH = theorem→ (Xf x) (ϕf x) (subpred q x) (εf x) (af x) (lf x) xs

  tail-is-optimal-play : is-optimal-play (ϕf x) (subpred q x) xs
  tail-is-optimal-play = IH IV

theorem← : (Xt : 𝑻)
           (ϕt : 𝓚 Xt)
           (q : Path Xt → R)
           (εt : 𝓙 Xt)
           (at : εt Attains ϕt)
           (lt : structure listed Xt)
           (xs : Path Xt)
         → is-optimal-play ϕt q xs
         → member xs (ι (path-sequence 𝕁𝕋 (εt⁺ Xt ϕt εt at lt) q))
theorem← [] ⟨⟩ q ⟨⟩ ⟨⟩ ⟨⟩ ⟨⟩ ⋆ = in-head
theorem← Xt@(X ∷ Xf) ϕt@(ϕ :: ϕf) q εt@(ε :: εf) at@(a :: af)
       lt@(l :: lf) (x :: xs) (om , op) = VI
 where
  p : X → R
  p x = path-sequence (𝕂 R) (ϕf x) (subpred q x)

  e⁺ : JT X
  e⁺ = ε⁺ X l ϕ ε a

  d⁺ : (x : X) → JT (Path (Xf x))
  d⁺ x = path-sequence 𝕁𝕋 (εt⁺ (Xf x) (ϕf x) (εf x) (af x) (lf x))

  t : List⁺ X
  t = τ e⁺ d⁺ q

  tf : (x : X) → T (Path (Xf x))
  tf x = d⁺ x (subpred q x)

  p' : X → R
  p' x = α-extᵀ (subpred q x) (tf x)

  IH : member xs (ι (tf x))
  IH = theorem← (Xf x) (ϕf x) (subpred q x) (εf x) (af x) (lf x) xs op

  I : p ＝ p'
  I = dfunext fe
       (λ x → (JT-in-terms-of-K (Xf x) (ϕf x) (subpred q x) (εf x) (af x) (lf x))⁻¹)

  II : p' x ＝ ϕ p'
  II = transport (λ - → - x ＝ ϕ -) I (om ⁻¹)

  III : member x (ι t)
  III = εᴸ-property← X l ϕ ε a p' x II

  IV : member (x :: xs) (ι (t ⊗ᴸ⁺ tf))
  IV = join-membership fe x xs t tf (III , IH)

  V : ι (t ⊗ᴸ⁺ tf) ＝ ι (path-sequence 𝕁𝕋 (εt⁺ Xt ϕt εt at lt) q)
  V = (ap ι (⊗ᴶᵀ-in-terms-of-⊗ᵀ e⁺ d⁺ q fe))⁻¹

  VI : member (x :: xs) (ι (path-sequence 𝕁𝕋 (εt⁺ Xt ϕt εt at lt) q))
  VI = transport (member (x :: xs)) V IV

\end{code}

To conclude, we package the above with a game as a parameter, where
the types of moves are listed, and where we are given attaining
selection functions for the quantifiers.

\begin{code}

module _ (G@(game Xt q ϕt) : Game)
         (Xt-is-listed : structure listed Xt)
         (εt : 𝓙 Xt)
         (εt-Attains-ϕt : εt Attains ϕt)
       where

 optimal-plays : List⁺ (Path Xt)
 optimal-plays = path-sequence 𝕁𝕋 (εt⁺ Xt ϕt εt εt-Attains-ϕt Xt-is-listed) q

 Theorem→ : (xs : Path Xt) → member xs (ι optimal-plays) → is-optimal-play ϕt q xs
 Theorem→ = theorem→ Xt ϕt q εt εt-Attains-ϕt Xt-is-listed

 Theorem← : (xs : Path Xt) → is-optimal-play ϕt q xs → member xs (ι optimal-plays)
 Theorem← = theorem← Xt ϕt q εt εt-Attains-ϕt Xt-is-listed

\end{code}
