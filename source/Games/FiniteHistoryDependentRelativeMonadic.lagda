Martin Escardo, Paulo Oliva, mid 2024.

Remark added 11th June 2025. This file is experimental. In particular,
we are not sure our use of the algebra is modelling the intented
notions. It may be that different players need different algebras. For
example, if we are working with the powerset monad, whose algebras are
the sup-lattices, and some players play argmax and some players play
argmin, then it is plausible that the argmax players need an
inf-algebra, whereas the argim players need a sup-algebra. Another
potential issue is the notion of attainability for multi-valued
selection functions and quantifiers.

Warning. This module is a mess. We plan to clean it up soon. At the
moment the proofs are in "blackboard" style (improvised proofs that
work) rather than "article" style (proofs written in a more
presentable way).

This generalizes (but also uses) the file GamesExperimental2.FiniteHistoryDependent
with a monad parameter 𝓣. When 𝓣 is the identity monad 𝕀𝕕, the
original development is obtained. We apply the selection-monad
transformer 𝕁-transf to 𝓣. Notice, however, that the definition of
game is the same. See [1] for background.

The main examples of 𝓣 we have in mind are the powerset monad (for the
Herbrand Functional Interpretation [2]), probability distribution
monads (for mixed strategies) and the reader monad (for alpha-beta
pruning in the file GamesExperimental2.alpha-beta).

[1] M. Escardo and P. Oliva.
    Higher-order Games with Dependent Types (2023)
    https://doi.org/10.1016/j.tcs.2023.114111
    Available in TypeTopology at GamesExperimental2.FiniteHistoryDependent.

[2] M. Escardo and P. Oliva.
    The Herbrand functional interpretation of the double negation shift (2017)
    https://doi.org/10.1017/jsl.2017.8
    (Not available in TypeTopology at the time of writing (October 2023).)

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MonadOnTypes.K
open import RelativeMonadOnStructuredTypes.OneSigmaStructure
open import RelativeMonadOnStructuredTypes.Definition
open import MLTT.Spartan hiding (J)
open import UF.FunExt

\end{code}

In our of our main examples, ρ will be "finite linear order structure".

\begin{code}

module Games.FiniteHistoryDependentRelativeMonadic
        (fe : Fun-Ext)
        {{ρ : 𝟙-Σ-structure}}
        {ℓ : Universe → Universe}
        (𝕋 : Relative-Monad {ℓ})
        {𝓤 𝓦₀ : Universe}
        (𝓡 : let open 𝟙-Σ-structure ρ in
              𝕊 𝓦₀)
        (𝓐 : let open 𝟙-Σ-structure ρ in
              Relative-Algebra 𝕋 ⟨ 𝓡 ⟩)
       where

open 𝟙-Σ-structure ρ

open import Games.TypeTrees {𝓤}

private
 R = ⟨ 𝓡 ⟩

\end{code}

Question. Why do we need the following import?

\begin{code}

open import Games.FiniteHistoryDependent {𝓤} {𝓦₀} R
     using (𝓚 ; Game ; game ; sequenceᴷ ; optimal-outcome)

open Game

open import RelativeMonadOnStructuredTypes.J-transf
open K-definitions R
open relative-T-definitions 𝕋
open relative-α-definitions 𝕋 𝓡 𝓐
open relative-JT-definitions 𝕋 𝓡 𝓐 fe

\end{code}

We need a variation of `structure` which equips the nodes of a
structured game tree with relative monadic structure.

Example 1. S X may be "Σ n ꞉ ℕ , Fin n ≃ X". We say "X is equipped
with a finite linear order". Now 𝕋 may be the monad of lists without
repetitions (which is possible because a finite linear order gives
decidable equality). Then `st : structure S (Xt G)` equips the types
of moves in the game tree with finite linear orders. In turn,
`structure' JT (Xt G) st` gives a tree of T-selection functions for
the types of moves at the nodes. (Notice that 𝕋 is the "free graphic
monoid".)

Example 2. Same S as the previous example, but with 𝕋 the monad of
sorted lists without repetitions. One possible implementation of 𝕋 is
with T X = X → 𝟚. This will be efficient if the sets of moves as small
enough. (It would be nice to test these two examples in practice.)

The types of trees with JT and KT structure.

\begin{code}

structure' : (𝕊 𝓤 → 𝓥 ̇ ) → (Xt : 𝑻) → structure S Xt → 𝓤 ⊔ 𝓥 ̇
structure' F [] ⟨⟩ = 𝟙
structure' F (X ∷ Xf) (s :: sf)
 = F (X , s) × ((x : X) → structure' F (Xf x) (sf x))

𝓙𝓣 : (Xt : 𝑻) → structure S Xt → ℓ 𝓦₀ ⊔ ℓ 𝓤 ⊔ 𝓤 ̇
𝓙𝓣 = structure' JT

𝓚𝓣 : (Xt : 𝑻) → structure S Xt → ℓ 𝓦₀ ⊔ 𝓦₀ ⊔ 𝓤 ̇
𝓚𝓣 = structure' KT

\end{code}

The original definition of Path Xt gives the type of all full paths
(of moves) in the tree Xt. The following does the same, but
additionally adds the structure S to this collection, so that, in
Example 1, this gives all full plays of the game tree, with a finite
linear order on the full plays. This is because we want to be able to
apply JT to the type of plays.

\begin{code}

Path-structure : {Xt : 𝑻} → structure S Xt → S (Path Xt)
Path-structure {[]}     ⟨⟩        = 𝟙-is-S
Path-structure {X ∷ Xf} (s :: sf) =
 Σ-is-S (X , s) (λ x → Path (Xf x) , Path-structure {Xf x} (sf x))

Pathₛ : (Xt : 𝑻) → structure S Xt → 𝕊 𝓤
Pathₛ Xt st = Path Xt , Path-structure st

\end{code}

The following enriches a game with structure on the sets of moves,
e.g. finite linear orders.

\begin{code}

module _ {ℓ : Universe → Universe} (𝕄 : Relative-Monad {ℓ}) where

 M : 𝕊 𝓤 → ℓ 𝓤 ̇
 M = functor 𝕄

 path-sequenceₛ : {Xt : 𝑻} (st : structure S Xt)
                → structure' M Xt st
                → M (Pathₛ Xt st)
 path-sequenceₛ {[]} ⟨⟩ ⟨⟩ = η 𝕄 ⟨⟩
 path-sequenceₛ {X ∷ Xf} (s :: sf) (t :: tf) =
  t ⊗ᵣ[ 𝕄 ] (λ x → path-sequenceₛ {Xf x} (sf x) (tf x))

sequenceᴶᵀ : {Xt : 𝑻} (st : structure S Xt) → 𝓙𝓣 Xt st → JT (Pathₛ Xt st)
sequenceᴶᵀ = path-sequenceₛ 𝕁𝕋

T-Strategy : (Xt : 𝑻) (st : structure S Xt)  → ℓ 𝓤 ⊔ 𝓤 ̇
T-Strategy = structure' T

T-strategic-path : {Xt : 𝑻} (st : structure S Xt)
                 → T-Strategy Xt st
                 → T (Pathₛ Xt st)
T-strategic-path = path-sequenceₛ 𝕋

is-in-T-equilibrium : {X : 𝓤 ̇ } {Xf : X → 𝑻}
                      (st@(s , sf) : structure S (X ∷ Xf))
                      (q : (Σ x ꞉ X , Path (Xf x)) → R)
                      (ϕ : K X)
                    → T-Strategy (X ∷ Xf) st
                    → 𝓦₀ ̇
is-in-T-equilibrium {X} {Xf} st@(s , sf) q ϕ σt@(σ :: σf)  =
    extᴬ q (T-strategic-path {X ∷ Xf} st σt)
 ＝ ϕ (λ x → extᴬ (subpred q x) (T-strategic-path (sf x) (σf x)))

is-in-T-sgpe' : {Xt : 𝑻}
                (st : structure S Xt)
              → 𝓚 Xt
              → (Path Xt → R)
              → T-Strategy Xt st
              → 𝓤 ⊔ 𝓦₀ ̇
is-in-T-sgpe' {[]}     st          ⟨⟩        q ⟨⟩           = 𝟙
is-in-T-sgpe' {X ∷ Xf} st@(s , sf) (ϕ :: ϕf) q σt@(σ :: σf) =
    is-in-T-equilibrium st q ϕ σt
  × ((x : X) → is-in-T-sgpe' {Xf x} (sf x) (ϕf x) (subpred q x) (σf x))

is-in-T-sgpe : (G : Game) (st : structure S (game-tree G))
             → T-Strategy (game-tree G) st
             → 𝓤 ⊔ 𝓦₀ ̇
is-in-T-sgpe (game Xt q ϕt) st = is-in-T-sgpe' {Xt} st ϕt q

\end{code}

TODO. This q has a type different from the q in
is-in-T-equilibrium. Better to use a different notation to make this
clear explicitly.

The main lemma is that the optimal outcome is the same thing as the
application of the outcome function to the path induced by a strategy
in perfect subgame equilibrium.

\begin{code}

T-sgpe-lemma : (Xt : 𝑻)
               (ϕt : 𝓚 Xt)
               (st : structure S Xt)
               (q : Path Xt → R)
               (σt : T-Strategy Xt st)
             → is-in-T-sgpe' st ϕt q σt
             → extᴬ q (T-strategic-path st σt) ＝ sequenceᴷ ϕt q
T-sgpe-lemma [] ⟨⟩ ⟨⟩ q ⟨⟩ ⟨⟩ =
 extᴬ q (T-strategic-path ⟨⟩ ⟨⟩) ＝⟨refl⟩
 aext 𝓐 q (ηᵀ ⟨⟩)                ＝⟨ unitᴬ q ⟨⟩ ⟩
 q ⟨⟩                            ＝⟨refl⟩
 sequenceᴷ ⟨⟩ q                  ∎
T-sgpe-lemma (X ∷ Xf) ϕt@(ϕ :: ϕf) st@(s :: sf) q σt@(σ :: σf) (h :: t) =
 extᴬ q (T-strategic-path st σt)                               ＝⟨ h ⟩
 ϕ (λ x → extᴬ (subpred q x) (T-strategic-path (sf x) (σf x))) ＝⟨ I ⟩
 ϕ (λ x → sequenceᴷ (ϕf x) (subpred q x))                      ＝⟨refl⟩
 sequenceᴷ ϕt q                                                ∎
 where
  IH : (x : X)
     → extᴬ (subpred q x) (T-strategic-path (sf x) (σf x))
       ＝ sequenceᴷ (ϕf x) (subpred q x)
  IH x = T-sgpe-lemma (Xf x) (ϕf x) (sf x) (subpred q x) (σf x) (t x)

  I = ap ϕ (dfunext fe IH)

\end{code}

This can be reformulated as follows in terms of the type of games:

\begin{code}

T-equilibrium-theorem
 : (G : Game)
   (st : structure S (game-tree G))
   (σt : T-Strategy (game-tree G) st)
 → is-in-T-sgpe G st σt
 → extᴬ (payoff-function G) (T-strategic-path st σt) ＝ optimal-outcome G
T-equilibrium-theorem (game Xt q ϕt) st = T-sgpe-lemma Xt ϕt st q

\end{code}

We now show how to use selection functions to compute a sgpe strategy.

\begin{code}

T-selection-strategy : {Xt : 𝑻} (st : structure S Xt)
                     → 𝓙𝓣 Xt st
                     → (Path Xt → R)
                     → T-Strategy Xt st
T-selection-strategy {[]}     ⟨⟩        ⟨⟩           q = ⟨⟩
T-selection-strategy Xt@{X ∷ Xf} st@(s :: sf) εt@(ε :: εf) q = σ :: σf
 where
  t : T (Pathₛ Xt st)
  t = sequenceᴶᵀ st εt (ηᵀ ∘ q)

  σ : T (X , s)
  σ = mapᵀ path-head t

  σf : (x : X) → T-Strategy (Xf x) (sf x)
  σf x = T-selection-strategy {Xf x} (sf x) (εf x) (subpred q x)

\end{code}

TODO. Explain the intuition of the condition extᵀ-const and
equivalents.

\begin{code}

mapᵀ-path-head-lemma' : {X : 𝓤 ̇ }
                        {Xf : X → 𝑻}
                        (s : S X)
                        (sf : (x : X) → structure S (Xf x))
                        (a : T (X , s))
                        (b : (x : X)
                      → T (Pathₛ (Xf x) (sf x)))
                      → mapᵀ path-head (a ⊗ᵀ b)
                      ＝ extᵀ (λ x → extᵀ (λ _ → ηᵀ x) (b x)) a
mapᵀ-path-head-lemma' {X} {Xf} s sf a b =
  mapᵀ path-head (a ⊗ᵀ b)                                  ＝⟨refl⟩
  extᵀ (ηᵀ ∘ path-head) (a ⊗ᵀ b)                           ＝⟨refl⟩
  extᵀ g (a ⊗ᵀ b)                                          ＝⟨refl⟩
  extᵀ g (extᵀ (λ x → mapᵀ (x ::_) (b x)) a)               ＝⟨refl⟩
  extᵀ g (extᵀ (λ x → extᵀ (ηᵀ ∘ (x ::_)) (b x)) a)        ＝⟨ ⦅1⦆ ⟩
  extᵀ (extᵀ g ∘ (λ x → extᵀ (ηᵀ ∘ (x ::_)) (b x))) a      ＝⟨refl⟩
  extᵀ (extᵀ g ∘ (λ x → extᵀ (f x) (b x))) a               ＝⟨refl⟩
  extᵀ (λ x → extᵀ g (extᵀ (f x) (b x))) a                 ＝⟨refl⟩
  extᵀ (λ x → (extᵀ g ∘ extᵀ (f x)) (b x)) a               ＝⟨ ⦅2⦆ ⟩
  extᵀ (λ x → extᵀ (extᵀ g ∘ (f x)) (b x)) a               ＝⟨refl⟩
  extᵀ (λ x → extᵀ (λ xs → extᵀ g (ηᵀ (x :: xs))) (b x)) a ＝⟨ ⦅3⦆ ⟩
  extᵀ (λ x → extᵀ (λ xs → g (x :: xs)) (b x)) a           ＝⟨refl⟩
  extᵀ (λ x → extᵀ (λ _ → ηᵀ x) (b x)) a                   ∎
 where
  g : Path (X ∷ Xf) → T (X , s)
  g = ηᵀ ∘ path-head

  f : (x : X) → Path (Xf x) → T (Pathₛ (X ∷ Xf) (s :: sf))
  f x = ηᵀ ∘ (x ::_)

  I : ∀ x → (extᵀ g ∘ extᵀ (f x)) (b x) ＝ extᵀ (extᵀ g ∘ (f x)) (b x)
  I x = (assocᵀ g (f x) (b x))⁻¹

  II : (x : X) (xs : Path (Xf x)) → extᵀ g (ηᵀ (x :: xs)) ＝ g (x :: xs)
  II x xs = unitᵀ g (x :: xs)

  ⦅1⦆ = (assocᵀ g (λ x → extᵀ (f x) (b x)) a)⁻¹
  ⦅2⦆ = ap (λ - → extᵀ - a) (dfunext fe I)
  ⦅3⦆ = ap (λ - →  extᵀ (λ x → extᵀ (- x) (b x)) a)
           (dfunext fe (λ x → dfunext fe (II x)))

mapᵀ-path-head-lemma : {X : 𝓤 ̇ }
                       {Xf : X → 𝑻}
                       (s : S X)
                       (sf : (x : X) → structure S (Xf x))
                       (a : T (X , s))
                       (b : (x : X)
                     → T (Pathₛ (Xf x) (sf x)))
                     → ext-const 𝕋
                     → mapᵀ path-head (a ⊗ᵀ b) ＝ a
mapᵀ-path-head-lemma {X} {Xf} s sf a b ext-const =
  mapᵀ path-head (a ⊗ᵀ b)                                  ＝⟨ ⦅1⦆ ⟩
  extᵀ (λ x → extᵀ (λ _ → ηᵀ x) (b x)) a                   ＝⟨ ⦅2⦆ ⟩
  extᵀ ηᵀ a                                                ＝⟨ extᵀ-η a ⟩
  a                                                        ∎
 where
 ⦅1⦆ = mapᵀ-path-head-lemma' s sf a b
 ⦅2⦆ = ap (λ - → extᵀ - a) (dfunext fe (λ x → ext-const (ηᵀ x) (b x)))

\end{code}

We also need the following technical lemma, which expresses the tensor
_⊗ᴶᵀ_ in terms of the tensor _⊗ᵀ_ as in Lemma 2.3 of reference [2]
above.

\begin{code}
module _ {𝓧  : 𝕊 𝓤}
         {𝓥 : Universe}
         {𝓨  : ⟨ 𝓧 ⟩ → 𝕊 𝓥}
         (ε  : JT 𝓧)
         (δ  : (x : ⟨ 𝓧 ⟩) → JT (𝓨 x))
 where

 private
  ν : (⟨ Σₛ x ꞉ 𝓧 , 𝓨 x ⟩ → T 𝓡) → (x : ⟨ 𝓧 ⟩) → T (𝓨 x)
  ν q x = δ x (λ y → q (x , y))

  τ : (⟨ Σₛ x ꞉ 𝓧 , 𝓨 x ⟩ → T 𝓡) → T 𝓧
  τ q = ε (λ x → extᵀ (λ y → q (x , y)) (ν q x))

 ⊗ᴶᵀ-in-terms-of-⊗ᵀ : (q : ⟨ Σₛ x ꞉ 𝓧 , 𝓨 x ⟩ → T 𝓡)
                    → (ε ⊗ᴶᵀ δ) q ＝ τ q ⊗ᵀ ν q
 ⊗ᴶᵀ-in-terms-of-⊗ᵀ q =
    (ε ⊗ᴶᵀ δ) q                                          ＝⟨refl⟩
    extᴶᵀ (λ x → extᴶᵀ (λ y _ → ηᵀ (x , y)) (δ x)) ε q   ＝⟨ ⦅1⦆ ⟩
    extᴶᵀ Θ ε q                                          ＝⟨refl⟩
    extᵀ (λ x → Θ x q) (ε (λ x → extᵀ q (Θ x q)))        ＝⟨ ⦅2⦆ ⟩
    extᵀ (λ x → Θ x q) (τ q)                             ＝⟨refl⟩
    τ q ⊗ᵀ ν q                                           ∎
     where
      Θ : ⟨ 𝓧 ⟩ → JT (Σₛ x ꞉ 𝓧 , 𝓨 x)
      Θ x r = extᵀ (λ y → ηᵀ (x , y)) (ν r x)

      I : (λ x → extᴶᵀ (λ y _ → ηᵀ (x , y)) (δ x)) ＝ Θ
      I = dfunext fe (λ x →
          dfunext fe (λ r → ap (λ - → extᵀ
                                       (λ y → ηᵀ (x , y))
                                       (δ x (λ y → - (x , y))))
                               (dfunext fe (unitᵀ r))))

      ⦅1⦆ = ap (λ - → extᴶᵀ - ε q) I

      II : ∀ x → extᵀ q ∘ extᵀ (λ y → ηᵀ (x , y)) ＝ extᵀ (λ y → q (x , y))
      II x = extᵀ q ∘ extᵀ (λ y → ηᵀ (x , y))               ＝⟨ ⦅i⦆ ⟩
             (λ x' → extᵀ (extᵀ q ∘ (λ y → ηᵀ (x , y))) x') ＝⟨refl⟩
             extᵀ (λ y → ((extᵀ q) ∘ ηᵀ) (x , y))           ＝⟨ ⦅ii⦆ ⟩
             extᵀ (λ y → q (x , y))                         ∎
       where
        ⦅i⦆  = dfunext fe (λ x' → (assocᵀ q (λ y → ηᵀ (x , y)) x')⁻¹)
        ⦅ii⦆ = ap extᵀ (dfunext fe (λ y → unitᵀ q (x , y)))

      III : ε (λ x → extᵀ q (extᵀ (λ y → ηᵀ (x , y)) (ν q x))) ＝ τ q
      III = ap ε (dfunext fe (λ x → ap (λ - → - (ν q x)) (II x)))

      ⦅2⦆ = ap (extᵀ (λ x → Θ x q)) III

\end{code}

The following is the main lemma of this file.

Given a selection tree εt over Xt and an outcome function q, we can
either sequence εt and apply it to q to obtain a monadic path on Xt,
or we can first use εt to calculate a strategy on Xt and derive its
monadic strategic path. The lemma says that these are the same path.

\begin{code}

T-main-lemma
 : ext-const 𝕋
 → {Xt : 𝑻}
   (st : structure S Xt)
   (εt : 𝓙𝓣 Xt st)
   (q : Path Xt → R)
 → sequenceᴶᵀ st εt (ηᵀ ∘ q) ＝ T-strategic-path st
                                 (T-selection-strategy st εt q)
T-main-lemma ext-const {[]}     ⟨⟩           ⟨⟩           q = refl
T-main-lemma ext-const {X ∷ Xf} st@(s :: sf) εt@(ε :: εf) q = γ
 where
  δ : (x : X) → JT (Pathₛ (Xf x) (sf x))
  δ x = sequenceᴶᵀ {Xf x} (sf x) (εf x)

  q' : (x : X) → Path (Xf x) → T 𝓡
  q' x = ηᵀ ∘ subpred q x

  σf : (x : X) → T-Strategy (Xf x) (sf x)
  σf x = T-selection-strategy {Xf x} (sf x) (εf x) (subpred q x)

  b c : (x : X) → T (Pathₛ (Xf x) (sf x))
  b x = δ x (q' x)
  c x = T-strategic-path (sf x) (σf x)

  IH : b ∼ c
  IH x = T-main-lemma ext-const (sf x) (εf x) (subpred q x)

  σ : T (X , s)
  σ = mapᵀ path-head (sequenceᴶᵀ st εt (ηᵀ ∘ q))

  I = ε (λ x → extᵀ (q' x) (c x))                       ＝⟨ ⦅1⦆ ⟩
      mapᵀ path-head (ε (λ x → extᵀ (q' x) (c x)) ⊗ᵀ c) ＝⟨ ⦅2⦆ ⟩
      mapᵀ path-head (ε (λ x → extᵀ (q' x) (b x)) ⊗ᵀ b) ＝⟨ ⦅3⦆ ⟩
      mapᵀ path-head ((ε ⊗ᴶᵀ δ) (ηᵀ ∘ q))               ＝⟨refl⟩
      mapᵀ path-head (sequenceᴶᵀ st εt (ηᵀ ∘ q))        ＝⟨refl⟩
      σ                                                 ∎
   where
    ⦅1⦆ = (mapᵀ-path-head-lemma s sf (ε (λ x → extᵀ (q' x) (c x))) c ext-const)⁻¹
    ⦅2⦆ = ap (λ - → mapᵀ path-head (ε (λ x → extᵀ (q' x) (- x)) ⊗ᵀ -))
              (dfunext fe (λ x → (IH x)⁻¹))
    ⦅3⦆ = (ap (mapᵀ path-head) (⊗ᴶᵀ-in-terms-of-⊗ᵀ ε δ (ηᵀ ∘ q)))⁻¹

  γ : sequenceᴶᵀ st εt (ηᵀ ∘ q)
    ＝ T-strategic-path st (T-selection-strategy st εt q)
  γ = sequenceᴶᵀ st εt (ηᵀ ∘ q)                          ＝⟨refl⟩
      (ε ⊗ᴶᵀ δ) (ηᵀ ∘ q)                                 ＝⟨ ⦅1⦆ ⟩
      ε (λ x → extᵀ (q' x) (b x)) ⊗ᵀ b                   ＝⟨ ⦅2⦆ ⟩
      (ε (λ x → extᵀ (q' x) (c x)) ⊗ᵀ c)                 ＝⟨ ⦅3⦆ ⟩
      σ ⊗ᵀ c                                             ＝⟨refl⟩
      σ ⊗ᵀ (λ x → T-strategic-path {Xf x} (sf x) (σf x)) ＝⟨refl⟩
      T-strategic-path st (σ :: σf)                      ＝⟨refl⟩
      T-strategic-path st (T-selection-strategy st εt q) ∎
   where
    ⦅1⦆ = ⊗ᴶᵀ-in-terms-of-⊗ᵀ ε δ (ηᵀ ∘ q)
    ⦅2⦆ = ap (λ - → ε (λ x → extᵀ (q' x) (- x)) ⊗ᵀ -) (dfunext fe IH)
    ⦅3⦆ = ap (_⊗ᵀ c) I

[_]_Attainsᴬ_ : {Xt : 𝑻}
                (st : structure S Xt)
              → 𝓙𝓣 Xt st
              → 𝓚 Xt
              → ℓ 𝓦₀ ⊔ 𝓤 ⊔ 𝓦₀ ̇
[_]_Attainsᴬ_ {[]}     ⟨⟩        ⟨⟩        ⟨⟩        = 𝟙
[_]_Attainsᴬ_ {X ∷ Xf} (s :: sf) (ε :: εf) (ϕ :: ϕf) =
 (ε attainsᴬ ϕ) × ((x : X) → [ sf x ] (εf x) Attainsᴬ (ϕf x))

T-selection-strategy-lemma
 : ext-const 𝕋
 → {Xt : 𝑻}
   (st : structure S Xt)
   (εt : 𝓙𝓣 Xt st)
   (ϕt : 𝓚 Xt)
   (q : Path Xt → R)
 → [ st ] εt Attainsᴬ ϕt
 → is-in-T-sgpe' st ϕt q (T-selection-strategy st εt q)
T-selection-strategy-lemma
 ext-const {[]} ⟨⟩ ⟨⟩ ⟨⟩ q ⟨⟩ = ⟨⟩
T-selection-strategy-lemma
 ext-const Xt@{X ∷ Xf} st@(s :: sf) εt@(ε :: εf) ϕt@(ϕ :: ϕf) q at@(a :: af) = γ
 where
  have-a : (p : X → T 𝓡) → α (extᵀ p (ε p)) ＝ ϕ (α ∘ p)
  have-a = a

  σf : (x : X) → T-Strategy (Xf x) (sf x)
  σf x = T-selection-strategy {Xf x} (sf x) (εf x) (subpred q x)

  σ : T (X , s)
  σ = mapᵀ path-head (sequenceᴶᵀ st εt (ηᵀ ∘ q))

  T-sp : (x : X) → T (Pathₛ (Xf x) (sf x))
  T-sp x = T-strategic-path (sf x) (σf x)

  p : X → T 𝓡
  p x = mapᵀ (subpred q x) (T-sp x)

  have-a' : α (extᵀ p (ε p)) ＝ ϕ (α ∘ p)
  have-a' = a p

  t : T (Pathₛ Xt st)
  t = T-strategic-path st (σ :: σf)

  III : ε p ＝ σ
  III = ε p
      ＝⟨refl⟩
        ε (λ x → mapᵀ (subpred q x) (T-sp x))
      ＝⟨refl⟩
        ε (λ x → mapᵀ
                  (subpred q x)
                  (T-strategic-path
                    (sf x)
                    (T-selection-strategy {Xf x} (sf x) (εf x) (subpred q x))))
      ＝⟨ III₀ ⟩
        ε (λ x → mapᵀ
                  (subpred q x)
                  (sequenceᴶᵀ (sf x) (εf x) (subpred (ηᵀ ∘ q) x)))
      ＝⟨refl⟩
        ε (λ x → mapᵀ (subpred q x) (ν x))
      ＝⟨refl⟩
        ε (λ x → extᵀ (subpred (ηᵀ ∘ q) x) (ν x))
      ＝⟨refl⟩
        τ
      ＝⟨ III₁ ⟩
        mapᵀ path-head (τ ⊗ᵀ ν)
      ＝⟨ III₂ ⟩
        mapᵀ path-head ((ε ⊗ᴶᵀ (λ x → sequenceᴶᵀ (sf x) (εf x))) (ηᵀ ∘ q))
      ＝⟨refl⟩
        mapᵀ path-head (sequenceᴶᵀ st εt (ηᵀ ∘ q))
      ＝⟨refl⟩
        σ ∎
      where
       ν : (x : X) → T (Pathₛ (Xf x) (sf x))
       ν x = sequenceᴶᵀ (sf x) (εf x) (subpred (ηᵀ ∘ q) x)

       τ : T (X , s)
       τ = ε (λ x → extᵀ (subpred (ηᵀ ∘ q) x) (ν x))

       III₀ = ap (λ - → ε (λ x → mapᵀ (subpred q x) (- x)))
                 (dfunext fe (λ x → (T-main-lemma ext-const
                                      (sf x) (εf x) (subpred q x))⁻¹))
       III₁ = (mapᵀ-path-head-lemma s sf τ ν ext-const)⁻¹
       III₂ = ap (mapᵀ path-head)
                 ((⊗ᴶᵀ-in-terms-of-⊗ᵀ
                    {X , s}
                    {𝓤}
                    {λ x → Pathₛ (Xf x) (sf x)}
                    ε
                    (λ x → sequenceᴶᵀ (sf x) (εf x))
                    (ηᵀ ∘ q))⁻¹)

  II = α (extᵀ p (ε p))
     ＝⟨ II₀ ⟩
       α (extᵀ p σ)
     ＝⟨refl⟩
       α (extᵀ (λ x → mapᵀ (subpred q x) (T-sp x)) σ)
     ＝⟨refl⟩
       α (extᵀ (λ x → extᵀ (ηᵀ ∘ subpred q x) (T-sp x)) σ)
     ＝⟨ II₁ ⟩
       α (extᵀ (λ x →  extᵀ (λ xs → extᵀ (ηᵀ ∘ q) (ηᵀ (x :: xs))) (T-sp x)) σ)
     ＝⟨refl⟩
       α (extᵀ (λ x →  extᵀ (extᵀ (ηᵀ ∘ q) ∘ (λ xs → ηᵀ (x :: xs))) (T-sp x)) σ)
     ＝⟨ II₂ ⟩
       α (extᵀ (λ x → extᵀ (ηᵀ ∘ q) (extᵀ (λ xs → ηᵀ (x :: xs)) (T-sp x))) σ)
     ＝⟨refl⟩
       α (extᵀ (extᵀ (λ x → ηᵀ (q x)) ∘ (λ x → mapᵀ (λ y → x , y) (T-sp x))) σ)
     ＝⟨ II₃ ⟩
       α (extᵀ (ηᵀ ∘ q) (extᵀ (λ x → mapᵀ (λ y → x , y) (T-sp x)) σ))
     ＝⟨refl⟩
       α (extᵀ (ηᵀ ∘ q) (σ ⊗ᵀ λ x → T-sp x))
     ＝⟨refl⟩
       α (extᵀ (ηᵀ ∘ q) t)
     ＝⟨refl⟩
       α (mapᵀ q t) ∎
     where
      II₀ = ap (λ - → α (extᵀ p -)) III
      II₁ = ap (λ - → α (extᵀ (λ x →  extᵀ (λ xs → - x xs) (T-sp x)) σ))
               (dfunext fe (λ x →
                dfunext fe (λ xs → (unitᵀ (ηᵀ ∘ q) (x :: xs))⁻¹)))
      II₂ = ap (λ - → α (extᵀ (λ x → - x) σ))
               (dfunext fe (λ x → assocᵀ
                                   (ηᵀ ∘ q)
                                   (λ xs → ηᵀ (x :: xs))
                                   (T-sp x)))
      II₃ = ap α (assocᵀ (ηᵀ ∘ q) (λ x → mapᵀ (λ y → x , y) (T-sp x)) σ)

  γ : is-in-T-sgpe' st ϕt q (T-selection-strategy st εt q)
  γ = (extᴬ q t                                  ＝⟨ extᴬ-agreement fe q t ⟩
       α (mapᵀ q t)                              ＝⟨ II ⁻¹ ⟩
       α (extᵀ p (ε p))                          ＝⟨ a p ⟩
       ϕ (α ∘ p)                                 ＝⟨refl⟩
       ϕ (λ x → α (mapᵀ (subpred q x) (T-sp x))) ＝⟨ γ₀ ⟩
       ϕ (λ x → extᴬ (subpred q x) (T-sp x))     ∎) ,
      (λ x → T-selection-strategy-lemma ext-const (sf x) (εf x) (ϕf x) (subpred q x) (af x))
   where
    γ₀ = ap ϕ ((dfunext fe (λ x → extᴬ-agreement fe (subpred q x) (T-sp x)))⁻¹)

main-theorem
 : ext-const 𝕋
 → (G@(game Xt q ϕt) : Game)
   (st : structure S Xt)
   (εt : 𝓙𝓣 Xt st)
 → [ st ] εt Attainsᴬ ϕt
 → is-in-T-sgpe G st (T-selection-strategy st εt q)
main-theorem ext-const G@(game Xt q ϕt) st εt
 = T-selection-strategy-lemma ext-const st εt ϕt q

\end{code}

Notice that the definition of T-selection-strategy st εt q doesn't use
the algebra 𝓐, but its correctness specification does.
