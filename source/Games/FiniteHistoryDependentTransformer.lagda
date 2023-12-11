_Martin Escardo, Paulo Oliva, 2022, version of October 2023.

Warning. This module is a mess. We plan to clean it up soon. At the
moment the proofs are in "blackboard" style (improvised proofs that
work) rather than "article" style (proofs written in a more
presentable way).

This generalizes (but also uses) the file Games.FiniteHistoryDependent
with a monad parameter 𝓣. When 𝓣 is the identity monad 𝕀𝕕, the
original development is obtained. We apply the selection-monad
transformer 𝕁-transf to 𝓣. Notice, however, that the definition of
game is the same. See [1] for background.

The main examples of 𝓣 we have in mind are the powerset monad (for the
Herbrand Functional Interpretation [2]), probability distribution
monads (for mixed strategies) and the reader monad (for alpha-beta
pruning in the file Games.alpha-beta).

[1] M. Escardo and P. Oliva.
    Higher-order Games with Dependent Types (2023)
    https://doi.org/10.1016/j.tcs.2023.114111
    Available in TypeTopology at Games.FiniteHistoryDependent.

[2] M. Escardo and P. Oliva.
    The Herbrand functional interpretation of the double negation shift (2017)
    https://doi.org/10.1017/jsl.2017.8
    (Not available in TypeTopology at the time of writing (October 2023).)

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import Games.TypeTrees
open import Games.Monad
open import Games.J
open import Games.K
open import MLTT.Spartan hiding (J)
open import UF.Base
open import UF.FunExt
open import UF.Equiv

module Games.FiniteHistoryDependentTransformer
        (fe : Fun-Ext)
        (𝕋  : Monad)
        (R  : Type)
        (𝓐  : Algebra 𝕋 R)
 where

open import Games.FiniteHistoryDependent R
     using (𝓚 ; Game ; game ; sequenceᴷ ; optimal-outcome)

open Game

fext : DN-funext 𝓤₀ 𝓤₀
fext = dfunext fe

open K-definitions R
open T-definitions 𝕋
open α-definitions 𝕋 R 𝓐
open JT-definitions 𝕋 R 𝓐 fe

\end{code}

The types of trees with JT and KT structure.

\begin{code}

𝓙𝓣 : 𝑻 → Type
𝓙𝓣 = structure JT

𝓚𝓣 : 𝑻 → Type
𝓚𝓣 = structure KT

sequenceᴶᵀ : {Xt : 𝑻} → 𝓙𝓣 Xt → JT (Path Xt)
sequenceᴶᵀ = path-sequence 𝕁𝕋

T-Strategy : 𝑻 -> Type
T-Strategy = structure T

T-strategic-path : {Xt : 𝑻} → T-Strategy Xt → T (Path Xt)
T-strategic-path = path-sequence 𝕋

is-in-T-equilibrium : {X : Type} {Xf : X → 𝑻}
                      (q : (Σ x ꞉ X , Path (Xf x)) → R)
                      (ϕ : K X)
                    → T-Strategy (X ∷ Xf)
                    → Type
is-in-T-equilibrium {X} {Xf} q ϕ σt@(σ :: σf)  =
 α-extᵀ q (T-strategic-path σt) ＝ ϕ (λ x → α-curryᵀ q x (T-strategic-path (σf x)))

is-in-T-sgpe : {Xt : 𝑻} → 𝓚 Xt → (Path Xt → R) → T-Strategy Xt → Type
is-in-T-sgpe {[]}     ⟨⟩        q ⟨⟩           = 𝟙
is-in-T-sgpe {X ∷ Xf} (ϕ :: ϕf) q σt@(σ :: σf) =
    is-in-T-equilibrium q ϕ σt
  × ((x : X) → is-in-T-sgpe {Xf x} (ϕf x) (subpred q x) (σf x))

is-T-optimal : (G : Game) → T-Strategy (Xt G) → Type
is-T-optimal (game Xt q ϕt) = is-in-T-sgpe {Xt} ϕt q

\end{code}

The main lemma is that the optimal outcome is the same thing as the
application of the outcome function to the path induced by a strategy
in perfect subgame equilibrium.

\begin{code}

T-sgpe-lemma : (Xt : 𝑻) (ϕt : 𝓚 Xt) (q : Path Xt → R) (σt : T-Strategy Xt)
             → is-in-T-sgpe ϕt q σt
             → α-extᵀ q (T-strategic-path σt) ＝ sequenceᴷ ϕt q
T-sgpe-lemma [] ⟨⟩ q ⟨⟩ ⟨⟩ =
  α-extᵀ q (T-strategic-path ⟨⟩) ＝⟨ refl ⟩
  α (extᵀ (ηᵀ ∘ q) (ηᵀ ⟨⟩))      ＝⟨ ap α (unitᵀ (ηᵀ ∘ q) ⟨⟩) ⟩
  α (ηᵀ (q ⟨⟩))                  ＝⟨ α-unitᵀ (q ⟨⟩) ⟩
  q ⟨⟩                           ＝⟨ refl ⟩
  sequenceᴷ ⟨⟩ q                 ∎
T-sgpe-lemma (X ∷ Xf) (ϕ :: ϕt) q (σ :: σf) (h :: t) =
 α-extᵀ q (T-strategic-path (σ :: σf))            ＝⟨ h ⟩
 ϕ (λ x → α-curryᵀ q x (T-strategic-path (σf x))) ＝⟨ ap ϕ (fext IH) ⟩
 ϕ (λ x → sequenceᴷ (ϕt x) (subpred q x))         ＝⟨ refl ⟩
 sequenceᴷ (ϕ :: ϕt) q                            ∎
  where
   IH : (x : X) → α-curryᵀ q x (T-strategic-path (σf x))
                ＝ sequenceᴷ (ϕt x) (subpred q x)
   IH x = T-sgpe-lemma (Xf x) (ϕt x) (subpred q x) (σf x) (t x)

\end{code}

This can be reformulated as follows in terms of the type of games:

\begin{code}

T-optimality-theorem : (G : Game) (σt : T-Strategy (Xt G))
                     → is-T-optimal G σt
                     → α-extᵀ (q G) (T-strategic-path σt)
                     ＝ optimal-outcome G
T-optimality-theorem (game Xt q ϕt) = T-sgpe-lemma Xt ϕt q

\end{code}

We now show how to use selection functions to compute a sgpe strategy.

\begin{code}

T-selection-strategy : {Xt : 𝑻} → 𝓙𝓣 Xt → (Path Xt → R) → T-Strategy Xt
T-selection-strategy {[]}     ⟨⟩           q = ⟨⟩
T-selection-strategy {X ∷ Xf} εt@(ε :: εf) q = σ :: σf
 where
  t : T (Path (X ∷ Xf))
  t = sequenceᴶᵀ εt (ηᵀ ∘ q)

  σ : T X
  σ = mapᵀ path-head t

  σf : (x : X) → T-Strategy (Xf x)
  σf x = T-selection-strategy {Xf x} (εf x) (subpred q x)

\end{code}

For the next technical lemma, we need the monad T to satisfy the
condition extᵀ-const defined in Games.Monads, which says that the
Kleisli extension of a constant function is itself constant. Ohad
Kammar pointed out to us that this condition is equivalent to the
monad being affine. A proof is included in the module Games.Monad.

TODO. Explain the intuition of the condition extᵀ-const and
equivalents.

\begin{code}

mapᵀ-path-head-lemma : {X : Type} {Xf : X → 𝑻}
                       (a : T X) (b : (x : X) → T (Path (Xf x)))
                     → ext-const 𝕋
                     → mapᵀ path-head (a ⊗ᵀ b) ＝ a
mapᵀ-path-head-lemma {X} {Xf} a b ext-const =
  mapᵀ path-head (a ⊗ᵀ b)                                  ＝⟨ refl ⟩
  extᵀ (ηᵀ ∘ path-head) (a ⊗ᵀ b)                           ＝⟨ refl ⟩
  extᵀ g (a ⊗ᵀ b)                                          ＝⟨ refl ⟩
  extᵀ g (extᵀ (λ x → mapᵀ (x ::_) (b x)) a)               ＝⟨ refl ⟩
  extᵀ g (extᵀ (λ x → extᵀ (ηᵀ ∘ (x ::_)) (b x)) a)        ＝⟨ ⦅1⦆ ⟩
  extᵀ (extᵀ g ∘ (λ x → extᵀ (ηᵀ ∘ (x ::_)) (b x))) a      ＝⟨ refl ⟩
  extᵀ (extᵀ g ∘ (λ x → extᵀ (f x) (b x))) a               ＝⟨ refl ⟩
  extᵀ (λ x → extᵀ g (extᵀ (f x) (b x))) a                 ＝⟨ refl ⟩
  extᵀ (λ x → (extᵀ g ∘ extᵀ (f x)) (b x)) a               ＝⟨ ⦅2⦆ ⟩
  extᵀ (λ x → extᵀ (extᵀ g ∘ (f x)) (b x)) a               ＝⟨ refl ⟩
  extᵀ (λ x → extᵀ (λ xs → extᵀ g (ηᵀ (x :: xs))) (b x)) a ＝⟨ ⦅3⦆ ⟩
  extᵀ (λ x → extᵀ (λ xs → g (x :: xs)) (b x)) a           ＝⟨ refl ⟩
  extᵀ (λ x → extᵀ (λ _ → ηᵀ x) (b x)) a                   ＝⟨ ⦅4⦆ ⟩
  extᵀ ηᵀ a                                                ＝⟨ extᵀ-η a ⟩
  a                                                        ∎
 where
  g : Path (X ∷ Xf) → T X
  g = ηᵀ ∘ path-head

  f : (x : X) → Path (Xf x) → T (Path (X ∷ Xf))
  f x = ηᵀ ∘ (x ::_)

  I : ∀ x → (extᵀ g ∘ extᵀ (f x)) (b x) ＝ extᵀ (extᵀ g ∘ (f x)) (b x)
  I x = (assocᵀ g (f x) (b x))⁻¹

  II : (x : X) (xs : Path (Xf x)) → extᵀ g (ηᵀ (x :: xs)) ＝ g (x :: xs)
  II x xs = unitᵀ g (x :: xs)

  ⦅1⦆ = (assocᵀ g (λ x → extᵀ (f x) (b x)) a)⁻¹
  ⦅2⦆ = ap (λ - → extᵀ - a) (fext I)
  ⦅3⦆ = ap (λ - →  extᵀ (λ x → extᵀ (- x) (b x)) a) (fext (λ x → fext (II x)))
  ⦅4⦆ = ap (λ - → extᵀ - a) (fext (λ x → ext-const (ηᵀ x) (b x)))

\end{code}

We also need the following technical lemma, which expresses the tensor
_⊗ᴶᵀ_ in terms of the tensor _⊗ᵀ_ as in Lemma 2.3 of reference [2]
above.

\begin{code}

module _ {X  : Type}
         {Y  : X → Type}
         (ε  : JT X)
         (δ  : (x : X) → JT (Y x))
 where

 private
  ν : ((Σ x ꞉ X , Y x) → T R) → (x : X) → T (Y x)
  ν q x = δ x (λ y → q (x , y))

  τ : ((Σ x ꞉ X , Y x) → T R) → T X
  τ q = ε (λ x → extᵀ (λ y → q (x , y)) (ν q x))

 ⊗ᴶᵀ-in-terms-of-⊗ᵀ : (q : (Σ x ꞉ X , Y x) → T R)
                    → (ε ⊗ᴶᵀ δ) q ＝ τ q ⊗ᵀ ν q
 ⊗ᴶᵀ-in-terms-of-⊗ᵀ q =
    (ε ⊗ᴶᵀ δ) q                                          ＝⟨ refl ⟩
    extᴶᵀ (λ x → extᴶᵀ (λ y _ → ηᵀ (x , y)) (δ x)) ε q   ＝⟨ ⦅1⦆ ⟩
    extᴶᵀ Θ ε q                                          ＝⟨ refl ⟩
    extᵀ (λ x → Θ x q) (ε (λ x → extᵀ q (Θ x q)))        ＝⟨ ⦅2⦆ ⟩
    extᵀ (λ x → Θ x q) (τ q)                             ＝⟨ refl ⟩
    τ q ⊗ᵀ ν q                                           ∎
     where
      Θ : X → JT (Σ x ꞉ X , Y x)
      Θ x r = extᵀ (λ y → ηᵀ (x , y)) (ν r x)

      I : (λ x → extᴶᵀ (λ y _ → ηᵀ (x , y)) (δ x)) ＝ Θ
      I = fext (λ x →
          fext (λ r → ap (λ - → extᵀ (λ y → ηᵀ (x , y)) (δ x (λ y → - (x , y))))
                         (fext (unitᵀ r))))

      ⦅1⦆ = ap (λ - → extᴶᵀ - ε q) I

      II : ∀ x → extᵀ q ∘ extᵀ (λ y → ηᵀ (x , y)) ＝ extᵀ (λ y → q (x , y))
      II x = extᵀ q ∘ extᵀ (λ y → ηᵀ (x , y))               ＝⟨ ⦅i⦆ ⟩
             (λ x' → extᵀ (extᵀ q ∘ (λ y → ηᵀ (x , y))) x') ＝⟨ refl ⟩
             extᵀ (λ y → ((extᵀ q) ∘ ηᵀ) (x , y))           ＝⟨ ⦅ii⦆ ⟩
             extᵀ (λ y → q (x , y))                         ∎
       where
        ⦅i⦆  = fext (λ x' → (assocᵀ q (λ y → ηᵀ (x , y)) x')⁻¹)
        ⦅ii⦆ = ap extᵀ (fext (λ y → unitᵀ q (x , y)))

      III : ε (λ x → extᵀ q (extᵀ (λ y → ηᵀ (x , y)) (ν q x))) ＝ τ q
      III = ap ε (fext (λ x → ap (λ - → - (ν q x)) (II x)))

      ⦅2⦆ = ap (extᵀ (λ x → Θ x q)) III

\end{code}

The following is the main lemma of this file.

Given a selection tree εt over Xt and an outcome function q, we can
either sequence εt and apply it to q to obtain a monadic path on Xt,
or we can first use εt to calculate a strategy on Xt and derive its
monadic strategic path. The lemma says that these are the same path.

\begin{code}

T-main-lemma : ext-const 𝕋
             → {Xt : 𝑻} (εt : 𝓙𝓣 Xt) (q : Path Xt → R)
             → sequenceᴶᵀ εt (ηᵀ ∘ q)
             ＝ T-strategic-path (T-selection-strategy εt q)
T-main-lemma ext-const {[]}     ⟨⟩           q = refl
T-main-lemma ext-const {X ∷ Xf} εt@(ε :: εf) q = γ
 where
  δ : (x : X) → JT (Path (Xf x))
  δ x = sequenceᴶᵀ {Xf x} (εf x)

  q' : (x : X) → Path (Xf x) → T R
  q' x = ηᵀ ∘ subpred q x

  σf : (x : X) → T-Strategy (Xf x)
  σf x = T-selection-strategy {Xf x} (εf x) (subpred q x)

  b c : (x : X) → T (Path (Xf x))
  b x = δ x (q' x)
  c x = T-strategic-path (σf x)

  IH : b ∼ c
  IH x = T-main-lemma ext-const (εf x) (subpred q x)

  σ : T X
  σ = mapᵀ path-head (sequenceᴶᵀ εt (ηᵀ ∘ q))

  I = ε (λ x → extᵀ (q' x) (c x))                       ＝⟨ ⦅1⦆ ⟩
      mapᵀ path-head (ε (λ x → extᵀ (q' x) (c x)) ⊗ᵀ c) ＝⟨ ⦅2⦆ ⟩
      mapᵀ path-head (ε (λ x → extᵀ (q' x) (b x)) ⊗ᵀ b) ＝⟨ ⦅3⦆ ⟩
      mapᵀ path-head ((ε ⊗ᴶᵀ δ) (ηᵀ ∘ q))               ＝⟨ refl ⟩
      mapᵀ path-head (sequenceᴶᵀ εt (ηᵀ ∘ q))           ＝⟨ refl ⟩
      σ                                                 ∎
   where
    ⦅1⦆ = (mapᵀ-path-head-lemma (ε (λ x → extᵀ (q' x) (c x))) c ext-const)⁻¹
    ⦅2⦆ = ap (λ - → mapᵀ path-head (ε (λ x → extᵀ (q' x) (- x)) ⊗ᵀ -))
            (fext (λ x → (IH x)⁻¹))
    ⦅3⦆ = (ap (mapᵀ path-head) (⊗ᴶᵀ-in-terms-of-⊗ᵀ ε δ (ηᵀ ∘ q)))⁻¹

  γ : sequenceᴶᵀ (ε :: εf) (ηᵀ ∘ q)
    ＝ T-strategic-path (T-selection-strategy (ε :: εf) q)
  γ = sequenceᴶᵀ (ε :: εf) (ηᵀ ∘ q)                    ＝⟨ refl ⟩
      (ε ⊗ᴶᵀ δ) (ηᵀ ∘ q)                                ＝⟨ ⦅1⦆ ⟩
      ε (λ x → extᵀ (q' x) (b x)) ⊗ᵀ b                  ＝⟨ ⦅2⦆ ⟩
      (ε (λ x → extᵀ (q' x) (c x)) ⊗ᵀ c)                ＝⟨ ⦅3⦆ ⟩
      σ ⊗ᵀ c                                            ＝⟨ refl ⟩
      σ ⊗ᵀ (λ x → T-strategic-path {Xf x} (σf x))       ＝⟨ refl ⟩
      T-strategic-path (σ :: σf)                        ＝⟨ refl ⟩
      T-strategic-path (T-selection-strategy (ε :: εf) q) ∎
   where
    ⦅1⦆ = ⊗ᴶᵀ-in-terms-of-⊗ᵀ ε δ (ηᵀ ∘ q)
    ⦅2⦆ = ap (λ - → ε (λ x → extᵀ (q' x) (- x)) ⊗ᵀ -) (fext IH)
    ⦅3⦆ = ap (_⊗ᵀ c) I

\end{code}

Is α-Overlineᵀ useful?

\begin{code}

α-Overlineᵀ : {Xt : 𝑻} → 𝓙𝓣 Xt → 𝓚𝓣 Xt
α-Overlineᵀ {[]}     ⟨⟩        = ⟨⟩
α-Overlineᵀ {X ∷ Xf} (ε :: εf) = α-overlineᵀ ε :: λ x → α-Overlineᵀ {Xf x} (εf x)

_Attainsᵀ_ : {Xt : 𝑻} → 𝓙𝓣 Xt → 𝓚 Xt → Type
_Attainsᵀ_ {[]}     ⟨⟩        ⟨⟩        = 𝟙
_Attainsᵀ_ {X ∷ Xf} (ε :: εf) (ϕ :: ϕf) = (ε α-attainsᵀ ϕ)
                                        × ((x : X) → (εf x) Attainsᵀ (ϕf x))

T-selection-strategy-lemma : ext-const 𝕋
                           → {Xt : 𝑻} (εt : 𝓙𝓣 Xt) (ϕt : 𝓚 Xt) (q : Path Xt → R)
                           → εt Attainsᵀ ϕt
                           → is-in-T-sgpe ϕt q (T-selection-strategy εt q)
T-selection-strategy-lemma ext-const {[]}     ⟨⟩           ⟨⟩           q ⟨⟩           = ⟨⟩
T-selection-strategy-lemma ext-const {X ∷ Xf} εt@(ε :: εf) ϕt@(ϕ :: ϕf) q at@(a :: af) = γ
 where
  have-a : (p : X → T R) → α (extᵀ p (ε p)) ＝ ϕ (α ∘ p)
  have-a = a

  σf : (x : X) → structure T (Xf x)
  σf x = T-selection-strategy {Xf x} (εf x) (subpred q x)

  σ : T X
  σ = mapᵀ path-head (sequenceᴶᵀ εt (ηᵀ ∘ q))

  p : X → T R
  p x = mapᵀ (subpred q x) (T-strategic-path (σf x))

  I = λ x → α-curryᵀ q x (T-strategic-path (σf x)) ＝⟨ refl ⟩
            α-extᵀ (subpred q x) (T-strategic-path (σf x)) ＝⟨ refl ⟩
            α (mapᵀ (subpred q x) (T-strategic-path (σf x))) ∎

  have-a' : α (extᵀ p (ε p)) ＝ ϕ (α ∘ p)
  have-a' = a p

  t : T (Path (X ∷ Xf))
  t = T-strategic-path (σ :: σf)

  III : ε p ＝ σ
  III = ε p ＝⟨ refl ⟩
        ε (λ x → mapᵀ (subpred q x) (T-strategic-path (σf x))) ＝⟨ refl ⟩
        ε (λ x → mapᵀ (subpred q x) (T-strategic-path (T-selection-strategy {Xf x} (εf x) (subpred q x)))) ＝⟨ III₀ ⟩
        ε (λ x → mapᵀ (subpred q x) (sequenceᴶᵀ (εf x) (subpred (ηᵀ ∘ q) x))) ＝⟨ refl ⟩
        ε (λ x → mapᵀ (subpred q x) (ν x)) ＝⟨ refl ⟩
        ε (λ x → extᵀ (subpred (ηᵀ ∘ q) x) (ν x)) ＝⟨ refl ⟩
        τ ＝⟨ III₁ ⟩
        mapᵀ path-head (τ ⊗ᵀ ν) ＝⟨ III₂ ⟩
        mapᵀ path-head ((ε ⊗ᴶᵀ (λ x → sequenceᴶᵀ (εf x))) (ηᵀ ∘ q)) ＝⟨ refl ⟩
        mapᵀ path-head (sequenceᴶᵀ εt (ηᵀ ∘ q)) ＝⟨ refl ⟩
        σ ∎
        where
         ν : (x : X) → T (Path (Xf x))
         ν x = sequenceᴶᵀ (εf x) (subpred (ηᵀ ∘ q) x)

         τ : T X
         τ = ε (λ x → extᵀ (subpred (ηᵀ ∘ q) x) (ν x))

         III₀ = ap (λ - → ε (λ x → mapᵀ (subpred q x) (- x))) (dfunext fe (λ x → (T-main-lemma ext-const (εf x) (subpred q x))⁻¹))
         III₁ = (mapᵀ-path-head-lemma τ ν ext-const)⁻¹
         III₂ = ap (mapᵀ path-head) ((⊗ᴶᵀ-in-terms-of-⊗ᵀ {X} {λ x → Path (Xf x)} ε (λ x → sequenceᴶᵀ (εf x)) (ηᵀ ∘ q)) ⁻¹)

  II : α (extᵀ p (ε p)) ＝ α-extᵀ q t
  II = α (extᵀ p (ε p)) ＝⟨ II₀ ⟩
       α (extᵀ p σ) ＝⟨ refl ⟩
       α (extᵀ (λ x → mapᵀ (subpred q x) (T-strategic-path (σf x))) σ) ＝⟨ refl ⟩
       α (extᵀ (λ x → extᵀ (ηᵀ ∘ subpred q x) (T-strategic-path (σf x))) σ) ＝⟨ II₁ ⟩
       α (extᵀ (λ x →  extᵀ (λ xs → extᵀ (ηᵀ ∘ q) (ηᵀ (x :: xs))) (T-strategic-path (σf x))) σ) ＝⟨ refl ⟩
       α (extᵀ (λ x →  extᵀ (extᵀ (ηᵀ ∘ q) ∘ (λ xs → ηᵀ (x :: xs))) (T-strategic-path (σf x))) σ) ＝⟨ II₂ ⟩
       α (extᵀ (λ x → extᵀ (ηᵀ ∘ q) (extᵀ (λ xs → ηᵀ (x :: xs)) (T-strategic-path (σf x)))) σ) ＝⟨ refl ⟩
       α (extᵀ (extᵀ (λ x → ηᵀ (q x)) ∘ (λ x → mapᵀ (λ y → x , y) (T-strategic-path (σf x)))) σ) ＝⟨ II₃ ⟩
       α (extᵀ (ηᵀ ∘ q) (extᵀ (λ x → mapᵀ (λ y → x , y) (T-strategic-path (σf x))) σ)) ＝⟨ refl ⟩
       α (extᵀ (ηᵀ ∘ q) (σ ⊗ᵀ λ x → T-strategic-path (σf x))) ＝⟨ refl ⟩
       α (extᵀ (ηᵀ ∘ q) (T-strategic-path (σ :: σf))) ＝⟨ refl ⟩
       α (mapᵀ q (T-strategic-path (σ :: σf))) ＝⟨ refl ⟩
       α (mapᵀ q (T-strategic-path (σ :: σf))) ＝⟨ refl ⟩
       α (mapᵀ q t) ＝⟨ refl ⟩
       α-extᵀ q t ∎
        where
         II₀ = ap (λ - → α (extᵀ p -)) III
         II₁ = ap (λ - → α (extᵀ (λ x →  extᵀ (λ xs → - x xs) (T-strategic-path (σf x))) σ)) (dfunext fe (λ x → dfunext fe (λ xs → (unitᵀ (ηᵀ ∘ q) (x :: xs))⁻¹)))
         II₂ = ap (λ - → α (extᵀ (λ x → - x) σ)) (dfunext fe (λ x → assocᵀ (ηᵀ ∘ q) (λ xs → ηᵀ (x :: xs)) (T-strategic-path (σf x))))
         II₃ = ap α (assocᵀ (ηᵀ ∘ q) (λ x → mapᵀ (λ y → x , y) (T-strategic-path (σf x))) σ)

  γ' : (α-extᵀ q t ＝ ϕ (α ∘ p))
     × (((x : X) → is-in-T-sgpe {Xf x} (ϕf x) (subpred q x) (σf x)))
  γ' = (α-extᵀ q t ＝⟨ II ⁻¹ ⟩
       α (extᵀ p (ε p)) ＝⟨ a p ⟩
       ϕ (α ∘ p) ∎) ,
       (λ x → T-selection-strategy-lemma ext-const (εf x) (ϕf x) (subpred q x) (af x))

  γ : is-in-T-sgpe (ϕ :: ϕf) q (T-selection-strategy (ε :: εf) q)
  γ = γ'

main-theorem : ext-const 𝕋
             → (G : Game)
               (εt : 𝓙𝓣 (Xt G))
             → εt Attainsᵀ (ϕt G)
             → is-T-optimal G (T-selection-strategy εt (q G))
main-theorem ext-const G εt = T-selection-strategy-lemma ext-const εt (ϕt G) (q G)

\end{code}

Alternative, non-inductive definition of T-optimality. We don't have
any use for it, but it is useful for comparison with the classical
notion. Partial, possibly empty, paths in 𝑻's, and related notions.

\begin{code}

pPath : 𝑻 → Type
pPath []       = 𝟙
pPath (X ∷ Xf) = 𝟙 + (Σ x ꞉ X , pPath (Xf x))

sub𝑻 : (Xt : 𝑻) → pPath Xt → 𝑻
sub𝑻 []       ⟨⟩              = []
sub𝑻 (X ∷ Xf) (inl ⟨⟩)        = X ∷ Xf
sub𝑻 (X ∷ Xf) (inr (x :: xs)) = sub𝑻 (Xf x) xs

Subpred : {Xt : 𝑻} → (Path Xt → R) → (xs : pPath Xt) → Path (sub𝑻 Xt xs) → R
Subpred {[]} q ⟨⟩ ⟨⟩ = q ⟨⟩
Subpred {X ∷ Xf} q (inl ⟨⟩) (y :: ys) = q (y :: ys)
Subpred {X ∷ Xf} q (inr (x :: xs)) ys = Subpred {Xf x} (subpred q x) xs ys

sub𝓚 : {Xt : 𝑻} → 𝓚 Xt → (xs : pPath Xt) → 𝓚 (sub𝑻 Xt xs)
sub𝓚 {[]} ϕt ⟨⟩ = ⟨⟩
sub𝓚 {X ∷ Xf} ϕt (inl ⟨⟩) = ϕt
sub𝓚 {X ∷ Xf} (ϕ :: ϕf) (inr (x :: xs)) = sub𝓚 {Xf x} (ϕf x) xs

sub𝓙𝓣 : {Xt : 𝑻} → 𝓙𝓣 Xt → (xs : pPath Xt) → 𝓙𝓣 (sub𝑻 Xt xs)
sub𝓙𝓣 {[]} εt ⟨⟩ = ⟨⟩
sub𝓙𝓣 {X ∷ Xf} εt (inl ⟨⟩) = εt
sub𝓙𝓣 {X ∷ Xf} (ε :: εf) (inr (x :: xs)) = sub𝓙𝓣 {Xf x} (εf x) xs

subgame : (G : Game) → pPath (Xt G) → Game
subgame (game Xt q ϕt) xs = game (sub𝑻 Xt xs) (Subpred q xs) (sub𝓚 ϕt xs)

sub-T-Strategy : {Xt : 𝑻} → T-Strategy Xt → (xs : pPath Xt) → T-Strategy (sub𝑻 Xt xs)
sub-T-Strategy {[]}     ⟨⟩        ⟨⟩              = ⟨⟩
sub-T-Strategy {X ∷ Xf} (σ :: σf) (inl ⟨⟩)        = σ :: σf
sub-T-Strategy {X ∷ Xf} (σ :: σf) (inr (x :: xs)) = sub-T-Strategy {Xf x} (σf x) xs

is-in-T-equilibrium' : (G : Game) → T-Strategy (Xt G) → Type
is-in-T-equilibrium' (game []       q ⟨⟩)       ⟨⟩ = 𝟙
is-in-T-equilibrium' (game (X ∷ Xf) q (ϕ :: _)) σt = is-in-T-equilibrium q ϕ σt

is-T-optimal₂ : (G : Game) (σ : T-Strategy (Xt G)) → Type
is-T-optimal₂ G σ =
 (xs : pPath (Xt G)) → is-in-T-equilibrium' (subgame G xs) (sub-T-Strategy σ xs)

T-sgpe-equiv : (G : Game) (σ : T-Strategy (Xt G))
             → is-T-optimal  G σ
             ↔ is-T-optimal₂ G σ
T-sgpe-equiv (game Xt q ϕt) σ = I ϕt q σ , II ϕt q σ
 where
  I : {Xt : 𝑻} (ϕt : 𝓚 Xt) (q : Path Xt → R) (σ : T-Strategy Xt)
    → is-T-optimal (game Xt q ϕt) σ → is-T-optimal₂ (game Xt q ϕt) σ
  I {[]}     ⟨⟩        q ⟨⟩        ⟨⟩        ⟨⟩              = ⟨⟩
  I {X ∷ Xf} (ϕ :: ϕf) q (σ :: σf) (i :: _)  (inl ⟨⟩)        = i
  I {X ∷ Xf} (ϕ :: ϕf) q (σ :: σf) (_ :: is) (inr (x :: xs)) =
    I {Xf x} (ϕf x) (subpred q x) (σf x) (is x) xs

  II : {Xt : 𝑻} (ϕt : 𝓚 Xt) (q : Path Xt → R) (σ : T-Strategy Xt)
    → is-T-optimal₂ (game Xt q ϕt) σ → is-T-optimal (game Xt q ϕt) σ
  II {[]}     ⟨⟩        q ⟨⟩        j = ⟨⟩
  II {X ∷ Xf} (ϕ :: ϕf) q (σ :: σf) j =
     j (inl ⟨⟩) ,
     (λ x → II {Xf x} (ϕf x) (subpred q x) (σf x) (λ xs → j (inr (x :: xs))))


{-
T-sgpe-equiv : (G : Game) (σ : T-Strategy (Xt G))
             → is-T-optimal G σ ↔ is-T-optimal₂ G σ
T-sgpe-equiv (game Xt q ϕt) σ = I ϕt q σ , II ϕt q σ

is-in-subgame-perfect-equilibrium : (G : Game) → 𝓙𝓣 (Xt G) → Type
is-in-subgame-perfect-equilibrium G εt =

 (xs : pPath (Xt G)) → is-in-head-equilibrium (subgame G xs) (sub𝓙𝓣 εt xs)

-}
\end{code}
