Chuangjie Xu 2013 (updated in February 2015, ported to TypeTopology in 2025)

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt using (DN-funext)

module C-Space.UsingFunExt.TdefinableFunctionsAreUC (fe : DN-funext 𝓤₀ 𝓤₀) where

open import Naturals.Properties

open import C-Space.Preliminaries.Sequence
open import C-Space.Preliminaries.Naturals.Order
open import C-Space.UniformContinuity
open import C-Space.Coverage
open import C-Space.UsingFunExt.Space
open import C-Space.UsingFunExt.CartesianClosedness fe
open import C-Space.UsingFunExt.DiscreteSpace fe
open import C-Space.UsingFunExt.YonedaLemma fe
open import C-Space.UsingFunExt.Fan fe

\end{code}

Syntax of system T

\begin{code}

infixr 10 _⊠_
infixr 10 _⇨_

data Ty : Set where
 ② : Ty
 Ⓝ : Ty
 _⊠_ : Ty → Ty → Ty
 _⇨_ : Ty → Ty → Ty

infixl 10 _₊_

data Cxt : ℕ → Set where
 ε : Cxt zero
 _₊_ : {n : ℕ} → Cxt n → Ty → Cxt (succ n)

data Fin : ℕ → Set where
 zero : {n : ℕ} → Fin (succ n)
 succ : {n : ℕ} → Fin n → Fin (succ n)

_[_] : {n : ℕ} → Cxt n → Fin n → Ty
(xs ₊ x) [ zero ]   = x
(xs ₊ x) [ succ i ] = xs [ i ]

infixl 10 _·_

data Tm : {n : ℕ} → Cxt n → Ty → Set where
 VAR  : {n : ℕ}{Γ : Cxt n}           → (i : Fin n) → Tm Γ (Γ [ i ])
 ⊥    : {n : ℕ}{Γ : Cxt n}           → Tm Γ ②
 ⊤    : {n : ℕ}{Γ : Cxt n}           → Tm Γ ②
 IF   : {n : ℕ}{Γ : Cxt n}{σ : Ty}   → Tm Γ (② ⇨ σ ⇨ σ ⇨ σ)
 ZERO : {n : ℕ}{Γ : Cxt n}           → Tm Γ Ⓝ
 SUCC : {n : ℕ}{Γ : Cxt n}           → Tm Γ (Ⓝ ⇨ Ⓝ)
 REC  : {n : ℕ}{Γ : Cxt n}{σ : Ty}   → Tm Γ (σ ⇨ (Ⓝ ⇨ σ ⇨ σ) ⇨ Ⓝ ⇨ σ)
 PAIR : {n : ℕ}{Γ : Cxt n}{σ τ : Ty} → Tm Γ σ → Tm Γ τ → Tm Γ (σ ⊠ τ)
 PRJ₁ : {n : ℕ}{Γ : Cxt n}{σ τ : Ty} → Tm Γ (σ ⊠ τ) → Tm Γ σ
 PRJ₂ : {n : ℕ}{Γ : Cxt n}{σ τ : Ty} → Tm Γ (σ ⊠ τ) → Tm Γ τ
 LAM  : {n : ℕ}{Γ : Cxt n}{σ τ : Ty} → Tm (Γ ₊ σ) τ → Tm Γ (σ ⇨ τ)
 _·_  : {n : ℕ}{Γ : Cxt n}{σ τ : Ty} → Tm Γ (σ ⇨ τ) → Tm Γ σ → Tm Γ τ

\end{code}

Interpretation in C-spaces

\begin{code}

c⟦_⟧ʸ : Ty → Space
c⟦ ② ⟧ʸ = 𝟚Space
c⟦ Ⓝ ⟧ʸ = ℕSpace
c⟦ σ ⊠ τ ⟧ʸ = c⟦ σ ⟧ʸ ⊗ c⟦ τ ⟧ʸ
c⟦ σ ⇨ τ ⟧ʸ = c⟦ σ ⟧ʸ ⇒ c⟦ τ ⟧ʸ

c⟦_⟧ᶜ : {n : ℕ} → Cxt n → Space
c⟦ ε ⟧ᶜ = 𝟙Space
c⟦ Γ ₊ A ⟧ᶜ = c⟦ Γ ⟧ᶜ ⊗ c⟦ A ⟧ʸ

continuous-prj : {n : ℕ}(Γ : Cxt n)(i : Fin n) → Map c⟦ Γ ⟧ᶜ c⟦ Γ [ i ] ⟧ʸ
continuous-prj  ε      ()
continuous-prj (Γ ₊ σ)  zero    = pr₂ , (λ _ → pr₂)
continuous-prj (Γ ₊ σ) (succ i) = prjᵢ₊₁ , cprjᵢ₊₁
 where
  prjᵢ : U c⟦ Γ ⟧ᶜ → U c⟦ Γ [ i ] ⟧ʸ
  prjᵢ = pr₁ (continuous-prj Γ i)
  prjᵢ₊₁ : U c⟦ Γ ₊ σ ⟧ᶜ → U c⟦ (Γ ₊ σ) [ succ i ] ⟧ʸ
  prjᵢ₊₁ (xs , _) = prjᵢ xs
  cprjᵢ : continuous c⟦ Γ ⟧ᶜ c⟦ Γ [ i ] ⟧ʸ prjᵢ
  cprjᵢ = pr₂ (continuous-prj Γ i)
  cprjᵢ₊₁ : continuous c⟦ Γ ₊ σ ⟧ᶜ c⟦ (Γ ₊ σ) [ succ i ] ⟧ʸ prjᵢ₊₁
  cprjᵢ₊₁ p pΓσ = cprjᵢ (pr₁ ∘ p) (pr₁ pΓσ)


c⟦_⟧ᵐ : {n : ℕ}{Γ : Cxt n}{σ : Ty} → Tm Γ σ → Map c⟦ Γ ⟧ᶜ c⟦ σ ⟧ʸ
c⟦ VAR {_} {Γ} i ⟧ᵐ            = continuous-prj Γ i
c⟦ ⊥ {_} {Γ} ⟧ᵐ                = continuous-constant c⟦ Γ ⟧ᶜ c⟦ ② ⟧ʸ ₀
c⟦ ⊤ {_} {Γ} ⟧ᵐ                = continuous-constant c⟦ Γ ⟧ᶜ c⟦ ② ⟧ʸ ₁
c⟦ IF {_} {Γ} {σ} ⟧ᵐ           = continuous-constant c⟦ Γ ⟧ᶜ c⟦ ② ⇨ σ ⇨ σ ⇨ σ ⟧ʸ (continuous-if c⟦ σ ⟧ʸ)
c⟦ ZERO {_} {Γ} ⟧ᵐ             = continuous-constant c⟦ Γ ⟧ᶜ c⟦ Ⓝ ⟧ʸ 0
c⟦ SUCC {_} {Γ} ⟧ᵐ             = continuous-constant c⟦ Γ ⟧ᶜ c⟦ Ⓝ ⇨ Ⓝ ⟧ʸ continuous-succ
c⟦ REC {_} {Γ} {σ} ⟧ᵐ          = continuous-constant c⟦ Γ ⟧ᶜ c⟦ σ ⇨ (Ⓝ ⇨ σ ⇨ σ) ⇨ Ⓝ ⇨ σ ⟧ʸ (continuous-rec c⟦ σ ⟧ʸ)
c⟦ PAIR {_} {Γ} {σ} {τ} M N ⟧ᵐ = continuous-pair c⟦ Γ ⟧ᶜ c⟦ σ ⟧ʸ c⟦ τ ⟧ʸ c⟦ M ⟧ᵐ c⟦ N ⟧ᵐ
c⟦ PRJ₁ {_} {Γ} {σ} {τ} W ⟧ᵐ   = continuous-pr₁ c⟦ Γ ⟧ᶜ c⟦ σ ⟧ʸ c⟦ τ ⟧ʸ c⟦ W ⟧ᵐ
c⟦ PRJ₂ {_} {Γ} {σ} {τ} W ⟧ᵐ   = continuous-pr₂ c⟦ Γ ⟧ᶜ c⟦ σ ⟧ʸ c⟦ τ ⟧ʸ c⟦ W ⟧ᵐ
c⟦ LAM {_} {Γ} {σ} {τ} M ⟧ᵐ    = continuous-λ c⟦ Γ ⟧ᶜ c⟦ σ ⟧ʸ c⟦ τ ⟧ʸ c⟦ M ⟧ᵐ
c⟦ _·_ {_} {Γ} {σ} {τ} M N ⟧ᵐ  = continuous-app c⟦ Γ ⟧ᶜ c⟦ σ ⟧ʸ c⟦ τ ⟧ʸ c⟦ M ⟧ᵐ c⟦ N ⟧ᵐ

\end{code}

Intepretations in sets

\begin{code}

s⟦_⟧ʸ : Ty → Set
s⟦ ② ⟧ʸ = 𝟚
s⟦ Ⓝ ⟧ʸ = ℕ
s⟦ σ ⊠ τ ⟧ʸ = s⟦ σ ⟧ʸ × s⟦ τ ⟧ʸ
s⟦ σ ⇨ τ ⟧ʸ = s⟦ σ ⟧ʸ → s⟦ τ ⟧ʸ

s⟦_⟧ᶜ : {n : ℕ} → Cxt n → Set
s⟦ ε ⟧ᶜ = 𝟙
s⟦ Γ ₊ A ⟧ᶜ = s⟦ Γ ⟧ᶜ × s⟦ A ⟧ʸ

prj : {n : ℕ}{Γ : Cxt n}(i : Fin n) → s⟦ Γ ⟧ᶜ → s⟦ Γ [ i ] ⟧ʸ
prj {zero}   {ε}     ()
prj {succ n} {Γ ₊ σ}  zero    (xs , x) = x
prj {succ n} {Γ ₊ σ} (succ i) (xs , x) = prj i xs

s⟦_⟧ᵐ : {n : ℕ}{Γ : Cxt n}{σ : Ty} → Tm Γ σ → s⟦ Γ ⟧ᶜ → s⟦ σ ⟧ʸ
s⟦ VAR i ⟧ᵐ ρ    = prj i ρ
s⟦ ⊥ ⟧ᵐ ρ        = ₀
s⟦ ⊤ ⟧ᵐ ρ        = ₁
s⟦ IF ⟧ᵐ ρ       = if
s⟦ ZERO ⟧ᵐ ρ     = zero
s⟦ SUCC ⟧ᵐ ρ     = succ
s⟦ REC ⟧ᵐ ρ      = ℕ-induction
s⟦ PAIR t u ⟧ᵐ ρ = (s⟦ t ⟧ᵐ ρ , s⟦ u ⟧ᵐ ρ)
s⟦ PRJ₁ w ⟧ᵐ ρ   = pr₁ (s⟦ w ⟧ᵐ ρ)
s⟦ PRJ₂ w ⟧ᵐ ρ   = pr₂ (s⟦ w ⟧ᵐ ρ)
s⟦ LAM t ⟧ᵐ ρ    = λ x → s⟦ t ⟧ᵐ (ρ , x)
s⟦ t · u ⟧ᵐ ρ    = s⟦ t ⟧ᵐ ρ (s⟦ u ⟧ᵐ ρ)

T-definable : (₂ℕ → ℕ) → Set
T-definable f = Σ \(t : Tm ε ((Ⓝ ⇨ ②) ⇨ Ⓝ)) → s⟦ t ⟧ᵐ ⋆ ＝ f

\end{code}

A logical relation over the two interpretations

\begin{code}

_R_ : {σ : Ty} → s⟦ σ ⟧ʸ → U c⟦ σ ⟧ʸ → Set
_R_ {②}     b       b'       = b ＝ b'
_R_ {Ⓝ}     n       n'       = n ＝ n'
_R_ {σ ⊠ τ} (x , y) (x' , y') = (x R x') × (y R y')
_R_ {σ ⇨ τ}  f       f'       = ∀(x : s⟦ σ ⟧ʸ)(x' : U c⟦ σ ⟧ʸ) → x R x' → (f x) R (pr₁ f' x')

_Rᶜ_ : {n : ℕ}{Γ : Cxt n} → s⟦ Γ ⟧ᶜ → U c⟦ Γ ⟧ᶜ → Set
_Rᶜ_ {zero}   {ε}      ⋆       ⋆        = 𝟙
_Rᶜ_ {succ n} {Γ ₊ σ} (ρ , x) (ρ' , x') = (ρ Rᶜ ρ') × (x R x')

Lemma[Rᶜ-prj] : {n : ℕ}{Γ : Cxt n}
              → ∀(ρ : s⟦ Γ ⟧ᶜ)(ρ' : U c⟦ Γ ⟧ᶜ) → ρ Rᶜ ρ'
              → ∀ i → (prj i ρ) R (pr₁ (continuous-prj Γ i) ρ')
Lemma[Rᶜ-prj] {zero}   {ε}     _ _ _ ()
Lemma[Rᶜ-prj] {succ n} {Γ ₊ σ} (ρ , x) (ρ' , x') (rs , r)  zero    = r
Lemma[Rᶜ-prj] {succ n} {Γ ₊ σ} (ρ , x) (ρ' , x') (rs , r) (succ i) = Lemma[Rᶜ-prj] ρ ρ' rs i

_Rᵐ_ : {σ : Ty}{n : ℕ}{Γ : Cxt n}
     → (s⟦ Γ ⟧ᶜ → s⟦ σ ⟧ʸ) → Map c⟦ Γ ⟧ᶜ c⟦ σ ⟧ʸ → Set
f Rᵐ f' = ∀ ρ ρ' → ρ Rᶜ ρ' → (f ρ) R (pr₁ f' ρ')

Lemma[s⟦t⟧ᵐRc⟦t⟧ᵐ] : {n : ℕ}{σ : Ty}{Γ : Cxt n}
                  → ∀(t : Tm Γ σ) → s⟦ t ⟧ᵐ Rᵐ c⟦ t ⟧ᵐ
Lemma[s⟦t⟧ᵐRc⟦t⟧ᵐ] (VAR i) ρ ρ' r = Lemma[Rᶜ-prj] ρ ρ' r i
Lemma[s⟦t⟧ᵐRc⟦t⟧ᵐ] ⊥ _ _ _ = refl
Lemma[s⟦t⟧ᵐRc⟦t⟧ᵐ] ⊤ _ _ _ = refl
Lemma[s⟦t⟧ᵐRc⟦t⟧ᵐ] (IF {n} {Γ} {σ}) ρ ρ' r = claim
 where
  claim : s⟦ IF {n} {Γ} {σ} ⟧ᵐ ρ R pr₁ c⟦ IF {n} {Γ} {σ} ⟧ᵐ ρ'
  claim ₀ ₀ refl _ _ rx _ _ ry = rx
  claim ₀ ₁ ()
  claim ₁ ₀ ()
  claim ₁ ₁ refl _ _ rx _ _ ry = ry
Lemma[s⟦t⟧ᵐRc⟦t⟧ᵐ] ZERO _ _ _ = refl
Lemma[s⟦t⟧ᵐRc⟦t⟧ᵐ] SUCC _ _ _ _ _ rn = ap succ rn
Lemma[s⟦t⟧ᵐRc⟦t⟧ᵐ] (REC {n} {Γ} {σ}) ρ ρ' r = claim
 where
  claim : s⟦ REC {n} {Γ} {σ} ⟧ᵐ ρ R pr₁ c⟦ REC {n} {Γ} {σ} ⟧ᵐ ρ'
  claim _ _ rx _ _  rf  0        0        _  = rx
  claim _ _ rx _ _  rf  0       (succ _)  ()
  claim _ _ rx _ _  rf (succ _)  0        ()
  claim _ _ rx f f' rf (succ m) (succ m') rm =
      rf m m' (ap pred rm) _ _ (claim _ _ rx f f' rf m m' (ap pred rm))
Lemma[s⟦t⟧ᵐRc⟦t⟧ᵐ] (PAIR t u) ρ ρ' r =
    Lemma[s⟦t⟧ᵐRc⟦t⟧ᵐ] t ρ ρ' r , Lemma[s⟦t⟧ᵐRc⟦t⟧ᵐ] u ρ ρ' r
Lemma[s⟦t⟧ᵐRc⟦t⟧ᵐ] (PRJ₁ w) ρ ρ' r = pr₁ (Lemma[s⟦t⟧ᵐRc⟦t⟧ᵐ] w ρ ρ' r)
Lemma[s⟦t⟧ᵐRc⟦t⟧ᵐ] (PRJ₂ w) ρ ρ' r = pr₂ (Lemma[s⟦t⟧ᵐRc⟦t⟧ᵐ] w ρ ρ' r)
Lemma[s⟦t⟧ᵐRc⟦t⟧ᵐ] (LAM t) ρ ρ' r x x' rx =
    Lemma[s⟦t⟧ᵐRc⟦t⟧ᵐ] t (ρ , x) (ρ' , x') (r , rx)
Lemma[s⟦t⟧ᵐRc⟦t⟧ᵐ] (t · u) ρ ρ' r =
    Lemma[s⟦t⟧ᵐRc⟦t⟧ᵐ] t ρ ρ' r (s⟦ u ⟧ᵐ ρ) (pr₁ c⟦ u ⟧ᵐ ρ') (Lemma[s⟦t⟧ᵐRc⟦t⟧ᵐ] u ρ ρ' r)

\end{code}

All T-definable functions ₂ℕ → ℕ are uniformly continuous

\begin{code}

uniformly-continuous : (₂ℕ → ℕ) → Set
uniformly-continuous f = locally-constant f

Theorem[T-definable-UC] : ∀(f : ₂ℕ → ℕ) → T-definable f → uniformly-continuous f
Theorem[T-definable-UC] f (F , e) = n , prf , min
 where
  f' : Map (ℕSpace ⇒ 𝟚Space) ℕSpace
  f' = pr₁ c⟦ F ⟧ᵐ ⋆
  claim₀ : f R f'
  claim₀ = transport (λ x → x R f') e (Lemma[s⟦t⟧ᵐRc⟦t⟧ᵐ] F ⋆ ⋆ ⋆)
  g : ₂ℕ → ℕ
  g = pr₁ (Lemma[Yoneda] ℕSpace f')
  ucg : uniformly-continuous g
  ucg = pr₂ (Lemma[Yoneda] ℕSpace f')
  n : ℕ
  n = pr₁ ucg
  claim₁ : ∀(α : ₂ℕ) → f α ＝ g α
  claim₁ α = claim₀ α ᾱ αRᾱ
   where
    ᾱ : Map ℕSpace 𝟚Space
    ᾱ = α , Lemma[discrete-ℕSpace] 𝟚Space α
    αRᾱ : α R ᾱ
    αRᾱ n .n refl = refl
  prf : ∀(α β : ₂ℕ) → α ＝⟦ n ⟧ β → f α ＝ f β
  prf α β en = (claim₁ α) ∙ (pr₁(pr₂ ucg) α β en) ∙ (claim₁ β)⁻¹
  min : ∀ m → (∀(α β : ₂ℕ) → α ＝⟦ m ⟧ β → f α ＝ f β) → n ≤ m
  min m prm = pr₂(pr₂ ucg) m (λ α β em → (claim₁ α)⁻¹ ∙ (prm α β em) ∙ (claim₁ β))

\end{code}
