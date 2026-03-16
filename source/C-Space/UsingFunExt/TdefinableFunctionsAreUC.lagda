Chuangjie Xu 2013 (updated in February 2015, ported to TypeTopology in 2025)

This module shows that every closed System T term of type `(Ⓝ ⇨ ②) ⇨ Ⓝ`
defines a uniformly continuous function on Cantor space.

The proof compares two semantics of System T:
- the ordinary set-theoretic interpretation, which yields the function computed
  by a term, and
- the interpretation in C-spaces, where continuity information is built into
  the semantics.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt using (DN-funext)

module C-Space.UsingFunExt.TdefinableFunctionsAreUC (fe : DN-funext 𝓤₀ 𝓤₀) where

open import Naturals.Properties

open import C-Space.Preliminaries.Booleans.Functions using (if)
open import C-Space.Preliminaries.Naturals.Order
open import C-Space.Preliminaries.Sequence
open import C-Space.UniformContinuity
open import C-Space.Coverage
open import C-Space.Syntax.SystemT
open import C-Space.UsingFunExt.Space
open import C-Space.UsingFunExt.CartesianClosedness fe
open import C-Space.UsingFunExt.DiscreteSpace fe
open import C-Space.UsingFunExt.YonedaLemma fe
open import C-Space.UsingFunExt.Fan fe

\end{code}

Interpretation of System T in C-spaces

This is the semantic interpretation used to obtain continuity information from
the C-space model.

\begin{code}

c⟦_⟧ʸ : Ty → Space
c⟦ ② ⟧ʸ = 𝟚Space
c⟦ Ⓝ ⟧ʸ = ℕSpace
c⟦ σ ⊠ τ ⟧ʸ = c⟦ σ ⟧ʸ ⊗ c⟦ τ ⟧ʸ
c⟦ σ ⇨ τ ⟧ʸ = c⟦ σ ⟧ʸ ⇒ c⟦ τ ⟧ʸ

c⟦_⟧ᶜ : Cxt → Space
c⟦ ε ⟧ᶜ = 𝟙Space
c⟦ Γ ₊ A ⟧ᶜ = c⟦ Γ ⟧ᶜ ⊗ c⟦ A ⟧ʸ

-- Semantic projection associated to a de Bruijn variable.
continuous-prj : (Γ : Cxt)(i : Fin (length Γ)) → Map c⟦ Γ ⟧ᶜ c⟦ Γ [ i ] ⟧ʸ
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


c⟦_⟧ᵐ : {Γ : Cxt}{σ : Ty} → Tm Γ σ → Map c⟦ Γ ⟧ᶜ c⟦ σ ⟧ʸ
c⟦ VAR {Γ} i ⟧ᵐ            = continuous-prj Γ i
c⟦ ⊥ {Γ} ⟧ᵐ                = continuous-constant c⟦ Γ ⟧ᶜ c⟦ ② ⟧ʸ ₀
c⟦ ⊤ {Γ} ⟧ᵐ                = continuous-constant c⟦ Γ ⟧ᶜ c⟦ ② ⟧ʸ ₁
c⟦ IF {Γ} {σ} ⟧ᵐ           = continuous-constant c⟦ Γ ⟧ᶜ c⟦ ② ⇨ σ ⇨ σ ⇨ σ ⟧ʸ (continuous-if c⟦ σ ⟧ʸ)
c⟦ ZERO {Γ} ⟧ᵐ             = continuous-constant c⟦ Γ ⟧ᶜ c⟦ Ⓝ ⟧ʸ 0
c⟦ SUCC {Γ} ⟧ᵐ             = continuous-constant c⟦ Γ ⟧ᶜ c⟦ Ⓝ ⇨ Ⓝ ⟧ʸ continuous-succ
c⟦ REC {Γ} {σ} ⟧ᵐ          = continuous-constant c⟦ Γ ⟧ᶜ c⟦ σ ⇨ (Ⓝ ⇨ σ ⇨ σ) ⇨ Ⓝ ⇨ σ ⟧ʸ (continuous-rec c⟦ σ ⟧ʸ)
c⟦ PAIR {Γ} {σ} {τ} M N ⟧ᵐ = continuous-pair c⟦ Γ ⟧ᶜ c⟦ σ ⟧ʸ c⟦ τ ⟧ʸ c⟦ M ⟧ᵐ c⟦ N ⟧ᵐ
c⟦ PRJ₁ {Γ} {σ} {τ} W ⟧ᵐ   = continuous-pr₁ c⟦ Γ ⟧ᶜ c⟦ σ ⟧ʸ c⟦ τ ⟧ʸ c⟦ W ⟧ᵐ
c⟦ PRJ₂ {Γ} {σ} {τ} W ⟧ᵐ   = continuous-pr₂ c⟦ Γ ⟧ᶜ c⟦ σ ⟧ʸ c⟦ τ ⟧ʸ c⟦ W ⟧ᵐ
c⟦ LAM {Γ} {σ} {τ} M ⟧ᵐ    = continuous-λ c⟦ Γ ⟧ᶜ c⟦ σ ⟧ʸ c⟦ τ ⟧ʸ c⟦ M ⟧ᵐ
c⟦ _·_ {Γ} {σ} {τ} M N ⟧ᵐ  = continuous-app c⟦ Γ ⟧ᶜ c⟦ σ ⟧ʸ c⟦ τ ⟧ʸ c⟦ M ⟧ᵐ c⟦ N ⟧ᵐ

\end{code}

Interpretation of System T in sets

This is the ordinary extensional semantics of System T.

\begin{code}

s⟦_⟧ʸ : Ty → Set
s⟦ ② ⟧ʸ = 𝟚
s⟦ Ⓝ ⟧ʸ = ℕ
s⟦ σ ⊠ τ ⟧ʸ = s⟦ σ ⟧ʸ × s⟦ τ ⟧ʸ
s⟦ σ ⇨ τ ⟧ʸ = s⟦ σ ⟧ʸ → s⟦ τ ⟧ʸ

s⟦_⟧ᶜ : Cxt → Set
s⟦ ε ⟧ᶜ = 𝟙
s⟦ Γ ₊ A ⟧ᶜ = s⟦ Γ ⟧ᶜ × s⟦ A ⟧ʸ

prj : {Γ : Cxt}(i : Fin (length Γ)) → s⟦ Γ ⟧ᶜ → s⟦ Γ [ i ] ⟧ʸ
prj {ε}     ()
prj {Γ ₊ σ}  zero    (xs , x) = x
prj {Γ ₊ σ} (succ i) (xs , x) = prj i xs

s⟦_⟧ᵐ : {Γ : Cxt}{σ : Ty} → Tm Γ σ → s⟦ Γ ⟧ᶜ → s⟦ σ ⟧ʸ
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

The relation `R` says that a set-theoretic value and a C-space value represent
the same mathematical object. The fundamental lemma below shows that every term
is related to its two interpretations.

\begin{code}

_R_ : {σ : Ty} → s⟦ σ ⟧ʸ → U c⟦ σ ⟧ʸ → Set
_R_ {②}     b       b'       = b ＝ b'
_R_ {Ⓝ}     n       n'       = n ＝ n'
_R_ {σ ⊠ τ} (x , y) (x' , y') = (x R x') × (y R y')
_R_ {σ ⇨ τ}  f       f'       = ∀(x : s⟦ σ ⟧ʸ)(x' : U c⟦ σ ⟧ʸ) → x R x' → (f x) R (pr₁ f' x')

_Rᶜ_ : {Γ : Cxt} → s⟦ Γ ⟧ᶜ → U c⟦ Γ ⟧ᶜ → Set
_Rᶜ_ {ε}      ⋆       ⋆        = 𝟙
_Rᶜ_ {Γ ₊ σ} (ρ , x) (ρ' , x') = (ρ Rᶜ ρ') × (x R x')

Lemma[Rᶜ-prj] : {Γ : Cxt}
              → ∀(ρ : s⟦ Γ ⟧ᶜ)(ρ' : U c⟦ Γ ⟧ᶜ) → ρ Rᶜ ρ'
              → ∀ i → (prj i ρ) R (pr₁ (continuous-prj Γ i) ρ')
Lemma[Rᶜ-prj] {ε}     _ _ _ ()
Lemma[Rᶜ-prj] {Γ ₊ σ} (ρ , x) (ρ' , x') (rs , r)  zero    = r
Lemma[Rᶜ-prj] {Γ ₊ σ} (ρ , x) (ρ' , x') (rs , r) (succ i) = Lemma[Rᶜ-prj] ρ ρ' rs i

_Rᵐ_ : {σ : Ty}{Γ : Cxt}
     → (s⟦ Γ ⟧ᶜ → s⟦ σ ⟧ʸ) → Map c⟦ Γ ⟧ᶜ c⟦ σ ⟧ʸ → Set
f Rᵐ f' = ∀ ρ ρ' → ρ Rᶜ ρ' → (f ρ) R (pr₁ f' ρ')

Lemma[s⟦t⟧ᵐRc⟦t⟧ᵐ] : {σ : Ty}{Γ : Cxt}
                  → ∀(t : Tm Γ σ) → s⟦ t ⟧ᵐ Rᵐ c⟦ t ⟧ᵐ
Lemma[s⟦t⟧ᵐRc⟦t⟧ᵐ] (VAR i) ρ ρ' r = Lemma[Rᶜ-prj] ρ ρ' r i
Lemma[s⟦t⟧ᵐRc⟦t⟧ᵐ] ⊥ _ _ _ = refl
Lemma[s⟦t⟧ᵐRc⟦t⟧ᵐ] ⊤ _ _ _ = refl
Lemma[s⟦t⟧ᵐRc⟦t⟧ᵐ] (IF {Γ} {σ}) ρ ρ' r = claim
 where
  claim : s⟦ IF {Γ} {σ} ⟧ᵐ ρ R pr₁ c⟦ IF {Γ} {σ} ⟧ᵐ ρ'
  claim ₀ ₀ refl _ _ rx _ _ ry = rx
  claim ₀ ₁ ()
  claim ₁ ₀ ()
  claim ₁ ₁ refl _ _ rx _ _ ry = ry
Lemma[s⟦t⟧ᵐRc⟦t⟧ᵐ] ZERO _ _ _ = refl
Lemma[s⟦t⟧ᵐRc⟦t⟧ᵐ] SUCC _ _ _ _ _ rn = ap succ rn
Lemma[s⟦t⟧ᵐRc⟦t⟧ᵐ] (REC {Γ} {σ}) ρ ρ' r = claim
 where
  claim : s⟦ REC {Γ} {σ} ⟧ᵐ ρ R pr₁ c⟦ REC {Γ} {σ} ⟧ᵐ ρ'
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

For a closed term `F`, the C-space interpretation gives a continuous map
`f' : Map (ℕSpace ⇒ 𝟚Space) ℕSpace`. By Yoneda this corresponds to a uniformly
continuous function `g : ₂ℕ → ℕ`. The logical relation shows that the original
set-theoretic function `f` agrees pointwise with `g`, so `f` inherits the same
least modulus of uniform continuity.

\begin{code}

uniformly-continuous : (₂ℕ → ℕ) → Set
uniformly-continuous f = locally-constant f

Theorem[T-definable-UC] : ∀(f : ₂ℕ → ℕ) → T-definable f → uniformly-continuous f
Theorem[T-definable-UC] f (F , e) = n , prf , min
 where
  -- `f'` is the interpretation of the closed term `F` in the C-space model.
  f' : Map (ℕSpace ⇒ 𝟚Space) ℕSpace
  f' = pr₁ c⟦ F ⟧ᵐ ⋆
  claim₀ : f R f'
  claim₀ = transport (λ x → x R f') e (Lemma[s⟦t⟧ᵐRc⟦t⟧ᵐ] F ⋆ ⋆ ⋆)
  -- Yoneda turns the C-space map into an ordinary uniformly continuous
  -- function on Cantor space.
  g : ₂ℕ → ℕ
  g = pr₁ (Lemma[Yoneda] ℕSpace f')
  ucg : uniformly-continuous g
  ucg = pr₂ (Lemma[Yoneda] ℕSpace f')
  n : ℕ
  n = pr₁ ucg
  -- The logical relation identifies the original function `f` with `g`
  -- pointwise.
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
