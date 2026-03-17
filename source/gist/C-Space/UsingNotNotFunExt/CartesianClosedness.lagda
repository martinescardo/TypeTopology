Chuangjie Xu 2013 (updated in February 2015, ported to TypeTopology in 2025)

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt using (DN-funext)

module gist.C-Space.UsingNotNotFunExt.CartesianClosedness (dnfe : ¬¬ (DN-funext 𝓤₀ 𝓤₀)) where

open import UF.Base

open import gist.C-Space.Preliminaries.Sequence
open import gist.C-Space.Preliminaries.DoubleNegation
open import gist.C-Space.Preliminaries.NotNotFunExt dnfe
open import gist.C-Space.UniformContinuity
open import gist.C-Space.Coverage
open import gist.C-Space.UsingNotNotFunExt.Space

\end{code}

The terminal C-space

\begin{code}

𝟙Space : Space
𝟙Space = 𝟙 , P , c₀ , c₁ , c₂ , c₃
 where
  P : (₂ℕ → 𝟙) → Set
  P p = 𝟙
  c₀ : ∀ x → (λ α → x) ∈ P
  c₀ _ = ⋆
  c₁ : ∀ t → t ∈ C → ∀ p → p ∈ P → p ∘ t ∈ P
  c₁ _ _ _ _ = ⋆
  c₂ : ∀ p → (Σ n ꞉ ℕ , ∀(s : ₂Fin n) → p ∘ cons s ∈ P) → p ∈ P
  c₂ _ _ = ⋆
  c₃ : ∀ p q → p ∈ P → (∀ α → ¬¬ (p α ＝ q α)) → q ∈ P
  c₃ _ _ _ _ = ⋆

continuous-unit : (A : Space) → Map A 𝟙Space
continuous-unit A = unique-to-𝟙 , (λ p _ → ⋆)

\end{code}

Binary product of C-spaces

\begin{code}

infixl 3 _⊗_

_⊗_ : Space → Space → Space
(X , P , pc₀ , pc₁ , pc₂ , pc₃) ⊗ (Y , Q , qc₀ , qc₁ , qc₂ , qc₃) =
     (X × Y) , R , rc₀ , rc₁ , rc₂ , rc₃
 where
  R : (₂ℕ → X × Y) → Set
  R r = ((pr₁ ∘ r) ∈ P) × ((pr₂ ∘ r) ∈ Q)

  rc₀ : ∀ w → (λ α → w) ∈ R
  rc₀ (x , y) = c₀ , c₁
   where
    c₀ : (λ α → x) ∈ P
    c₀ = pc₀ x
    c₁ : (λ α → y) ∈ Q
    c₁ = qc₀ y

  rc₁ : ∀ t → t ∈ C → ∀ r → r ∈ R → r ∘ t ∈ R
  rc₁ t uc r rR = c₀ , c₁
   where
    c₀ : pr₁ ∘ (r ∘ t) ∈ P
    c₀ = pc₁ t uc (pr₁ ∘ r) (pr₁ rR)
    c₁ : pr₂ ∘ (r ∘ t) ∈ Q
    c₁ = qc₁ t uc (pr₂ ∘ r) (pr₂ rR)

  rc₂ : ∀ r → (Σ n ꞉ ℕ , ∀(s : ₂Fin n) → r ∘ cons s ∈ R) → r ∈ R
  rc₂ r (n , prf) = c₀ , c₁
   where
    c₀ : pr₁ ∘ r ∈ P
    c₀ = pc₂ (pr₁ ∘ r) (n , (λ s → pr₁(prf s)))
    c₁ : pr₂ ∘ r ∈ Q
    c₁ = qc₂ (pr₂ ∘ r) (n , (λ s → pr₂(prf s)))

  rc₃ : ∀ r r' → r ∈ R → (∀ α → ¬¬ (r α ＝ r' α)) → r' ∈ R
  rc₃ r r' rR ex = c₀ , c₁
   where
    c₀ : pr₁ ∘ r' ∈ P
    c₀ = pc₃ _ _ (pr₁ rR) (λ α → ¬¬ap pr₁ (ex α))
    c₁ : pr₂ ∘ r' ∈ Q
    c₁ = qc₃ _ _ (pr₂ rR) (λ α → ¬¬ap pr₂ (ex α))

\end{code}

Exponential of C-spaces

\begin{code}

infixr 3 _⇒_

_⇒_ : Space → Space → Space
X ⇒ Y = Map X Y , R , rc₀ , rc₁ , rc₂ , rc₃
 where
  R : (₂ℕ → Map X Y) → Set
  R r = ∀ p → p ∈ Probe X → ∀ t → t ∈ C → (λ α → pr₁(r(t α))(p α)) ∈ Probe Y

  rc₀ : ∀(φ : Map X Y) → (λ α → φ) ∈ R
  rc₀ (φ , cφ) p pP t uc = cφ p pP

  rc₁ : ∀ t → t ∈ C → ∀(r : ₂ℕ → Map X Y) → r ∈ R → r ∘ t ∈ R
  rc₁ t uc r rR p pP t' uc' = rR p pP (t ∘ t') (Lemma[∘-UC] t uc t' uc')

  rc₂ : ∀(r : ₂ℕ → Map X Y) →
         (Σ n ꞉ ℕ , ∀(s : ₂Fin n) → r ∘ cons s ∈ R) → r ∈ R
  rc₂ r (n , ps) p pP t uc = cond₂ Y (λ α → pr₁(r(t α))(p α)) (m , prf)
   where
    m : ℕ
    m = pr₁ (Theorem[Coverage-axiom] n t uc)
    prf : ∀(s : ₂Fin m) → (λ α → pr₁(r(t(cons s α)))(p(cons s α))) ∈ Probe Y
    prf s = cond₃ Y _ _ claim₀ claim₁
     where
      s' : ₂Fin n
      s' = pr₁ (pr₂ (Theorem[Coverage-axiom] n t uc) s)
      t' : ₂ℕ → ₂ℕ
      t' = pr₁ (pr₂ (pr₂ (Theorem[Coverage-axiom] n t uc) s))
      uc' : t' ∈ C
      uc' = pr₁ (pr₂ (pr₂ (pr₂ (Theorem[Coverage-axiom] n t uc) s)))
      ex : ∀(α : ₂ℕ) → t (cons s α) ∼ cons s' (t' α)
      ex = pr₂ (pr₂ (pr₂ (pr₂ (Theorem[Coverage-axiom] n t uc) s)))
      psX : p ∘ cons s ∈ Probe X
      psX = cond₁ X (cons s) (Lemma[cons-UC] s) p pP
      claim₀ : (λ α → pr₁(r(cons s' (t' α)))(p(cons s α))) ∈ Probe Y
      claim₀ = ps s' (p ∘ cons s) psX t' uc'
      claim₁ : ∀(α : ₂ℕ) → ¬¬ (pr₁(r(cons s' (t' α)))(p(cons s α)) ＝
                               pr₁(r(t(cons s α)))(p(cons s α)))
      claim₁ α = ¬¬happly (¬¬ap (pr₁ ∘ r) (¬¬sym e)) (p(cons s α))
       where
        e : ¬¬ (t (cons s α) ＝ cons s' (t' α))
        e = fe (ex α)
           ----

  rc₃ : ∀(r r' : ₂ℕ → Map X Y) → r ∈ R → (∀ α → ¬¬ (r α ＝ r' α)) → r' ∈ R
  rc₃ r r' rR ex p pX t tC = cond₃ Y _ _ (rR p pX t tC) ex'
   where
    ex' : ∀(α : ₂ℕ) → ¬¬ (pr₁(r(t α))(p α) ＝ pr₁(r'(t α))(p α))
    ex' α = ¬¬happly (¬¬ap pr₁ (ex (t α))) (p α)

\end{code}

Universal properties of products and of exponentials

\begin{code}

continuous-pair : (X Y Z : Space)
                → Map X Y → Map X Z → Map X (Y ⊗ Z)
continuous-pair X Y Z (f , cf) (g , cg) = (fg , cfg)
 where
  fg : U X → U (Y ⊗ Z)
  fg x = (f x , g x)
  cfg : continuous X (Y ⊗ Z) fg
  cfg p pX = cf p pX , cg p pX

continuous-pr₁ : (X Y Z : Space) → Map X (Y ⊗ Z) → Map X Y
continuous-pr₁ X Y Z (w , cw) = pr₁ ∘ w , (λ p pX → pr₁ (cw p pX))

continuous-pr₂ : (X Y Z : Space) → Map X (Y ⊗ Z) → Map X Z
continuous-pr₂ X Y Z (w , cw) = pr₂ ∘ w , (λ p pX → pr₂ (cw p pX))

continuous-λ : (X Y Z : Space) → Map (X ⊗ Y) Z → Map X (Y ⇒ Z)
continuous-λ X Y Z (f , cf) = g , cg
 where
  g : U X → U(Y ⇒ Z)
  g x = h , ch
   where
    h : U Y → U Z
    h y = f(x , y)
    ch : continuous Y Z h
    ch q qY = cf r rXY
     where
      r : ₂ℕ → U X × U Y
      r α = (x , q α)
      rXY : r ∈ Probe (X ⊗ Y)
      rXY = cond₀ X x , qY
  cg : continuous X (Y ⇒ Z) g
  cg p pX q qY t uct = cf r rXY
   where
    r : ₂ℕ → U X × U Y
    r α = (p(t α) , q α)
    rXY : r ∈ Probe (X ⊗ Y)
    rXY = cond₁ X t uct p pX , qY

continuous-app : (X Y Z : Space) → Map X (Y ⇒ Z) → Map X Y → Map X Z
continuous-app X Y Z (f , cf) (a , ca) = (fa , cfa)
 where
  fa : U X → U Z
  fa x = pr₁ (f x) (a x)
  cfa : continuous X Z fa
  cfa p pX = cf p pX (a ∘ p) (ca p pX) id Lemma[id-UC]

\end{code}
