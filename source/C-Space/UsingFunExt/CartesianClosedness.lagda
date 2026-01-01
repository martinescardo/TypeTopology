Chuangjie Xu 2012 (updated in February 2015, ported to TypeTopology in 2025)

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt using (naive-funext)

module C-Space.UsingFunExt.CartesianClosedness (fe : naive-funext 𝓤₀ 𝓤₀) where

open import C-Space.Preliminaries.Sequence
open import C-Space.UniformContinuity
open import C-Space.Coverage
open import C-Space.UsingFunExt.Space

\end{code}

The category of C-spaces is cartesian closed.

The terminal C-space:

\begin{code}

𝟙Space : Space
𝟙Space = 𝟙 , P , c₀ , c₁ , c₂
 where
  P : (₂ℕ → 𝟙) → Set
  P p = 𝟙
  c₀ : ∀(x : 𝟙) → (λ α → x) ∈ P
  c₀ _ = ⋆
  c₁ : ∀(t : ₂ℕ → ₂ℕ) → t ∈ C → ∀(p : ₂ℕ → 𝟙) → p ∈ P → p ∘ t ∈ P
  c₁ _ _ _ _ = ⋆
  c₂ : ∀(p : ₂ℕ → 𝟙) → (Σ \(n : ℕ) → ∀(s : ₂Fin n) → (p ∘ (cons s)) ∈ P) → p ∈ P
  c₂ _ _ = ⋆

continuous-unit : (A : Space) → Map A 𝟙Space
continuous-unit A = unique-to-𝟙 , (λ p _ → ⋆)

\end{code}

Binary product of C-spaces:

\begin{code}

infixl 3 _⊗_

_⊗_ : Space → Space → Space
(X , P , pc₀ , pc₁ , pc₂) ⊗ (Y , Q , qc₀ , qc₁ , qc₂) = (X × Y) , R , rc₀ , rc₁ , rc₂
 where
  R : (₂ℕ → X × Y) → Set
  R r = ((pr₁ ∘ r) ∈ P) × ((pr₂ ∘ r) ∈ Q)

  rc₀ : ∀(w : X × Y) → (λ α → w) ∈ R
  rc₀ (x , y) = c₀ , c₁
   where
    c₀ : (λ α → x) ∈ P
    c₀ = pc₀ x
    c₁ : (λ α → y) ∈ Q
    c₁ = qc₀ y

  rc₁ : ∀(t : ₂ℕ → ₂ℕ) → t ∈ C → ∀(r : ₂ℕ → X × Y) →  r ∈ R → r ∘ t ∈ R
  rc₁ t uc r rR = c₀ , c₁
   where
    c₀ : pr₁ ∘ (r ∘ t) ∈ P
    c₀ = pc₁ t uc (pr₁ ∘ r) (pr₁ rR)
    c₁ : pr₂ ∘ (r ∘ t) ∈ Q
    c₁ = qc₁ t uc (pr₂ ∘ r) (pr₂ rR)

  rc₂ : ∀(r : ₂ℕ → X × Y) → (Σ \(n : ℕ) → ∀(s : ₂Fin n) → (r ∘ (cons s)) ∈ R) → r ∈ R
  rc₂ r (n , prf) = c₀ , c₁
   where
    c₀ : pr₁ ∘ r ∈ P
    c₀ = pc₂ (pr₁ ∘ r) (n , (λ s → pr₁(prf s)))
    c₁ : pr₂ ∘ r ∈ Q
    c₁ = qc₂ (pr₂ ∘ r) (n , (λ s → pr₂(prf s)))

\end{code}

Exponential of C-spaces

\begin{code}

infixr 3 _⇒_

_⇒_ : Space → Space → Space
X ⇒ Y = Map X Y , R , rc₀ , rc₁ , rc₂
 where
  R : (₂ℕ → Map X Y) → Set
  R r = ∀(p : ₂ℕ → U X) → p ∈ Probe X → ∀(t : ₂ℕ → ₂ℕ) → t ∈ C →
         (λ α → (pr₁ ∘ r)(t α)(p α)) ∈ Probe Y

  rc₀ : ∀(φ : Map X Y) → (λ α → φ) ∈ R
  rc₀ (φ , cφ) p pP t uc = cφ p pP

  rc₁ : ∀(t : ₂ℕ → ₂ℕ) → t ∈ C → ∀(r : ₂ℕ → Map X Y) → r ∈ R → r ∘ t ∈ R
  rc₁ t uc r rR p pP t' uc' = rR p pP (t ∘ t') (Lemma[∘-UC] t uc t' uc')

  rc₂ : ∀(r : ₂ℕ → Map X Y) →
         (Σ \(n : ℕ) → ∀(s : ₂Fin n) → (r ∘ (cons s)) ∈ R) → r ∈ R
  rc₂ r (n , ps) p pP t uc = cond₂ Y (λ α → (pr₁ ∘ r)(t α)(p α)) (m , prf)
   where
    m : ℕ
    m = pr₁ (Theorem[Coverage-axiom] n t uc)
    prf : ∀(s : ₂Fin m) → (λ α → (pr₁ ∘ r)(t(cons s α))(p(cons s α))) ∈ Probe Y
    prf s = transport (λ x → (λ α → (pr₁ ∘ r)(x α)(p(cons s α))) ∈ Probe Y) eq claim
     where
      s' : ₂Fin n
      s' = pr₁ (pr₂ (Theorem[Coverage-axiom] n t uc) s)
      t' : ₂ℕ → ₂ℕ
      t' = pr₁ (pr₂ (pr₂ (Theorem[Coverage-axiom] n t uc) s))
      uc' : t' ∈ C
      uc' = pr₁ (pr₂ (pr₂ (pr₂ (Theorem[Coverage-axiom] n t uc) s)))
      ex : ∀ α → t (cons s α) ∼ cons s' (t' α)
      ex = pr₂ (pr₂ (pr₂ (pr₂ (Theorem[Coverage-axiom] n t uc) s)))
      eq : cons s' ∘ t' ＝ t ∘ cons s 
      eq = (fe (λ α → fe (ex α)))⁻¹
           ----      ----
      psinP : (p ∘ (cons s)) ∈ Probe X
      psinP = cond₁ X (cons s) (Lemma[cons-UC] s) p pP
      claim : (λ α → (pr₁ ∘ r)(cons s' (t' α))(p(cons s α))) ∈ Probe Y
      claim = ps s' (p ∘ (cons s)) psinP t' uc'

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

cpr₁ : (X Y : Space) → Map (X ⊗ Y) X
cpr₁ X Y = pr₁ , (λ _ → pr₁)

cpr₂ : (X Y : Space) → Map (X ⊗ Y) Y
cpr₂ X Y = pr₂ , (λ _ → pr₂)

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

Arbitrary product of C-spaces

\begin{code}

∏ : {I : Set} → (I → Space) → Space
∏ {I} X = A , P , c₀ , c₁ , c₂
 where
  A : Set
  A = (i : I) → U(X i)
  π : (i : I) → A → U(X i)
  π i a = a i

  P : (₂ℕ → A) → Set
  P p = ∀(i : I) → (π i) ∘ p ∈ Probe (X i)

  c₀ : ∀(a : A) → (λ α → a) ∈ P
  c₀ a i = cond₀ (X i) (a i)

  c₁ : ∀(t : ₂ℕ → ₂ℕ) → t ∈ C → ∀(p : ₂ℕ → A) → p ∈ P → p ∘ t ∈ P
  c₁ t uc p pP i = cond₁ (X i) t uc ((π i) ∘ p) (pP i)

  c₂ : ∀(p : ₂ℕ → A) → (Σ \(n : ℕ) → ∀(s : ₂Fin n) → (p ∘ (cons s)) ∈ P) → p ∈ P
  c₂ p (n , pr) i = cond₂ (X i) ((π i) ∘ p) (n , λ s → pr s i)


continuous-π : {I : Set} → (X : I → Space) → (i : I) → Map (∏ X) (X i)
continuous-π {I} X i = π , cts
 where
  π : U(∏ X) → U(X i)
  π w = w i
  cts : continuous (∏ X) (X i) π
  cts p pX = pX i


universal-property-∏ :
    {I : Set} → ∀(X : I → Space) →
    ∀(Y : Space) → ∀(f : (i : I) → Map Y (X i)) →
    Σ \(g : Map Y (∏ X)) →
      ∀(i : I) → ∀(y : U Y) → pr₁(continuous-π X i)(pr₁ g y) ＝ pr₁ (f i) y
universal-property-∏ {I} X Y f = (g , cg) , (λ _ _ → refl)
 where
  g : U Y → U(∏ X)
  g y i = pr₁ (f i) y
  cg : continuous Y (∏ X) g
  cg q qY i = pr₂ (f i) q qY

\end{code}
