Chuangjie Xu 2013 (ported to TypeTopology in 2025)

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt using (naive-funext)

module C-Spaces.UsingFunExt.LocalCartesianClosedness (fe : naive-funext 𝓤₀ 𝓤₀) where

open import C-Spaces.Preliminaries.Sequence
open import C-Spaces.UniformContinuity
open import C-Spaces.Coverage
open import C-Spaces.UsingFunExt.Space
open import C-Spaces.UsingFunExt.CartesianClosedness fe

\end{code}

Subspace

\begin{code}

Subspace : (X : Space) → (U X → Set) → Space
Subspace X Prp = A , R , rc₀ , rc₁ , rc₂
 where
  A : Set
  A = Σ \(x : U X) → Prp x
  R : (₂ℕ → A) → Set
  R r = pr₁ ∘ r ∈ Probe X
  rc₀ : ∀(a : A) → (λ α → a) ∈ R
  rc₀ (x , _) = cond₀ X x
  rc₁ : ∀(t : ₂ℕ → ₂ℕ) → t ∈ C → ∀(r : ₂ℕ → A) → r ∈ R → r ∘ t ∈ R
  rc₁ t uc r rR = cond₁ X t uc (pr₁ ∘ r) rR
  rc₂ : ∀(r : ₂ℕ → A) → (Σ \(n : ℕ) → ∀(s : ₂Fin n) → (r ∘ (cons s)) ∈ R) → r ∈ R
  rc₂ r pr = cond₂ X (pr₁ ∘ r) pr

cts-incl : (X : Space) → (Prp : U X → Set) → Map (Subspace X Prp) X
cts-incl X Prp = pr₁ , (λ r rR → rR)

\end{code}

C-spaces have all pullbacks.

\begin{code}

_×[_]_⟨_,_⟩ : (X Z Y : Space) → Map X Z → Map Y Z → Space
X ×[ Z ] Y ⟨ f , g ⟩ = Subspace (X ⊗ Y) Prp
 where
  Prp : U (X ⊗ Y) → Set
  Prp (x , y) = pr₁ f x ＝ pr₁ g y

⟪_×[_]_⟨_,_⟩⟫-pr₁ : (X Z Y : Space) → (f : Map X Z) → (g : Map Y Z) → 
                   Map (X ×[ Z ] Y ⟨ f , g ⟩) X
⟪ X ×[ Z ] Y ⟨ f , g ⟩⟫-pr₁ = (pr₁ ∘ pr₁) , λ r rR → pr₁ rR

⟪_×[_]_⟨_,_⟩⟫-pr₂ : (X Z Y : Space) → (f : Map X Z) → (g : Map Y Z) → 
                   Map (X ×[ Z ] Y ⟨ f , g ⟩) Y
⟪ X ×[ Z ] Y ⟨ f , g ⟩⟫-pr₂ = (pr₂ ∘ pr₁) , λ r rR → pr₂ rR

\end{code}

Equalizers are calculated in the same way as above.

\begin{code}

⟪_,_⟫Eq₍_,_₎ : (X Y : Space) → Map X Y → Map X Y → Space
⟪ X , Y ⟫Eq₍ f , g ₎ = Subspace X Prp
 where
  Prp : U X → Set
  Prp x = pr₁ f x ＝ pr₁ g x

\end{code}

Binary products in a slice category are constructed via pullbacks.

\begin{code}

⟪_,_,_⟫_×_ : (X Z Y : Space) → (f : Map X Z) → (g : Map Y Z) → Map (X ×[ Z ] Y ⟨ f , g ⟩) Z
⟪ X , Z , Y ⟫ f × g = h , cts
 where
  h : U (X ×[ Z ] Y ⟨ f , g ⟩) → U Z
  h ((x , y) , e) = pr₁ f x
  cts : continuous (X ×[ Z ] Y ⟨ f , g ⟩) Z h
  cts r rR = pr₂ f (pr₁ ∘ pr₁ ∘ r) (pr₁ rR)

\end{code}

Given a continuous map f : X → Y and y : Y, the fiber f⁻¹(y) is a C-space.

\begin{code}

⟪_,_⟫_⁻¹₍_₎ : (X Y : Space) → Map X Y → U Y → Space
⟪ X , Y ⟫ f ⁻¹₍ y ₎ = Subspace X Prp
 where
  Prp : U X → Set
  Prp x = pr₁ f x ＝ y

\end{code}

An exponential in a slice category C-space/X is constructed in the
same way as in Set/X, with a suitable C-topology on its domain.

\begin{code}

dom⟪_,_,_⟫_^_ : (X Z Y : Space) → Map Y Z → Map X Z → Space
dom⟪ X , Z , Y ⟫ g ^ f = A , R , rc₀ , rc₁ , rc₂
 where
  f⁻¹ : U Z → Space
  f⁻¹ z = ⟪ X , Z ⟫ f ⁻¹₍ z ₎
  g⁻¹ : U Z → Space
  g⁻¹ z = ⟪ Y , Z ⟫ g ⁻¹₍ z ₎
  A : Set
  A = Σ \(z : U Z) → Map (f⁻¹ z) (g⁻¹  z)
  R : (₂ℕ → A) → Set
  R r =  (pr₁ ∘ r ∈ Probe Z)
       × (∀(t : ₂ℕ → ₂ℕ) → t ∈ C → ∀(p : ₂ℕ → U X) → p ∈ Probe X →
           (e : ∀(α : ₂ℕ) → pr₁ f(p α) ＝ pr₁(r(t α))) →
           (λ α → pr₁(pr₁(pr₂(r(t α)))(p α , e α))) ∈ Probe Y)

  lemma : ∀(w₀ w₁ : A) → (u : U ⟪ X , Z ⟫ f ⁻¹₍ pr₁ w₁ ₎) → (e : w₁ ＝ w₀) →
           pr₁(pr₁(pr₂ w₀)(pr₁ u , transport _ e (pr₂ u))) ＝ pr₁(pr₁(pr₂ w₁)u)
  lemma w .w u refl = refl

  rc₀ : ∀(a : A) → (λ α → a) ∈ R
  rc₀ (z , φ , cφ) = c₀ , c₁
   where
    c₀ : (λ α → z) ∈ Probe Z
    c₀ = cond₀ Z z
    c₁ : ∀(t : ₂ℕ → ₂ℕ) → t ∈ C → ∀(p : ₂ℕ → U X) → p ∈ Probe X →
          (e : ∀(α : ₂ℕ) → pr₁ f (p α) ＝ z)
       → (λ α → pr₁ (φ (p α , e α))) ∈ Probe Y
    c₁ t uc p pP e = cφ (λ α → p α , e α) pP

  rc₁ : ∀(t : ₂ℕ → ₂ℕ) → t ∈ C → ∀(r : ₂ℕ → A) → r ∈ R → r ∘ t ∈ R
  rc₁ t uct r rR = c₀ , c₁
   where
    c₀ : pr₁ ∘ r ∘ t ∈ Probe Z
    c₀ = cond₁ Z t uct (pr₁ ∘ r) (pr₁ rR)
    c₁ : ∀(u : ₂ℕ → ₂ℕ) → u ∈ C → ∀(p : ₂ℕ → U X) → p ∈ Probe X →
          (e : ∀(α : ₂ℕ) → pr₁ f(p α) ＝ pr₁(r(t(u α))))
       → (λ α → pr₁(pr₁(pr₂(r(t(u α))))(p α , e α))) ∈ Probe Y
    c₁ u ucu p pP e = pr₂ rR (t ∘ u) (Lemma[∘-UC] t uct u ucu) p pP e

  rc₂ : ∀(r : ₂ℕ → A) → (Σ \(n : ℕ) → ∀(s : ₂Fin n) → (r ∘ (cons s)) ∈ R) → r ∈ R
  rc₂ r (n , pr) = c₀ , c₁
   where
    c₀ : pr₁ ∘ r ∈ Probe Z
    c₀ = cond₂ Z (pr₁ ∘ r) (n , λ s → pr₁ (pr s))
    c₁ : ∀(t : ₂ℕ → ₂ℕ) → t ∈ C → ∀(p : ₂ℕ → U X) → p ∈ Probe X →
          (e : ∀(α : ₂ℕ) → pr₁ f(p α) ＝ pr₁(r(t α)))
       → (λ α → pr₁(pr₁(pr₂(r(t α)))(p α , e α))) ∈ Probe Y
    c₁ t uc p pP e = cond₂ Y (λ α → pr₁(pr₁(pr₂(r(t α)))(p α , e α))) (m , prf)
     where
      m : ℕ
      m = pr₁ (Theorem[Coverage-axiom] n t uc)
      prf : ∀(s : ₂Fin m)
          → (λ α → pr₁(pr₁(pr₂(r(t(cons s α))))(p(cons s α) , e(cons s α)))) ∈ Probe Y
      prf s = transport (Probe Y) claim₂ claim₀
       where
        s' : ₂Fin n
        s' = pr₁ (pr₂ (Theorem[Coverage-axiom] n t uc) s)
        t' : ₂ℕ → ₂ℕ
        t' = pr₁ (pr₂ (pr₂ (Theorem[Coverage-axiom] n t uc) s))
        uc' : t' ∈ C
        uc' = pr₁ (pr₂ (pr₂ (pr₂ (Theorem[Coverage-axiom] n t uc) s)))
        ex : ∀ α → t (cons s α) ∼ cons s' (t' α)
        ex = pr₂ (pr₂ (pr₂ (pr₂ (Theorem[Coverage-axiom] n t uc) s)))
        psinP : (p ∘ (cons s)) ∈ Probe X
        psinP = cond₁ X (cons s) (Lemma[cons-UC] s) p pP
        er : ∀(α : ₂ℕ) → r(t(cons s α)) ＝ r(cons s' (t' α))
        er α = ap r (fe (ex α))
                    ----
        e' : ∀(α : ₂ℕ) → pr₁ f(p(cons s α)) ＝ pr₁(r(cons s' (t' α)))
        e' α = transport (λ a → pr₁ f(p(cons s α)) ＝ pr₁ a) (er α) (e(cons s α))
        claim₀ : (λ α → pr₁(pr₁(pr₂(r(cons s'(t' α))))(p(cons s α) , e' α))) ∈ Probe Y
        claim₀ = pr₂ (pr s') t' uc' (p ∘ (cons s)) psinP e'
        claim₁ : ∀(α : ₂ℕ) → pr₁(pr₁(pr₂(r(cons s'(t' α))))(p(cons s α) , e' α))
                           ＝ pr₁(pr₁(pr₂(r(t(cons s α))))(p(cons s α) , e(cons s α)))
        claim₁ α = lemma (r(cons s' (t' α))) (r(t(cons s α)))
                         (p(cons s α) , e(cons s α)) (er α)
        claim₂ : (λ α → pr₁(pr₁(pr₂(r(cons s'(t' α))))(p(cons s α) , e' α)))
               ＝ (λ α → pr₁(pr₁(pr₂(r(t(cons s α))))(p(cons s α) , e(cons s α))))
        claim₂ = fe claim₁
                ----

⟪_,_,_⟫_^_ : (X Z Y : Space) → (g : Map Y Z) → (f : Map X Z) → Map (dom⟪ X , Z , Y ⟫ g ^ f) Z
⟪ X , Z , Y ⟫ g ^ f = pr₁ , λ r rR → pr₁ rR

\end{code}

Pullback functors:

\begin{code}

⟪_,_⟫_* : (X Y : Space) → (Map X Y) → Mapto Y → Mapto X
⟪ X , Y ⟫ f * (Z , g) = X ×[ Y ] Z ⟨ f , g ⟩ , ⟪ X ×[ Y ] Z ⟨ f , g ⟩⟫-pr₁

\end{code}

Dependent sums (left adjoint) are calculated via composition.

\begin{code}

⟪_,_⟫Σ[_] : (X Y : Space) → Map X Y → Mapto X → Mapto Y
⟪ X , Y ⟫Σ[ f ] (Z , g) = Z , ⟪ Z , X , Y ⟫ f ○ g

dom⟪_,_⟫Σ[_] : (X Y : Space) → Map X Y → Mapto X → Space
dom⟪ X , Y ⟫Σ[ f ] (Z , g) = Z

\end{code}

Dependent products (right adjoint) are via the following diagram

   Π[f](g) -----> (g∘f)^f
     | ⌟             |
     |               | g^f
     |               |
     V               V
    id -----------> f^f.

\begin{code}

dom⟪_,_⟫Π[_] : (X Y : Space) → (Map X Y) → Mapto X → Space
dom⟪ X , Y ⟫Π[ f ] (Z , g) = Subspace A Prp
 where
  f⁻¹ : U Y → Space
  f⁻¹ y = ⟪ X , Y ⟫ f ⁻¹₍ y ₎
  f∘g : Map Z Y
  f∘g = ⟪ Z , X , Y ⟫ f ○ g
  A : Space
  A = dom⟪ X , Y , Z ⟫ f∘g ^ f
  Prp : U A → Set
  Prp (y , φ) = ∀(x : U(f⁻¹ y)) → pr₁ g (pr₁ (pr₁ φ x)) ＝ pr₁ x

⟪_,_⟫Π[_] : (X Y : Space) → (Map X Y) → Mapto X → Mapto Y
⟪ X , Y ⟫Π[ f ] (Z , g) = A , h
 where
  A : Space
  A = dom⟪ X , Y ⟫Π[ f ] (Z , g)
  h : Map A Y
  h = pr₁ ∘ pr₁ , (λ r rR → pr₁ rR)

\end{code}

According to the diagram, we get the following definition of Π, which
is equivalent to the above one. We use the above one since it is
simpler and easier to work with.

⟪_,_⟫Π[_] : (X Y : Space) → (Map X Y) → Mapto X → Mapto Y
⟪ X , Y ⟫Π[ f ] (Z , g) = A , h
 where
  dom[f∘g^f] : Space
  dom[f∘g^f] = dom⟪ X , Y , Z ⟫ (⟪ Z , X , Y ⟫ f ○ g) ^ f
  dom[f^f] : Space
  dom[f^f] = dom⟪ X , Y , X ⟫ f ^ f
  f⁻¹ : U Y → Space
  f⁻¹ y = ⟪ X , Y ⟫ f ⁻¹₍ y ₎
  
  h₀ : Map Y dom[f^f]
  h₀ = h , cts
   where
    h : U Y → U dom[f^f]
    h y = y , id , (λ p pP → pP)
    cts : continuous {Y} {dom[f^f]} h
    cts q qQ = ∧-intro qQ (λ t uc p pP e → pP)

  h₁ : Map dom[f∘g^f] dom[f^f]
  h₁ = h , cts
   where
    h : U dom[f∘g^f] → U dom[f^f]
    h (y , φ , cφ) = y , ψ , cψ
     where
      ψ : U (f⁻¹ y) → U (f⁻¹ y)
      ψ x = pr₁ g (pr₁ (φ x)) , pr₂ (φ x)
      cψ : continuous {f⁻¹ y} {f⁻¹ y} ψ
      cψ p pP = pr₂ g (pr₁ ∘ φ ∘ p) (cφ p pP)
    cts : continuous {dom[f∘g^f]} {dom[f^f]} h
    cts q (qQ₀ , qQ₁) = ∧-intro qQ₀ claim
     where
      claim : ∀(t : ₂ℕ → ₂ℕ) → t ∈ C → ∀(p : ₂ℕ → U X) → p ∈ Probe X →
              (e : ∀(α : ₂ℕ) → [ pr₁ f (p α) ＝ pr₁ (h(q(t α))) ]) →
              (λ α → pr₁ g (pr₁(pr₁(pr₂(q(t α)))(p α , e α)))) ∈ Probe X
         -- = (λ α → pr₁(pr₁(pr₂(h(q(t α))))(p α , e α))) ∈ Probe X
      claim t uc p pP e = pr₂ g r rZ
       where
        r : ₂ℕ → U Z
        r α = pr₁(pr₁(pr₂(q(t α)))(p α , e α))
        rZ : r ∈ Probe Z
        rZ = qQ₁ t uc p pP e

  A : Space
  A = Y ×[ dom[f^f] ] dom[f∘g^f] ⟨ h₀ , h₁ ⟩

  h : Map A Y
  h = ⟪ Y ×[ dom[f^f] ] dom[f∘g^f] ⟨ h₀ , h₁ ⟩⟫-pr₁

dom⟪_,_⟫Π[_] : (X Y : Space) → (Map X Y) → Mapto X → Space
dom⟪ X , Y ⟫Π[ f ] (Z , g)= pr₁(⟪ X , Y ⟫Π[ f ] (Z , g))


