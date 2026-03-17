Chuangjie Xu 2013 (ported to TypeTopology in 2025)

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan renaming (_+_ to _⊎_)
open import UF.FunExt using (naive-funext)

module gist.C-Space.UsingFunExt.Coproduct (fe : naive-funext 𝓤₀ 𝓤₀) where

open import Naturals.Addition

open import gist.C-Space.Preliminaries.Sequence
open import gist.C-Space.Preliminaries.Naturals.Order
open import gist.C-Space.UniformContinuity
open import gist.C-Space.Coverage
open import gist.C-Space.UsingFunExt.Space
open import gist.C-Space.UsingFunExt.CartesianClosedness fe

\end{code}

The initial C-space

\begin{code}

𝟘Space : Space
𝟘Space = 𝟘 , P , c₀ , c₁ , c₂
 where
  P : (₂ℕ → 𝟘) → Set
  P p = 𝟘
  c₀ : ∀(x : 𝟘) → (λ α → x) ∈ P
  c₀ x = x
  c₁ : ∀(t : ₂ℕ → ₂ℕ) → t ∈ C → ∀(p : ₂ℕ → 𝟘) → p ∈ P → p ∘ t ∈ P
  c₁ _ _ p _ = p 0̄
  c₂ : ∀(p : ₂ℕ → 𝟘) → (Σ \(n : ℕ) → ∀(s : ₂Fin n) → (p ∘ (cons s)) ∈ P) → p ∈ P
  c₂ p _ = p 0̄

continuous-empty : (A : Space) → Map 𝟘Space A
continuous-empty A = (λ ()) , (λ p → λ ())

\end{code}

Binary coproduct of C-spaces

\begin{code}

infixl 3 _⊕_

_⊕_ : Space → Space → Space
(X , P , pc₀ , pc₁ , pc₂) ⊕ (Y , Q , qc₀ , qc₁ , qc₂) = (X ⊎ Y) , R , rc₀ , rc₁ , rc₂
 where
  R : (₂ℕ → X ⊎ Y) → Set
  R r = Σ \(n : ℕ) → ∀(s : ₂Fin n) →
           (Σ \(p : ₂ℕ → X) → (p ∈ P) × (∀(α : ₂ℕ) → r(cons s α) ＝ inl(p α)))
         ⊎ (Σ \(q : ₂ℕ → Y) → (q ∈ Q) × (∀(α : ₂ℕ) → r(cons s α) ＝ inr(q α)))

  rc₀ : ∀(w : X ⊎ Y) → (λ α → w) ∈ R
  rc₀ (inl x) = 0 , λ s → inl ((λ α → x) , pc₀ x , (λ _ → refl))
  rc₀ (inr y) = 0 , λ s → inr ((λ α → y) , qc₀ y , (λ _ → refl))

  rc₁ : ∀(t : ₂ℕ → ₂ℕ) → t ∈ C → ∀(r : ₂ℕ → X ⊎ Y) →  r ∈ R → r ∘ t ∈ R
  rc₁ t uc r (m , pr) = n , prf
   where
    n : ℕ
    n = pr₁ (Theorem[Coverage-axiom] m t uc)
    prf : ∀(s : ₂Fin n) → (Σ \(p : ₂ℕ → X) → (p ∈ P) × (∀(α : ₂ℕ) → r(t(cons s α)) ＝ inl(p α)))
                        ⊎ (Σ \(q : ₂ℕ → Y) → (q ∈ Q) × (∀(α : ₂ℕ) → r(t(cons s α)) ＝ inr(q α)))
    prf s = cases (inl ∘ c₀) (inr ∘ c₁) (pr s')
     where
      s' : ₂Fin m
      s' = pr₁ (pr₂ (Theorem[Coverage-axiom] m t uc) s)
      t' : ₂ℕ → ₂ℕ
      t' = pr₁ (pr₂ (pr₂ (Theorem[Coverage-axiom] m t uc) s))
      uc' : t' ∈ C
      uc' = pr₁ (pr₂ (pr₂ (pr₂ (Theorem[Coverage-axiom] m t uc) s)))
      ex : ∀ α → t (cons s α) ∼ cons s' (t' α)
      ex = pr₂ (pr₂ (pr₂ (pr₂ (Theorem[Coverage-axiom] m t uc) s)))
      eqtα : ∀(α : ₂ℕ) → r(t(cons s α)) ＝ r(cons s' (t' α))
      eqtα α = ap r (fe (ex α))
                    ----

      c₀ : (Σ \(p : ₂ℕ → X) → (p ∈ P) × (∀(α : ₂ℕ) → r(cons s' α) ＝ inl(p α))) →
            Σ \(p : ₂ℕ → X) → (p ∈ P) × (∀(α : ₂ℕ) → r(t(cons s α)) ＝ inl(p α))
      c₀ (p , pP , eα) = (p ∘ t') , (pc₁ t' uc' p pP) , eα'
       where
        eα' : ∀(α : ₂ℕ) → r(t(cons s α)) ＝ inl(p(t' α))
        eα' α = eqtα α ∙ eα (t' α)
      c₁ : (Σ \(q : ₂ℕ → Y) → (q ∈ Q) × (∀(α : ₂ℕ) → r(cons s' α) ＝ inr(q α))) →
            Σ \(q : ₂ℕ → Y) → (q ∈ Q) × (∀(α : ₂ℕ) → r(t(cons s α)) ＝ inr(q α))
      c₁ (q , qQ , eα) = (q ∘ t') , (qc₁ t' uc' q qQ) , eα'
       where
        eα' : ∀(α : ₂ℕ) → r(t(cons s α)) ＝ inr(q(t' α))
        eα' α = eqtα α ∙ eα (t' α)

  rc₂ : ∀(r : ₂ℕ → X ⊎ Y) → (Σ \(n : ℕ) → ∀(s : ₂Fin n) → (r ∘ (cons s)) ∈ R) → r ∈ R
  rc₂ r (n , pr) = (k + n) , prf
   where
    k : ℕ
    k = pr₁ (max-fin (λ s → pr₁ (pr s)))
    k-max : ∀(s : ₂Fin n) → pr₁ (pr s) ≤ k
    k-max = pr₂ (max-fin (λ s → pr₁ (pr s)))
    prf : ∀(s : ₂Fin (k + n)) → (Σ \(p : ₂ℕ → X) → (p ∈ P) × (∀(α : ₂ℕ) → r(cons s α) ＝ inl(p α)))
                              ⊎ (Σ \(q : ₂ℕ → Y) → (q ∈ Q) × (∀(α : ₂ℕ) → r(cons s α) ＝ inr(q α)))
    prf s = cases (inl ∘ c₀) (inr ∘ c₁) (pr₂ (pr s₀) s₁)
     where
      s₀ : ₂Fin n
      s₀ = ftake k n s
      l : ℕ
      l = pr₁ (pr s₀)
      l≤k : l ≤ k
      l≤k = k-max s₀
      m : ℕ
      m =  pr₁ (Lemma[≤-Σ] l k l≤k)
      k=m+l : k ＝ m + l
      k=m+l = (pr₂ (Lemma[≤-Σ] l k l≤k))⁻¹ ∙ (addition-commutativity l m)
      s₁ : ₂Fin l
      s₁ = ftake m l (transport ₂Fin k=m+l (fdrop k n s))
      s₂ : ₂Fin m
      s₂ = fdrop m l (transport ₂Fin k=m+l (fdrop k n s))
      lemma : ∀(α : ₂ℕ) → cons s α ＝ cons s₀ (cons s₁ (cons s₂ α))
      lemma α = fe (λ i → (Lemma[cons-ftake-fdrop]² n m l k k=m+l s α i)⁻¹)
               ----
      c₀ : (Σ \(p : ₂ℕ → X) → (p ∈ P) × (∀(α : ₂ℕ) → r(cons s₀ (cons s₁ α)) ＝ inl(p α))) →
            Σ \(p : ₂ℕ → X) → (p ∈ P) × (∀(α : ₂ℕ) → r(cons s α) ＝ inl(p α))
      c₀ (p , pP , e) = ps₂ , ps₂P , e'
       where
        ps₂ : ₂ℕ → X
        ps₂ = p ∘ (cons s₂)
        ps₂P : ps₂ ∈ P
        ps₂P = pc₁ (cons s₂) (Lemma[cons-UC] s₂) p pP
        e' : ∀(α : ₂ℕ) → r(cons s α) ＝ inl(p(cons s₂ α))
        e' α = (ap r (lemma α)) ∙ (e (cons s₂ α))
      c₁ : (Σ \(q : ₂ℕ → Y) → (q ∈ Q) × (∀(α : ₂ℕ) → r(cons s₀ (cons s₁ α)) ＝ inr(q α))) →
            Σ \(q : ₂ℕ → Y) → (q ∈ Q) × (∀(α : ₂ℕ) → r(cons s α) ＝ inr(q α))
      c₁ (q , qQ , e) = qs₂ , qs₂Q , e'
       where
        qs₂ : ₂ℕ → Y
        qs₂ = q ∘ (cons s₂)
        qs₂Q : qs₂ ∈ Q
        qs₂Q = qc₁ (cons s₂) (Lemma[cons-UC] s₂) q qQ
        e' : ∀(α : ₂ℕ) → r(cons s α) ＝ inr(q(cons s₂ α))
        e' α = (ap r (lemma α)) ∙ (e (cons s₂ α))



continuous-inl : (X Y : Space) → Map X (X ⊕ Y)
continuous-inl X Y = inl , cts
 where
  cts : ∀(r : ₂ℕ → U X) → r ∈ Probe X → inl ∘ r ∈ Probe (X ⊕ Y)
  cts r rP = 0 , prf
   where
    prf : ∀(s : ₂Fin 0) →
            (Σ \(p : ₂ℕ → U X) → (p ∈ Probe X) × (∀(α : ₂ℕ) → inl(r(cons s α)) ＝ inl(p α)))
          ⊎ (Σ \(q : ₂ℕ → U Y) → (q ∈ Probe Y) × (∀(α : ₂ℕ) → inl(r(cons s α)) ＝ inr(q α)))
    prf ⟨⟩ = inl (r , rP , (λ α → refl))

continuous-inr : (X Y : Space) → Map Y (X ⊕ Y)
continuous-inr X Y = inr , cts
 where
  cts : ∀(r : ₂ℕ → U Y) → r ∈ Probe Y → inr ∘ r ∈ Probe (X ⊕ Y)
  cts r rQ = 0 , prf
   where
    prf : ∀(s : ₂Fin 0) →
            (Σ \(p : ₂ℕ → U X) → (p ∈ Probe X) × (∀(α : ₂ℕ) → inr(r(cons s α)) ＝ inl(p α)))
          ⊎ (Σ \(q : ₂ℕ → U Y) → (q ∈ Probe Y) × (∀(α : ₂ℕ) → inr(r(cons s α)) ＝ inr(q α)))
    prf ⟨⟩ = inr (r , rQ , (λ α → refl))


continuous-case : (X Y Z : Space) → Map (X ⇒ Z) ((Y ⇒ Z) ⇒ (X ⊕ Y) ⇒ Z)
continuous-case X Y Z = c , cts
 where
  c : U(X ⇒ Z) → U((Y ⇒ Z) ⇒ (X ⊕ Y) ⇒ Z)
  c (f₀ , cf₀) = case-f₀ , ccf₀
   where
    case-f₀ : U(Y ⇒ Z) → U((X ⊕ Y) ⇒ Z)
    case-f₀ (f₁ , cf₁) = case-f₀-f₁ , ccf₀f₁
     where
      case-f₀-f₁ : U(X ⊕ Y) → U Z
      case-f₀-f₁ (inl x) = f₀ x
      case-f₀-f₁ (inr y) = f₁ y
      ccf₀f₁ : continuous (X ⊕ Y) Z case-f₀-f₁
      ccf₀f₁ r (n , pr) = cond₂ Z (case-f₀-f₁ ∘ r) (n , prf)
       where
        prf : ∀(s : ₂Fin n) → case-f₀-f₁ ∘ r ∘ (cons s) ∈ Probe Z
        prf s = cases claim₀ claim₁ (pr s)
         where
          claim₀ : (Σ \(p : ₂ℕ → U X) → (p ∈ Probe X) × (∀(α : ₂ℕ) → r(cons s α) ＝ inl(p α))) →
                    case-f₀-f₁ ∘ r ∘ cons s ∈ Probe Z
          claim₀ (p , pX , e) = transport (Probe Z) sclaim₀ sclaim₁
           where
            ex : ∀(α : ₂ℕ) → f₀(p α) ＝ case-f₀-f₁(r(cons s α))
            ex α = ap case-f₀-f₁ (e α)⁻¹
            sclaim₀ : f₀ ∘ p ＝ case-f₀-f₁ ∘ r ∘ cons s
            sclaim₀ = fe ex
                     ----
            sclaim₁ : f₀ ∘ p ∈ Probe Z
            sclaim₁ = cf₀ p pX
          claim₁ : (Σ \(q : ₂ℕ → U Y) → (q ∈ Probe Y) × (∀(α : ₂ℕ) → r(cons s α) ＝ inr(q α))) →
                    case-f₀-f₁ ∘ r ∘ (cons s) ∈ Probe Z
          claim₁ (q , qY , e) = transport (Probe Z) sclaim₀ sclaim₁
           where
            ex : ∀(α : ₂ℕ) → f₁(q α) ＝ case-f₀-f₁(r(cons s α))
            ex α = ap case-f₀-f₁ (e α)⁻¹
            sclaim₀ : f₁ ∘ q ＝ case-f₀-f₁ ∘ r ∘ cons s
            sclaim₀ = fe ex
                     ----
            sclaim₁ : f₁ ∘ q ∈ Probe Z
            sclaim₁ = cf₁ q qY
    ccf₀ : continuous (Y ⇒ Z) ((X ⊕ Y) ⇒ Z) case-f₀
    ccf₀ r rYZ u (n , pr) t uc = cond₂ Z (λ α → pr₁(case-f₀(r(t α)))(u α)) (n , prf)
     where
      prf : ∀(s : ₂Fin n) → (λ α → pr₁(case-f₀(r(t(cons s α))))(u(cons s α))) ∈ Probe Z
      prf s = cases claim₀ claim₁ (pr s)
       where
        claim₀ : (Σ \(p : ₂ℕ → U X) → (p ∈ Probe X) × (∀(α : ₂ℕ) → u(cons s α) ＝ inl(p α))) →
                  (λ α → pr₁(case-f₀(r(t(cons s α))))(u(cons s α))) ∈ Probe Z
        claim₀ (p , pX , e) = transport (Probe Z) sclaim₀ sclaim₁
         where
          ex : ∀(α : ₂ℕ) → f₀(p α) ＝ pr₁(case-f₀(r(t(cons s α))))(u(cons s α))
          ex α = ap (pr₁(case-f₀(r(t(cons s α))))) (e α)⁻¹
          sclaim₀ : f₀ ∘ p ＝ (λ α → pr₁(case-f₀(r(t(cons s α))))(u(cons s α)))
          sclaim₀ = fe ex
                   ----
          sclaim₁ : f₀ ∘ p ∈ Probe Z
          sclaim₁ = cf₀ p pX
        claim₁ : (Σ \(q : ₂ℕ → U Y) → (q ∈ Probe Y) × (∀(α : ₂ℕ) → u(cons s α) ＝ inr(q α))) →
                  (λ α → pr₁(case-f₀(r(t(cons s α))))(u(cons s α))) ∈ Probe Z
        claim₁ (q , qY , e) = transport (Probe Z) sclaim₀ sclaim₁
         where
          ex : ∀(α : ₂ℕ) → pr₁(r(t(cons s α)))(q α) ＝ pr₁(case-f₀(r(t(cons s α))))(u(cons s α))
          ex α = ap (pr₁(case-f₀(r(t(cons s α))))) (e α)⁻¹
          sclaim₀ : (λ α → pr₁(r(t(cons s α)))(q α))
                  ＝ (λ α → pr₁(case-f₀(r(t(cons s α))))(u(cons s α)))
          sclaim₀ = fe ex
                   ----
          sclaim₁ : (λ α → pr₁(r(t(cons s α)))(q α)) ∈ Probe Z
          sclaim₁ = rYZ q qY (t ∘ (cons s)) (Lemma[∘-UC] t uc (cons s) (Lemma[cons-UC] s))
  cts : continuous (X ⇒ Z) ((Y ⇒ Z) ⇒ (X ⊕ Y) ⇒ Z) c
  cts u uXZ v vYZ t uct w (n , pr) r ucr = cond₂ Z (λ α → pr₁(pr₁(c(u(t(r α))))(v(r α)))(w α)) (n , prf)
   where
    prf : ∀(s : ₂Fin n) → (λ α → pr₁(pr₁(c(u(t(r(cons s α)))))(v(r(cons s α))))(w(cons s α))) ∈ Probe Z
    prf s = cases claim₀ claim₁ (pr s)
     where
      claim₀ : (Σ \(p : ₂ℕ → U X) → (p ∈ Probe X) × (∀(α : ₂ℕ) → w(cons s α) ＝ inl(p α))) →
                (λ α → pr₁(pr₁(c(u(t(r(cons s α)))))(v(r(cons s α))))(w(cons s α))) ∈ Probe Z
      claim₀ (p , pX , e) = transport (Probe Z) sclaim₀ sclaim₂
       where
        ex  : ∀(α : ₂ℕ) → pr₁(u(t(r(cons s α))))(p α)
                        ＝ pr₁(pr₁(c(u(t(r(cons s α)))))(v(r(cons s α))))(w(cons s α))
        ex  α = ap (pr₁(pr₁(c(u(t(r(cons s α)))))(v(r(cons s α))))) (e α)⁻¹
        sclaim₀ : (λ α → pr₁(u(t(r(cons s α))))(p α))
                ＝ (λ α → pr₁(pr₁(c(u(t(r(cons s α)))))(v(r(cons s α))))(w(cons s α)))
        sclaim₀ = fe ex
                 ----
        sclaim₁ : t ∘ r ∘ cons s ∈ C
        sclaim₁ = Lemma[∘-UC] (t ∘ r) (Lemma[∘-UC] t uct r ucr) (cons s) (Lemma[cons-UC] s)
        sclaim₂ : (λ α → pr₁(u(t(r(cons s α))))(p α)) ∈ Probe Z
        sclaim₂ = uXZ p pX (t ∘ r ∘ (cons s)) sclaim₁
      claim₁ : (Σ \(q : ₂ℕ → U Y) → (q ∈ Probe Y) × (∀(α : ₂ℕ) → w(cons s α) ＝ inr(q α))) →
                (λ α → pr₁(pr₁(c(u(t(r(cons s α)))))(v(r(cons s α))))(w(cons s α))) ∈ Probe Z
      claim₁ (q , qY , e) = transport (Probe Z) sclaim₀ sclaim₁
       where
        ex : ∀(α : ₂ℕ) → pr₁(v(r(cons s α)))(q α)
                       ＝ pr₁(pr₁(c(u(t(r(cons s α)))))(v(r(cons s α))))(w(cons s α))
        ex α = ap (pr₁(pr₁(c(u(t(r(cons s α)))))(v(r(cons s α))))) (e α)⁻¹
        sclaim₀ : (λ α → pr₁(v(r(cons s α)))(q α))
                ＝ (λ α → pr₁(pr₁(c(u(t(r(cons s α)))))(v(r(cons s α))))(w(cons s α)))
        sclaim₀ = fe ex
                 ----
        sclaim₁ : (λ α → pr₁(v(r(cons s α)))(q α)) ∈ Probe Z
        sclaim₁ = vYZ q qY (r ∘ cons s) (Lemma[∘-UC] r ucr (cons s) (Lemma[cons-UC] s))

\end{code}

Arbitrary coproduct of C-spaces

\begin{code}

∐ : {I : Set} → (I → Space) → Space
∐ {I} X = A , P , c₀ , c₁ , c₂
 where
  A : Set
  A = Σ \(i : I) → U(X i)

  P : (₂ℕ → A) → Set
  P p = Σ \(n : ℕ) → ∀(s : ₂Fin n) →
         Σ \(i : I) → Σ \(q : ₂ℕ → U(X i)) →
          (q ∈ Probe (X i)) × (∀(α : ₂ℕ) → p(cons s α) ＝ (i , q α))

  c₀ : ∀(x : A) → (λ α → x) ∈ P
  c₀ (i , x) = 0 , λ s → i , (λ α → x) , cond₀ (X i) x , (λ α → refl)

  c₁ : ∀(t : ₂ℕ → ₂ℕ) → t ∈ C → ∀(p : ₂ℕ → A) → p ∈ P → p ∘ t ∈ P
  c₁ t uc p (m , pr) = n , prf
   where
    n : ℕ
    n = pr₁ (Theorem[Coverage-axiom] m t uc)
    prf : ∀(s : ₂Fin n) → Σ \(i : I) → Σ \(q : ₂ℕ → U(X i)) →
           (q ∈ Probe (X i)) × (∀(α : ₂ℕ) → (p ∘ t)(cons s α) ＝ (i , q α))
    prf s = i , (q ∘ t') , claim₁ , claim₃
     where
      s' : ₂Fin m
      s' = pr₁ (pr₂ (Theorem[Coverage-axiom] m t uc) s)
      t' : ₂ℕ → ₂ℕ
      t' = pr₁ (pr₂ (pr₂ (Theorem[Coverage-axiom] m t uc) s))
      uc' : t' ∈ C
      uc' = pr₁ (pr₂ (pr₂ (pr₂ (Theorem[Coverage-axiom] m t uc) s)))
      ex : ∀ α → t (cons s α) ∼ cons s' (t' α)
      ex = pr₂ (pr₂ (pr₂ (pr₂ (Theorem[Coverage-axiom] m t uc) s)))
      i : I
      i = pr₁ (pr s')
      q : ₂ℕ → U(X i)
      q = pr₁ (pr₂ (pr s'))
      claim₀ : q ∈ Probe(X i)
      claim₀ = pr₁ (pr₂ (pr₂ (pr s')))
      claim₁ : (q ∘ t') ∈ Probe(X i)
      claim₁ = cond₁ (X i) t' uc' q claim₀
      claim₂ : ∀(α : ₂ℕ) → p(cons s' α) ＝ (i , q α)
      claim₂ = pr₂ (pr₂ (pr₂ (pr s')))
      claim₃ : ∀(α : ₂ℕ) → (p ∘ t)(cons s α) ＝ (i , q(t' α))
      claim₃ α = eq₁ ∙ eq₂
       where
        eq₀ : t(cons s α) ＝ cons s' (t' α)
        eq₀ = fe (ex α)
             ----
        eq₁ : p(t(cons s α)) ＝ p(cons s' (t' α))
        eq₁ = ap p eq₀
        eq₂ : p(cons s' (t' α)) ＝ (i , q(t' α))
        eq₂ = claim₂ (t' α)

  c₂ : ∀(p : ₂ℕ → A) → (Σ \(n : ℕ) → ∀(s : ₂Fin n) → (p ∘ (cons s)) ∈ P) → p ∈ P
  c₂ p (n , pr) = (k + n) , prf
   where
    k : ℕ
    k = pr₁ (max-fin (λ s → pr₁ (pr s)))
    k-max : ∀(s : ₂Fin n) → pr₁ (pr s) ≤ k
    k-max = pr₂ (max-fin (λ s → pr₁ (pr s)))
    prf : ∀(s : ₂Fin (k + n)) → Σ \(i : I) → Σ \(q : ₂ℕ → U(X i)) →
           (q ∈ Probe (X i)) × (∀(α : ₂ℕ) → p(cons s α) ＝ (i , q α))
    prf s = i , q' , claim₁ , claim₃
     where
      s₀ : ₂Fin n
      s₀ = ftake k n s
      l : ℕ
      l = pr₁ (pr s₀)
      l≤k : l ≤ k
      l≤k = k-max s₀
      m : ℕ
      m = pr₁ (Lemma[≤-Σ] l k l≤k)
      k=m+l : k ＝ m + l
      k=m+l = (pr₂ (Lemma[≤-Σ] l k l≤k))⁻¹ ∙ (addition-commutativity l m)
      s₁ : ₂Fin l
      s₁ = ftake m l (transport ₂Fin k=m+l (fdrop k n s))
      s₂ : ₂Fin m
      s₂ = fdrop m l (transport ₂Fin k=m+l (fdrop k n s))
      lemma : ∀(α : ₂ℕ) → cons s α ＝ cons s₀ (cons s₁ (cons s₂ α))
      lemma α = fe (λ i → (Lemma[cons-ftake-fdrop]² n m l k k=m+l s α i)⁻¹)
               ----
      i : I
      i = pr₁ (pr₂ (pr s₀) s₁)
      q : ₂ℕ → U(X i)
      q = pr₁ (pr₂ (pr₂ (pr s₀) s₁))
      claim₀ : q ∈ Probe(X i)
      claim₀ = pr₁ (pr₂ (pr₂ (pr₂ (pr s₀) s₁)))
      q' : ₂ℕ → U(X i)
      q' = q ∘ (cons s₂)
      claim₁ : q' ∈ Probe(X i)
      claim₁ = cond₁ (X i) (cons s₂) (Lemma[cons-UC] s₂) q claim₀
      claim₂ : ∀(α : ₂ℕ) → p(cons s₀ (cons s₁ α)) ＝ (i , q α)
      claim₂ = pr₂ (pr₂ (pr₂ (pr₂ (pr s₀) s₁)))
      claim₃ : ∀(α : ₂ℕ) → p(cons s α) ＝ (i , q' α)
      claim₃ α = eq₀ ∙ eq₁
       where
        eq₀ : p(cons s α) ＝ p(cons s₀ (cons s₁ (cons s₂ α)))
        eq₀ = ap p (lemma α)
        eq₁ : p(cons s₀ (cons s₁ (cons s₂ α))) ＝ (i , q' α)
        eq₁ = claim₂ (cons s₂ α)


continuous-inj : {I : Set} → (X : I → Space) → (i : I) → Map (X i) (∐ X)
continuous-inj {I} X i = inj , cts
 where
  inj : U(X i) → U(∐ X)
  inj x = (i , x)
  cts : continuous (X i) (∐ X) inj
  cts p pi = 0 , prf
   where
    prf : ∀(s : ₂Fin 0) → Σ \(i : I) → Σ \(q : ₂ℕ → U(X i)) →
           (q ∈ Probe (X i)) × (∀(α : ₂ℕ) → (inj ∘ p)(cons s α) ＝ (i , q α))
    prf ⟨⟩ = i , p , pi , (λ _ → refl)


universal-property-∐ :
    {I : Set} → ∀(X : I → Space) →
    ∀(Y : Space) → ∀(f : (i : I) → Map (X i) Y) →
    Σ \(g : Map (∐ X) Y) →
      ∀(i : I) → ∀(x : U(X i)) → pr₁ g (pr₁ (continuous-inj X i) x) ＝ pr₁ (f i) x
universal-property-∐ {I} X Y f = (g , cg) , (λ _ _ → refl)
 where
  g : U(∐ X) → U Y
  g (i , x) = pr₁ (f i) x
  cg : continuous (∐ X) Y g
  cg p (n , pr) = cond₂ Y (g ∘ p) (n , prf)
   where
    prf : ∀(s : ₂Fin n) → (g ∘ p ∘ (cons s)) ∈ Probe Y
    prf s = transport (Probe Y) claim₄ claim₅
     where
      i : I
      i = pr₁ (pr s)
      q : ₂ℕ → U(X i)
      q = pr₁ (pr₂ (pr s))
      claim₀ : q ∈ Probe(X i)
      claim₀ = pr₁ (pr₂ (pr₂ (pr s)))
      claim₁ : ∀(α : ₂ℕ) → p(cons s α) ＝ (i , q α)
      claim₁ = pr₂ (pr₂ (pr₂ (pr s)))
      claim₂ : ∀(α : ₂ℕ) → g(p(cons s α)) ＝ g(i , q α)
      claim₂ α = ap g (claim₁ α)
      claim₃ : ∀(α : ₂ℕ) → pr₁(f i)(q α) ＝ g(p(cons s α))
      claim₃ α = (claim₂ α)⁻¹
      claim₄ : pr₁ (f i) ∘ q ＝ g ∘ p ∘ cons s
      claim₄ = fe claim₃
              ----
      claim₅ : pr₁ (f i) ∘ q ∈ Probe Y
      claim₅ = pr₂ (f i) q claim₀

\end{code}
