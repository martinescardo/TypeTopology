Chuangjie Xu 2012 (ported to TypeTopology in 2025)

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (_+_)
open import UF.FunExt using (DN-funext)

module C-Space.UsingNotNotFunExt.DiscreteSpace (dnfe : ¬¬ DN-funext 𝓤₀ 𝓤₀) where

open import UF.Base
open import UF.Sets
open import UF.DiscreteAndSeparated
open import Naturals.Addition
open import Naturals.Properties

open import C-Space.Preliminaries.Booleans.Functions using (if)
open import C-Space.Preliminaries.Naturals.Order
open import C-Space.Preliminaries.Sequence
open import C-Space.Preliminaries.DoubleNegation
open import C-Space.Preliminaries.NotNotFunExt dnfe
open import C-Space.UniformContinuity
open import C-Space.Coverage
open import C-Space.UsingNotNotFunExt.Space
open import C-Space.UsingNotNotFunExt.CartesianClosedness dnfe

\end{code}

The locally constant functions ₂ℕ → X on any set X form a C-topology on X. Any
space with such a C-topology is discrete, i.e. all maps from it to any other
space is continuous.

\begin{code}

LC : {X : Set} → (₂ℕ → X) → Set
LC = locally-constant

LC-topology : (X : Set) → is-discrete X → probe-axioms X LC
LC-topology X dis = c₀ , c₁ , c₂ , c₃
 where
  c₀ : ∀(x : X) → (λ α → x) ∈ LC
  c₀ x = 0 , (λ _ _ _ → refl) , (λ _ _ → ≤-zero)

  c₁ : ∀ t → t ∈ C → ∀ p → p ∈ LC → p ∘ t ∈ LC
  c₁ t uct p ucp = Lemma[LM-least-modulus] _＝_ dis _⁻¹ _∙_ (p ∘ t) n prf
   where
    m : ℕ
    m = pr₁ ucp
    n : ℕ
    n = pr₁(uct m)
    prp : ∀(α β : ₂ℕ) → α ＝⟦ m ⟧ β → p α ＝ p β
    prp = pr₁ (pr₂ ucp)
    prt : ∀(α β : ₂ℕ) → α ＝⟦ n ⟧ β → t α ＝⟦ m ⟧ t β
    prt = pr₁ (pr₂ (uct m))
    prf : ∀(α β : ₂ℕ) → α ＝⟦ n ⟧ β → p(t α) ＝ p(t β)
    prf α β en = prp (t α) (t β) (prt α β en)

  c₂ : ∀(p : ₂ℕ → X) → (Σ \(n : ℕ) → ∀(s : ₂Fin n) → (p ∘ (cons s)) ∈ LC) → p ∈ LC
  c₂ p (n , ps) = Lemma[LM-least-modulus] _＝_ dis _⁻¹ _∙_ p (n + k) prf
   where
    f : ₂Fin n → ℕ
    f s = pr₁ (ps s)
    k : ℕ
    k = pr₁ (max-fin f)
    k-max : ∀(s : ₂Fin n) → f s ≤ k
    k-max = pr₂ (max-fin f)
    fact : ∀(s : ₂Fin n) → ∀(α β : ₂ℕ) → α ＝⟦ k ⟧ β → p(cons s α) ＝ p(cons s β)
    fact s α β ek = pr₁ (pr₂ (ps s)) α β (Lemma[＝⟦⟧-≤] ek (k-max s))
    prf : ∀(α β : ₂ℕ) → α ＝⟦ n + k ⟧ β → p α ＝ p β
    prf α β enk = discrete-is-¬¬-separated dis _ _ goal
     where
      s : ₂Fin n
      s = take n α
      en : α ＝⟦ n ⟧ β
      en = Lemma[＝⟦⟧-≤] enk (Lemma[a≤a+b] n k)
      eqs : take n α ＝ take n β
      eqs = Lemma[＝⟦⟧-take] en
      α' : ₂ℕ
      α' = drop n α
      eα₀ : cons s α' ∼ α
      eα₀ = Lemma[cons-take-drop] n α
      eα : ¬¬ (cons s α' ＝ α)
      eα = fe eα₀
          ----
      β' : ₂ℕ
      β' = drop n β
      eβ₀ : cons (take n β) β' ∼ β
      eβ₀ = Lemma[cons-take-drop] n β
      eβ₁ : cons s β' ∼ β
      eβ₁ = transport (λ x → cons x β' ∼ β) (eqs ⁻¹) eβ₀
      eβ : ¬¬ (cons s β' ＝ β)
      eβ = fe eβ₁
          ----
      awk : ∀(i : ℕ) → i < k → α' i ＝ β' i
      awk i i<k = eqα ∙ subgoal ∙ eqβ ⁻¹
       where
        i+n<k+n : i + n < k + n
        i+n<k+n = Lemma[a<b→a+c<b+c] i k n i<k
        i+n<n+k : i + n < n + k
        i+n<n+k = transport (λ m → (i + n) < m) (addition-commutativity k n) i+n<k+n
        subgoal : α (i + n) ＝ β (i + n)
        subgoal = Lemma[＝⟦⟧-<] enk (i + n) i+n<n+k
        le : (n i : ℕ) → (α : ₂ℕ) → drop n α i ＝ α (i + n)
        le 0 i α = refl
        le (succ n) i α = le n i (α ∘ succ)
        eqα : α' i ＝ α (i + n)
        eqα = le n i α
        eqβ : β' i ＝ β (i + n)
        eqβ = le n i β
      ek : α' ＝⟦ k ⟧ β'
      ek = Lemma[<-＝⟦⟧] awk
      claim₀ : ¬¬ (p α ＝ p(cons s α'))
      claim₀ = ¬¬sym (¬¬ap p eα)
      claim₁ : ¬¬ (p(cons s α') ＝ p(cons s β'))
      claim₁ = ¬¬-intro (fact s α' β' ek)
      claim₂ : ¬¬ (p(cons s β') ＝ p β)
      claim₂ = ¬¬ap p eβ
      goal : ¬¬ (p α ＝ p β)
      goal = ¬¬trans claim₀ (¬¬trans claim₁ claim₂)

  c₃ : ∀ p q → p ∈ LC → (∀ α → ¬¬ (p α ＝ q α)) → q ∈ LC 
  c₃ p q (n , prf , min) ex = n , prf' , min'
   where
    ex' : p ∼ q
    ex' α = discrete-is-¬¬-separated dis _ _ (ex α)
    prf' : ∀ α β → α ＝⟦ n ⟧ β → q α ＝ q β
    prf' α β en = (ex' α)⁻¹ ∙ prf α β en ∙ ex' β
    min' : (n' : ℕ) → (∀ α β → α ＝⟦ n' ⟧ β → q α ＝ q β) → n ≤ n'
    min' n' pr' = min n' pr
     where
      pr : ∀ α β → α ＝⟦ n' ⟧ β → p α ＝ p β
      pr α β en' = (ex' α) ∙ (pr' α β en') ∙ ex' β ⁻¹


DiscreteSpace : (X : Set) → is-discrete X → Space
DiscreteSpace X dec = X , LC , LC-topology X dec


Lemma[discreteness] : (X : Set) (dec : is-discrete X) (Y : Space)
                    → ∀(f : X → U Y) → continuous (DiscreteSpace X dec) Y f
Lemma[discreteness] X dec Y f p (m , prf , _) = cond₂ Y (f ∘ p) (m , claim)
 where
  claim : ∀(s : ₂Fin m) → f ∘ p ∘ cons s ∈ Probe Y
  claim s = cond₃' Y _ _ claim₂ claim₁
   where
    y : U Y
    y = f(p(cons s 0̄))
    claim₀ : ∀(α : ₂ℕ) → p(cons s 0̄) ＝ p(cons s α)
    claim₀ α = prf (cons s 0̄) (cons s α) (Lemma[cons-＝⟦⟧] s 0̄ α)
    claim₁ : ∀(α : ₂ℕ) → y ＝ f(p(cons s α))
    claim₁ α = ap f (claim₀ α)
    claim₂ : (λ α → y) ∈ Probe Y
    claim₂ = cond₀ Y y

\end{code}

All the uniformly continuous maps ₂ℕ → ₂ (and ₂ℕ → ℕ) are
locally constant. And hence they form a C-topology on ₂ (and ℕ).

The coproduct 1 + 1:

\begin{code}

𝟚Space : Space
𝟚Space = DiscreteSpace 𝟚 𝟚-is-discrete

Lemma[discrete-𝟚Space] : (X : Space) → ∀(f : 𝟚 → U X) → continuous 𝟚Space X f
Lemma[discrete-𝟚Space] X f = Lemma[discreteness] 𝟚 𝟚-is-discrete X f

continuous-if : (A : Space) → Map 𝟚Space (A ⇒ A ⇒ A)
continuous-if A = IF , c-IF
 where
  IF : 𝟚 → U (A ⇒ A ⇒ A)
  IF b = if-b , c-if-b
   where
    if-b : U A → U (A ⇒ A)
    if-b a₀ = if-b-a₀ , c-if-b-a₀
     where
      if-b-a₀ : U A → U A
      if-b-a₀ a₁ = if b a₀ a₁
      c-if-b-a₀ : continuous A A if-b-a₀
      c-if-b-a₀ p pA = lemma b
       where
        lemma : ∀(i : 𝟚) → (λ a₁ → 𝟚-cases a₀ a₁ i) ∘ p ∈ Probe A
        lemma ₀ = cond₀ A a₀
        lemma ₁ = pA
    c-if-b : continuous A (A ⇒ A) if-b
    c-if-b p pA q qA t tC = lemma b
     where
      lemma : ∀(i : 𝟚) → (λ α → 𝟚-cases (p(t α)) (q α) i) ∈ Probe A
      lemma ₀ = cond₁ A t tC p pA
      lemma ₁ = qA
  c-IF : continuous 𝟚Space (A ⇒ A ⇒ A) IF
  c-IF = Lemma[discrete-𝟚Space] (A ⇒ A ⇒ A) IF

\end{code}

The natural numbers object:

\begin{code}

ℕSpace : Space
ℕSpace = DiscreteSpace ℕ ℕ-is-discrete

Lemma[discrete-ℕSpace] : (X : Space) → ∀(f : ℕ → U X) → continuous ℕSpace X f
Lemma[discrete-ℕSpace] X f = Lemma[discreteness] ℕ ℕ-is-discrete X f

continuous-succ : Map ℕSpace ℕSpace
continuous-succ = succ , c-succ
 where
  c-succ : ∀(p : ₂ℕ → ℕ) → p ∈ LC → succ ∘ p ∈ LC
  c-succ p (n , prf , min) = n , prf' , min'
   where
    prf' : ∀(α β : ₂ℕ) → α ＝⟦ n ⟧ β → succ (p α) ＝ succ (p β)
    prf' α β en = ap succ (prf α β en)
    min' : ∀(n' : ℕ) → (∀ α β → α ＝⟦ n' ⟧ β → succ(p α) ＝ succ(p β)) → n ≤ n'
    min' n' pr' = min n' (λ α β en' → succ-lc(pr' α β en'))

continuous-rec : (A : Space) → Map A ((ℕSpace ⇒ A ⇒ A) ⇒ ℕSpace ⇒ A)
continuous-rec A = r , continuity-of-rec
 where
  ū : U(ℕSpace ⇒ A ⇒ A) → ℕ → U A → U A
  ū (f , _) n x = pr₁ (f n) x
  r : U A → U((ℕSpace ⇒ A ⇒ A) ⇒ ℕSpace ⇒ A)
  r a = (g , cg)
   where
    g : U(ℕSpace ⇒ A ⇒ A) → U(ℕSpace ⇒ A)
    g f = ℕ-induction a (ū f) , Lemma[discrete-ℕSpace] A (ℕ-induction a (ū f))
    cg : continuous (ℕSpace ⇒ A ⇒ A) (ℕSpace ⇒ A) g
    cg p pNAA q qN t uct = cond₂ A (λ α → ℕ-induction a (ū(p(t α))) (q α)) (n , prf)
     where
      n : ℕ
      n = pr₁ qN
      prf : ∀(s : ₂Fin n) → (λ α → ℕ-induction a (ū(p(t(cons s α)))) (q(cons s α))) ∈ Probe A
      prf s = cond₃' A _ _ claim₀ claim₁
       where
        ucts : uniformly-continuous-₂ℕ (t ∘ (cons s))
        ucts = Lemma[∘-UC] t uct (cons s) (Lemma[cons-UC] s)
        lemma : ∀(k : ℕ) → (λ α → ℕ-induction a (ū(p(t(cons s α)))) k) ∈ Probe A
        lemma 0        = cond₁ A (t ∘ (cons s)) ucts (λ _ → a) (cond₀ A a)
        lemma (succ k) = claim (λ α → ℕ-induction a (ū(p(t(cons s α)))) k) (lemma k) id Lemma[id-UC]
         where
          claim : (λ α → pr₁ (p (t(cons s α))) k) ∈ Probe (A ⇒ A)
          claim = pNAA (λ _ → k) (0 , (λ _ _ _ → refl) , (λ _ _ → ≤-zero)) (t ∘ (cons s)) ucts
        claim₀ : (λ α → ℕ-induction a (ū(p(t(cons s α)))) (q(cons s 0̄))) ∈ Probe A
        claim₀ = lemma (q(cons s 0̄))
        eq : ∀(α : ₂ℕ) → q (cons s 0̄) ＝ q (cons s α)
        eq α = pr₁ (pr₂ qN) (cons s 0̄) (cons s α) (Lemma[cons-＝⟦⟧] s 0̄ α)
        claim₁ : ∀(α : ₂ℕ) → ℕ-induction a (ū(p(t(cons s α)))) (q(cons s 0̄)) ＝
                             ℕ-induction a (ū(p(t(cons s α)))) (q(cons s α))
        claim₁ α = ap (ℕ-induction a (ū(p(t(cons s α))))) (eq α)

  continuity-of-rec : continuous A ((ℕSpace ⇒ A ⇒ A) ⇒ ℕSpace ⇒ A) r
  continuity-of-rec p pA q qNAA t uct u uN v ucv =
                    cond₂ A (λ α → ℕ-induction (p(t(v α))) (ū(q(v α))) (u α)) (n , prf)
   where
    n : ℕ
    n = pr₁ uN
    prf : ∀(s : ₂Fin n)
        → (λ α → ℕ-induction (p(t(v(cons s α)))) (ū(q(v(cons s α)))) (u(cons s α))) ∈ Probe A
    prf s = cond₃' A _ _ claim₀ claim₁
     where
      ucvs : uniformly-continuous-₂ℕ (v ∘ (cons s))
      ucvs = Lemma[∘-UC] v ucv (cons s) (Lemma[cons-UC] s)
      uctvs : uniformly-continuous-₂ℕ (t ∘ v ∘ (cons s))
      uctvs = Lemma[∘-UC] t uct (v ∘ (cons s)) ucvs
      lemma : ∀(k : ℕ) → (λ α → ℕ-induction (p(t(v(cons s α)))) (ū(q(v(cons s α)))) k) ∈ Probe A
      lemma 0        = cond₁ A (t ∘ v ∘ (cons s)) uctvs p pA
      lemma (succ k) = claim (λ α → ℕ-induction (p(t(v(cons s α)))) (ū(q(v(cons s α)))) k)
                             (lemma k) id Lemma[id-UC]
       where
        claim : (λ α → pr₁ (q(v(cons s α))) k) ∈ Probe (A ⇒ A)
        claim = qNAA (λ _ → k) (0 , (λ _ _ _ → refl) , (λ _ _ → ≤-zero)) (v ∘ (cons s)) ucvs
      claim₀ : (λ α → ℕ-induction (p(t(v(cons s α)))) (ū(q(v(cons s α)))) (u(cons s 0̄))) ∈ Probe A
      claim₀ = lemma (u(cons s 0̄))
      eq : ∀(α : ₂ℕ) → u(cons s 0̄) ＝ u(cons s α)
      eq α = pr₁ (pr₂ uN) (cons s 0̄) (cons s α) (Lemma[cons-＝⟦⟧] s 0̄ α)
      claim₁ : ∀(α : ₂ℕ) → ℕ-induction (p(t(v(cons s α)))) (ū(q(v(cons s α)))) (u(cons s 0̄))
                         ＝ ℕ-induction (p(t(v(cons s α)))) (ū(q(v(cons s α)))) (u(cons s α))
      claim₁ α = ap (ℕ-induction (p(t(v(cons s α)))) (ū(q(v(cons s α))))) (eq α)

\end{code}

When X is an hset, local constancy of ₂ℕ → X is an hprop.

\begin{code}

Lemma[LC-hprop] : {X : Set} → is-set X → ∀(p : ₂ℕ → X)
                → (lc₀ lc₁ : p ∈ LC) → ¬¬ (lc₀ ＝ lc₁)
Lemma[LC-hprop] hsX p (n₀ , (prf₀ , min₀)) (n₁ , (prf₁ , min₁)) = ¬¬to-Σ-＝ (e , ee)
 where
  e : n₀ ＝ n₁
  e = Lemma[m≤n∧n≤m→m=n] (min₀ n₁ prf₁) (min₁ n₀ prf₀)
  prf₀'min₀' :  (∀(α β : ₂ℕ) → α ＝⟦ n₁ ⟧ β → p α ＝ p β)
              × (∀(n' : ℕ) → (∀(α β : ₂ℕ) → α ＝⟦ n' ⟧ β → p α ＝ p β) → n₁ ≤ n')
  prf₀'min₀' = transport _ e (prf₀ , min₀)
  prf₀' : ∀(α β : ₂ℕ) → α ＝⟦ n₁ ⟧ β → p α ＝ p β
  prf₀' = pr₁ prf₀'min₀'
  eeprf : ∀(α β : ₂ℕ) → (en : α ＝⟦ n₁ ⟧ β) → prf₀' α β en ＝ prf₁ α β en
  eeprf α β en = hsX (prf₀' α β en) (prf₁ α β en)
  epr : ¬¬ (prf₀' ＝ prf₁)
  epr = fe³ eeprf
       -----
  min₀' : ∀(n' : ℕ) → (∀(α β : ₂ℕ) → α ＝⟦ n' ⟧ β → p α ＝ p β) → n₁ ≤ n'
  min₀' = pr₂ prf₀'min₀'
  eemin : ∀(n' : ℕ) → (prf' : ∀(α β : ₂ℕ) → α ＝⟦ n' ⟧ β → p α ＝ p β) → min₀' n' prf' ＝ min₁ n' prf'
  eemin n' prf' = ≤-is-prop (min₀' n' prf') (min₁ n' prf')
  emin : ¬¬ (min₀' ＝ min₁)
  emin = fe² eemin
        -----
  ee : ¬¬ ((prf₀' , min₀') ＝ (prf₁ , min₁))
  ee = ¬¬to-×-＝ epr emin


Lemma[Map-discrete] : (X : Space)(Y : Set)(d : is-discrete Y)(h : is-set Y) →
                      (f g : Map X (DiscreteSpace Y d)) →
                      (∀(x : U X) → pr₁ f x ＝ pr₁ g x) → ¬¬ (f ＝ g)
Lemma[Map-discrete] X Y d h (f , cf) (g , cg) ex = ¬¬-kleisli claim ¬¬e₀
 where
  ¬¬e₀ : ¬¬ (f ＝ g)
  ¬¬e₀ = fe ex
        ----
  claim : f ＝ g → ¬¬ ((f , cf) ＝ (g , cg))
  claim e₀ = ¬¬to-Σ-＝ (e₀ , e₁)
   where
    W : ((p : ₂ℕ → U X) → p ∈ Probe X → ℕ) → Set
    W φ = (∀(p : ₂ℕ → U X) (pX : p ∈ Probe X) →
           ∀(α β : ₂ℕ) → α ＝⟦ φ p pX ⟧ β → g(p α) ＝ g(p β))
        × (∀(p : ₂ℕ → U X) → ∀(pX : p ∈ Probe X) →
           ∀(m : ℕ) → (∀(α β : ₂ℕ) → α ＝⟦ m ⟧ β → g(p α) ＝ g(p β)) → φ p pX ≤ m)

    cf' : ∀(p : ₂ℕ → U X) → p ∈ Probe X →
          Σ \(n : ℕ) →
            (∀(α β : ₂ℕ) → α ＝⟦ n ⟧ β → g(p α) ＝ g(p β))
          × (∀(m : ℕ) → (∀(α β : ₂ℕ) → α ＝⟦ m ⟧ β → g(p α) ＝ g(p β)) → n ≤ m)
    cf' = transport _ e₀ cf
    φf : (p : ₂ℕ → U X) → p ∈ Probe X → ℕ
    φf p pX = pr₁ (cf' p pX)
    Φf₀ : ∀(p : ₂ℕ → U X) (pX : p ∈ Probe X)
        → ∀(α β : ₂ℕ) → α ＝⟦ φf p pX ⟧ β → g(p α) ＝ g(p β)
    Φf₀ p pX = pr₁ (pr₂ (cf' p pX))
    Φf₁ : ∀(p : ₂ℕ → U X) (pX : p ∈ Probe X)
        → ∀(m : ℕ) → (∀(α β : ₂ℕ) → α ＝⟦ m ⟧ β → g(p α) ＝ g(p β)) → φf p pX ≤ m
    Φf₁ p pX = pr₂ (pr₂ (cf' p pX))
    CF : Σ \(φ : (p : ₂ℕ → U X) → p ∈ Probe X → ℕ) → W φ
    CF = (φf , Φf₀ , Φf₁)

    φg : (p : ₂ℕ → U X) → p ∈ Probe X → ℕ
    φg p pX = pr₁ (cg p pX)
    Φg₀ : ∀(p : ₂ℕ → U X) (pX : p ∈ Probe X)
        → ∀(α β : ₂ℕ) → α ＝⟦ φg p pX ⟧ β → g(p α) ＝ g(p β)
    Φg₀ p pX = pr₁ (pr₂ (cg p pX))
    Φg₁ : ∀(p : ₂ℕ → U X) (pX : p ∈ Probe X)
        → ∀(m : ℕ) → (∀(α β : ₂ℕ) → α ＝⟦ m ⟧ β → g(p α) ＝ g(p β)) → φg p pX ≤ m
    Φg₁ p pX = pr₂ (pr₂ (cg p pX))
    CG : Σ \(φ : (p : ₂ℕ → U X) → p ∈ Probe X → ℕ) → W φ
    CG = (φg , Φg₀ , Φg₁)

    epx : (p : ₂ℕ → U X) → (pX : p ∈ Probe X) → φf p pX ＝ φg p pX
    epx p pX = Lemma[m≤n∧n≤m→m=n] claim₀ claim₁
     where
      claim₀ : φf p pX ≤ φg p pX
      claim₀ = Φf₁ p pX (φg p pX) (Φg₀ p pX)
      claim₁ : φg p pX ≤ φf p pX
      claim₁ = Φg₁ p pX (φf p pX) (Φf₀ p pX)
    ¬¬eφ : ¬¬ (φf ＝ φg)
    ¬¬eφ = fe² epx
        -----

    claim-E : φf ＝ φg → ¬¬ (CF ＝ CG)
    claim-E eφ = ¬¬to-Σ-＝ (eφ , eΦ)
     where
      Φf' : W φg
      Φf' = transport W eφ (Φf₀ , Φf₁)
      Φf₀' : ∀(p : ₂ℕ → U X) (pX : p ∈ Probe X)
           → ∀(α β : ₂ℕ) → α ＝⟦ φg p pX ⟧ β → g(p α) ＝ g(p β)
      Φf₀' = pr₁ Φf'
      Φf₁' : ∀(p : ₂ℕ → U X) (pX : p ∈ Probe X)
           → ∀(m : ℕ) → (∀(α β : ₂ℕ) → α ＝⟦ m ⟧ β → g(p α) ＝ g(p β)) → φg p pX ≤ m
      Φf₁' = pr₂ Φf'
      eΦx₀ : (p : ₂ℕ → U X) → (pX : p ∈ Probe X) → ∀(α β : ₂ℕ) → (en : α ＝⟦ φg p pX ⟧ β)
           → Φf₀' p pX α β en ＝ Φg₀ p pX α β en
      eΦx₀ p pX α β en = h (Φf₀' p pX α β en) (Φg₀ p pX α β en)
      eΦ₀  : ¬¬ (Φf₀' ＝ Φg₀)
      eΦ₀  = fe⁵ eΦx₀
            -----
      eΦx₁ : (p : ₂ℕ → U X) → (pX : p ∈ Probe X) → (m : ℕ) →
             (pr : ∀(α β : ₂ℕ) → α ＝⟦ m ⟧ β → g(p α) ＝ g(p β))
           → Φf₁' p pX m pr ＝ Φg₁ p pX m pr
      eΦx₁ p pX m pr = ≤-is-prop (Φf₁' p pX m pr) (Φg₁ p pX m pr)
      eΦ₁  : ¬¬ (Φf₁' ＝ Φg₁)
      eΦ₁  = fe⁴ eΦx₁
            -----
      eΦ : ¬¬ ((Φf₀' , Φf₁') ＝ (Φg₀ , Φg₁))
      eΦ = ¬¬to-×-＝ eΦ₀ eΦ₁

    E : ¬¬ (CF ＝ CG)
    E = ¬¬-kleisli claim-E ¬¬eφ

    e₁ : ¬¬ (cf' ＝ cg)
    e₁ = ¬¬-functor (ap (λ w p pX → (pr₁ w p pX , pr₁(pr₂ w) p pX , pr₂(pr₂ w) p pX))) E

Lemma[Map-₂-＝] : (X : Space) → (f g : Map X 𝟚Space) →
                   (∀(x : U X) → pr₁ f x ＝ pr₁ g x) → ¬¬ (f ＝ g)
Lemma[Map-₂-＝] X = Lemma[Map-discrete] X 𝟚 𝟚-is-discrete 𝟚-is-set

Lemma[Map-ℕ-＝] : (X : Space) → (f g : Map X ℕSpace) →
                   (∀(x : U X) → pr₁ f x ＝ pr₁ g x) → ¬¬ (f ＝ g)
Lemma[Map-ℕ-＝] X = Lemma[Map-discrete] X ℕ ℕ-is-discrete ℕ-is-set

\end{code}
