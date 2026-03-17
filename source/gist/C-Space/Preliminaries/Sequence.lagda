Chuangjie Xu 2013 (ported to TypeTopology in 2025)

Module for both finite and infinite sequences of boolean 𝟚

\begin{code}

{-# OPTIONS --safe --without-K #-}

module gist.C-Space.Preliminaries.Sequence where

open import MLTT.Spartan hiding (_+_)
open import Naturals.Addition
open import UF.DiscreteAndSeparated

open import gist.C-Space.Preliminaries.Naturals.Order

\end{code}

Infinite sequences are defined as functions:

\begin{code}

₂ℕ : Set
₂ℕ = ℕ → 𝟚

0̄ : ₂ℕ
0̄ i = ₀
1̄ : ₂ℕ
1̄ i = ₁

\end{code}

Finite sequences are defined as vectors:

\begin{code}

infixr 50 _∷_

data ₂Fin : ℕ → Set where
 ⟨⟩ : ₂Fin 0
 _∷_ : {n : ℕ} → 𝟚 → ₂Fin n → ₂Fin (succ n)

head : {n : ℕ} → ₂Fin (succ n) → 𝟚
head (b ∷ _) = b

tail : {n : ℕ} → ₂Fin (succ n) → ₂Fin n
tail (_ ∷ s) = s

₂Fin-＝ : ∀{n : ℕ} {s s' : ₂Fin (succ n)}
       → head s ＝ head s' → tail s ＝ tail s' → s ＝ s'
₂Fin-＝ {n} {x ∷ xs} {.x ∷ .xs} refl refl = refl

⟨₀⟩ : ₂Fin 1
⟨₀⟩ = ₀ ∷ ⟨⟩
⟨₁⟩ : ₂Fin 1
⟨₁⟩ = ₁ ∷ ⟨⟩

ftake : (n k : ℕ) → ₂Fin (n + k) → ₂Fin k
ftake n 0        v       = ⟨⟩
ftake n (succ k) (h ∷ t) = h ∷ ftake n k t

fdrop : (n k : ℕ) → ₂Fin (n + k) → ₂Fin n
fdrop n 0        v       = v
fdrop n (succ k) (h ∷ t) = fdrop n k t

take : (m : ℕ) → ₂ℕ → ₂Fin m
take 0 α = ⟨⟩
take (succ n) α = α 0 ∷ take n (α ∘ succ)

drop : ℕ → ₂ℕ → ₂ℕ
drop 0 α = α
drop (succ m) α = drop m (α ∘ succ)

Lemma[drop+] : ∀(n : ℕ) → ∀(α : ₂ℕ) → ∀(i : ℕ) → drop n α i ＝ α (i + n)
Lemma[drop+] 0        α i = refl
Lemma[drop+] (succ n) α i = Lemma[drop+] n (α ∘ succ) i

isomorphism-₂Fin : ∀(X : Set) → ∀(n : ℕ) → (f : ₂Fin (succ n) → X) →
                    Σ \(g : 𝟚 → ₂Fin n → X) →
                     ∀(s : ₂Fin (succ n)) → f s ＝ g (head s) (tail s)
isomorphism-₂Fin X n f = g , prf
 where
  g : 𝟚 → ₂Fin n → X
  g b s = f (b ∷ s)
  prf : ∀(s : ₂Fin (succ n)) → f s ＝ g (head s) (tail s)
  prf (b ∷ s) = refl

max-fin : {n : ℕ} → (f : ₂Fin n → ℕ) →
           Σ \(m : ℕ) → ∀(s : ₂Fin n) → f s ≤ m
max-fin {0} f = (f ⟨⟩) , prf
 where
  prf : ∀(s : ₂Fin 0) → f s ≤ f ⟨⟩
  prf ⟨⟩ = ≤-refl
max-fin {succ n} f = m , prf
 where
  g : 𝟚 → ₂Fin n → ℕ
  g = pr₁ (isomorphism-₂Fin ℕ n f)
  m₀ : ℕ
  m₀ = pr₁ (max-fin (g ₀))
  prf₀ : ∀(s : ₂Fin n) → g ₀ s ≤ m₀
  prf₀ = pr₂ (max-fin (g ₀))
  m₁ : ℕ
  m₁ = pr₁ (max-fin (g ₁))
  prf₁ : ∀(s : ₂Fin n) → g ₁ s ≤ m₁
  prf₁ = pr₂ (max-fin (g ₁))
  m : ℕ
  m = max m₀ m₁
  prf : ∀(s : ₂Fin (succ n)) → f s ≤ m
  prf (₀ ∷ s) = ≤-trans (prf₀ s) (max-spec₀ m₀ m₁)
  prf (₁ ∷ s) = ≤-trans (prf₁ s) (max-spec₁ m₀ m₁)

\end{code}

Pointwise equality over infinite sequences:

\begin{code}

Lemma[∼-take] : ∀(n : ℕ) → ∀(α β : ₂ℕ) → α ∼ β → take n α ＝ take n β
Lemma[∼-take] 0        α β e = refl
Lemma[∼-take] (succ n) α β e = ₂Fin-＝ (e 0) (Lemma[∼-take] n (α ∘ succ) (β ∘ succ) (λ i → e (succ i)))

Lemma[∼-drop] : ∀(n : ℕ) → ∀(α β : ₂ℕ) → α ∼ β → drop n α ∼ drop n β
Lemma[∼-drop] 0        α β e = e
Lemma[∼-drop] (succ n) α β e = Lemma[∼-drop] n (α ∘ succ) (β ∘ succ) (λ i → e (succ i))

\end{code}

"Agree with" relation over infinite sequences, which is an equivalence
relation and a deciable type:

\begin{code}

infixl 10 _＝⟦_⟧_

data _＝⟦_⟧_ {X : Set} : (ℕ → X) → ℕ → (ℕ → X) → Set where
 ＝⟦zero⟧ : {α β : ℕ → X} → α ＝⟦ 0 ⟧ β
 ＝⟦succ⟧ : {α β : ℕ → X}{n : ℕ} → α ＝⟦ n ⟧ β → α n ＝ β n → α ＝⟦ succ n ⟧ β

＝⟦⟧-refl : {n : ℕ}{α : ₂ℕ} → α ＝⟦ n ⟧ α
＝⟦⟧-refl {0}      = ＝⟦zero⟧
＝⟦⟧-refl {succ n} = ＝⟦succ⟧ ＝⟦⟧-refl refl

＝⟦⟧-sym : {n : ℕ}{α β : ₂ℕ} → α ＝⟦ n ⟧ β → β ＝⟦ n ⟧ α
＝⟦⟧-sym {0}      ＝⟦zero⟧        = ＝⟦zero⟧
＝⟦⟧-sym {succ n} (＝⟦succ⟧ en e) = ＝⟦succ⟧ (＝⟦⟧-sym en) (e ⁻¹)

＝⟦⟧-trans : {n : ℕ}{α₀ α₁ α₂ : ₂ℕ} → α₀ ＝⟦ n ⟧ α₁ → α₁ ＝⟦ n ⟧ α₂ → α₀ ＝⟦ n ⟧ α₂
＝⟦⟧-trans {0}      ＝⟦zero⟧        ＝⟦zero⟧          = ＝⟦zero⟧
＝⟦⟧-trans {succ n} (＝⟦succ⟧ en e) (＝⟦succ⟧ en' e') = ＝⟦succ⟧ (＝⟦⟧-trans en en') (e ∙ e')

Lemma[＝⟦succ⟧]₀ : {α β : ₂ℕ}{n : ℕ} → α ＝⟦ succ n ⟧ β → α ＝⟦ n ⟧ β
Lemma[＝⟦succ⟧]₀ (＝⟦succ⟧ en _) = en

Lemma[＝⟦succ⟧]₁ : {α β : ₂ℕ}{n : ℕ} → α ＝⟦ succ n ⟧ β → α n ＝ β n
Lemma[＝⟦succ⟧]₁ (＝⟦succ⟧ _ e) = e

Lemma[＝⟦⟧-decidable] : {m : ℕ} → ∀(α β : ₂ℕ) → is-decidable (α ＝⟦ m ⟧ β)
Lemma[＝⟦⟧-decidable] {0}      α β = inl ＝⟦zero⟧
Lemma[＝⟦⟧-decidable] {succ m} α β = cases claim₀ claim₁ IH
 where
  IH : is-decidable (α ＝⟦ m ⟧ β)
  IH = Lemma[＝⟦⟧-decidable] {m} α β
  claim₀ : α ＝⟦ m ⟧ β → is-decidable (α ＝⟦ succ m ⟧ β)
  claim₀ em = cases c₀ c₁ (𝟚-is-discrete (α m) (β m))
   where
    c₀ : α m ＝ β m → is-decidable (α ＝⟦ succ m ⟧ β)
    c₀ e = inl (＝⟦succ⟧ em e)
    c₁ : ¬ (α m ＝ β m) → is-decidable (α ＝⟦ succ m ⟧ β)
    c₁ f = inr (λ e → f (Lemma[＝⟦succ⟧]₁ e))
  claim₁ : ¬ (α ＝⟦ m ⟧ β) → is-decidable (α ＝⟦ succ m ⟧ β)
  claim₁ f = inr (λ e → f(Lemma[＝⟦succ⟧]₀ e))

Lemma[＝⟦⟧-zero] : ∀{n : ℕ}{α β : ₂ℕ} → α ＝⟦ succ n ⟧ β → α 0 ＝ β 0
Lemma[＝⟦⟧-zero] {0}      (＝⟦succ⟧ ＝⟦zero⟧ e) = e
Lemma[＝⟦⟧-zero] {succ n} (＝⟦succ⟧ en e)      = Lemma[＝⟦⟧-zero] en

Lemma[＝⟦⟧-succ] : ∀{n : ℕ}{α β : ₂ℕ} → α ＝⟦ succ n ⟧ β → (α ∘ succ) ＝⟦ n ⟧ (β ∘ succ)
Lemma[＝⟦⟧-succ] {0}      _              = ＝⟦zero⟧
Lemma[＝⟦⟧-succ] {succ n} (＝⟦succ⟧ en e) = ＝⟦succ⟧ (Lemma[＝⟦⟧-succ] en) e

\end{code}

The following lemmas give an equivalent defintion of _＝⟦_⟧_:

\begin{code}

Lemma[<-＝⟦⟧] : ∀{n : ℕ}{α β : ₂ℕ} → (∀(i : ℕ) → i < n → α i ＝ β i) → α ＝⟦ n ⟧ β
Lemma[<-＝⟦⟧] {0}        {α} {β} f = ＝⟦zero⟧
Lemma[<-＝⟦⟧] {(succ n)} {α} {β} f = ＝⟦succ⟧ IH claim
 where
  f' : ∀(i : ℕ) → i < n → α i ＝ β i
  f' i r = f i (≤-trans r (Lemma[n≤n+1] n))
  IH : α ＝⟦ n ⟧ β
  IH = Lemma[<-＝⟦⟧] {n} {α} {β} f'
  claim : α n ＝ β n
  claim = f n ≤-refl

Lemma[＝⟦⟧-<] : ∀{n : ℕ}{α β : ₂ℕ} → α ＝⟦ n ⟧ β → ∀(i : ℕ) → i < n → α i ＝ β i
Lemma[＝⟦⟧-<] {0}      _ i        ()
Lemma[＝⟦⟧-<] {succ n} e 0        r          = Lemma[＝⟦⟧-zero] e
Lemma[＝⟦⟧-<] {succ n} e (succ i) (≤-succ r) = Lemma[＝⟦⟧-<] (Lemma[＝⟦⟧-succ] e) i r

\end{code}

Some useful lemmas about _＝⟦_⟧_:

\begin{code}

Lemma[＝⟦⟧-≤] : ∀{n m : ℕ}{α β : ₂ℕ} → α ＝⟦ n ⟧ β → m ≤ n → α ＝⟦ m ⟧ β
Lemma[＝⟦⟧-≤] {n} {m} {α} {β} en r = Lemma[<-＝⟦⟧] claim₁
 where
  claim₀ : ∀(i : ℕ) → i < n → α i ＝ β i
  claim₀ = Lemma[＝⟦⟧-<] en
  claim₁ : ∀(i : ℕ) → i < m → α i ＝ β i
  claim₁ i r' = claim₀ i (≤-trans r' r)

Lemma[＝⟦⟧-take] : ∀{n : ℕ}{α β : ₂ℕ} → α ＝⟦ n ⟧ β → take n α ＝ take n β
Lemma[＝⟦⟧-take] {0}      {α} {β} _  = refl
Lemma[＝⟦⟧-take] {succ n} {α} {β} en = ₂Fin-＝ base IH
 where
  base : α 0 ＝ β 0
  base = Lemma[＝⟦⟧-zero] en
  IH : take n (α ∘ succ) ＝ take n (β ∘ succ)
  IH = Lemma[＝⟦⟧-take] (Lemma[＝⟦⟧-succ] en)

Lemma[＝⟦⟧-drop] : ∀{n m : ℕ}{α β : ₂ℕ} → α ＝⟦ n + m ⟧ β → drop n α ＝⟦ m ⟧ drop n β
Lemma[＝⟦⟧-drop] {n} {0}      {α} {β} _               = ＝⟦zero⟧
Lemma[＝⟦⟧-drop] {n} {succ m} {α} {β} (＝⟦succ⟧ enm e) = ＝⟦succ⟧ IH goal
 where
  IH : drop n α ＝⟦ m ⟧ drop n β
  IH = Lemma[＝⟦⟧-drop] enm
  claim : ∀ γ → drop n γ m ＝ γ (n + m)
  claim γ = transport (λ k → drop n γ m ＝ γ k)
                      (addition-commutativity m n)
                      (Lemma[drop+] n γ m)
  goal : drop n α m ＝ drop n β m
  goal = claim α ∙ e ∙ (claim β) ⁻¹

\end{code}

Concatenation map:

\begin{code}

cons : {m : ℕ} → ₂Fin m → ₂ℕ → ₂ℕ
cons ⟨⟩      α          = α 
cons (h ∷ _) α 0        = h
cons (_ ∷ t) α (succ i) = cons t α i

cons₀ : ₂ℕ → ₂ℕ
cons₀ α 0        = ₀
cons₀ α (succ i) = α i
cons₁ : ₂ℕ → ₂ℕ
cons₁ α 0        = ₁
cons₁ α (succ i) = α i

Lemma[cons-take-drop] : ∀(n : ℕ) → ∀(α : ₂ℕ) → cons (take n α) (drop n α) ∼ α
Lemma[cons-take-drop] 0        α i        = refl
Lemma[cons-take-drop] (succ n) α 0        = refl
Lemma[cons-take-drop] (succ n) α (succ i) = Lemma[cons-take-drop] n (α ∘ succ) i

Lemma[cons-∼] : ∀{m : ℕ} → ∀(s : ₂Fin m) → ∀(α β : ₂ℕ) → α ∼ β → cons s α ∼ cons s β
Lemma[cons-∼] ⟨⟩      α β eq i        = eq i
Lemma[cons-∼] (h ∷ _) α β eq 0        = refl
Lemma[cons-∼] (_ ∷ t) α β eq (succ i) = Lemma[cons-∼] t α β eq i

lemma-blah : {n : ℕ}(s : ₂Fin n)(α β : ₂ℕ)(i : ℕ) → i < n → cons s α i ＝ cons s β i
lemma-blah ⟨⟩      α β i        ()
lemma-blah (b ∷ s) α β 0        r          = refl
lemma-blah (b ∷ s) α β (succ i) (≤-succ r) = lemma-blah s α β i r

Lemma[cons-＝⟦⟧] : ∀{n : ℕ} → ∀(s : ₂Fin n) → ∀(α β : ₂ℕ) → cons s α ＝⟦ n ⟧ cons s β
Lemma[cons-＝⟦⟧] s α β = Lemma[<-＝⟦⟧] (lemma-blah s α β)

Lemma[cons-take-＝⟦⟧] : ∀(n : ℕ) → ∀(α β : ₂ℕ) → α ＝⟦ n ⟧ cons (take n α) β
Lemma[cons-take-＝⟦⟧] n α β = Lemma[<-＝⟦⟧] (lemma n α β)
 where
  lemma : ∀(n : ℕ) → ∀(α β : ₂ℕ) → ∀(i : ℕ) → i < n → α i ＝ cons (take n α) β i
  lemma 0        α β i        ()
  lemma (succ n) α β 0        r          = refl
  lemma (succ n) α β (succ i) (≤-succ r) = lemma n (α ∘ succ) β i r

Lemma[cons-ftake-fdrop] : ∀(n k : ℕ) → ∀(s : ₂Fin (n + k)) → ∀(α : ₂ℕ) →
                          cons (ftake n k s) (cons (fdrop n k s) α) ∼ cons s α
Lemma[cons-ftake-fdrop] n 0        s       α i        = refl
Lemma[cons-ftake-fdrop] n (succ k) (b ∷ _) α 0        = refl
Lemma[cons-ftake-fdrop] n (succ k) (_ ∷ s) α (succ i) = Lemma[cons-ftake-fdrop] n k s α i

Lemma[cons-ftake-fdrop]² : ∀(n m l k : ℕ) → (eq : k ＝ m + l) →
                            ∀(s : ₂Fin (k + n)) → ∀(α : ₂ℕ) →
    cons (ftake k n s) 
         (cons (ftake m l (transport ₂Fin eq (fdrop k n s)))
               (cons (fdrop m l ((transport ₂Fin eq (fdrop k n s)))) α))
  ∼ cons s α
Lemma[cons-ftake-fdrop]² n m l k eq s α = goal
 where
  ss : ₂Fin k
  ss = fdrop k n s
  ss' : ₂Fin (m + l)
  ss' = transport ₂Fin eq ss
  Q : (i : ℕ) → ₂Fin i  → Set
  Q i t = cons (ftake k n s) (cons t α) ∼ cons s α
  claim₀ : cons (ftake k n s) (cons ss α) ∼ cons s α
  claim₀ = Lemma[cons-ftake-fdrop] k n s α
  transport² : {X : Set} (Y : X → Set) (Z : (x : X) → Y x → Set)
             → {x x' : X} {y : Y x}
             → (p : x ＝ x') → Z x y → Z x' (transport Y p y)
  transport² Y Z refl z = z
  claim₁ : cons (ftake k n s) (cons ss' α) ∼ cons s α
  claim₁ = transport² ₂Fin Q eq claim₀
  claim₂ : cons (ftake m l ss') (cons (fdrop m l ss') α) ∼ cons ss' α
  claim₂ = Lemma[cons-ftake-fdrop] m l ss' α
  claim₃ :  cons (ftake k n s) (cons (ftake m l ss') (cons (fdrop m l ss') α))
          ∼ cons (ftake k n s) (cons ss' α)
  claim₃ = Lemma[cons-∼] (ftake k n s)
                         (cons (ftake m l ss') (cons (fdrop m l ss') α))
                         (cons ss' α) claim₂
  goal : cons (ftake k n s) (cons (ftake m l ss') (cons (fdrop m l ss') α)) ∼ cons s α
  goal i = (claim₃ i) ∙ (claim₁ i)

Lemma[cons-＝⟦⟧-≤] : {n m : ℕ}{α β : ₂ℕ} → (s : ₂Fin n) → m ≤ n → cons s α ＝⟦ m ⟧ cons s β
Lemma[cons-＝⟦⟧-≤] _ ≤-zero     = ＝⟦zero⟧
Lemma[cons-＝⟦⟧-≤] s (≤-succ r) = ＝⟦succ⟧ (Lemma[cons-＝⟦⟧-≤] s (≤-r-succ r)) (lemma s r)
 where
  lemma : {n m : ℕ}{α β : ₂ℕ} → (s : ₂Fin (succ n)) → m ≤ n → cons s α m ＝ cons s β m
  lemma (b ∷ s) ≤-zero     = refl
  lemma (b ∷ s) (≤-succ r) = lemma s r

Lemma[＝⟦⟧-cons-take] : {α β : ₂ℕ} → ∀(n : ℕ) → α ＝⟦ n ⟧ cons (take n α) β
Lemma[＝⟦⟧-cons-take] {α} {β} n = lemma₁ n n ≤-refl
 where
  lemma₀ : ∀(α β : ₂ℕ)(m k : ℕ) → succ m ≤ k → α m ＝ cons (take k α) β m
  lemma₀ α β m        0        ()
  lemma₀ α β 0        (succ k) r          = refl
  lemma₀ α β (succ m) (succ k) (≤-succ r) = lemma₀ (α ∘ succ) β m k r
  lemma₁ : ∀(m k : ℕ) → m ≤ k → α ＝⟦ m ⟧ cons (take k α) β
  lemma₁ 0        k        ≤-zero     = ＝⟦zero⟧
  lemma₁ (succ m) 0        ()
  lemma₁ (succ m) (succ k) (≤-succ r) = ＝⟦succ⟧ (lemma₁ m (succ k) (≤-r-succ r))
                                                (lemma₀ α β m (succ k) (≤-succ r))

Lemma[＝⟦⟧-＝⟦⟧-take] : {α β γ : ₂ℕ} → ∀(n : ℕ) → α ＝⟦ n ⟧ β → β ＝⟦ n ⟧ cons (take n α) γ
Lemma[＝⟦⟧-＝⟦⟧-take] n en = ＝⟦⟧-trans (＝⟦⟧-sym en) (Lemma[＝⟦⟧-cons-take] n)

Lemma[cons-take-0] : {α β : ₂ℕ} → ∀(n : ℕ) → β 0 ＝ cons (take n α) β n
Lemma[cons-take-0]  0       = refl
Lemma[cons-take-0] (succ n) = Lemma[cons-take-0] n

\end{code}

Overwriting map:

\begin{code}

overwrite : ₂ℕ → ℕ → 𝟚 → ₂ℕ
overwrite α 0        b 0        = b
overwrite α 0        b (succ i) = α (succ i)
overwrite α (succ n) b 0        = α 0
overwrite α (succ n) b (succ i) = overwrite (α ∘ succ) n b i

Lemma[overwrite] : ∀(α : ₂ℕ) → ∀(n : ℕ) → ∀(b : 𝟚) → overwrite α n b n ＝ b
Lemma[overwrite] α 0        b = refl
Lemma[overwrite] α (succ n) b = Lemma[overwrite] (α ∘ succ) n b

Lemma[overwrite-≠] : ∀(α : ₂ℕ) → ∀(n : ℕ) → ∀(b : 𝟚) → ∀(i : ℕ) → i ≠ n → α i ＝ overwrite α n b i
Lemma[overwrite-≠] α 0        b 0        r = 𝟘-elim (r refl)
Lemma[overwrite-≠] α 0        b (succ i) r = refl
Lemma[overwrite-≠] α (succ n) b 0        r = refl
Lemma[overwrite-≠] α (succ n) b (succ i) r = Lemma[overwrite-≠] (α ∘ succ) n b i (λ e → r (ap succ e))

Lemma[overwrite-＝⟦⟧] : ∀(α : ₂ℕ) → ∀(n : ℕ) → ∀(b : 𝟚) → α ＝⟦ n ⟧ overwrite α n b
Lemma[overwrite-＝⟦⟧] α n b = Lemma[<-＝⟦⟧] claim
 where
  claim : ∀(i : ℕ) → i < n → α i ＝ overwrite α n b i
  claim i r = Lemma[overwrite-≠] α n b i (Lemma[m<n→m≠n] r)

\end{code}

The product of a family of deciable sets, indexed by finite sequences,
is also decidable.

\begin{code}

Lemma[₂Fin-decidability] : (n : ℕ) → (Y : ₂Fin n → Set)
                         → (∀ s → is-decidable (Y s)) → is-decidable (∀ s → Y s)
Lemma[₂Fin-decidability] 0 Y decY = cases (inl ∘ c₀) (inr ∘ c₁) (decY ⟨⟩)
 where
  c₀ : Y ⟨⟩ → ∀ s → Y s
  c₀ y ⟨⟩ = y
  c₁ : ¬ (Y ⟨⟩) → ¬ (∀ s → Y s)
  c₁ f g = f (g ⟨⟩) 
Lemma[₂Fin-decidability] (succ n) Y decY = cases c₀ c₁ IH₀
 where
  Y₀ : ₂Fin n → Set
  Y₀ s = Y (₀ ∷ s)
  decY₀ : ∀ s → is-decidable (Y₀ s)
  decY₀ s = decY (₀ ∷ s)
  IH₀ : is-decidable (∀ s → Y₀ s)
  IH₀ = Lemma[₂Fin-decidability] n Y₀ decY₀
  Y₁ : ₂Fin n → Set
  Y₁ s = Y (₁ ∷ s)
  decY₁ : ∀ s → is-decidable (Y₁ s)
  decY₁ s = decY (₁ ∷ s)
  IH₁ : is-decidable (∀ s → Y₁ s)
  IH₁ = Lemma[₂Fin-decidability] n Y₁ decY₁
  c₀ : (∀ s → Y₀ s) → is-decidable (∀ s → Y s)
  c₀ y₀ = cases (inl ∘ sc₀) (inr ∘ sc₁) IH₁
   where
    sc₀ : (∀ s → Y₁ s) → ∀ s → Y s
    sc₀ y₁ (₀ ∷ s) = y₀ s
    sc₀ y₁ (₁ ∷ s) = y₁ s
    sc₁ : ¬ (∀ s → Y₁ s) → ¬ (∀ s → Y s)
    sc₁ f₁ ys = f₁ (λ s → ys (₁ ∷ s))
  c₁ : ¬ (∀ s → Y₀ s) → is-decidable (∀ s → Y s)
  c₁ f₀ = inr (λ ys → f₀ (λ s → ys (₀ ∷ s)))

\end{code}
