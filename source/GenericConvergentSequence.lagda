Martin Escardo 2012.

See my paper "Infinite sets that satisfy the principle of
omniscience" for a discussion of the type ℕ∞ defined here. 
Essentially, ℕ∞ is ℕ with an added point ∞.

(Added December 2017. What we knew for a long time: The ℕ∞ is a
retract of the Cantor type ℕ → 𝟚. This required adding a number of
lemmas.)

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module GenericConvergentSequence where

open import SpartanMLTT
open import UF-Base
open import UF-Subsingletons
open import UF-Subsingletons-FunExt
open import UF-FunExt
open import UF-Embedding
open import UF-SetExamples
open import DiscreteAndSeparated

FunExt₀ : U₁ ̇
FunExt₀ = FunExt U₀ U₀

\end{code}

Definition (The generic convergent sequence).
We use u,v to range over ℕ∞ and α,β to range over ₂ℕ:

\begin{code}

decreasing : (ℕ → 𝟚) → U₀ ̇
decreasing α = (i : ℕ) → α i ≥ α(succ i)

decreasing-isProp : FunExt₀ → (α : ℕ → 𝟚) → isProp(decreasing α)
decreasing-isProp fe α = isProp-exponential-ideal fe (λ i → isProp-exponential-ideal fe (λ p → 𝟚-isSet))

ℕ∞ : U₀ ̇
ℕ∞ = Σ \(α : ℕ → 𝟚) → decreasing α

{- Old:
decreasing-isProp : FunExt₀ → {α : ℕ → 𝟚} → isProp(decreasing α)
decreasing-isProp fe {α} p q = funext fe fact₂
 where
  fact₀ : (i : ℕ) (f g : α(succ i) ≡ ₁ → α i ≡ ₁) → f ≡ g
  fact₀ i f g = funext fe fact₁
   where
    fact₁ : (r : α (succ i) ≡ ₁) → f r ≡ g r
    fact₁ r = 𝟚-isSet (f r) (g r)
  fact₂ : (i : ℕ) → p i ≡ q i
  fact₂ i = fact₀ i (p i) (q i) 
-}

incl : ℕ∞ → (ℕ → 𝟚)
incl = pr₁

incl-lc : FunExt₀ → left-cancellable incl
incl-lc fe = pr₁-lc (decreasing-isProp fe _)  

force-decreasing : (ℕ → 𝟚) → (ℕ → 𝟚)
force-decreasing β 0 = β 0
force-decreasing β (succ i) = min𝟚 (β(succ i)) (force-decreasing β i)

force-decreasing-is-decreasing : (β : ℕ → 𝟚) → decreasing(force-decreasing β)
force-decreasing-is-decreasing β zero     = Lemma[min𝟚ab≡₁→b≡₁] {β 1} {β zero}
force-decreasing-is-decreasing β (succ i) = Lemma[minab≤b] {β (succ (succ i))} {force-decreasing β (succ i)}

force-decreasing-unchanged : (α : ℕ → 𝟚) → decreasing α → force-decreasing α ∼ α
force-decreasing-unchanged α d zero     = refl
force-decreasing-unchanged α d (succ i) = g
  where
    IH : force-decreasing α i ≡ α i
    IH = force-decreasing-unchanged α d i
    p : α (succ i) ≤ α i
    p = d i
    h : min𝟚 (α (succ i)) (α i) ≡ α (succ i)
    h = Lemma[a≤b→min𝟚ab≡a] p
    g' : min𝟚 (α (succ i)) (force-decreasing α i) ≡ α (succ i)
    g' = transport (λ b → min𝟚 (α (succ i)) b ≡ α (succ i)) (IH ⁻¹) h
    g : force-decreasing α (succ i) ≡ α (succ i)
    g = g'

lcni : (ℕ  → 𝟚) → ℕ∞
lcni β = force-decreasing β , force-decreasing-is-decreasing β

clni-incl : FunExt₀ → (x : ℕ∞) → lcni(incl x) ≡ x
clni-incl fe (α , d) = to-Σ-≡ (force-decreasing α) α (force-decreasing-is-decreasing α) d
                               (funext fe (force-decreasing-unchanged α d)) (decreasing-isProp fe α _ _)

force-decreasing-is-smaller : (β : ℕ → 𝟚) (i : ℕ) → force-decreasing β i ≤ β i
force-decreasing-is-smaller β zero     p = p
force-decreasing-is-smaller β (succ i) p = Lemma[min𝟚ab≡₁→a≡₁] p

force-decreasing-is-not-much-smaller : (β : ℕ → 𝟚) (n : ℕ) → force-decreasing β n ≡ ₀ → (Σ \(m : ℕ) → β m ≡ ₀)
force-decreasing-is-not-much-smaller β zero  p    = zero , p
force-decreasing-is-not-much-smaller β (succ n) p = f c
  where
    A = Σ \(m : ℕ) → β m ≡ ₀
    c : (β (succ n) ≡ ₀) + (force-decreasing β n ≡ ₀)
    c = lemma[min𝟚ab≡₀] {β (succ n)} {force-decreasing β n} p
    f : (β (succ n) ≡ ₀) + (force-decreasing β n ≡ ₀) → A
    f (inl q) = succ n , q
    f (inr r) = force-decreasing-is-not-much-smaller β n r

Cantor-separated : FunExt₀ → separated (ℕ → 𝟚)
Cantor-separated fe = separated-ideal fe (λ _ → 𝟚-is-separated)

ℕ∞-separated : FunExt₀ → separated ℕ∞
ℕ∞-separated fe = subtype-of-separated-is-separated pr₁ (incl-lc fe) (Cantor-separated fe)

ℕ∞-set : FunExt₀ → isSet ℕ∞
ℕ∞-set fe = separated-isSet fe (ℕ∞-separated fe)

open import TotallySeparated

ℕ∞-totally-separated : FunExt₀ → totally-separated ℕ∞
ℕ∞-totally-separated fe {x} {y} α = g
 where
  p : ℕ → (ℕ∞ → 𝟚)
  p i x = incl x i
  l : incl x ≡ incl y
  l = funext fe (λ i → α (p i))
  g : x ≡ y
  g = incl-lc fe l

Zero : ℕ∞
Zero = ((λ i → ₀) , λ i → id {U₀} {₀ ≡ ₁})

Succ : ℕ∞ → ℕ∞
Succ (α , d) = (α' , d')
 where 
  α' : ℕ → 𝟚
  α' 0 = ₁
  α'(succ n) = α n
  d' : decreasing α'
  d' 0 = λ r → refl
  d' (succ i) = d i

positivity : ℕ∞ → 𝟚
positivity u = incl u 0 

isZero : ℕ∞ → U₀ ̇
isZero u = positivity u ≡ ₀

positive : ℕ∞ → U₀ ̇
positive u = positivity u ≡ ₁

isZero-Zero : isZero Zero
isZero-Zero = refl

Zero-not-Succ : {u : ℕ∞} → Zero ≢ Succ u
Zero-not-Succ {u} r = zero-is-not-one(ap positivity r)

∞ : ℕ∞
∞ = ((λ i → ₁) , λ i → id {U₀} {₁ ≡ ₁})

Succ-∞-is-∞ : FunExt₀ → Succ ∞ ≡ ∞
Succ-∞-is-∞ fe = incl-lc fe (funext fe lemma) 
 where
   lemma : (i : ℕ) → incl(Succ ∞) i ≡ incl ∞ i
   lemma 0 = refl
   lemma (succ i) = refl

unique-fixed-point-of-Succ : FunExt₀ → (u : ℕ∞) → u ≡ Succ u → u ≡ ∞
unique-fixed-point-of-Succ fe u r = incl-lc fe (funext fe lemma)
 where
  fact : (i : ℕ) → incl u i ≡ incl(Succ u) i 
  fact i = ap (λ w → incl w i) r
  lemma : (i : ℕ) → incl u i ≡ ₁
  lemma 0 = fact 0
  lemma (succ i) = fact(succ i) ∙ lemma i

Pred : ℕ∞ → ℕ∞
Pred(α , d) = (α ∘ succ , d ∘ succ)

Pred-Zero-is-Zero : Pred Zero ≡ Zero
Pred-Zero-is-Zero = refl 

Pred-Succ-u-is-u : {u : ℕ∞} → Pred(Succ u) ≡ u
Pred-Succ-u-is-u {u} = refl

Pred-∞-is-∞ : Pred ∞ ≡ ∞
Pred-∞-is-∞ = refl

Succ-lc : left-cancellable Succ
Succ-lc = ap Pred

under : ℕ → ℕ∞
under 0 = Zero
under (succ n) = Succ(under n)

_≣_ : ℕ∞ → ℕ → U₀ ̇
u ≣ n = u ≡ under n

under-lc : left-cancellable under
under-lc {0} {0} r = refl
under-lc {0} {succ n} r = 𝟘-elim(Zero-not-Succ r)
under-lc {succ m} {0} r = 𝟘-elim(Zero-not-Succ (r ⁻¹))
under-lc {succ m} {succ n} r = ap succ (under-lc {m} {n} (Succ-lc r))

-- This should be proved as a consequence of a general theorem:
under-embedding : FunExt₀ → isEmbedding under
under-embedding fe x (x₀ , r₀) (x₁ , r₁) =
  to-Σ-≡ x₀ x₁ r₀ r₁ (under-lc (r₀ ∙ r₁ ⁻¹)) (ℕ∞-set fe _ _)

under-lc-refl : (k : ℕ) → under-lc refl ≡ refl {_} {ℕ} {k}
under-lc-refl 0 = refl
under-lc-refl (succ k) = ap (ap succ) (under-lc-refl k)

under-diagonal₀ : (n : ℕ) → incl(under n) n ≡ ₀
under-diagonal₀ 0 = refl
under-diagonal₀ (succ n) = under-diagonal₀ n

under-diagonal₁ : (n : ℕ) → incl(under(succ n)) n ≡ ₁

under-diagonal₁ 0 = refl
under-diagonal₁ (succ n) = under-diagonal₁ n
 
isZero-equal-Zero : FunExt₀ → {u : ℕ∞} → isZero u → u ≡ Zero
isZero-equal-Zero fe {u} base = incl-lc fe (funext fe lemma)
 where
  lemma : (i : ℕ) → incl u i ≡ incl Zero i
  lemma 0 = base
  lemma (succ i) = Lemma[[a≡₁→b≡₁]→b≡₀→a≡₀] (pr₂ u i) (lemma i)

not-Zero-is-Succ : FunExt₀ → {u : ℕ∞} → u ≢ Zero → u ≡ Succ(Pred u)
not-Zero-is-Succ fe {u} f = incl-lc fe (funext fe lemma)
 where
  lemma : (i : ℕ) → incl u i ≡ incl(Succ(Pred u)) i 
  lemma 0 = Lemma[b≢₀→b≡₁] (f ∘ isZero-equal-Zero fe)
  lemma (succ i) = refl

positive-is-not-Zero : {u : ℕ∞} → positive u → u ≢ Zero
positive-is-not-Zero {u} r s = lemma r
 where
  lemma : ¬(positive u)
  lemma = Lemma[b≡₀→b≢₁](ap positivity s)

positive-equal-Succ : FunExt₀ → {u : ℕ∞} → positive u → u ≡ Succ(Pred u)
positive-equal-Succ fe r = not-Zero-is-Succ fe (positive-is-not-Zero r)

Succ-criterion : FunExt₀ → {u : ℕ∞} {n : ℕ} → incl u n ≡ ₁ → incl u(succ n) ≡ ₀ → u ≡ Succ(under n)
Succ-criterion fe {u} {n} r s = incl-lc fe (funext fe (lemma u n r s))
 where
  lemma : (u : ℕ∞) (n : ℕ) → incl u n ≡ ₁ → incl u(succ n) ≡ ₀ 
        → (i : ℕ) → incl u i ≡ incl (Succ(under n)) i
  lemma u 0 r s 0 = r
  lemma u 0 r s (succ i) = lemma₀ i
     where 
      lemma₀ : (i : ℕ) → incl u (succ i) ≡ ₀ 
      lemma₀ 0 = s
      lemma₀ (succ i) = Lemma[[a≡₁→b≡₁]→b≡₀→a≡₀] (pr₂ u (succ i)) (lemma₀ i)
  lemma u (succ n) r s 0 = lemma₁ (succ n) r
     where 
      lemma₁ : (n : ℕ) → incl u n ≡ ₁ → positive u
      lemma₁ 0 t = t
      lemma₁ (succ n) t = lemma₁ n (pr₂ u n t)
  lemma u (succ n) r s (succ i) = lemma (Pred u) n r s i


∞-is-not-ℕ : (n : ℕ) → ∞ ≢ under n
∞-is-not-ℕ n s = zero-is-not-one ((ap (λ w → incl w n) s ∙ under-diagonal₀ n)⁻¹)

not-ℕ-is-∞ : FunExt₀ → {u : ℕ∞} → ((n : ℕ) → u ≢ under n) → u ≡ ∞
not-ℕ-is-∞ fe {u} f = incl-lc fe (funext fe lemma) 
 where
  lemma : (n : ℕ) → incl u n ≡ ₁
  lemma 0 = Lemma[b≢₀→b≡₁](λ r → f 0 (isZero-equal-Zero fe r)) 
  lemma (succ n) = Lemma[b≢₀→b≡₁](λ r → f(succ n)(Succ-criterion fe (lemma n) r)) 

ℕ∞-density : FunExt₀ → {p : ℕ∞ → 𝟚} → ((n : ℕ) → p(under n) ≡ ₁) → p ∞ ≡ ₁ → (u : ℕ∞) → p u ≡ ₁
ℕ∞-density fe {p} f r u = Lemma[b≢₀→b≡₁] lemma
 where 
  claim : p u ≡ ₀ → (n : ℕ) → u ≢ under n
  claim g n = contrapositive (λ s → ap p s ∙ f n) (Lemma[b≡₀→b≢₁] g)

  claim-∞ : p u ≡ ₀ → u ≢ ∞
  claim-∞ = (contrapositive (λ s → ap p s ∙ r)) ∘ Lemma[b≡₀→b≢₁]

  lemma : p u ≢ ₀
  lemma t = claim-∞ t (not-ℕ-is-∞ fe (claim t)) 

under𝟙 : ℕ + 𝟙 → ℕ∞
under𝟙 = cases under (λ _ → ∞)

under𝟙-embedding : FunExt₀ → isEmbedding under𝟙
under𝟙-embedding fe = disjoint-cases-embedding under (λ _ → ∞) (under-embedding fe) g d
 where
  g : isEmbedding (λ _ → ∞)
  g x (* , p) (* , q) = ap (λ p → * , p) (ℕ∞-set fe p q)
  d : (n : ℕ) (y : 𝟙) → under n ≢ ∞
  d n _ p = ∞-is-not-ℕ n (p ⁻¹)

under𝟙-dense : FunExt₀ → ¬ Σ \(u : ℕ∞) → Π \(x : ℕ + 𝟙) → u ≢ under𝟙 x
under𝟙-dense fe (u , f) = g (not-ℕ-is-∞ fe h)
 where
  g : u ≢ ∞
  g = f (inr *)
  h : (n : ℕ) → u ≢ under n 
  h n = f (inl n)

\end{code}

There should be a better proof of the following. The idea is simple:
by the above development, u = under 0 if and only if incl u 0 ≡ 0, and
u ≡ under(n+1) if and only incl u n ≡ ₁ and incl u (n+1) ≡ ₀.

\begin{code}

finite-isolated : FunExt₀ → (u : ℕ∞) (n : ℕ) → (u ≡ under n) + (u ≢ under n)
finite-isolated fe u 0 = two-equality-cases lemma₀ lemma₁
 where 
  lemma₀ : isZero u → (u ≡ Zero) + (u ≢ Zero)
  lemma₀ r = inl(isZero-equal-Zero fe r)
  lemma₁ : positive u → (u ≡ Zero) + (u ≢ Zero)
  lemma₁ r = inr(contrapositive fact (Lemma[b≡₁→b≢₀] r))
    where fact : u ≡ Zero → isZero u
          fact r = ap (λ u → incl u 0) r
finite-isolated fe u (succ n) = two-equality-cases lemma₀ lemma₁
 where
  lemma₀ :  incl u n ≡ ₀ → (u ≡ under(succ n)) + (u ≢ under(succ n))
  lemma₀ r = inr(contrapositive lemma (Lemma[b≡₀→b≢₁] r))
   where
    lemma : u ≡ under(succ n) → incl u n ≡ ₁
    lemma r = ap (λ v → incl v n) r ∙ under-diagonal₁ n
  lemma₁ :  incl u n ≡ ₁ → (u ≡ under(succ n)) + (u ≢ under(succ n))
  lemma₁ r = two-equality-cases lemma₁₀ lemma₁₁
   where
    lemma₁₀ :  incl u (succ n) ≡ ₀ → (u ≡ under(succ n)) + (u ≢ under(succ n))
    lemma₁₀ s = inl(Succ-criterion fe r s)
    lemma₁₁ :  incl u (succ n) ≡ ₁ → (u ≡ under(succ n)) + (u ≢ under(succ n))
    lemma₁₁ s = inr (contrapositive lemma (Lemma[b≡₁→b≢₀] s))
     where
      lemma : u ≡ under(succ n) → incl u (succ n) ≡ ₀
      lemma r = ap (λ v → incl v (succ n)) r ∙ under-diagonal₀(succ n)

open import DiscreteAndSeparated

under-lemma : FunExt₀ → (u : ℕ∞) (n : ℕ) → incl u n ≡ ₀ → Σ \(m : ℕ) → u ≡ under m
under-lemma fe u zero p     = zero , isZero-equal-Zero fe p
under-lemma fe u (succ n) p = g (𝟚-discrete (incl u n) ₀)
 where
  g :  decidable(incl u n ≡ ₀) → Σ \(m : ℕ) → u ≡ under m
  g (inl p) = under-lemma fe u n p
  g (inr φ) = succ n , s
    where
      q : incl u n ≡ ₁
      q = Lemma[b≢₀→b≡₁] φ
      s : u ≡ Succ (under n)
      s = Succ-criterion fe {u} {n} q p

\end{code}

Order on ℕ∞:

\begin{code}

_≼_ : ℕ∞ → ℕ∞ → U₀ ̇
u ≼ v = (n : ℕ) → incl u n ≤ incl v n

∞-greatest : (u : ℕ∞) → u ≼ ∞
∞-greatest u = λ n _ → refl

max : ℕ∞ → ℕ∞ → ℕ∞
max (α , r) (β , s) = (λ i → max𝟚 (α i) (β i)) , t
 where
  t : decreasing (λ i → max𝟚 (α i) (β i))
  t i p = max𝟚-lemma-converse (α i) (β i) (f (max𝟚-lemma(α(succ i)) (β(succ i)) p))
    where
     f : (α(succ i) ≡ ₁) + (β(succ i) ≡ ₁) → (α i ≡ ₁) + (β i ≡ ₁)
     f (inl p) = inl (r i p)
     f (inr p) = inr (s i p)

\end{code}

More lemmas about order should be added, but I will do this on demand
as the need arises.

\begin{code}

_⊏_ : ℕ → ℕ∞ → U₀ ̇
n ⊏ u = incl u n ≡ ₁

infix  30 _⊏_

_≺_ : ℕ∞ → ℕ∞ → U₀ ̇
u ≺ v = Σ \(n : ℕ) → (u ≡ under n) × n ⊏ v

{-

≺-OK-founded : (p : ℕ∞ → 𝟚) → ((v : ℕ∞) → ((u : ℕ∞) → u ≺ v → p u ≡ ₁) → p v ≡ ₁) → (v : ℕ∞) → p v ≡ ₁
≺-OK-founded p φ = ℕ∞-density a b
 where
  a : (n : ℕ) → p(under n) ≡ ₁
  a zero = φ (under zero) f
   where
    f : (u : ℕ∞) → u ≺ under zero → p u ≡ ₁
    f u (_ , _ , ())
  a (succ n) = {!!}

  b : p ∞ ≡ ₁
  b = {!!}

-}
\end{code}
