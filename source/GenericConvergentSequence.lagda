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

open import SpartanMLTT renaming (_≤_ to _≤₂_) renaming (≤-anti to ≤₂-anti)
open import UF-Base
open import UF-Subsingletons
open import UF-Subsingletons-FunExt
open import UF-FunExt
open import UF-Embedding
open import UF-SetExamples
open import DiscreteAndSeparated
open import NaturalsOrder

funext₀ : U₁ ̇
funext₀ = funext U₀ U₀

\end{code}

Definition (The generic convergent sequence).
We use u,v to range over ℕ∞ and α,β to range over ₂ℕ:

\begin{code}

decreasing : (ℕ → 𝟚) → U₀ ̇
decreasing α = (i : ℕ) → α(succ i) ≤₂ α i 

decreasing-is-prop : funext₀ → (α : ℕ → 𝟚) → is-prop(decreasing α)
decreasing-is-prop fe α = is-prop-exponential-ideal fe
                            (λ i → is-prop-exponential-ideal fe (λ p → 𝟚-is-set))

ℕ∞ : U₀ ̇
ℕ∞ = Σ \(α : ℕ → 𝟚) → decreasing α

decreasing-is-prop-old : funext₀ → {α : ℕ → 𝟚} → is-prop(decreasing α)
decreasing-is-prop-old fe {α} p q = dfunext fe fact₂
 where
  fact₀ : (i : ℕ) (f g : α(succ i) ≡ ₁ → α i ≡ ₁) → f ≡ g
  fact₀ i f g = nfunext fe fact₁
   where
    fact₁ : (r : α (succ i) ≡ ₁) → f r ≡ g r
    fact₁ r = 𝟚-is-set (f r) (g r)
  fact₂ : (i : ℕ) → p i ≡ q i
  fact₂ i = fact₀ i (p i) (q i) 

incl : ℕ∞ → (ℕ → 𝟚)
incl = pr₁

incl-lc : funext₀ → left-cancellable incl
incl-lc fe = pr₁-lc (decreasing-is-prop fe _)  

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
    p : α (succ i) ≤₂ α i
    p = d i
    h : min𝟚 (α (succ i)) (α i) ≡ α (succ i)
    h = Lemma[a≤b→min𝟚ab≡a] p
    g' : min𝟚 (α (succ i)) (force-decreasing α i) ≡ α (succ i)
    g' = transport (λ b → min𝟚 (α (succ i)) b ≡ α (succ i)) (IH ⁻¹) h
    g : force-decreasing α (succ i) ≡ α (succ i)
    g = g'

lcni : (ℕ  → 𝟚) → ℕ∞
lcni β = force-decreasing β , force-decreasing-is-decreasing β

clni-incl : funext₀ → (x : ℕ∞) → lcni(incl x) ≡ x
clni-incl fe (α , d) = to-Σ-≡'' (dfunext fe (force-decreasing-unchanged α d) , decreasing-is-prop fe α _ _)

force-decreasing-is-smaller : (β : ℕ → 𝟚) (i : ℕ) → force-decreasing β i ≤₂ β i
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

Cantor-separated : funext₀ → separated (ℕ → 𝟚)
Cantor-separated fe = separated-ideal fe (λ _ → 𝟚-is-separated)

ℕ∞-separated : funext₀ → separated ℕ∞
ℕ∞-separated fe = subtype-of-separated-is-separated pr₁ (incl-lc fe) (Cantor-separated fe)

ℕ∞-is-set : funext₀ → is-set ℕ∞
ℕ∞-is-set fe = separated-is-set fe (ℕ∞-separated fe)

open import TotallySeparated

ℕ∞-totally-separated : funext₀ → totally-separated ℕ∞
ℕ∞-totally-separated fe {x} {y} α = g
 where
  p : ℕ → (ℕ∞ → 𝟚)
  p i x = incl x i
  l : incl x ≡ incl y
  l = dfunext fe (λ i → α (p i))
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

_⊑_ : ℕ∞ → ℕ → U₀ ̇
u ⊑ n = incl u n ≡ ₀

_⊏_ : ℕ → ℕ∞ → U₀ ̇
n ⊏ u = incl u n ≡ ₁

not-⊏-is-⊒ : {m : ℕ} {u : ℕ∞} → ¬(m ⊏ u) → u ⊑ m
not-⊏-is-⊒ f = Lemma[b≢₁→b≡₀] f

not-⊑-is-⊐ : {m : ℕ} {u : ℕ∞} → ¬(u ⊑ m) → m ⊏ u
not-⊑-is-⊐ f = Lemma[b≢₀→b≡₁] f

is-Zero : ℕ∞ → U₀ ̇
is-Zero u = u ⊑ 0

positive : ℕ∞ → U₀ ̇
positive u = 0 ⊏ u

positivity : ℕ∞ → 𝟚
positivity u = incl u 0 

is-Zero-Zero : is-Zero Zero
is-Zero-Zero = refl

Zero-not-Succ : {u : ℕ∞} → Zero ≢ Succ u
Zero-not-Succ {u} r = zero-is-not-one(ap positivity r)

∞ : ℕ∞
∞ = ((λ i → ₁) , λ i → id {U₀} {₁ ≡ ₁})

Succ-∞-is-∞ : funext₀ → Succ ∞ ≡ ∞
Succ-∞-is-∞ fe = incl-lc fe (dfunext fe lemma) 
 where
   lemma : (i : ℕ) → incl(Succ ∞) i ≡ incl ∞ i
   lemma 0 = refl
   lemma (succ i) = refl

unique-fixed-point-of-Succ : funext₀ → (u : ℕ∞) → u ≡ Succ u → u ≡ ∞
unique-fixed-point-of-Succ fe u r = incl-lc fe claim
 where
  fact : (i : ℕ) → incl u i ≡ incl(Succ u) i 
  fact i = ap (λ w → incl w i) r
  lemma : (i : ℕ) → incl u i ≡ ₁
  lemma 0 = fact 0
  lemma (succ i) = fact(succ i) ∙ lemma i
  claim : incl u ≡ incl ∞
  claim = (dfunext fe lemma)

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

-- This should be proved as a consequence of a more general theorem
-- with essentially the same proof:
under-embedding : funext₀ → is-embedding under
under-embedding fe x (x₀ , r₀) (x₁ , r₁) = to-Σ-≡'' (under-lc (r₀ ∙ r₁ ⁻¹) , ℕ∞-is-set fe _ _)

under-lc-refl : (k : ℕ) → under-lc refl ≡ refl {_} {ℕ} {k}
under-lc-refl 0 = refl
under-lc-refl (succ k) = ap (ap succ) (under-lc-refl k)

under-diagonal₀ : (n : ℕ) → under n ⊑ n
under-diagonal₀ 0 = refl
under-diagonal₀ (succ n) = under-diagonal₀ n

under-diagonal₁ : (n : ℕ) → n ⊏ under(succ n)
under-diagonal₁ 0 = refl
under-diagonal₁ (succ n) = under-diagonal₁ n
 
is-Zero-equal-Zero : funext₀ → {u : ℕ∞} → is-Zero u → u ≡ Zero
is-Zero-equal-Zero fe {u} base = incl-lc fe (dfunext fe lemma)
 where
  lemma : (i : ℕ) → incl u i ≡ incl Zero i
  lemma 0 = base
  lemma (succ i) = Lemma[[a≡₁→b≡₁]→b≡₀→a≡₀] (pr₂ u i) (lemma i)

not-Zero-is-Succ : funext₀ → {u : ℕ∞} → u ≢ Zero → u ≡ Succ(Pred u)
not-Zero-is-Succ fe {u} f = incl-lc fe (dfunext fe lemma)
 where
  lemma : (i : ℕ) → incl u i ≡ incl(Succ(Pred u)) i 
  lemma 0 = Lemma[b≢₀→b≡₁] (f ∘ is-Zero-equal-Zero fe)
  lemma (succ i) = refl

positive-is-not-Zero : {u : ℕ∞} → positive u → u ≢ Zero
positive-is-not-Zero {u} r s = lemma r
 where
  lemma : ¬(positive u)
  lemma = Lemma[b≡₀→b≢₁](ap positivity s)

positive-equal-Succ : funext₀ → {u : ℕ∞} → positive u → u ≡ Succ(Pred u)
positive-equal-Succ fe r = not-Zero-is-Succ fe (positive-is-not-Zero r)

Succ-criterion : funext₀ → {u : ℕ∞} {n : ℕ} → n ⊏ u → u ⊑ succ n → u ≡ Succ(under n)
Succ-criterion fe {u} {n} r s = incl-lc fe claim
 where
  lemma : (u : ℕ∞) (n : ℕ) → n ⊏ u → u ⊑ succ n 
        → (i : ℕ) → incl u i ≡ incl (Succ(under n)) i
  lemma u 0 r s 0 = r
  lemma u 0 r s (succ i) = lemma₀ i
     where 
      lemma₀ : (i : ℕ) → u ⊑ succ i
      lemma₀ 0 = s
      lemma₀ (succ i) = Lemma[[a≡₁→b≡₁]→b≡₀→a≡₀] (pr₂ u (succ i)) (lemma₀ i)
  lemma u (succ n) r s 0 = lemma₁ (succ n) r
     where 
      lemma₁ : (n : ℕ) → n ⊏ u → positive u
      lemma₁ 0 t = t
      lemma₁ (succ n) t = lemma₁ n (pr₂ u n t)
  lemma u (succ n) r s (succ i) = lemma (Pred u) n r s i
  claim : incl u ≡ incl (Succ (under n))
  claim = dfunext fe (lemma u n r s)


∞-is-not-ℕ : (n : ℕ) → ∞ ≢ under n
∞-is-not-ℕ n s = zero-is-not-one ((ap (λ w → incl w n) s ∙ under-diagonal₀ n)⁻¹)

not-ℕ-is-∞ : funext₀ → {u : ℕ∞} → ((n : ℕ) → u ≢ under n) → u ≡ ∞
not-ℕ-is-∞ fe {u} f = incl-lc fe (dfunext fe lemma) 
 where
  lemma : (n : ℕ) → n ⊏ u
  lemma 0 = Lemma[b≢₀→b≡₁](λ r → f 0 (is-Zero-equal-Zero fe r)) 
  lemma (succ n) = Lemma[b≢₀→b≡₁](λ r → f(succ n)(Succ-criterion fe (lemma n) r)) 

ℕ∞-density : funext₀ → {p : ℕ∞ → 𝟚} → ((n : ℕ) → p(under n) ≡ ₁) → p ∞ ≡ ₁ → (u : ℕ∞) → p u ≡ ₁
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

under𝟙-embedding : funext₀ → is-embedding under𝟙
under𝟙-embedding fe = disjoint-cases-embedding under (λ _ → ∞) (under-embedding fe) g d
 where
  g : is-embedding (λ _ → ∞)
  g x (* , p) (* , q) = ap (λ p → * , p) (ℕ∞-is-set fe p q)
  d : (n : ℕ) (y : 𝟙) → under n ≢ ∞
  d n _ p = ∞-is-not-ℕ n (p ⁻¹)

under𝟙-dense : funext₀ → ¬ Σ \(u : ℕ∞) → (x : ℕ + 𝟙) → u ≢ under𝟙 x
under𝟙-dense fe (u , f) = g (not-ℕ-is-∞ fe h)
 where
  g : u ≢ ∞
  g = f (inr *)
  h : (n : ℕ) → u ≢ under n 
  h n = f (inl n)

\end{code}

There should be a better proof of the following. The idea is simple:
by the above development, u = under 0 if and only if incl u 0 ≡ 0, and
u ≡ under(n+1) if and only if n ⊏ u ⊑ n+1.

\begin{code}

finite-isolated : funext₀ → (u : ℕ∞) (n : ℕ) → (u ≡ under n) + (u ≢ under n)
finite-isolated fe u 0 = two-equality-cases lemma₀ lemma₁
 where 
  lemma₀ : is-Zero u → (u ≡ Zero) + (u ≢ Zero)
  lemma₀ r = inl(is-Zero-equal-Zero fe r)
  lemma₁ : positive u → (u ≡ Zero) + (u ≢ Zero)
  lemma₁ r = inr(contrapositive fact (Lemma[b≡₁→b≢₀] r))
    where fact : u ≡ Zero → is-Zero u
          fact r = ap (λ u → incl u 0) r
finite-isolated fe u (succ n) = two-equality-cases lemma₀ lemma₁
 where
  lemma₀ :  u ⊑ n → (u ≡ under(succ n)) + (u ≢ under(succ n))
  lemma₀ r = inr(contrapositive lemma (Lemma[b≡₀→b≢₁] r))
   where
    lemma : u ≡ under(succ n) → n ⊏ u
    lemma r = ap (λ v → incl v n) r ∙ under-diagonal₁ n
  lemma₁ :  n ⊏ u → (u ≡ under(succ n)) + (u ≢ under(succ n))
  lemma₁ r = two-equality-cases lemma₁₀ lemma₁₁
   where
    lemma₁₀ :  u ⊑ succ n → (u ≡ under(succ n)) + (u ≢ under(succ n))
    lemma₁₀ s = inl(Succ-criterion fe r s)
    lemma₁₁ :  succ n ⊏ u → (u ≡ under(succ n)) + (u ≢ under(succ n))
    lemma₁₁ s = inr (contrapositive lemma (Lemma[b≡₁→b≢₀] s))
     where
      lemma : u ≡ under(succ n) → u ⊑ succ n
      lemma r = ap (λ v → incl v (succ n)) r ∙ under-diagonal₀(succ n)

under-lemma : funext₀ → (u : ℕ∞) (n : ℕ) → u ⊑ n → Σ \(m : ℕ) → (m ≤ n) × (u ≡ under m)
under-lemma fe u zero p     = zero , ≤-refl zero , is-Zero-equal-Zero fe p
under-lemma fe u (succ n) p = g (𝟚-discrete (incl u n) ₀)
 where
  IH : u ⊑ n → Σ \(m : ℕ) → (m ≤ n) × (u ≡ under m)
  IH = under-lemma fe u n
  g :  decidable(u ⊑ n) → Σ \(m : ℕ) → (m ≤ succ n) × (u ≡ under m)
  g (inl q) = pr₁(IH q) , ≤-trans (pr₁(IH q)) n (succ n) (pr₁(pr₂(IH q))) (≤-succ n) , pr₂(pr₂(IH q))
  g (inr φ) = succ n , ≤-refl n , s
    where
      q : n ⊏ u
      q = Lemma[b≢₀→b≡₁] φ
      s : u ≡ Succ (under n)
      s = Succ-criterion fe {u} {n} q p

\end{code}

Order on ℕ∞:

\begin{code}

_≼_ : ℕ∞ → ℕ∞ → U₀ ̇
u ≼ v = (n : ℕ) → n ⊏ u → n ⊏ v

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

∞-⊏-maximal : (n : ℕ) → n ⊏ ∞
∞-⊏-maximal n = refl

_≺_ : ℕ∞ → ℕ∞ → U₀ ̇
u ≺ v = Σ \(n : ℕ) → (u ≡ under n) × n ⊏ v

≺-prop-valued : funext₀ → (u v : ℕ∞) → is-prop (u ≺ v)
≺-prop-valued fe u v (n , r , a) (m , s , b) =
  to-Σ-≡'' (under-lc (r ⁻¹ ∙ s) , to-Σ-≡'' (ℕ∞-is-set fe _ _ , 𝟚-is-set _ _))

⊏-gives-≺ : (n : ℕ) (u : ℕ∞) → n ⊏ u → under n ≺ u
⊏-gives-≺ n u a = n , refl , a

≺-gives-⊏ : (n : ℕ) (u : ℕ∞) → under n ≺ u → n ⊏ u
≺-gives-⊏ n u (m , r , a) = back-transport (λ k → k ⊏ u) (under-lc r) a

∞-maximal : (n : ℕ) → under n ≺ ∞
∞-maximal n = n , refl , ∞-⊏-maximal n

⊏-reflect : (m n : ℕ) →  m ⊏ under n → m < n
⊏-reflect zero zero ()
⊏-reflect zero (succ n) l = zero-minimal n
⊏-reflect (succ m) zero ()
⊏-reflect (succ m) (succ n) l = ⊏-reflect m n l

⊏-back : (u : ℕ∞) (n : ℕ) → succ n ⊏ u → n ⊏ u
⊏-back = pr₂

⊏-trans'' : (u : ℕ∞) (n : ℕ) → (m : ℕ) → m ≤ n → n ⊏ u → m ⊏ u
⊏-trans'' u = regress (λ n → n ⊏ u) (⊏-back u) 

⊏-trans' : (u : ℕ∞) (n : ℕ) → (m : ℕ) → m < n → n ⊏ u → m ⊏ u
⊏-trans' u n m l = ⊏-trans'' u n m (≤-trans m (succ m) n (≤-succ m) l)

⊏-trans : (m n : ℕ) (u : ℕ∞) → m ⊏ under n → n ⊏ u → m ⊏ u
⊏-trans m n u a = ⊏-trans' u n m (⊏-reflect m n a)

≺-trans : (u v w : ℕ∞) → u ≺ v → v ≺ w → u ≺ w
≺-trans u v w (m , r , a) (n , s , b) = m , r , ⊏-trans m n w (transport (λ t → m ⊏ t) s a) b

open import Ordinals hiding (_≤_) hiding (≤-refl)

≺-well-founded₂ : funext₀ → is-well-founded₂ _≺_
≺-well-founded₂ fe p φ = ℕ∞-density fe a b
 where
  γ : (n : ℕ) → ((m : ℕ) → m < n → p (under m) ≡ ₁) → p (under n) ≡ ₁
  γ n g = φ (under n) h
   where
    h : (u : ℕ∞) → u ≺ under n → p u ≡ ₁
    h u (m , r , l) = back-transport (λ v → p v ≡ ₁) r (g m (⊏-reflect m n l))
  a : (n : ℕ) → p(under n) ≡ ₁
  a = course-of-values-induction (λ n → p(under n) ≡ ₁) γ
  f : (u : ℕ∞) → u ≺ ∞ → p u ≡ ₁
  f u (n , r , l) = back-transport (λ v → p v ≡ ₁) r (a n)
  b : p ∞ ≡ ₁
  b = φ ∞ f

≺-extensional : funext₀ → is-extensional _≺_
≺-extensional fe u v l m = γ
 where
  f : (i : ℕ) → i ⊏ u → i ⊏ v
  f i a = ≺-gives-⊏ i v (l (under i) (⊏-gives-≺ i u a))
  g : (i : ℕ) → i ⊏ v → i ⊏ u
  g i a = ≺-gives-⊏ i u (m (under i) (⊏-gives-≺ i v a))
  h : (i : ℕ) → incl u i ≡ incl v i
  h i = ≤₂-anti (f i) (g i)
  γ : u ≡ v
  γ = incl-lc fe (dfunext fe h)

ℕ∞-ordinal₂ : funext₀ → is-ordinal₂ _≺_
ℕ∞-ordinal₂ fe = (≺-well-founded₂ fe) , (≺-extensional fe) , ≺-trans

≺-cotransitive : funext₀ → cotransitive _≺_
≺-cotransitive fe u v w (n , r , a) = g (𝟚-discrete (incl w n) ₁)
 where
  g : decidable(n ⊏ w) → (u ≺ w) + (w ≺ v)
  g (inl a) = inl (n , r , a)
  g (inr f) = inr (m , s , ⊏-trans'' v n m l a)
   where
    b : w ⊑ n
    b = not-⊏-is-⊒ {n} {w} f
    σ : Σ \(m : ℕ) → (m ≤ n) × (w ≡ under m)
    σ = under-lemma fe w n b
    m : ℕ
    m = pr₁ σ
    l : m ≤ n
    l = pr₁(pr₂ σ)
    s : w ≡ under m
    s = pr₂(pr₂ σ)

\end{code}

precedences:

\begin{code}

infix  30 _⊏_
infix  30 _≺_

\end{code}
