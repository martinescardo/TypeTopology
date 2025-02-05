Martin Escardo and Tom de Jong, August 2024

Moved from the file InjectiveTypes.CounterExamples on 12 September 2024.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.PropTrunc

module Apartness.Properties
        (pt : propositional-truncations-exist)
       where

open import Apartness.Definition
open import MLTT.Spartan
open import MLTT.Two-Properties
open import Naturals.Properties
open import NotionsOfDecidability.DecidableClassifier
open import Taboos.LPO
open import Taboos.WLPO
open import TypeTopology.Cantor renaming (_♯_ to _♯[Cantor]_) hiding (_＝⟦_⟧_)
open import TypeTopology.TotallySeparated
open import UF.Base
open import UF.ClassicalLogic
open import UF.DiscreteAndSeparated renaming (_♯_ to ♯[Π])
open import UF.FunExt
open import UF.Size
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

open Apartness pt
open PropositionalTruncation pt
open total-separatedness-via-apartness pt

\end{code}

We define an apartness relation to be nontrivial if it tells two points apart.

\begin{code}

has-two-points-apart : {X : 𝓤 ̇ } → Apartness X 𝓥 → 𝓥 ⊔ 𝓤 ̇
has-two-points-apart {𝓤} {𝓥} {X} (_♯_ , α) = Σ (x , y) ꞉ X × X , (x ♯ y)

Nontrivial-Apartness : 𝓤 ̇ → (𝓥 : Universe) → 𝓥 ⁺ ⊔ 𝓤 ̇
Nontrivial-Apartness X 𝓥 = Σ a ꞉ Apartness X 𝓥 , has-two-points-apart a

\end{code}

Assuming weak excluded middle, every type with two distinct points can be
equipped with a nontrivial apartness relation.

\begin{code}

WEM-gives-that-type-with-two-distinct-points-has-nontrivial-apartness
 : funext 𝓤 𝓤₀
 → {X : 𝓤 ̇ }
 → has-two-distinct-points X
 → typal-WEM 𝓤
 → Nontrivial-Apartness X 𝓤
WEM-gives-that-type-with-two-distinct-points-has-nontrivial-apartness
 {𝓤} fe {X} htdp wem = γ
 where
  s : (x y z : X) → x ≠ y → (x ≠ z) + (y ≠ z)
  s x y z d =
   Cases (wem (x ≠ z))
    (λ (a : ¬ (x ≠ z))  → inr (λ {refl → a d}))
    (λ (b : ¬¬ (x ≠ z)) → inl (three-negations-imply-one b))

  c : is-cotransitive _≠_
  c x y z d = ∣ s x y z d ∣

  γ : Nontrivial-Apartness X 𝓤
  γ = (_≠_ ,
      ((λ x y → negations-are-props fe) ,
       ≠-is-irrefl ,
       (λ x y → ≠-sym) , c)) ,
      htdp

WEM-gives-that-type-with-two-distinct-points-has-nontrivial-apartness⁺
 : funext 𝓤 𝓤₀
 → {X : 𝓤 ⁺ ̇ }
 → is-locally-small X
 → has-two-distinct-points X
 → typal-WEM 𝓤
 → Nontrivial-Apartness X 𝓤
WEM-gives-that-type-with-two-distinct-points-has-nontrivial-apartness⁺
 {𝓤} fe {X} ls ((x₀ , x₁) , d) wem = γ
 where
  _♯_ : X → X → 𝓤 ̇
  x ♯ y = x ≠⟦ ls ⟧ y

  s : (x y z : X) → x ♯ y → (x ♯ z) + (y ♯ z)
  s x y z a = Cases (wem (x ♯ z)) (inr ∘ f) (inl ∘ g)
   where
    f : ¬ (x ♯ z) → y ♯ z
    f = contrapositive
         (λ (e : y ＝⟦ ls ⟧ z) → transport (x ♯_) (＝⟦ ls ⟧-gives-＝ e) a)

    g : ¬¬ (x ♯ z) → x ♯ z
    g = three-negations-imply-one

  c : is-cotransitive _♯_
  c x y z d = ∣ s x y z d ∣

  γ : Nontrivial-Apartness X 𝓤
  γ = (_♯_ ,
       (λ x y → negations-are-props fe) ,
       (λ x → ≠⟦ ls ⟧-irrefl) ,
       (λ x y → ≠⟦ ls ⟧-sym) ,
       c) ,
      (x₀ , x₁) , ≠-gives-≠⟦ ls ⟧ d

\end{code}

In particular, weak excluded middle yields a nontrivial apartness relation on
any universe.

\begin{code}

WEM-gives-non-trivial-apartness-on-universe
 : funext (𝓤 ⁺) 𝓤₀
 → typal-WEM (𝓤 ⁺)
 → Nontrivial-Apartness (𝓤 ̇ ) (𝓤 ⁺)
WEM-gives-non-trivial-apartness-on-universe fe =
 WEM-gives-that-type-with-two-distinct-points-has-nontrivial-apartness
  fe
  universe-has-two-distinct-points

\end{code}

Further properties of apartness relations can be found in the following file
InjectiveTypes.CounterExamples. In particular, it is shown that the universe
can't have any nontrivial apartness unless weak excluded middle holds.

Added 31 January 2025 by Tom de Jong and Martin Escardo.

\begin{code}

EM-gives-tight-apartness-is-≠ : DNE 𝓥
                              → (X : 𝓤 ̇  )
                              → ((_♯_ , _ , _) : Tight-Apartness X 𝓥)
                              → ((x y : X) → x ♯ y ↔ x ≠ y)
EM-gives-tight-apartness-is-≠ dne X (_♯_ , ♯-is-apartness , ♯-is-tight) x y = III
 where
  I : x ♯ y → x ≠ y
  I = not-equal-if-apart _♯_ ♯-is-apartness
  II : x ≠ y → x ♯ y
  II ν = dne (x ♯ y)
             (apartness-is-prop-valued _♯_ ♯-is-apartness x y)
             (contrapositive (♯-is-tight x y) ν)
  III : x ♯ y ↔ x ≠ y
  III = I , II

\end{code}

Added 1 February 2025 by Tom de Jong.

The above shows that classically any type can have at most one tight apartness
(the one given by negation of equality). We show that the Cantor type (ℕ → 𝟚)
cannot be shown to have at most one tight apartness relation in constructive
mathematics: the statement that the Cantor type has at most one tight apartness
relation implies (WLPO ⇒ LPO) which is a constructive taboo as there are
(topological) models of intuitionistic set theory that validate WLPO but not
LPO, see the fifth page and Theorem 5.1 of the paper below.

Matt Hendtlass and Robert Lubarsky. 'Separating Fragments of WLEM, LPO, and MP'
The Journal of Symbolic Logic. Vol. 81, No. 4, 2016, pp. 1315-1343.
DOI: 10.1017/jsl.2016.38
URL: https://www.math.fau.edu/people/faculty/lubarsky/separating-llpo.pdf

\begin{code}

At-Most-One-Tight-Apartness : (X : 𝓤 ̇  ) (𝓥 : Universe) → (𝓥 ⁺ ⊔ 𝓤) ̇
At-Most-One-Tight-Apartness X 𝓥 = is-prop (Tight-Apartness X 𝓥)

At-Most-One-Tight-Apartness-on-Cantor-gives-WLPO-implies-LPO
 : Fun-Ext
 → At-Most-One-Tight-Apartness Cantor 𝓤₀
 → WLPO-variation₂ → LPO-variation
At-Most-One-Tight-Apartness-on-Cantor-gives-WLPO-implies-LPO  fe hyp wlpo = VI
 where
  _♯_ = _♯[Cantor]_

  has-root : Cantor → 𝓤₀ ̇
  has-root α = Σ n ꞉ ℕ , α n ＝ ₀

  P⁺ : (α : Cantor) → Σ b ꞉ 𝟚 , (b ＝ ₀ ↔ ¬¬ (has-root α))
                              × (b ＝ ₁ ↔ ¬ (has-root α))
  P⁺ α = boolean-value' (wlpo α)

  P : Cantor → 𝟚
  P α = pr₁ (P⁺ α)
  P-specification₀ : (α : Cantor) → P α ＝ ₀ ↔ ¬¬ (has-root α)
  P-specification₀ α = pr₁ (pr₂ (P⁺ α))
  P-specification₁ : (α : Cantor) → P α ＝ ₁ ↔ ¬ (has-root α)
  P-specification₁ α = pr₂ (pr₂ (P⁺ α))

  P-of-𝟏-is-₁ : P 𝟏 ＝ ₁
  P-of-𝟏-is-₁ = rl-implication (P-specification₁ 𝟏) I
   where
    I : ¬ has-root (λ n → ₁)
    I (n , p) = one-is-not-zero p

  P-differentiates-at-𝟏-specification : (α : Cantor)
                                      → P α ≠ P 𝟏 ↔ ¬¬ (has-root α)
  P-differentiates-at-𝟏-specification α = I , II
   where
    I : P α ≠ P 𝟏 → ¬¬ has-root α
    I ν = lr-implication (P-specification₀ α) I₂
     where
      I₁ : P α ＝ ₁ → P α ＝ ₀
      I₁ e = 𝟘-elim (ν (e ∙ P-of-𝟏-is-₁ ⁻¹))
      I₂ : P α ＝ ₀
      I₂ = 𝟚-equality-cases id I₁
    II : ¬¬ has-root α → P α ≠ P 𝟏
    II ν e = ν (lr-implication (P-specification₁ α) (e ∙ P-of-𝟏-is-₁))

  I : (α : Cantor) → ¬¬ (has-root α) → α ♯₂ 𝟏
  I α ν = ∣ P , rl-implication (P-differentiates-at-𝟏-specification α) ν ∣

  II : (α : Cantor) → α ♯ 𝟏 ↔ has-root α
  II α = II₁ , II₂
   where
    II₁ : α ♯ 𝟏 → has-root α
    II₁ a = pr₁ has-root' , 𝟚-equality-cases id (λ p → 𝟘-elim (pr₂ has-root' p))
     where
      has-root' : Σ n ꞉ ℕ , α n ≠ ₁
      has-root' = apartness-criterion-converse α 𝟏 a
    II₂ : has-root α → α ♯ 𝟏
    II₂ (n , p) = apartness-criterion α 𝟏
                   (n , λ (q : α n ＝ ₁) → zero-is-not-one (p ⁻¹ ∙ q))

  III : (α : Cantor) → α ♯₂ 𝟏 → α ♯ 𝟏
  III α = Idtofun (eq α 𝟏)
   where
    eq : (α β : Cantor) → α ♯₂ β ＝ α ♯ β
    eq α β =
     happly
      (happly
       (ap pr₁
           (hyp (_♯₂_ ,
                 ♯₂-is-apartness ,
                 ♯₂-is-tight (Cantor-is-totally-separated fe))
                (_♯_ ,
                 ♯-is-apartness fe pt ,
                 ♯-is-tight fe)))
       α)
      β

  IV : (α : Cantor) → ¬¬-stable (has-root α)
  IV α ν = lr-implication (II α) (III α (I α ν))

  recall : (α : Cantor) → type-of (wlpo α) ＝ is-decidable (¬ (has-root α))
  recall α = refl

  V : (α : Cantor) → is-decidable (has-root α)
  V α = κ (wlpo α)
   where
    κ : is-decidable (¬ (has-root α)) → is-decidable (has-root α)
    κ (inl p) = inr p
    κ (inr q) = inl (IV α q)

  VI : LPO-variation
  VI = V

\end{code}

Added 5 February 2025 by Tom de Jong.

A simpler theorem with a much stronger conclusion is possible, following a
generalization of an idea of Andrew Swan.

We record some basic general results first.

\begin{code}

≠-is-apartness-on-discrete-type : funext 𝓤 𝓤₀
                                → {X : 𝓤 ̇  }
                                → is-discrete X
                                → is-apartness _≠_
≠-is-apartness-on-discrete-type fe {X} X-discrete =
   (λ x y → negations-are-props fe)
 , ≠-is-irrefl
 , (λ x y → ≠-sym)
 , (λ x y z a → I x y z a (X-discrete x z))
  where
   I : (x y z : X) → x ≠ y
     → (x ＝ z) + ¬ (x ＝ z)
     → (x ≠ z) ∨ (y ≠ z)
   I x y z a (inl refl) = ∣ inr (≠-sym a) ∣
   I x y z a (inr ν)    = ∣ inl ν ∣

≠-is-tight-on-discrete-type : {X : 𝓤 ̇  }
                            → is-discrete X
                            → is-tight _≠_
≠-is-tight-on-discrete-type = discrete-is-¬¬-separated

At-Most-One-Tight-Apartness-on-discrete-type-with-two-distinct-points-gives-DNE
 : funext 𝓤 𝓤₀
 → (X : 𝓤 ̇  )
 → has-two-distinct-points X
 → is-discrete X
 → At-Most-One-Tight-Apartness X 𝓤
 → DNE 𝓤
At-Most-One-Tight-Apartness-on-discrete-type-with-two-distinct-points-gives-DNE
 {𝓤} fe X ((x₀ , x₁) , x₀-is-not-x₁) X-discrete hyp P P-is-prop = II
  where
   _♯_ : X → X → 𝓤 ̇
   x ♯ y = P × (x ≠ y)

   pv : is-prop-valued _♯_
   pv x y = ×-is-prop P-is-prop (negations-are-props fe)
   ir : is-irreflexive _♯_
   ir x (p , ν) = ≠-is-irrefl x ν
   sy : is-symmetric _♯_
   sy x y (p , ν) = (p , ≠-sym ν)

   ct : is-cotransitive _♯_
   ct x y z (p , ν) = κ (X-discrete x z)
    where
     κ : (x ＝ z) + (x ≠ z) → (x ♯ z) ∨ (y ♯ z)
     κ (inl refl) = ∣ inr (p , ≠-sym ν) ∣
     κ (inr   ν') = ∣ inl (p , ν') ∣

   tg : ¬¬ P → is-tight _♯_
   tg dnp x y na = discrete-is-¬¬-separated X-discrete x y I
    where
     I : ¬ (x ≠ y)
     I ν = dnp (λ (p : P) → na (p , ν))

   I : ¬¬ P → x₀ ♯ x₁
   I dnp = Idtofun ((eq x₀ x₁) ⁻¹) x₀-is-not-x₁
    where
     eq : (x y : X) → (x ♯ y) ＝ (x ≠ y)
     eq x y =
       happly
       (happly
         (ap pr₁
             (hyp (_♯_ , (pv , ir , sy , ct) ,  tg dnp)
                  (_≠_ , ≠-is-apartness-on-discrete-type fe X-discrete ,
                         ≠-is-tight-on-discrete-type X-discrete)))
         x)
       y

   II : ¬¬ P → P
   II dnp = pr₁ (I dnp)

At-Most-One-Tight-Apartness-on-ℕ-gives-DNE
 : funext 𝓤₀ 𝓤₀
 → At-Most-One-Tight-Apartness ℕ 𝓤₀
 → DNE 𝓤₀
At-Most-One-Tight-Apartness-on-ℕ-gives-DNE fe =
 At-Most-One-Tight-Apartness-on-discrete-type-with-two-distinct-points-gives-DNE
   fe ℕ ((0 , 1) , zero-not-positive 0) ℕ-is-discrete

\end{code}

Added 5th February 2025 by Martin Escardo. We improve the above result
by Tom de Jong and Andrew Swan. If a type has exactly one tight
apartness with two points apart, then double negation elimination, and
hence excluded middle, hold.

\begin{code}

Exactly-One-Tight-Apartness-on-type-with-two-points-apart-gives-DNE
 : {X : 𝓤 ̇}
   ((_♯_ , a , _) : Tight-Apartness X 𝓤)
 → has-two-points-apart (_♯_ , a)
 → At-Most-One-Tight-Apartness X 𝓤
 → DNE 𝓤
Exactly-One-Tight-Apartness-on-type-with-two-points-apart-gives-DNE
 {𝓤} {X}
 (_♯_ , a@(♯-pv , ♯-irrefl , ♯-sym , ♯-cot) , ♯-tight)
 ((x₀ , x₁) , x₀-apart-from-x₁)
 α P P-is-prop = VI
  where
   _♯ᴾ_ : X → X → 𝓤 ̇
   x ♯ᴾ y = P × (x ♯ y)

   ♯ᴾ-pv : is-prop-valued _♯ᴾ_
   ♯ᴾ-pv x y = ×-is-prop P-is-prop (♯-pv x y)

   ♯ᴾ-irrefl : is-irreflexive _♯ᴾ_
   ♯ᴾ-irrefl x (p , ν) = ♯-irrefl x ν

   ♯ᴾ-sym : symmetric _♯ᴾ_
   ♯ᴾ-sym x y (p , ν) = (p , ♯-sym x y ν)

   ♯ᴾ-cot : is-cotransitive _♯ᴾ_
   ♯ᴾ-cot x y z (p , ν) = ∥∥-functor f (♯-cot x y z ν)
    where
     f : (x ♯ z) + (y ♯ z) → (x ♯ᴾ z) + (y ♯ᴾ z)
     f (inl l) = inl (p , l)
     f (inr r) = inr (p , r)

   ♯ᴾ-tight : ¬¬ P → is-tight _♯ᴾ_
   ♯ᴾ-tight dnp x y na = ♯-tight x y I
    where
     I : ¬ (x ♯ y)
     I ν = dnp (λ (p : P) → na (p , ν))

   aᴾ : is-apartness _♯ᴾ_
   aᴾ = (♯ᴾ-pv , ♯ᴾ-irrefl , ♯ᴾ-sym , ♯ᴾ-cot)

   II : ¬¬ P → x₀ ♯ᴾ x₁
   II dnp = Idtofun (V ⁻¹) x₀-apart-from-x₁
    where
     III : _♯ᴾ_  ＝ _♯_
     III = ap pr₁ (α (_♯ᴾ_ , aᴾ , ♯ᴾ-tight dnp)
                     (_♯_  , a  , ♯-tight))

     IV : {x : X} → x ♯ᴾ_ ＝ x ♯_
     IV {x} =  happly III x

     V : {x y : X} → x ♯ᴾ y ＝ x ♯ y
     V {x} {y} = happly IV y

   VI : ¬¬ P → P
   VI = pr₁ ∘ II

\end{code}

The previous result is a particular case, of course:

\begin{code}

At-Most-One-Tight-Apartness-on-discrete-type-with-two-distinct-points-gives-DNE'
 : funext 𝓤 𝓤₀
 → {X : 𝓤 ̇}
 → is-discrete X
 → has-two-distinct-points X
 → At-Most-One-Tight-Apartness X 𝓤
 → DNE 𝓤
At-Most-One-Tight-Apartness-on-discrete-type-with-two-distinct-points-gives-DNE'
 fe δ
 = Exactly-One-Tight-Apartness-on-type-with-two-points-apart-gives-DNE
    (_≠_ , ≠-is-apartness-on-discrete-type fe δ , ≠-is-tight-on-discrete-type δ)

\end{code}
