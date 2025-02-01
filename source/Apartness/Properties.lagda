Martin Escardo and Tom de Jong, August 2024

Moved from the file InjectiveTypes.CounterExamples on 12 September 2024.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.PropTrunc

module Apartness.Properties
        (pt : propositional-truncations-exist)
       where

open import MLTT.Spartan
open import Apartness.Definition
open import UF.Base
open import UF.ClassicalLogic
open import UF.FunExt
open import UF.Size
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

open Apartness pt
open PropositionalTruncation pt

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

TODO: COMMENT AND POINTER TO TypeTopology.SimpleTypes.

\begin{code}

open import Taboos.WLPO
open import Taboos.LPO
open import NotionsOfDecidability.Decidable
open import NotionsOfDecidability.DecidableClassifier
open import MLTT.Two-Properties

open import TypeTopology.TotallySeparated
open import TypeTopology.Cantor

At-Most-One-Tight-Apartness : (X : 𝓤 ̇  ) (𝓥 : Universe) → (𝓥 ⁺ ⊔ 𝓤) ̇
At-Most-One-Tight-Apartness X 𝓥 = is-prop (Tight-Apartness X 𝓥)

foo : Fun-Ext
    → At-Most-One-Tight-Apartness (ℕ → 𝟚) 𝓤₀
    → WLPO-variation₂ → LPO-variation
foo fe hyp wlpo = VI
 where
  open total-separatedness-via-apartness pt

  X : 𝓤₀ ̇
  X = ℕ → 𝟚

  has-root : X → 𝓤₀ ̇
  has-root α = Σ n ꞉ ℕ , α n ＝ ₀

  P⁺ : (α : X) → Σ b ꞉ 𝟚 , (b ＝ ₀ ↔ ¬¬ (has-root α))
                         × (b ＝ ₁ ↔ ¬ (has-root α))
  P⁺ α = boolean-value' (wlpo α)

  P : X → 𝟚
  P α = pr₁ (P⁺ α)

  P-specification₀ : (α : X) → P α ＝ ₀ ↔ ¬¬ (has-root α)
  P-specification₀ α = pr₁ (pr₂ (P⁺ α))

  P-specification₁ : (α : X) → P α ＝ ₁ ↔ ¬ (has-root α)
  P-specification₁ α = pr₂ (pr₂ (P⁺ α))

  g : X
  g n = ₁

  P-of-g-is-₁ : P g ＝ ₁
  P-of-g-is-₁ = rl-implication (P-specification₁ g) I
   where
    I : ¬ has-root (λ n → ₁)
    I (n , p) = one-is-not-zero p

  P-differentiates-at-g-specification : (f : X) → P f ≠ P g ↔ ¬¬ (has-root f)
  P-differentiates-at-g-specification f = I , II
   where
    I : P f ≠ P g → ¬¬ has-root f
    I ν = lr-implication (P-specification₀ f) I₂
     where
      I₁ : P f ＝ ₁ → P f ＝ ₀
      I₁ e = 𝟘-elim (ν
                      (P f ＝⟨ e ⟩
                       ₁   ＝⟨ P-of-g-is-₁ ⁻¹ ⟩
                       P g ∎))
      I₂ : P f ＝ ₀
      I₂ = 𝟚-equality-cases id I₁
    II : ¬¬ has-root f → P f ≠ P g
    II ν e = ν (lr-implication (P-specification₁ f) (e ∙ P-of-g-is-₁))

  I : (f : X) → ¬¬ (has-root f) → f ♯₂ g
  I f ν = ∣ P , rl-implication (P-differentiates-at-g-specification f) ν ∣

  II : (f : X) → f ♯ g ↔ has-root f
  II f = II₁ , II₂
   where
    II₁ : f ♯ g → has-root f
    II₁ a = pr₁ has-root' , 𝟚-equality-cases id (λ p → 𝟘-elim (pr₂ has-root' p))
     where
      has-root' : Σ n ꞉ ℕ , f n ≠ ₁
      has-root' = apartness-criterion-converse f g a
    II₂ : has-root f → f ♯ g
    II₂ (n , p) = apartness-criterion f g
                   (n , (λ (q : f n ＝ ₁) → zero-is-not-one (p ⁻¹ ∙ q)))

  III : (f : X) → f ♯₂ g → f ♯ g
  III f = Idtofun (eq f g)
   where
    eq : (f₁ f₂ : X) → f₁ ♯₂ f₂ ＝ f₁ ♯ f₂
    eq f₁ f₂ =
     happly
      (happly
       (ap pr₁
           (hyp (_♯₂_ ,
                 ♯₂-is-apartness ,
                 ♯₂-is-tight (Cantor-is-totally-separated fe))
                (_♯_ ,
                 ♯-is-apartness fe pt ,
                 ♯-is-tight fe)))
       f₁)
      f₂

  IV : (f : X) → ¬¬-stable (has-root f)
  IV f ν = lr-implication (II f) (III f (I f ν))

  recall₁ : (f : X) → type-of (wlpo f) ＝ is-decidable (¬ (has-root f))
  recall₁ f = refl

  V : (f : X) → is-decidable (has-root f)
  V f = κ (wlpo f)
   where
    κ : is-decidable (¬ (has-root f)) → is-decidable (has-root f)
    κ (inl p) = inr p
    κ (inr q) = inl (IV f q)

  VI : LPO-variation
  VI = V

\end{code}