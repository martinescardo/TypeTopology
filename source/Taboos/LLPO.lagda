Martin Escardo, 15th November 2023.

Lesser Limited Principle of Omniscience.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Taboos.LLPO where

open import CoNaturals.BothTypes
open import CoNaturals.Equivalence
open import CoNaturals.Type2Properties
open import MLTT.Plus-Properties
open import MLTT.Spartan
open import MLTT.Two-Properties
open import Naturals.Parity
open import Naturals.Properties
open import Notation.CanonicalMap
open import Taboos.BasicDiscontinuity
open import Taboos.WLPO
open import UF.Equiv
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

open ℕ∞-equivalence

private
 T : (ℕ → 𝟚) → 𝓤₀ ̇
 T α = Σ n ꞉ ℕ , α n ＝ ₁

 ¬T : (ℕ → 𝟚) → 𝓤₀ ̇
 ¬T α = (n : ℕ) → α n ＝ ₀

private
 instance
  Canonical-Map-ℕ-ℕ∞' : Canonical-Map ℕ ℕ∞'
  ι {{Canonical-Map-ℕ-ℕ∞'}} = ℕ-to-ℕ∞'

 instance
  canonical-map-ℕ∞'-ℕ→𝟚 : Canonical-Map ℕ∞' (ℕ → 𝟚)
  ι {{canonical-map-ℕ∞'-ℕ→𝟚}} = ℕ∞'-to-ℕ→𝟚

\end{code}

The definition of LLPO uses _∨_ rather than _+_. We show that with
_+_, LLPO implies WLPO, but it is known that LLPO with _∨_ doesn't
(there are counter-models).

\begin{code}

untruncated-LLPO : 𝓤₀ ̇
untruncated-LLPO = (α : ℕ → 𝟚)
                 → is-prop (T α)
                 → ((n : ℕ) → α ( double n) ＝ ₀)
                 + ((n : ℕ) → α (sdouble n) ＝ ₀)

\end{code}

The following version is logically equivalent, which shows that
untruncated LLPO is an instance of De Morgan Law.

\begin{code}

untruncated-LLPO' : 𝓤₀ ̇
untruncated-LLPO' = (β γ : ℕ → 𝟚)
                  → is-prop (T β)
                  → is-prop (T γ)
                  → ¬ (T β × T γ) → ¬ T β + ¬ T γ

untrucated-LLPO'-gives-untruncated-LLPO : untruncated-LLPO' → untruncated-LLPO
untrucated-LLPO'-gives-untruncated-LLPO llpo' α h = III
 where
  β γ : ℕ → 𝟚
  β n = α ( double n)
  γ n = α (sdouble n)

  i : is-prop (T β)
  i (n , e) (n' , e') = to-T-＝ (double-lc (index-uniqueness α h e e'))

  j : is-prop (T γ)
  j (n , e) (n' , e') = to-T-＝ (sdouble-lc (index-uniqueness α h e e'))

  I : ¬ (T β × T γ)
  I ((k , e) , (k' , e')) = even-not-odd' k k' (index-uniqueness α h e e')

  II : ¬ T β + ¬ T γ
  II = llpo' β γ i j I

  III : ((n : ℕ) → α (double n) ＝ ₀) + ((n : ℕ) → α (sdouble n) ＝ ₀)
  III = +functor not-T-gives-¬T not-T-gives-¬T II

untrucated-LLPO-gives-untruncated-LLPO' : untruncated-LLPO → untruncated-LLPO'
untrucated-LLPO-gives-untruncated-LLPO' llpo β γ i j ν = III
 where
  f : (n : ℕ) → is-even' n + is-odd' n → 𝟚
  f n (inl (k , _)) = β k
  f n (inr (k , _)) = γ k

  α : ℕ → 𝟚
  α n = f n (even-or-odd' n)

  α-β : (n : ℕ) → α (double n) ＝ β n
  α-β n = a (even-or-odd' (double n))
   where
    a : (d : is-even' (double n) + is-odd' (double n)) → f (double n) d ＝ β n
    a (inl (k , e)) = ap β (double-lc e)
    a (inr (k , e)) = 𝟘-elim (even-not-odd' n k (e ⁻¹))

  α-γ : (n : ℕ) → α (sdouble n) ＝ γ n
  α-γ n = a (even-or-odd' (sdouble n))
   where
    a : (d : is-even' (sdouble n) + is-odd' (sdouble n)) → f (sdouble n) d ＝ γ n
    a (inl (k , e)) = 𝟘-elim (even-not-odd' k n e)
    a (inr (k , e)) = ap γ (sdouble-lc e)

  I : is-prop (T α)
  I (n , e) (n' , e') = a (even-or-odd' n) (even-or-odd' n')
   where
    a : (d  : is-even' n  + is-odd' n )
        (d' : is-even' n' + is-odd' n')
      → (n , e) ＝[ T α ] (n' , e')
    a (inl (k , refl)) (inl (k' , refl)) =
     to-T-＝ (ap  double (index-uniqueness β i ((α-β k)⁻¹ ∙ e) ((α-β k') ⁻¹ ∙ e')))
    a (inl (k , refl)) (inr (k' , refl)) =
     𝟘-elim (ν ((k  , ((α-β k )⁻¹ ∙ e )) , (k' , (( α-γ k')⁻¹ ∙ e'))))
    a (inr (k , refl)) (inl (k' , refl)) =
     𝟘-elim (ν ((k' , ((α-β k')⁻¹ ∙ e')) , (k  , (( α-γ k )⁻¹ ∙ e ))))
    a (inr (k , refl)) (inr (k' , refl)) =
     to-T-＝ (ap sdouble (index-uniqueness γ j ((α-γ k)⁻¹ ∙ e) ((α-γ k') ⁻¹ ∙ e')))

  II : ((n : ℕ) → α (double n) ＝ ₀) + ((n : ℕ) → α (sdouble n) ＝ ₀)
  II = llpo α I

  III : ¬ T β + ¬ T γ
  III = +functor
         (λ (ψ : (n : ℕ) → α ( double n) ＝ ₀)
               → ¬T-gives-not-T (λ n → (α-β n)⁻¹ ∙ ψ n))
         (λ (ψ : (n : ℕ) → α (sdouble n) ＝ ₀)
               → ¬T-gives-not-T (λ n → (α-γ n)⁻¹ ∙ ψ n))
         II

\end{code}

Two more equivalent formulations of LLPO.

\begin{code}

untruncated-ℕ∞-LLPO : 𝓤₀ ̇
untruncated-ℕ∞-LLPO = (u v : ℕ∞)
                    → ¬ (is-finite u × is-finite v)
                    → (u ＝ ∞) + (v ＝ ∞)

untruncated-ℕ∞'-LLPO : 𝓤₀ ̇
untruncated-ℕ∞'-LLPO = (u v : ℕ∞')
                     → ¬ (is-finite' u × is-finite' v)
                     → (u ＝ ∞') + (v ＝ ∞')

untruncated-LLPO'-gives-untruncated-ℕ∞'-LLPO : funext₀
                                             → untruncated-LLPO'
                                             → untruncated-ℕ∞'-LLPO
untruncated-LLPO'-gives-untruncated-ℕ∞'-LLPO fe llpo u v μ = II I
 where
  I : ¬ T (ι u) + ¬ T (ι v)
  I = llpo (ι u) (ι v) (ℕ∞'-to-ℕ→𝟚-at-most-one-₁ u) (ℕ∞'-to-ℕ→𝟚-at-most-one-₁ v) μ

  II : type-of I → (u ＝ ∞') + (v ＝ ∞')
  II (inl a) = inl (not-T-is-∞' fe u a)
  II (inr b) = inr (not-T-is-∞' fe v b)

untruncated-ℕ∞'-LLPO-gives-untruncated-LLPO' : funext₀
                                             → untruncated-ℕ∞'-LLPO
                                             → untruncated-LLPO'
untruncated-ℕ∞'-LLPO-gives-untruncated-LLPO' fe llpo α β a b μ = II I
 where
  I : ((α , a) ＝ ∞') + ((β , b) ＝ ∞')
  I = llpo (α , a) (β , b) (λ (ϕ , γ) → μ (ϕ , γ))

  II : type-of I → ¬ T α + ¬ T β
  II (inl e) = inl (¬T-gives-not-T (λ n → ap (λ - → pr₁ - n) e))
  II (inr e) = inr (¬T-gives-not-T (λ n → ap (λ - → pr₁ - n) e))

untruncated-ℕ∞-LLPO-gives-untruncated-ℕ∞'-LLPO : funext₀
                                               → untruncated-ℕ∞-LLPO
                                               → untruncated-ℕ∞'-LLPO
untruncated-ℕ∞-LLPO-gives-untruncated-ℕ∞'-LLPO fe llpo u v μ = II I
 where
  I : (ℕ∞'-to-ℕ∞ fe u ＝ ∞) + (ℕ∞'-to-ℕ∞ fe v ＝ ∞)
  I = llpo
        (ℕ∞'-to-ℕ∞ fe u)
        (ℕ∞'-to-ℕ∞ fe v)
        (λ (a , b) → μ (finite-gives-finite' fe u a ,
                        finite-gives-finite' fe v b))

  II : type-of I → (u ＝ ∞') + (v ＝ ∞')
  II (inl d) = inl (∞-gives-∞' fe u d)
  II (inr e) = inr (∞-gives-∞' fe v e)

untruncated-ℕ∞'-LLPO-gives-untruncated-ℕ∞-LLPO : funext₀
                                               → untruncated-ℕ∞'-LLPO
                                               → untruncated-ℕ∞-LLPO
untruncated-ℕ∞'-LLPO-gives-untruncated-ℕ∞-LLPO fe llpo u v μ = II I
 where
  I : (ℕ∞-to-ℕ∞' fe u ＝ ∞') + (ℕ∞-to-ℕ∞' fe v ＝ ∞')
  I = llpo
        (ℕ∞-to-ℕ∞' fe u)
        (ℕ∞-to-ℕ∞' fe v)
        (λ (a , b) → μ (finite'-gives-finite fe u a ,
                        finite'-gives-finite fe v b))

  II : type-of I → (u ＝ ∞) + (v ＝ ∞)
  II (inl d) = inl (∞'-gives-∞ fe u d)
  II (inr e) = inr (∞'-gives-∞ fe v e)

untruncated-ℕ∞-LLPO-gives-untruncated-LPO : funext₀
                                          → untruncated-ℕ∞-LLPO
                                          → untruncated-LLPO
untruncated-ℕ∞-LLPO-gives-untruncated-LPO fe unllpo =
 untrucated-LLPO'-gives-untruncated-LLPO
  (untruncated-ℕ∞'-LLPO-gives-untruncated-LLPO' fe
    (untruncated-ℕ∞-LLPO-gives-untruncated-ℕ∞'-LLPO fe unllpo))

untruncated-LLPO-gives-untruncated-ℕ∞-LPO : funext₀
                                          → untruncated-LLPO
                                          → untruncated-ℕ∞-LLPO
untruncated-LLPO-gives-untruncated-ℕ∞-LPO fe ullpo =
 untruncated-ℕ∞'-LLPO-gives-untruncated-ℕ∞-LLPO fe
  (untruncated-LLPO'-gives-untruncated-ℕ∞'-LLPO fe
   (untrucated-LLPO-gives-untruncated-LLPO' ullpo))

\end{code}

The following result seems to be new (and I announced it years ago in
the constructivenews mailing list). The idea is to construct a
non-continuous function using untruncated LLPO, and then derive WLPO
from this. This proof was written here 15th November 2023, simplified
28th February 2023, for which we included the above ℕ∞-versions of
LLPO and their equivalences.

\begin{code}

untruncated-ℕ∞-LLPO-gives-WLPO : funext₀ → untruncated-ℕ∞-LLPO → WLPO
untruncated-ℕ∞-LLPO-gives-WLPO fe llpo = wlpo
 where
  D : ℕ∞ → ℕ∞ → 𝓤₀ ̇
  D u v = (u ＝ ∞) + (v ＝ ∞)

  ϕ : (u v : ℕ∞) → D u v → 𝟚
  ϕ u v (inl _) = ₀
  ϕ u v (inr _) = ₁

  l₀ : (u : ℕ∞) → D u ∞
  l₀ u = llpo u ∞ (λ (_ , ∞-is-finite) → is-infinite-∞ ∞-is-finite)

  l₁ : (u : ℕ∞) → D ∞ u
  l₁ u = llpo ∞ u (λ (∞-is-finite , _) → is-infinite-∞ ∞-is-finite)

  l-∞-agreement : l₀ ∞ ＝ l₁ ∞
  l-∞-agreement = refl

  f₀ f₁ : ℕ∞ → 𝟚
  f₀ u = ϕ u ∞ (l₀ u)
  f₁ u = ϕ ∞ u (l₁ u)

  f-∞-agreement : f₀ ∞ ＝ f₁ ∞
  f-∞-agreement = refl

  ϕ₀-property : (u : ℕ∞) (d : D u ∞) → is-finite u → ϕ u ∞ d ＝ ₁
  ϕ₀-property .∞ (inl refl) ∞-is-finite = 𝟘-elim (is-infinite-∞ ∞-is-finite)
  ϕ₀-property u  (inr _)    _           = refl

  ϕ₁-property : (u : ℕ∞) (d : D ∞ u) → is-finite u → ϕ ∞ u d ＝ ₀
  ϕ₁-property u  (inl _)    _           = refl
  ϕ₁-property .∞ (inr refl) ∞-is-finite = 𝟘-elim (is-infinite-∞ ∞-is-finite)

  f₀-property : (u : ℕ∞) → is-finite u → f₀ u ＝ ₁
  f₀-property u = ϕ₀-property u (l₀ u)

  f₁-property : (u : ℕ∞) → is-finite u → f₁ u ＝ ₀
  f₁-property u = ϕ₁-property u (l₁ u)

  wlpo₀ : f₀ ∞ ＝ ₀ → WLPO
  wlpo₀ e = wlpo
   where
    g₀ : ℕ∞ → 𝟚
    g₀ = complement ∘ f₀

    b₀ : (n : ℕ) → g₀ (ι n) ＝ ₀
    b₀ n = ap complement (f₀-property (ι n) (ℕ-to-ℕ∞-is-finite n))

    b₁ : g₀ ∞ ＝ ₁
    b₁ = ap complement e

    wlpo : WLPO
    wlpo = basic-discontinuity-taboo fe g₀ (b₀ , b₁)

  wlpo₁ : f₁ ∞ ＝ ₁ → WLPO
  wlpo₁ b₁ = wlpo
   where
    b₀ : (n : ℕ) → f₁ (ι n) ＝ ₀
    b₀ n = f₁-property (ι n) (ℕ-to-ℕ∞-is-finite n)

    wlpo : WLPO
    wlpo = basic-discontinuity-taboo fe f₁ (b₀ , b₁)

  wlpo : WLPO
  wlpo = Cases (𝟚-possibilities (f₀ ∞))
          (λ (a : f₀ ∞ ＝ ₀)
                → wlpo₀ a)
          (λ (b : f₀ ∞ ＝ ₁)
                → Cases (𝟚-possibilities (f₁ ∞))
                   (λ (c : f₁ ∞ ＝ ₀)
                         → 𝟘-elim (zero-is-not-one
                                    (₀    ＝⟨ c ⁻¹ ⟩
                                     f₁ ∞ ＝⟨ f-∞-agreement ⟩
                                     f₀ ∞ ＝⟨ b ⟩
                                     ₁    ∎)))
                   (λ (d : f₁ ∞ ＝ ₁)
                         → wlpo₁ d))

\end{code}

Added 27th Feb 2024. The converse also holds with a simpler proof, and
so there isn't any difference between WLPO and untruncated LLPO.

\begin{code}

WLPO-gives-untruncated-LLPO : WLPO-traditional → untruncated-LLPO
WLPO-gives-untruncated-LLPO wlpo α Tα-is-prop =
 Cases (wlpo (complement ∘ α ∘ double))
  (λ (a : (n : ℕ) → complement (α (double n)) ＝ ₁)
        → inl (λ n → complement₁ (a n)))
  (λ (b : ¬ ((n : ℕ) → complement (α (double n)) ＝ ₁))
        → inr (λ n → 𝟚-equality-cases
                      (λ (c : α (sdouble n) ＝ ₀)
                            → c)
                      (λ (d : α (sdouble n) ＝ ₁)
                            → 𝟘-elim
                               (b (λ m → ap
                                          complement
                                          (different-from-₁-equal-₀
                                            (λ (p : α (double m) ＝ ₁)
                                                  → double-is-not-sdouble
                                                     (index-uniqueness
                                                       α
                                                       Tα-is-prop
                                                       p
                                                       d))))))))
\end{code}

End of 27th Feb 2024 addition.

We now formulate (truncated) LLPO.

\begin{code}

module _ (pt : propositional-truncations-exist) where

 open PropositionalTruncation pt

 LLPO : 𝓤₀ ̇
 LLPO = (α : ℕ → 𝟚)
      → is-prop (Σ n ꞉ ℕ , α n ＝ ₁)
      → ((n : ℕ) → α (double n) ＝ ₀) ∨ ((n : ℕ) → α (sdouble n) ＝ ₀)

 LLPO' : 𝓤₀ ̇
 LLPO' = (β γ : ℕ → 𝟚)
       → is-prop (T β)
       → is-prop (T γ)
       → ¬ (T β × T γ) → ¬ T β ∨ ¬ T γ

 ℕ∞-LLPO : 𝓤₀ ̇
 ℕ∞-LLPO = (u v : ℕ∞) → ¬ (is-finite u × is-finite v) → (u ＝ ∞) ∨ (v ＝ ∞)

 ℕ∞-LLPO' : 𝓤₀ ̇
 ℕ∞-LLPO' = (u v : ℕ∞) → ¬ ((u ≠ ∞) × (v ≠ ∞)) → (u ＝ ∞) ∨ (v ＝ ∞)

 ℕ∞'-LLPO : 𝓤₀ ̇
 ℕ∞'-LLPO = (u v : ℕ∞') → ¬ (is-finite' u × is-finite' v) → (u ＝ ∞') ∨ (v ＝ ∞')

 untruncated-LLPO-gives-LLPO : untruncated-LLPO → LLPO
 untruncated-LLPO-gives-LLPO ullpo α i = ∣ ullpo α i ∣

\end{code}

TODO. Show that all these variants are equivalent.

LLPO doesn't imply WLPO (there are published refereces - find and
include them here). One example seems to Johnstone's topological
topos, but this is unpublished as far as I know.

Added 17th July 2024. There is a proof by Chris Grossack here:
https://grossack.site/2024/07/03/topological-topos-3-bonus-axioms
