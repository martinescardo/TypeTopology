Martin Escardo, 15th November 2023.

Lesser Limited Principle of Omniscience.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Taboos.LLPO where

open import CoNaturals.GenericConvergentSequence
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

private
 T : (ℕ → 𝟚) → 𝓤₀ ̇
 T α = Σ n ꞉ ℕ , α n ＝ ₁

private
 instance
  Canonical-Map-ℕ-ℕ∞' : Canonical-Map ℕ ℕ∞'
  ι {{Canonical-Map-ℕ-ℕ∞'}} = ℕ-to-ℕ∞'

\end{code}

The definition of LLPO uses _∨_ rather than _+_. We show that LLPO
defined with _+_ implies WLPO, although it is known that LLPO defined with
_∨_ doesn't (there are counter-models).

LLPO says that for every binary sequence with at most one , either
even terms or the odd terms are all 0. It is known that WLPO (it is
decidable whether a given binary sequence is constantly 0) implies
LLPO.

We can implement this disjunction with "+" or "∨", and we discuss
both here.

With "∨", it is known that LLPO doesn't imply WLPO (there are
counter-models).

The main result in this file is that LLPO defined with "+" implies
WLPO. This seems to be a new result.

\begin{code}

untruncated-LLPO : 𝓤₀ ̇
untruncated-LLPO = (α : ℕ → 𝟚)
                 → is-prop (T α)
                 → ((n : ℕ) → α ( double n) ＝ ₀)
                 + ((n : ℕ) → α (sdouble n) ＝ ₀)

\end{code}

The following version is equivalent, which shows that (untruncated)
LLPO is an instance of De Morgan Law.

\begin{code}

untruncated-LLPO' : 𝓤₀ ̇
untruncated-LLPO' = (β γ : ℕ → 𝟚)
                  → is-prop (T β)
                  → is-prop (T γ)
                  → ¬ (T β × T γ) → ¬ T β + ¬ T γ

¬T : (ℕ → 𝟚) → 𝓤₀ ̇
¬T α = (n : ℕ) → α n ＝ ₀

not-T-gives-¬T : {α : ℕ → 𝟚} → ¬ (T α) → ¬T α
not-T-gives-¬T {α} ϕ n = different-from-₁-equal-₀ (λ (e : α n ＝ ₁) → ϕ (n , e))

¬T-gives-not-T : {α : ℕ → 𝟚} → ¬T α → ¬ (T α)
¬T-gives-not-T {α} ψ (n , e) = zero-is-not-one ((ψ n)⁻¹ ∙ e)

unprime : untruncated-LLPO' → untruncated-LLPO
unprime llpo' α h = III
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

prime : untruncated-LLPO → untruncated-LLPO'
prime llpo β γ i j ν = III
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

The following result seems to be new (and I announced it years ago in
the constructivenews mailing list).

\begin{code}

untruncated-LLPO-gives-WLPO : funext₀ → untruncated-LLPO' → WLPO
untruncated-LLPO-gives-WLPO fe llpo = wlpo
 where
  ϕ : (u v : ℕ∞') → ¬ is-finite' u + ¬ is-finite' v → 𝟚
  ϕ u v (inl l) = ₀
  ϕ u v (inr r) = ₁

  l₀ : (u : ℕ∞') → ¬ is-finite' u + ¬ is-finite' ∞'
  l₀ u = llpo (ℕ∞'-to-ℕ→𝟚 u)      (ℕ∞'-to-ℕ→𝟚 ∞')
              (ℕ∞'-to-ℕ→𝟚-prop u) (ℕ∞'-to-ℕ→𝟚-prop ∞')
              (λ (_ , (_ , e)) → zero-is-not-one e)

  l₁ : (u : ℕ∞') → ¬ is-finite' ∞' + ¬ is-finite' u
  l₁ u = llpo (ℕ∞'-to-ℕ→𝟚 ∞')      (ℕ∞'-to-ℕ→𝟚 u)
              (ℕ∞'-to-ℕ→𝟚-prop ∞') (ℕ∞'-to-ℕ→𝟚-prop u)
              (λ ((_ , e) , _) → zero-is-not-one e)

  l-property : l₁ ∞' ＝ l₀ ∞'
  l-property = ap (llpo (ℕ∞'-to-ℕ→𝟚 ∞')      (ℕ∞'-to-ℕ→𝟚 ∞')
                  (ℕ∞'-to-ℕ→𝟚-prop ∞') (ℕ∞'-to-ℕ→𝟚-prop ∞'))
                  (dfunext fe (λ (((_ , e) , _) : T (λ _ → ₀) × T (λ _ → ₀))
                                                → 𝟘-elim (zero-is-not-one e)))
  f₀ f₁ : ℕ∞' → 𝟚
  f₀ u = ϕ u  ∞' (l₀ u)
  f₁ u = ϕ ∞' u  (l₁ u)

  f-property : ¬ ((f₀ ∞' ＝ ₁) × (f₁ ∞' ＝ ₀))
  f-property (e₀ , e₁) =
   zero-is-not-one
    (₀               ＝⟨ e₁ ⁻¹ ⟩
     f₁ ∞'           ＝⟨ refl ⟩
     ϕ ∞' ∞' (l₁ ∞') ＝⟨ ap (ϕ ∞' ∞') l-property ⟩
     ϕ ∞' ∞' (l₀ ∞') ＝⟨ refl ⟩
     f₀ ∞'           ＝⟨ e₀ ⟩
     ₁               ∎ )

  ϕ₀-property : (u : ℕ∞') (d : ¬ is-finite' u + ¬ is-finite' ∞')
              → is-finite' u
              → ϕ u ∞' d ＝ ₁
  ϕ₀-property u (inl l) h = 𝟘-elim (l h)
  ϕ₀-property u (inr _) h = refl

  ϕ₁-property : (u : ℕ∞') (d : ¬ is-finite' ∞' + ¬ is-finite' u)
              → is-finite' u
              → ϕ ∞' u d ＝ ₀
  ϕ₁-property u (inl _) h = refl
  ϕ₁-property u (inr r) h = 𝟘-elim (r h)

  f₀-property : (u : ℕ∞') → is-finite' u → f₀ u ＝ ₁
  f₀-property u = ϕ₀-property u (l₀ u)

  f₁-property : (u : ℕ∞') → is-finite' u → f₁ u ＝ ₀
  f₁-property u = ϕ₁-property u (l₁ u)

  wlpo₀ : f₀ ∞' ＝ ₀ → WLPO
  wlpo₀ e = wlpo
   where
    𝕗₀ : ℕ∞ → 𝟚
    𝕗₀ = complement ∘ f₀ ∘ ⌜ ℕ∞-to-ℕ∞'-≃ fe ⌝

    b₀ : (n : ℕ) → 𝕗₀ (ι n) ＝ ₀
    b₀ n = 𝕗₀ (ι n)                                   ＝⟨ refl ⟩
           complement (f₀ (⌜ ℕ∞-to-ℕ∞'-≃ fe ⌝ (ι n))) ＝⟨ I ⟩
           complement (f₀ (ι n))                      ＝⟨ II ⟩
           complement ₁                               ＝⟨ refl ⟩
           ₀                                          ∎
            where
             I  = ap (complement ∘ f₀) (finite-preservation fe n)
             II = ap complement (f₀-property (ι n) (ℕ-to-ℕ∞'-is-finite' n))


    b₁ : 𝕗₀ ∞ ＝ ₁
    b₁ = 𝕗₀ ∞                                   ＝⟨ refl ⟩
         complement (f₀ (⌜ ℕ∞-to-ℕ∞'-≃ fe ⌝ ∞)) ＝⟨ I ⟩
         complement (f₀ ∞')                     ＝⟨ II ⟩
         complement ₀                           ＝⟨ refl ⟩
         ₁                                      ∎
          where
           I  = ap (complement ∘ f₀) (∞-preservation fe)
           II = ap complement e

    wlpo : WLPO
    wlpo = basic-discontinuity-taboo fe 𝕗₀ (b₀ , b₁)

  wlpo₁ : f₁ ∞' ＝ ₁ → WLPO
  wlpo₁ e = wlpo
   where
    𝕗₁ : ℕ∞ → 𝟚
    𝕗₁ = f₁ ∘ ⌜ ℕ∞-to-ℕ∞'-≃ fe ⌝

    b₀ : (n : ℕ) → 𝕗₁ (ι n) ＝ ₀
    b₀ n = 𝕗₁ (ι n)                      ＝⟨ refl ⟩
           f₁ (⌜ ℕ∞-to-ℕ∞'-≃ fe ⌝ (ι n)) ＝⟨ ap f₁ (finite-preservation fe n) ⟩
           f₁ (ι n)                      ＝⟨ I ⟩
           ₀                             ∎
            where
             I = f₁-property (ι n) (ℕ-to-ℕ∞'-is-finite' n)

    b₁ : 𝕗₁ ∞ ＝ ₁
    b₁ = 𝕗₁ ∞                      ＝⟨ refl ⟩
         f₁ (⌜ ℕ∞-to-ℕ∞'-≃ fe ⌝ ∞) ＝⟨ ap f₁ (∞-preservation fe) ⟩
         f₁ ∞'                     ＝⟨ e ⟩
         ₁                         ∎

    wlpo : WLPO
    wlpo = basic-discontinuity-taboo fe 𝕗₁ (b₀ , b₁)

  wlpo : WLPO
  wlpo = Cases (𝟚-possibilities (f₀ ∞'))
          (λ (e₀ : f₀ ∞' ＝ ₀) → wlpo₀ e₀)
          (λ (e₀ : f₀ ∞' ＝ ₁)
                 → Cases (𝟚-possibilities (f₁ ∞'))
                    (λ (e₁ : f₁ ∞' ＝ ₀) → 𝟘-elim (f-property (e₀ , e₁)))
                    (λ (e₁ : f₁ ∞' ＝ ₁) → wlpo₁ e₁))

\end{code}

TODO. (Easy, but perhaps laborious.) Show the following.

\begin{code}

{-
WLPO-gives-untruncated-LLPO : WLPO-traditional → untruncated-LLPO
WLPO-gives-untruncated-LLPO = {!!}
-}

\end{code}

We now formalate (truncated) LLPO.

\begin{code}

module _ (pt : propositional-truncations-exist) where

 open PropositionalTruncation pt

 LLPO : 𝓤₀ ̇
 LLPO = (α : ℕ → 𝟚)
      → is-prop (Σ n ꞉ ℕ , α n ＝ ₁)
      → ((n : ℕ) → α (double n) ＝ ₀) ∨ ((n : ℕ) → α (sdouble n) ＝ ₀)

 untruncated-LLPO-gives-LLPO : untruncated-LLPO → LLPO
 untruncated-LLPO-gives-LLPO ullpo α i = ∣ ullpo α i ∣

\end{code}

The most natural form of LLPO for what we've done above is the following.

\begin{code}

 ℕ∞-LLPO : 𝓤₀ ̇
 ℕ∞-LLPO = (u v : ℕ∞) → ¬ (is-finite u × is-finite v) → (u ＝ ∞) ∨ (v ＝ ∞)

\end{code}

TODO. (Easy, given what we've proved.) Show that ℕ∞-LLPO and LLPO are
logically equivalent (and hence equivalent).

TODO. Give a better version of untruncated-LLPO-gives-WLPO using
this. The proof won't be different. It will just be a factorization
through the proof of the previous TODO.

LLPO doesn't imply WLPO (there are published refereces - find and
include them here). One example seems to Johnstone's topological
topos, but this is unpublished as far as I know.
