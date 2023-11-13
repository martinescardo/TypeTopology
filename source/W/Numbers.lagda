Martin Escardo, July 2023

A type of numbers used to measure lengths of paths in trees in W-types
(see the module W.Paths).

For an exposition of what is done here, see the post 7/6 of this thread:
https://mathstodon.xyz/@MartinEscardo/110753930251021051

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (_^_)

module W.Numbers where

open import Fin.Type hiding (suc)
open import NotionsOfDecidability.Decidable
open import UF.Base
open import UF.DiscreteAndSeparated
open import UF.Embeddings
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.ExcludedMiddle
open import UF.FunExt
open import UF.PropIndexedPiSigma
open import UF.PropTrunc
open import UF.Retracts
open import UF.Sets
open import UF.SubtypeClassifier
open import UF.SubtypeClassifier-Properties
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import W.Properties
open import W.Type

\end{code}

We work with a fixed universe 𝓥.

\begin{code}

module _ {𝓥 : Universe} where

 𝓝 : 𝓥 ⁺ ̇
 𝓝 = W (Ω 𝓥) _holds

 positive : 𝓝 → Ω 𝓥
 positive = W-root

 is-positive : 𝓝 → 𝓥 ̇
 is-positive n = positive n holds

\end{code}

The predecessor function is defined on positive numbers.

\begin{code}

 Pred : (n : 𝓝) → is-positive n → 𝓝
 Pred = W-forest

\end{code}

For every proposition p, there is a p-ary successor function. Notice
that we can regard an element of 𝓝 ^ p as a p-indexed tuple of
elements of 𝓝, or, equivalently, as a partial element of 𝓝.

\begin{code}

 _^_ : 𝓤 ̇  → Ω 𝓥 → 𝓥 ⊔ 𝓤 ̇
 X ^ p = p holds → X

 Suc : (p : Ω 𝓥) → 𝓝 ^ p → 𝓝
 Suc = ssup

 Suc-positivity : (p : Ω 𝓥) (ns : 𝓝 ^ p) → positive (Suc p ns) ＝ p
 Suc-positivity = W-ssup-root

 Pred-Suc : (p : Ω 𝓥) (ns : 𝓝 ^ p) → Pred (Suc p ns) ＝ ns
 Pred-Suc = W-ssup-forest

 Suc-Pred : (n : 𝓝) → Suc (positive n) (Pred n) ＝ n
 Suc-Pred = W-η

 𝓝-induction : (P : 𝓝 → 𝓦 ̇ )
             → ((p : Ω 𝓥) (ns : 𝓝 ^ p)
                   → ((h : p holds) → P (ns h))
                   → P (Suc p ns))
             → (n : 𝓝) → P n
 𝓝-induction = W-induction

 𝓝-induction' : (P : 𝓝 → 𝓦 ̇ )
              → ((n : 𝓝)
                    → ((p : is-positive n) → P (Pred n p))
                    → P n)
              → (n : 𝓝) → P n
 𝓝-induction' = W-induction'

\end{code}

A criterion for equality on 𝓝.

\begin{code}

 to-𝓝-＝ : {p q : Ω 𝓥} {ms : 𝓝 ^ p} {ns : 𝓝 ^ q}
         → (Σ e ꞉ p ＝ q , (ms ＝ ns ∘ transport _holds e))
         → Suc p ms ＝ Suc q ns
 to-𝓝-＝ = to-W-＝ (Ω 𝓥) _holds

 from-𝓝-＝ : {p q : Ω 𝓥} {ms : 𝓝 ^ p} {ns : 𝓝 ^ q}
           → Suc p ms ＝ Suc q ns
           → (Σ e ꞉ p ＝ q , (ms ＝ ns ∘ transport _holds e))
 from-𝓝-＝ = from-W-＝ (Ω 𝓥) _holds

\end{code}

The ⊥-ary successor function amounts to the number zero, and the ⊤-ary
successor function amounts to the ordinary successor function.

\begin{code}

 private
  Zero' : (𝟘 → 𝓝) → 𝓝
  Zero' = Suc ⊥

  Succ' : (𝟙 → 𝓝) → 𝓝
  Succ' = Suc ⊤

 Zero : 𝓝
 Zero = Zero' unique-from-𝟘

 Succ : 𝓝 → 𝓝
 Succ n = Succ' (λ _ → n)

 being-positive-is-prop : (n : 𝓝) → is-prop (is-positive n)
 being-positive-is-prop n = holds-is-prop (positive n)

 Succ-is-positive : (n : 𝓝) → is-positive (Succ n)
 Succ-is-positive n = ⊤-holds

 Zero-is-not-positive : ¬ is-positive Zero
 Zero-is-not-positive = ⊥-doesnt-hold

 Succ-is-not-Zero : (n : 𝓝) → Succ n ≠ Zero
 Succ-is-not-Zero n e = Zero-is-not-positive
                         (transport
                           is-positive
                           e
                           (Succ-is-positive n))

 Zero-is-not-Succ : (n : 𝓝) → Zero ≠ Succ n
 Zero-is-not-Succ n = ≠-sym (Succ-is-not-Zero n)

\end{code}

The type of positive numbers.

\begin{code}

 𝓝⁺ : 𝓥 ⁺ ̇
 𝓝⁺ = Σ n ꞉ 𝓝 , is-positive n

 forget-positivity : 𝓝⁺ → 𝓝
 forget-positivity = pr₁

 forget-positivity-is-embedding : is-embedding forget-positivity
 forget-positivity-is-embedding = pr₁-is-embedding being-positive-is-prop

 Pred⁺ : 𝓝⁺ → 𝓝
 Pred⁺ = uncurry Pred

 Succ⁺ : 𝓝 → 𝓝⁺
 Succ⁺ n = Succ n , Succ-is-positive n

 Pred⁺-Succ⁺ : (n : 𝓝) → Pred⁺ (Succ⁺ n) ＝ n
 Pred⁺-Succ⁺ n = refl

 Succ-lc : left-cancellable Succ
 Succ-lc {m} {n} e = II
  where
   have-e : Succ m ＝ Succ n
   have-e = e

   I : Succ⁺ m ＝ Succ⁺ n
   I = embeddings-are-lc forget-positivity forget-positivity-is-embedding e

   II : m ＝ n
   II = ap Pred⁺ I

\end{code}

The type of natural numbers is embedded into our type of numbers.

\begin{code}

 ℕ-to-𝓝 : ℕ → 𝓝
 ℕ-to-𝓝 zero     = Zero
 ℕ-to-𝓝 (succ n) = Succ (ℕ-to-𝓝 n)

 ℕ-to-𝓝-lc : left-cancellable ℕ-to-𝓝
 ℕ-to-𝓝-lc {zero}   {zero}   e = refl
 ℕ-to-𝓝-lc {zero}   {succ n} e = 𝟘-elim (Zero-is-not-Succ (ℕ-to-𝓝 n) e)
 ℕ-to-𝓝-lc {succ m} {zero}   e = 𝟘-elim (Succ-is-not-Zero (ℕ-to-𝓝 m) e)
 ℕ-to-𝓝-lc {succ m} {succ n} e = ap succ (ℕ-to-𝓝-lc (Succ-lc e))

\end{code}

We now assume functional and propositional extensionality.

\begin{code}

 module _ (fe : Fun-Ext) (pe : Prop-Ext) where

  𝓝-is-set : is-set 𝓝
  𝓝-is-set = W-is-set (Ω 𝓥) _holds fe (Ω-is-set fe pe)

  Succ-is-embedding : is-embedding Succ
  Succ-is-embedding = lc-maps-into-sets-are-embeddings Succ Succ-lc 𝓝-is-set

  ℕ-to-𝓝-is-embedding : is-embedding ℕ-to-𝓝
  ℕ-to-𝓝-is-embedding = lc-maps-into-sets-are-embeddings ℕ-to-𝓝 ℕ-to-𝓝-lc 𝓝-is-set

  Succ⁺-Pred⁺ : (n⁺ : 𝓝⁺) → Succ⁺ (Pred⁺ n⁺) ＝ n⁺
  Succ⁺-Pred⁺ (n , pos) = to-subtype-＝ being-positive-is-prop I
   where
    I = Succ (Pred n pos)         ＝⟨ refl ⟩
        Suc ⊤ (λ _ → Pred n pos)  ＝⟨ II ⟩
        Suc (positive n) (Pred n) ＝⟨ Suc-Pred n ⟩
        n                         ∎
     where
      II = to-𝓝-＝
            (((true-gives-equal-⊤ pe fe
                (is-positive n)
                (being-positive-is-prop n)
                pos)⁻¹) ,
            dfunext fe (λ h → ap (Pred n) (being-positive-is-prop n _ _)))

\end{code}

Hence 𝓝⁺ and 𝓝 are equivalent.

\begin{code}

  𝓝⁺-≃-𝓝 : 𝓝⁺ ≃ 𝓝
  𝓝⁺-≃-𝓝 = qinveq Pred⁺ (Succ⁺ , Succ⁺-Pred⁺ , Pred⁺-Succ⁺)

\end{code}

End of the anonymous submodule assuming Fun-Ext and Prop-Ext.

Our numbers "count" the number of elements of certain types.

\begin{code}

 𝓕𝓲𝓷 : 𝓝 → 𝓥 ̇
 𝓕𝓲𝓷 (ssup p ns) = p holds + (Σ h ꞉ p holds , 𝓕𝓲𝓷 (ns h))

\end{code}

The map Fin : ℕ → 𝓤₀ factors as ℕ-to-𝓝 : ℕ → 𝓝 followed
by 𝓕𝓲𝓷 : 𝓝 → 𝓥.

\begin{code}

 Fin-factor : (n : ℕ) → 𝓕𝓲𝓷 (ℕ-to-𝓝 n) ≃ Fin n
 Fin-factor zero =
  𝟘 + (Σ h ꞉ 𝟘 , 𝓕𝓲𝓷 (𝟘-elim h)) ≃⟨ 𝟘-lneutral ⟩
  (Σ h ꞉ 𝟘 , 𝓕𝓲𝓷 (𝟘-elim h))     ≃⟨ prop-indexed-sum-zero id ⟩
  𝟘                              ■

 Fin-factor (succ n) = I
  where
   IH : 𝓕𝓲𝓷 (ℕ-to-𝓝 n) ≃ Fin n
   IH = Fin-factor n

   I = 𝓕𝓲𝓷 (ℕ-to-𝓝 (succ n))          ≃⟨ ≃-refl _ ⟩
       𝟙 + (Σ h ꞉ 𝟙 , 𝓕𝓲𝓷 (ℕ-to-𝓝 n)) ≃⟨ II  ⟩
       𝟙 + 𝓕𝓲𝓷 (ℕ-to-𝓝 n)             ≃⟨ III ⟩
       𝟙 + Fin n                       ≃⟨ +comm ⟩
       Fin n + 𝟙 {𝓥}                   ≃⟨ IV ⟩
       Fin n + 𝟙 {𝓤₀}                  ≃⟨ ≃-refl _ ⟩
       Fin (succ n)                    ■
    where
     II  = +-cong (≃-refl 𝟙) 𝟙-lneutral
     III = +-cong (≃-refl 𝟙) IH
     IV  = +-cong (≃-refl _) (one-𝟙-only 𝓥 𝓤₀)

\end{code}

Although we can't say that ℕ-to-𝓝 n is a surjection, its image has
empty complement.

\begin{code}

 Ω-to-𝓝 : Ω 𝓥 → 𝓝
 Ω-to-𝓝 p = Suc p (λ _ → Zero)

 Ω-to-𝓝-behaviour : (p : Ω 𝓥) → is-positive (Ω-to-𝓝 p) ＝ (p holds)
 Ω-to-𝓝-behaviour p = refl

 Ω-is-retract-of-𝓝 : retract Ω 𝓥 of 𝓝
 Ω-is-retract-of-𝓝 = positive , Ω-to-𝓝 , (λ x → refl)

 Ω-to-𝓝-is-section : is-section Ω-to-𝓝
 Ω-to-𝓝-is-section = section-is-section Ω-is-retract-of-𝓝

 Ω-to-𝓝-lc : left-cancellable Ω-to-𝓝
 Ω-to-𝓝-lc = sections-are-lc Ω-to-𝓝 Ω-to-𝓝-is-section

 decidability-of-positivity-gives-LEM : ((n : 𝓝) → is-decidable (is-positive n))
                                      →  LEM 𝓥
 decidability-of-positivity-gives-LEM f p = I
  where
   I : is-decidable (is-positive (Ω-to-𝓝 p))
   I = f (Ω-to-𝓝 p)

\end{code}

We now assume functional and propositional extensionality
again. Sections are not necessarily embeddings
(https://doi.org/10.2168/LMCS-12(3:9)2016), but sections into sets
are:

\begin{code}

 module _ (fe : Fun-Ext) (pe : Prop-Ext) where

  Ω-to-𝓝-is-embedding : is-embedding Ω-to-𝓝
  Ω-to-𝓝-is-embedding = lc-maps-into-sets-are-embeddings
                          Ω-to-𝓝
                          Ω-to-𝓝-lc
                          (𝓝-is-set fe pe)

  lc-map-from-Ω-to-ℕ-gives-LEM : (Σ f ꞉ (Ω 𝓥 → ℕ) , left-cancellable f)
                               → LEM 𝓥
  lc-map-from-Ω-to-ℕ-gives-LEM (f , f-lc) p = I (ℕ-is-discrete (f ⊤) (f p))
   where
    I : is-decidable (f ⊤ ＝ f p) → is-decidable (p holds)
    I (inl e) = inl (Idtofun (ap _holds (f-lc e)) ⋆)
    I (inr ν) = inr (λ (h : p holds)
                          → ν (ap f (holds-gives-equal-⊤ pe fe p h)⁻¹))

\end{code}

We now further assume that propositional truncations exist.

\begin{code}

  module _ (pt : propositional-truncations-exist) where

   open PropositionalTruncation pt
   open import UF.ImageAndSurjection pt

   ℕ-to-𝓝-surjection-gives-LEM : is-surjection ℕ-to-𝓝 → LEM 𝓥
   ℕ-to-𝓝-surjection-gives-LEM s p = I
    where
     f : ℕ ≃ 𝓝
     f = ℕ-to-𝓝 ,
         surjective-embeddings-are-equivs ℕ-to-𝓝
          (ℕ-to-𝓝-is-embedding fe pe) s

     g : Ω 𝓥 → ℕ
     g = ⌜ f ⌝⁻¹ ∘ Ω-to-𝓝

     g-is-emb : is-embedding g
     g-is-emb = ∘-is-embedding
                 Ω-to-𝓝-is-embedding
                 (equivs-are-embeddings ⌜ f ⌝⁻¹ ⌜ f ⌝⁻¹-is-equiv)

     I : is-decidable (p holds)
     I = lc-map-from-Ω-to-ℕ-gives-LEM (g , embeddings-are-lc g g-is-emb) p

\end{code}

Although the above shows that ℕ-to-𝓝 isn't necessarily a surjection,
its image has empty complement in the sense that there is no 𝓷 : 𝓝
which is different from ℕ-to-𝓝 n for every n : ℕ.

\begin{code}

   ℕ-to-𝓝-has-empty-complement : ¬ (Σ 𝓷 ꞉ 𝓝 , ((n : ℕ) → ℕ-to-𝓝 n ≠ 𝓷))
   ℕ-to-𝓝-has-empty-complement = uncurry ψ
    where
     ψ : (𝓷 : 𝓝) → ¬ ((n : ℕ) → ℕ-to-𝓝 n ≠ 𝓷)
     ψ (ssup p ns) f = III IV
      where
       I : Zero ≠ ssup p ns
       I = f 0

       II : ¬ (p holds) → Zero ＝ ssup p ns
       II ν = to-𝓝-＝ ((II₁ ⁻¹) , dfunext fe (λ x → 𝟘-elim x))
        where
         II₁ : p ＝ ⊥
         II₁ = fails-gives-equal-⊥ pe fe p ν


       III : ¬¬ (p holds)
       III h = I (II h)

       IV : ¬ (p holds)
       IV h = ψ (ns h) f'
        where
         IV₁ : p ＝ ⊤
         IV₁ = holds-gives-equal-⊤ pe fe p h

         f' : (n : ℕ) → ℕ-to-𝓝 n ≠ ns h
         f' n e = f (succ n) IV₂
          where
           IV₂ = Succ (ℕ-to-𝓝 n)        ＝⟨ refl ⟩
                 Suc ⊤ (λ _ → ℕ-to-𝓝 n) ＝⟨ IV₃ ⟩
                 Suc ⊤ (λ _ → ns h)     ＝⟨ IV₄ ⟩
                 Suc p ns               ∎
                  where
                   IV₃ = ap (λ - → Suc ⊤ (λ _ → -)) e
                   IV₄ = to-𝓝-＝
                          ((IV₁ ⁻¹) ,
                           dfunext fe (λ _ → ap ns (holds-is-prop p _ _)))

\end{code}

So if excluded middle holds then ℕ-to-𝓝 is a surjection and the types ℕ
and 𝓝 are equivalent.

\begin{code}

   LEM-gives-ℕ-to-𝓝-surjection : LEM (𝓥 ⁺) → is-surjection ℕ-to-𝓝
   LEM-gives-ℕ-to-𝓝-surjection lem 𝓷 = III
    where
     em = LEM-gives-EM lem

     I : ¬ ((n : ℕ) → ℕ-to-𝓝 n ≠ 𝓷)
     I = not-Σ-implies-Π-not ℕ-to-𝓝-has-empty-complement 𝓷

     II : ∃ n ꞉ ℕ , ¬¬ (ℕ-to-𝓝 n ＝ 𝓷)
     II = not-Π-implies-∃-not pt em (λ n → negations-are-props fe) I

     III : ∃ n ꞉ ℕ , ℕ-to-𝓝 n ＝ 𝓷
     III = ∥∥-functor
            (λ (n , ν) → (n , ¬¬-elim (em (ℕ-to-𝓝 n ＝ 𝓷) (𝓝-is-set fe pe)) ν))
            II

\end{code}

It is possible to reach the same conclusion assuming LEM 𝓥 rather than
LEM (𝓥 ⁺).

\begin{code}

   LEM-gives-ℕ-to-𝓝-is-equiv : LEM 𝓥 → is-equiv ℕ-to-𝓝
   LEM-gives-ℕ-to-𝓝-is-equiv lem =
    qinvs-are-equivs ℕ-to-𝓝
     ((λ 𝓷 → f 𝓷 (lem (positive 𝓷))) ,
     (λ n → η n (lem (positive (ℕ-to-𝓝 n)))) ,
     (λ 𝓷 → ε 𝓷 (lem (positive 𝓷))))
    where
     f : (𝓷 : 𝓝) → is-decidable (is-positive 𝓷) → ℕ
     f (ssup p ns) (inr ν) = zero
     f (ssup p ns) (inl h) = succ (f (ns h) (lem (positive (ns h))))

     η : (n : ℕ) (d : is-decidable (is-positive (ℕ-to-𝓝 n)))
       → f (ℕ-to-𝓝 n) d ＝ n
     η zero (inr ν)     = refl
     η (succ n) (inr ν) = 𝟘-elim (ν (Succ-is-positive (Succ (ℕ-to-𝓝 n))))
     η (succ n) (inl h) = ap succ (η n (lem (positive (ℕ-to-𝓝 n))))

     ε : (𝓷 : 𝓝) (d : is-decidable (is-positive 𝓷)) → ℕ-to-𝓝 (f 𝓷 d) ＝ 𝓷
     ε (ssup p ns) (inr ν) = to-𝓝-＝ ((I ⁻¹) , dfunext fe (λ x → 𝟘-elim x))
      where
       I : p ＝ ⊥
       I = fails-gives-equal-⊥ pe fe p ν
     ε (ssup p ns) (inl h) =
      to-𝓝-＝ ((I ⁻¹) ,
               dfunext fe (λ _ →
                ℕ-to-𝓝 (f (ns h) (lem (positive (ns h)))) ＝⟨ II ⟩
                ns h                                      ＝⟨ III ⟩
                (ns ∘ transport _holds (I ⁻¹)) _          ∎))
      where
       I : p ＝ ⊤
       I = holds-gives-equal-⊤ pe fe p h

       II  = ε (ns h) (lem (positive (ns h)))
       III = ap ns (holds-is-prop p h _)

\end{code}

TODO. Show that 𝓝 has the structure of an ordinal. This requires more
work.
