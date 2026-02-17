Martin Escardo 12-14 March 2024.

We construct an embedding of ℕ∞ into ℕ⊥, the lifting of ℕ, or the
flat domain of natural numbers, and prove various properties of it.

We conclude that we can recover ℕ∞ as the subtype of sharp elements of ℕ⊥,

  ℕ∞ ≃ (Σ y ꞉ ℕ⊥ , is-sharp y),

where y is called sharp if η n ⊑ y is decidable for every n ꞉ ℕ [1].

[1] Tom de Jong. Apartness, sharp elements, and the Scott topology of
    domains.
    Mathematical Structures in Computer Science , Volume 33 , Issue 7,
    August 2023 , pp. 573 - 604.
    https://doi.org/10.1017/S0960129523000282

There are two equivalent copies of ℕ∞ in this development. We use the
one defined in CoNaturals.GenericConvergentSequence2 imported via the
module CoNaturals.Type2.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.Subsingletons

module CoNaturals.Sharp
        (fe : funext 𝓤₀ 𝓤₀)
        (pe : propext 𝓤₀)
       where

open import CoNaturals.Type2
open import Lifting.Construction 𝓤₀
open import Lifting.IdentityViaSIP 𝓤₀ {𝓤₀} {ℕ}
open import Lifting.Set 𝓤₀
open import Lifting.UnivalentWildCategory 𝓤₀ {𝓤₀} ℕ
open import MLTT.Plus-Properties
open import MLTT.Two-Properties
open import Notation.CanonicalMap
open import NotionsOfDecidability.Decidable
open import UF.DiscreteAndSeparated
open import UF.Embeddings
open import UF.Equiv
open import UF.PropTrunc
open import UF.Subsingletons-FunExt

\end{code}

We introduce the following standard notation, and write ι : ℕ → ℕ⊥ for
the canonical inclusion of the natural numbers into the flat domain ℕ⊥
of natural numbers. Notice that we also write ι : ℕ → ℕ∞ for the
canonical inclusion of the natural numbers into the conatural numbers,
introduced in the module that defines ℕ∞.

\begin{code}

ℕ⊥ = 𝓛 ℕ

instance
 canonical-map-ℕ-ℕ⊥ : Canonical-Map ℕ ℕ⊥
 ι {{canonical-map-ℕ-ℕ⊥}} = η

instance
 Canonical-Map-ℕ-ℕ∞ : Canonical-Map ℕ ℕ∞
 ι {{Canonical-Map-ℕ-ℕ∞}} = ℕ-to-ℕ∞

\end{code}

We define a map

   sharp : ℕ∞ → ℕ⊥

so that

 * sharp (ι n) ＝ ι n and

 * sharp ∞ ＝ ⊥.

\begin{code}

sharp : ℕ∞ → ℕ⊥
sharp x = is-finite x , size {x} , being-finite-is-prop fe x

sharp-finite : (n : ℕ) → sharp (ι n) ＝ ι n
sharp-finite n = II
 where
  I : sharp (ι n) ⊑ ι n
  I = (λ _ → ⋆) ,
      (λ (n' , e) → ℕ-to-ℕ∞-lc fe ((diagonal-lemma fe n' (ι n) e)⁻¹))

  II : sharp (ι n) ＝ ι n
  II = ⊑-anti-lemma pe fe fe I
        (λ _ → n , (ℕ-to-ℕ∞-diagonal fe n))

sharp-∞ : sharp ∞ ＝ ⊥
sharp-∞ = II
 where
  I : sharp ∞ ⊑ ⊥
  I = is-infinite-∞ , (λ is-finite-∞ → 𝟘-elim (is-infinite-∞ is-finite-∞))

  II : sharp ∞ ＝ ⊥
  II = ⊑-anti pe fe fe (I , ⊥-least (sharp ∞))

\end{code}

The map sharp is left-cancellable and hence an embedding.

\begin{code}

sharp-lc : left-cancellable sharp
sharp-lc {x} {y} e = II
 where
  I : (x y : ℕ∞) → sharp x ⋍· sharp y → (n : ℕ) → ι n ＝ x → ι n ＝ y
  I x y a n e =
   ι n                     ＝⟨ ap ι (g φ) ⟩
   ι (size {y} (⌜ f ⌝ φ))  ＝⟨ size-property fe (⌜ f ⌝ φ) ⟩
   y                       ∎
   where
    φ : is-finite x
    φ = n , (ℕ∞-to-ℕ→𝟚 x n     ＝⟨ ap (λ - → ℕ∞-to-ℕ→𝟚 - n) (e ⁻¹) ⟩
             ℕ∞-to-ℕ→𝟚 (ι n) n ＝⟨ ℕ-to-ℕ∞-diagonal fe n ⟩
             ₁                 ∎)

    f : is-finite x ≃ is-finite y
    f = is-defined-⋍· (sharp x) (sharp y) a

    g : (φ : is-finite x) → size {x} φ ＝ size {y} (⌜ f ⌝ φ)
    g = value-⋍· (sharp x) (sharp y) a

  II : x ＝ y
  II = ℕ∞-equality-criterion fe x y
        (I x y (Id-to-⋍· _ _ e))
        (I y x (Id-to-⋍· _ _ (e ⁻¹)))

sharp-is-embedding : is-embedding sharp
sharp-is-embedding = lc-maps-into-sets-are-embeddings sharp sharp-lc
                      (lifting-of-set-is-set fe fe pe ℕ ℕ-is-set)

\end{code}

We have the following two corollaries.

\begin{code}

sharp-finite' : (x : ℕ∞) (n : ℕ) → sharp x ＝ ι n → x ＝ ι n
sharp-finite' x n e = sharp-lc (sharp x     ＝⟨ e ⟩
                                ι n         ＝⟨ (sharp-finite n)⁻¹ ⟩
                                sharp (ι n) ∎)

sharp-∞' : (x : ℕ∞) → sharp x ＝ ⊥ → x ＝ ∞
sharp-∞' x e = sharp-lc (sharp x ＝⟨ e ⟩
                         ⊥       ＝⟨ sharp-∞ ⁻¹ ⟩
                         sharp ∞ ∎)
\end{code}

The image of the embedding has empty complement, in the following
sense.

\begin{code}

sharp-image-has-empty-complement : ¬ (Σ l ꞉ 𝓛 ℕ , ((x : ℕ∞) → sharp x ≠ l))
sharp-image-has-empty-complement (l , f) =
 η-image fe fe pe
   (l ,
   (λ (e : l ＝ ⊥) → f ∞ (sharp-∞ ∙ e ⁻¹)) ,
   (λ n (e : l ＝ η n) → f (ι n) (sharp-finite n ∙ e ⁻¹)))

\end{code}

But the embedding is a surjection (and hence an equivalence) if and
only if excluded middle holds.

\begin{code}

module _ (pt : propositional-truncations-exist) where

 open PropositionalTruncation pt
 open import UF.ImageAndSurjection pt
 open import UF.ClassicalLogic

 sharp-is-surjection-gives-EM : is-surjection sharp → EM 𝓤₀
 sharp-is-surjection-gives-EM sharp-is-surjection P P-is-prop =
  ∥∥-rec (decidability-of-prop-is-prop fe P-is-prop) II I
  where
   y : ℕ⊥
   y = P , (λ _ → 0) , P-is-prop

   I : ∃ x ꞉ ℕ∞ , sharp x ＝ y
   I = sharp-is-surjection y

   II : (Σ x ꞉ ℕ∞ , sharp x ＝ y) → P + ¬ P
   II (x , e) = IV III
    where
     III : (ι 0 ＝ x) + (ι 0 ≠ x)
     III = finite-isolated fe 0 x

     IV : (ι 0 ＝ x) + (ι 0 ≠ x) → P + ¬ P
     IV (inl d) = inl (⌜ C ⌝⁻¹ ⋆)
      where
       A = y           ＝⟨ e ⁻¹ ⟩
           sharp x     ＝⟨ ap sharp (d ⁻¹) ⟩
           sharp (ι 0) ＝⟨ sharp-finite 0 ⟩
           ι 0         ∎

       B : y ⋍· ι 0
       B = Id-to-⋍· _ _ A

       C : P ≃ 𝟙
       C = is-defined-⋍· y (ι 0) B

     IV (inr ν) = inr (contrapositive B C)
      where
       A : y ⊑ ι 0
       A = unique-to-𝟙 , (λ (p : P) → refl)

       B : P → y ＝ ι 0
       B p = ⊑-anti-lemma pe fe fe A (λ _ → p)

       C : ¬ (y ＝ ι 0)
       C d = ν (C₁ ⁻¹)
        where
         C₀ = sharp x ＝⟨ e ⟩
              y       ＝⟨ d ⟩
              ι 0     ∎

         C₁ : x ＝ ι 0
         C₁ = sharp-finite' x 0 C₀

 EM-gives-sharp-is-retraction : EM 𝓤₀ → (y : ℕ⊥) → Σ x ꞉ ℕ∞ , sharp x ＝ y
 EM-gives-sharp-is-retraction em y@(P , φ , P-is-prop) =
   I (em P P-is-prop)
  where
   I : P + ¬ P → Σ x ꞉ ℕ∞ , sharp x ＝ y
   I (inl p) = ι (φ p) , III
    where
     II : sharp (ι (φ p)) ⊑ y
     II = (λ _ → p) ,
          (λ (n , e) → ℕ-to-ℕ∞-lc fe ((diagonal-lemma fe n (ι (φ p)) e)⁻¹))

     III : sharp (ι (φ p)) ＝ y
     III = ⊑-anti-lemma pe fe fe II (λ _ → ℕ-to-ℕ∞-is-finite (φ p))

   I (inr ν) = ∞ , III
    where
     II : sharp ∞ ⊑ y
     II = transport (_⊑ y) (sharp-∞ ⁻¹) (⊥-least y)

     III : sharp ∞ ＝ y
     III = ⊑-anti-lemma pe fe fe II λ (p : P) → 𝟘-elim (ν p)

 EM-gives-sharp-is-surjection : EM 𝓤₀ → is-surjection sharp
 EM-gives-sharp-is-surjection em y = ∣ EM-gives-sharp-is-retraction em y ∣

 EM-gives-sharp-is-equiv : EM 𝓤₀ → is-equiv sharp
 EM-gives-sharp-is-equiv em = lc-split-surjections-are-equivs
                               sharp
                               sharp-lc
                               (EM-gives-sharp-is-retraction em)
\end{code}

Added 14th March 2024.

The image of the function sharp consists precisely of the sharp
elements of ℕ⊥ in the sense of [1], so that we can recover ℕ∞ as the
subtype of sharp elements of ℕ⊥:

            ℕ∞ ≃ (Σ y : ℕ⊥ , is-sharp y).

In an algebraic domain D, it is proved in [1] that d : D is sharp if
and only if b ⊑ d is decidable for every compact element b : D.

In DomainTheory.Lifting.LiftingSetAlgebraic, it is shown that the
compact elements of 𝓛 X for a set X are precisely ⊥ and those of the
form η x. But ⊥ ⊑ d is always decidable, simply because it is true. So
an element d of 𝓛 X is sharp if and only if η x ⊑ d is decidable for
every x : X.

We continue with the particular case X = ℕ.

\begin{code}

is-sharp : ℕ⊥ → 𝓤₀ ̇
is-sharp y = (n : ℕ) → is-decidable (ι n ⊑ y)

being-sharp-is-prop : (y : ℕ⊥) → is-prop (is-sharp y)
being-sharp-is-prop l = Π-is-prop fe
                         (λ n → decidability-of-prop-is-prop fe
                                 (⊑-prop-valued fe fe ℕ-is-set (ι n) l))

sharp-is-sharp : (x : ℕ∞) → is-sharp (sharp x)
sharp-is-sharp x n = I (finite-isolated fe n x)
 where
  I : is-decidable (ι n ＝ x) → is-decidable (ι n ⊑ sharp x)
  I (inl refl) = inl ((λ ⋆ → n , ℕ-to-ℕ∞-diagonal fe n) , (λ ⋆ → refl))
  I (inr ν) = inr f
   where
    f : ¬ (ι n ⊑ sharp x)
    f (a , b) = ν (ι n                ＝⟨ ap ι (b ⋆) ⟩
                   ι (size {x} (a ⋆)) ＝⟨ size-property fe (a ⋆) ⟩
                   x                  ∎)

only-sharp-is-sharp : (y : ℕ⊥) → is-sharp y → Σ x ꞉ ℕ∞ , sharp x ＝ y
only-sharp-is-sharp y@(P , φ , P-is-prop) y-is-sharp = V
 where
  y-is-sharp' : (n : ℕ) → ¬ (ι n ⊑ y) + (ι n ⊑ y)
  y-is-sharp' n = +-commutative (y-is-sharp n)

  α : ℕ → 𝟚
  α = indicator-map y-is-sharp'

  α-property₀ : (n : ℕ) → α n ＝ ₀ → ¬ (ι n ⊑ y)
  α-property₀ = indicator-property₀ y-is-sharp'

  α-property₁ : (n : ℕ) → α n ＝ ₁ → ι n ⊑ y
  α-property₁ = indicator-property₁ y-is-sharp'

  α-property : (n n' : ℕ) → α n ＝ ₁ → α n' ＝ ₁ → n ＝ n'
  α-property n n' e e' = η-bounded y n n' (α-property₁ n e) (α-property₁ n' e')

  a : has-at-most-one-₁ α
  a (n , e) (n' , e') = to-T-＝ (α-property n n' e e')

  x : ℕ∞
  x = α , a

  II : sharp x ⊑ y
  II = II₀ , II₁
   where
    II₀ : (Σ n ꞉ ℕ , α n ＝ ₁) → P
    II₀ (n , e) = def-pr (ι n) y (α-property₁ n e) ⋆

    II₁ : ((n , e) : Σ n ꞉ ℕ , α n ＝ ₁) → n ＝ φ (II₀ (n , e))
    II₁ (n , e) = α-property n n' e B
     where
      n' : ℕ
      n' = φ (II₀ (n , e))

      A : ι n' ⊑ y
      A = (λ _ → II₀ (n , e)) , (λ _ → refl)

      B : α n' ＝ ₁
      B = different-from-₀-equal-₁ (λ (d : α n' ＝ ₀) → α-property₀ n' d A)

  III : P → Σ n ꞉ ℕ , α n ＝ ₁
  III p = φ p , different-from-₀-equal-₁ (λ (e : α (φ p) ＝ ₀) → III₁ e III₀)
   where
    III₀ : ι (φ p) ⊑ y
    III₀ = (λ _ → p) , (λ _ → refl)

    III₁ : α (φ p) ＝ ₀ → ¬ (ι (φ p) ⊑ y)
    III₁ = α-property₀ (φ p)

  IV : sharp x ＝ y
  IV = ⊑-anti-lemma pe fe fe II III

  V : Σ x ꞉ ℕ∞ , sharp x ＝ y
  V = x , IV

\end{code}

The following gives yet another construction of the conatural numbers.

\begin{code}

theorem : ℕ∞ ≃ (Σ y ꞉ ℕ⊥ , is-sharp y)
theorem = r , r-is-equiv
 where
  r : ℕ∞ → (Σ y ꞉ ℕ⊥ , is-sharp y)
  r x = sharp x , sharp-is-sharp x

  r-is-embedding : is-embedding r
  r-is-embedding = factor-is-embedding r pr₁
                    sharp-is-embedding
                    (pr₁-is-embedding being-sharp-is-prop)

  s : (Σ y ꞉ ℕ⊥ , is-sharp y) → ℕ∞
  s (y , y-is-sharp) = pr₁ (only-sharp-is-sharp y y-is-sharp)

  h : (σ@(y , _) : Σ y ꞉ ℕ⊥ , is-sharp y) → sharp (s σ) ＝ y
  h (y , y-is-sharp) = pr₂ (only-sharp-is-sharp y y-is-sharp)

  rs : r ∘ s ∼ id
  rs σ = to-subtype-＝ being-sharp-is-prop (h σ)

  r-is-equiv : is-equiv r
  r-is-equiv = embeddings-with-sections-are-equivs r r-is-embedding (s , rs)

\end{code}

TODO. Notice that

 is-sharp y ≃ ((x : X) → is-decidable (fiber (value y) x))

because (ι x ⊑ u) ≃ fiber (value y) x.

Other ways to distinguish ℕ∞ and ℕ⊥:

 * ℕ∞ is totally separated.

 * ℕ⊥ is injective and hence indecomposable.

This is already proved in other modules.

For any type X, we can define X∞ = (Σ y ꞉ X⊥ , is-sharp y). But to
define a map X → X∞ we need X to have decidable equality, because
η x ⊑ η y iff x ＝ y.

In a constructive setting, there are in principle discrete types X
that are not necessarily countable. One of them is the type ℕ∞ → 𝟚.
But this is countable as soon as we assume that all functions ℕ∞ → 𝟚
are continuous (which is implied by "all functions (ℕ → ℕ) → ℕ are
continuous").
