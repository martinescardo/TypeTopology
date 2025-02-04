Martin Escardo, 20 Feb 2012.

We give a negative answer to a question posed by Altenkirch, Anberrée
and Li.

They asked whether for every definable type X in Martin-Löf type
theory, it is the case that for any two provably distinct elements
x₀,x₁:X, there is a function p:X→𝟚 and a proof d: p x₀ ≠ p x₁. Here 𝟚
is the type of binary numerals, or booleans if you like, but I am not
telling you which of ₀ and ₁ is to be regarded as true or false.

If one thinks of 𝟚-valued maps as characteristic functions of clopen
sets in a topological view of types, then their question amounts to
asking whether the definable types are totally separated, that is,
whether the clopens separate the points. See Johnstone's book "Stone
Spaces" for some information about this notion - e.g. for compact
spaces, it agrees with total disconnectedness (the connected
components are the singletons) and zero-dimensionality (the clopens
form a base of the topology), but in general the three notions don't
agree.

We give an example of a type X whose total separatedness implies a
constructive taboo. The proof works by constructing two elements x₀
and x₁ of X, and a discontinuous function ℕ∞→𝟚 from any hypothetical
p:X→𝟚 with p x₀ ≠ p x₁, and then reducing discontinuity to WLPO.

Our proof assumes function extensionality. Without the assumption
there are fewer closed terms of type X→𝟚, and their question was for
closed terms X, x₀,x₁:X, and d:x₀≠x₁, and so the negative answer also
works in the absence of function extensionality. But assuming function
extensionality we get a stronger result, which is not restricted to
closed terms, and which is a theorem rather than a metatheorem.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module TypeTopology.FailureOfTotalSeparatedness (fe₀ : funext₀) where

open import MLTT.Spartan

open import CoNaturals.Type
open import MLTT.Two-Properties
open import Notation.CanonicalMap
open import Taboos.BasicDiscontinuity fe₀
open import Taboos.WLPO
open import UF.Base

\end{code}

The idea of the following construction is to replace ∞ in ℕ∞ by two
copies ∞₀ and ∞₁, which are different but not distinguishable by maps
into 𝟚, unless WLPO holds. (We can use the Cantor type (ℕ → 𝟚) or the
Baire type (ℕ → ℕ), or many other types instead of ℕ∞, with ∞ replaced
by any fixed element. But I think the proposed construction gives a
more transparent and conceptual argument. See more below.)

\begin{code}

ℕ∞₂ : 𝓤₀ ̇
ℕ∞₂ = Σ u ꞉ ℕ∞ , (u ＝ ∞ → 𝟚)

∞₀ : ℕ∞₂
∞₀ = (∞ , λ r → ₀)

∞₁ : ℕ∞₂
∞₁ = (∞ , λ r → ₁)

\end{code}

The elements ∞₀ and ∞₁ look different:

\begin{code}

naive : (pr₂ ∞₀ refl ＝ ₀) × (pr₂ ∞₁ refl ＝ ₁)
naive = refl , refl

\end{code}

But there is no function p : ℕ∞₂ → 𝟚 such that p x = pr₂ x refl, because
pr₁ x may be different from ∞, in which case pr₂ x is the function with
empty graph, and so it can't be applied to anything, and certainly
not to refl. In fact, the definition

   p : ℕ∞₂ → 𝟚
   p x = pr₂ x refl

doesn't type check (Agda says: "(pr₁ (pr₁ x) x) != ₁ of type 𝟚 when
checking that the expression refl has type pr₁ x ＝ ∞"), and hence we
haven't distinguished ∞₀ and ∞₁ by applying the same function to
them. This is clearly seen when enough implicit arguments are made
explicit.

No matter how hard we try to find such a function, we won't succeed,
because we know that WLPO is not provable:

\begin{code}

failure : (p : ℕ∞₂ → 𝟚) → p ∞₀ ≠ p ∞₁ → WLPO
failure p = disagreement-taboo p₀ p₁ lemma
 where
  p₀ : ℕ∞ → 𝟚
  p₀ u = p (u , λ r → ₀)

  p₁ : ℕ∞ → 𝟚
  p₁ u = p (u , λ r → ₁)

  lemma : (n : ℕ) → p₀ (ι n) ＝ p₁ (ι n)
  lemma n = ap (λ - → p (ι n , -)) (dfunext fe₀ claim)
   where
    claim : (r : ι n ＝ ∞) → (λ r → ₀) r ＝ (λ r → ₁) r
    claim s = 𝟘-elim (∞-is-not-finite n (s ⁻¹))

open import UF.DiscreteAndSeparated hiding (_♯_)

𝟚-indistinguishability : ¬ WLPO → (p : ℕ∞₂ → 𝟚) → p ∞₀ ＝ p ∞₁
𝟚-indistinguishability nwlpo p = 𝟚-is-¬¬-separated (p ∞₀) (p ∞₁)
                                  (not-Σ-implies-Π-not
                                    (contrapositive
                                      (λ (p , ν) → failure p ν)
                                      nwlpo)
                                    p)
\end{code}

Precisely because one cannot construct maps from ℕ∞₂ into 𝟚 that
distinguish ∞₀ and ∞₁, it is a bit tricky to prove that they are
indeed different:

\begin{code}

∞₀-and-∞₁-different : ∞₀ ≠ ∞₁
∞₀-and-∞₁-different r = zero-is-not-one claim₂
 where
  p : ∞ ＝ ∞
  p = ap pr₁ r

  t : {x x' : ℕ∞} → x ＝ x' → (x ＝ ∞ → 𝟚) → (x' ＝ ∞ → 𝟚)
  t = transport (λ - → - ＝ ∞ → 𝟚)

  claim₀ : refl ＝ p
  claim₀ = ℕ∞-is-set fe₀ refl p

  claim₁ : t p (λ p → ₀) ＝ (λ p → ₁)
  claim₁ = from-Σ-＝' r

  claim₂ : ₀ ＝ ₁
  claim₂ =  ₀                  ＝⟨ ap (λ - → t - (λ _ → ₀) refl) claim₀ ⟩
            t p (λ _ → ₀) refl ＝⟨ ap (λ - → - refl) claim₁ ⟩
            ₁                  ∎

\end{code}

Finally, the total separatedness of ℕ∞₂ is a taboo. In particular, it
can't be proved, because ¬ WLPO is consistent.

\begin{code}

open import TypeTopology.TotallySeparated

ℕ∞₂-is-not-totally-separated-in-general : is-totally-separated ℕ∞₂
                                        → ¬¬ WLPO
ℕ∞₂-is-not-totally-separated-in-general ts nwlpo = c
 where
  g : ¬ ((p : ℕ∞₂ → 𝟚) → p ∞₀ ＝ p ∞₁)
  g = contrapositive ts ∞₀-and-∞₁-different

  c : 𝟘
  c = g (𝟚-indistinguishability nwlpo)

\end{code}

We can generalize this as follows, without using ℕ∞.

From an arbitrary type X and distinguished element a : X, we construct
a new type Y, which will fail to be totally separated unless the point
a is weakly isolated. The idea is to "explode" the point a into two
different copies, which cannot be distinguished unless the point a is
weakly isolated, and keep all the other original points unchanged.

Recall that the notion of weakly isolated point is defined as follows.

\begin{code}

_ : {X : 𝓤 ̇ } (x : X) → is-weakly-isolated x ＝ ∀ x' → is-decidable (x' ≠ x)
_ = λ x → refl

module general-example
        (fe : FunExt)
        (𝓤 : Universe)
        (X : 𝓤 ̇ )
        (a : X)
       where

 Y : 𝓤 ̇
 Y = Σ x ꞉ X , (x ＝ a → 𝟚)

 e : 𝟚 → X → Y
 e n x = (x , λ p → n)

 a₀ : Y
 a₀ = e ₀ a

 a₁ : Y
 a₁ = e ₁ a

 Proposition : a₀ ≠ a₁
 Proposition r = zero-is-not-one zero-is-one
  where
   P : Y → 𝓤 ̇
   P (x , f) = Σ q ꞉ x ＝ a , f q ＝ ₁

   observation₀ : P a₀ ＝ (a ＝ a) × (₀ ＝ ₁)
   observation₀ = refl

   observation₁ : P a₁ ＝ (a ＝ a) × (₁ ＝ ₁)
   observation₁ = refl

   t : P a₁ → P a₀
   t = transport P (r ⁻¹)

   p₁ : P a₁
   p₁ = refl , refl

   p₀ : P a₀
   p₀ = t p₁

   zero-is-one : ₀ ＝ ₁
   zero-is-one = pr₂ p₀

\end{code}

Points different from the point a are mapped to the same point by the
two embeddings e₀ and e₁:

\begin{code}

 Lemma : (x : X) → x ≠ a → e ₀ x ＝ e ₁ x
 Lemma x φ = ap (λ - → (x , -)) claim
  where
   claim : (λ p → ₀) ＝ (λ p → ₁)
   claim = dfunext (fe 𝓤 𝓤₀) (λ p → 𝟘-elim (φ p))

\end{code}

The following theorem shows that, because not every type X has
decidable equality, the points a₀,a₁ of Y cannot necessarily be
distinguished by maps into the discrete set 𝟚. To get the desired
conclusion, it is enough to consider X = (ℕ → 𝟚), which is
¬¬-separated, in the sense that ¬¬ (x ＝ y) → x ＝ y, assuming
extensionality. (Cf. the module DiscreteAndSeparated.)

\begin{code}

 Theorem : (Σ g ꞉ (Y → 𝟚), g a₀ ≠ g a₁) → is-weakly-isolated a
 Theorem (g , d) x = 𝟚-equality-cases' (claim₀' x) (claim₁' x)
  where
   f : X → 𝟚
   f x = g (e ₀ x) ⊕ g (e ₁ x)

   claim₀ : f a ＝ ₁
   claim₀ = Lemma[b≠c→b⊕c＝₁] d

   claim₁ : (x : X) → x ≠ a → f x ＝ ₀
   claim₁ x φ = Lemma[b＝c→b⊕c＝₀] (ap g (Lemma x φ))

   claim₀' : (x : X) → f x ＝ ₀ → x ≠ a
   claim₀' x p r = 𝟘-elim (equal-₀-different-from-₁ fact claim₀)
    where
     fact : f a ＝ ₀
     fact = ap f (r ⁻¹) ∙ p

   claim₁' : (x : X) → f x ＝ ₁ → ¬ (x ≠ a)
   claim₁' x p φ = 𝟘-elim (equal-₀-different-from-₁ fact p)
    where
     fact : f x ＝ ₀
     fact = claim₁ x φ

 Theorem' : ¬ is-weakly-isolated a → (g : Y → 𝟚) → g a₀ ＝ g a₁
 Theorem' nw g = 𝟚-is-¬¬-separated
                  (g a₀)
                  (g a₁)
                  (contrapositive
                    (λ (d : g a₀ ≠ g a₁) → Theorem (g , d))
                    nw)

\end{code}

Added 10th October 2024.

Examples. As discussed in the module DecidabilityOfNonContinuity, we
have that ¬ WPO is a weak continuity principle. Using this, we get
explicit examples of non weakly isolated points. Notice that, because
excluded middle is consistent, it is consistent that every point of
every set is (weakly) isolated. So we can't give any example of a
non-isolated point or weakly-non-isolated of a set without assuming an
anticlassical principle such as ¬ WLPO.

\begin{code}

open import UF.Equiv

∞-is-weakly-isolated-gives-WLPO : is-weakly-isolated ∞ → WLPO
∞-is-weakly-isolated-gives-WLPO w u =
 Cases (w u)
  (λ (a : u ≠ ∞) → inr a)
  (λ (b : ¬ (u ≠ ∞)) → inl (ℕ∞-is-¬¬-separated fe₀ u ∞ b))

open import TypeTopology.Cantor

weakly-isolated-point-of-Cantor-gives-WLPO : (α : Cantor)
                                           → is-weakly-isolated α
                                           → WLPO
weakly-isolated-point-of-Cantor-gives-WLPO = III
 where
  I : is-weakly-isolated 𝟏 → WLPO-traditional
  I i α = Cases (i α)
           (λ (d : α ≠ 𝟏)
                 → inr (λ (a : (n : ℕ) → α n ＝ ₁) → d (dfunext fe₀ a)))
           (λ (e : ¬ (α ≠ 𝟏))
                 → inl (λ n → happly (Cantor-is-¬¬-separated fe₀ α 𝟏 e) n))

  II : (α : Cantor) → is-weakly-isolated α → WLPO-traditional
  II α i = I b
   where
    a : is-weakly-isolated (⌜ Cantor-swap-≃ fe₀ α 𝟏 ⌝ α)
    a = equivs-preserve-weak-isolatedness (Cantor-swap-≃ fe₀ α 𝟏) α i

    b : is-weakly-isolated 𝟏
    b = transport is-weakly-isolated (Cantor-swap-swaps fe₀ α 𝟏) a

  III : (α : Cantor) → is-weakly-isolated α → WLPO
  III α i = WLPO-traditional-gives-WLPO fe₀ (II α i)

module examples-of-non-weakly-isolated-points (nwlpo : ¬ WLPO) where

 ∞-is-not-weakly-isolated : ¬ is-weakly-isolated ∞
 ∞-is-not-weakly-isolated =
  contrapositive ∞-is-weakly-isolated-gives-WLPO nwlpo

 ∞-is-not-isolated : ¬ is-isolated ∞
 ∞-is-not-isolated =
  contrapositive
   (isolated-gives-weakly-isolated ∞)
   ∞-is-not-weakly-isolated

 Cantor-has-no-weakly-isolated-points : (α : Cantor) → ¬ is-weakly-isolated α
 Cantor-has-no-weakly-isolated-points α =
  contrapositive (weakly-isolated-point-of-Cantor-gives-WLPO α) nwlpo

 Cantor-has-no-isolated-points : (α : Cantor) → ¬ is-isolated α
 Cantor-has-no-isolated-points α =
  contrapositive
   (isolated-gives-weakly-isolated α)
   (Cantor-has-no-weakly-isolated-points α)

 Cantor-is-perfect : is-perfect Cantor
 Cantor-is-perfect (α , i) = Cantor-has-no-isolated-points α i

\end{code}

Using the terminology of the module imported below, the above amount
to the following.

\begin{code}

open import TypeTopology.LimitPoints

∞-is-a-limit-point⁺-of-ℕ∞ : is-limit-point⁺ ∞
∞-is-a-limit-point⁺-of-ℕ∞ = ∞-is-weakly-isolated-gives-WLPO

every-point-of-the-Cantor-type-is-a-limit-point⁺
 : (α : Cantor) → is-limit-point⁺ α
every-point-of-the-Cantor-type-is-a-limit-point⁺ =
 weakly-isolated-point-of-Cantor-gives-WLPO

\end{code}

Added 4th Feb 2025. A characterization of equality in ℕ∞₂.

\begin{code}

open import UF.SigmaIdentity
open import UF.EquivalenceExamples

ℕ∞₂-equality : funext 𝓤₀ 𝓤₀
             → (u@(x , f) v@(y , g) : ℕ∞₂)
             → (u ＝ v) ≃ (Σ p ꞉ x ＝ y , f ∘ (p ∙_) ∼ g)
ℕ∞₂-equality fe u@(x , f) v@(y , g) = IV
 where
  i : ((x , f) (y , g) : ℕ∞₂) → x ＝ y → 𝓤₀ ̇
  i (x , f) (y , g) p = f ∘ (p ∙'_) ∼ g

  ρ : (u : ℕ∞₂) → i u u refl
  ρ u p = refl

  open Σ-identity renaming (canonical-map to κ)

  c : {x : ℕ∞} (s t : x ＝ ∞ → 𝟚) → s ＝ t → s ∼ t
  c = κ i ρ

  I : {x : ℕ∞} (s t : x ＝ ∞ → 𝟚) → c s t ∼ happly' s t
  I s t refl = refl

  θ : {x : ℕ∞} (s t : x ＝ ∞ → 𝟚) → is-equiv (c s t)
  θ s t = equiv-closed-under-∼ (happly' s t) (c s t) (fe s t) (I s t)

  II : (u ＝ v) ≃ (Σ p ꞉ x ＝ y , f ∘ (p ∙'_) ∼ g)
  II = characterization-of-＝ (i , ρ , θ) (x , f) (y , g)

  III : (p : x ＝ y) → (f ∘ (p ∙'_) ∼ g) ≃ (f ∘ (p ∙_) ∼ g)
  III p = transport-≃
           (λ - → (f ∘ (- ∘ _) ∼ g))
           (dfunext fe (∙-agrees-with-∙' p))

  IV = (u ＝ v)                         ≃⟨ II ⟩
       (Σ p ꞉ x ＝ y , f ∘ (p ∙'_) ∼ g) ≃⟨ Σ-cong III ⟩
       (Σ p ꞉ x ＝ y , f ∘ (p ∙_) ∼ g)  ■

\end{code}
