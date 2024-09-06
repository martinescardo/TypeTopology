Martin Escardo. March 2022.

When is Σ discrete and/or totally separated? More generally what do
the isolated points of Σ look like?

This is, in particular, needed in order to prove things about compact
ordinals.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module TypeTopology.SigmaDiscreteAndTotallySeparated where

open import CoNaturals.Type
open import MLTT.Spartan
open import NotionsOfDecidability.Complemented
open import Taboos.WLPO
open import TypeTopology.CompactTypes
open import TypeTopology.FailureOfTotalSeparatedness
open import TypeTopology.GenericConvergentSequenceCompactness
open import TypeTopology.PropTychonoff
open import TypeTopology.TotallySeparated
open import UF.Base
open import UF.DiscreteAndSeparated
open import UF.Equiv
open import UF.FunExt
open import UF.Sets
open import UF.Subsingletons

Σ-isolated : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {x : X} {y : Y x}
           → is-isolated x
           → is-isolated y
           → is-isolated (x , y)
Σ-isolated {𝓤} {𝓥} {X} {Y} {x} {y} d e (x' , y') = g (d x')
 where
  g : is-decidable (x ＝ x') → is-decidable ((x , y) ＝ (x' , y'))
  g (inl p) = f (e' y')
   where
    e' : is-isolated (transport Y p y)
    e' = equivs-preserve-isolatedness (transport Y p) (transports-are-equivs p) y e

    f : is-decidable (transport Y p y ＝ y') → is-decidable ((x , y) ＝ (x' , y'))
    f (inl q) = inl (to-Σ-＝ (p , q))
    f (inr ψ) = inr c
     where
      c : x , y ＝ x' , y' → 𝟘
      c r = ψ q
       where
        p' : x ＝ x'
        p' = ap pr₁ r

        q' : transport Y p' y ＝ y'
        q' = from-Σ-＝' r

        s : p' ＝ p
        s = isolated-is-h-isolated x d p' p

        q : transport Y p y ＝ y'
        q = transport (λ - → transport Y - y ＝ y') s q'

  g (inr φ) = inr (λ q → φ (ap pr₁ q))

Σ-is-discrete : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
              → is-discrete X
              → ((x : X) → is-discrete (Y x))
              → is-discrete (Σ Y)
Σ-is-discrete d e (x , y) (x' , y') = Σ-isolated (d x) (e x y) (x' , y')

×-isolated : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {x : X} {y : Y}
           → is-isolated x
           → is-isolated y
           → is-isolated (x , y)
×-isolated d e = Σ-isolated d e

×-is-discrete : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
              → is-discrete X
              → is-discrete Y
              → is-discrete (X × Y)
×-is-discrete d e = Σ-is-discrete d (λ _ → e)

×-isolated-left : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {x : X} {y : Y}
                → is-isolated (x , y)
                → is-isolated x
×-isolated-left {𝓤} {𝓥} {X} {Y} {x} {y} i x' = γ (i (x' , y))
 where
  γ : is-decidable ((x , y) ＝ (x' , y)) → is-decidable (x ＝ x')
  γ (inl p) = inl (ap pr₁ p)
  γ (inr ν) = inr (λ (q : x ＝ x') → ν (to-×-＝ q refl))

×-isolated-right : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {x : X} {y : Y}
                 → is-isolated (x , y)
                 → is-isolated y
×-isolated-right {𝓤} {𝓥} {X} {Y} {x} {y} i y' = γ (i (x , y'))
 where
  γ : is-decidable ((x , y) ＝ (x , y')) → is-decidable (y ＝ y')
  γ (inl p) = inl (ap pr₂ p)
  γ (inr ν) = inr (λ (q : y ＝ y') → ν (to-×-＝ refl q))


Σ-isolated-right : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {x : X} {y : Y x}
                 → is-set X
                 → is-isolated {_} {Σ Y} (x , y)
                 → is-isolated y
Σ-isolated-right {𝓤} {𝓥} {X} {Y} {x} {y} s i y' = γ (i (x , y'))
 where
  γ : is-decidable ((x , y) ＝ (x , y')) → is-decidable (y ＝ y')
  γ (inl p) =
    inl (y                               ＝⟨ refl ⟩
         transport Y refl y              ＝⟨ ap (λ - → transport Y - y) (s refl (ap pr₁ p)) ⟩
         transport Y (ap pr₁ p) y        ＝⟨ (transport-ap Y pr₁ p)⁻¹ ⟩
         transport (λ - → Y (pr₁ -)) p y ＝⟨ apd pr₂ p ⟩
         y'                              ∎)
  γ (inr ν) = inr (contrapositive (ap (x ,_)) ν)

\end{code}

Here we need a compactness assumption:

\begin{code}

Σ-isolated-left : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {x : X} {y : Y x}
                → ((x : X) → is-Compact (Y x))
                → is-isolated (x , y)
                → is-isolated x
Σ-isolated-left {𝓤} {𝓥} {X} {Y} {x} {y} σ i x' = γ δ
 where
   A : (y' : Y x') → 𝓤 ⊔ 𝓥 ̇
   A y' = (x , y) ＝ (x' , y')

   d : is-complemented A
   d y' = i (x' , y')

   δ : is-decidable (Σ A)
   δ = σ x' A d

   γ : is-decidable (Σ A) → is-decidable (x ＝ x')
   γ (inl (y' , p)) = inl (ap pr₁ p)
   γ (inr ν)        = inr (λ (q : x ＝ x') → ν (transport Y q y , to-Σ-＝ (q , refl)))

\end{code}

TODO. Is this assumption absolutely necessary?

Recall that we proved the following:

\begin{code}

private
 recall : (X : 𝓤 ̇ ) (Y : X → 𝓥 ̇ )
        → is-discrete X
        → ((x : X) → is-totally-separated (Y x))
        → is-totally-separated (Σ Y)
 recall = Σ-is-totally-separated-if-index-type-is-discrete

\end{code}

We now derive a constructive taboo from the assumption that totally
separated types are closed under Σ.

\begin{code}

module _ (fe : FunExt) where

 private
  fe₀ = fe 𝓤₀ 𝓤₀

 Σ-totally-separated-taboo :

      (∀ {𝓤} {𝓥} (X : 𝓤 ̇ ) (Y : X → 𝓥 ̇ )
          → is-totally-separated X
          → ((x : X) → is-totally-separated (Y x))
          → is-totally-separated (Σ Y))
    →
      ¬¬ WLPO

 Σ-totally-separated-taboo τ =
   ℕ∞₂-is-not-totally-separated-in-general fe₀
    (τ ℕ∞ (λ u → u ＝ ∞ → 𝟚)
       (ℕ∞-is-totally-separated fe₀)
          (λ u → Π-is-totally-separated fe₀ (λ _ → 𝟚-is-totally-separated)))
\end{code}

Remark. ¬ WLPO is equivalent to a continuity principle that is
compatible with constructive mathematics and with MLTT. Therefore its
negatation is not provable. See

  Constructive decidability of classical continuity.
  Mathematical Structures in Computer Science
  Volume 25 , Special Issue 7: Computing with Infinite Data:
  Topological and Logical Foundations Part 1 , October 2015 , pp. 1578-1589
  https://doi.org/10.1017/S096012951300042X

Even compact totally separated types fail to be closed under Σ:

\begin{code}

 Σ-totally-separated-stronger-taboo :

      (∀ {𝓤} {𝓥} (X : 𝓤 ̇ ) (Y : X → 𝓥 ̇ )
          → is-compact X
          → ((x : X) → is-compact (Y x))
          → is-totally-separated X
          → ((x : X) → is-totally-separated (Y x))
          → is-totally-separated (Σ Y))
   →
      ¬¬ WLPO

 Σ-totally-separated-stronger-taboo τ =
   ℕ∞₂-is-not-totally-separated-in-general fe₀
    (τ ℕ∞ (λ u → u ＝ ∞ → 𝟚)
       (ℕ∞-compact fe₀)
       (λ _ → compact∙-types-are-compact
               (prop-tychonoff fe (ℕ∞-is-set fe₀) (λ _ → 𝟚-is-compact∙)))
       (ℕ∞-is-totally-separated fe₀)
          (λ u → Π-is-totally-separated fe₀ (λ _ → 𝟚-is-totally-separated)))

\end{code}

Added 20th December 2023. Sums are not closed under total
separatedness in general, as discussed above, but we have the
following useful special case.

\begin{code}

open import Notation.CanonicalMap hiding ([_])

Σ-indexed-by-ℕ∞-is-totally-separated-if-family-at-∞-is-prop
  : funext 𝓤₀ 𝓤₀
  → (A : ℕ∞ → 𝓥 ̇ )
  → ((u : ℕ∞) → is-totally-separated (A u))
  → is-prop (A ∞)
  → is-totally-separated (Σ A)
Σ-indexed-by-ℕ∞-is-totally-separated-if-family-at-∞-is-prop
 fe₀ A A-is-ts A∞-is-prop {u , a} {v , b} ϕ = IV
 where
  have-ϕ : (p : Σ A → 𝟚) → p (u , a) ＝ p (v , b)
  have-ϕ = ϕ

  ϕ₁ : (q : ℕ∞ → 𝟚) → q u ＝ q v
  ϕ₁ q = ϕ (λ (w , _) → q w)

  I : u ＝ v
  I = ℕ∞-is-totally-separated fe₀ ϕ₁

  a' : A v
  a' = transport A I a

  a-fact : (u , a) ＝[ Σ A ] (v , a')
  a-fact = to-Σ-＝ (I , refl)

  II : (r : A v → 𝟚) → r a' ＝ r b
  II r = II₃
   where
    II₀ : (n : ℕ) → v ＝ ι n → r a' ＝ r b
    II₀ n refl = e
     where
      p' : ((w , c) : Σ A) → is-decidable (ι n ＝ w) → 𝟚
      p' (w , c) (inl e) = r (transport⁻¹ A e c)
      p' (w , c) (inr ν) = ₀ -- Anything works here.

      p'-property : ((w , c) : Σ A) (d d' : is-decidable (ι n ＝ w))
                  → p' (w , c) d ＝ p' (w , c) d'
      p'-property (w , c) (inl e) (inl e')  = ap (λ - → r (transport⁻¹ A - c))
                                                 (ℕ∞-is-set fe₀ e e')
      p'-property (w , c) (inl e) (inr ν')  = 𝟘-elim (ν' e)
      p'-property (w , c) (inr ν) (inl e')  = 𝟘-elim (ν e')
      p'-property (w , c) (inr ν) (inr ν')  = refl

      p : Σ A → 𝟚
      p (w , c) = p' (w , c) (finite-isolated fe₀ n w)

      e = r a'                   ＝⟨ refl ⟩
          p' (v , a') (inl refl) ＝⟨ e₀ ⟩
          p (v , a')             ＝⟨ e₁ ⟩
          p (u , a)              ＝⟨ e₂ ⟩
          p (v , b)              ＝⟨ e₃ ⟩
          p' (v , b) (inl refl)  ＝⟨ refl ⟩
          r b                    ∎
           where
            e₀ = p'-property (v , a') (inl refl) (finite-isolated fe₀ n v)
            e₁ = ap p (a-fact ⁻¹)
            e₂ = ϕ p
            e₃ = (p'-property (v , b) (inl refl) (finite-isolated fe₀ n v))⁻¹

    II₁ : v ＝ ∞ → r a' ＝ r b
    II₁ refl = ap r (A∞-is-prop a' b)

    II₂ : ¬ (r a' ≠ r b)
    II₂ ν = II∞ (not-finite-is-∞ fe₀ IIₙ)
     where
      IIₙ : (n : ℕ) → v ≠ ι n
      IIₙ n = contrapositive (II₀ n) ν

      II∞ : v ≠ ∞
      II∞ = contrapositive II₁ ν

    II₃ : r a' ＝ r b
    II₃ = 𝟚-is-¬¬-separated (r a') (r b) II₂

  III : a' ＝ b
  III = A-is-ts v II

  IV : (u , a) ＝[ Σ A ] (v , b)
  IV = to-Σ-＝ (I , III)

\end{code}

Added 21st December 2023. A modification of the above proof gives the
following.

\begin{code}

open import UF.Embeddings

subtype-is-totally-separated''
  : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
    (f : X → Y)
  → is-totally-separated Y
  → left-cancellable f
  → is-totally-separated X
subtype-is-totally-separated'' {𝓤} {𝓥} {X} {Y} f Y-is-ts f-lc {x} {x'} ϕ = II
 where
  have-ϕ : (p : X → 𝟚) → p x ＝ p x'
  have-ϕ = ϕ

  ϕ₁ : (q : Y → 𝟚) → q (f x) ＝ q (f x')
  ϕ₁ q = ϕ (q ∘ f)

  I : f x ＝ f x'
  I = Y-is-ts ϕ₁

  II : x ＝ x'
  II = f-lc I

subtype-is-totally-separated'
  : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
    (f : X → Y)
  → is-totally-separated Y
  → is-embedding f
  → is-totally-separated X
subtype-is-totally-separated' f Y-is-ts f-is-emb =
 subtype-is-totally-separated'' f Y-is-ts (embeddings-are-lc f f-is-emb)

subtype-is-totally-separated
  : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ )
  → is-totally-separated X
  → ((x : X) → is-prop (A x))
  → is-totally-separated (Σ A)
subtype-is-totally-separated A X-is-ts A-is-prop-valued =
 subtype-is-totally-separated'' pr₁ X-is-ts (pr₁-lc (λ {x} → A-is-prop-valued x))

\end{code}
