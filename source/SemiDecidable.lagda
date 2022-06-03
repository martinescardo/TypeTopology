Tom de Jong, October–November 2021.

Refactored: January 2022.

We investigate constructive taboos surrounding semidecidability.

In particular, we try to investigate what form of countable choice, if any, is
necessary for the semidecidable propositions to be closed under countable joins.

Before we do that, we relate Bishop's Limited Principle of Omniscience (LPO),
Markov's Principle (MP) and strong Brouwer-Kripke Schema (BKS⁺) to properties of
the type of semidecidable propositions. (See Appendix II of
CantorSchroederBernstein.lagda for more on BKS⁺.)

Moreover, we formalize [Theorem 3, EK2017] which says that the semidecidable
propositions are closed under Σ if and only if a certain weak choice principle,
called Escardo Knapp Choice here, holds.

The table of contents is as follows:

∗ Part I   Basic definitions and properties of semidecidablity (structure)

∗ Part II  Formulating LPO, MP and BKS⁺ in terms of the type of semidecidability
           propositions having/being a particular subtype.

∗ Part III LPO, MP, BKS⁺ and closure properties of the type of semidecidable
           propositions.

∗ Part IV  Escardo Knapp Choice, the dominance axiom and closure under Σ
           (Formalization of some results by Escardó and Knapp [EK2017])

∗ Part V   (Subsingleton) Countable choice and closure under (subsingleton)
           countable joins

A summary of implications between weak choice principles and closure conditions
of semidecidable propositions can be found at the end of Part V, just before the
two closing remarks.

NB: is-semidecidable is called isRosolini in [EK2017], because the term
semidecidability is already used in computability theory.

References
──────────

[Bauer2006] Andrej Bauer, "First Steps in Synthetic Computability Theory",
            Electronic Notes in Theoretical Computer Science, volume 155,
            pages 5–13, 2006. Proceedings of the 21st Annual Conference on
            Mathematical Foundations of Programming Semantics (MFPS XXI).
            doi:10.1016/j.entcs.2005.11.049

[EK2017] Martín H. Escardó and Cory M. Knapp, "Partial Elements and Recursion
         via Dominances in Univalent Type Theory", In Valentin Goranko and Mads
         Dam, editors, 26th EACSL Annual Conference on Computer Science Logic
         (CSL 2017), volume 82 of Leibniz International Proceedings in
         Informatics (LIPIcs), pages 21:1–21:16.
         Schloss Dagstuhl–Leibniz-Zentrum für Informatik, 2017.
         doi:10.4230/LIPIcs.CSL.2017.21.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import SpartanMLTT

open import UF-Equiv
open import UF-Equiv-FunExt
open import UF-EquivalenceExamples
open import UF-FunExt
open import UF-ImageAndSurjection
open import UF-Miscelanea
open import UF-Powerset
open import UF-PropTrunc
open import UF-Subsingletons
open import UF-Subsingletons-FunExt
open import UF-UniverseEmbedding

open import BinaryNaturals hiding (_+_)
open import CompactTypes
open import DecidableAndDetachable
open import DiscreteAndSeparated
open import Fin-Properties
open import NaturalsOrder
open import OrderNotation
open import Two-Properties

\end{code}

Part I: Basic definitions and properties of semidecidablity (structure).

\begin{code}

module SemiDecidable
        (fe  : Fun-Ext)
        (pe  : Prop-Ext)
        (pt  : propositional-truncations-exist)
       where

fe' : FunExt
fe' 𝓤 𝓥 = fe

open PropositionalTruncation pt
open ImageAndSurjection pt

semidecidability-structure : (X : 𝓤 ̇  ) → 𝓤 ̇
semidecidability-structure X = Σ α ꞉ (ℕ → 𝟚) , X ≃ (∃ n ꞉ ℕ , α n ≡ ₁)

semidecidability-structure' : (𝓣 : Universe) (X : 𝓤 ̇  ) → 𝓣 ⁺ ⊔ 𝓤 ̇
semidecidability-structure' 𝓣 X = Σ A ꞉ (ℕ → Ω 𝓣) , is-complemented-subset A
                                                  × (X ≃ (∃ n ꞉ ℕ , n ∈ A))

is-semidecidable : (X : 𝓤 ̇  ) → 𝓤 ̇
is-semidecidable X = ∥ semidecidability-structure X ∥

is-semidecidable' : (𝓣 : Universe) (X : 𝓤 ̇  ) → 𝓣 ⁺ ⊔ 𝓤 ̇
is-semidecidable' 𝓣 X = ∥ semidecidability-structure' 𝓣 X ∥

\end{code}

The difference between property and structure will be important in our
discussions regarding countable choice, as we will see later.

We proceed by showing that the primed versions are equivalent to the unprimed
versions above.

\begin{code}

semidecidability-structure-≃ : {𝓣 : Universe} {X : 𝓤 ̇  }
                             → semidecidability-structure X
                             ≃ semidecidability-structure' 𝓣 X
semidecidability-structure-≃ {𝓤} {𝓣} {X} =
 (Σ α ꞉ (ℕ → 𝟚) , X ≃ (∃ n ꞉ ℕ , α n ≡ ₁))                           ≃⟨ I   ⟩
 (Σ 𝔸 ꞉ (Σ A ꞉ (ℕ → Ω 𝓣) , is-complemented-subset A)
                          , X ≃ (∃ n ꞉ ℕ , ⌜ χ ⌝ 𝔸 n ≡ ₁))           ≃⟨ II  ⟩
 (Σ A ꞉ (ℕ → Ω 𝓣) , Σ δ ꞉ is-complemented-subset A
                         , X ≃ (∃ n ꞉ ℕ , ⌜ χ ⌝ (A , δ) n ≡ ₁))      ≃⟨ III ⟩
 (Σ A ꞉ (ℕ → Ω 𝓣) , is-complemented-subset A × (X ≃ (∃ n ꞉ ℕ , n ∈ A))) ■
  where
   χ : (Σ A ꞉ (ℕ → Ω 𝓣) , is-complemented-subset A) ≃ (ℕ → 𝟚)
   χ = ≃-sym (𝟚-classifies-decidable-subsets fe fe pe)
   I   = ≃-sym (Σ-change-of-variable (λ α → X ≃ (∃ n ꞉ ℕ , α n ≡ ₁))
          ⌜ χ ⌝ (⌜⌝-is-equiv χ))
   II  = Σ-assoc
   III = Σ-cong (λ A → Σ-cong
                (λ δ → ≃-cong-right fe' (∥∥-cong pt (Σ-cong (λ n → κ A δ n)))))
    where
     κ : (A : ℕ → Ω 𝓣) (δ : is-complemented-subset A) (n : ℕ )
       → (⌜ χ ⌝ (A , δ) n ≡ ₁) ≃ (A n holds)
     κ A δ n = logically-equivalent-props-are-equivalent
                    𝟚-is-set (holds-is-prop (A n))
                    (lr-implication (pr₂ lemma)) (rl-implication (pr₂ lemma))
      where
       lemma : ((⌜ χ ⌝ (A , δ) n ≡ ₀) ⇔ ¬ (n ∈ A))
             × ((⌜ χ ⌝ (A , δ) n ≡ ₁) ⇔   (n ∈ A))
       lemma = 𝟚-classifies-decidable-subsets-values fe fe pe A δ n

is-semidecidable-≃ : {𝓣 : Universe} {X : 𝓤 ̇  }
                   → is-semidecidable X ≃ is-semidecidable' 𝓣 X
is-semidecidable-≃ = ∥∥-cong pt (semidecidability-structure-≃)

\end{code}

We proceed by proving some basic lemmas about semidecidability (structure).

\begin{code}

prop-if-semidecidability-structure : {X : 𝓤 ̇  }
                                   → semidecidability-structure X → is-prop X
prop-if-semidecidability-structure σ = equiv-to-prop (pr₂ σ) ∥∥-is-prop

prop-if-semidecidable : {X : 𝓤 ̇  } → is-semidecidable X → is-prop X
prop-if-semidecidable = ∥∥-rec (being-prop-is-prop fe)
                               prop-if-semidecidability-structure

being-semidecidable-is-prop : {X : 𝓤 ̇  } → is-prop (is-semidecidable X)
being-semidecidable-is-prop = ∥∥-is-prop

semidecidability-structure-cong : {X : 𝓤 ̇  } {Y : 𝓥 ̇  }
                                → X ≃ Y
                                → semidecidability-structure X
                                → semidecidability-structure Y
semidecidability-structure-cong {𝓤} {𝓥} f (ϕ , e) = (ϕ , (≃-sym f ● e))

is-semidecidable-cong : {X : 𝓤 ̇  } {Y : 𝓥 ̇  }
                      → X ≃ Y
                      → is-semidecidable X
                      → is-semidecidable Y
is-semidecidable-cong = ∥∥-functor ∘ semidecidability-structure-cong

\end{code}

The types 𝟘 and 𝟙 are semidecidable and hence, so are all singletons, empty
types and all decidable propositions.

\begin{code}

𝟘-has-semidecidability-structure' : semidecidability-structure (𝟘 {𝓤₀})
𝟘-has-semidecidability-structure' = ϕ , e
 where
  ϕ : ℕ → 𝟚
  ϕ _ = ₀
  ϕ-is-not-₁-anywhere : ¬ (∃ n ꞉ ℕ , ϕ n ≡ ₁)
  ϕ-is-not-₁-anywhere = forall₀-implies-not-exists₁ pt ϕ (λ _ → refl)
  e : 𝟘 ≃ (∃ n ꞉ ℕ , ϕ n ≡ ₁)
  e = ≃-sym (lr-implication negations-are-equiv-to-𝟘 ϕ-is-not-₁-anywhere)

𝟘-has-semidecidability-structure : semidecidability-structure (𝟘 {𝓤})
𝟘-has-semidecidability-structure {𝓤} =
 semidecidability-structure-cong one-𝟘-only 𝟘-has-semidecidability-structure'

𝟘-is-semidecidable : is-semidecidable (𝟘 {𝓤})
𝟘-is-semidecidable = ∣ 𝟘-has-semidecidability-structure ∣

empty-types-have-semidecidability-structure : {X : 𝓤 ̇  } → is-empty X
                                            → semidecidability-structure X
empty-types-have-semidecidability-structure e =
 semidecidability-structure-cong
  (≃-sym (lr-implication negations-are-equiv-to-𝟘 e))
  𝟘-has-semidecidability-structure

empty-types-are-semidecidable : {X : 𝓤 ̇  } → is-empty X → is-semidecidable X
empty-types-are-semidecidable e =
 ∣ empty-types-have-semidecidability-structure e ∣

𝟙-has-semidecidability-structure : semidecidability-structure (𝟙 {𝓤})
𝟙-has-semidecidability-structure = ϕ , e
 where
  ϕ : ℕ → 𝟚
  ϕ _ = ₁
  w : ∃ n ꞉ ℕ , ϕ n ≡ ₁
  w = ∣ 0 , refl ∣
  e : 𝟙 ≃ (∃ n ꞉ ℕ , ϕ n ≡ ₁)
  e = ≃-sym (lr-implication singletons-are-equiv-to-𝟙
              (w , (∥∥-is-prop w)))

𝟙-is-semidecidable : is-semidecidable (𝟙 {𝓤})
𝟙-is-semidecidable = ∣ 𝟙-has-semidecidability-structure ∣

singletons-have-semidecidability-structure : {X : 𝓤 ̇  } → is-singleton X
                                           → semidecidability-structure X
singletons-have-semidecidability-structure {𝓤} i =
 semidecidability-structure-cong
  (≃-sym (lr-implication singletons-are-equiv-to-𝟙 i))
  (𝟙-has-semidecidability-structure {𝓤})

singletons-are-semidecidable : {X : 𝓤 ̇  } → is-singleton X → is-semidecidable X
singletons-are-semidecidable i = ∣ singletons-have-semidecidability-structure i ∣

decidable-props-are-semidecidable : {X : 𝓤 ̇  }
                                  → is-prop X
                                  → decidable X
                                  → is-semidecidable X
decidable-props-are-semidecidable i (inl  x) = singletons-are-semidecidable (x , i x)
decidable-props-are-semidecidable i (inr nx) = empty-types-are-semidecidable nx

\end{code}

If X and its negation ¬ X are semidecidable propositions, then so decidability
of X becomes semidecidable.

\begin{code}

decidability-is-semidecidable : (X : 𝓤 ̇  )
                              → is-semidecidable X
                              → is-semidecidable (¬ X)
                              → is-semidecidable (decidable X)
decidability-is-semidecidable X σ τ = ∥∥-rec being-semidecidable-is-prop ψ τ
 where
  ψ : semidecidability-structure (¬ X) → is-semidecidable (decidable X)
  ψ (β , g) = ∥∥-functor ϕ σ
   where
    ϕ : semidecidability-structure X → semidecidability-structure (decidable X)
    ϕ (α , f) = γ , h
     where
      γ : ℕ → 𝟚
      γ n = max𝟚 (α n) (β n)
      X-is-prop : is-prop X
      X-is-prop = prop-if-semidecidable σ
      dec-of-X-is-prop : is-prop (decidable X)
      dec-of-X-is-prop = decidability-of-prop-is-prop fe X-is-prop
      h : decidable X ≃ (∃ n ꞉ ℕ , γ n ≡ ₁)
      h = logically-equivalent-props-are-equivalent
           dec-of-X-is-prop ∥∥-is-prop u v
       where
        u : decidable X → ∃ n ꞉ ℕ , γ n ≡ ₁
        u (inl  x) = ∥∥-functor
                      (λ (n , b) → n , max𝟚-lemma-converse (inl b))
                      (⌜ f ⌝ x)
        u (inr nx) = ∥∥-functor
                      (λ (n , b) → n , max𝟚-lemma-converse (inr b))
                      (⌜ g ⌝ nx)
        v : ∃ n ꞉ ℕ , γ n ≡ ₁ → decidable X
        v = ∥∥-rec dec-of-X-is-prop ν
         where
          ν : (Σ n ꞉ ℕ , γ n ≡ ₁) → decidable X
          ν (n , p) = cases (λ a → inl (⌜ f ⌝⁻¹ ∣ n , a ∣))
                            (λ b → inr (⌜ g ⌝⁻¹ ∣ n , b ∣))
                            (max𝟚-lemma p)

\end{code}

The following pairing lemma comes in useful, especially when we are given a
ℕ-indexed family Xₙ where each Xₙ is equiped with semidecidability structure.

\begin{code}

semidecidability-pairing-lemma : {X : 𝓤 ̇  }
  → (Σ Ψ ꞉ (ℕ → ℕ → 𝟚) , X ≃ (∃ n ꞉ ℕ , Σ m ꞉ ℕ , Ψ n m ≡ ₁))
  ≃ semidecidability-structure X
semidecidability-pairing-lemma {𝓤} {X} =
 (Σ Ψ ꞉ (ℕ → ℕ → 𝟚) , X ≃ (∃ n ꞉ ℕ , Σ m ꞉ ℕ , Ψ n m            ≡ ₁)) ≃⟨ I   ⟩
 (Σ Ψ ꞉ (ℕ × ℕ → 𝟚) , X ≃ (∃ n ꞉ ℕ , Σ m ꞉ ℕ , Ψ (n , m)        ≡ ₁)) ≃⟨ II  ⟩
 (Σ ϕ ꞉ (ℕ → 𝟚)     , X ≃ (∃ n ꞉ ℕ , Σ m ꞉ ℕ , ⌜ e₂ ⌝ ϕ (n , m) ≡ ₁)) ≃⟨ III ⟩
 (Σ ϕ ꞉ (ℕ → 𝟚)     , X ≃ (∃ k ꞉ ℕ           , ϕ k              ≡ ₁)) ■
 where
  e₁ : (ℕ × ℕ → 𝟚) ≃ (ℕ → ℕ → 𝟚)
  e₁ = curry-uncurry fe'
  e₂ : (ℕ → 𝟚) ≃ (ℕ × ℕ → 𝟚)
  e₂ = →cong'' fe fe (≃-sym pairing)
  I  = ≃-sym (Σ-change-of-variable (λ Ψ → X ≃ (∃ n ꞉ ℕ , Σ m ꞉ ℕ , Ψ n m ≡ ₁))
                                   ⌜ e₁ ⌝ (⌜⌝-is-equiv e₁))
  II = ≃-sym (Σ-change-of-variable
               (λ Ψ → X ≃ (∃ n ꞉ ℕ , Σ m ꞉ ℕ , Ψ (n , m) ≡ ₁))
               ⌜ e₂ ⌝ (⌜⌝-is-equiv e₂))
  III = Σ-cong (λ ϕ → ≃-cong-right fe' (∥∥-cong pt (lemma ϕ)))
   where
    ρ : ℕ × ℕ ≃ ℕ
    ρ = pairing
    σ : (ℕ → 𝟚) → (ℕ × ℕ → 𝟚)
    σ = ⌜ e₂ ⌝
    lemma : (ϕ : ℕ → 𝟚)
          → (Σ n ꞉ ℕ , Σ m ꞉ ℕ , σ ϕ (n , m) ≡ ₁) ≃ (Σ k ꞉ ℕ , ϕ k ≡ ₁)
    lemma ϕ = (Σ n ꞉ ℕ , Σ m ꞉ ℕ , σ ϕ (n , m)           ≡ ₁) ≃⟨ ≃-sym Σ-assoc ⟩
              (Σ p ꞉ ℕ × ℕ       , σ ϕ p                 ≡ ₁) ≃⟨ ⦅i⦆           ⟩
              (Σ k ꞉ ℕ           , σ ϕ (⌜ ρ ⌝⁻¹ k)       ≡ ₁) ≃⟨ ≃-refl _      ⟩
              (Σ k ꞉ ℕ           , ϕ (⌜ ρ ⌝ (⌜ ρ ⌝⁻¹ k)) ≡ ₁) ≃⟨ ⦅ii⦆          ⟩
              (Σ k ꞉ ℕ           , ϕ k                   ≡ ₁) ■
     where
      ⦅i⦆  = ≃-sym (Σ-change-of-variable (λ p → σ ϕ p ≡ ₁)
                     ⌜ ρ ⌝⁻¹ (⌜⌝⁻¹-is-equiv ρ))
      ⦅ii⦆ = Σ-cong (λ k → ≡-cong-l (ϕ ((⌜ ρ ⌝ ∘ ⌜ ρ ⌝⁻¹) k)) ₁
                           (ap ϕ (≃-sym-is-rinv ρ k)))

\end{code}

Part II: We will shortly study Bishop's Limited Principle of Omniscience (LPO),
Markov's Principle (MP) and strong Brouwer-Kripke schema (BKS⁺) and their
relations to semidecidability.

Before we do so we consider various subtypes of Ω, namely

∗ Ωᵈᵉᶜ - the type of decidable propositions, which is equivalent to 𝟚
∗ Ω¬¬  - the type of ¬¬-stable propositions
∗ Ωˢᵈ  - the type of semidecidable propositions

In short, we have the following diagram

𝟚 ≃ Ωᵈᵉᶜ ⟶ Ωˢᵈ --→ Ω¬¬
               ↘   ↓
                   Ω

where
∗ the dotted map exists (and makes the triangle commute) if and only if Markov's
  Principle holds;
∗ all maps (including the dotted one, if it exists) are embeddings;
∗ the embedding Ωᵈᵉᶜ ⟶ Ωˢᵈ is an equivalence if and only if LPO holds;
∗ the embedding Ωˢᵈ  ⟶ Ω   is an equivalence if and only if BKS⁺ holds.

\begin{code}

open import UF-Embeddings

open import CanonicalMapNotation

Ω¬¬-to-Ω : Ω¬¬ 𝓤 → Ω 𝓤
Ω¬¬-to-Ω = pr₁

instance
 canonical-map-Ω¬¬-to-Ω : Canonical-Map (Ω¬¬ 𝓤) (Ω 𝓤)
 ι {{canonical-map-Ω¬¬-to-Ω}} = Ω¬¬-to-Ω

Ω¬¬-to-Ω-is-embedding : is-embedding (canonical-map (Ω¬¬ 𝓤) (Ω 𝓤))
Ω¬¬-to-Ω-is-embedding =
 pr₁-is-embedding (λ P → being-¬¬-stable-is-prop fe (holds-is-prop P))

Ωˢᵈ : (𝓤 : Universe) → 𝓤 ⁺ ̇
Ωˢᵈ 𝓤 = Σ X ꞉ 𝓤 ̇  , is-semidecidable X

Ωˢᵈ-to-Ω : Ωˢᵈ 𝓤 → Ω 𝓤
Ωˢᵈ-to-Ω (X , σ) = (X , prop-if-semidecidable σ)

instance
 canonical-map-Ωˢᵈ-to-Ω : Canonical-Map (Ωˢᵈ 𝓤) (Ω 𝓤)
 ι {{canonical-map-Ωˢᵈ-to-Ω}} = Ωˢᵈ-to-Ω

Ωˢᵈ-to-Ω-left-cancellable : left-cancellable (canonical-map (Ωˢᵈ 𝓤) (Ω 𝓤))
Ωˢᵈ-to-Ω-left-cancellable {𝓤} {(X , σ)} {(Y , τ)} e =
 to-subtype-≡ (λ _ → being-semidecidable-is-prop) (ap pr₁ e)

Ωˢᵈ-to-Ω-is-embedding : is-embedding (canonical-map (Ωˢᵈ 𝓤) (Ω 𝓤))
Ωˢᵈ-to-Ω-is-embedding = lc-maps-into-sets-are-embeddings ι
                         Ωˢᵈ-to-Ω-left-cancellable (Ω-is-set fe pe)

Ωˢᵈ-is-set : is-set (Ωˢᵈ 𝓤)
Ωˢᵈ-is-set = subtypes-of-sets-are-sets ι Ωˢᵈ-to-Ω-left-cancellable
              (Ω-is-set fe pe)

Ωᵈᵉᶜ : (𝓤 : Universe) → 𝓤 ⁺ ̇
Ωᵈᵉᶜ 𝓤 = Σ P ꞉ Ω 𝓤 , decidable (P holds)

Ωᵈᵉᶜ-to-Ωˢᵈ : Ωᵈᵉᶜ 𝓤 → Ωˢᵈ 𝓤
Ωᵈᵉᶜ-to-Ωˢᵈ ((P , i) , d) = (P , decidable-props-are-semidecidable i d)

instance
 canonical-map-Ωᵈᵉᶜ-to-Ωˢᵈ : Canonical-Map (Ωᵈᵉᶜ 𝓤) (Ωˢᵈ 𝓤)
 ι {{canonical-map-Ωᵈᵉᶜ-to-Ωˢᵈ}} = Ωᵈᵉᶜ-to-Ωˢᵈ

Ωᵈᵉᶜ-to-Ωˢᵈ-left-cancellable : left-cancellable (canonical-map (Ωᵈᵉᶜ 𝓤) (Ωˢᵈ 𝓤))
Ωᵈᵉᶜ-to-Ωˢᵈ-left-cancellable {𝓤} {(X , _)} {(Y , _)} e =
 to-subtype-≡ (λ (P , i) → decidability-of-prop-is-prop fe i)
              (Ω-extensionality fe pe
               (idtofun (X holds) (Y holds) (ap pr₁ e))
               (idtofun (Y holds) (X holds) (ap pr₁ (e ⁻¹))))

Ωᵈᵉᶜ-to-Ωˢᵈ-is-embedding : is-embedding (canonical-map (Ωᵈᵉᶜ 𝓤) (Ωˢᵈ 𝓤))
Ωᵈᵉᶜ-to-Ωˢᵈ-is-embedding = lc-maps-into-sets-are-embeddings ι
                            Ωᵈᵉᶜ-to-Ωˢᵈ-left-cancellable
                            Ωˢᵈ-is-set

𝟚-to-Ωˢᵈ : 𝟚 → Ωˢᵈ 𝓤
𝟚-to-Ωˢᵈ = Ωᵈᵉᶜ-to-Ωˢᵈ ∘ ⌜ 𝟚-is-the-type-of-decidable-propositions fe pe ⌝

instance
 canonical-map-𝟚-to-Ωˢᵈ : Canonical-Map 𝟚 (Ωˢᵈ 𝓤)
 ι {{canonical-map-𝟚-to-Ωˢᵈ}} = 𝟚-to-Ωˢᵈ

𝟚-to-Ωˢᵈ-is-embedding : is-embedding (canonical-map 𝟚 (Ωˢᵈ 𝓤))
𝟚-to-Ωˢᵈ-is-embedding {𝓤} =
 ∘-is-embedding (equivs-are-embeddings ⌜ χ ⌝ (⌜⌝-is-equiv χ))
                Ωᵈᵉᶜ-to-Ωˢᵈ-is-embedding
  where
   χ : 𝟚 ≃ Ωᵈᵉᶜ 𝓤
   χ = 𝟚-is-the-type-of-decidable-propositions fe pe

\end{code}

Part II(a): LPO and semidecidability

\begin{code}

LPO : 𝓤₀ ̇
LPO = (α : ℕ → 𝟚) → decidable (∃ n ꞉ ℕ , α n ≡ ₁)

LPO-is-prop : is-prop LPO
LPO-is-prop = Π-is-prop fe (λ α → decidability-of-prop-is-prop fe ∥∥-is-prop)

LPO' : (𝓤 : Universe) → 𝓤 ⁺ ̇
LPO' 𝓤 = (X : 𝓤 ̇  ) → is-semidecidable X → decidable X

LPO'-is-prop : is-prop (LPO' 𝓤)
LPO'-is-prop = Π₂-is-prop fe (λ X σ → decidability-of-prop-is-prop fe
                                       (prop-if-semidecidable σ))

\end{code}

LPO is a more traditional way of formulating the Limited Principle of
Omniscience, but LPO' is perhaps conceptually clearer and is the formulation
that is most convenient for us here. The two formulations are equivalent as
proved below.

\begin{code}

LPO-equivalence : LPO ≃ LPO' 𝓤
LPO-equivalence {𝓤} = logically-equivalent-props-are-equivalent
                       LPO-is-prop LPO'-is-prop f g
 where
  f : LPO → LPO' 𝓤
  f lpo X σ = ∥∥-rec (decidability-of-prop-is-prop fe
                       (prop-if-semidecidable σ)) γ σ
   where
    γ : semidecidability-structure X → decidable X
    γ (α , e) = decidable-cong (≃-sym e) (lpo α)
  g : LPO' 𝓤 → LPO
  g τ α = decidable-cong (Lift-≃ 𝓤 X) (τ X' σ')
   where
    X : 𝓤₀ ̇
    X = ∃ n ꞉ ℕ , α n ≡ ₁
    X' : 𝓤 ̇
    X' = Lift 𝓤 X
    σ' : is-semidecidable X'
    σ' = is-semidecidable-cong (≃-sym (Lift-≃ 𝓤 X)) ∣ α , ≃-refl X ∣

\end{code}

By the above equivalence it follows that having LPO' in any universe is
equivalent to having LPO' in any other universe.

\begin{code}

LPO-across-universes : {𝓤 𝓥 : Universe} → LPO' 𝓤 ≃ LPO' 𝓥
LPO-across-universes {𝓤} {𝓥} = LPO' 𝓤  ≃⟨ ≃-sym LPO-equivalence ⟩
                               LPO     ≃⟨ LPO-equivalence       ⟩
                               LPO' 𝓥  ■

\end{code}

Finally, we characterize LPO as saying exactly that the canonical map from 𝟚 to
the type of semidecidable propositions, Ωˢᵈ, is an equivalence.

\begin{code}

LPO-in-terms-of-Ωᵈᵉᶜ-and-Ωˢᵈ : LPO' 𝓤 ≃ is-equiv (canonical-map (Ωᵈᵉᶜ 𝓤) (Ωˢᵈ 𝓤))
LPO-in-terms-of-Ωᵈᵉᶜ-and-Ωˢᵈ {𝓤} = logically-equivalent-props-are-equivalent
                                    LPO'-is-prop
                                    (being-equiv-is-prop fe' ι)
                                    ⦅⇒⦆ ⦅⇐⦆
   where
    ⦅⇒⦆ : LPO' 𝓤 → is-equiv ι
    ⦅⇒⦆ lpo = surjective-embeddings-are-equivs ι Ωᵈᵉᶜ-to-Ωˢᵈ-is-embedding
              (λ (X , σ) → ∣ ((X , prop-if-semidecidable σ) , lpo X σ)
                           , to-subtype-≡ (λ _ → being-semidecidable-is-prop)
                              refl ∣)
    ⦅⇐⦆ : is-equiv ι → LPO' 𝓤
    ⦅⇐⦆ ι-is-equiv X σ = transport decidable e Y-is-dec
     where
      β : Ωˢᵈ 𝓤 → Ωᵈᵉᶜ 𝓤
      β = inverse ι ι-is-equiv
      Y : 𝓤 ̇
      Y = pr₁ (β (X , σ)) holds
      Y-is-dec : decidable Y
      Y-is-dec = pr₂ (β (X , σ))
      e : Y ≡ X
      e = ap pr₁ (inverses-are-sections ι ι-is-equiv (X , σ))

LPO-in-terms-of-𝟚-and-Ωˢᵈ : LPO ≃ is-equiv (canonical-map 𝟚 (Ωˢᵈ 𝓤))
LPO-in-terms-of-𝟚-and-Ωˢᵈ {𝓤} = logically-equivalent-props-are-equivalent
                                 LPO-is-prop (being-equiv-is-prop fe' ι)
                                 ⦅⇒⦆ ⦅⇐⦆
 where
  χ : 𝟚 ≃ Ωᵈᵉᶜ 𝓤
  χ = 𝟚-is-the-type-of-decidable-propositions fe pe
  ⦅⇒⦆ : LPO → is-equiv ι
  ⦅⇒⦆ lpo = ∘-is-equiv (⌜⌝-is-equiv χ)
            (⌜ LPO-in-terms-of-Ωᵈᵉᶜ-and-Ωˢᵈ ⌝ (⌜ LPO-equivalence ⌝ lpo))
  ⦅⇐⦆ : is-equiv ι → LPO
  ⦅⇐⦆ i = ⌜ LPO-equivalence ⌝⁻¹
          (⌜ LPO-in-terms-of-Ωᵈᵉᶜ-and-Ωˢᵈ ⌝⁻¹
            (≃-2-out-of-3-right (⌜⌝-is-equiv χ) i))

\end{code}

Part II(b): Markov's Principle and semidecidability.

As with LPO, we introduce two formulations of Markov's Principle and prove their
equivalence.

\begin{code}

MP : 𝓤₀ ̇
MP = (α : ℕ → 𝟚) → ¬¬-stable (∃ n ꞉ ℕ , α n ≡ ₁)

MP-is-prop : is-prop MP
MP-is-prop = Π₂-is-prop fe (λ α h → ∥∥-is-prop)

MP' : (𝓤 : Universe) → 𝓤 ⁺ ̇
MP' 𝓤 = ((X : 𝓤 ̇  ) → is-semidecidable X → ¬¬-stable X)

MP'-is-prop : is-prop (MP' 𝓤)
MP'-is-prop = Π₃-is-prop fe (λ X σ h → prop-if-semidecidable σ)

MP-equivalence : MP ≃ MP' 𝓤
MP-equivalence {𝓤} = logically-equivalent-props-are-equivalent
                           MP-is-prop MP'-is-prop f g
 where
  f : MP → MP' 𝓤
  f mp X σ nnX = ∥∥-rec (prop-if-semidecidable σ) γ σ
   where
    γ : semidecidability-structure X → X
    γ (α , e) = ⌜ e ⌝⁻¹ (mp α (¬¬-functor ⌜ e ⌝ nnX))
  g : MP' 𝓤 → MP
  g τ α = ¬¬-stable-≃ (Lift-≃ 𝓤 X) (τ X' σ')
   where
    X : 𝓤₀ ̇
    X = ∃ n ꞉ ℕ , α n ≡ ₁
    X' : 𝓤 ̇
    X' = Lift 𝓤 X
    σ' : is-semidecidable X'
    σ' = is-semidecidable-cong (≃-sym (Lift-≃ 𝓤 X)) ∣ α , ≃-refl X ∣

MP-across-universes : {𝓤 𝓥 : Universe} → MP' 𝓤 ≃ MP' 𝓥
MP-across-universes {𝓤} {𝓥} = MP' 𝓤  ≃⟨ ≃-sym MP-equivalence ⟩
                               MP    ≃⟨ MP-equivalence       ⟩
                               MP' 𝓥 ■

\end{code}

The below is a formalization of [Proposition 3.17, Bauer2006], specifically of
the equivalence of items (i) and (iii) there.

\begin{code}

MP-in-terms-of-Ω¬¬-and-Ω : MP ≃ (Σ e ꞉ (Ωˢᵈ 𝓤 → Ω¬¬ 𝓤) , Ωˢᵈ-to-Ω ∼ Ω¬¬-to-Ω ∘ e)
MP-in-terms-of-Ω¬¬-and-Ω {𝓤} = MP-equivalence ● claim
 where
  factors-is-prop : is-prop (Σ e ꞉ (Ωˢᵈ 𝓤 → Ω¬¬ 𝓤) , Ωˢᵈ-to-Ω ∼ Ω¬¬-to-Ω ∘ e)
  factors-is-prop (e , p) (e' , p') =
   to-subtype-≡ (λ f → Π-is-prop fe (λ _ → Ω-is-set fe pe))
                (dfunext fe γ)
    where
     γ : e ∼ e'
     γ (X , σ) = to-subtype-≡
                  (λ P → being-¬¬-stable-is-prop fe (holds-is-prop P))
                  (pr₁ (e (X , σ))       ≡⟨ refl           ⟩
                   Ω¬¬-to-Ω (e (X , σ))  ≡⟨ (p (X , σ)) ⁻¹ ⟩
                   Ωˢᵈ-to-Ω (X , σ)      ≡⟨ p' (X , σ)     ⟩
                   Ω¬¬-to-Ω (e' (X , σ)) ≡⟨ refl           ⟩
                   pr₁ (e' (X , σ))      ∎)
  claim : MP' 𝓤 ≃ (Σ e ꞉ (Ωˢᵈ 𝓤 → Ω¬¬ 𝓤) , Ωˢᵈ-to-Ω ∼ Ω¬¬-to-Ω ∘ e)
  claim = logically-equivalent-props-are-equivalent MP'-is-prop factors-is-prop
           ⦅⇒⦆ ⦅⇐⦆
   where
    ⦅⇒⦆ : MP' 𝓤 → (Σ e ꞉ (Ωˢᵈ 𝓤 → Ω¬¬ 𝓤) , Ωˢᵈ-to-Ω ∼ Ω¬¬-to-Ω ∘ e)
    ⦅⇒⦆ mp = e , (λ (X , σ) → refl)
     where
      e : Ωˢᵈ 𝓤 → Ω¬¬ 𝓤
      e (X , σ) = (X , prop-if-semidecidable σ) , mp X σ
    ⦅⇐⦆ : (Σ e ꞉ (Ωˢᵈ 𝓤 → Ω¬¬ 𝓤) , Ωˢᵈ-to-Ω ∼ Ω¬¬-to-Ω ∘ e) → MP' 𝓤
    ⦅⇐⦆ (e , p) X σ = transport ¬¬-stable (eq ⁻¹) Y-¬¬-stable
     where
      Y : 𝓤 ̇
      Y = pr₁ (e (X , σ)) holds
      Y-¬¬-stable : ¬¬-stable Y
      Y-¬¬-stable = pr₂ (e (X , σ))
      eq : X ≡ Y
      eq = ap pr₁ (p (X , σ))

\end{code}

NB: The map e : Ωˢᵈ 𝓤 → Ω¬¬ 𝓤 in the type of MP-in-terms-of-Ω¬¬-and-Ω is an
    embedding, because embeddings have the 2-out-of-3 property and
    Ωˢᵈ-to-Ω ∼ Ω¬¬-to-Ω ∘ e is required to hold.

\begin{code}

Ωˢᵈ-to-Ω¬¬-is-embedding : (e : Ωˢᵈ 𝓤 → Ω¬¬ 𝓤)
                        → Ωˢᵈ-to-Ω ∼ Ω¬¬-to-Ω ∘ e
                        → is-embedding e
Ωˢᵈ-to-Ω¬¬-is-embedding e h = factor-is-embedding e Ω¬¬-to-Ω
                               (embedding-closed-under-∼ Ωˢᵈ-to-Ω (Ω¬¬-to-Ω ∘ e)
                                 Ωˢᵈ-to-Ω-is-embedding (λ p → (h p) ⁻¹))
                               Ω¬¬-to-Ω-is-embedding

\end{code}

Part II(c): Strong Brouwer-Kripke Schema (BKS⁺) and semidecidability.

\begin{code}

BKS⁺ : (𝓤 : Universe) → (𝓤 ⁺) ̇
BKS⁺ 𝓤 = (X : 𝓤 ̇  ) → is-prop X → is-semidecidable X

BKS⁺-is-prop : is-prop (BKS⁺ 𝓤)
BKS⁺-is-prop = Π₂-is-prop fe (λ _ _ → being-semidecidable-is-prop)

BKS⁺-in-terms-of-Ωˢᵈ-and-Ω : BKS⁺ 𝓤 ≃ is-equiv (canonical-map (Ωˢᵈ 𝓤) (Ω 𝓤))
BKS⁺-in-terms-of-Ωˢᵈ-and-Ω {𝓤} =
 logically-equivalent-props-are-equivalent
  BKS⁺-is-prop (being-equiv-is-prop fe' ι) ⦅⇒⦆ ⦅⇐⦆
   where
    ⦅⇒⦆ : BKS⁺ 𝓤 → is-equiv ι
    ⦅⇒⦆ bks = surjective-embeddings-are-equivs ι Ωˢᵈ-to-Ω-is-embedding
              (λ P → ∣ (P holds , bks (P holds) (holds-is-prop P))
                     , to-subtype-≡ (λ _ → being-prop-is-prop fe) refl ∣)
    ⦅⇐⦆ : is-equiv ι → BKS⁺ 𝓤
    ⦅⇐⦆ ι-is-equiv X X-is-prop = transport is-semidecidable e Y-is-semidecidable
     where
      β : Ω 𝓤 → Ωˢᵈ 𝓤
      β = inverse ι ι-is-equiv
      Y : 𝓤 ̇
      Y = pr₁ (β (X , X-is-prop))
      Y-is-semidecidable : is-semidecidable Y
      Y-is-semidecidable = pr₂ (β (X , X-is-prop))
      e : Y ≡ X
      e = ap pr₁ (inverses-are-sections ι ι-is-equiv (X , X-is-prop))

\end{code}

We close part II with some remarks relating BKS⁺ and LPO with excluded middle;
and BKS⁺ and propositional resizing.

NB: We use the formulation LPO' as it is more convient for our purposes, but
recall that we proved LPO' equivalent to LPO.

Somewhat similar results can be found in CantorSchroederBernstein.lagda, where
the observation that BKS⁺ → MP → EM is attributed to Moschovakis. As LPO → MP,
it follows that BKS⁺ → LPO → EM, but we give a direct proof of the latter here.
In particular, we prove EM ≃ BKS⁺ × LPO directly, although this follows from the
fact that EM ≃ BKS⁺ × MP.

\begin{code}

LPO→MP : LPO → MP
LPO→MP lpo α = ¬¬-stable-if-decidable (∃ n ꞉ ℕ , α n ≡ ₁) (lpo α)

open import UF-ExcludedMiddle

BKS⁺→LPO→EM : BKS⁺ 𝓤 → LPO' 𝓤 → EM 𝓤
BKS⁺→LPO→EM {𝓤} bks lpo X X-is-prop = lpo X (bks X X-is-prop)

EM→BKS⁺ : EM 𝓤 → BKS⁺ 𝓤
EM→BKS⁺ {𝓤} em X X-is-prop =
 decidable-props-are-semidecidable X-is-prop (em X X-is-prop)

EM→LPO : EM 𝓤 → LPO' 𝓤
EM→LPO {𝓤} em X X-is-semidec = em X (prop-if-semidecidable X-is-semidec)

EM-is-conjunction-of-BKS⁺-and-LPO : EM 𝓤 ≃ BKS⁺ 𝓤 × LPO' 𝓤
EM-is-conjunction-of-BKS⁺-and-LPO =
 logically-equivalent-props-are-equivalent
  (EM-is-prop fe') (×-is-prop BKS⁺-is-prop LPO'-is-prop)
  (λ em → (EM→BKS⁺ em , EM→LPO em))
  (λ (bks , lpo) → BKS⁺→LPO→EM bks lpo)

open import UF-Size

BKS⁺-gives-Propositional-Resizing : BKS⁺ 𝓤
                                  → propositional-resizing 𝓤 𝓤₀
BKS⁺-gives-Propositional-Resizing bks X X-is-prop =
 ∥∥-rec (prop-being-small-is-prop (λ _ → pe) fe' X X-is-prop 𝓤₀) γ (bks X X-is-prop)
  where
   γ : semidecidability-structure X → X has-size 𝓤₀
   γ (α , e) = (∃ n ꞉ ℕ , α n ≡ ₁) , (≃-sym e)

\end{code}

Part III: The above taboos (LPO, MP, BKS⁺) and closure properties of the type
of semidecidable propositions.

In order, we consider:
 (1) Closure under negations
 (2) Closure under implications
 (3) Closure under all meets
 (4) Closure under all joins

The special case of countable choice is considered in Part V.

 (1) Closure under negations

\begin{code}

Semidecidable-Closed-Under-Negations : (𝓤 : Universe) → 𝓤 ⁺ ̇
Semidecidable-Closed-Under-Negations 𝓤 = (X : 𝓤 ̇  )
                                       → is-semidecidable X
                                       → is-semidecidable (¬ X)

semidecidable-negations-from-LPO : LPO' 𝓤
                                 → Semidecidable-Closed-Under-Negations 𝓤
semidecidable-negations-from-LPO lpo X σ =
 decidable-props-are-semidecidable (negations-are-props fe)
  (¬-preserves-decidability (lpo X σ))

\end{code}

 It turns out that in the presence of Markov's Principle, the above implication
 can be reversed. In other words, if we accept Markov's Principle, then LPO is
 equivalent to semidecidable propositions being closed under negation.

 I found the proof of this by inspecting the proof of [Theorem 3.21, Bauer2006].

\begin{code}

LPO-from-semidecidable-negations : MP' 𝓤
                                 → Semidecidable-Closed-Under-Negations 𝓤
                                 → LPO' 𝓤
LPO-from-semidecidable-negations mp h X σ = mp (decidable X) τ
                                             (all-types-are-¬¬-decidable X)
 where
  τ : is-semidecidable (decidable X)
  τ = decidability-is-semidecidable X σ (h X σ)

\end{code}

 (2) Closure under implications

 The situation for implications is very similar, which is not too surprising as
 negations are just particular implications.

\begin{code}

Semidecidable-Closed-Under-Implications : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥) ⁺ ̇
Semidecidable-Closed-Under-Implications 𝓤 𝓥 = (X : 𝓤 ̇  ) (Y : 𝓥 ̇  )
                                            → is-semidecidable X
                                            → is-semidecidable Y
                                            → is-semidecidable (X → Y)

semidecidable-implications-from-LPO : LPO' 𝓤
                                    → Semidecidable-Closed-Under-Implications
                                       𝓤 𝓤₀
semidecidable-implications-from-LPO lpo X Y σ τ =
 decidable-props-are-semidecidable
  (Π-is-prop fe (λ _ → prop-if-semidecidable τ))
  (→-preserves-decidability (lpo X σ) (⌜ LPO-across-universes ⌝ lpo Y τ))

LPO-from-semidecidable-implications : MP' 𝓤
                                    → Semidecidable-Closed-Under-Implications
                                       𝓤 𝓤₀
                                    → LPO' 𝓤
LPO-from-semidecidable-implications mp h =
 LPO-from-semidecidable-negations mp (λ X σ → h X 𝟘 σ 𝟘-is-semidecidable)

\end{code}

 (3) Closure under all meets

 For meets the situation is asymetric. We only managed to prove that if we have
 all meets, then we can deduce LPO; and if we have BKS⁺, then we have all meets.

\begin{code}

Semidecidable-All-Meets : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥) ⁺ ̇
Semidecidable-All-Meets 𝓤 𝓥 = (X : 𝓤 ̇  ) (Y : X → 𝓥 ̇  )
                            → ((x : X) → is-semidecidable (Y x))
                            → is-semidecidable (Π Y)

all-meets-implies-negations : Semidecidable-All-Meets 𝓤 𝓤₀
                            → Semidecidable-Closed-Under-Negations 𝓤
all-meets-implies-negations h X _ = h X (λ _ → 𝟘) (λ _ → 𝟘-is-semidecidable)

all-meets-implies-LPO : Semidecidable-All-Meets 𝓤 𝓤₀ → MP' 𝓤 → LPO' 𝓤
all-meets-implies-LPO h mp =
 LPO-from-semidecidable-negations mp (all-meets-implies-negations h)

BKS⁺-implies-all-meets : BKS⁺ (𝓤 ⊔ 𝓥)
                       → Semidecidable-All-Meets 𝓤 𝓥
BKS⁺-implies-all-meets bks X Y σ =
 bks (Π Y) (Π-is-prop fe (λ x → prop-if-semidecidable (σ x)))

\end{code}

 (4) Closure under all joins

 For joins the situation is nicely symmetric again (modulo universe
 parameters): we have closure under all joins if and only if BKS⁺ holds.

\begin{code}

Semidecidable-All-Joins : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥) ⁺ ̇
Semidecidable-All-Joins 𝓤 𝓥 = (X : 𝓤 ̇  ) (Y : X → 𝓥 ̇  )
                            → ((x : X) → is-semidecidable (Y x))
                            → is-semidecidable (∃ Y)

BKS⁺-implies-all-joins : BKS⁺ (𝓤 ⊔ 𝓥)
                       → Semidecidable-All-Joins 𝓤 𝓥
BKS⁺-implies-all-joins bks X Y σ = bks (∃ Y) ∥∥-is-prop

\end{code}

In fact, for the reverse implication, closure under subsingleton joins suffices.

\begin{code}

Semidecidable-Subsingleton-Joins : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥) ⁺ ̇
Semidecidable-Subsingleton-Joins 𝓤 𝓥 = (X : 𝓤 ̇  ) (Y : X → 𝓥 ̇  ) → is-prop X
                                     → ((x : X) → is-semidecidable (Y x))
                                     → is-semidecidable (∃ Y)

subsingleton-joins-implies-BKS⁺ : Semidecidable-Subsingleton-Joins 𝓤 𝓤₀
                                → BKS⁺ 𝓤
subsingleton-joins-implies-BKS⁺ σ X X-is-prop =
 is-semidecidable-cong γ (σ X (λ _ → 𝟙) X-is-prop (λ _ → 𝟙-is-semidecidable))
  where
   γ : ∥ X × 𝟙 ∥ ≃ X
   γ = ∥ X × 𝟙 ∥ ≃⟨ ∥∥-cong pt 𝟙-rneutral ⟩
       ∥ X ∥     ≃⟨ prop-is-equivalent-to-its-truncation X-is-prop ⟩
       X         ■

all-joins-implies-BKS⁺ : Semidecidable-All-Joins 𝓤 𝓤₀
                       → BKS⁺ 𝓤
all-joins-implies-BKS⁺ j =
 subsingleton-joins-implies-BKS⁺ (λ X Y X-is-prop σ → j X Y σ)

\end{code}

Part IV: Escardo Knapp Choice, the dominance axiom and closure under Σ

We start by formulating:
∗ that the semidecidable types are closed under Σ;
∗ Rosolini's dominance axiom of dependent closure under ×;

and prove their equivalence following [End of Section 2.5, EKC2017].

\end{code}

\begin{code}

Semidecidable-Closed-Under-Σ : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥) ⁺ ̇
Semidecidable-Closed-Under-Σ 𝓤 𝓥 = (P : 𝓤 ̇  )
                                 → is-semidecidable P
                                 → (Q : P → 𝓥 ̇  )
                                 → ((p : P) → is-semidecidable (Q p))
                                 → is-semidecidable (Σ Q)

Semidecidable-Dominance-Axiom : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥) ⁺ ̇
Semidecidable-Dominance-Axiom 𝓤 𝓥 = (P : 𝓤 ̇  )
                                  → is-semidecidable P
                                  → (Q : 𝓥 ̇  )
                                  → (P → is-semidecidable Q)
                                  → is-semidecidable (P × Q)

\end{code}

That the dominance axiom implies closure in Σ is proved next.

There is a very similar result and proof in Dominance.lagda (see
D3-and-D5'-give-D5), but we can't use it here, because we have more general
universe parameters (i.e. P : 𝓤, but Q : P → 𝓥) which are not possible in
Dominance.lagda as the dominance is given by a function d : 𝓣 → 𝓚 whose domain
is a *fixed* universe 𝓣.

\begin{code}

closure-under-Σ-if-dominance-axiom : Semidecidable-Dominance-Axiom 𝓤 (𝓤 ⊔ 𝓥)
                                   → Semidecidable-Closed-Under-Σ 𝓤 𝓥
closure-under-Σ-if-dominance-axiom {𝓤} {𝓥} D P ρ Q σ = τ
 where
  i : is-prop P
  i = prop-if-semidecidable ρ
  j : (p : P) → is-prop (Q p)
  j p = prop-if-semidecidable (σ p)
  Q' : 𝓤 ⊔ 𝓥 ̇
  Q' = Σ Q
  k : is-prop Q'
  k = Σ-is-prop i j
  e : (p : P) → Q' ≃ Q p
  e p = logically-equivalent-props-are-equivalent k (j p)
         (λ (p' , q) → transport Q (i p' p) q)
         (λ q → p , q)
  τ : is-semidecidable (Σ Q)
  τ = is-semidecidable-cong (Σ-cong e) (D P ρ Q' τ')
   where
    τ' : P → is-semidecidable Q'
    τ' p = is-semidecidable-cong (≃-sym (e p)) (σ p)

dominance-axiom-if-closure-under-Σ : Semidecidable-Closed-Under-Σ 𝓤 𝓥
                                   → Semidecidable-Dominance-Axiom 𝓤 𝓥
dominance-axiom-if-closure-under-Σ scus P ρ Q σ = scus P ρ (λ _ → Q) σ

\end{code}

Next, we introduce the choice principle from [EK2017] - we call it Escardo Knapp
Choice (EKC) - and formalize [Theorem 3, EK2017] which says that the
semidecidable types are closed under Σ if and only if Escardo Knapp Choice holds.

\begin{code}

Escardo-Knapp-Choice : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥) ⁺ ̇
Escardo-Knapp-Choice 𝓤 𝓥 = (P : 𝓤 ̇  ) (Q : 𝓥 ̇  )
                         → is-semidecidable P
                         → (P → is-semidecidable Q)
                         → ∥ (P → semidecidability-structure Q) ∥

semidecidable-closed-under-Σ-implies-EKC : Semidecidable-Closed-Under-Σ 𝓤 𝓥
                                         → Escardo-Knapp-Choice 𝓤 𝓥
semidecidable-closed-under-Σ-implies-EKC H P Q ρ σ = ∥∥-functor g τ
 where
  τ : is-semidecidable (P × Q)
  τ = H P ρ (λ _ → Q) σ
  f : P → (P × Q) ≃ Q
  f p = logically-equivalent-props-are-equivalent
         (×-is-prop (prop-if-semidecidable ρ) Q-is-prop) Q-is-prop
          pr₂ (λ q → p , q)
   where
    Q-is-prop : is-prop Q
    Q-is-prop = prop-if-semidecidable (σ p)
  g : semidecidability-structure (P × Q) → (P → semidecidability-structure Q)
  g ss p = semidecidability-structure-cong (f p) ss

\end{code}

The converse holds too, albeit with a longer proof.

(In the paper, some of the verifications - most importantly, the proof τ below -
are left to the reader, presumably because they are straightforward yet tedious.)

\begin{code}

EKC-implies-semidecidable-closed-under-Σ : Escardo-Knapp-Choice 𝓤 (𝓤 ⊔ 𝓥)
                                         → Semidecidable-Closed-Under-Σ 𝓤 𝓥
EKC-implies-semidecidable-closed-under-Σ {𝓤} {𝓥} ekc =
 closure-under-Σ-if-dominance-axiom γ
  where
   γ : Semidecidable-Dominance-Axiom 𝓤 (𝓤 ⊔ 𝓥)
   γ P ρ Q σ = ∥∥-rec being-semidecidable-is-prop r ρ
    where
     r : semidecidability-structure P → is-semidecidable (P × Q)
     r (α , e) = ∥∥-functor s (ekc P Q ρ σ)
      where
       to-P : (∃ n ꞉ ℕ , α n ≡ ₁) → P
       to-P = ⌜ e ⌝⁻¹
       s : (P → semidecidability-structure Q)
         → semidecidability-structure (P × Q)
       s σ⁺ = ⌜ semidecidability-pairing-lemma ⌝ τ
        where
         β : P → (ℕ → 𝟚)
         β p = pr₁ (σ⁺ p)
         φ : ℕ × ℕ → 𝓤₀ ̇
         φ (n , m) = Σ b ꞉ α n ≡ ₁ , β (to-P ∣ n , b ∣) m ≡ ₁
         φ-is-detachable : detachable φ
         φ-is-detachable (n , m) =
          decidable-closed-under-Σ 𝟚-is-set (𝟚-is-discrete (α n) ₁)
                                   (λ b → 𝟚-is-discrete (β (to-P ∣ n , b ∣) m) ₁)
         φ-is-prop-valued : (k : ℕ × ℕ) → is-prop (φ k)
         φ-is-prop-valued k = Σ-is-prop 𝟚-is-set (λ b → 𝟚-is-set)
         φ⁺ : ℕ × ℕ → Ω 𝓤₀
         φ⁺ k = φ k , φ-is-prop-valued k

         τ : Σ Ψ ꞉ (ℕ → ℕ → 𝟚) , P × Q ≃ (∃ n ꞉ ℕ , Σ m ꞉ ℕ ,  Ψ n m ≡ ₁)
         τ = ⌜ uncurry-lemma ⌝ τ'
          where
           uncurry-lemma :
              (Σ Ψ ꞉ (ℕ × ℕ → 𝟚) , P × Q ≃ (∃ n ꞉ ℕ , Σ m ꞉ ℕ ,  Ψ (n , m) ≡ ₁))
            ≃ (Σ Ψ ꞉ (ℕ → ℕ → 𝟚) , P × Q ≃ (∃ n ꞉ ℕ , Σ m ꞉ ℕ ,  Ψ n m ≡ ₁))
           uncurry-lemma = ≃-sym
                            (Σ-change-of-variable _ ⌜ μ ⌝⁻¹ (⌜⌝⁻¹-is-equiv μ))
            where
             μ : (ℕ × ℕ → 𝟚) ≃ (ℕ → ℕ → 𝟚)
             μ = curry-uncurry fe'

           τ' : (Σ Ψ ꞉ (ℕ × ℕ → 𝟚) , P × Q ≃ (∃ n ꞉ ℕ , Σ m ꞉ ℕ , Ψ (n , m) ≡ ₁))
           τ' = Ψ , (P × Q                              ≃⟨ I  ⟩
                    (∃ n ꞉ ℕ , Σ m ꞉ ℕ , φ (n , m))     ≃⟨ II ⟩
                    (∃ n ꞉ ℕ , Σ m ꞉ ℕ , Ψ (n , m) ≡ ₁) ■)
            where
             χ : (Σ A ꞉ (ℕ × ℕ → Ω 𝓤₀) , is-complemented-subset A) → (ℕ × ℕ → 𝟚)
             χ = ⌜ 𝟚-classifies-decidable-subsets fe fe pe ⌝⁻¹
             Ψ : ℕ × ℕ → 𝟚
             Ψ = χ (φ⁺ , φ-is-detachable)

             II = ∥∥-cong pt
                   (Σ-cong (λ n →
                     Σ-cong (λ m → logically-equivalent-props-are-equivalent
                                    (φ-is-prop-valued (n , m))
                                    𝟚-is-set
                                    (rl-implication (lemma n m))
                                    (lr-implication (lemma n m)))))
              where
               lemma : (n m : ℕ)
                     → χ (φ⁺ , φ-is-detachable) (n , m) ≡ ₁ ⇔ (n , m) ∈ φ⁺
               lemma n m = pr₂ (𝟚-classifies-decidable-subsets-values fe fe pe
                                 φ⁺ φ-is-detachable (n , m))
             I  = logically-equivalent-props-are-equivalent j ∥∥-is-prop f g
              where
               j : is-prop (P × Q)
               j = prop-criterion
                    (λ (p , q) → ×-is-prop (prop-if-semidecidable ρ)
                                           (prop-if-semidecidable (σ p)))
               e' : (p : P) → Q ≃ (∃ m ꞉ ℕ , β p m ≡ ₁)
               e' p = pr₂ (σ⁺ p)
               g : (∃ n ꞉ ℕ , Σ m ꞉ ℕ , φ (n , m)) → P × Q
               g = ∥∥-rec j g'
                where
                 g' : (Σ n ꞉ ℕ , Σ m ꞉ ℕ , φ (n , m)) → P × Q
                 g' (n , m , b , b') = p , ⌜ e' p ⌝⁻¹ ∣ m , b' ∣
                  where
                   p : P
                   p = to-P ∣ n , b ∣
               f : P × Q → ∃ n ꞉ ℕ , Σ m ꞉ ℕ , φ (n , m)
               f (p , q) = ∥∥-rec ∥∥-is-prop f' (⌜ e ⌝ p)
                where
                 f' : (Σ n ꞉ ℕ , α n ≡ ₁)
                    → ∃ n ꞉ ℕ , Σ m ꞉ ℕ , φ (n , m)
                 f' (n , b) = ∥∥-functor f'' (⌜ e' p' ⌝ q)
                  where
                   p' : P
                   p' = to-P ∣ n , b ∣
                   f'' : (Σ m ꞉ ℕ , β p' m ≡ ₁)
                       → Σ n ꞉ ℕ , Σ m ꞉ ℕ , φ (n , m)
                   f'' (m , b') = n , m , b , b'

\end{code}

Part V: (Subsingleton) Countable choice and closure under (subsingleton)
        countable joins

We investigate the connections between
(1) closure of semidecidable propositions under (particular kinds of) countable joins
and
(2) instances of countable choice.

Our findings are summarized at the end in a diagram of implications.


We start by proving that if we have a countable family Xₙ and each Xₙ has
semidecidability structure, then so does ∃ X.

The situation where Xₙ is only known to be semidecidable is rather different in
the absence of countable choice.

\begin{code}

∃-has-semidecidability-structure : (X : ℕ → 𝓤 ̇  )
                                 → (Π n ꞉ ℕ , semidecidability-structure (X n))
                                 → semidecidability-structure (∃ X)
∃-has-semidecidability-structure X σ = ⌜ semidecidability-pairing-lemma ⌝ γ
 where
  γ : Σ Ψ ꞉ (ℕ → ℕ → 𝟚) , ∃ X ≃ (∃ n ꞉ ℕ , Σ m ꞉ ℕ , Ψ n m ≡ ₁)
  γ = Ψ , e
   where
    lemma : (Π n ꞉ ℕ , semidecidability-structure (X n))
          → (Σ Ψ ꞉ (ℕ → ℕ → 𝟚) , Π n ꞉ ℕ , X n ≃ (∃ m ꞉ ℕ , Ψ n m ≡ ₁))
    lemma = ⌜ ΠΣ-distr-≃ ⌝
    Ψ : ℕ → ℕ → 𝟚
    Ψ = pr₁ (lemma σ)
    e = ∃ X                             ≃⟨ ∃-cong pt (pr₂ (lemma σ)) ⟩
        (∃ n ꞉ ℕ , ∃ m ꞉ ℕ , Ψ n m ≡ ₁) ≃⟨ outer-∃-inner-Σ pt        ⟩
        (∃ n ꞉ ℕ , Σ m ꞉ ℕ , Ψ n m ≡ ₁) ■

\end{code}

Next, we consider a particular instance of countable choice that we dub
Countable Semidecidable Choice (CSC) here and prove that it suffices to show
that the semidecidable propositions are closed under countable choice.

\begin{code}

Countable-Semidecidable-Choice : (𝓤 : Universe) → 𝓤 ⁺ ̇
Countable-Semidecidable-Choice 𝓤 =
   (X : ℕ → 𝓤 ̇  )
 → (Π n ꞉ ℕ , ∥ semidecidability-structure (X n) ∥)
 → ∥ Π n ꞉ ℕ , semidecidability-structure (X n) ∥

Semidecidable-Closed-Under-Countable-Joins : (𝓤 : Universe) → 𝓤 ⁺ ̇
Semidecidable-Closed-Under-Countable-Joins 𝓤 =
 (X : ℕ → 𝓤 ̇  ) → (Π n ꞉ ℕ , is-semidecidable (X n)) → is-semidecidable (∃ X)

CSC-implies-semidecidable-closed-under-countable-joins :
   Countable-Semidecidable-Choice 𝓤
 → Semidecidable-Closed-Under-Countable-Joins 𝓤
CSC-implies-semidecidable-closed-under-countable-joins {𝓤} csc X σ =
 ∥∥-functor (∃-has-semidecidability-structure X) (csc X σ)

\end{code}

We were not able to prove that the above implication can be reversed, i.e. that
CSC is necessary for the semidecidable propositions to be closed under countable
joins.


However, for a particular kind of families Xₙ we can find another (weak)
instance of countable choice and prove it equivalent to closure under these
particular kind of families.

The condition on the families Xₙ is that they are such that Σ X is a
proposition. In other words, there exists at most one n : ℕ such that Xₙ holds.

The closure condition is formulated precisely below as the weak choice principle
which we call Subsingleton Countable Semidecidable Choice (SCSC).

\begin{code}

Semidecidable-Closed-Under-Subsingleton-Countable-Joins : (𝓤 : Universe) → 𝓤 ⁺ ̇
Semidecidable-Closed-Under-Subsingleton-Countable-Joins 𝓤 =
   (X : ℕ → 𝓤 ̇  )
 → is-prop (Σ X)
 → (Π n ꞉ ℕ , is-semidecidable (X n))
 → is-semidecidable (Σ X)

Subsingleton-Countable-Semidecidable-Choice : (𝓤 : Universe) → 𝓤 ⁺ ̇
Subsingleton-Countable-Semidecidable-Choice 𝓤 =
   (X : ℕ → 𝓤 ̇  )
 → is-prop (Σ X)
 → (Π n ꞉ ℕ , ∥ semidecidability-structure (X n) ∥)
 → ∥ Π n ꞉ ℕ , semidecidability-structure (X n) ∥

SCSC-implies-semidecidable-closed-under-subsingleton-countable-joins :
   Subsingleton-Countable-Semidecidable-Choice 𝓤
 → Semidecidable-Closed-Under-Subsingleton-Countable-Joins 𝓤
SCSC-implies-semidecidable-closed-under-subsingleton-countable-joins
 scsc X ΣX-is-prop X-semidec = ∥∥-functor γ (scsc X ΣX-is-prop X-semidec)
  where
   γ : ((n : ℕ) → semidecidability-structure (X n))
     → semidecidability-structure (Σ X)
   γ σ = semidecidability-structure-cong
          e (∃-has-semidecidability-structure X σ)
    where
     e : ∃ X ≃ Σ X
     e = prop-is-equivalent-to-its-truncation ΣX-is-prop

\end{code}

The point of introducing the above choice principle and closure condition is
that we can prove the converse, formulated below:

\begin{code}

SCSC-if-semidecidable-closed-under-subsingleton-countable-joins :
   Semidecidable-Closed-Under-Subsingleton-Countable-Joins 𝓤
 → Subsingleton-Countable-Semidecidable-Choice 𝓤

\end{code}

The proof of the converse is somewhat involved and relies on the following
lemma, which looks like it reverses ∃-has-semidecidability-structure although we
assume semidecidability structure on Σ X rather than ∃ X here.

\begin{code}

semidecidability-structure-Σ : (X : ℕ → 𝓤 ̇  )
                             → (Π n ꞉ ℕ , is-prop (X n))
                             → semidecidability-structure (Σ X)
                             → (Π n ꞉ ℕ , semidecidability-structure (X n))

\end{code}

Before starting the formalized proof, we explain the proof strategy here.

(1) By assumption, we start with Ψ : ℕ → 𝟚 such that
      (Σ X) ≃ (∃ m ꞉ ℕ , Ψ m ≡ ₁).

(2) Using Ψ and the equivalence above, we construct P : ℕ → ℕ → 𝓤 such that for
    every n : ℕ we have
      (X n) ≃ (∃ k ꞉ ℕ , P n k), witnessed by f, say.

    Explicitly, P is given by
       P n m = (Σ p ꞉ (Ψ m ≡ ₁) , pr₁ (f ∣ m , p ∣) ≡ n).

(3) We prove that each P n is detachable and subsingleton-valued, i.e. that each
    P n is a decidable subset of ℕ.

This equips every X n with semidecidability structure.


In developing the proof, we found it easier to consider the more general setting
where we replace ℕ by any type X, the family X : ℕ → 𝓤 by a family Y : X → 𝓥 and
the predicate Ψ by a family A : X → 𝓦. The following "key-construction" and
lemma are steps (1) and (2) in the more general setting.

\begin{code}

private

 key-construction : {X : 𝓤 ̇  } {Y : X → 𝓥 ̇  } {A : X → 𝓦 ̇  }
                  → (∃ A → Σ Y)
                  → X → X → 𝓤 ⊔ 𝓦 ̇
 key-construction {𝓤} {𝓥} {𝓦} {X} {Y} {A} f x y =
   Σ a ꞉ A y , pr₁ (f ∣ y , a ∣) ≡ x

 key-construction-lemma : {X : 𝓤 ̇  } {Y : X → 𝓥 ̇  } {A : X → 𝓦 ̇  }
                        → ((x : X) → is-prop (Y x))
                        → (f : ∃ A ≃ Σ Y)
                        → (x : X) → Y x ≃ ∃ (key-construction ⌜ f ⌝ x)
 key-construction-lemma {𝓤} {𝓥} {𝓦} {X} {Y} {A} i f x =
  logically-equivalent-props-are-equivalent (i x) ∥∥-is-prop α β
   where
    β : ∃ (key-construction ⌜ f ⌝ x) → Y x
    β = ∥∥-rec (i x) γ
     where
      γ : Σ (key-construction ⌜ f ⌝ x) → Y x
      γ (y , a , e) = transport Y e (pr₂ (⌜ f ⌝ ∣ y , a ∣))
    α : Y x → ∃ (key-construction ⌜ f ⌝ x)
    α y = ∥∥-functor γ (⌜ f ⌝⁻¹ (x , y))
     where
      γ : Σ A → Σ (key-construction ⌜ f ⌝ x)
      γ (x' , a) = x' , (a , ap pr₁ e)
       where
        e = ⌜ f ⌝ ∣ x' , a ∣        ≡⟨ I  ⟩
            ⌜ f ⌝ (⌜ f ⌝⁻¹ (x , y)) ≡⟨ II ⟩
            (x , y)                 ∎
         where
          I  = ap ⌜ f ⌝ (∥∥-is-prop ∣ x' , a ∣ (⌜ f ⌝⁻¹ (x , y)))
          II = ≃-sym-is-rinv f (x , y)

\end{code}

Now, only step (3) remains and this is straightforward.

\begin{code}

semidecidability-structure-Σ  = γ
 where
  γ : (X : ℕ → 𝓤 ̇  )
    → (Π n ꞉ ℕ , is-prop (X n))
    → semidecidability-structure (Σ X)
    → (Π n ꞉ ℕ , semidecidability-structure (X n))
  γ X X-is-prop-valued (Ψ , e) n = ⌜ semidecidability-structure-≃ ⌝⁻¹ σ
   where
    σ : semidecidability-structure' 𝓤₀ (X n)
    σ = φ⁺ , φ-is-detachable ,
        (key-construction-lemma X-is-prop-valued (≃-sym e) n)
     where
      φ : ℕ → 𝓤₀ ̇
      φ = key-construction {𝓤₀} {_} {𝓤₀} {ℕ} {X} {λ m → Ψ m ≡ ₁} ⌜ e ⌝⁻¹ n
      φ-is-detachable : detachable φ
      φ-is-detachable m = decidable-closed-under-Σ 𝟚-is-set
                           (𝟚-is-discrete (Ψ m) ₁)
                           (λ (p : Ψ m ≡ ₁) → ℕ-is-discrete
                                               (pr₁ (⌜ e ⌝⁻¹ ∣ m , p ∣)) n)
      φ⁺ : ℕ → Ω 𝓤₀
      φ⁺ n = (φ n , φ-is-prop-valued n)
       where
        φ-is-prop-valued : (m : ℕ) → is-prop (φ m)
        φ-is-prop-valued m = Σ-is-prop 𝟚-is-set (λ _ → ℕ-is-set)


\end{code}

Finally, we prove, using semidecidability-structure-Σ, the desired converse:
i.e. that SCSC implies that the semidecidable propositions are closed under
subsingleton countable joins.

\begin{code}

SCSC-if-semidecidable-closed-under-subsingleton-countable-joins = γ
 where
  γ : Semidecidable-Closed-Under-Subsingleton-Countable-Joins 𝓤
    → Subsingleton-Countable-Semidecidable-Choice 𝓤
  γ h X i σ = ∥∥-functor (semidecidability-structure-Σ X j) (h X i σ)
   where
    j : (n : ℕ) → is-prop (X n)
    j n = prop-if-semidecidable (σ n)

\end{code}

Martín Escardó observed that for the semidecidable propositions closure under
subsingleton countable joins implies closure under Σ.

Hence, the choice principle SCSC implies the choice principle EKC.

Before formalizing Martín's observation, we prove a lemma that, given a
decidable subset A ⊆ ℕ allows us to find a decidable subset B ⊆ ℕ such that B
contains a single element precisely when A is inhabited. This is done by finding
the least such n ∈ A, if A happens to be inhabited.

\begin{code}

subset-with-only-the-least-witness : (A : ℕ → Ω 𝓤)
                                   → is-complemented-subset A
                                   → Σ B ꞉ (ℕ → Ω 𝓤) , is-complemented-subset B
                                                     × ((∃ n ꞉ ℕ , n ∈ A)
                                                     ≃ (Σ n ꞉ ℕ , n ∈ B))
subset-with-only-the-least-witness {𝓤} A A-is-decidable = B , B-is-decidable , γ
 where
  B : ℕ → Ω 𝓤
  B n = (n ∈ A × is-empty (Σ r ꞉ Fin' n , pr₁ r ∈ A))
      , (×-is-prop (∈-is-prop A n) (negations-are-props fe))
  B-is-decidable : is-complemented-subset B
  B-is-decidable n = ×-preserves-decidability (A-is-decidable n)
                                              (¬-preserves-decidability σ)
   where
    σ : decidable (Σ r ꞉ Fin' n , pr₁ r ∈ A)
    σ = Compact-closed-under-≃ (≃-Fin n) Fin-Compact (pr₁ ∘ A ∘ pr₁)
         (λ r → A-is-decidable (pr₁ r))
  ΣB-is-prop : is-prop (Σ n ꞉ ℕ , n ∈ B)
  ΣB-is-prop (n , a , min) (n' , a' , min') =
   to-subtype-≡ (∈-is-prop B) (κ (<-trichotomous n n'))
    where
     κ : (n < n') + (n ≡ n') + (n' < n)
       → n ≡ n'
     κ (inl k)       = 𝟘-elim (min' ((n , k) , a))
     κ (inr (inl e)) = e
     κ (inr (inr l)) = 𝟘-elim (min ((n' , l) , a'))
  γ : (∃ n ꞉ ℕ , n ∈ A) ≃ (Σ n ꞉ ℕ , n ∈ B)
  γ = logically-equivalent-props-are-equivalent ∥∥-is-prop ΣB-is-prop f g
   where
    g : (Σ n ꞉ ℕ , n ∈ B) → (∃ n ꞉ ℕ , n ∈ A)
    g (n , a , _) = ∣ n , a ∣
    f : (∃ n ꞉ ℕ , n ∈ A) → (Σ n ꞉ ℕ , n ∈ B)
    f = ∥∥-rec ΣB-is-prop h
     where
      h : (Σ n ꞉ ℕ , n ∈ A) → (Σ n ꞉ ℕ , n ∈ B)
      h (n , a) = k , a' , ν
       where
        u : Σμ (λ m → m ∈ A)
        u = least-from-given (λ m → m ∈ A) A-is-decidable (n , a)
        k : ℕ
        k = pr₁ u
        a' : k ∈ A
        a' = pr₁ (pr₂ u)
        min : (m : ℕ) → m ∈ A → k ≤ m
        min = pr₂ (pr₂ u)
        ν : is-empty (Σ r ꞉ Fin' k , pr₁ r ∈ A)
        ν ((m , l) , aₘ) = less-not-bigger-or-equal m k l (min m aₘ)

\end{code}

We now use the above lemma to prove Martín's observation, from which it follows
that SCSC implies EKC.

We briefly sketch the proof of the observation.

(1) Assume P : 𝓤 is semidecidable and Q : P → 𝓥.
    We are to show that Σ Q is semidecidable.

(2) Find α : ℕ → 𝟚 witnesses the semidecidability of P.

(3) Construct a decidable subset P̃ ⊆ ℕ such that P̃ contains the least n for
    which α n ≡ ₁, if it exists. Then, Σ P̃ ≃ P by (2).

(4) Construct Q̃ ⊆ ℕ as {n ∈ ℕ | n ∈ P̃ and Q pₙ}, where pₙ is constructed
    using n ∈ P̃ and the equivalence between Σ P̃ and P.

(5) Note that Σ Q̃ is a subsingleton, because P̃ contains at most one element.
    Now prove that Σ Q̃ ≃ Σ Q.

(6) Show that Σ Q̃ is semidecidable using the assumption that semidecidable types
    are closed under subsingleton countable joins:
    ∗ recall that Σ Q̃ is a subsingleton;
    ∗ hence, it suffices to prove that each Q̃ n is semidecidable, which is
      straightforward using decidability of P̃.

(7) From (5) and (6), it follows that Σ Q is semidecidable, as desired.

\begin{code}

closure-under-Σ-if-closure-under-subsingleton-countable-joins :
   Semidecidable-Closed-Under-Subsingleton-Countable-Joins 𝓤
 → Semidecidable-Closed-Under-Σ 𝓥 𝓤
closure-under-Σ-if-closure-under-subsingleton-countable-joins {𝓤} H P ρ Q σ =
 ∥∥-rec being-semidecidable-is-prop γ ρ
  where
   γ : semidecidability-structure P
     → is-semidecidable (Σ Q)
   γ (α , e) = is-semidecidable-cong ΣQ̃-ΣQ-equiv ΣQ̃-is-semidecidable
    where
     Q-is-prop-valued : (p : P) → is-prop (Q p)
     Q-is-prop-valued p = prop-if-semidecidable (σ p)

     W : Σ B ꞉ (ℕ → Ω 𝓤₀) , is-complemented-subset B
                          × ((∃ n ꞉ ℕ , α n ≡ ₁) ≃ (Σ n ꞉ ℕ , n ∈ B))
     W = subset-with-only-the-least-witness
          (λ n → (α n ≡ ₁) , 𝟚-is-set) (λ n → 𝟚-is-discrete (α n) ₁)

     P̃ : ℕ → Ω 𝓤₀
     P̃ = pr₁ W
     P̃-is-decidable : is-complemented-subset P̃
     P̃-is-decidable = pr₁ (pr₂ W)
     ΣP̃-equiv : (∃ n ꞉ ℕ , α n ≡ ₁) ≃ (Σ n ꞉ ℕ , n ∈ P̃)
     ΣP̃-equiv = pr₂ (pr₂ W)
     ΣP̃-to-P : (Σ n ꞉ ℕ , n ∈ P̃) → P
     ΣP̃-to-P = ⌜ e ⌝⁻¹ ∘ ⌜ ΣP̃-equiv ⌝⁻¹

     Q̃ : ℕ → 𝓤 ̇
     Q̃ n = Σ q ꞉ n ∈ P̃ , Q (ΣP̃-to-P (n , q))
     Q̃-is-prop-valued : (n : ℕ) → is-prop (Q̃ n)
     Q̃-is-prop-valued n = Σ-is-prop (∈-is-prop P̃ n)
                            (λ q₁ → Q-is-prop-valued (ΣP̃-to-P (n , q₁)))

     ΣQ̃-is-prop : is-prop (Σ Q̃)
     ΣQ̃-is-prop (n , q₁ , q) (n' , q₁' , q') =
      to-subtype-≡ Q̃-is-prop-valued
                   (ap pr₁ (equiv-to-prop (≃-sym ΣP̃-equiv) ∥∥-is-prop
                             (n , q₁) (n' , q₁')))
     ΣQ̃-ΣQ-equiv : Σ Q̃ ≃ Σ Q
     ΣQ̃-ΣQ-equiv = logically-equivalent-props-are-equivalent ΣQ̃-is-prop
                     (Σ-is-prop (prop-if-semidecidable ρ)
                     (λ p → prop-if-semidecidable (σ p)))
                     f g
      where
       f : Σ Q̃ → Σ Q
       f (n , q₁ , q) = (ΣP̃-to-P (n , q₁) , q)
       g : Σ Q → Σ Q̃
       g (p , q) = (n , q₁ , transport Q (prop-if-semidecidable ρ p p') q)
        where
         n : ℕ
         n = pr₁ (⌜ ΣP̃-equiv ⌝ (⌜ e ⌝ p))
         q₁ : n ∈ P̃
         q₁ = pr₂ (⌜ ΣP̃-equiv ⌝ (⌜ e ⌝ p))
         p' : P
         p' = ΣP̃-to-P (n , q₁)

     ΣQ̃-is-semidecidable : is-semidecidable (Σ Q̃)
     ΣQ̃-is-semidecidable = H Q̃ ΣQ̃-is-prop τ
      where
       τ : (n : ℕ) → is-semidecidable (Q̃ n)
       τ n = κ (P̃-is-decidable n)
        where
         κ : decidable (n ∈ P̃) → is-semidecidable (Q̃ n)
         κ (inl  q₁) = is-semidecidable-cong claim (σ p)
          where
           p : P
           p = ΣP̃-to-P (n , q₁)
           claim : Q p ≃ Q̃ n
           claim = logically-equivalent-props-are-equivalent
                    (Q-is-prop-valued p) (Q̃-is-prop-valued n)
                    ϕ ψ
            where
             ϕ : Q p → Q̃ n
             ϕ q = q₁ , q
             ψ : Q̃ n → Q p
             ψ (q₁ , q) =
              transport Q (prop-if-semidecidable ρ (ΣP̃-to-P (n , q₁)) p) q
         κ (inr nq₁) = empty-types-are-semidecidable claim
          where
           claim : is-empty (Q̃ n)
           claim (q₁ , q) = nq₁ q₁

SCSC-implies-EKC :
   Semidecidable-Closed-Under-Subsingleton-Countable-Joins 𝓤
 → Escardo-Knapp-Choice 𝓥 𝓤
SCSC-implies-EKC = semidecidable-closed-under-Σ-implies-EKC
                 ∘ closure-under-Σ-if-closure-under-subsingleton-countable-joins

\end{code}

Summary of the above implications between choice principles and closure
conditions:

Recall that
∗  CSC =              Countable Semidecidable Choice
∗ SCSS = Subsingleton Countable Semidecidable Choice
∗  EKC = Escardo Knapp Choice


        EKC ⟵⟶ Rosolini's Dominance Axiom
         ↑  ⟵⟶ Semidecidable closed under Σ
         ∣                ↑
         ∣                ∣
         ∣                ∣
         ∣                ∣
       SCSC ⟵⟶ Semidecidable closed under
         ↑     subsingleton countable joins
         ∣                ↑
         ∣                ∣
         ∣                ∣
         ∣                ∣
        CSC  ⟶ Semidecidable closed under
                            countable joins


The conjecture is that semidecidable propositions are closed under countable
joins if and only if some form of countable choice holds. But it is not clear
what form this is.

Note that in the above diagram of implications, we only have
  CSC ⟶ (Semidecidable closed under countable joins).

However, for subsingleton countable joins we could get an if and only if with
SCSC, so we do have (Semidecidable closed under countable joins) ⟶ SCSC, which
shows that having closure under countable joins does imply some weak countable
choice principle.



Finally, two closing remarks regarding BSK⁺, SCSC and Escardo Knapp Choice.

\begin{code}

BKS⁺-implies-SCSC : BKS⁺ 𝓤
                  → Subsingleton-Countable-Semidecidable-Choice 𝓤
BKS⁺-implies-SCSC {𝓤} bks =
 SCSC-if-semidecidable-closed-under-subsingleton-countable-joins γ
  where
   γ : Semidecidable-Closed-Under-Subsingleton-Countable-Joins 𝓤
   γ X i σ = bks (Σ X) i

\end{code}

Hence, BKS⁺ implies Escardo Knapp Choice. But we can also easily give a direct
proof of this fact.

\begin{code}

BKS⁺-implies-EKC : BKS⁺ (𝓤 ⊔ 𝓥) → Escardo-Knapp-Choice 𝓤 𝓥
BKS⁺-implies-EKC bks = semidecidable-closed-under-Σ-implies-EKC
                        (λ P σ Q τ → bks (Σ Q)
                        (Σ-is-prop (prop-if-semidecidable σ)
                                   (λ p → prop-if-semidecidable (τ p))))

\end{code}
