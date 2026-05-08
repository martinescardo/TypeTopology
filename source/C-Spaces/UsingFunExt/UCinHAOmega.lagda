Chuangjie Xu 2013 (updated in February 2015, ported to TypeTopology in 2025)

We validate the uniform-continuity principle in HAω via C-spaces.

The syntax of HAω and the interpretation of System T terms are factored out into
`C-Spaces.Syntax.HAOmega` and `TdefinableFunctionsAreUC`. This module adds the
realizability semantics for HAω-formulas and shows that the distinguished
formula `Principle[UC]` is realized in the C-space model.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt using (DN-funext)

module C-Spaces.UsingFunExt.UCinHAOmega (fe : DN-funext 𝓤₀ 𝓤₀) where


open import C-Spaces.Preliminaries.Sequence
open import C-Spaces.Preliminaries.Booleans.Functions
open import C-Spaces.Preliminaries.Naturals.Order
open import C-Spaces.Syntax.HAOmega
open import C-Spaces.UsingFunExt.Space
open import C-Spaces.UsingFunExt.CartesianClosedness fe
open import C-Spaces.UsingFunExt.DiscreteSpace fe
open import C-Spaces.UsingFunExt.Fan fe
open import C-Spaces.UsingFunExt.TdefinableFunctionsAreUC fe
     renaming (c⟦_⟧ʸ to ⟦_⟧ʸ ; c⟦_⟧ᶜ to ⟦_⟧ᶜ; c⟦_⟧ᵐ to ⟦_⟧ᵐ)

\end{code}

Realizability semantics

The type `∣ φ ∣` is the type of realizers of `φ`. Equality is realized by a
natural-number placeholder, while conjunction, implication, and quantifiers are
interpreted by the corresponding type formers.

\begin{code}

∣_∣ : {Γ : Cxt} → HAω Γ → Ty
∣ M == N ∣  = Ⓝ
∣ φ ∧∧ ψ ∣  = ∣ φ ∣ ⊠ ∣ ψ ∣
∣ φ →→ ψ ∣  = ∣ φ ∣ ⇨ ∣ ψ ∣
∣ Ā σ · φ ∣ = σ ⇨ ∣ φ ∣
∣ Ē σ · φ ∣ = σ ⊠ ∣ φ ∣

\end{code}

A pair `(ρ , r)` realizes a formula `φ` when `ρ` interprets the free variables
of `φ` and `r` supplies the realizer data required by the logical shape of `φ`.
The type `φ is-realizable` is the corresponding existential statement saying
that some environment-realizer pair realizes `φ`.

\begin{code}

infix 50 _is-realized-by_

_is-realized-by_ : {Γ : Cxt} → (φ : HAω Γ) → U ⟦ Γ ⟧ᶜ × U ⟦ ∣ φ ∣ ⟧ʸ → Set
(M == N)  is-realized-by (ρ , _)     = pr₁ ⟦ M ⟧ᵐ ρ ＝ pr₁ ⟦ N ⟧ᵐ ρ
(φ ∧∧ ψ)  is-realized-by (ρ , x , y) = φ is-realized-by (ρ , x) × ψ is-realized-by (ρ , y)
(φ →→ ψ)  is-realized-by (ρ , f)     = ∀(x : U ⟦ ∣ φ ∣ ⟧ʸ) → φ is-realized-by (ρ , x) → ψ is-realized-by (ρ , pr₁ f x)
(Ā σ · φ) is-realized-by (ρ , f)     = ∀(x : U ⟦ σ ⟧ʸ) → φ is-realized-by ((ρ , x) , pr₁ f x)
(Ē σ · φ) is-realized-by (ρ , x , y) = φ is-realized-by ((ρ , x) , y)

_is-realizable : {Γ : Cxt} → HAω Γ → Set
_is-realizable {Γ} φ = Σ \(w : U ⟦ Γ ⟧ᶜ × U ⟦ ∣ φ ∣ ⟧ʸ) → φ is-realized-by w

\end{code}

In the case of the formula `Principle[UC]`, realizability amounts to producing
for each functional `f : (ℕSpace ⇒ 𝟚Space) ⇒ ℕSpace` a modulus together with
enough auxiliary data to satisfy the realizability interpretation of the
quantifier prefix.

The final theorem is obtained by supplying a realizer for the quantifier prefix
of `Principle[UC]`. The modulus component is extracted by the fan functional,
and the remaining higher-type component is filled by a constant dummy witness,
which is sufficient because only the modulus is used in the equality
conclusion. The proof then shows that realization of the premise
`A＝⟦M⟧B == ⊤` yields agreement of the two input sequences on the required
initial segment, so that the fan theorem can be applied.

\begin{code}

Theorem : Principle[UC] is-realizable
Theorem = (⋆ , e) , prf
 where
  e : U (((ℕSpace ⇒ 𝟚Space) ⇒ ℕSpace) ⇒ (ℕSpace ⊗ ((ℕSpace ⇒ 𝟚Space) ⇒ (ℕSpace ⇒ 𝟚Space) ⇒ ℕSpace ⇒ ℕSpace)))
  e = g , cts-g
   where
    -- This witness is constant and computationally irrelevant for the equality conclusion.
    c : Map (ℕSpace ⇒ 𝟚Space) ((ℕSpace ⇒ 𝟚Space) ⇒ ℕSpace ⇒ ℕSpace)
    c = continuous-constant (ℕSpace ⇒ 𝟚Space) ((ℕSpace ⇒ 𝟚Space) ⇒ ℕSpace ⇒ ℕSpace)
                            (continuous-constant (ℕSpace ⇒ 𝟚Space) (ℕSpace ⇒ ℕSpace)
                                                 (continuous-constant ℕSpace ℕSpace 0))
    -- The modulus component is computed by the fan functional.
    g : Map (ℕSpace ⇒ 𝟚Space) ℕSpace → ℕ × Map (ℕSpace ⇒ 𝟚Space) ((ℕSpace ⇒ 𝟚Space) ⇒ ℕSpace ⇒ ℕSpace)
    g f = pr₁ fan f , c
    cts-g : continuous ((ℕSpace ⇒ 𝟚Space) ⇒ ℕSpace)
                       (ℕSpace ⊗ ((ℕSpace ⇒ 𝟚Space) ⇒ (ℕSpace ⇒ 𝟚Space) ⇒ ℕSpace ⇒ ℕSpace)) g
    cts-g p pP = pr₂ fan p pP , (λ _ _ _ _ _ _ _ _ _ _ _ _ → 0 , (λ _ _ _ → refl) , (λ _ _ → ≤-zero))
  prf : Principle[UC] is-realized-by (⋆ , e)
  prf f = prf'
   where
    -- The candidate modulus supplied by the realizer.
    m : ℕ
    m = pr₁ (pr₁ e f)
    prf' : ∀(α β : Map ℕSpace 𝟚Space) →
           ∀(x : ℕ) → (A＝⟦M⟧B == ⊤) is-realized-by (((((⋆ , f) , m) , α) , β) , x) →
           pr₁ f α ＝ pr₁ f β
   -- i.e. if α and β agree up to the realized modulus m, then f α ＝ f β.
    prf' α β _ EM = fan-behaviour f α β em
     where
      ρ : U ⟦ Γ ⟧ᶜ
      ρ = ((((⋆ , f) , m) , α) , β)
      -- The recursive boolean accumulator extracted from the interpretation of
      -- the term `step`.
      g : ℕ → 𝟚 → 𝟚
      g n b = pr₁ (pr₁ (pr₁ ⟦ step ⟧ᵐ ρ) n) b
      -- If the accumulator remains equal to ₁ for k steps, then α and β agree
      -- on their first k bits.
      lemma : (k : ℕ) → ℕ-induction ₁ g k ＝ ₁ → pr₁ α ＝⟦ k ⟧ pr₁ β
      lemma 0        refl = ＝⟦zero⟧
      lemma (succ k) esk  = ＝⟦succ⟧ IH claim₁
       where
        ek : ℕ-induction ₁ g k ＝ ₁
        ek = pr₂ (Lemma[min] (eq (pr₁ α k) (pr₁ β k)) (ℕ-induction ₁ g k)  esk)
        IH : pr₁ α ＝⟦ k ⟧ pr₁ β
        IH = lemma k ek
        claim₀ : eq (pr₁ α k) (pr₁ β k) ＝ ₁
        claim₀ = pr₁ (Lemma[min] (eq (pr₁ α k) (pr₁ β k)) (ℕ-induction ₁ g k) esk)
        claim₁ : pr₁ α k ＝ pr₁ β k
        claim₁ = Lemma[eq] (pr₁ α k) (pr₁ β k) claim₀
      -- The realization assumption for `A＝⟦M⟧B == ⊤` yields prefix agreement
      -- at the modulus `m`.
      em : pr₁ α ＝⟦ m ⟧ pr₁ β
      em = lemma m EM

\end{code}
