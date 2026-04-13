Chuangjie Xu 2014 (ported to TypeTopology in 2026)

This file defines a category-with-families structure on C-spaces. A
type over a context is given by a family together with a notion of
admissible dependent probes satisfying the expected closure axioms. A
term is a section whose composites with probes are admissible. From
these data we define substitution, context comprehension, and verify
the basic CwF equalities needed in the concrete model.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt using (Fun-Ext; dfunext)

module C-Spaces.UsingFunExt.CwF (fe : Fun-Ext) where

open import UF.Base
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

open import C-Spaces.CwFs.Base
open import C-Spaces.Preliminaries.Sequence
open import C-Spaces.UniformContinuity
open import C-Spaces.Coverage
open import C-Spaces.UsingFunExt.Space
open import C-Spaces.UsingFunExt.CartesianClosedness (dfunext fe)

\end{code}

Contexts are C-spaces, and substitutions are continuous maps.

\begin{code}

Con : Set₁
Con = Space

Sub : Con → Con → Set
Sub = Map

\end{code}

A dependent version of the probe axioms.

For a family `A` over a space `Γ`, the predicate `Q` specifies which
dependent probes are admissible. The four clauses say that admissible
dependent probes are closed under constants, precomposition by
uniformly continuous maps, gluing from finite approximations, and
change of witness for the underlying probe.

The last clause would be unnecessary if the probe predicate itself were
proposition-valued.

\begin{code}

dependent-probe-axioms : (Γ : Space) (A : U Γ → Set)
                       → ((p : ₂ℕ → U Γ) → p ∈ Probe Γ → ((α : ₂ℕ) → A (p α)) → Set)
                       → Set
dependent-probe-axioms (Γ , P , c₀ , c₁ , c₂) A Q
 =  ((γ : Γ) (a : A γ) → (λ α → a) ∈ Q (λ α → γ) (c₀ γ))
  × ((t : ₂ℕ → ₂ℕ) (tC : t ∈ C) (p : ₂ℕ → Γ) (pP : p ∈ P) →
     (q : (α : ₂ℕ) → A (p α)) → q ∈ Q p pP → q ∘ t ∈ Q (p ∘ t) (c₁ t tC p pP))
  × ((p : ₂ℕ → Γ)
     (q : (α : ₂ℕ) → A (p α))
     (d : Σ \(n : ℕ) → (s : ₂Fin n) → Σ \(psP : p ∘ cons s ∈ P) → q ∘ cons s ∈ Q (p ∘ cons s) psP) →
     q ∈ Q p (c₂ p (pr₁ d , λ s → pr₁ (pr₂ d s))))
  × ((p : ₂ℕ → Γ) (pP pP' : p ∈ P) (q : (α : ₂ℕ) → A (p α)) → Q p pP q → Q p pP' q)

dependent-probe-axioms-is-prop
 : (Γ : Space) (A : U Γ → Set)
 → (Q : (p : ₂ℕ → U Γ) → p ∈ Probe Γ → ((α : ₂ℕ) → A (p α)) → Set)
 → (∀ p pΓ q → is-prop (q ∈ Q p pΓ))
 → is-prop (dependent-probe-axioms Γ A Q)
dependent-probe-axioms-is-prop (Γ , P , c₀ , c₁ , c₂) A Q pQ
 = ×-is-prop c₀-prop (×-is-prop c₁-prop (×-is-prop c₂-prop c₃-prop))
 where
  c₀-prop
   : is-prop ((γ : Γ) (a : A γ) → (λ α → a) ∈ Q (λ α → γ) (c₀ γ))
  c₀-prop
   = Π₂-is-prop fe (λ γ a → pQ (λ α → γ) (c₀ γ) (λ α → a))
  c₁-prop
   : is-prop ((t : ₂ℕ → ₂ℕ) (tC : t ∈ C) (p : ₂ℕ → Γ) (pP : p ∈ P) →
              (q : (α : ₂ℕ) → A (p α)) → q ∈ Q p pP → q ∘ t ∈ Q (p ∘ t) (c₁ t tC p pP))
  c₁-prop
   = Π₆-is-prop fe (λ t tC p pP q qQ → pQ (p ∘ t) (c₁ t tC p pP) (q ∘ t))
  c₂-prop
   : is-prop ((p : ₂ℕ → Γ)
              (q : (α : ₂ℕ) → A (p α))
              (d : Σ \(n : ℕ) → (s : ₂Fin n) → Σ \(psP : p ∘ cons s ∈ P) → q ∘ cons s ∈ Q (p ∘ cons s) psP) →
              q ∈ Q p (c₂ p (pr₁ d , λ s → pr₁ (pr₂ d s))))
  c₂-prop
   = Π₃-is-prop fe (λ p q d → pQ p (c₂ p (pr₁ d , λ s → pr₁ (pr₂ d s))) q)
  c₃-prop
   : is-prop ((p : ₂ℕ → Γ) (pP pP' : p ∈ P) (q : (α : ₂ℕ) → A (p α)) → Q p pP q → Q p pP' q)
  c₃-prop
   = Π₅-is-prop fe (λ p pP pP' q qQ → pQ p pP' q)

\end{code}

Types over a context are families equipped with proposition-valued
dependent probes satisfying the axioms above. Terms are sections whose
composites with probes are admissible.

\begin{code}

Ty : Con → Set₁
Ty Γ = Σ \(A : U Γ → Set) →
         Σ \(Q : (p : ₂ℕ → U Γ) → p ∈ Probe Γ → ((α : ₂ℕ) → A (p α)) → Set)
           → (∀ p pΓ q → is-prop (q ∈ Q p pΓ)) ×
             dependent-probe-axioms Γ A Q

tyProbe : (Γ : Con) (A : Ty Γ)
        → (p : ₂ℕ → U Γ) → p ∈ Probe Γ → ((α : ₂ℕ) → U A (p α)) → Set
tyProbe _ (_ , Q , _) = Q

tyProbe-is-prop : (Γ : Con) (A : Ty Γ)
                → ∀ p pΓ q → is-prop (q ∈ tyProbe Γ A p pΓ)
tyProbe-is-prop _ (_ , _ , pQ , _) = pQ

Tm : (Γ : Con) → Ty Γ → Set
Tm (Γ , P , _) (A , Q , _)
 = Σ \(u : (γ : Γ) → A γ) → (p : ₂ℕ → Γ) (pP : p ∈ P) → u ∘ p ∈ Q p pP

\end{code}

Substitution is defined by reindexing both the underlying family and
its dependent probe predicate along a substitution.

\begin{code}

⟪_,_⟫_[_]ʸ : (Γ Δ : Con) → Ty Γ → Sub Δ Γ → Ty Δ
⟪ Γ , Δ ⟫ (A , Q , pQ , tc₀ , tc₁ , tc₂ , tc₃) [ σ , cσ ]ʸ
 = Aσ , Q' , pQ' , c₀ , c₁ , c₂ , c₃
 where
  Aσ : U Δ → Set
  Aσ δ = A (σ δ)
  Q' : (p : ₂ℕ → U Δ) → p ∈ Probe Δ → ((α : ₂ℕ) → Aσ (p α)) → Set
  Q' p pΔ q = q ∈ Q (σ ∘ p) (cσ p pΔ)
  pQ' : ∀ p pΔ q → is-prop (q ∈ Q' p pΔ)
  pQ' p pΔ q = pQ (σ ∘ p) (cσ p pΔ) q
  c₀ : (δ : U Δ) (a : Aσ δ) → (λ α → a) ∈ Q' (λ α → δ) (cond₀ Δ δ)
  c₀ δ a = goal
   where
    fact : (λ α → a) ∈ Q (λ α → σ δ) (cond₀ Γ (σ δ))
    fact = tc₀ (σ δ) a
    goal : (λ α → a) ∈ Q (λ α → σ δ) (cσ (λ α → δ) (cond₀ Δ δ))
    goal = tc₃ (λ α → σ δ) _ _ (λ α → a) fact
  c₁ : (t : ₂ℕ → ₂ℕ) (tC : t ∈ C) (p : ₂ℕ → U Δ) (pΔ : p ∈ Probe Δ) →
       (q : (α : ₂ℕ) → Aσ (p α)) → q ∈ Q' p pΔ → q ∘ t ∈ Q' (p ∘ t) (cond₁ Δ t tC p pΔ)
  c₁ t tC p pΔ q qQ' = goal
   where
    fact : q ∘ t ∈ Q (σ ∘ p ∘ t) (cond₁ Γ t tC (σ ∘ p) (cσ p pΔ))
    fact = tc₁ t tC (σ ∘ p) (cσ p pΔ) q qQ'
    goal : q ∘ t ∈ Q (σ ∘ p ∘ t) (cσ (p ∘ t) (cond₁ Δ t tC p pΔ))
    goal = tc₃ (σ ∘ p ∘ t) _ _ (q ∘ t) fact
  c₂ : (p : ₂ℕ → U Δ) (q : (α : ₂ℕ) → Aσ (p α)) →
       (d : Σ \(n : ℕ) → (s : ₂Fin n) → Σ \(psΔ : p ∘ cons s ∈ Probe Δ)
          → q ∘ cons s ∈ Q' (p ∘ cons s) psΔ) →
       q ∈ Q' p (cond₂ Δ p (pr₁ d , λ s → pr₁ (pr₂ d s)))
  c₂ p q (n , ξ) = goal
   where
    ξ' : (s : ₂Fin n)
       → Σ \(σpsΓ : σ ∘ p ∘ cons s ∈ Probe Γ) → q ∘ cons s ∈ Q (σ ∘ p ∘ cons s) σpsΓ
    ξ' s = cσ (p ∘ cons s) (pr₁ (ξ s)) , pr₂ (ξ s)
    fact : q ∈ Q (σ ∘ p) (cond₂ Γ (σ ∘ p) (n , λ s → pr₁ (ξ' s)))
    fact = tc₂ (σ ∘ p) q (n , ξ')
    goal : q ∈ Q (σ ∘ p) (cσ p (cond₂ Δ p (n , λ s → pr₁ (ξ s))))
    goal = tc₃ (σ ∘ p) _ _ q fact
  c₃ : (p : ₂ℕ → U Δ) (pΔ pΔ' : p ∈ Probe Δ) (q : (α : ₂ℕ) → Aσ (p α)) →
       Q' p pΔ q → Q' p pΔ' q
  c₃ p _ _ = tc₃ (σ ∘ p) _ _

⟪_,_,_⟫_[_]ᵐ : (Γ Δ : Con) (A : Ty Γ)
             → Tm Γ A → (σ : Sub Δ Γ) → Tm Δ (⟪ Γ , Δ ⟫ A [ σ ]ʸ)
⟪ Γ , Δ , (A , Q , _) ⟫ (u , cu) [ σ , cσ ]ᵐ = uσ , cuσ
 where
  uσ : (δ : U Δ) → A (σ δ)
  uσ δ = u (σ δ)
  cuσ : (p : ₂ℕ → U Δ) (pΔ : p ∈ Probe Δ) → uσ ∘ p ∈ Q (σ ∘ p) (cσ p pΔ)
  cuσ p pΔ = cu (σ ∘ p) (cσ p pΔ)

\end{code}

Context comprehension is given by the sigma-space of a family, equipped
with the evident probe structure.

\begin{code}

_₊_ : (Γ : Con) → Ty Γ → Con
Γ ₊ (A , Q , pQ , tc₀ , tc₁ , tc₂ , tc₃) = (Σ A , R , c₀ , c₁ , c₂)
 where
  R : (₂ℕ → Σ A) → Set
  R r = Σ \(rΓ : pr₁ ∘ r ∈ Probe Γ) → pr₂ ∘ r ∈ Q (pr₁ ∘ r) rΓ
  c₀ : (w : Σ A) → (λ α → w) ∈ R
  c₀ (γ , a) = cond₀ Γ γ , tc₀ γ a
  c₁ : (t : ₂ℕ → ₂ℕ) (tC : t ∈ C) (r : ₂ℕ → Σ A) (rR : r ∈ R) → r ∘ t ∈ R
  c₁ t tC r (rΓ , rQ) = cond₁ Γ t tC (pr₁ ∘ r) rΓ ,
                        tc₁ t tC (pr₁ ∘ r) rΓ (pr₂ ∘ r) rQ
  c₂ : (r : ₂ℕ → Σ A)
     → (Σ \(n : ℕ) → ∀(s : ₂Fin n) → r ∘ cons s ∈ R) → r ∈ R
  c₂ r (n , ξ) = cond₂ Γ (pr₁ ∘ r) (n , λ s → pr₁ (ξ s)) ,
                 tc₂ (pr₁ ∘ r) (pr₂ ∘ r) (n , ξ)

⟪_,_⟫p : (Γ : Con) (A : Ty Γ) → Sub (Γ ₊ A) Γ
⟪ Γ , A ⟫p = pr₁ , (λ p pΓA → pr₁ pΓA)

⟪_⟫_[p]ʸ : (Γ : Con) → (A : Ty Γ) → Ty (Γ ₊ A)
⟪ Γ ⟫ A [p]ʸ = ⟪ Γ , Γ ₊ A ⟫ A [ ⟪ Γ , A ⟫p ]ʸ

⟪_,_⟫q : (Γ : Con) (A : Ty Γ) → Tm (Γ ₊ A) (⟪ Γ ⟫ A [p]ʸ)
⟪ Γ , A ⟫q = pr₂ , (λ p pΓA → pr₂ pΓA)

⟪_,_,_⟫⟨_,_⟩ : (Γ Δ : Con) (A : Ty Γ)
             → (σ : Sub Δ Γ) → Tm Δ (⟪ Γ , Δ ⟫ A [ σ ]ʸ)
             → Sub Δ (Γ ₊ A)
⟪ Γ , Δ , A ⟫⟨ (σ , cσ) , (u , cu) ⟩ = (σu , cσu)
 where
  σu : U Δ → Σ (U A)
  σu δ = (σ δ , u δ)
  cσu : ∀(p : ₂ℕ → U Δ) (pΔ : p ∈ Probe Δ) → σu ∘ p ∈ Probe (Γ ₊ A)
  cσu p pΔ = (cσ p pΔ , cu p pΔ)

\end{code}

We can now assemble these operations into a CwF structure on spaces.

\begin{code}

SpaceCwFStructure : CwFStructure
SpaceCwFStructure = record {
    Con = Space
  ; Sub = Map
  ; idSub = λ {Γ} → idMap Γ
  ; _○_ = λ {Γ Δ Θ} f g → ⟪ Γ , Δ , Θ ⟫ f ○ g
  ; ε = 𝟙Space
  ; εSub = λ {Γ} → continuous-unit Γ
  ; Ty = Ty
  ; _[_] = λ {Γ Δ} A σ → ⟪ Γ , Δ ⟫ A [ σ ]ʸ
  ; Tm = Tm
  ; _⁅_⁆ = λ {Γ Δ A} t σ → ⟪ Γ , Δ , A ⟫ t [ σ ]ᵐ
  ; _₊_ = _₊_
  ; ⟨_,_⟩ = λ {Γ Δ A} σ u → ⟪ Γ , Δ , A ⟫⟨ σ , u ⟩
  ; p = λ {Γ A} → ⟪ Γ , A ⟫p
  ; q = λ {Γ A} → ⟪ Γ , A ⟫q
  }

\end{code}

We next verify the basic equalities satisfied by this structure.

For the term equalities below we work with raw equalities, without the
explicit transports that appear in `CwFLaws`. This is enough for the
present concrete development because the family `Tm Γ A` only depends
definitionally on the family part and the probe predicate part of
`A : Ty Γ`; it ignores the proof components. For example,
`⟪ Γ , Γ , A ⟫ t [ idMap Γ ]ᵐ ＝ t` type checks because reindexing along
`idMap` leaves those data judgmentally unchanged, even though the full
equality `⟪ Γ , Γ ⟫ A [ idMap Γ ]ʸ ＝ A` still needs proof irrelevance for
the proof fields.

Accordingly, this file does not yet package the results below into an
element of `CwFLaws SpaceCwFStructure`. The record `CwFLaws` phrases
some laws, such as `tm[id]`, `tm[○]`, `q,-β`, and `,○-distrib`, with
transports along the corresponding type equalities. To build that
record one would still need bridge lemmas showing that these transports
act trivially on the concrete term family used here.

\begin{code}

-- Left unit law for substitutions.
-- id ∘ σ ＝ σ
idl : {Γ Δ : Con} {σ : Sub Γ Δ}
    → ⟪ Γ , Δ , Δ ⟫ idMap Δ ○ σ ＝ σ
idl = refl

-- Right unit law for substitutions.
-- σ ∘ id = σ
idr : {Γ Δ : Con} {σ : Sub Γ Δ}
    → ⟪ Γ , Γ , Δ ⟫ σ ○ idMap Γ ＝ σ
idr = refl

-- Associativity of substitution composition.
-- (σ ∘ τ) ∘ ρ = σ ∘ (τ ∘ ρ)
○-assoc : {Γ Δ Θ Ξ : Con} {σ : Sub Θ Ξ} {τ : Sub Δ Θ} {ρ : Sub Γ Δ}
        → ⟪ Γ , Δ , Ξ ⟫ (⟪ Δ , Θ , Ξ ⟫ σ ○ τ) ○ ρ ＝
          ⟪ Γ , Θ , Ξ ⟫ σ ○ (⟪ Γ , Δ , Θ ⟫ τ ○ ρ)
○-assoc = refl

-- There is a unique substitution into the terminal context.
εSub-unique : {Γ : Con} {σ : Sub Γ 𝟙Space}
            → σ ＝ continuous-unit Γ
εSub-unique = refl

-- Type substitution by the identity map is extensionality equal to the original type.
-- A [ id ] = A
ty[id] : (Γ : Con) (A : Ty Γ)
       → ⟪ Γ , Γ ⟫ A [ idMap Γ ]ʸ ＝ A
ty[id] Γ A =
  to-Σ-＝
    (refl ,
     to-Σ-＝
       (refl ,
        to-×-＝ refl
          (dependent-probe-axioms-is-prop Γ _ _ (tyProbe-is-prop Γ A) _ _)))

-- Type substitution is compatible with composition.
-- A [ σ ∘ τ ] = A [ σ ] [ τ ]
ty[○] : (Γ Δ Θ : Con) (A : Ty Γ) (σ : Sub Δ Γ) (τ : Sub Θ Δ)
      → ⟪ Γ , Θ ⟫ A [ ⟪ Θ , Δ , Γ ⟫ σ ○ τ ]ʸ ＝
        ⟪ Δ , Θ ⟫ ⟪ Γ , Δ ⟫ A [ σ ]ʸ [ τ ]ʸ
ty[○] Γ Δ Θ A σ τ =
  to-Σ-＝
    (refl ,
     to-Σ-＝
       (refl ,
        to-×-＝ refl
          (dependent-probe-axioms-is-prop Θ _ _ (tyProbe-is-prop Θ Aστ) _ _)))
 where
  Aστ : Ty Θ
  Aστ = ⟪ Γ , Θ ⟫ A [ ⟪ Θ , Δ , Γ ⟫ σ ○ τ ]ʸ

-- Term substitution by the identity map is judgmentally trivial in this concrete model.
-- t [ id ] = t
tm[id] : (Γ : Con) (A : Ty Γ) (t : Tm Γ A)
       → ⟪ Γ , Γ , A ⟫ t [ idMap Γ ]ᵐ ＝ t
tm[id] Γ A t = refl

-- Term substitution is compatible with composition.
-- t [ σ ∘ τ ] = t [ σ ] [ τ ]
tm[○] : {Γ Δ Θ : Con} {A : Ty Γ} {t : Tm Γ A} {σ : Sub Δ Γ} {τ : Sub Θ Δ}
      → ⟪ Γ , Θ , A ⟫ t [ ⟪ Θ , Δ , Γ ⟫ σ ○ τ ]ᵐ ＝
        ⟪ Δ , Θ , ⟪ Γ , Δ ⟫ A [ σ ]ʸ ⟫ ⟪ Γ , Δ , A ⟫ t [ σ ]ᵐ [ τ ]ᵐ
tm[○] = refl

-- The first projection of a comprehension pair is the original substitution.
-- p ∘ ⟨ σ , t ⟩ ＝ σ
p,-β : {Γ Δ : Con} {A : Ty Γ} {σ : Sub Δ Γ} {t : Tm Δ (⟪ Γ , Δ ⟫ A [ σ ]ʸ)}
     → ⟪ Δ , Γ ₊ A , Γ ⟫ ⟪ Γ , A ⟫p ○ ⟪ Γ , Δ , A ⟫⟨ σ , t ⟩ ＝ σ
p,-β = refl

-- The second projection of a comprehension pair recovers the given term.
-- q [ ⟨ σ , t ⟩ ] = t
q,-β : {Γ Δ : Con} {A : Ty Γ} {σ : Sub Δ Γ} {t : Tm Δ (⟪ Γ , Δ ⟫ A [ σ ]ʸ)}
     → ⟪ Γ ₊ A , Δ , ⟪ Γ ⟫ A [p]ʸ ⟫ ⟪ Γ , A ⟫q [ ⟪ Γ , Δ , A ⟫⟨ σ , t ⟩ ]ᵐ ＝ t
q,-β = refl

-- Pairing the projections yields the identity substitution on the comprehension context.
-- ⟨ p , q ⟩ ＝ id
p,q-η : {Γ Δ : Con} {A : Ty Γ} {σ : Sub Δ Γ} {t : Tm Δ (⟪ Γ , Δ ⟫ A [ σ ]ʸ)}
      → ⟪ Γ , Γ ₊ A , A ⟫⟨ ⟪ Γ , A ⟫p , ⟪ Γ , A ⟫q ⟩ ＝ idMap (Γ ₊ A)
p,q-η = refl

-- Pairing is stable under postcomposition.
-- ⟨ σ , t ⟩ ∘ τ = ⟨ σ ∘ τ , t [ τ ] ⟩
,○-distrib : {Γ Δ Θ : Con} {A : Ty Γ}
           → {σ : Sub Δ Γ} {t : Tm Δ (⟪ Γ , Δ ⟫ A [ σ ]ʸ)} {τ : Sub Θ Δ}
           → ⟪ Θ , Δ , Γ ₊ A ⟫ ⟪ Γ , Δ , A ⟫⟨ σ , t ⟩ ○ τ ＝
             ⟪ Γ , Θ , A ⟫⟨ ⟪ Θ , Δ , Γ ⟫ σ ○ τ , ⟪ Δ , Θ , ⟪ Γ , Δ ⟫ A [ σ ]ʸ ⟫ t [ τ ]ᵐ ⟩
,○-distrib = refl

\end{code}
