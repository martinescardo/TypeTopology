Chuangjie Xu 2013

(Improved on 14 August, 2014)

(ported to TypeTopology in 2025)

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt using (DN-funext)

module C-Space.UsingFunExt.Hierarchy (fe : DN-funext 𝓤₀ 𝓤₀) where

open import UF.Base
open import UF.DiscreteAndSeparated

open import C-Space.Preliminaries.Sequence
open import C-Space.Preliminaries.FunExt fe
open import C-Space.UniformContinuity
open import C-Space.Coverage
open import C-Space.UsingFunExt.Space
open import C-Space.UsingFunExt.CartesianClosedness fe
open import C-Space.UsingFunExt.DiscreteSpace fe
open import C-Space.UsingFunExt.IndiscreteSpace fe

\end{code}

Type structure

\begin{code}

data Ty : Set where
 Ⓝ : Ty
 _⊠_ : Ty → Ty → Ty
 _⇨_ : Ty → Ty → Ty

\end{code}

The full type hierarchy (FTH) is a full subcategory of sets. Objects in FTH can
be considered as (the interpretations of) the elements of Ty, while morphisms
are maps ⟦ σ ⟧s → ⟦ τ ⟧s, where ⟦_⟧s is the interpretation of Ty in Set.

\begin{code}

⟦_⟧s : Ty → Set
⟦ Ⓝ ⟧s = ℕ
⟦ σ ⊠ τ ⟧s = ⟦ σ ⟧s × ⟦ τ ⟧s
⟦ σ ⇨ τ ⟧s = ⟦ σ ⟧s → ⟦ τ ⟧s

\end{code}

Similarly, the Kleene-Kreisel hierarchy (KKH), via C-space manifestation, also
contains (interpretations of) elements of Ty as objects, and continuous maps
from ⟦ σ ⟧c to ⟦ τ ⟧c as morphisms.

\begin{code}

⟦_⟧c : Ty → Space
⟦ Ⓝ ⟧c = ℕSpace
⟦ σ ⊠ τ ⟧c = ⟦ σ ⟧c ⊗ ⟦ τ ⟧c
⟦ σ ⇨ τ ⟧c = ⟦ σ ⟧c ⇒ ⟦ τ ⟧c

\end{code}

In this module, the double negation of function extensionality doesn't
seem to be sufficient. Hence we use the full one as a hypothesis, to
show the following:

(1) Probes on the spaces in the Kleene-Kreisel hierarchy are
    hpropositions.

(2) If two continuous maps in the Kleene-Kreisel hierarchy are
    pointwise equal, the they are identical morphisms.

\begin{code}

Lemma[simple-probe-hprop] : (σ : Ty) → (p : ₂ℕ → U ⟦ σ ⟧c)
                          → ∀(pσ₀ pσ₁ : p ∈ Probe ⟦ σ ⟧c) → pσ₀ ＝ pσ₁
Lemma[simple-probe-hprop] Ⓝ p pN₀ pN₁ = Lemma[LC-hprop] ℕ-is-set p pN₀ pN₁
Lemma[simple-probe-hprop] (σ ⊠ τ) r rστ₀ rστ₁ = to-×-＝ IHσ IHτ
 where
  IHσ : pr₁ rστ₀ ＝ pr₁ rστ₁
  IHσ = Lemma[simple-probe-hprop] σ (pr₁ ∘ r) (pr₁ rστ₀) (pr₁ rστ₁)
  IHτ : pr₂ rστ₀ ＝ pr₂ rστ₁
  IHτ = Lemma[simple-probe-hprop] τ (pr₂ ∘ r) (pr₂ rστ₀) (pr₂ rστ₁)
Lemma[simple-probe-hprop] (σ ⇨ τ) r rστ₀ rστ₁ = goal
 where
  IH : ∀(p : ₂ℕ → U ⟦ σ ⟧c) → (pσ : p ∈ Probe ⟦ σ ⟧c) → ∀(t : ₂ℕ → ₂ℕ) → (uc : t ∈ C) → 
       rστ₀ p pσ t uc ＝ rστ₁ p pσ t uc
  IH p pσ t uc = Lemma[simple-probe-hprop] τ (λ α → (pr₁ ∘ r)(t α)(p α))
                                           (rστ₀ p pσ t uc) (rστ₁ p pσ t uc)
  goal : rστ₀ ＝ rστ₁
  goal = fe⁴ IH
        -----

Lemma[simple-Map-＝] : ∀(X : Space) → ∀(σ : Ty) → ∀(f g : Map X ⟦ σ ⟧c)
                    → (∀(x : U X) → pr₁ f x ＝ pr₁ g x) → f ＝ g
Lemma[simple-Map-＝] X σ (f , cf) (g , cg) ex = to-Σ-＝ (e₀ , e₁)
 where
  e₀  : f ＝ g
  e₀  = fe ex
  cg' : continuous X ⟦ σ ⟧c g
  cg' = transport (continuous X ⟦ σ ⟧c) e₀ cf
  ee₁ : ∀(p : ₂ℕ → U X) → (pX : p ∈ Probe X) → cg' p pX ＝ cg p pX
  ee₁ p pX = Lemma[simple-probe-hprop] σ (g ∘ p) (cg' p pX) (cg p pX)
  e₁  : cg' ＝ cg
  e₁  = fe² ee₁
       -----

\end{code}

The main lemma says that if UC holds then all spaces in the
Kleene-Kreisel hierarchy are indiscrete, in the sense that all maps
from cantor space are probes.

Notice that this doesn't depend on function extensionality.

\begin{code}

Lemma[UC-implies-indiscreteness] : Axiom[UC-ℕ] → ∀(σ : Ty) → indiscrete ⟦ σ ⟧c
Lemma[UC-implies-indiscreteness] ucN Ⓝ = ucN
Lemma[UC-implies-indiscreteness] ucN (σ ⊠ τ) = λ p → IHσ (pr₁ ∘ p) , IHτ (pr₂ ∘ p)
 where
  IHσ : indiscrete ⟦ σ ⟧c
  IHσ = Lemma[UC-implies-indiscreteness] ucN σ
  IHτ : indiscrete ⟦ τ ⟧c
  IHτ = Lemma[UC-implies-indiscreteness] ucN τ
Lemma[UC-implies-indiscreteness] ucN (σ ⇨ τ) = λ r p _ t _ → IHτ (λ α → pr₁(r(t α))(p α))
 where
  IHτ : indiscrete ⟦ τ ⟧c
  IHτ = Lemma[UC-implies-indiscreteness] ucN τ

\end{code}

If UC holds for types, then the full type and Kleene-Kreisel hierarchies agree,
in the sense that the two interpretations of each type are equivalent.

\begin{code}

_≅_ : Set → Set → Set
X ≅ Y = Σ \(f : X → Y) → Σ \(g : Y → X) →
           (∀(x : X) → g(f x) ＝ x) × (∀(y : Y) → f(g y) ＝ y)


Theorem[UC→⟦σ⟧s≅⟦σ⟧c] : Axiom[UC-ℕ] → ∀(σ : Ty) → ⟦ σ ⟧s ≅ U ⟦ σ ⟧c
Theorem[UC→⟦σ⟧s≅⟦σ⟧c] ucN Ⓝ = id , id , (λ x → refl) , (λ y → refl)
Theorem[UC→⟦σ⟧s≅⟦σ⟧c] ucN (σ ⊠ τ) = f , g , ex , ey
 where
  IHσ : ⟦ σ ⟧s ≅ U ⟦ σ ⟧c
  IHσ = Theorem[UC→⟦σ⟧s≅⟦σ⟧c] ucN σ
  fσ  : ⟦ σ ⟧s → U ⟦ σ ⟧c
  fσ  = pr₁ IHσ
  gσ  : U ⟦ σ ⟧c → ⟦ σ ⟧s
  gσ  = pr₁ (pr₂ IHσ)
  exσ : ∀(x : ⟦ σ ⟧s)   → gσ(fσ x) ＝ x
  exσ = pr₁ (pr₂ (pr₂ IHσ))
  eyσ : ∀(y : U ⟦ σ ⟧c) → fσ(gσ y) ＝ y
  eyσ = pr₂ (pr₂ (pr₂ IHσ))
  IHτ : ⟦ τ ⟧s ≅ U ⟦ τ ⟧c
  IHτ = Theorem[UC→⟦σ⟧s≅⟦σ⟧c] ucN τ
  fτ  : ⟦ τ ⟧s → U ⟦ τ ⟧c
  fτ  = pr₁ IHτ
  gτ  : U ⟦ τ ⟧c → ⟦ τ ⟧s
  gτ  = pr₁ (pr₂ IHτ)
  exτ : ∀(x : ⟦ τ ⟧s)   → gτ(fτ x) ＝ x
  exτ = pr₁ (pr₂ (pr₂ IHτ))
  eyτ : ∀(y : U ⟦ τ ⟧c) → fτ(gτ y) ＝ y
  eyτ = pr₂ (pr₂ (pr₂ IHτ))
  f : ⟦ σ ⟧s × ⟦ τ ⟧s → U ⟦ σ ⟧c × U ⟦ τ ⟧c
  f (x , x') = (fσ x , fτ x')
  g : U ⟦ σ ⟧c × U ⟦ τ ⟧c → ⟦ σ ⟧s × ⟦ τ ⟧s
  g (y , y') = (gσ y , gτ y')
  ex : ∀(x : ⟦ σ ⟧s × ⟦ τ ⟧s) → g(f x) ＝ x
  ex (x , x') = to-×-＝ (exσ x) (exτ x')
  ey : ∀(y : U ⟦ σ ⟧c × U ⟦ τ ⟧c) → f(g y) ＝ y
  ey (y , y') = to-×-＝ (eyσ y) (eyτ y')
Theorem[UC→⟦σ⟧s≅⟦σ⟧c] ucN (σ ⇨ τ) = f , g , ex , ey
 where
  IHσ : ⟦ σ ⟧s ≅ U ⟦ σ ⟧c
  IHσ = Theorem[UC→⟦σ⟧s≅⟦σ⟧c] ucN σ
  fσ  : ⟦ σ ⟧s → U ⟦ σ ⟧c
  fσ  = pr₁ IHσ
  gσ  : U ⟦ σ ⟧c → ⟦ σ ⟧s
  gσ  = pr₁ (pr₂ IHσ)
  exσ : ∀(x : ⟦ σ ⟧s)   → gσ(fσ x) ＝ x
  exσ = pr₁ (pr₂ (pr₂ IHσ))
  eyσ : ∀(y : U ⟦ σ ⟧c) → fσ(gσ y) ＝ y
  eyσ = pr₂ (pr₂ (pr₂ IHσ))
  IHτ : ⟦ τ ⟧s ≅ U ⟦ τ ⟧c
  IHτ = Theorem[UC→⟦σ⟧s≅⟦σ⟧c] ucN τ
  fτ  : ⟦ τ ⟧s → U ⟦ τ ⟧c
  fτ  = pr₁ IHτ
  gτ  : U ⟦ τ ⟧c → ⟦ τ ⟧s
  gτ  = pr₁ (pr₂ IHτ)
  exτ : ∀(x : ⟦ τ ⟧s)   → gτ(fτ x) ＝ x
  exτ = pr₁ (pr₂ (pr₂ IHτ))
  eyτ : ∀(y : U ⟦ τ ⟧c) → fτ(gτ y) ＝ y
  eyτ = pr₂ (pr₂ (pr₂ IHτ))
  f : (⟦ σ ⟧s → ⟦ τ ⟧s) → U(⟦ σ ⟧c ⇒ ⟦ τ ⟧c)
  f φ = fτ ∘ φ ∘ gσ , λ p _ → Lemma[UC-implies-indiscreteness] ucN τ (fτ ∘ φ ∘ gσ ∘ p)
  g : U(⟦ σ ⟧c ⇒ ⟦ τ ⟧c) → ⟦ σ ⟧s → ⟦ τ ⟧s
  g (ψ , _) = gτ ∘ ψ ∘ fσ
  ex : ∀(φ : ⟦ σ ⟧s → ⟦ τ ⟧s) → g(f φ) ＝ φ
  ex φ = fe claim
        ----
   where
    claim : ∀(x : ⟦ σ ⟧s) → g (f φ) x ＝ φ x
    claim x = e₀ ∙ e₁
     where
      e₀ : gτ(fτ(φ(gσ(fσ x)))) ＝ gτ(fτ(φ x))
      e₀ = ap (gτ ∘ fτ ∘ φ) (exσ x)
      e₁ : gτ(fτ(φ x)) ＝ φ x
      e₁ = exτ (φ x)
  ey : ∀(ψ : U(⟦ σ ⟧c ⇒ ⟦ τ ⟧c)) → f(g ψ) ＝ ψ
  ey ψ = Lemma[simple-Map-＝] ⟦ σ ⟧c τ (f(g ψ)) ψ claim
   where
    claim : ∀(y : U ⟦ σ ⟧c) → pr₁ (f (g ψ)) y ＝ pr₁ ψ y
    claim y = e₀ ∙ e₁
     where
      e₀ : fτ(gτ(pr₁ ψ (fσ(gσ y)))) ＝ fτ(gτ(pr₁ ψ y))
      e₀ = ap (fτ ∘ gτ ∘ (pr₁ ψ)) (eyσ y)
      e₁ : fτ(gτ(pr₁ ψ y)) ＝ pr₁ ψ y
      e₁ = eyτ (pr₁ ψ y)

\end{code}

Since we consider objects in both hierarchies as elements of Ty, the equivalence
on objects is simply the identity.  Then the equivalence on hom-sets directly
follows the above theorem.

\begin{code}

HomFTH : Ty → Ty → Set
HomFTH σ τ = ⟦ σ ⟧s → ⟦ τ ⟧s

HomKKH : Ty → Ty → Set
HomKKH σ τ = Map ⟦ σ ⟧c ⟦ τ ⟧c

Corollary[UC→HomFTH≅HomKKH] : Axiom[UC-ℕ] → ∀(σ τ : Ty) → HomFTH σ τ ≅ HomKKH σ τ
Corollary[UC→HomFTH≅HomKKH] uc σ τ = Theorem[UC→⟦σ⟧s≅⟦σ⟧c] uc (σ ⇨ τ)

\end{code}
