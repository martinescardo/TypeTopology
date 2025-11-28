Martin Escardo, 1-7 November 2023.

We prove the main results of [1] and [2] about automorphisms of Ω.

[1] Peter T. Johnstone. Automorphisms of Ω. Algebra Universalis,
    9 (1979) 1-7.
    https://doi.org/10.1007/BF02488012

[2] Peter Freyd. Choice and well-ordering.  Annals of Pure and Applied
    Logic 35 (1987) 149-166.
    https://doi.org/10.1016/0168-0072(87)90060-1
    https://core.ac.uk/download/pdf/81927529.pdf

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import Groups.Type
open import MLTT.Spartan
open import UF.Embeddings
open import UF.Equiv hiding (_≅_)
open import UF.Equiv-FunExt
open import UF.FunExt
open import UF.Logic
open import UF.Sets
open import UF.Sets-Properties
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier hiding (Ω)
open import UF.SubtypeClassifier-Properties

module Higgs.AutomorphismsOfOmega
        {𝓤 : Universe}
        (fe : Fun-Ext)
        (pe : propext 𝓤)
       where

private
 𝓤⁺ = 𝓤 ⁺

open import Higgs.InvolutionTheorem fe pe
open import Higgs.Rigidity fe pe

open Conjunction
open Implication fe
open Universal fe

can-recover-automorphism-from-its-value-at-⊤
 : (𝕗 : Aut Ω)
   (p : Ω)
 → ⌜ 𝕗 ⌝ p ＝ (p ⇔ ⌜ 𝕗 ⌝ ⊤)
can-recover-automorphism-from-its-value-at-⊤ 𝕗@(f , _) p =
 Ω-ext' pe fe
  ((f p ＝ ⊤)       ≃⟨ Ω-automorphism-swap-≃ 𝕗 ⟩
   (f ⊤ ＝ p)       ≃⟨ ≃-sym (⇔-equiv-to-＝ pe (f ⊤) p) ⟩
   ((f ⊤ ⇔ p) ＝ ⊤) ≃⟨ transport-≃ (_＝ ⊤) (⇔-sym pe (f ⊤) p) ⟩
   ((p ⇔ f ⊤) ＝ ⊤) ■)

\end{code}

The Higgs object ℍ as defined by Johnstone in [1].

\begin{code}

is-widespread : Ω → 𝓤⁺ ̇
is-widespread r = (p : Ω) → ((p ⇔ r) ⇔ r) ＝ p

being-widespread-is-prop : (r : Ω) → is-prop (is-widespread r)
being-widespread-is-prop r = Π-is-prop fe (λ p → Ω-is-set fe pe)

ℍ : 𝓤⁺ ̇
ℍ = Σ r ꞉ Ω , is-widespread r

⟪_⟫ : ℍ → Ω
⟪ r , _ ⟫ = r

⟪_⟫-is-widespread : (x : ℍ) → is-widespread ⟪ x ⟫
⟪ _ , i ⟫-is-widespread = i

ℍ-is-set : is-set ℍ
ℍ-is-set = subsets-of-sets-are-sets
            Ω
            is-widespread
            (Ω-is-set fe pe)
            (λ {r} → being-widespread-is-prop r)

to-ℍ-＝ : (r s : Ω) {i : is-widespread r} {j : is-widespread s}
       → r ＝ s
       → (r , i) ＝[ ℍ ] (s , j)
to-ℍ-＝ r s {i} {j} = to-subtype-＝ being-widespread-is-prop

to-ℍ-＝' : (x@(r , i) y@(s , j) : ℍ)
         → (r holds ↔ s holds)
         → x ＝ y
to-ℍ-＝' (r , i) (s , j) (f , g) = to-ℍ-＝ r s (Ω-extensionality pe fe f g)

\end{code}

The equality of the Higgs object has values in 𝓤⁺, but is equivalent
to an equality with values in 𝓤 and hence in Ω.

\begin{code}

_＝ₕ_ : ℍ → ℍ → Ω
(p , p-is-ws) ＝ₕ (q , q-is-ws) = p ⇔ q

infix 4 _＝ₕ_

＝ₕ-agrees-with-＝ : (x y : ℍ) → ((x ＝ₕ y) holds) ≃ (x ＝ y)
＝ₕ-agrees-with-＝ x@(p , p-is-ws) y@(q , q-is-ws)
 = logically-equivalent-props-are-equivalent
    (holds-is-prop (x ＝ₕ y))
    ℍ-is-set
    (to-ℍ-＝' x y)
    (λ (e : x ＝ y) → idtofun _ _ (ap (_holds ∘ ⟪_⟫) e) ,
                      idtofun _ _ (ap (_holds ∘ ⟪_⟫) (e ⁻¹)))

Ω-automorphisms-are-⇔-embeddings : (𝕗 : Aut Ω)
                                   (p q : Ω)
                                 → (p ⇔ q) ＝ (⌜ 𝕗 ⌝ p ⇔ ⌜ 𝕗 ⌝ q)
Ω-automorphisms-are-⇔-embeddings 𝕗@(f , f-is-equiv) p q =
 Ω-ext' pe fe
  (((p ⇔ q) ＝ ⊤)     ≃⟨ I ⟩
   (p ＝ q)           ≃⟨ II ⟩
   (f p ＝ f q)       ≃⟨ III ⟩
   ((f p ⇔ f q) ＝ ⊤) ■)
  where
   I   = ⇔-equiv-to-＝ pe p q
   II  = embedding-criterion-converse' f (equivs-are-embeddings' 𝕗) p q
   III = ≃-sym (⇔-equiv-to-＝ pe (f p) (f q))

eval-at-⊤-is-widespread : (𝕗 : Aut Ω) → is-widespread (eval-at-⊤ 𝕗)
eval-at-⊤-is-widespread 𝕗@(f , _) p = II
 where
  I = p ⇔ ⊤           ＝⟨ I₀ ⟩
      f p ⇔ f ⊤       ＝⟨ I₁ ⟩
      (p ⇔ f ⊤) ⇔ f ⊤ ∎
   where
    I₀ = Ω-automorphisms-are-⇔-embeddings 𝕗 p ⊤
    I₁ = ap (_⇔ f ⊤) (can-recover-automorphism-from-its-value-at-⊤ 𝕗 p)

  II : ((p ⇔ f ⊤) ⇔ f ⊤) ＝ p
  II = transport (_＝ p) I (⊤-⇔-neutral pe p)

Aut-Ω-to-ℍ : Aut Ω → ℍ
Aut-Ω-to-ℍ 𝕗 = eval-at-⊤ 𝕗 , eval-at-⊤-is-widespread 𝕗

ℍ-to-Aut-Ω : ℍ → Aut Ω
ℍ-to-Aut-Ω (r , i) = (λ p → p ⇔ r) , involutions-are-equivs _ i

η-ℍ : ℍ-to-Aut-Ω ∘ Aut-Ω-to-ℍ ∼ id
η-ℍ 𝕗@(f , f-is-equiv) = to-≃-＝ fe h
 where
  h : (λ p → p ⇔ f ⊤) ∼ f
  h p = (can-recover-automorphism-from-its-value-at-⊤ 𝕗 p)⁻¹

ε-ℍ : Aut-Ω-to-ℍ ∘ ℍ-to-Aut-Ω ∼ id
ε-ℍ (r , i) = to-ℍ-＝ (⊤ ⇔ r) r (⊤-⇔-neutral' pe r)

ℍ-to-Aut-Ω-is-equiv : is-equiv ℍ-to-Aut-Ω
ℍ-to-Aut-Ω-is-equiv = qinvs-are-equivs ℍ-to-Aut-Ω (Aut-Ω-to-ℍ , ε-ℍ , η-ℍ)

Aut-Ω-to-ℍ-is-equiv : is-equiv Aut-Ω-to-ℍ
Aut-Ω-to-ℍ-is-equiv = inverses-are-equivs ℍ-to-Aut-Ω ℍ-to-Aut-Ω-is-equiv

opaque
 ℍ-to-Aut-Ω-equivalence : ℍ ≃ Aut Ω
 ℍ-to-Aut-Ω-equivalence = ℍ-to-Aut-Ω , ℍ-to-Aut-Ω-is-equiv

\end{code}

The type Aut Ω is a group under composition, the symmetric group on Ω,
where the neutral element is the identity automorphism and the inverse
of any element is itself.  That is, Aut Ω is a boolean group, or a
group of order 2. We now show that the group structure on ℍ induced by
the above equivalence is given by logical equivalence _⇔_ with neutral
element ⊤.

\begin{code}

open import Groups.Type
open import Groups.Symmetric fe

Ωₛ : Group 𝓤⁺
Ωₛ = symmetric-group Ω (Ω-is-set fe pe)

opaque
 𝓗-construction : Σ s ꞉ Group-structure ℍ , is-hom (ℍ , s) Ωₛ ℍ-to-Aut-Ω
 𝓗-construction = transport-Group-structure Ωₛ ℍ ℍ-to-Aut-Ω ℍ-to-Aut-Ω-is-equiv

𝓗 : Group 𝓤⁺
𝓗 = ℍ , pr₁ 𝓗-construction

𝓗-to-Ωₛ-isomorphism : 𝓗 ≅ Ωₛ
𝓗-to-Ωₛ-isomorphism = ℍ-to-Aut-Ω , ℍ-to-Aut-Ω-is-equiv , pr₂ 𝓗-construction

𝓚-isomorphism-explicitly : (x : ℍ) (p : Ω)
                         → ⌜ ℍ-to-Aut-Ω x ⌝ p ＝ (p ⇔ ⟪ x ⟫)
𝓚-isomorphism-explicitly x p = refl

\end{code}

The unit of 𝓗 is ⊤ and its multiplication is logical equivalence.

\begin{code}

opaque
 unfolding 𝓗-construction

 𝓗-unit : ⟪ unit 𝓗 ⟫ ＝ ⊤
 𝓗-unit = refl

 𝓗-multiplication : (x y : ℍ) → ⟪ x ·⟨ 𝓗 ⟩ y ⟫ ＝ (⟪ x ⟫ ⇔ ⟪ y ⟫)
 𝓗-multiplication x y =
  ⟪ x ·⟨ 𝓗 ⟩ y ⟫     ＝⟨refl⟩
  (⊤ ⇔ ⟪ x ⟫) ⇔ ⟪ y ⟫ ＝⟨ ap (_⇔ ⟪ y ⟫) (⊤-⇔-neutral' pe ⟪ x ⟫) ⟩
  ⟪ x ⟫ ⇔ ⟪ y ⟫       ∎

 corollary-⊤ : is-widespread ⊤
 corollary-⊤ = ⟪ unit 𝓗 ⟫-is-widespread

𝕥 : ℍ
𝕥 = ⊤ , corollary-⊤

corollary-⇔ : (r s : Ω)
            → is-widespread r
            → is-widespread s
            → is-widespread (r ⇔ s)
corollary-⇔ r s i j = II
 where
  x y : ℍ
  x = (r , i)
  y = (s , j)

  I : ⟪ x ·⟨ 𝓗 ⟩ y ⟫ ＝ (r ⇔ s)
  I = 𝓗-multiplication x y

  II : is-widespread (r ⇔ s)
  II = transport is-widespread I ⟪ x ·⟨ 𝓗 ⟩ y ⟫-is-widespread

corollary-⇔-assoc : (r s t : Ω)
                  → is-widespread r
                  → is-widespread s
                  → is-widespread t
                  → (r ⇔ s) ⇔ t ＝ r ⇔ (s ⇔ t)
corollary-⇔-assoc r s t i j k = I
 where
  _·_ : ℍ → ℍ → ℍ
  x · y = x ·⟨ 𝓗 ⟩ y

  x y z : ℍ
  x = (r , i)
  y = (s , j)
  z = (t , k)

  I =  (r ⇔ s) ⇔ t             ＝⟨refl⟩
       (⟪ x ⟫ ⇔ ⟪ y ⟫) ⇔ ⟪ z ⟫ ＝⟨ ap (_⇔ ⟪ z ⟫) ((𝓗-multiplication _ _)⁻¹) ⟩
       ⟪ x · y ⟫ ⇔ ⟪ z ⟫       ＝⟨ (𝓗-multiplication _ _)⁻¹ ⟩
       ⟪ (x · y) · z ⟫         ＝⟨ ap ⟪_⟫ (assoc 𝓗 x y z) ⟩
       ⟪ x · (y · z) ⟫         ＝⟨ 𝓗-multiplication _ _ ⟩
       ⟪ x ⟫ ⇔ ⟪ y · z ⟫       ＝⟨ ap (⟪ x ⟫ ⇔_) (𝓗-multiplication _ _) ⟩
       ⟪ x ⟫ ⇔ (⟪ y ⟫ ⇔ ⟪ z ⟫) ＝⟨refl⟩
       r ⇔ (s ⇔ t)             ∎

\end{code}

Alternative characterization of the widespread property, as stated in
Johnstone's Elephant.

\begin{code}

open import UF.PropTrunc

module _ (pt : propositional-truncations-exist) where

 open PropositionalTruncation pt hiding (_∨_ ; ∨-elim)
 open Disjunction pt

 is-widespread' : Ω → 𝓤⁺ ̇
 is-widespread' r = (p : Ω) → (p ∨ (p ⇒ r)) holds

 widespread'-gives-widespread : (r : Ω)
                              → is-widespread' r
                              → is-widespread  r
 widespread'-gives-widespread r w' = w
  where
   I : (p : Ω)
     → (p holds + (p holds → r holds))
     → ((p ⇔ r) ⇔ r) ＝ p
   I p (inl h) =
    (p ⇔ r) ⇔ r ＝⟨ ap (λ - → (- ⇔ r) ⇔ r) I₀ ⟩
    (⊤ ⇔ r) ⇔ r ＝⟨ ap (_⇔ r) (⊤-⇔-neutral' pe r) ⟩
    r ⇔ r       ＝⟨ ⇔-refl pe r ⟩
    ⊤           ＝⟨ I₀ ⁻¹ ⟩
    p           ∎
     where
      I₀ : p ＝ ⊤
      I₀ = holds-gives-equal-⊤ pe fe p h

   I p (inr f) = Ω-ext pe fe I₁ I₂
    where
     have-f : (p ⇒ r) holds
     have-f = f

     I₁ : (p ⇔ r) ⇔ r ＝ ⊤ → p ＝ ⊤
     I₁ e₁ =
      p     ＝⟨ I₄ ⟩
      r     ＝⟨ (⇔-gives-＝ pe _ _ e₁)⁻¹ ⟩
      p ⇔ r ＝⟨ ＝-gives-⇔ pe _ _ I₄ ⟩
      ⊤     ∎
       where
        I₂ : r ⇒ (p ⇔ r) ＝ ⊤
        I₂ = ∧-elim-R pe fe _ _ e₁

        I₃ : (r ⇒ (p ⇔ r)) holds
        I₃ = equal-⊤-gives-holds _ I₂

        g : (r ⇒ p) holds
        g r-holds = ∧-Elim-R (p ⇒ r) (r ⇒ p) (I₃ r-holds) r-holds

        I₄ : p ＝ r
        I₄ = Ω-extensionality pe fe f g

     I₂ : p ＝ ⊤ → (p ⇔ r) ⇔ r ＝ ⊤
     I₂ e₂ =
      (p ⇔ r) ⇔ r ＝⟨ ap (λ - → (- ⇔ r) ⇔ r) e₂ ⟩
      (⊤ ⇔ r) ⇔ r ＝⟨ ap (_⇔ r) (⊤-⇔-neutral' pe r) ⟩
      r ⇔ r       ＝⟨ ⇔-refl pe r ⟩
      ⊤           ∎

   w : is-widespread r
   w p = ∥∥-rec (Ω-is-set fe pe) (I p) (w' p)

\end{code}

TODO. Write the above proof purely equationally. In order to do this,
first formulate and prove the equational definition of Heyting algebra
in other modules. Or to begin with, for simplicity, just prove in
UF.Logic that Ω satisfies the equations that define a lattice to be a
Heyting algebra.

\begin{code}

 widespread-gives-widespread' : (r : Ω)
                              → is-widespread  r
                              → is-widespread' r
 widespread-gives-widespread' r@(R , R-is-prop) w = IV
  where
   have-w : (p : Ω) → ((p ⇔ r) ⇔ r) ＝ p
   have-w = w

   module _ (p@(P , P-is-prop) : Ω) where

    P' : 𝓤 ̇
    P' = ∥ P + (P → R) ∥

    I : ((P' ↔ R) ↔ R) ↔ P'
    I = equal-⊤-gives-holds _ (＝-gives-⇔ pe _ _ (w (P' , ∥∥-is-prop)))

    II : (P' → R) → R
    II f = f ∣ inr (λ (π : P) → f ∣ inl π ∣) ∣

    III : P'
    III = lr-implication I
           ((λ (e : P' ↔ R) → II (lr-implication e)) ,
            (λ (ρ : R) → (λ (_ : P') → ρ) ,
                         (λ (_ : R) → ∣ inr (λ (_ : P) → ρ) ∣)))

    IV : (p ∨ (p ⇒ r)) holds
    IV = III

\end{code}
