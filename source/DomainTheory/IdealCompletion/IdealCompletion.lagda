Tom de Jong, 26 February 2020
Minor updates on 28 January 2022

We construct the rounded ideal completion of an abstract basis, cf. Section
2.2.6 in Domain Theory by Abramsky and Jung.

Further properties and developments are in the file IdealCompletion-Properties.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (J)

open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module DomainTheory.IdealCompletion.IdealCompletion
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (𝓥 : Universe) -- universe where the index types for directedness
                       -- completeness live
       where

open import DomainTheory.Basics.Dcpo pt fe 𝓥
open import OrderedTypes.Poset fe
open import UF.Powerset
open import UF.Sets
open import UF.Sets-Properties
open import UF.SubtypeClassifier
open import UF.Subsingletons-FunExt

open PosetAxioms

open PropositionalTruncation pt

module Ideals
        {P : 𝓤 ̇ }
        (_≺_ : P → P → 𝓥 ⊔ 𝓣 ̇ )
        (≺-prop-valued : {p q : P} → is-prop (p ≺ q))
        (INT₂ : {q₀ q₁ p : P} → q₀ ≺ p → q₁ ≺ p
              → ∃ r ꞉ P , q₀ ≺ r × q₁ ≺ r × r ≺ p)
        (INT₀ : (p : P) → ∃ q ꞉ P , q ≺ p)
        (≺-trans : {p q r : P} → p ≺ q → q ≺ r → p ≺ r)
       where

 is-lowerset : (P → Ω (𝓥 ⊔ 𝓣)) → 𝓥 ⊔ 𝓤 ⊔ 𝓣 ̇
 is-lowerset A = (p q : P) → p ≺ q → q ∈ A → p ∈ A

 being-lowerset-is-prop : (I :  P → Ω (𝓥 ⊔ 𝓣)) → is-prop (is-lowerset I)
 being-lowerset-is-prop I = Π₄-is-prop fe (λ p q l i → ∈-is-prop I p)

 is-inhabited-set : (P → Ω (𝓥 ⊔ 𝓣)) → 𝓤 ⊔ 𝓥 ⊔ 𝓣 ̇
 is-inhabited-set A = ∃ p ꞉ P , p ∈ A

 being-inhabited-set-is-prop : (I : P → Ω (𝓥 ⊔ 𝓣))
                             → is-prop (is-inhabited-set I)
 being-inhabited-set-is-prop I = ∥∥-is-prop

 is-semidirected-set : (P → Ω (𝓥 ⊔ 𝓣)) → 𝓥 ⊔ 𝓤 ⊔ 𝓣 ̇
 is-semidirected-set A = (p q : P) → p ∈ A → q ∈ A
                          → ∃ r ꞉ P , r ∈ A
                          × p ≺ r × q ≺ r

 being-semidirected-set-is-prop : (I : P → Ω (𝓥 ⊔ 𝓣))
                                → is-prop (is-semidirected-set I)
 being-semidirected-set-is-prop I = Π₄-is-prop fe (λ p q i j → ∃-is-prop)

 is-directed-set : (P → Ω (𝓥 ⊔ 𝓣)) → 𝓥 ⊔ 𝓤 ⊔ 𝓣 ̇
 is-directed-set A = is-inhabited-set A × is-semidirected-set A

 being-directed-set-is-prop : (I : P → Ω (𝓥 ⊔ 𝓣))
                            → is-prop (is-directed-set I)
 being-directed-set-is-prop I =
  ×-is-prop
   (being-inhabited-set-is-prop I)
   (being-semidirected-set-is-prop I)

 directed-sets-are-inhabited : (A : P → Ω (𝓥 ⊔ 𝓣))
                             → is-directed-set A → is-inhabited-set A
 directed-sets-are-inhabited A = pr₁

 directed-sets-are-semidirected : (A : P → Ω (𝓥 ⊔ 𝓣))
                                → is-directed-set A
                                → is-semidirected-set A
 directed-sets-are-semidirected A = pr₂

 is-ideal : (P → Ω (𝓥 ⊔ 𝓣)) → 𝓥 ⊔ 𝓤 ⊔ 𝓣 ̇
 is-ideal I = is-lowerset I × is-directed-set I

 being-ideal-is-prop : (I : P → Ω (𝓥 ⊔ 𝓣)) → is-prop (is-ideal I)
 being-ideal-is-prop I =
  ×-is-prop
   (being-lowerset-is-prop I)
   (being-directed-set-is-prop I)

 ideals-are-lowersets : (I : P → Ω (𝓥 ⊔ 𝓣)) → is-ideal I → is-lowerset I
 ideals-are-lowersets I = pr₁

 ideals-are-directed-sets : (I : P → Ω (𝓥 ⊔ 𝓣))
                          → is-ideal I → is-directed-set I
 ideals-are-directed-sets I = pr₂

 ideals-are-inhabited : (I : P → Ω (𝓥 ⊔ 𝓣))
                      → is-ideal I → is-inhabited-set I
 ideals-are-inhabited I ι =
  directed-sets-are-inhabited I (ideals-are-directed-sets I ι)

 ideals-are-semidirected : (I : P → Ω (𝓥 ⊔ 𝓣))
                         → is-ideal I → is-semidirected-set I
 ideals-are-semidirected I ι =
  directed-sets-are-semidirected I (ideals-are-directed-sets I ι)

 Idl : 𝓥 ⁺ ⊔ 𝓣 ⁺ ⊔ 𝓤 ̇
 Idl = Σ I ꞉ (P → Ω (𝓥 ⊔ 𝓣)) , is-ideal I

 carrier : Idl → P → Ω (𝓥 ⊔ 𝓣)
 carrier = pr₁

 ideality : (I : Idl) → is-ideal (carrier I)
 ideality = pr₂

 _∈ᵢ_ : P → Idl → 𝓥 ⊔ 𝓣 ̇
 p ∈ᵢ I = p ∈ carrier I

 _⊑_ : Idl → Idl → 𝓥 ⊔ 𝓤 ⊔ 𝓣 ̇
 I ⊑ J = carrier I ⊆ carrier J

 Idl-∐ : {𝓐 : 𝓥 ̇ } (α : 𝓐 → Idl) → is-directed _⊑_ α → Idl
 Idl-∐ {𝓐} α δ = (∐α , ls , inh , ε)
  where
   open unions-of-small-families pt 𝓥 𝓣 P
   ∐α : P → Ω (𝓥 ⊔ 𝓣)
   ∐α = ⋃ (carrier ∘ α)
   ls : is-lowerset ∐α
   ls p q l = ∥∥-functor γ
    where
     γ : (Σ a ꞉ 𝓐 , q ∈ᵢ α a) → (Σ a ꞉ 𝓐 , p ∈ᵢ α a)
     γ (a , u) = a , ideals-are-lowersets (carrier (α a)) (ideality (α a))
                     p q l u
   inh : ∃ p ꞉ P , p ∈ ∐α
   inh = ∥∥-rec ∥∥-is-prop γ (inhabited-if-directed _⊑_ α δ)
    where
     γ : 𝓐 → ∃ p ꞉ P , p ∈ ∐α
     γ a = ∥∥-functor h inh'
      where
       inh' : is-inhabited-set (carrier (α a))
       inh' = directed-sets-are-inhabited (carrier (α a))
              (ideals-are-directed-sets (carrier (α a)) (ideality (α a)))
       h : (Σ p ꞉ P , p ∈ᵢ α a) → (Σ p ꞉ P , p ∈ ∐α)
       h (p , u) = p , ∣ a , u ∣
   ε : is-semidirected-set ∐α
   ε p q i j = ∥∥-rec₂ ∥∥-is-prop γ i j
    where
     γ : (Σ a ꞉ 𝓐 , p ∈ᵢ α a)
       → (Σ b ꞉ 𝓐 , q ∈ᵢ α b)
       → ∃ r ꞉ P , r ∈ ∐α × p ≺ r × q ≺ r
     γ (a , ia) (b , jb) =
      ∥∥-rec ∥∥-is-prop g (semidirected-if-directed _⊑_ α δ a b)
       where
        g : (Σ c ꞉ 𝓐 , α a ⊑ α c × α b ⊑ α c)
          → ∃ r ꞉ P , r ∈ ∐α × p ≺ r × q ≺ r
        g (c , l , m) = do
         (r , k , u , v) ← directed-sets-are-semidirected (carrier (α c))
                           (ideals-are-directed-sets (carrier (α c))
                            (ideality (α c)))
                           p q ic jc
         ∣ r , ∣ c , k ∣ , u , v ∣
         where
         ic : p ∈ᵢ α c
         ic = l p ia
         jc : q ∈ᵢ α c
         jc = m q jb

 Idl-DCPO : DCPO {𝓥 ⁺ ⊔ 𝓣 ⁺ ⊔ 𝓤} {𝓥 ⊔ 𝓤 ⊔ 𝓣}
 Idl-DCPO = Idl , _⊑_ , γ
  where
   γ : dcpo-axioms _⊑_
   γ = pa , dc
    where
     pa : poset-axioms _⊑_
     pa = s , pv , r , t , a
      where
       s : is-set Idl
       s = subtypes-of-sets-are-sets' carrier
            (pr₁-lc λ {I} → being-ideal-is-prop I)
            (powersets-are-sets'' fe fe pe)
       pv : is-prop-valued _⊑_
       pv I J = ⊆-is-prop' fe fe (carrier I) (carrier J)
       r : (I : Idl) → I ⊑ I
       r I = ⊆-refl' (carrier I)
       t : is-transitive _⊑_
       t I J K = ⊆-trans' (carrier I) (carrier J) (carrier K)
       a : is-antisymmetric _⊑_
       a I J u v = to-subtype-＝
                    (λ K → being-ideal-is-prop K)
                    (subset-extensionality'' pe fe fe u v)
     dc : is-directed-complete _⊑_
     dc 𝓐 α δ = (Idl-∐ α δ) , ub , lb
      where
       ub : (a : 𝓐) → α a ⊑ Idl-∐ α δ
       ub a p p-in-a = ∣ a , p-in-a ∣
       lb : is-lowerbound-of-upperbounds _⊑_ (Idl-∐ α δ) α
       lb I ub p p-in-∐α = ∥∥-rec (∈-is-prop (carrier I) p) h p-in-∐α
        where
         h : (Σ a ꞉ 𝓐 , p ∈ᵢ α a) → p ∈ᵢ I
         h (a , q) = ub a p q

\end{code}
