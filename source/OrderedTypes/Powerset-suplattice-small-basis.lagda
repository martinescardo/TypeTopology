\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module OrderedTypes.Powerset-suplattice-small-basis
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
       where

private
 fe' : FunExt
 fe' 𝓤 𝓥 = fe {𝓤} {𝓥}

open import MLTT.Spartan
open import UF.Embeddings
open import UF.Equiv
open import UF.Logic
open import UF.Powerset-MultiUniverse
open import UF.Retracts
open import UF.Sets
open import UF.Sets-Properties
open import UF.Size
open import UF.SmallnessProperties
open import UF.Subsingletons-Properties
open import UF.SubtypeClassifier
open import OrderedTypes.SupLattice pt fe
open import OrderedTypes.SupLattice-SmallBasis pt fe

open AllCombinators pt fe
open PropositionalTruncation pt hiding (_∨_)
open import Locales.Frame pt fe hiding (⟨_⟩ ; join-of ; rel-syntax)
open import Slice.Family

\end{code}

We show that the powerset of any given small type A is itself a sup-lattice with
small basis. To do this we first need to define the truncated singleton
construction and show that it has the proper characterization of the singleton.

\begin{code}

module _ (A : 𝓤 ̇) where

 open singleton-subsets
 open unions-of-small-families pt 𝓤 𝓤 A
 open PropositionalSubsetInclusionNotation fe
 open Joins {𝓤 ⁺} {𝓤} {𝓟 {𝓤} A} _⊆ₚ_

 𝓟-sup-lattice : Sup-Lattice (𝓤 ⁺) 𝓤 𝓤
 𝓟-sup-lattice
  = (𝓟 {𝓤} A , (_⊆ₚ_ , sup) , (par-ord , suprema))
  where
   sup : Fam 𝓤 (𝓟 A) → 𝓟 {𝓤} A
   sup (S , s) a = ⋃ s a
   par-ord : is-partial-order (𝓟 A) _⊆ₚ_
   par-ord = ((⊆-refl , ⊆-trans) , subset-extensionality pe fe)
   suprema : (S : Fam 𝓤 (𝓟 {𝓤} A)) → ((sup S) is-lub-of S) holds
   suprema (S , s)
    = (⋃-is-upperbound s , λ (U , O) → ⋃-is-lowerbound-of-upperbounds s U O)
 
 ❴_❵ₜᵣ : A → 𝓟 {𝓤} A
 ❴ x ❵ₜᵣ = λ y → (∥ x ＝ y ∥ , ∥∥-is-prop)

 ∈-❴❵ₜᵣ : {x : A} → x ∈ ❴ x ❵ₜᵣ
 ∈-❴❵ₜᵣ {x} = ∣ refl ∣

 ❴❵ₜᵣ-subset-characterization : {x : A} (S : 𝓟 {𝓥} A) → x ∈ S ↔ ❴ x ❵ₜᵣ ⊆ S
 ❴❵ₜᵣ-subset-characterization {𝓥} {x} S = ⦅⇒⦆ , ⦅⇐⦆
  where
   ⦅⇒⦆ : x ∈ S → ❴ x ❵ₜᵣ ⊆ S
   ⦅⇒⦆ x∈S y = ∥∥-rec (holds-is-prop (S y)) (λ p → transport (_∈ S) p x∈S)
   ⦅⇐⦆ : ❴ x ❵ₜᵣ ⊆ S → x ∈ S
   ⦅⇐⦆ γ = γ x ∣ refl ∣

 basis-char : (S : 𝓟 {𝓤} A)
            → ⋃ (↓ᴮ-inclusion 𝓟-sup-lattice ❴_❵ₜᵣ S) ＝ S
 basis-char S = subset-extensionality pe fe I II
  where
   I : ⋃ (↓ᴮ-inclusion 𝓟-sup-lattice ❴_❵ₜᵣ S) ⊆ S
   I x = ∥∥-rec (holds-is-prop (S x))
          (λ ((a , a∈↓S) , o)
            → ∥∥-rec (holds-is-prop (S x))
               (λ p → transport (_∈ S) p (a∈↓S a ∈-❴❵ₜᵣ)) o)
   II : S ⊆ ⋃ (↓ᴮ-inclusion 𝓟-sup-lattice ❴_❵ₜᵣ S)
   II x x∈S
    = ∣ (x , pr₁ (❴❵ₜᵣ-subset-characterization {_} {x} S) x∈S) , ∈-❴❵ₜᵣ ∣

 ❴❵ₜᵣ-is-basis : is-basis 𝓟-sup-lattice ❴_❵ₜᵣ
 ❴❵ₜᵣ-is-basis
  = record{≤-is-small = λ S a → ((❴ a ❵ₜᵣ ⊆ S) , ≃-refl (❴ a ❵ₜᵣ ⊆ S)) ;
           ↓-is-sup
            = λ S → transport
                     (λ - → (- is-lub-of (↓ᴮ 𝓟-sup-lattice ❴_❵ₜᵣ S
                                   , ↓ᴮ-inclusion 𝓟-sup-lattice ❴_❵ₜᵣ S)) holds)
                     (basis-char S)
                     (⋃-is-upperbound (↓ᴮ-inclusion 𝓟-sup-lattice ❴_❵ₜᵣ S)
                      , λ (U , O) → ⋃-is-lowerbound-of-upperbounds
                                    (↓ᴮ-inclusion 𝓟-sup-lattice ❴_❵ₜᵣ S) U O) }

\end{code}

We will now observe that a sup lattice L, with small basis B, gives L as a
retraction of 𝓟 B.

           L --- ↓ᴮ ---> 𝓟 B --- ⋁ ---> L
            \                          ^
             \                        /
               -------- id ----------

\begin{code}

module sup-lattice-powerset-retract
         (L : Sup-Lattice 𝓤 𝓣 𝓥)
         {B : 𝓥 ̇} (β : B → ⟨ L ⟩) (h : is-basis L β)
       where

 open is-basis h

 ↓-map : ⟨ L ⟩ → 𝓟 {𝓥} B
 ↓-map x b = ((b ≤ᴮ x) , ≤ᴮ-is-prop-valued)

 ↓-monotone : (x y : ⟨ L ⟩)
            → (x ≤⟨ L ⟩ y) holds
            → ↓-map x ⊆ ↓-map y
 ↓-monotone x y x≤y b b∈↓x = ≤ᴮ-≤-to-≤ᴮ b∈↓x x≤y 

 ⋁-map : 𝓟 {𝓥} B → ⟨ L ⟩
 ⋁-map S = ⋁⟨ L ⟩ (𝕋 S , β ∘ 𝕋-to-carrier S)

 ⋁-monotone : (S T : 𝓟 {𝓥} B)
            → S ⊆ T
            → (⋁-map S ≤⟨ L ⟩ ⋁-map T) holds
 ⋁-monotone S T S⊆T = joins-preserve-containment L β S T S⊆T

 ⋁∘↓∼id
  : ⋁-map ∘ ↓-map ∼ id
 ⋁∘↓∼id x = is-supᴮ' x ⁻¹

 sup-lattice-retract-of-pow : retract ⟨ L ⟩ of 𝓟 {𝓥} B
 sup-lattice-retract-of-pow = (⋁-map , ↓-map , ⋁∘↓∼id)

\end{code}

We now show in the presence of Ω-resizing any small generated sup lattice
is also small.

\begin{code}

 sup-lattice-is-small : Ω-resizing 𝓥
                      → ⟨ L ⟩ is 𝓥 small
 sup-lattice-is-small omega-res
  = embedded-retract-is-small sup-lattice-retract-of-pow
     (sections-into-sets-are-embeddings ↓-map (⋁-map , ⋁∘↓∼id)
      (powersets-are-sets fe pe))
     (Π-is-small fe' (B , ≃-refl B) (λ _ → omega-res))

\end{code}

Now we will investigate the connection between least (pre) fixed points of
monotone maps on small generated sup lattices and monotone operators on the
power set.

\begin{code}

module _ (𝓤 : Universe) (A : 𝓤 ̇) where

 monotone-operator-has-least-pre-fixed-point
  : (f : 𝓟 {𝓤} A → 𝓟 {𝓤} A)
  → is-monotone-endomap (𝓟-sup-lattice A) f
  → (𝓤 ⁺) ̇
 monotone-operator-has-least-pre-fixed-point f f-mono
  = Σ S ꞉ 𝓟 {𝓤} A , f S ⊆ S × ((T : 𝓟 {𝓤} A) → f T ⊆ T → S ⊆ T)

 monotone-operator-LPFP : (𝓤 ⁺) ̇
 monotone-operator-LPFP
  = (f : 𝓟 {𝓤} A → 𝓟 {𝓤} A) (f-mono : is-monotone-endomap (𝓟-sup-lattice A) f)
  → monotone-operator-has-least-pre-fixed-point f f-mono

 module _ (f : 𝓟 {𝓤} A → 𝓟 {𝓤} A)
          (f-mono : is-monotone-endomap (𝓟-sup-lattice A) f)
        where

  mon-op-LPFP-point : monotone-operator-LPFP → 𝓟 {𝓤} A
  mon-op-LPFP-point m = pr₁ (m f f-mono)

  mon-op-LPFP-pre-fixed
   : (m : monotone-operator-LPFP)
   → f (mon-op-LPFP-point m) ⊆ mon-op-LPFP-point m
  mon-op-LPFP-pre-fixed m = pr₁ (pr₂ (m f f-mono))

  mon-op-LPFP-least
   : (m : monotone-operator-LPFP)
   → (T : 𝓟 {𝓤} A)
   → f T ⊆ T
   → mon-op-LPFP-point m ⊆ T
  mon-op-LPFP-least m = pr₂ (pr₂ (m f f-mono))

module _ (𝓤 𝓣 𝓥 : Universe)
         (L : Sup-Lattice 𝓤 𝓣 𝓥)
         {B : 𝓥 ̇} (β : B → ⟨ L ⟩) (h : is-basis L β)
       where

 open is-basis h

 monotone-map-has-least-pre-fixed-point
  : (f : ⟨ L ⟩ → ⟨ L ⟩)
  → is-monotone-endomap L f
  → 𝓤 ⊔ 𝓣 ̇
 monotone-map-has-least-pre-fixed-point f mono-f
  = Σ p ꞉ ⟨ L ⟩ , (f p ≤⟨ L ⟩ p) holds
                × ((q : ⟨ L ⟩) → (f q ≤⟨ L ⟩ q) holds → (p ≤⟨ L ⟩ q) holds)

 monotone-map-LPFP : 𝓤 ⊔ 𝓣 ̇
 monotone-map-LPFP
  = (f : ⟨ L ⟩ → ⟨ L ⟩) (f-mono : is-monotone-endomap L f)
  → monotone-map-has-least-pre-fixed-point f f-mono

\end{code}

Clearly monotone-map-LPFP 𝓤⁺ 𝓤 𝓤 implies monotone-operator-LPFP 𝓤.

\begin{code}

montone-map-implies-monotone-operator-LPFP
 : (A : 𝓤 ̇)
 → monotone-map-LPFP (𝓤 ⁺) 𝓤 𝓤 (𝓟-sup-lattice A) (❴_❵ₜᵣ A) (❴❵ₜᵣ-is-basis A)
 → monotone-operator-LPFP 𝓤 A
montone-map-implies-monotone-operator-LPFP A mon-map-LPFP = mon-map-LPFP

\end{code}

We also have that monotone-operator-LPFP 𝓥 implies monotone-map-LPFP 𝓤 𝓣 𝓥.

\begin{code}

monotone-operator-implies-monotone-map-LPFP
 : (L : Sup-Lattice 𝓤 𝓣 𝓥)
   {B : 𝓥 ̇} (β : B → ⟨ L ⟩) (h : is-basis L β)
 → monotone-operator-LPFP 𝓥 B
 → monotone-map-LPFP 𝓤 𝓣 𝓥 L β h
monotone-operator-implies-monotone-map-LPFP
 {𝓤} {𝓣} {𝓥} L {B} β h mon-op-LPFP f f-mono = (p , fp≤p , p≤any)
 where
  open sup-lattice-powerset-retract L β h
  open is-basis h
  open equational-reasoning-≤ L
  mon-op : 𝓟 {𝓥} B → 𝓟 {𝓥} B
  mon-op = ↓-map ∘ f ∘ ⋁-map
  mon-op-is-monotone : is-monotone-endomap (𝓟-sup-lattice B) mon-op
  mon-op-is-monotone
   = ∘-presererves-monotone
      (𝓟-sup-lattice B) L (𝓟-sup-lattice B) ⋁-map (↓-map ∘ f) ⋁-monotone
       (∘-presererves-monotone L L (𝓟-sup-lattice B) f ↓-map f-mono ↓-monotone)
  S : 𝓟 {𝓥} B
  S = mon-op-LPFP-point 𝓥 B mon-op mon-op-is-monotone mon-op-LPFP
  mon-opS⊆S : mon-op S ⊆ S
  mon-opS⊆S = mon-op-LPFP-pre-fixed 𝓥 B mon-op mon-op-is-monotone mon-op-LPFP
  S⊆any : (T : 𝓟 {𝓥} B) → (mon-op T ⊆ T) → S ⊆ T
  S⊆any = mon-op-LPFP-least 𝓥 B mon-op mon-op-is-monotone mon-op-LPFP
  p : ⟨ L ⟩
  p = ⋁-map S
  fp≤p : (f p ≤⟨ L ⟩ p) holds
  fp≤p = f p                ≤[ ＝-to-≤ L (⋁∘↓∼id (f p) ⁻¹) ]
         ⋁-map (mon-op S)   ≤[ ⋁-monotone (mon-op S) S mon-opS⊆S ]
         p                  ▣
  p≤any : (q : ⟨ L ⟩) → (f q ≤⟨ L ⟩ q) holds → (p ≤⟨ L ⟩ q) holds
  p≤any q fq≤q = ⋁-map S          ≤[ ⋁-monotone S (↓-map q) II ]
                 ⋁-map (↓-map q)  ≤[ ＝-to-≤ L (⋁∘↓∼id q) ]
                 q                ▣
   where
    I : mon-op (↓-map q) ⊆ ↓-map q
    I = ⊆-trans (mon-op (↓-map q)) (↓-map (f q)) (↓-map q)
         (pr₁ (⊆-refl-consequence (mon-op (↓-map q)) (↓-map (f q))
                (ap (↓-map ∘ f) (⋁∘↓∼id q))))
         (↓-monotone (f q) q fq≤q)
    II : S ⊆ ↓-map q
    II = S⊆any (↓-map q) I

\end{code}


