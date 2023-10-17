Lane Biocini
21 January 2026

The universal property of PSL(2,ℤ) as an initial algebra.

An 𝓜-algebra in a group G is a pair ⟨s',r'⟩ of elements satisfying
s'² = e and r'³ = e. The universal property states that for any such
algebra, there exists a unique group homomorphism φ : PSL(2,ℤ) → G
with φ(S) = s' and φ(R) = r'.

Categorically, this says PSL(2,ℤ) is the initial object in the category
of groups equipped with an 𝓜-algebra structure, equivalently, it is the
free group on generators ⟨s,r⟩ quotiented by the relations s² = r³ = 1.

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

module Groups.ModularGroup.UniversalProperty where

open import MLTT.Spartan
open import UF.Base
open import UF.FunExt
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import Groups.Type renaming (inv to group-inv)
open import Groups.ModularGroup.Type
open import Groups.ModularGroup.Base
open import Groups.ModularGroup.Properties
open import Groups.ModularGroup.Induction
open import Groups.ModularGroup.Multiplication
open import Groups.ModularGroup.Inverse
open import Groups.ModularGroup.Group

module _ (G : Group 𝓤) where
 private
  |G| = ⟨ G ⟩
  _*_ = multiplication G
  e = unit G
  |G|-inv = group-inv G

 𝓜-alg : 𝓤 ̇
 𝓜-alg = Σ s ꞉ |G| , Σ r ꞉ |G| , (s * s ＝ e) × (r * (r * r) ＝ e)

 gen-s : 𝓜-alg → |G|
 gen-s (s , _) = s

 gen-r : 𝓜-alg → |G|
 gen-r (_ , r , _) = r

 s-order-2 : (alg : 𝓜-alg) → gen-s alg * gen-s alg ＝ e
 s-order-2 (_ , _ , p , _) = p

 r-order-3 : (alg : 𝓜-alg) → gen-r alg * (gen-r alg * gen-r alg) ＝ e
 r-order-3 (_ , _ , _ , p) = p

 gen-r² : 𝓜-alg → |G|
 gen-r² alg = gen-r alg * gen-r alg

 r²-r-is-e : (alg : 𝓜-alg) → gen-r² alg * gen-r alg ＝ e
 r²-r-is-e alg =
   gen-r² alg * gen-r alg              ＝⟨ I ⟩
   gen-r alg * (gen-r alg * gen-r alg) ＝⟨ r-order-3 alg ⟩
   e                                   ∎
  where
   I = assoc G (gen-r alg) (gen-r alg) (gen-r alg)

 r-r²-is-e : (alg : 𝓜-alg) → gen-r alg * gen-r² alg ＝ e
 r-r²-is-e = r-order-3

 Hom : 𝓤 ̇
 Hom = Σ φ ꞉ (PSL2Z → |G|) , is-hom 𝓜 G φ

 hom-s²-rule : (h : Hom) → pr₁ h S * pr₁ h S ＝ e
 hom-s²-rule (φ , φ-hom) =
   φ S * φ S   ＝⟨ φ-hom ⁻¹ ⟩
   φ (S · S)   ＝⟨ ap φ (s² E) ⟩
   φ E         ＝⟨ φ-E ⟩
   e           ∎
  where
   φ-E = homs-preserve-unit 𝓜 G φ (λ {x} {y} → φ-hom {x} {y})

 hom-r³-rule : (h : Hom) → pr₁ h R * (pr₁ h R * pr₁ h R) ＝ e
 hom-r³-rule (φ , φ-hom) =
   φ R * (φ R * φ R)     ＝⟨ ap (φ R *_) (φ-hom ⁻¹) ⟩
   φ R * φ (R · R)       ＝⟨ φ-hom ⁻¹ ⟩
   φ (R · (R · R))       ＝⟨ ap φ (·-assoc R R R ⁻¹) ⟩
   φ ((R · R) · R)       ＝⟨ ap φ (r³ E) ⟩
   φ E                   ＝⟨ φ-E ⟩
   e                     ∎
  where
   φ-E = homs-preserve-unit 𝓜 G φ (λ {x} {y} → φ-hom {x} {y})

 \end{code}

Given an 𝓜-algebra ⟨s',r'⟩ in G, we construct the canonical homomorphism
by mutual recursion on the Cayley graph structure. The uniqueness proof
uses PSL2Z-η: any homomorphism agreeing on S and R must equal this one.

\begin{code}

 module _ (alg : 𝓜-alg) where
   private
    s' = gen-s alg
    r' = gen-r alg
    r²' = gen-r² alg
    s²' = s-order-2 alg
    r³' = r-order-3 alg
    r²r' = r²-r-is-e alg
    rr²' = r-r²-is-e alg

   -- Define the hom center map by mutual recursion on S-edge/R-edge
   hmap-η : S-edge → |G|
   hmap-θ : R-edge → |G|

   hmap-η e₀         = e
   hmap-η e₁         = s'
   hmap-η (cross re) = s' * hmap-θ re

   hmap-θ (r+ se) = r' * hmap-η se
   hmap-θ (r- se) = r²' * hmap-η se

   hmap : PSL2Z → |G|
   hmap (η se) = hmap-η se
   hmap (θ re) = hmap-θ re

   hmap-E : hmap E ＝ e
   hmap-E = refl

   hmap-S : hmap S ＝ s'
   hmap-S = refl

   hmap-R : hmap R ＝ r'
   hmap-R = unit-right G r'

   hmap-R² : hmap R² ＝ r²'
   hmap-R² = unit-right G r²'

   hmap-s : (x : PSL2Z) → hmap (s x) ＝ s' * hmap x
   hmap-s (η e₀) = unit-right G s' ⁻¹
   hmap-s (η e₁) = s²' ⁻¹
   hmap-s (η (cross re)) =
     hmap (s (η (cross re)))    ＝⟨ unit-left G (hmap-θ re) ⁻¹ ⟩
     (unit G * hmap-θ re)       ＝⟨ ap (_* hmap-θ re) s²' ⁻¹ ⟩
     (s' * s') * hmap-θ re      ＝⟨ assoc G s' s' (hmap-θ re) ⟩
     (s' * (s' * hmap-θ re))    ∎
   hmap-s (θ re) = refl

   hmap-r : (x : PSL2Z) → hmap (r x) ＝ r' * hmap x
   hmap-r (η e₀) = refl
   hmap-r (η e₁) = refl
   hmap-r (η (cross re)) = refl
   hmap-r (θ (r+ se)) = assoc G r' r' (hmap-η se)
   hmap-r (θ (r- se)) =
    hmap (r (θ (r- se)))        ＝⟨ unit-left G (hmap-η se) ⁻¹ ⟩
    unit G * hmap-η se          ＝⟨ ap (_* hmap-η se) rr²' ⁻¹ ⟩
    (r' * r²') * hmap-η se      ＝⟨ assoc G r' r²' (hmap-η se) ⟩
    r' * (r²' * hmap-η se)      ∎

   hmap-r² : (x : PSL2Z) → hmap (r² x) ＝ r²' * hmap x
   hmap-r² x =
    hmap (r² x)              ＝⟨ hmap-r (r x) ⟩
    r' * hmap (r x)          ＝⟨ ap (r' *_) (hmap-r x) ⟩
    r' * (r' * hmap x)       ＝⟨ assoc G r' r' (hmap x) ⁻¹ ⟩
    r²' * hmap x             ∎

   -- show hmap satisfies our definition of hom
   hmap-is-hom : is-hom 𝓜 G hmap
   hmap-is-hom {x} {y} = PSL2Z-gen-ind base ind-s ind-r x y
    where
     base : (y : PSL2Z) → hmap (E · y) ＝ hmap E * hmap y
     base y = unit-left G (hmap y) ⁻¹

     ind-s : (x : PSL2Z)
           → ((y : PSL2Z) → hmap (x · y) ＝ hmap x * hmap y)
           → (y : PSL2Z) → hmap ((s x) · y) ＝ hmap (s x) * hmap y
     ind-s x ih y =
      hmap ((s x) · y)         ＝⟨ ap hmap (·-s-left x y) ⟩
      hmap (s (x · y))         ＝⟨ hmap-s (x · y) ⟩
      s' * hmap (x · y)        ＝⟨ ap (s' *_) (ih y) ⟩
      s' * (hmap x * hmap y)   ＝⟨ assoc G s' (hmap x) (hmap y) ⁻¹ ⟩
      (s' * hmap x) * hmap y   ＝⟨ ap (_* hmap y) (hmap-s x ⁻¹) ⟩
      hmap (s x) * hmap y      ∎

     ind-r : (x : PSL2Z)
           → ((y : PSL2Z) → hmap (x · y) ＝ hmap x * hmap y)
           → (y : PSL2Z) → hmap ((r x) · y) ＝ hmap (r x) * hmap y
     ind-r x ih y =
      hmap ((r x) · y)         ＝⟨ ap hmap (·-r-left x y) ⟩
      hmap (r (x · y))         ＝⟨ hmap-r (x · y) ⟩
      r' * hmap (x · y)        ＝⟨ ap (r' *_) (ih y) ⟩
      r' * (hmap x * hmap y)   ＝⟨ assoc G r' (hmap x) (hmap y) ⁻¹ ⟩
      (r' * hmap x) * hmap y   ＝⟨ ap (_* hmap y) (hmap-r x ⁻¹) ⟩
      hmap (r x) * hmap y      ∎

   hmap-preserves-inv : (x : PSL2Z) → hmap (inv x) ＝ |G|-inv (hmap x)
   hmap-preserves-inv =
    homs-preserve-invs 𝓜 G hmap (λ {x} {y} → hmap-is-hom {x} {y})

   hmap-unique : (φ : PSL2Z → |G|)
                 → is-hom 𝓜 G φ
                 → φ S ＝ s'
                 → φ R ＝ r'
                 → φ ∼ hmap
   hmap-unique φ φ-hom φ-S φ-R =
    PSL2Z-η (s' *_) (r' *_) φ hmap base φ-s hmap-s φ-r hmap-r
    where
     φ-E : φ E ＝ e
     φ-E = homs-preserve-unit 𝓜 G φ (λ {x} {y} → φ-hom {x} {y})

     base : φ E ＝ hmap E
     base = φ-E

     φ-s : (x : PSL2Z) → φ (s x) ＝ s' * φ x
     φ-s x =
      φ (s x)     ＝⟨ φ-hom ⟩
      φ S * φ x   ＝⟨ ap (_* φ x) φ-S ⟩
      s' * φ x    ∎

     φ-r : (x : PSL2Z) → φ (r x) ＝ r' * φ x
     φ-r x =
      φ (r x)     ＝⟨ φ-hom ⟩
      φ R * φ x   ＝⟨ ap (_* φ x) φ-R ⟩
      r' * φ x    ∎

\end{code}

The universal property: the type of homomorphisms respecting the
algebra is contractible (has exactly one element). This requires
function extensionality to identify homotopic maps.

First we ask that any candidate hom respects the generators.

\begin{code}

   respects-gen : Hom → 𝓤 ̇
   respects-gen (φ , _) = (φ S ＝ s') × (φ R ＝ r')

   module _ (fe : Fun-Ext) where
    private
     canonical-hom : Hom
     canonical-hom = hmap , (λ {x} {y} → hmap-is-hom {x} {y})

     canonical-respecs-gen : respects-gen canonical-hom
     canonical-respecs-gen = refl , hmap-R

\end{code}

Then we show that any homomorphism respecting the algebra equals the
canonical one.

\begin{code}

     hom-unique : (h : Hom) → respects-gen h → canonical-hom ＝ h
     hom-unique (φ , φ-hom) (φ-S , φ-R) =
       to-subtype-＝
         (being-hom-is-prop fe 𝓜 G)
         (dfunext fe
           (λ x → hmap-unique φ (λ {a} {b} → φ-hom {a} {b}) φ-S φ-R x ⁻¹))

    universal : ∃! h ꞉ Hom , respects-gen h
    universal = (canonical-hom , canonical-respecs-gen) ,
                (λ (h , r) → to-subtype-＝
                  (λ h' → ×-is-prop (groups-are-sets G) (groups-are-sets G))
                   (hom-unique h r))

\end{code}
