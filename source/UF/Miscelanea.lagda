Martin Escardo

UF things that depend on non-UF things.

Find a better home for all of this.

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

module UF.Miscelanea where

open import MLTT.Plus-Properties
open import MLTT.Spartan
open import Naturals.Properties
open import TypeTopology.DiscreteAndSeparated
open import UF.Base
open import UF.Embeddings
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.Lower-FunExt
open import UF.Retracts
open import UF.Size
open import UF.SmallnessProperties
open import UF.Subsingletons renaming (⊤Ω to ⊤ ; ⊥Ω to ⊥)
open import UF.Subsingletons-FunExt

decidable-types-are-collapsible : {X : 𝓤 ̇ } → is-decidable X → collapsible X
decidable-types-are-collapsible (inl x) = pointed-types-are-collapsible x
decidable-types-are-collapsible (inr u) = empty-types-are-collapsible u

discrete-is-Id-collapsible : {X : 𝓤 ̇ } → is-discrete X → Id-collapsible X
discrete-is-Id-collapsible d = decidable-types-are-collapsible (d _ _)

discrete-types-are-sets : {X : 𝓤 ̇ } → is-discrete X → is-set X
discrete-types-are-sets d = Id-collapsibles-are-sets (discrete-is-Id-collapsible d)

being-isolated-is-prop : FunExt → {X : 𝓤 ̇ } (x : X) → is-prop (is-isolated x)
being-isolated-is-prop {𝓤} fe x = prop-criterion γ
 where
  γ : is-isolated x → is-prop (is-isolated x)
  γ i = Π-is-prop (fe 𝓤 𝓤)
         (λ x → sum-of-contradictory-props
                 (local-hedberg _ (λ y → decidable-types-are-collapsible (i y)) x)
                 (negations-are-props (fe 𝓤 𝓤₀))
                 (λ p n → n p))

being-isolated'-is-prop : FunExt → {X : 𝓤 ̇ } (x : X) → is-prop (is-isolated' x)
being-isolated'-is-prop {𝓤} fe x = prop-criterion γ
 where
  γ : is-isolated' x → is-prop (is-isolated' x)
  γ i = Π-is-prop (fe 𝓤 𝓤)
         (λ x → sum-of-contradictory-props
                 (local-hedberg' _ (λ y → decidable-types-are-collapsible (i y)) x)
                 (negations-are-props (fe 𝓤 𝓤₀))
                 (λ p n → n p))

being-discrete-is-prop : FunExt → {X : 𝓤 ̇ } → is-prop (is-discrete X)
being-discrete-is-prop {𝓤} fe = Π-is-prop (fe 𝓤 𝓤) (being-isolated-is-prop fe)

isolated-is-h-isolated : {X : 𝓤 ̇ } (x : X) → is-isolated x → is-h-isolated x
isolated-is-h-isolated {𝓤} {X} x i {y} = local-hedberg x (λ y → γ y (i y)) y
 where
  γ : (y : X) → is-decidable (x ＝ y) → Σ f ꞉ (x ＝ y → x ＝ y) , wconstant f
  γ y (inl p) = (λ _ → p) , (λ q r → refl)
  γ y (inr n) = id , (λ q r → 𝟘-elim (n r))

isolated-inl : {X : 𝓤 ̇ } (x : X) (i : is-isolated x) (y : X) (r : x ＝ y)
             → i y ＝ inl r
isolated-inl x i y r =
  equality-cases (i y)
   (λ (p : x ＝ y) (q : i y ＝ inl p)
      → q ∙ ap inl (isolated-is-h-isolated x i p r))
   (λ (h : x ≠ y) (q : i y ＝ inr h)
      → 𝟘-elim(h r))

isolated-inr : {X : 𝓤 ̇ }
             → funext 𝓤 𝓤₀
             → (x : X) (i : is-isolated x) (y : X) (n : x ≠ y) → i y ＝ inr n
isolated-inr fe x i y n =
  equality-cases (i y)
   (λ (p : x ＝ y) (q : i y ＝ inl p)
      → 𝟘-elim (n p))
   (λ (m : x ≠ y) (q : i y ＝ inr m)
      → q ∙ ap inr (dfunext fe (λ (p : x ＝ y) → 𝟘-elim (m p))))

\end{code}

The following variation of the above doesn't require function extensionality:

\begin{code}

isolated-inr' : {X : 𝓤 ̇ }
                (x : X) (i : is-isolated x) (y : X) (n : x ≠ y)
              → Σ m ꞉ x ≠ y , i y ＝ inr m
isolated-inr' x i y n =
  equality-cases (i y)
   (λ (p : x ＝ y) (q : i y ＝ inl p)
      → 𝟘-elim (n p))
   (λ (m : x ≠ y) (q : i y ＝ inr m)
      → m , q)

discrete-inl : {X : 𝓤 ̇ } (d : is-discrete X) (x y : X) (r : x ＝ y)
             → d x y ＝ inl r
discrete-inl d x = isolated-inl x (d x)

discrete-inr : funext 𝓤 𝓤₀
             → {X : 𝓤 ̇ }
               (d : is-discrete X)
               (x y : X)
               (n : ¬ (x ＝ y))
             → d x y ＝ inr n
discrete-inr fe d x = isolated-inr fe x (d x)

isolated-Id-is-prop : {X : 𝓤 ̇ } (x : X)
                    → is-isolated' x
                    → (y : X) → is-prop (y ＝ x)
isolated-Id-is-prop x i = local-hedberg' x (λ y → decidable-types-are-collapsible (i y))

lc-maps-reflect-isolatedness : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                             → left-cancellable f
                             → (x : X) → is-isolated (f x) → is-isolated x
lc-maps-reflect-isolatedness f l x i y = γ (i (f y))
 where
  γ : (f x ＝ f y) + ¬ (f x ＝ f y) → (x ＝ y) + ¬ (x ＝ y)
  γ (inl p) = inl (l p)
  γ (inr n) = inr (contrapositive (ap f) n)

lc-maps-reflect-discreteness : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                             → left-cancellable f
                             → is-discrete Y
                             → is-discrete X
lc-maps-reflect-discreteness f l d x =
 lc-maps-reflect-isolatedness f l x (d (f x))

embeddings-reflect-isolatedness : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                                → is-embedding f
                                → (x : X) → is-isolated (f x)
                                → is-isolated x
embeddings-reflect-isolatedness f e x i y = lc-maps-reflect-isolatedness f
                                              (embeddings-are-lc f e) x i y

equivs-reflect-isolatedness : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                            → is-equiv f
                            → (x : X) → is-isolated (f x)
                            → is-isolated x
equivs-reflect-isolatedness f e = embeddings-reflect-isolatedness f
                                   (equivs-are-embeddings f e)

embeddings-reflect-discreteness : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                                → is-embedding f
                                → is-discrete Y
                                → is-discrete X
embeddings-reflect-discreteness f e = lc-maps-reflect-discreteness f (embeddings-are-lc f e)

equivs-preserve-discreteness : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                             → is-equiv f
                             → is-discrete X
                             → is-discrete Y
equivs-preserve-discreteness f e = lc-maps-reflect-discreteness
                                     (inverse f e)
                                     (equivs-are-lc
                                        (inverse f e)
                                        (inverses-are-equivs f e))

equiv-to-discrete : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                  → X ≃ Y
                  → is-discrete X
                  → is-discrete Y
equiv-to-discrete (f , e) = equivs-preserve-discreteness f e

𝟙-is-set : is-set (𝟙 {𝓤})
𝟙-is-set = discrete-types-are-sets 𝟙-is-discrete

𝟚-is-set : is-set 𝟚
𝟚-is-set = discrete-types-are-sets 𝟚-is-discrete

ℕ-is-set : is-set ℕ
ℕ-is-set = discrete-types-are-sets ℕ-is-discrete

𝟚-to-Ω : 𝟚 → Ω 𝓤
𝟚-to-Ω ₀ = ⊥
𝟚-to-Ω ₁ = ⊤

module _ (fe : funext 𝓤 𝓤) (pe : propext 𝓤) where

 𝟚-to-Ω-is-embedding : is-embedding (𝟚-to-Ω {𝓤})
 𝟚-to-Ω-is-embedding _ (₀ , p) (₀ , q) = to-Σ-＝ (refl , Ω-is-set fe pe p q)
 𝟚-to-Ω-is-embedding _ (₀ , p) (₁ , q) = 𝟘-elim (⊥-is-not-⊤ (p ∙ q ⁻¹))
 𝟚-to-Ω-is-embedding _ (₁ , p) (₀ , q) = 𝟘-elim (⊥-is-not-⊤ (q ∙ p ⁻¹))
 𝟚-to-Ω-is-embedding _ (₁ , p) (₁ , q) = to-Σ-＝ (refl , Ω-is-set fe pe p q)

 𝟚-to-Ω-fiber : (p : Ω 𝓤) → fiber 𝟚-to-Ω p ≃ (¬ (p holds) + p holds)
 𝟚-to-Ω-fiber p =
  fiber (𝟚-to-Ω {𝓤}) p           ≃⟨ ≃-refl _ ⟩
  (Σ n ꞉ 𝟚 , 𝟚-to-Ω {𝓤} n ＝ p ) ≃⟨ I₀ ⟩
  (⊥ ＝ p) + (⊤ ＝ p)            ≃⟨ I₁ ⟩
  (¬ (p holds) + p holds)        ■
    where
     I₀ = alternative-+
     I₁ = +-cong
           (＝-flip ● equal-⊥-≃ pe fe p)
           (＝-flip ● equal-⊤-≃ pe fe p)

 𝟚-to-Ω-is-small-map : (𝟚-to-Ω {𝓤}) is 𝓤 small-map
 𝟚-to-Ω-is-small-map p = (¬ (p holds) + p holds) ,
                                   ≃-sym (𝟚-to-Ω-fiber p)

is-decidable-is-¬¬-stable : {X : 𝓤 ̇ } → is-decidable X → ¬¬-stable X
is-decidable-is-¬¬-stable (inl x) φ = x
is-decidable-is-¬¬-stable (inr u) φ = unique-from-𝟘(φ u)

¬¬-stable-is-collapsible : funext 𝓤 𝓤₀
                         → {X : 𝓤 ̇ } → ¬¬-stable X → collapsible X
¬¬-stable-is-collapsible {𝓤} fe {X} s = (f , g)
 where
  f : X → X
  f x = s(λ u → u x)

  claim₀ : (x y : X) → (u : is-empty X) → u x ＝ u y
  claim₀ x y u = unique-from-𝟘(u x)

  claim₁ : (x y : X) → (λ u → u x) ＝ (λ u → u y)
  claim₁ x y = dfunext fe (claim₀ x y)

  g : (x y : X) → f x ＝ f y
  g x y = ap s (claim₁ x y)

¬¬-separated-is-Id-collapsible : funext 𝓤 𝓤₀ → {X : 𝓤 ̇ }
                               → is-¬¬-separated X
                               → Id-collapsible X
¬¬-separated-is-Id-collapsible fe s = ¬¬-stable-is-collapsible fe (s _ _)

¬¬-separated-types-are-sets : funext 𝓤 𝓤₀ → {X : 𝓤 ̇ }
                            → is-¬¬-separated X
                            → is-set X
¬¬-separated-types-are-sets fe s =
 Id-collapsibles-are-sets (¬¬-separated-is-Id-collapsible fe s)

being-¬¬-separated-is-prop : funext 𝓤 𝓤
                           → {X : 𝓤 ̇ }
                           → is-prop (is-¬¬-separated X)
being-¬¬-separated-is-prop {𝓤} fe {X} = prop-criterion f
 where
  f : is-¬¬-separated X → is-prop (is-¬¬-separated X)
  f s = Π-is-prop fe (λ _ →
        Π-is-prop fe (λ _ →
        Π-is-prop fe (λ _ → ¬¬-separated-types-are-sets (lower-funext 𝓤 𝓤 fe) s)))

𝟚-ℕ-embedding : 𝟚 → ℕ
𝟚-ℕ-embedding ₀ = 0
𝟚-ℕ-embedding ₁ = 1

𝟚-ℕ-embedding-is-lc : left-cancellable 𝟚-ℕ-embedding
𝟚-ℕ-embedding-is-lc {₀} {₀} refl = refl
𝟚-ℕ-embedding-is-lc {₀} {₁} r    = 𝟘-elim (positive-not-zero 0 (r ⁻¹))
𝟚-ℕ-embedding-is-lc {₁} {₀} r    = 𝟘-elim (positive-not-zero 0 r)
𝟚-ℕ-embedding-is-lc {₁} {₁} refl = refl

C-B-embedding : (ℕ → 𝟚) → (ℕ → ℕ)
C-B-embedding α = 𝟚-ℕ-embedding ∘ α

C-B-embedding-is-lc : funext 𝓤₀ 𝓤₀ → left-cancellable C-B-embedding
C-B-embedding-is-lc fe {α} {β} p = dfunext fe h
 where
  h : (n : ℕ) → α n ＝ β n
  h n = 𝟚-ℕ-embedding-is-lc (ap (λ - → - n) p)

𝟚-retract-of-ℕ : retract 𝟚 of ℕ
𝟚-retract-of-ℕ = r , s , rs
 where
  r : ℕ → 𝟚
  r 0        = ₀
  r (succ n) = ₁

  s : 𝟚 → ℕ
  s ₀ = 0
  s ₁ = 1

  rs : r ∘ s ∼ id
  rs ₀ = refl
  rs ₁ = refl

\end{code}

Added 19th Feb 2020:

\begin{code}

open import UF.Embeddings

maps-of-props-into-h-isolated-points-are-embeddings :

   {P : 𝓤 ̇ } {X : 𝓥 ̇ } (f : P → X)
 → is-prop P
 → ((p : P) → is-h-isolated (f p))
 → is-embedding f

maps-of-props-into-h-isolated-points-are-embeddings f i j q (p , s) (p' , s') =
 to-Σ-＝ (i p p' , j p' _ s')

maps-of-props-into-isolated-points-are-embeddings : {P : 𝓤 ̇ } {X : 𝓥 ̇ }
                                                    (f : P → X)
                                                  → is-prop P
                                                  → ((p : P) → is-isolated (f p))
                                                  → is-embedding f
maps-of-props-into-isolated-points-are-embeddings f i j =
 maps-of-props-into-h-isolated-points-are-embeddings f i
  (λ p → isolated-is-h-isolated (f p) (j p))

global-point-is-embedding : {X : 𝓤 ̇  } (f : 𝟙 {𝓥} → X)
                          → is-h-isolated (f ⋆)
                          → is-embedding f
global-point-is-embedding f h =
 maps-of-props-into-h-isolated-points-are-embeddings
  f 𝟙-is-prop h'
   where
    h' : (p : 𝟙) → is-h-isolated (f p)
    h' ⋆ = h

\end{code}

Added 30 Jul 2023.

\begin{code}

constant-maps-are-h-isolated : funext 𝓤 𝓥
                             → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (y₀ : Y)
                             → is-h-isolated y₀
                             → is-h-isolated (λ (x : X) → y₀)
constant-maps-are-h-isolated fe y₀ y₀-iso {f} = II
 where
  I = ((λ x → y₀) ＝ f) ≃⟨ ≃-funext fe (λ x → y₀) f ⟩
       (λ x → y₀) ∼ f   ■

  II : is-prop ((λ x → y₀) ＝ f)
  II = equiv-to-prop I (Π-is-prop fe (λ _ → y₀-iso))

\end{code}

Added 25 August 2023.

\begin{code}

open import TypeTopology.DiscreteAndSeparated

to-Ω-＝ : funext 𝓤 𝓤
        → {P Q : 𝓤 ̇ }
          {i : is-prop P} {j : is-prop Q}
        → P ＝ Q
        → (P , i) ＝[ Ω 𝓤 ] (Q , j)
to-Ω-＝ fe = to-subtype-＝ (λ _ → being-prop-is-prop fe)

from-Ω-＝ : {P Q : 𝓤 ̇ }
            {i : is-prop P} {j : is-prop Q}
          → (P , i) ＝[ Ω 𝓤 ] (Q , j)
          → P ＝ Q
from-Ω-＝ = ap _holds

to-Ω¬¬-＝ : funext 𝓤 𝓤
          → {p q : Ω 𝓤}
            {i : ¬¬-stable (p holds)} {j : ¬¬-stable (q holds)}
          → p ＝ q
          → (p , i) ＝[ Ω¬¬ 𝓤 ] (q , j)
to-Ω¬¬-＝ fe = to-subtype-＝ λ p → being-¬¬-stable-is-prop fe (holds-is-prop p)

Ω¬¬-to-Ω : Ω¬¬ 𝓤 → Ω 𝓤
Ω¬¬-to-Ω = pr₁

_holds' : Ω¬¬ 𝓤 → 𝓤 ̇
_holds' 𝕡 = (Ω¬¬-to-Ω 𝕡) holds

holds'-is-prop : (𝕡 : Ω¬¬ 𝓤) → is-prop (𝕡 holds')
holds'-is-prop 𝕡 = holds-is-prop (Ω¬¬-to-Ω 𝕡)

holds'-is-¬¬-stable : (𝕡 : Ω¬¬ 𝓤) → ¬¬-stable (𝕡 holds')
holds'-is-¬¬-stable = pr₂

from-Ω¬¬-＝ : {p q : Ω 𝓤}
              {i : ¬¬-stable (p holds)} {j : ¬¬-stable (q holds)}
           → (p , i) ＝[ Ω¬¬ 𝓤 ] (q , j)
           → p ＝ q
from-Ω¬¬-＝ = ap Ω¬¬-to-Ω

to-Ω¬¬-＝' : funext 𝓤 𝓤
           → {P Q : 𝓤 ̇}
             {i : is-prop P} {j : is-prop Q}
             {s : ¬¬-stable P} {t : ¬¬-stable Q}
           → P ＝ Q
           → ((P , i) , s) ＝[ Ω¬¬ 𝓤 ] ((Q , j) , t)
to-Ω¬¬-＝' fe e = to-Ω¬¬-＝ fe (to-Ω-＝ fe e)

from-Ω¬¬-＝' : {P Q : 𝓤 ̇}
               {i : is-prop P} {j : is-prop Q}
               {s : ¬¬-stable P} {t : ¬¬-stable Q}
             → ((P , i) , s) ＝[ Ω¬¬ 𝓤 ] ((Q , j) , t)
             → P ＝ Q
from-Ω¬¬-＝' e = from-Ω-＝ (from-Ω¬¬-＝ e)

Ω¬¬-is-set : FunExt
           → PropExt
           → is-set (Ω¬¬ 𝓤)
Ω¬¬-is-set {𝓤} fe pe = ¬¬-separated-types-are-sets
                        (fe (𝓤 ⁺) 𝓤₀)
                        (Ω¬¬-is-¬¬-separated (fe 𝓤 𝓤) (pe 𝓤))

Ω¬¬-to-Ω-is-embedding : funext 𝓤 𝓤 → is-embedding (Ω¬¬-to-Ω {𝓤})
Ω¬¬-to-Ω-is-embedding fe = pr₁-is-embedding λ p → being-¬¬-stable-is-prop fe (holds-is-prop p)

Ω-to-Ω¬¬ : funext 𝓤 𝓤₀ → Ω 𝓤 → Ω¬¬ 𝓤
Ω-to-Ω¬¬ fe p = ((¬¬ (p holds)) , negations-are-props fe) , ¬-is-¬¬-stable

Ω¬¬-retract-equation : (fe : funext 𝓤 𝓤)
                       (fe₀ : funext 𝓤 𝓤₀)
                       (pe : propext 𝓤)
                     → Ω-to-Ω¬¬ fe₀ ∘ Ω¬¬-to-Ω ∼ id
Ω¬¬-retract-equation fe fe₀ pe 𝕡 = to-Ω¬¬-＝' fe
                                    (pe (negations-are-props fe₀)
                                        (holds'-is-prop 𝕡)
                                        (holds'-is-¬¬-stable 𝕡)
                                        ¬¬-intro)

Ω¬¬-is-retract-of-Ω : funext 𝓤 𝓤
                    → propext 𝓤
                    → retract (Ω¬¬ 𝓤) of Ω 𝓤
Ω¬¬-is-retract-of-Ω {𝓤} fe pe = Ω-to-Ω¬¬ (lower-funext 𝓤 𝓤 fe) ,
                                Ω¬¬-to-Ω ,
                                Ω¬¬-retract-equation fe (lower-funext 𝓤 𝓤 fe) pe

𝟘-is-¬¬-stable : ¬¬ 𝟘 {𝓤} → 𝟘 {𝓥}
𝟘-is-¬¬-stable ϕ = 𝟘-elim (ϕ 𝟘-elim)

𝟙-is-¬¬-stable : ¬¬ 𝟙 {𝓤} → 𝟙 {𝓥}
𝟙-is-¬¬-stable _ = ⋆

⊥Ω¬¬ ⊤Ω¬¬ : Ω¬¬ 𝓤
⊥Ω¬¬ = ⊥ , 𝟘-is-¬¬-stable
⊤Ω¬¬ = ⊤ , 𝟙-is-¬¬-stable

⊥Ω¬¬-is-not-⊤Ω¬¬ : ⊥Ω¬¬ {𝓤} ≠ ⊤Ω¬¬ {𝓤}
⊥Ω¬¬-is-not-⊤Ω¬¬ e = ⊥-is-not-⊤ (ap Ω¬¬-to-Ω e)

𝟚-to-Ω¬¬ : 𝟚 → Ω¬¬ 𝓤
𝟚-to-Ω¬¬ ₀ = ⊥Ω¬¬
𝟚-to-Ω¬¬ ₁ = ⊤Ω¬¬

module _ (fe : FunExt) (pe : PropExt) where

 𝟚-to-Ω¬¬-is-embedding : is-embedding (𝟚-to-Ω¬¬ {𝓤})
 𝟚-to-Ω¬¬-is-embedding _ (₀ , p) (₀ , q) = to-Σ-＝ (refl , Ω¬¬-is-set fe pe p q)
 𝟚-to-Ω¬¬-is-embedding _ (₀ , p) (₁ , q) = 𝟘-elim (⊥-is-not-⊤ (ap pr₁ p ∙ (ap pr₁ q)⁻¹))
 𝟚-to-Ω¬¬-is-embedding _ (₁ , p) (₀ , q) = 𝟘-elim (⊥-is-not-⊤ (ap pr₁ q ∙ (ap pr₁ p ⁻¹)))
 𝟚-to-Ω¬¬-is-embedding _ (₁ , p) (₁ , q) = to-Σ-＝ (refl , Ω¬¬-is-set fe pe p q)

 𝟚-to-Ω¬¬-fiber : ((p , s) : Ω¬¬ 𝓤) → fiber 𝟚-to-Ω¬¬ (p , s) ≃ (¬ (p holds) + p holds)
 𝟚-to-Ω¬¬-fiber {𝓤} 𝕡@(p , s) =
  fiber (𝟚-to-Ω¬¬ {𝓤}) 𝕡                        ≃⟨ ≃-refl _ ⟩
  (Σ n ꞉ 𝟚 , 𝟚-to-Ω¬¬ {𝓤} n ＝ 𝕡 )              ≃⟨ alternative-+ ⟩
  (𝟚-to-Ω¬¬ ₀ ＝ p , s) + (𝟚-to-Ω¬¬ ₁ ＝ p , s) ≃⟨ I ⟩
  (⊥ ＝ p) + (⊤ ＝ p)                           ≃⟨ II ⟩
  (¬ (p holds) + (p holds))                     ■
  where
   I = +-cong
        (embedding-criterion-converse' pr₁
          (pr₁-is-embedding (λ p → being-¬¬-stable-is-prop (fe _ _) (holds-is-prop p))) _ _)
        (embedding-criterion-converse' pr₁
          (pr₁-is-embedding (λ p → being-¬¬-stable-is-prop (fe _ _) (holds-is-prop p))) _ _)

   II = +-cong
           (＝-flip ● equal-⊥-≃ (pe _) (fe _ _) p)
           (＝-flip ● equal-⊤-≃ (pe _) (fe _ _) p)

 𝟚-to-Ω¬¬-is-small-map : (𝟚-to-Ω¬¬ {𝓤}) is 𝓤 small-map
 𝟚-to-Ω¬¬-is-small-map (p , s) = (¬ (p holds) + p holds) ,
                                   ≃-sym (𝟚-to-Ω¬¬-fiber (p , s))

\end{code}
