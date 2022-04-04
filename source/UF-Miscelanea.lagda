Martin Escardo

UF things that depend on non-UF things.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module UF-Miscelanea where

open import SpartanMLTT

open import Plus-Properties
open import NaturalNumbers-Properties
open import UF-Base
open import UF-Subsingletons renaming (⊤Ω to ⊤ ; ⊥Ω to ⊥)
open import UF-FunExt
open import UF-Lower-FunExt
open import UF-Subsingletons-FunExt
open import UF-Equiv
open import UF-Embeddings
open import DiscreteAndSeparated

decidable-is-collapsible : {X : 𝓤 ̇ } → decidable X → collapsible X
decidable-is-collapsible (inl x) = pointed-types-are-collapsible x
decidable-is-collapsible (inr u) = empty-types-are-collapsible u

discrete-is-Id-collapsible : {X : 𝓤 ̇ } → is-discrete X → Id-collapsible X
discrete-is-Id-collapsible d = decidable-is-collapsible (d _ _)

discrete-types-are-sets : {X : 𝓤 ̇ } → is-discrete X → is-set X
discrete-types-are-sets d = Id-collapsibles-are-sets (discrete-is-Id-collapsible d)

being-isolated-is-prop : FunExt → {X : 𝓤 ̇ } (x : X) → is-prop (is-isolated x)
being-isolated-is-prop {𝓤} fe x = prop-criterion γ
 where
  γ : is-isolated x → is-prop (is-isolated x)
  γ i = Π-is-prop (fe 𝓤 𝓤)
         (λ x → sum-of-contradictory-props
                 (local-hedberg _ (λ y → decidable-is-collapsible (i y)) x)
                 (negations-are-props (fe 𝓤 𝓤₀))
                 (λ p n → n p))

being-isolated'-is-prop : FunExt → {X : 𝓤 ̇ } (x : X) → is-prop (is-isolated' x)
being-isolated'-is-prop {𝓤} fe x = prop-criterion γ
 where
  γ : is-isolated' x → is-prop (is-isolated' x)
  γ i = Π-is-prop (fe 𝓤 𝓤)
         (λ x → sum-of-contradictory-props
                 (local-hedberg' _ (λ y → decidable-is-collapsible (i y)) x)
                 (negations-are-props (fe 𝓤 𝓤₀))
                 (λ p n → n p))

being-discrete-is-prop : FunExt → {X : 𝓤 ̇ } → is-prop (is-discrete X)
being-discrete-is-prop {𝓤} fe {X} = Π-is-prop (fe 𝓤 𝓤) (being-isolated-is-prop fe)

isolated-is-h-isolated : {X : 𝓤 ̇ } (x : X) → is-isolated x → is-h-isolated x
isolated-is-h-isolated {𝓤} {X} x i {y} = local-hedberg x (λ y → γ y (i y)) y
 where
  γ : (y : X) → decidable (x ≡ y) → Σ f ꞉ (x ≡ y → x ≡ y) , wconstant f
  γ y (inl p) = (λ _ → p) , (λ q r → refl)
  γ y (inr n) = id , (λ q r → 𝟘-elim (n r))

isolated-inl : {X : 𝓤 ̇ } (x : X) (i : is-isolated x) (y : X) (r : x ≡ y) → i y ≡ inl r
isolated-inl x i y r =
  equality-cases (i y)
    (λ (p : x ≡ y) (q : i y ≡ inl p) → q ∙ ap inl (isolated-is-h-isolated x i p r))
    (λ (h : x ≢ y) (q : i y ≡ inr h) → 𝟘-elim(h r))

isolated-inr : {X : 𝓤 ̇ }
             → funext 𝓤 𝓤₀
             → (x : X) (i : is-isolated x) (y : X) (n : x ≢ y) → i y ≡ inr n
isolated-inr fe x i y n =
  equality-cases (i y)
  (λ (p : x ≡ y) (q : i y ≡ inl p) → 𝟘-elim (n p))
  (λ (m : x ≢ y) (q : i y ≡ inr m) → q ∙ ap inr (dfunext fe (λ (p : x ≡ y) → 𝟘-elim (m p))))

\end{code}

The following variation of the above doesn't require function extensionality:

\begin{code}

isolated-inr' : {X : 𝓤 ̇ }
              → (x : X) (i : is-isolated x) (y : X) (n : x ≢ y) → Σ m ꞉ x ≢ y , i y ≡ inr m
isolated-inr' x i y n =
  equality-cases (i y)
  (λ (p : x ≡ y) (q : i y ≡ inl p) → 𝟘-elim (n p))
  (λ (m : x ≢ y) (q : i y ≡ inr m) → m , q)

discrete-inl : {X : 𝓤 ̇ } (d : is-discrete X) (x y : X) (r : x ≡ y) → d x y ≡ inl r
discrete-inl d x = isolated-inl x (d x)

discrete-inr : funext 𝓤 𝓤₀
             → {X : 𝓤 ̇ }
               (d : is-discrete X)
               (x y : X)
               (n : ¬ (x ≡ y))
             → d x y ≡ inr n
discrete-inr fe d x = isolated-inr fe x (d x)

isolated-Id-is-prop : {X : 𝓤 ̇ } (x : X) → is-isolated' x → (y : X) → is-prop (y ≡ x)
isolated-Id-is-prop x i = local-hedberg' x (λ y → decidable-is-collapsible (i y))

lc-maps-reflect-isolatedness : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                             → left-cancellable f
                             → (x : X) → is-isolated (f x) → is-isolated x
lc-maps-reflect-isolatedness f l x i y = γ (i (f y))
 where
  γ : (f x ≡ f y) + ¬ (f x ≡ f y) → (x ≡ y) + ¬ (x ≡ y)
  γ (inl p) = inl (l p)
  γ (inr n) = inr (contrapositive (ap f) n)

lc-maps-reflect-discreteness : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                             → left-cancellable f
                             → is-discrete Y
                             → is-discrete X
lc-maps-reflect-discreteness f l d x = lc-maps-reflect-isolatedness f l x (d (f x))

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


open import UF-Equiv

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

𝟚inΩ : 𝟚 → Ω 𝓤
𝟚inΩ ₀ = ⊥
𝟚inΩ ₁ = ⊤

𝟚inΩ-embedding : funext 𝓤 𝓤 → propext 𝓤 → is-embedding (𝟚inΩ {𝓤})
𝟚inΩ-embedding fe pe (P , isp) (₀ , p) (₀ , q) = to-Σ-≡ (refl , Ω-is-set fe pe p q)
𝟚inΩ-embedding fe pe (P , isp) (₀ , p) (₁ , q) = 𝟘-elim (⊥-is-not-⊤ (p ∙ q ⁻¹))
𝟚inΩ-embedding fe pe (P , isp) (₁ , p) (₀ , q) = 𝟘-elim (⊥-is-not-⊤ (q ∙ p ⁻¹))
𝟚inΩ-embedding fe pe (P , isp) (₁ , p) (₁ , q) = to-Σ-≡ (refl , Ω-is-set fe pe p q)

nonempty : 𝓤 ̇ → 𝓤 ̇
nonempty X = is-empty(is-empty X)

stable : 𝓤 ̇ → 𝓤 ̇
stable X = nonempty X → X

decidable-is-stable : {X : 𝓤 ̇ } → decidable X → stable X
decidable-is-stable (inl x) φ = x
decidable-is-stable (inr u) φ = unique-from-𝟘(φ u)

stable-is-collapsible : funext 𝓤 𝓤₀
                      → {X : 𝓤 ̇ } → stable X → collapsible X
stable-is-collapsible {𝓤} fe {X} s = (f , g)
 where
  f : X → X
  f x = s(λ u → u x)

  claim₀ : (x y : X) → (u : is-empty X) → u x ≡ u y
  claim₀ x y u = unique-from-𝟘(u x)

  claim₁ : (x y : X) → (λ u → u x) ≡ (λ u → u y)
  claim₁ x y = dfunext fe (claim₀ x y)

  g : (x y : X) → f x ≡ f y
  g x y = ap s (claim₁ x y)

¬¬-separated-is-Id-collapsible : funext 𝓤 𝓤₀ → {X : 𝓤 ̇ }
                               → is-¬¬-separated X
                               → Id-collapsible X
¬¬-separated-is-Id-collapsible fe s = stable-is-collapsible fe (s _ _)

¬¬-separated-types-are-sets : funext 𝓤 𝓤₀ → {X : 𝓤 ̇ }
                            → is-¬¬-separated X
                            → is-set X
¬¬-separated-types-are-sets fe s = Id-collapsibles-are-sets (¬¬-separated-is-Id-collapsible fe s)

being-¬¬-separated-is-prop : funext 𝓤 𝓤
                           → {X : 𝓤 ̇ }
                           → is-prop (is-¬¬-separated X)
being-¬¬-separated-is-prop {𝓤} fe {X} = prop-criterion f
 where
  f : is-¬¬-separated X → is-prop (is-¬¬-separated X)
  f s = Π-is-prop fe (λ _ →
        Π-is-prop fe (λ _ →
        Π-is-prop fe (λ _ → ¬¬-separated-types-are-sets (lower-funext 𝓤 𝓤 fe) s)))

\end{code}

Find a better home for this:

\begin{code}

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
  h : (n : ℕ) → α n ≡ β n
  h n = 𝟚-ℕ-embedding-is-lc (ap (λ - → - n) p)

\end{code}

Added 19th Feb 2020:

\begin{code}

open import UF-Embeddings

maps-of-props-into-h-isolated-points-are-embeddings : {P : 𝓤 ̇ } {X : 𝓥 ̇ } (f : P → X)
                                                    → is-prop P
                                                    → ((p : P) → is-h-isolated (f p))
                                                    → is-embedding f
maps-of-props-into-h-isolated-points-are-embeddings f i j q (p , s) (p' , s') = to-Σ-≡ (i p p' , j p' _ s')

maps-of-props-into-isolated-points-are-embeddings : {P : 𝓤 ̇ } {X : 𝓥 ̇ } (f : P → X)
                                                  → is-prop P
                                                  → ((p : P) → is-isolated (f p))
                                                  → is-embedding f
maps-of-props-into-isolated-points-are-embeddings f i j = maps-of-props-into-h-isolated-points-are-embeddings
                                                           f i (λ p → isolated-is-h-isolated (f p) (j p))

\end{code}
