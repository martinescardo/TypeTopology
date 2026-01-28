Martin Escardo 17th December 2018. (This has a connection with injectivity.)

We have a look at the algebras of the lifting monad.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan

module Lifting.Algebras
        (𝓣 : Universe)
       where

open import UF.Base
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.UA-FunExt
open import UF.Univalence

open import Lifting.Construction 𝓣
open import Lifting.Identity 𝓣
open import Lifting.Monad 𝓣

\end{code}

An element of 𝓛 (𝓛 X) amounts to a family of partial elements of X
indexed by a proposition:

\begin{code}

double-𝓛-charac : (X : 𝓤 ̇ )
                → 𝓛 (𝓛 X) ≃ (Σ P ꞉ 𝓣 ̇
                                 , (Σ Q ꞉ (P → 𝓣 ̇ )
                                        , ((p : P) → Q p → X)
                                        × ((p : P) → is-prop (Q p)))
                                 × is-prop P)
double-𝓛-charac X = Σ-cong (λ P → ×-cong (γ X P) (≃-refl (is-prop P)))
 where
  γ : (X : 𝓤 ̇ ) (P : 𝓣 ̇ )
    → (P → 𝓛 X)
    ≃ (Σ Q ꞉ (P → 𝓣 ̇ ), ((p : P) → Q p → X) × ((p : P) → is-prop (Q p)))
  γ X P =
   (P → Σ Q ꞉ 𝓣 ̇ , (Q → X) × is-prop Q)                                 ≃⟨ I ⟩
   (Σ Q ꞉ (P → 𝓣 ̇ ), ((p : P) → ((Q p → X) × is-prop (Q p))))           ≃⟨ II ⟩
   (Σ Q ꞉ (P → 𝓣 ̇ ), ((p : P) → Q p → X) × ((p : P) → is-prop (Q p)))   ■
    where
     I  = ΠΣ-distr-≃
     II = Σ-cong (λ Q → →×)

\end{code}

The usual definition of algebra of a monad and construction of free
algebras:

\begin{code}

𝓛-algebra : 𝓤 ̇ → 𝓣 ⁺ ⊔ 𝓤 ̇
𝓛-algebra X = Σ s ꞉ (𝓛 X → X) , (s ∘ η ∼ id) × (s ∘ μ ∼ s ∘ 𝓛̇ s)

free-𝓛-algebra : is-univalent 𝓣 → (X : 𝓤 ̇ ) → 𝓛-algebra (𝓛 X)
free-𝓛-algebra ua X = μ , 𝓛-unit-left∼ ua , 𝓛-assoc∼ ua

\end{code}

We can describe algebras in terms of "extension" operations subject to
two laws:

\begin{code}

extension-op : 𝓤 ̇ → 𝓣 ⁺ ⊔ 𝓤 ̇
extension-op X = {P : 𝓣 ̇ } → is-prop P → (P → X) → X

\end{code}

The intuitive idea is that a "extension" operation extends a partial
element to a total element.

To characterize algebras, the extension operations have two satisfy the
following two laws:

\begin{code}

𝓛-alg-Law₀ : {X : 𝓤 ̇ } → extension-op X → 𝓤 ̇
𝓛-alg-Law₀ {𝓤} {X} ∐ = (x : X) → ∐ 𝟙-is-prop (λ (p : 𝟙) → x) ＝ x

𝓛-alg-Law₁ : {X : 𝓤 ̇ } → extension-op X → 𝓣 ⁺ ⊔ 𝓤 ̇
𝓛-alg-Law₁ {𝓤} {X} ∐ =
   (P : 𝓣 ̇ ) (Q : P → 𝓣 ̇ )
   (i : is-prop P) (j : (p : P) → is-prop (Q p))
   (φ : Σ Q → X)
 → ∐ (Σ-is-prop i j) φ ＝ ∐ i (λ p → ∐ (j p) (λ q → φ (p , q)))

\end{code}

Omitting the witnesses of proposition-hood, the above two laws can be
written in more standard mathematical notation as follows:

    ∐  x = x
   p:𝟙

    ∐          φ r  =  ∐   ∐     φ (p , q)
  r : Σ {P} Q         p:P q:Q(p)


\begin{code}

𝓛-alg : 𝓤 ̇ → 𝓣 ⁺ ⊔ 𝓤 ̇
𝓛-alg X = Σ ∐ ꞉ extension-op X , 𝓛-alg-Law₀ ∐ × 𝓛-alg-Law₁ ∐

𝓛-alg-structure-map : {X : 𝓤 ̇ } → 𝓛-alg X → extension-op X
𝓛-alg-structure-map (∐ , l₀ , l₁) = ∐

𝓛-alg-law₀ : {X : 𝓤 ̇ } (𝓐 : 𝓛-alg X) → 𝓛-alg-Law₀ (𝓛-alg-structure-map 𝓐)
𝓛-alg-law₀ (∐ , l₀ , l₁) = l₀

𝓛-alg-law₁ : {X : 𝓤 ̇ } (𝓐 : 𝓛-alg X) → 𝓛-alg-Law₁ (𝓛-alg-structure-map 𝓐)
𝓛-alg-law₁ (∐ , l₀ , l₁) = l₁

\end{code}

Before proving that we have an equivalence

  𝓛-algebra X ≃ 𝓛-alg X,

we characterize the algebra morphisms in terms of extensions (unfortunately
overloading is not available):

\begin{code}

private
 ⋁ : {X : 𝓤 ̇ } → (𝓛 X → X) → extension-op X
 ⋁ s {P} i φ = s (P , φ , i)

 ∐̇ : {X : 𝓤 ̇ } → 𝓛-algebra X → extension-op X
 ∐̇ (s , _) = ⋁ s

 ∐ : {X : 𝓤 ̇ } → 𝓛-alg X → extension-op X
 ∐ (∐ , κ , ι) = ∐

 law₀ : {X : 𝓤 ̇ } (a : 𝓛-alg X) → 𝓛-alg-Law₀ (∐ a)
 law₀ (∐ , κ , ι) = κ

 law₁ : {X : 𝓤 ̇ } (a : 𝓛-alg X) → 𝓛-alg-Law₁ (∐ a)
 law₁ (∐ , κ , ι) = ι

\end{code}

The algebra morphisms are the maps that preserve extensions. Omitting the
first argument of ⋁, the following says that the morphisms are the
maps h : X → Y with

  h (⋁ φ) ＝ ⋁ h (φ p)
            p:P

for all φ : P → X.

\begin{code}

𝓛-morphism-charac : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                    (s : 𝓛 X → X) (t : 𝓛 Y → Y)
                    (h : X → Y)
                  → (h ∘ s ∼ t ∘ 𝓛̇ h)
                  ≃ ({P : 𝓣 ̇ } (i : is-prop P) (φ : P → X)
                       → h (⋁ s i φ) ＝ ⋁ t i (λ p → h (φ p)))
𝓛-morphism-charac s t h = qinveq (λ H {P} i φ → H (P , φ , i))
                                 ((λ {π (P , φ , i) → π {P} i φ}) ,
                                 (λ _ → refl) ,
                                 (λ _ → refl))

\end{code}

We name the other two projections of 𝓛-alg:

\begin{code}

𝓛-alg-const : {X : 𝓤 ̇ } (A : 𝓛-alg X) (x : X)
            → ∐ A 𝟙-is-prop (λ (p : 𝟙) → x) ＝ x
𝓛-alg-const (∐ , κ , ι) = κ

𝓛-alg-iterated : {X : 𝓤 ̇ } (A : 𝓛-alg X)
                 (P : 𝓣 ̇ ) (Q : P → 𝓣 ̇ )
                 (i : is-prop P) (j : (p : P) → is-prop (Q p))
                 (φ : Σ Q → X)
               → ∐ A (Σ-is-prop i j) φ
               ＝ ∐ A i (λ p → ∐ A (j p) (λ q → φ (p , q)))
𝓛-alg-iterated (∐ , κ , ι) = ι

\end{code}

We could write a proof of the following characterization of the
𝓛-algebras by composing equivalences as above, but it seems more
direct, and just as clear, to write a direct proof, by construction of
the equivalence and its inverse. This also emphasizes that the
equivalence is definitional, in the sense that the two required
equations hold definitionally.

\begin{code}

𝓛-algebra-gives-alg : {X : 𝓤 ̇ } → 𝓛-algebra X → 𝓛-alg X
𝓛-algebra-gives-alg (s , unit , assoc) =
  ⋁ s ,
  unit ,
  (λ P Q i j φ → assoc (P , (λ p → Q p , (λ q → φ (p , q)) , j p) , i))

𝓛-alg-gives-algebra : {X : 𝓤 ̇ } → 𝓛-alg X → 𝓛-algebra X
𝓛-alg-gives-algebra {𝓤} {X} (∐ , unit , ι) = s , unit , assoc
 where
  s : 𝓛 X → X
  s (P , φ , i) = ∐ i φ

  assoc : s ∘ μ ∼ s ∘ 𝓛̇ s
  assoc (P , g , i) = ι P (pr₁ ∘ g) i
                       (λ p → pr₂ (pr₂ (g p)))
                       (λ r → pr₁ (pr₂ (g (pr₁ r))) (pr₂ r))

𝓛-alg-charac : {X : 𝓤 ̇ } → 𝓛-algebra X ≃ 𝓛-alg X
𝓛-alg-charac = qinveq
                𝓛-algebra-gives-alg
                (𝓛-alg-gives-algebra , ((λ _ → refl) , (λ _ → refl)))
\end{code}

We now consider an equivalent of 𝓛-alg-Law₀ (which is useful e.g. for
type injectivity purposes).

\begin{code}

𝓛-alg-Law₀' : {X : 𝓤 ̇ } → extension-op X → 𝓣 ⁺ ⊔ 𝓤 ̇
𝓛-alg-Law₀' {𝓤} {X} ∐ = (P : 𝓣 ̇ )
                         (i : is-prop P)
                         (φ : P → X)
                         (p : P)
                       → ∐ i φ ＝ φ p

𝓛-alg-Law₀-gives₀' : propext 𝓣
                   → funext 𝓣 𝓣
                   → funext 𝓣 𝓤
                   → {X : 𝓤 ̇ }
                     (∐ : extension-op X)
                   → 𝓛-alg-Law₀ ∐
                   → 𝓛-alg-Law₀' ∐
𝓛-alg-Law₀-gives₀' pe fe fe' {X} ∐ κ P i φ p = γ
 where
  r : φ ＝ λ (_ : P) → φ p
  r = dfunext fe' (λ p' → ap φ (i p' p))

  s : P ＝ 𝟙 → ∐ {P} i φ ＝ ∐ {𝟙} 𝟙-is-prop (λ (_ : 𝟙) → φ p)
  s refl = ap₂ ∐ (being-prop-is-prop fe i 𝟙-is-prop) r

  t : P ＝ 𝟙
  t = pe i 𝟙-is-prop unique-to-𝟙 (λ _ → p)

  γ = ∐ {P} i φ                   ＝⟨ s t ⟩
      ∐ 𝟙-is-prop (φ ∘ (λ _ → p)) ＝⟨ κ (φ p) ⟩
      φ p                         ∎

𝓛-alg-Law₀'-gives₀ : {X : 𝓤 ̇ }
                     (∐ : extension-op X)
                    → 𝓛-alg-Law₀' ∐
                    → 𝓛-alg-Law₀ ∐
𝓛-alg-Law₀'-gives₀ {𝓤} {X} ∐ φ x = φ 𝟙 𝟙-is-prop (λ _ → x) ⋆

\end{code}

We now consider a non-dependent version of 𝓛-alg-Law₁, and show that it is
equivalent to 𝓛-alg-Law₁:

\begin{code}

𝓛-alg-Law₁' : {X : 𝓤 ̇ } → extension-op X → 𝓣 ⁺ ⊔ 𝓤 ̇
𝓛-alg-Law₁' {𝓤} {X} ∐ = (P Q : 𝓣 ̇ )
                         (i : is-prop P) (j : is-prop Q)
                         (φ : P × Q → X)
                       → ∐ (×-is-prop i j) φ ＝ ∐ i (λ p → ∐ j (λ q → φ (p , q)))

\end{code}

The difference with 𝓛-alg-Law₁ is that the family φ has type P × Q → X
rather than Σ {P} Q → X, and so the modified, logically equivalent law
amounts to

    ∐   ∐   φ (p , q) =   ∐        φ r
   p:P q:Q              r : P × Q

One direction of the logical equivalence is trivial:

\begin{code}

𝓛-alg-Law₁-gives₁' : {X : 𝓤 ̇ } (∐ : extension-op X)
                   → 𝓛-alg-Law₁ ∐ → 𝓛-alg-Law₁' ∐
𝓛-alg-Law₁-gives₁' {𝓤} {X} ∐ a P Q i j = a P (λ _ → Q) i (λ p → j)

\end{code}

To establish the converse we need the following lemma for extensions,
which is interesting on its own right,

  ∐  φ p ＝ ∐  φ (k q),
 p:P      q:Q

and also gives self-distributivity of extensions:

  ∐   ∐  φ (p , q) =   ∐   ∐  φ (p , q)
 p:P q:Q              q:Q p:P


\begin{code}

change-of-variables-in-extension
 : {X : 𝓤 ̇ } (∐ : extension-op X)
   (P : 𝓣 ̇ ) (i : is-prop P)
   (Q : 𝓣 ̇ ) (j : is-prop Q)
   (h : P → Q) (k : Q → P)
   (φ : P → X)
 → is-univalent 𝓣
 → ∐ i φ ＝ ∐ j (φ ∘ k)
change-of-variables-in-extension ∐ P i Q j h k φ ua
 = γ
 where
  cd : (r : Q ＝ P) → ∐ i φ ＝ ∐ j (φ ∘ Idtofun r)
  cd refl = ap (λ - → ∐ - φ) (being-prop-is-prop (univalence-gives-funext ua) i j)

  e : Q ≃ P
  e = qinveq k (h , ((λ q → j (h (k q)) q) , λ p → i (k (h p)) p))

  a : Idtofun (eqtoid ua Q P e) ＝ k
  a = ap ⌜_⌝ (idtoeq'-eqtoid ua Q P e)

  γ : ∐ i φ ＝ ∐ j (φ ∘ k)
  γ = cd (eqtoid ua Q P e) ∙ ap (λ - → ∐ j (φ ∘ -)) a

\end{code}

NB. The above is proved without univalence, but with propositional and
functional extensionality in the module InjectiveTypes.Structure.

\begin{code}

𝓛-alg-self-distr : {X : 𝓤 ̇ } (∐ : extension-op X)
                   (P : 𝓣 ̇ ) (i : is-prop P)
                   (Q : 𝓣 ̇ ) (j : is-prop Q)
                 → is-univalent 𝓣
                 → 𝓛-alg-Law₁' ∐
                 → (φ : P × Q → X)
                      → ∐ i (λ p → ∐ j (λ q → φ (p , q)))
                      ＝ ∐ j (λ q → ∐ i (λ p → φ (p , q)))

𝓛-alg-self-distr ∐ P i Q j ua l₁' φ =
 ∐ i (λ p → ∐ j (λ q → φ (p , q)))                     ＝⟨ a ⟩
 ∐ (Σ-is-prop i (λ p → j)) φ                           ＝⟨ b ⟩
 ∐ (Σ-is-prop j (λ p → i)) (φ ∘ (λ t → pr₂ t , pr₁ t)) ＝⟨ c ⟩
 ∐ j (λ q → ∐ i (λ p → φ (p , q)))                     ∎
  where
   a = (l₁' P Q i j φ)⁻¹
   b = change-of-variables-in-extension
        ∐
        (P × Q)
        (Σ-is-prop i (λ p → j))
        (Q × P)
        (Σ-is-prop j (λ p → i))
        (λ t → pr₂ t , pr₁ t) (λ t → pr₂ t , pr₁ t) φ ua
   c = l₁' Q P j i (λ t → φ (pr₂ t , pr₁ t))

\end{code}

Using this we can prove the other direction of the logical equivalence
claimed above:

\begin{code}

𝓛-alg-Law₁'-gives₁ : {X : 𝓤 ̇ } (∐ : extension-op X)
                    → is-univalent 𝓣
                    → funext 𝓣 𝓤
                    → 𝓛-alg-Law₁' ∐
                    → 𝓛-alg-Law₁ ∐
𝓛-alg-Law₁'-gives₁ {𝓤} {X} ∐ ua fe a P Q i j φ = γ
 where
  h : (p : P) → Q p → Σ Q
  h p q = (p , q)

  k : (p : P) → Σ Q → Q p
  k p (p' , q) = transport Q (i p' p) q

  φ' : P × Σ Q → X
  φ' (p , p' , q) = φ (p , k p (p' , q))

  k' : Σ Q → P × Σ Q
  k' (p , q) = p , p , q

  H : φ' ∘ k' ∼ φ
  H (p , q) = ap (λ - → φ (p , -)) (j p _ _)

  γ = ∐ {Σ Q} (Σ-is-prop i j) φ                                         ＝⟨ b ⟩
      ∐ {Σ Q} (Σ-is-prop i j) (φ' ∘ k')                                 ＝⟨ c ⁻¹ ⟩
      ∐ {P × Σ Q} (×-is-prop i (Σ-is-prop i j)) φ'                      ＝⟨ d ⟩
      ∐ {P} i (λ p → ∐ {Σ Q} (Σ-is-prop i j) ((λ σ → φ (p , σ)) ∘ k p)) ＝⟨ e ⟩
      ∐ {P} i (λ p → ∐ {Q p} (j p) (λ q → φ (p , q)))                   ∎
   where
    b = (ap (∐ {Σ Q} (Σ-is-prop i j)) (dfunext fe H))⁻¹
    c = change-of-variables-in-extension
         ∐
         (P × Σ Q)
         (×-is-prop i (Σ-is-prop i j))
         (Σ Q)
         (Σ-is-prop i j) pr₂ k' φ' ua
    d = a P (Σ Q) i (Σ-is-prop i j) (λ z → φ (pr₁ z , k (pr₁ z) (pr₂ z)))
    e = (ap (∐ {P} i)
          (dfunext fe (λ p → change-of-variables-in-extension
                              ∐
                              (Q p)
                              (j p)
                              (Σ Q) (Σ-is-prop i j)
                              (h p) (k p) (λ σ → φ (p , σ)) ua)))⁻¹
\end{code}

The algebras form an exponential ideal with the pointwise
operations. More generally:

\begin{code}

Π-is-alg : funext 𝓤 𝓥
         → {X : 𝓤 ̇ } (A : X → 𝓥 ̇ )
         → ((x : X) → 𝓛-alg (A x)) → 𝓛-alg (Π A)
Π-is-alg {𝓤} {𝓥} fe {X} A 𝓐 = ∐· , l₀ , l₁
 where
  ∐· : {P : 𝓣 ̇ } → is-prop P → (P → Π A) → Π A
  ∐· i φ x = ∐ (𝓐 x) i (λ p → φ p x)

  l₀ : (φ : Π A) → ∐· 𝟙-is-prop (λ p → φ) ＝ φ
  l₀ φ = dfunext fe (λ x → law₀ (𝓐 x) (φ x))

  l₁ : (P : 𝓣 ̇ ) (Q : P → 𝓣 ̇ )
       (i : is-prop P) (j : (p : P) → is-prop (Q p))
       (φ : Σ Q → Π A)
      → ∐· (Σ-is-prop i j) φ
      ＝ ∐· i (λ p → ∐· (j p) (λ q → φ (p , q)))
  l₁ P Q i j φ = dfunext fe (λ x → law₁ (𝓐 x) P Q i j (λ σ → φ σ x))

\end{code}

This is the case for any monad of a certain kind, but the way we
proved this above using our characterizations of the algebras applies
only to our monad.

The following examples are crucial for injectivity. They say that the
universe is an algebra in at least two ways, with ∐ = Σ and ∐ = Π
respectively.

\begin{code}

universe-is-algebra-Σ : is-univalent 𝓣 → 𝓛-alg (𝓣 ̇ )
universe-is-algebra-Σ ua = sum , k , ι
 where
  sum : {P : 𝓣 ̇ } → is-prop P → (P → 𝓣 ̇ ) → 𝓣 ̇
  sum {P} i = Σ

  k : (X : 𝓣 ̇ ) → Σ (λ p → X) ＝ X
  k X = eqtoid ua (𝟙 × X) X 𝟙-lneutral

  ι : (P : 𝓣 ̇ ) (Q : P → 𝓣 ̇ ) (i : is-prop P)
      (j : (p : P) → is-prop (Q p)) (φ : Σ Q → 𝓣 ̇ )
    → Σ φ ＝ Σ (λ p → Σ (λ q → φ (p , q)))
  ι P Q i j φ = eqtoid ua _ _ Σ-assoc

universe-is-algebra-Π : is-univalent 𝓣 → 𝓛-alg (𝓣 ̇ )
universe-is-algebra-Π ua = prod , k , ι
 where
  fe : funext 𝓣 𝓣
  fe = univalence-gives-funext ua

  prod : {P : 𝓣 ̇ } → is-prop P → (P → 𝓣 ̇ ) → 𝓣 ̇
  prod {P} i = Π

  k : (X : 𝓣 ̇ ) → Π (λ p → X) ＝ X
  k X = eqtoid ua (𝟙 → X) X (≃-sym (𝟙→ (univalence-gives-funext ua)))

  ι : (P : 𝓣 ̇ ) (Q : P → 𝓣 ̇ ) (i : is-prop P)
      (j : (p : P) → is-prop (Q p)) (φ : Σ Q → 𝓣 ̇ )
    → Π φ ＝ Π (λ p → Π (λ q → φ (p , q)))
  ι P Q i j φ = eqtoid ua _ _ (curry-uncurry' fe fe)

\end{code}

Added 6th June 2025. A retract of the underlying type of an algebra
can be given an algebra structure, if the induced idempotent is an
automorphism, in such a way that the section becomes a homomorphism.

\begin{code}

is-hom : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → 𝓛-alg A → 𝓛-alg B → (A → B) → 𝓣 ⁺ ⊔ 𝓤 ⊔ 𝓥 ̇
is-hom {𝓤} {𝓥} {A} {B} (∐ᵃ , _) (∐ᵇ , _) h =
 (P : 𝓣 ̇ ) (i : is-prop P) (φ : P → A) → h (∐ᵃ i φ) ＝ ∐ᵇ i (h ∘ φ)

id-is-hom : {A : 𝓤 ̇ } (𝓐 : 𝓛-alg A)
          → is-hom 𝓐 𝓐 id
id-is-hom 𝓐 P i φ = refl

∘-is-hom : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {C : 𝓦 ̇ }
           (𝓐 : 𝓛-alg A) (𝓑 : 𝓛-alg B) (𝓒 : 𝓛-alg C)
           (h : A → B) (k : B → C)
         → is-hom 𝓐 𝓑 h
         → is-hom 𝓑 𝓒 k
         → is-hom 𝓐 𝓒 (k ∘ h)
∘-is-hom (∐ᵃ , _) (∐ᵇ , _) (∐ᶜ , _) h k h-is-hom k-is-hom P i φ =
 k (h (∐ᵃ i φ))   ＝⟨ ap k (h-is-hom P i φ) ⟩
 k (∐ᵇ i (h ∘ φ)) ＝⟨ k-is-hom P i (h ∘ φ) ⟩
 ∐ᶜ i (k ∘ h ∘ φ) ∎

open import UF.Sets

being-hom-is-prop : Fun-Ext
                  → {A : 𝓤 ̇ } (𝓐 : 𝓛-alg A)
                    {B : 𝓥 ̇ } (𝓑 : 𝓛-alg B)
                  → is-set B
                  → (h : A → B)
                  → is-prop (is-hom 𝓐 𝓑 h)
being-hom-is-prop fe 𝓐 𝓑 B-is-set h = Π₃-is-prop fe (λ _ _ _ → B-is-set)

⟨_⟩ : {A : 𝓤 ̇ } → 𝓛-alg A → 𝓤 ̇
⟨_⟩ {𝓤} {A} 𝓐 = A

Hom : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → 𝓛-alg A → 𝓛-alg B → 𝓣 ⁺ ⊔ 𝓤 ⊔ 𝓥 ̇
Hom 𝓐 𝓑 = Σ h ꞉ (⟨ 𝓐 ⟩ →  ⟨ 𝓑 ⟩) , is-hom 𝓐 𝓑 h

open import UF.Retracts

module _
         (A : 𝓤 ̇ )
         (B : 𝓥 ̇ )
         (𝓐@(∐ᵃ , lawᵃ₀ , lawᵃ₁) : 𝓛-alg A)
         ((r , s , rs) : retract B of A)
         (sr-is-hom : is-hom 𝓐 𝓐 (s ∘ r))
         (fe : Fun-Ext)
       where

 private
  ∐ᵇ : extension-op B
  ∐ᵇ i φ = r (∐ᵃ i (s ∘ φ))

  lawᵇ₀ : 𝓛-alg-Law₀ ∐ᵇ
  lawᵇ₀ b =
   ∐ᵇ 𝟙-is-prop (λ _ → b)       ＝⟨refl⟩
   r (∐ᵃ 𝟙-is-prop (λ _ → s b)) ＝⟨ ap r (lawᵃ₀ (s b)) ⟩
   r (s b)                      ＝⟨ rs b ⟩
   b                            ∎

\end{code}

Before we know that ∐ᵇ satisfies the second algebra law, we can show
that the section is a homomorphism. In fact, we use this to prove the
second algebra law.

\begin{code}

  s-is-hom = λ P i φ →
   s (∐ᵇ i φ)           ＝⟨refl⟩
   s (r (∐ᵃ i (s ∘ φ))) ＝⟨ sr-is-hom P i (s ∘ φ) ⟩
   ∐ᵃ i (s ∘ r ∘ s ∘ φ) ＝⟨ ap (λ - → ∐ᵃ i (s ∘ - ∘ φ)) (dfunext fe rs) ⟩
   ∐ᵃ i (s ∘ φ)         ∎

  lawᵇ₁ : 𝓛-alg-Law₁ ∐ᵇ
  lawᵇ₁ P Q i j φ =
   ∐ᵇ (Σ-is-prop i j) φ                                    ＝⟨refl⟩
   r (∐ᵃ (Σ-is-prop i j) (s ∘ φ))                          ＝⟨ by-lawᵃ₁ ⟩
   r (∐ᵃ i (λ p → ∐ᵃ (j p) (λ q → s (φ (p , q)))))         ＝⟨ because-s-is-hom ⟩
   r (∐ᵃ i (λ p → s (r (∐ᵃ (j p) (λ q → s (φ (p , q))))))) ＝⟨refl⟩
   ∐ᵇ i (λ p → ∐ᵇ (j p) (λ q → φ (p , q)))                 ∎
    where
     by-lawᵃ₁ = ap r (lawᵃ₁ P Q i j (s ∘ φ))
     because-s-is-hom =
      ap (r ∘ ∐ᵃ i)
         ((dfunext fe (λ p → s-is-hom (Q p) (j p) (λ q → φ (p , q))))⁻¹)

  𝓑 : 𝓛-alg B
  𝓑 = ∐ᵇ , lawᵇ₀ , lawᵇ₁

\end{code}

The following are the only public things in this anonymous module.

\begin{code}

 retract-of-algebra : 𝓛-alg B
 retract-of-algebra = 𝓑

 section-is-hom : is-hom retract-of-algebra 𝓐 s
 section-is-hom = s-is-hom

\end{code}

Added 6th September 2025 by Martin Escardo. Use Ω to repackage things
more neatly. We use uppercase names to distinguish the repackaged
things.

\begin{code}

module algebra-repackaging where

 open import UF.SubtypeClassifier

 Extension-op : 𝓤 ̇ → 𝓣 ⁺ ⊔ 𝓤 ̇
 Extension-op X = (P : Ω 𝓣) → (P holds → X) → X

 𝓛-Alg-Law₀ : {X : 𝓤 ̇ } → Extension-op X → 𝓤 ̇
 𝓛-Alg-Law₀ {𝓤} {X} ∐ = (x : X) → ∐ ⊤ (λ _ → x) ＝ x

 𝓛-Alg-Law₁ : {X : 𝓤 ̇ } → Extension-op X → 𝓣 ⁺ ⊔ 𝓤 ̇
 𝓛-Alg-Law₁ {𝓤} {X} ∐ =
    (P : Ω 𝓣) (Q : P holds → Ω 𝓣)
    (φ : (ΣΩ p ꞉ P , Q p) holds → X)
  → ∐ (ΣΩ p ꞉ P , Q p) φ ＝ ∐ P (λ p → ∐ (Q p) (λ q → φ (p , q)))

 𝓛-Alg : 𝓤 ̇ → 𝓣 ⁺ ⊔ 𝓤 ̇
 𝓛-Alg X = Σ ∐ ꞉ Extension-op X , 𝓛-Alg-Law₀ ∐ × 𝓛-Alg-Law₁ ∐

 𝓛-Alg-gives-𝓛-alg : {X : 𝓤 ̇ } → 𝓛-Alg X → 𝓛-alg X
 𝓛-Alg-gives-𝓛-alg (∐ , l₀ , l₁) =
  (λ {P} P-is-prop → ∐ (P , P-is-prop)) ,
  l₀ ,
  (λ P Q i j → l₁ (P , i) (λ p → Q p , j p))

\end{code}

But we probably won't use the above repackaging, as we already have
everything written with the original choice of implementation.

Added 8th September 2025 by Martin Escardo. The discussion of free
algebras in the category of sets can be carried out without using
univalence, and only its two consequences, propositional and
functional extensionality. Notice that already the associativity law
for the lifting monad uses univalence.

\begin{code}

is-free-𝓛-alg : {F : 𝓤 ̇ } (𝓕 : 𝓛-alg F) (X : 𝓥 ̇ ) (ι : X → F) → 𝓤ω
is-free-𝓛-alg 𝓕 X ι = {𝓦 : Universe}
                       {A : 𝓦 ̇ }
                       (i : is-set A)
                       (𝓐 : 𝓛-alg A)
                       (f : X → A)
                     → ∃! (f̅ , _) ꞉ Hom 𝓕 𝓐 , f̅ ∘ ι ∼ f

\end{code}

Notice that above definition says that precomposition with ι is an
equivalence.

\begin{code}

module free-algebra-eliminators
         {F : 𝓤 ̇ }
         (𝓕 : 𝓛-alg F)
         (X : 𝓥 ̇ )
         (ι : X → F)
         (𝓕-is-free : is-free-𝓛-alg 𝓕 X ι)
         {A : 𝓦 ̇ }
         (i : is-set A)
         (𝓐 : 𝓛-alg A)
         (f : X → A)
       where

 private
  eu : ∃! (f̅ , _) ꞉ Hom 𝓕 𝓐 , f̅ ∘ ι ∼ f
  eu = 𝓕-is-free i 𝓐 f

 unique-hom : F → A
 unique-hom = pr₁ (∃!-witness eu)

 unique-hom-is-hom : is-hom 𝓕 𝓐 unique-hom
 unique-hom-is-hom = pr₂ (∃!-witness eu)

 unique-hom-is-extension : unique-hom ∘ ι ∼ f
 unique-hom-is-extension = ∃!-is-witness eu

 at-most-one-extending-hom : is-prop (Σ (f̅ , _) ꞉ Hom 𝓕 𝓐 , f̅ ∘ ι ∼ f)
 at-most-one-extending-hom = singletons-are-props eu

 at-most-one-extending-hom' : ((h , h-is-hom) (k , k-is-hom) : Hom 𝓕 𝓐)
                            → h ∘ ι ∼ f
                            → k ∘ ι ∼ f
                            → h ∼ k
 at-most-one-extending-hom' 𝕙@(h , h-is-hom) 𝕜@(k , k-is-hom) p q =
  happly (ap (pr₁ ∘ pr₁) (at-most-one-extending-hom (𝕙 , p) (𝕜 , q)))

 the-only-hom-extension : ((h , h-is-hom) : Hom 𝓕 𝓐)
                        → h ∘ ι ∼ f
                        → h ∼ unique-hom
 the-only-hom-extension 𝕙@(h , h-is-hom) x =
  at-most-one-extending-hom' 𝕙 (∃!-witness eu) x unique-hom-is-extension

\end{code}

We now construct the canonical free algebra.

\begin{code}

module free-algebras-in-the-category-of-sets
        (pe : Prop-Ext)
        (fe : Fun-Ext)
        {𝓤 : Universe}
        (X : 𝓤 ̇ )
        (X-is-set : is-set X)
       where

 ⨆ : extension-op (𝓛 X)
 ⨆ {P} P-is-prop φ =
  (Σ p ꞉ P , is-defined (φ p)) ,
  (λ (p , d) → value (φ p) d) ,
  Σ-is-prop P-is-prop (λ p → being-defined-is-prop (φ p))

 canonical-free-algebra : 𝓛-alg (𝓛 X)
 canonical-free-algebra = ⨆ , l₀ , l₁
  where
   l₀ : 𝓛-alg-Law₀ ⨆
   l₀ l@(P , φ , P-is-prop) =
     from-⋍ pe fe fe (((λ (⋆ , p) → p) , (λ p → ⋆ , p)) , (λ _ → refl))

   l₁ : 𝓛-alg-Law₁ ⨆
   l₁ P Q i j f = from-⋍ pe fe fe
                   (((λ ((p , q) , d) → (p , (q , d))) ,
                     λ (p , (q , d)) → ((p , q), d)) ,
                    (λ _ → refl))

\end{code}

We rely on the following useful lemma, which says that every element
of 𝓛 X is a join of positive elements, as in the case after Anders
Kock (see [1] below), and which is interesting in its own right. The
positive elements of the free algebra 𝓛 X are those of the form η x,
but we don't need to know this or the definition of positive element
in order to formulate and prove the following.

\begin{code}

 every-element-of-𝓛-is-a-positive-join : (l@(P , φ , i) : 𝓛 X)
                                       → l ＝ ⨆ i (η ∘ φ)
 every-element-of-𝓛-is-a-positive-join l@(P , φ , i) =
  from-⋍ pe fe fe (((λ (p : P) → p , ⋆) , pr₁) , (λ (_ : P) → refl))

 private
  𝓕 = canonical-free-algebra

 module _
          {𝓥 : Universe}
          {A : 𝓥 ̇ }
          (A-is-set : is-set A)
          (𝓐@(∐ , l₀ , l₁) : 𝓛-alg A)
          (f : X → A)
        where

  𝓛-extension : (𝓛 X → A)
  𝓛-extension (P , φ , P-is-prop) = ∐ P-is-prop (f ∘ φ)

  private
   f̅ = 𝓛-extension

  𝓛-extension-is-hom : is-hom 𝓕 𝓐 f̅
  𝓛-extension-is-hom P i φ =
   l₁ P
      (λ p → is-defined (φ p))
      i
      (λ p → being-defined-is-prop (φ p))
      (λ (p , d) → f (value (φ p) d))

  𝓛-extension-extends : f̅ ∘ η ∼ f
  𝓛-extension-extends x = l₀ (f x)

  private
   H : 𝓣 ⁺ ⊔ 𝓤 ⊔ 𝓥 ̇
   H = Σ (h , _) ꞉ Hom 𝓕 𝓐 , h ∘ η ∼ f

  hom-agreement
   : (((h , _) , _) ((h' , _) , _) : H)
   → h ∼ h'
  hom-agreement
   ((h , h-is-hom) , e) ((h' , h'-is-hom) , e') l@(P , φ , i)
   = h l               ＝⟨ I ⟩
     h (⨆ i (η ∘ φ))   ＝⟨ II ⟩
     ∐ i (h  ∘ η ∘ φ)  ＝⟨ III ⟩
     ∐ i (h' ∘ η ∘ φ)  ＝⟨ II' ⟩
     h' (⨆ i (η ∘ φ))  ＝⟨ I' ⟩
     h' l              ∎
    where
      I   = ap h (every-element-of-𝓛-is-a-positive-join l)
      II  = h-is-hom P i (η ∘ φ)
      III = ap (λ - → ∐ i (- ∘ φ))
               (dfunext fe (λ (x : X) → h (η x)  ＝⟨ e x ⟩
                                        f x      ＝⟨ (e' x)⁻¹ ⟩
                                        h' (η x) ∎))
      II' = (h'-is-hom P i (η ∘ φ))⁻¹
      I'  = (ap h' (every-element-of-𝓛-is-a-positive-join l))⁻¹

  homomorphic-𝓛-extensions-form-a-prop : is-prop H
  homomorphic-𝓛-extensions-form-a-prop he he'
   = to-subtype-＝
      (λ h → Π-is-prop fe (λ x → A-is-set))
      (to-subtype-＝
        (being-hom-is-prop fe 𝓕 𝓐 A-is-set)
        (dfunext fe (hom-agreement he he')))

  free-algebra-universal-property : is-singleton H
  free-algebra-universal-property
   = pointed-props-are-singletons
      ((f̅ , 𝓛-extension-is-hom) , 𝓛-extension-extends)
      homomorphic-𝓛-extensions-form-a-prop

\end{code}

Notice that the universal property of the algebra freely generated by
X : 𝓤 with insertion of generators η : X → 𝓛 X eliminates into any
universe 𝓥:

\begin{code}

 𝓛-is-free : is-free-𝓛-alg canonical-free-algebra X η
 𝓛-is-free = free-algebra-universal-property

\end{code}

Moved from AnAlgebraWhichIsNotAlwaysFree 29th Nov 2025. If two
algebras A and B are freely generated by the same set of generators,
they are canonically equivalent.

       i
  G ────────→ A
   ╲         │ ↑
    ╲        │ │
     ╲       │ │
    j ╲    h │ │ h⁻¹
       ╲     │ │
        ╲    │ │
         ╲   │ │
          ╲  ↓ │
           ➘  B

The proof is a standard categorical argument. The homomorphism h is
the unique homomorphic extension of j along i, and the homomorphism
h⁻¹ is the unique homomorphisc extension of i along j. But also the
composites h ∘ h⁻¹ : A → A and h⁻¹ ∘ h : B → B are the unique
homomorphisms extending the identity function along i and j
respectively, and so, because the identity functions are respectively
such a homomorphisms, we conclude that both composites agree with the
respective identity functions.

\begin{code}

module _
        {A : 𝓤 ̇ }
        {B : 𝓥 ̇ }
        (G : 𝓦 ̇ )
        (A-is-set : is-set A)
        (B-is-set : is-set B)
        (G-is-set : is-set G)
        (i : G → A)
        (j : G → B)
        (𝓐 : 𝓛-alg A)
        (𝓑 : 𝓛-alg B)
        (ϕ : is-free-𝓛-alg 𝓐 G i)
        (γ : is-free-𝓛-alg 𝓑 G j)
     where

 module A = free-algebra-eliminators 𝓐 G i ϕ B-is-set 𝓑 j
 module B = free-algebra-eliminators 𝓑 G j γ A-is-set 𝓐 i

 private
  h : A → B
  h = A.unique-hom

  h-is-hom : is-hom 𝓐 𝓑 h
  h-is-hom = A.unique-hom-is-hom

  h-extends-j : h ∘ i ∼ j
  h-extends-j = A.unique-hom-is-extension

  h⁻¹ : B → A
  h⁻¹ = B.unique-hom

  h⁻¹-is-hom : is-hom 𝓑 𝓐 h⁻¹
  h⁻¹-is-hom = B.unique-hom-is-hom

  h⁻¹-extends-i : h⁻¹ ∘ j ∼ i
  h⁻¹-extends-i = B.unique-hom-is-extension

  I : is-hom 𝓐 𝓐 (h⁻¹ ∘ h)
  I = ∘-is-hom 𝓐 𝓑 𝓐 h h⁻¹ h-is-hom h⁻¹-is-hom

  II : is-hom 𝓑 𝓑 (h ∘ h⁻¹)
  II = ∘-is-hom 𝓑 𝓐 𝓑 h⁻¹ h h⁻¹-is-hom h-is-hom

  III : h⁻¹ ∘ h ∼ id
  III = at-most-one-extending-hom'
         (h⁻¹ ∘ h , I)
         (id , id-is-hom 𝓐)
         (λ g → h⁻¹ (h (i g)) ＝⟨ ap h⁻¹ (h-extends-j g) ⟩
                h⁻¹ (j g)     ＝⟨ h⁻¹-extends-i g ⟩
                i g           ∎)
         (λ (_ : G) → by-definition)
   where
    open free-algebra-eliminators
          𝓐 G i ϕ A-is-set 𝓐 i
  IV : h ∘ h⁻¹ ∼ id
  IV = at-most-one-extending-hom'
        (h ∘ h⁻¹ , II)
        (id , id-is-hom 𝓑)
        (λ g → h (h⁻¹ (j g)) ＝⟨ ap h (h⁻¹-extends-i g) ⟩
               h (i g)       ＝⟨ h-extends-j g ⟩
               j g           ∎)
        (λ (_ : G) → by-definition)
   where
    open free-algebra-eliminators
          𝓑 G j γ B-is-set 𝓑 j

 unique-hom-is-equiv : is-equiv h
 unique-hom-is-equiv = qinvs-are-equivs h (h⁻¹ , III , IV)

\end{code}

The following was moved here 5th Dec 2025 from another 2nd Dec 2025
file.

Any algebra isomorphic to the free algebra 𝓛 G in the category of
algebras is itself free.

\begin{code}

module _ (pe : Prop-Ext)
         (fe : Fun-Ext)
         {A        : 𝓥 ̇ }
         (A-is-set : is-set A)
         (G        : 𝓦 ̇ )
         (G-is-set : is-set G)
         (ι        : G → A)
         (𝓐        : 𝓛-alg A)
       where

 private
  open free-algebras-in-the-category-of-sets pe fe G G-is-set

  h : 𝓛 G → A
  h = 𝓛-extension A-is-set 𝓐 ι

  𝓛G : 𝓛-alg (𝓛 G)
  𝓛G = canonical-free-algebra

 module _ (h⁻¹               : A → 𝓛 G)
          (h⁻¹-is-section    : h ∘ h⁻¹ ∼ id)
          (h⁻¹-is-retraction : h⁻¹ ∘ h ∼ id)
          (h⁻¹-is-hom        : is-hom  𝓐 𝓛G h⁻¹)
      where

  𝓛-alg-isomorphic-to-free-𝓛-alg-is-itself-free : is-free-𝓛-alg 𝓐 G ι
  𝓛-alg-isomorphic-to-free-𝓛-alg-is-itself-free {𝓦} {B} B-is-set 𝓑 f = III
   where
    h-is-hom : is-hom 𝓛G 𝓐 h
    h-is-hom = 𝓛-extension-is-hom A-is-set 𝓐 ι

    h-extends-ι : h ∘ η ∼ ι
    h-extends-ι = 𝓛-extension-extends A-is-set 𝓐 ι

    h⁻¹-extends-η : h⁻¹ ∘ ι ∼ η
    h⁻¹-extends-η g = h⁻¹ (ι g)     ＝⟨ ap h⁻¹ (h-extends-ι g ⁻¹) ⟩
                      h⁻¹ (h (η g)) ＝⟨ h⁻¹-is-retraction (η g) ⟩
                      η g           ∎

    I : ∃! (f̅ , _) ꞉ Hom 𝓛G 𝓑 , f̅ ∘ η ∼ f
    I = 𝓛-is-free B-is-set 𝓑 f

    II : (Σ  (f̅ , _) ꞉ Hom 𝓛G 𝓑 , f̅ ∘ η ∼ f)
       → (∃! (f̅̅ , _) ꞉ Hom  𝓐 𝓑 , f̅̅ ∘ ι ∼ f)
    II ((f̅ , f̅-is-hom) , e) = II₁
     where
      f̅̅ : A → B
      f̅̅ = f̅ ∘ h⁻¹

      f̅̅-is-hom : is-hom 𝓐 𝓑 f̅̅
      f̅̅-is-hom = ∘-is-hom 𝓐 𝓛G 𝓑 h⁻¹ f̅ h⁻¹-is-hom f̅-is-hom

      e̅ :  f̅̅ ∘ ι ∼ f
      e̅ g = f̅̅ (ι g)       ＝⟨by-definition⟩
            f̅ (h⁻¹ (ι g)) ＝⟨ ap f̅ (h⁻¹-extends-η g) ⟩
            f̅ (η g)       ＝⟨ e g ⟩
            f g           ∎

      c : Σ (f̅̅ , _) ꞉ Hom 𝓐 𝓑 , f̅̅ ∘ ι ∼ f
      c = (f̅̅ , f̅̅-is-hom) , e̅

      II₀ : is-prop (type-of c)
      II₀ ((f₀ , f₀-is-hom) , e₀) ((f₁ , f₁-is-hom) , e₁) = II₀₁
       where
        f₀-agrees-with-f₁ : f₀ ∼ f₁
        f₀-agrees-with-f₁ π =
         f₀ π           ＝⟨ ap f₀ ((h⁻¹-is-section π)⁻¹) ⟩
         f₀ (h (h⁻¹ π)) ＝⟨ II₀₀ (h⁻¹ π) ⟩
         f₁ (h (h⁻¹ π)) ＝⟨ ap f₁ (h⁻¹-is-section π) ⟩
         f₁ π           ∎
          where
           II₀₀ : f₀ ∘ h ∼ f₁ ∘ h
           II₀₀ = hom-agreement B-is-set 𝓑 f
                   ((f₀ ∘ h , ∘-is-hom 𝓛G 𝓐 𝓑 h f₀ h-is-hom f₀-is-hom) ,
                    (λ g → f₀ (h (η g)) ＝⟨ ap f₀ (h-extends-ι g) ⟩
                           f₀ (ι g)     ＝⟨ e₀ g ⟩
                           f g          ∎))
                   ((f₁ ∘ h , ∘-is-hom 𝓛G 𝓐 𝓑 h f₁ h-is-hom f₁-is-hom) ,
                    (λ g → f₁ (h (η g)) ＝⟨ ap f₁ (h-extends-ι g) ⟩
                           f₁ (ι g)     ＝⟨ e₁ g ⟩
                           f g          ∎))

        II₀₁ : ((f₀ , f₀-is-hom) , e₀) ＝ ((f₁ , f₁-is-hom) , e₁)
        II₀₁ = to-subtype-＝
                (λ σ → Π-is-prop fe (λ (_ : G) → B-is-set))
                (to-subtype-＝
                  (λ (_ : A → B) → Π₃-is-prop fe (λ P i φ → B-is-set))
                  (dfunext fe f₀-agrees-with-f₁))

      II₁ : ∃! (f̅̅ , _) ꞉ Hom 𝓐 𝓑 , f̅̅ ∘ ι ∼ f
      II₁ = pointed-props-are-singletons c II₀

    III : ∃! (f̅̅ , _) ꞉ Hom 𝓐 𝓑 , f̅̅ ∘ ι ∼ f
    III = II (center I)
\end{code}

Added 23rd Nov 2025. Anders Kock' [1] definition of positive element.

[1] Anders Kock. The constructive lift monad.
    BRICS Report Series (Aarhus), ISSN 0909-0878 (1995)
    http://tildeweb.au.dk/au76680/CLM.pdf

\begin{code}

is-positive : {A : 𝓤 ̇ } → 𝓛-alg A → A → 𝓣 ⁺ ⊔ 𝓤 ̇
is-positive (⨆ , l₀ , l₁) a =
   (P : 𝓣 ̇ )
   (i : is-prop P)
 → ⨆ i (λ (_ : P) → a) ＝ a
 → P

being-positive-is-prop : Fun-Ext
                       → {A : 𝓤 ̇ }
                       → (𝓐 : 𝓛-alg A)
                       → (a : A) → is-prop (is-positive 𝓐 a)
being-positive-is-prop fe 𝓐 a = Π₃-is-prop fe (λ _ P-is-prop _ → P-is-prop)

\end{code}
