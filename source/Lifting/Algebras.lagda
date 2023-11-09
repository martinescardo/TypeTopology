Martin Escardo 17th December 2018. (This has a connection with injectivity.)

We have a look at the algebras of the lifting monad.

\begin{code}

{-# OPTIONS --safe --without-K #-}

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

open import Lifting.IdentityViaSIP 𝓣
open import Lifting.Lifting 𝓣
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
    → (P → 𝓛 X) ≃ (Σ Q ꞉ (P → 𝓣 ̇ ), ((p : P) → Q p → X) × ((p : P) → is-prop (Q p)))
  γ X P = (P → Σ Q ꞉ 𝓣 ̇ , (Q → X) × is-prop Q)                                 ≃⟨ I ⟩
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

We can describe algebras in terms of "join" operations subject to two
laws:

\begin{code}

joinop : 𝓤 ̇ → 𝓣 ⁺ ⊔ 𝓤 ̇
joinop X = {P : 𝓣 ̇ } → is-prop P → (P → X) → X

\end{code}

The intuitive idea is that a "join" operation on X consists of, for
each proposition P, a map (P → X) → X that "puts together" the
elements of a family f : P → X to get an element ∐ f of X.

Unfortunately, we won't be able to write simply ∐ f in Agda notation,
as the witness that P is a proposition can almost never be
automatically inferred and hence has to be written explicitly.

To characterize algebras, the join operations have two satisfy the
following two laws:

\begin{code}

𝓛-alg-Law₀ : {X : 𝓤 ̇ } → joinop X → 𝓤 ̇
𝓛-alg-Law₀ {𝓤} {X} ∐ = (x : X) → ∐ 𝟙-is-prop (λ (p : 𝟙) → x) ＝ x

𝓛-alg-Law₁ : {X : 𝓤 ̇ } → joinop X → 𝓣 ⁺ ⊔ 𝓤 ̇
𝓛-alg-Law₁ {𝓤} {X} ∐ = (P : 𝓣 ̇ ) (Q : P → 𝓣 ̇ )
                        (i : is-prop P) (j : (p : P) → is-prop (Q p))
                        (f : Σ Q → X)
                      → ∐ (Σ-is-prop i j) f ＝ ∐ i (λ p → ∐ (j p) (λ q → f (p , q)))

\end{code}

Omitting the witnesses of proposition-hood, the above two laws can be
written in more standard mathematical notation as follows:

    ∐  x = x
   p:𝟙

    ∐          f r  =  ∐   ∐     f (p , q)
  r : Σ {P} Q         p:P q:Q(p)


\begin{code}

𝓛-alg : 𝓤 ̇ → 𝓣 ⁺ ⊔ 𝓤 ̇
𝓛-alg X = Σ ∐ ꞉ joinop X , 𝓛-alg-Law₀ ∐ × 𝓛-alg-Law₁ ∐

\end{code}

Before proving that we have an equivalence

  𝓛-algebra X ≃ 𝓛-alg X,

we characterize the algebra morphisms in terms of joins (unfortunately
overloading is not available):

\begin{code}

⋁ : {X : 𝓤 ̇ } → (𝓛 X → X) → joinop X
⋁ s {P} i f = s (P , f , i)

∐̇ : {X : 𝓤 ̇ } → 𝓛-algebra X → joinop X
∐̇ (s , _) = ⋁ s

∐ : {X : 𝓤 ̇ } → 𝓛-alg X → joinop X
∐ (∐ , κ , ι) = ∐

law₀ : {X : 𝓤 ̇ } (a : 𝓛-alg X) → 𝓛-alg-Law₀ (∐ a)
law₀ (∐ , κ , ι) = κ

law₁ : {X : 𝓤 ̇ } (a : 𝓛-alg X) → 𝓛-alg-Law₁ (∐ a)
law₁ (∐ , κ , ι) = ι


\end{code}

The algebra morphisms are the maps that preserve joins. Omitting the
first argument of ⋁, the following says that the morphisms are the
maps h : X → Y with

  h (⋁ f) ＝ ⋁ h (f p)
            p:P

for all f:P→X.

\begin{code}

𝓛-morphism-charac : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                    (s : 𝓛 X → X) (t : 𝓛 Y → Y)
                    (h : X → Y)

                  → (h ∘ s ∼ t ∘ 𝓛̇ h)
                  ≃ ({P : 𝓣 ̇ } (i : is-prop P) (f : P → X)
                       → h (⋁ s i f) ＝ ⋁ t i (λ p → h (f p)))
𝓛-morphism-charac s t h = qinveq (λ H {P} i f → H (P , f , i))
                                 ((λ {π (P , f , i) → π {P} i f}) ,
                                 (λ _ → refl) ,
                                 (λ _ → refl))

\end{code}

We name the other two projections of 𝓛-alg:

\begin{code}

𝓛-alg-const : {X : 𝓤 ̇ } (A : 𝓛-alg X) → (x : X) → ∐ A 𝟙-is-prop (λ (p : 𝟙) → x) ＝ x
𝓛-alg-const (∐ , κ , ι) = κ

𝓛-alg-iterated : {X : 𝓤 ̇ } (A : 𝓛-alg X)
                 (P : 𝓣 ̇ ) (Q : P → 𝓣 ̇ )
                 (i : is-prop P) (j : (p : P) → is-prop (Q p))
                 (f : Σ Q → X)
               → ∐ A (Σ-is-prop i j) f ＝ ∐ A i (λ p → ∐ A (j p) (λ q → f (p , q)))
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
  (λ P Q i j f → assoc (P , (λ p → Q p , (λ q → f (p , q)) , j p) , i))

𝓛-alg-gives-algebra : {X : 𝓤 ̇ } → 𝓛-alg X → 𝓛-algebra X
𝓛-alg-gives-algebra {𝓤} {X} (∐ , unit , ι) = s , unit , assoc
 where
  s : 𝓛 X → X
  s (P , f , i) = ∐ i f

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

𝓛-alg-Law₀' : {X : 𝓤 ̇ } → joinop X → 𝓣 ⁺ ⊔ 𝓤 ̇
𝓛-alg-Law₀' {𝓤} {X} ∐ = (P : 𝓣 ̇ )
                        (i : is-prop P)
                        (f : P → X)
                        (p : P)
                      → ∐ i f ＝ f p

𝓛-alg-Law₀-gives₀' : propext 𝓣
                   → funext 𝓣 𝓣
                   → funext 𝓣 𝓤
                   → {X : 𝓤 ̇ }
                     (∐ : joinop X)
                   → 𝓛-alg-Law₀ ∐
                   → 𝓛-alg-Law₀' ∐
𝓛-alg-Law₀-gives₀' pe fe fe' {X} ∐ κ P i f p = γ
 where
  r : f ＝ λ (_ : P) → f p
  r = dfunext fe' (λ p' → ap f (i p' p))

  s : P ＝ 𝟙 → ∐ {P} i f ＝ ∐ {𝟙} 𝟙-is-prop (λ (_ : 𝟙) → f p)
  s refl = ap₂ ∐ (being-prop-is-prop fe i 𝟙-is-prop) r

  t : P ＝ 𝟙
  t = pe i 𝟙-is-prop unique-to-𝟙 (λ _ → p)

  γ = ∐ {P} i f                   ＝⟨ s t ⟩
      ∐ 𝟙-is-prop (f ∘ (λ _ → p)) ＝⟨ κ (f p) ⟩
      f p                         ∎

𝓛-alg-Law₀'-gives₀ : {X : 𝓤 ̇ }
                     (∐ : joinop X)
                    → 𝓛-alg-Law₀' ∐
                    → 𝓛-alg-Law₀ ∐
𝓛-alg-Law₀'-gives₀ {𝓤} {X} ∐ φ x = φ 𝟙 𝟙-is-prop (λ _ → x) ⋆

\end{code}

We now consider a non-dependent version of 𝓛-alg-Law₁, and show that it is
equivalent to 𝓛-alg-Law₁:

\begin{code}

𝓛-alg-Law₁' : {X : 𝓤 ̇ } → joinop X → 𝓣 ⁺ ⊔ 𝓤 ̇
𝓛-alg-Law₁' {𝓤} {X} ∐ = (P Q : 𝓣 ̇ )
                        (i : is-prop P)
                        (j : is-prop Q)
                        (f : P × Q → X)
                           → ∐ (×-is-prop i j) f
                           ＝ ∐ i (λ p → ∐ j (λ q → f (p , q)))

\end{code}

The difference with 𝓛-alg-Law₁ is that the family f has type P × Q → X
rather than Σ {P} Q → X, and so the modified, logically equivalent law
amounts to

    ∐   ∐   f (p , q) =   ∐        f r
   p:P q:Q              r : P × Q

One direction of the logical equivalence is trivial:

\begin{code}

𝓛-alg-Law₁-gives₁' : {X : 𝓤 ̇ } (∐ : joinop X)
                   → 𝓛-alg-Law₁ ∐ → 𝓛-alg-Law₁' ∐
𝓛-alg-Law₁-gives₁' {𝓤} {X} ∐ a P Q i j = a P (λ _ → Q) i (λ p → j)

\end{code}

To establish the converse we need the following lemma for joins, which
is interesting on its own right,

  ∐  f p ＝ ∐  f (k q),
 p:P      q:Q

and also gives self-distributivity of joins:

  ∐   ∐  f (p , q) =   ∐   ∐  f (p , q)
 p:P q:Q              q:Q p:P


\begin{code}

change-of-variables-in-join : {X : 𝓤 ̇ } (∐ : joinop X)
                              (P : 𝓣 ̇ ) (i : is-prop P)
                              (Q : 𝓣 ̇ ) (j : is-prop Q)
                              (h : P → Q) (k : Q → P)
                              (f : P → X)
                            → is-univalent 𝓣
                            → ∐ i f ＝ ∐ j (f ∘ k)

change-of-variables-in-join ∐ P i Q j h k f ua = γ
 where
  cd : (r : Q ＝ P) → ∐ i f ＝ ∐ j (f ∘ Idtofun r)
  cd refl = ap (λ - → ∐ - f) (being-prop-is-prop (univalence-gives-funext ua) i j)

  e : Q ≃ P
  e = qinveq k (h , ((λ q → j (h (k q)) q) , λ p → i (k (h p)) p))

  a : Idtofun (eqtoid ua Q P e) ＝ k
  a = ap ⌜_⌝ (idtoeq'-eqtoid ua Q P e)

  γ : ∐ i f ＝ ∐ j (f ∘ k)
  γ = cd (eqtoid ua Q P e) ∙ ap (λ - → ∐ j (f ∘ -)) a

𝓛-alg-self-distr : {X : 𝓤 ̇ } (∐ : joinop X)
                   (P : 𝓣 ̇ ) (i : is-prop P)
                   (Q : 𝓣 ̇ ) (j : is-prop Q)
                 → is-univalent 𝓣
                 → 𝓛-alg-Law₁' ∐
                 → (f : P × Q → X)
                      → ∐ i (λ p → ∐ j (λ q → f (p , q)))
                      ＝ ∐ j (λ q → ∐ i (λ p → f (p , q)))

𝓛-alg-self-distr ∐ P i Q j ua l₁' f =
 ∐ i (λ p → ∐ j (λ q → f (p , q)))                     ＝⟨ a ⟩
 ∐ (Σ-is-prop i (λ p → j)) f                           ＝⟨ b ⟩
 ∐ (Σ-is-prop j (λ p → i)) (f ∘ (λ t → pr₂ t , pr₁ t)) ＝⟨ c ⟩
 ∐ j (λ q → ∐ i (λ p → f (p , q)))                     ∎
  where
   a = (l₁' P Q i j f)⁻¹
   b = change-of-variables-in-join
        ∐
        (P × Q)
        (Σ-is-prop i (λ p → j))
        (Q × P)
        (Σ-is-prop j (λ p → i))
        (λ t → pr₂ t , pr₁ t) (λ t → pr₂ t , pr₁ t) f ua
   c = l₁' Q P j i (λ t → f (pr₂ t , pr₁ t))

\end{code}

Using this we can prove the other direction of the logical equivalence
claimed above:

\begin{code}

𝓛-alg-Law₁'-gives₁ : {X : 𝓤 ̇ } (∐ : joinop X)
                    → is-univalent 𝓣
                    → funext 𝓣 𝓤
                    → 𝓛-alg-Law₁' ∐
                    → 𝓛-alg-Law₁ ∐
𝓛-alg-Law₁'-gives₁ {𝓤} {X} ∐ ua fe a P Q i j f = γ
 where
  h : (p : P) → Q p → Σ Q
  h p q = (p , q)

  k : (p : P) → Σ Q → Q p
  k p (p' , q) = transport Q (i p' p) q

  f' : P × Σ Q → X
  f' (p , p' , q) = f (p , k p (p' , q))

  k' : Σ Q → P × Σ Q
  k' (p , q) = p , p , q

  H : f' ∘ k' ∼ f
  H (p , q) = ap (λ - → f (p , -)) (j p _ _)

  γ = ∐ {Σ Q} (Σ-is-prop i j) f                                         ＝⟨ b ⟩
      ∐ {Σ Q} (Σ-is-prop i j) (f' ∘ k')                                 ＝⟨ c ⁻¹ ⟩
      ∐ {P × Σ Q} (×-is-prop i (Σ-is-prop i j)) f'                      ＝⟨ d ⟩
      ∐ {P} i (λ p → ∐ {Σ Q} (Σ-is-prop i j) ((λ σ → f (p , σ)) ∘ k p)) ＝⟨ e ⟩
      ∐ {P} i (λ p → ∐ {Q p} (j p) (λ q → f (p , q)))                   ∎
   where
    b = (ap (∐ {Σ Q} (Σ-is-prop i j)) (dfunext fe H))⁻¹
    c = change-of-variables-in-join
         ∐
         (P × Σ Q)
         (×-is-prop i (Σ-is-prop i j))
         (Σ Q)
         (Σ-is-prop i j) pr₂ k' f' ua
    d = a P (Σ Q) i (Σ-is-prop i j) (λ z → f (pr₁ z , k (pr₁ z) (pr₂ z)))
    e = (ap (∐ {P} i)
          (dfunext fe (λ p → change-of-variables-in-join
                              ∐
                              (Q p)
                              (j p)
                              (Σ Q) (Σ-is-prop i j)
                              (h p) (k p) (λ σ → f (p , σ)) ua)))⁻¹
\end{code}

The algebras form an exponential ideal with the pointwise
operations. More generally:

\begin{code}

Π-is-alg : funext 𝓤 𝓥
         → {X : 𝓤 ̇ } (A : X → 𝓥 ̇ )
         → ((x : X) → 𝓛-alg (A x)) → 𝓛-alg (Π A)
Π-is-alg {𝓤} {𝓥} fe {X} A α = ∐· , l₀ , l₁
 where
  ∐· : {P : 𝓣 ̇ } → is-prop P → (P → Π A) → Π A
  ∐· i f x = ∐ (α x) i (λ p → f p x)

  l₀ : (φ : Π A) → ∐· 𝟙-is-prop (λ p → φ) ＝ φ
  l₀ φ = dfunext fe (λ x → law₀ (α x) (φ x))

  l₁ : (P : 𝓣 ̇ ) (Q : P → 𝓣 ̇ )
       (i : is-prop P) (j : (p : P) → is-prop (Q p))
       (f : Σ Q → Π A)
      → ∐· (Σ-is-prop i j) f
      ＝ ∐· i (λ p → ∐· (j p) (λ q → f (p , q)))
  l₁ P Q i j f = dfunext fe (λ x → law₁ (α x) P Q i j (λ σ → f σ x))

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
      (j : (p : P) → is-prop (Q p)) (f : Σ Q → 𝓣 ̇ )
    → Σ f ＝ Σ (λ p → Σ (λ q → f (p , q)))
  ι P Q i j f = eqtoid ua _ _ Σ-assoc

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
      (j : (p : P) → is-prop (Q p)) (f : Σ Q → 𝓣 ̇ )
    → Π f ＝ Π (λ p → Π (λ q → f (p , q)))
  ι P Q i j f = eqtoid ua _ _ (curry-uncurry' fe fe)

\end{code}
