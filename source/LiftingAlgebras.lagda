Martin Escardo 17th December 2018. (This has a connection with injectivity.)

We have a look at the algebras of the lifting monad.

\begin{code}

open import SpartanMLTT

module LiftingAlgebras
        (𝓣 : Universe)
       where

open import UF-Base
open import UF-Subsingletons
open import UF-Subsingletons-FunExt
open import UF-Equiv
open import UF-EquivalenceExamples
open import UF-FunExt
open import UF-Univalence
open import UF-UA-FunExt

open import Lifting 𝓣
open import LiftingIdentityViaSIP 𝓣
open import LiftingMonad 𝓣

\end{code}


An element of 𝓛(𝓛 X) amounts to a family of partial elements of X
indexed by a proposition:

\begin{code}

double-𝓛-charac : (X : 𝓤 ̇)
                → 𝓛 (𝓛 X) ≃ Σ \(P : 𝓣 ̇)
                                   → (Σ \(Q : P → 𝓣 ̇) → ((p : P) → (Q p → X)) × ((p : P) → is-prop (Q p)))
                                   × is-prop P
double-𝓛-charac X = Σ-cong (λ P → ×-cong (γ X P) (≃-refl (is-prop P)))
 where
  γ : (X : 𝓤 ̇) (P : 𝓣 ̇) → (P → 𝓛 X) ≃ (Σ \(Q : P → 𝓣 ̇) → ((p : P) → (Q p → X)) × ((p : P) → is-prop (Q p)))
  γ X P = (P → Σ \(Q : 𝓣 ̇) → (Q → X) × is-prop Q)                               ≃⟨ ΠΣ-distr-≃ ⟩
          (Σ \(Q : P → 𝓣 ̇) → (p : P) → ((Q p → X) × is-prop (Q p)))             ≃⟨ Σ-cong (λ Q → →×) ⟩
          (Σ \(Q : P → 𝓣 ̇) → ((p : P) → (Q p → X)) × ((p : P) → is-prop (Q p))) ■

\end{code}

The usual definition of algebra of a monad:

\begin{code}


𝓛-algebra : 𝓤 ̇ → 𝓣 ⁺ ⊔ 𝓤 ̇
𝓛-algebra X = Σ \(s : 𝓛 X → X) → (s ∘ η ∼ id) × (s ∘ 𝓛̇ s ∼ s ∘ μ)

\end{code}

Which we will describe in terms of "join" operations subject to two laws:

\begin{code}

joinop : 𝓤 ̇ → 𝓣 ⁺ ⊔ 𝓤 ̇
joinop X = {P : 𝓣 ̇} → is-prop P → (P → X) → X

𝓛-alg-Law₀ : {X : 𝓤 ̇} → joinop X → 𝓤 ̇
𝓛-alg-Law₀ {𝓤} {X} ∐ = (x : X) → ∐ 𝟙-is-prop (λ (p : 𝟙) → x) ≡ x

𝓛-alg-Law₁ : {X : 𝓤 ̇} → joinop X → 𝓣 ⁺ ⊔ 𝓤 ̇
𝓛-alg-Law₁ {𝓤} {X} ∐ = (P : 𝓣 ̇) (Q : P → 𝓣 ̇) (i : is-prop P) (j : (p : P) → is-prop (Q p)) (f : Σ Q → X)
                          → ∐ i (λ p → ∐ (j p) (λ q → f (p , q))) ≡ ∐ (Σ-is-prop i j) f

𝓛-alg : 𝓤 ̇ → 𝓣 ⁺ ⊔ 𝓤 ̇
𝓛-alg X = Σ \(∐ : joinop X) → 𝓛-alg-Law₀ ∐ × 𝓛-alg-Law₁ ∐

\end{code}

Before proving that we have an equivalence 𝓛-algebra X ≃ 𝓛-alg X, we
characterize the algebra morphisms in terms of joins (unfortunately
overloading is not available):

\begin{code}

⋁ : {X : 𝓤 ̇} → (𝓛 X → X) → joinop X
⋁ s {P} i f = s (P , f , i)

∐̇ : {X : 𝓤 ̇} → 𝓛-algebra X → joinop X
∐̇ (s , _) = ⋁ s

∐ : {X : 𝓤 ̇} → 𝓛-alg X → joinop X
∐ (∐ , κ , ι) = ∐

\end{code}

The algebra morphisms are the maps that preserve joins.

\begin{code}

𝓛-morphism-charac : {X : 𝓤 ̇} {Y : 𝓥 ̇}
                    (s : 𝓛 X → X) (t : 𝓛 Y → Y)
                    (h : X → Y)

   → (h ∘ s ∼ t ∘ 𝓛̇ h) ≃ ({P : 𝓣 ̇} (i : is-prop P) (f : P → X) → h (⋁ s i f) ≡ ⋁ t i (λ p → h (f p)))
𝓛-morphism-charac s t h = qinveq (λ H {P} i f → H (P , f , i))
                                 ((λ {π (P , f , i) → π {P} i f}) ,
                                 (λ _ → refl) ,
                                 (λ _ → refl))

\end{code}

We name the other two projections of 𝓛-alg:

\begin{code}

𝓛-alg-const : {X : 𝓤 ̇} (A : 𝓛-alg X) → (x : X) → ∐ A 𝟙-is-prop (λ (p : 𝟙) → x) ≡ x
𝓛-alg-const (∐ , κ , ι) = κ

𝓛-alg-iterated : {X : 𝓤 ̇} (A : 𝓛-alg X)
                 (P : 𝓣 ̇) (Q : P → 𝓣 ̇) (i : is-prop P) (j : (p : P) → is-prop (Q p))
                 (f : Σ Q → X)
               → ∐ A i (λ p → ∐ A (j p) (λ q → f (p , q))) ≡ ∐ A (Σ-is-prop i j) f
𝓛-alg-iterated (∐ , κ , ι) = ι

\end{code}

We could write a proof of the following characterization of the
𝓛-algebras by composing equivalences as above, but it seems more
direct, and just as clear, to write a direct proof, by construction of
the equivalence and its inverse. This also emphasizes that the
equivalence is definitional, in the sense that the two required
equations hold definitionally.

\begin{code}

𝓛-algebra-gives-alg : {X : 𝓤 ̇} → 𝓛-algebra X → 𝓛-alg X
𝓛-algebra-gives-alg (s , κ , l) = ⋁ s ,
                                  κ ,
                                  (λ P Q i j f → l (P , (λ p → Q p , (λ q → f (p , q)) , j p) , i))

𝓛-alg-gives-algebra : {X : 𝓤 ̇} → 𝓛-alg X → 𝓛-algebra X
𝓛-alg-gives-algebra {𝓤} {X} (∐ , κ , ι) = s , κ , algebra-Law
 where
  s : 𝓛 X → X
  s (P , f , i) = ∐ i f
  algebra-Law : (l : 𝓛 (𝓛 X)) → s (𝓛̇ s l) ≡ s (μ l)
  algebra-Law (P , g , i) = ι P (pr₁ ∘ g) i (λ p → pr₂ (pr₂ (g p))) (λ r → pr₁ (pr₂ (g (pr₁ r))) (pr₂ r))

𝓛-alg-charac : {X : 𝓤 ̇} → 𝓛-algebra X ≃ 𝓛-alg X
𝓛-alg-charac = qinveq 𝓛-algebra-gives-alg (𝓛-alg-gives-algebra , ((λ _ → refl) , (λ _ → refl)))

\end{code}

We now consider a non-dependent version of 𝓛-alg-Law₁, and show that it is
equivalent to 𝓛-alg-Law₁:

\begin{code}

𝓛-alg-Law₁' : {X : 𝓤 ̇} → joinop X → 𝓣 ⁺ ⊔ 𝓤 ̇
𝓛-alg-Law₁' {𝓤} {X} ∐ = (P Q : 𝓣 ̇) (i : is-prop P) (j : is-prop Q) (f : P × Q → X)
                             → ∐ i (λ p → ∐ j (λ q → f (p , q))) ≡ ∐ (×-is-prop i j) f


𝓛-alg-Law₁-gives₁' : {X : 𝓤 ̇} (∐ : joinop X)
                   → 𝓛-alg-Law₁ ∐ → 𝓛-alg-Law₁' ∐
𝓛-alg-Law₁-gives₁' {𝓤} {X} ∐ a P Q i j = a P (λ _ → Q) i (λ p → j)

\end{code}

To establish the converse we need the following lemma for joins, which
is interesting on its own right and also gives commutativity of joins:

\begin{code}

change-of-variables-in-join : {X : 𝓤 ̇} (∐ : joinop X)
                              (P : 𝓣 ̇) (i : is-prop P)
                              (Q : 𝓣 ̇) (j : is-prop Q)
                              (h : P → Q) (k : Q → P) (f : P → X)
                            → is-univalent 𝓣
                            → ∐ i f ≡ ∐ j (f ∘ k)

change-of-variables-in-join ∐ P i Q j h k f ua = cd (eqtoid ua Q P e) ∙ ap (λ - → ∐ j (f ∘ -)) a
 where
  cd : (r : Q ≡ P) → ∐ i f ≡ ∐ j (f ∘ Idtofun r)
  cd refl = ap (λ - → ∐ - f) (being-a-prop-is-a-prop (funext-from-univalence ua) i j)
  e : Q ≃ P
  e = qinveq k (h , ((λ q → j (h (k q)) q) , λ p → i (k (h p)) p))
  a : Idtofun (eqtoid ua Q P e) ≡ k
  a = ap eqtofun (idtoeq'-eqtoid ua Q P e)


𝓛-alg-comm : {X : 𝓤 ̇} (∐ : joinop X)
             (P : 𝓣 ̇) (i : is-prop P)
             (Q : 𝓣 ̇) (j : is-prop Q)
           → is-univalent 𝓣
           → 𝓛-alg-Law₁' ∐
           → (f : P × Q → X) → ∐ i (λ p → ∐ j (λ q → f (p , q)))
                             ≡ ∐ j (λ q → ∐ i (λ p → f (p , q)))

𝓛-alg-comm ∐ P i Q j ua l₁' f = ∐ i (λ p → ∐ j (λ q → f (p , q)))                     ≡⟨ a ⟩
                                ∐ (Σ-is-prop i (λ p → j)) f                           ≡⟨ c ⟩
                                ∐ (Σ-is-prop j (λ p → i)) (f ∘ (λ t → pr₂ t , pr₁ t)) ≡⟨(b ⁻¹)⟩
                                ∐ j (λ q → ∐ i (λ p → f (p , q)))                     ∎
 where
  a = l₁' P Q i j f
  b = l₁' Q P j i (λ t → f (pr₂ t , pr₁ t))
  c = change-of-variables-in-join ∐ (P × Q) (Σ-is-prop i (λ p → j)) (Q × P) (Σ-is-prop j (λ p → i))
                                  (λ t → pr₂ t , pr₁ t) (λ t → pr₂ t , pr₁ t) f ua

𝓛-alg-Law₁'-gives₁ : {X : 𝓤 ̇} (∐ : joinop X)
                    → is-univalent 𝓣 → funext 𝓣 𝓤
                    → 𝓛-alg-Law₁' ∐ → 𝓛-alg-Law₁ ∐
𝓛-alg-Law₁'-gives₁ {𝓤} {X} ∐ ua fe a P Q i j f =
 ∐ {P} i (λ p → ∐ {Q p} (j p) (λ q → f (p , q)))                   ≡⟨ b ⟩
 ∐ {P} i (λ p → ∐ {Σ Q} (Σ-is-prop i j) ((λ σ → f (p , σ)) ∘ k p)) ≡⟨ c ⟩
 ∐ {P × Σ Q} (×-is-prop i (Σ-is-prop i j)) f'                      ≡⟨ d ⟩
 ∐ {Σ Q} (Σ-is-prop i j) (f' ∘ k')                                 ≡⟨ e ⟩
 ∐ {Σ Q} (Σ-is-prop i j) f ∎
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
  b = ap (∐ {P} i) (dfunext fe (λ p → change-of-variables-in-join ∐ (Q p) (j p) (Σ Q) (Σ-is-prop i j)
                                                                 (h p) (k p) (λ σ → f (p , σ)) ua))
  c = a P (Σ Q) i (Σ-is-prop i j) (λ z → f (pr₁ z , k (pr₁ z) (pr₂ z)))
  d = change-of-variables-in-join ∐ (P × Σ Q) (×-is-prop i (Σ-is-prop i j)) (Σ Q) (Σ-is-prop i j) pr₂ k' f' ua
  e = ap (∐ {Σ Q} (Σ-is-prop i j)) (dfunext fe H)

\end{code}

Crucial examples for injectivity.

\begin{code}

universe-is-algebra-Σ : is-univalent 𝓣 → 𝓛-alg (𝓣 ̇)
universe-is-algebra-Σ ua = sum , k , ι
 where
  sum : {P : 𝓣 ̇} → is-prop P → (P → 𝓣 ̇) → 𝓣 ̇
  sum {P} i = Σ
  k : (X : 𝓣 ̇) → Σ (λ p → X) ≡ X
  k X = eqtoid ua (𝟙 × X) X 𝟙-lneutral
  ι : (P : 𝓣 ̇) (Q : P → 𝓣 ̇) (i : is-prop P)
      (j : (p : P) → is-prop (Q p)) (f : Σ Q → 𝓣 ̇)
    → Σ (λ p → Σ (λ q → f (p , q))) ≡ Σ f
  ι P Q i j f = (eqtoid ua _ _ Σ-assoc)⁻¹

universe-is-algebra-Π : is-univalent 𝓣 → 𝓛-alg (𝓣 ̇)
universe-is-algebra-Π ua = prod , k , ι
 where
  fe : funext 𝓣 𝓣
  fe = funext-from-univalence ua
  prod : {P : 𝓣 ̇} → is-prop P → (P → 𝓣 ̇) → 𝓣 ̇
  prod {P} i = Π
  k : (X : 𝓣 ̇) → Π (λ p → X) ≡ X
  k X = eqtoid ua (𝟙 → X) X (≃-sym (𝟙→ (funext-from-univalence ua)))
  ι : (P : 𝓣 ̇) (Q : P → 𝓣 ̇) (i : is-prop P)
      (j : (p : P) → is-prop (Q p)) (f : Σ Q → 𝓣 ̇)
    → Π (λ p → Π (λ q → f (p , q))) ≡ Π f
  ι P Q i j f = (eqtoid ua _ _ (curry-uncurry' fe fe fe))⁻¹

{- Not true without additional hypotheses:
retract-of-𝓛-alg : {X : 𝓤 ̇} {Y : 𝓥 ̇} → retract Y of X → 𝓛-alg X → 𝓛-alg Y
retract-of-𝓛-alg {𝓤} {𝓥} {X} {Y} (ρ , σ , ρσ) (∐ , u , a) = (∐' , u' , a')
 where
  ∐' : {P : 𝓣 ̇} → is-prop P → (P → Y) → Y
  ∐' {P} i f = ρ (∐ i (σ ∘ f))
  u' : (y : Y) → ∐' 𝟙-is-prop (λ p → y) ≡ y
  u' y = ap ρ (u (σ y)) ∙ ρσ y
  a' : (P : 𝓣 ̇) (Q : P → 𝓣 ̇) (i : is-prop P)
       (j : (p : P) → is-prop (Q p)) (f : Σ Q → Y)
          → ∐' i (λ p → ∐' (j p) (λ q → f (p , q))) ≡ ∐' (Σ-is-prop i j) f
  a' P Q i j f = {!!}
    where
     bb : (p : P) → σ (ρ (∐ (j p) (λ q → σ (f (p , q)))))
                  ≡       ∐ (j p) (λ q → σ (f (p , q)))
     bb = {!!}
     aa : ∐ i (λ p → σ (∐' (j p) (λ q → f (p , q))))
        ≡ ∐ (Σ-is-prop i j) (σ ∘ f)
     aa = ∐ i (λ p → σ (∐' (j p) (λ q → f (p , q)))) ≡⟨ ap (∐ i) (dfunext {!!} bb) ⟩
          ∐ i (λ z → ∐ (j z) (λ q → σ (f (z , q)))) ≡⟨ {!!} ⟩
          {!!} ≡⟨ {!!} ⟩
          ∐ i (λ p → ∐ (j p) (λ q → σ (f (p , q))))  ≡⟨ a P Q i j (σ ∘ f) ⟩
          ∐ (Σ-is-prop i j) (σ ∘ f) ∎
     cc : ρ (∐ i (λ p → σ (∐' (j p) (λ q → f (p , q))))) ≡
            ρ (∐ (Σ-is-prop i j) (σ ∘ f))
     cc = ap ρ aa
-}

\end{code}
