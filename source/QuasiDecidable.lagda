Martin Escardo, May 2020.

The quasidecidable propositions, defined below, generalize the
semidecidable propositions.  A weakening of the axiom of countable
choice is equivalent to the equivalence of semidecidability with
quasidecidability.

The quasidecidable propositions form a dominance, and their totality
defines the initial σ-frame.  A σ-frame is a poset with countable
joins and finite meets such that binary meets distribute over
countable joins.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import DecidableAndDetachable
open import Dominance
open import UF-PropTrunc renaming (⊥ to false ; ⊤ to true)
open import UF-Equiv
open import UF-Equiv-FunExt
open import UF-Univalence
open import UF-UA-FunExt
open import UF-EquivalenceExamples
open import UF-Yoneda
open import UF-SIP
open import UF-SIP-Examples
open import UF-Embeddings
open import UF-Powerset

module QuasiDecidable where

\end{code}


We now move to quasidecidable propositions, but we first review
semidecidable ones.

A proposition is semidecidable if it is a countable join of decidable
propositions. See the paper
https://www.cs.bham.ac.uk/~mhe/papers/partial-elements-and-recursion.pdf
by Martin Escardo and Cory Knapp.

NB. Semidecidable propositions are called Rosolini propositions in the above reference.

We assume the existence of propositional truncations for a while:

\begin{code}

module _ (pt : propositional-truncations-exist) where

 open PropositionalTruncation pt

 is-semidecidable : 𝓤 ̇ → 𝓤 ̇
 is-semidecidable X = ∃ α ꞉ (ℕ → 𝟚), X ≃ (∃ n ꞉ ℕ , α n ≡ ₁)

\end{code}

Exercise. X is semidecidable iff it is a countable join of decidable
propositions:

\begin{code}

 is-semidecidable' : 𝓤 ̇ → 𝓤 ⁺ ̇
 is-semidecidable' {𝓤} X = ∃ A ꞉ (ℕ → 𝓤 ̇ ), ((n : ℕ) → decidable (A n)) × (X ≃ (∃ n ꞉ ℕ , A n))

\end{code}

The following shows that we need to truncate, because the Cantor type
(ℕ → 𝟚) is certainly not the type of semidecidable propositions:

\begin{code}
 semidecidability-data : 𝓤 ̇ → 𝓤 ̇
 semidecidability-data X = Σ α ꞉ (ℕ → 𝟚), X ≃ (∃ n ꞉ ℕ , α n ≡ ₁)

 totality-of-semidecidability-data : is-univalent 𝓤₀
                                   → (Σ X ꞉ 𝓤₀ ̇ , semidecidability-data X) ≃ (ℕ → 𝟚)
 totality-of-semidecidability-data ua =

   (Σ X ꞉ 𝓤₀ ̇ , Σ α ꞉ (ℕ → 𝟚), X ≃ (∃ n ꞉ ℕ , α n ≡ ₁)) ≃⟨ i   ⟩
   (Σ α ꞉ (ℕ → 𝟚), Σ X ꞉ 𝓤₀ ̇ , X ≃ (∃ n ꞉ ℕ , α n ≡ ₁)) ≃⟨ ii  ⟩
   (Σ α ꞉ (ℕ → 𝟚), Σ X ꞉ 𝓤₀ ̇ , (∃ n ꞉ ℕ , α n ≡ ₁) ≃ X) ≃⟨ iii ⟩
   (ℕ → 𝟚) × 𝟙 {𝓤₀}                                     ≃⟨ iv  ⟩
   (ℕ → 𝟚)                                              ■
  where
   i   = Σ-flip
   ii  = Σ-cong (λ α → Σ-cong (λ X → ≃-Sym'' (univalence-gives-funext ua)))
   iii = Σ-cong (λ α → singleton-≃-𝟙 (univalence-via-singletons→ ua (∃ n ꞉ ℕ , α n ≡ ₁)))
   iv  = 𝟙-rneutral
\end{code}

The type of semidecidable propositions is not a σ-frame unless we have
enough countable choice - see the Escardo-Knapp reference above.

The set of quasidecidable propositions, if it exists, is the smallest
collection of propositions containing 𝟘 and 𝟙 and closed under
countable joins.

Exercise. It exists under propositional resizing assumptions (just
take the intersection of all 𝟘-𝟙-ω-closed subsets of Ω 𝓤₀).

\begin{code}

 𝟘-𝟙-ω-closed : (𝓤₀ ̇ → 𝓤 ̇ ) → 𝓤₁ ⊔ 𝓤 ̇
 𝟘-𝟙-ω-closed {𝓤} A = A 𝟘
                    × A 𝟙
                    × ((P : ℕ → 𝓤₀ ̇ ) → ((n : ℕ) → A (P n)) → A (∃ n ꞉ ℕ , P n))
\end{code}

We now assume that there is a smallest collection of types, called
quasidecidable, satisfying the above closure property. The types in
this collection are automatically propositions. The "smallest"
condition amounts to an induction principle.

\begin{code}

 module _ (is-quasidecidable : 𝓤₀ ̇ → 𝓤₀ ̇ )
          (being-quasidecidable-is-prop : ∀ P → is-prop (is-quasidecidable P))
          (𝟘-𝟙-ω-closure : 𝟘-𝟙-ω-closed is-quasidecidable)
          (quasidecidable-induction : ∀ {𝓤} (A : 𝓤₀ ̇ → 𝓤 ̇ )
                                    → 𝟘-𝟙-ω-closed A
                                    → (P : 𝓤₀ ̇ ) →  is-quasidecidable P → A P)
      where
\end{code}

We break apart the closure condition for notational convenience:

\begin{code}

  𝟘-is-quasidecidable : is-quasidecidable 𝟘
  𝟘-is-quasidecidable = pr₁ 𝟘-𝟙-ω-closure

  𝟙-is-quasidecidable : is-quasidecidable 𝟙
  𝟙-is-quasidecidable = pr₁ (pr₂ 𝟘-𝟙-ω-closure)

  quasidecidable-closed-under-ω-joins : ((P : ℕ → 𝓤₀ ̇ ) → ((n : ℕ) → is-quasidecidable (P n)) → is-quasidecidable (∃ n ꞉ ℕ , P n))
  quasidecidable-closed-under-ω-joins = pr₂ (pr₂ 𝟘-𝟙-ω-closure)

\end{code}

As promised, the quasidecidable types are automatically propositions,
with a proof by induction:

\begin{code}

  quasidecidable-types-are-props : ∀ P → is-quasidecidable P → is-prop P
  quasidecidable-types-are-props = quasidecidable-induction is-prop (𝟘-is-prop , 𝟙-is-prop , λ P φ → ∃-is-prop)

\end{code}

And they form a dominance, again with a proof by induction. The main
dominance condition generalizes closure under binary products (that
is, conjunctions, or meets):

\begin{code}

  quasidecidable-dom : propext 𝓤₀
                     → (P : 𝓤₀ ̇ )
                     → is-quasidecidable P
                     → (Q : 𝓤₀ ̇ )
                     → (P → is-quasidecidable Q)
                     → is-quasidecidable (P × Q)
  quasidecidable-dom pe = quasidecidable-induction A (a₀ , a₁ , aω)
   where
    A : 𝓤₀ ̇ → 𝓤₁ ̇
    A P = (Q : 𝓤₀ ̇ ) → (P → is-quasidecidable Q) → is-quasidecidable (P × Q)
    a₀ : A 𝟘
    a₀ Q φ = transport is-quasidecidable r 𝟘-is-quasidecidable
     where
      r : 𝟘 ≡ 𝟘 × Q
      r = pe 𝟘-is-prop (λ (z , q) → 𝟘-elim z) unique-from-𝟘 pr₁
    a₁ : A 𝟙
    a₁ Q φ = transport is-quasidecidable r (φ *)
     where
      i : is-prop Q
      i = quasidecidable-types-are-props Q (φ *)
      r : Q ≡ 𝟙 × Q
      r = pe i (×-is-prop 𝟙-is-prop i) (λ q → (* , q)) pr₂
    aω :  (P : ℕ → 𝓤₀ ̇ ) → ((n : ℕ) → A (P n)) → A (∃ n ꞉ ℕ , P n)
    aω P f Q φ = γ
     where
      φ' : (n : ℕ) → P n → is-quasidecidable Q
      φ' n p = φ ∣ n , p ∣
      a : (n : ℕ) → is-quasidecidable (P n × Q)
      a n = f n Q (φ' n)
      b : is-quasidecidable (∃ n ꞉ ℕ , P n × Q)
      b = quasidecidable-closed-under-ω-joins (λ n → P n × Q) a
      c : (∃ n ꞉ ℕ , P n × Q) → ((∃ n ꞉ ℕ , P n) × Q)
      c s = (t , q)
       where
        t : ∃ n ꞉ ℕ , P n
        t = ∥∥-rec ∃-is-prop (λ (n , (p , q)) → ∣ n , p ∣) s
        i : is-prop Q
        i = quasidecidable-types-are-props Q (φ t)
        q : Q
        q = ∥∥-rec i (λ (n , (p , q)) → q) s
      d : ((∃ n ꞉ ℕ , P n) × Q) → (∃ n ꞉ ℕ , P n × Q)
      d (t , q) = ∥∥-functor (λ (n , p) → n , (p , q)) t
      r : (∃ n ꞉ ℕ , P n × Q) ≡ ((∃ n ꞉ ℕ , P n) × Q)
      r = pe ∃-is-prop
            (×-prop-criterion ((λ _ → ∃-is-prop) ,
                               (λ e → quasidecidable-types-are-props Q (φ e))))
            c d
      γ : is-quasidecidable ((∃ n ꞉ ℕ , P n) × Q)
      γ = transport is-quasidecidable r b

\end{code}

This condition automatically implies closure under Σ, or joins indexed
by quasidecidable propositions:

\begin{code}

  quasidecidable-closed-under-Σ : propext 𝓤₀
                                 → (P : 𝓤₀ ̇ )
                                 → (Q : P → 𝓤₀ ̇ )
                                 → is-quasidecidable P
                                 → ((p : P) → is-quasidecidable (Q p))
                                 → is-quasidecidable (Σ Q)
  quasidecidable-closed-under-Σ pe = D3-and-D5'-give-D5 pe is-quasidecidable
                                       quasidecidable-types-are-props
                                       (λ P Q' i j → quasidecidable-dom pe P i Q' j)

\end{code}

Notice that Σ Q is equivalent to ∃ Q as quasidecidable types are
propositions.

The following summarizes the dominance conditions:

\begin{code}

  quasidecidability-is-dominance : propext 𝓤₀ → is-dominance is-quasidecidable
  quasidecidability-is-dominance pe = being-quasidecidable-is-prop ,
                                      quasidecidable-types-are-props ,
                                      𝟙-is-quasidecidable ,
                                      quasidecidable-closed-under-Σ pe
\end{code}

We now show that binary meets (cartesian products) of quasidecidable
properties distribute over countable joins (existential
quantifications over ℕ). One direction is trivial, and the other
follows by induction:

\begin{code}

  quasidecidable-σ-frame-trivial :
             (P : 𝓤₀ ̇ )
           → is-quasidecidable P
           → (Q : ℕ → 𝓤₀ ̇ )
           → ((n : ℕ) → is-quasidecidable (Q n))
           → P × ∃ Q → ∃ n ꞉ ℕ , P × Q n
  quasidecidable-σ-frame-trivial P i Q φ (p , e) = ∥∥-rec ∃-is-prop (λ (n , q) → ∣ n , p , q ∣) e


  quasidecidable-σ-frame-non-trivial :
             (P : 𝓤₀ ̇ )
           → is-quasidecidable P
           → (Q : ℕ → 𝓤₀ ̇ )
           → ((n : ℕ) → is-quasidecidable (Q n))
           → (∃ n ꞉ ℕ , P × Q n) → P × ∃ Q
  quasidecidable-σ-frame-non-trivial = quasidecidable-induction A (a₀ , a₁ , aω)
   where
    A : 𝓤₀ ̇ → 𝓤₁ ̇
    A P = (Q : ℕ → 𝓤₀ ̇ )
        → ((n : ℕ) → is-quasidecidable (Q n))
        → (∃ n ꞉ ℕ , P × Q n) → P × ∃ Q
    a₀ : A 𝟘
    a₀ Q φ e = 𝟘-elim (∥∥-rec 𝟘-is-prop (λ (n , z , q) → z) e)
    a₁ : A 𝟙
    a₁ Q φ e = * , (∥∥-rec ∃-is-prop (λ (n , o , q) → ∣ n , q ∣) e)
    aω : (P : ℕ → 𝓤₀ ̇ ) → ((n : ℕ) → A (P n)) → A (∃ P)
    aω P f Q φ e = ∥∥-rec ∃-is-prop (λ (n , ep , q) → ep) e , ∥∥-rec ∃-is-prop ((λ (n , ep , q) → ∣ n , q ∣)) e

\end{code}

Putting the two directions together with the aid of propositional
extensionality, we get the σ-frame distributive law:

\begin{code}

  quasidecidable-σ-frame : propext 𝓤₀
           → (P : 𝓤₀ ̇ )
           → is-quasidecidable P
           → (Q : ℕ → 𝓤₀ ̇ )
           → ((n : ℕ) → is-quasidecidable (Q n))
           → P × ∃ Q ≡ (∃ n ꞉ ℕ , P × Q n)
  quasidecidable-σ-frame pe P i Q φ = pe (×-is-prop (quasidecidable-types-are-props P i)
                                                    (quasidecidable-types-are-props (∃ Q)
                                                    (quasidecidable-closed-under-ω-joins Q φ)))
                                         ∃-is-prop
                                         (quasidecidable-σ-frame-trivial P i Q φ)
                                         (quasidecidable-σ-frame-non-trivial P i Q φ)
\end{code}

Next we define the σ-frame QD of quasidecidable propositions, with
underlying type 𝓠.

\begin{code}

  𝓠 : 𝓤₁ ̇
  𝓠 = Σ P ꞉ 𝓤₀ ̇ , is-quasidecidable P

  _is-true : 𝓠 → 𝓤₀ ̇
  _is-true (P , i) = P

  being-true-is-quasidecidable : (𝕡 : 𝓠) → is-quasidecidable (𝕡 is-true)
  being-true-is-quasidecidable (P , i) = i

  being-true-is-prop : (𝕡 : 𝓠) → is-prop (𝕡 is-true)
  being-true-is-prop (P , i) = quasidecidable-types-are-props P i

  𝓠→Ω : 𝓠 → Ω 𝓤₀
  𝓠→Ω (P , i) = P , quasidecidable-types-are-props P i

  𝓠→Ω-is-embedding : funext 𝓤₀ 𝓤₀ → is-embedding 𝓠→Ω
  𝓠→Ω-is-embedding fe₀ = NatΣ-is-embedding is-quasidecidable is-prop ζ ζ-is-embedding
   where
    ζ : (P : 𝓤₀ ̇ ) → is-quasidecidable P → is-prop P
    ζ = quasidecidable-types-are-props
    ζ-is-embedding : (P : 𝓤₀ ̇ ) → is-embedding (ζ P)
    ζ-is-embedding P = maps-of-props-are-embeddings (ζ P) (being-quasidecidable-is-prop P) (being-prop-is-prop fe₀)

\end{code}

We now assume functional and propositional extensionality for the
first universe to give the quasidecidable propositions the structure
of a σ-frame:

\begin{code}

  module _ (fe₀ : funext 𝓤₀ 𝓤₀)
           (pe₀ : propext 𝓤₀)
         where

   𝓠-is-set : is-set 𝓠
   𝓠-is-set = subtypes-of-sets-are-sets 𝓠→Ω (embeddings-are-lc 𝓠→Ω (𝓠→Ω-is-embedding fe₀)) (Ω-is-set fe₀ pe₀)

\end{code}

We make the following definitions private in order to have the general
symbols available in other contexts, but they are still available as
the structure and axioms of the σ-frame QD of quasidecidable
proposition:

\begin{code}

   private ⊥ : 𝓠
   ⊥ = 𝟘 , 𝟘-is-quasidecidable

   private ⊤ : 𝓠
   ⊤ = 𝟙 , 𝟙-is-quasidecidable

   private _∧_ : 𝓠 → 𝓠 → 𝓠
   (P , i) ∧ (Q , j) = (P × Q) , quasidecidable-dom pe₀ P i Q (λ _ → j)

   private ⋁ : (ℕ → 𝓠) → 𝓠
   ⋁ 𝕡 = (∃ n ꞉ ℕ , 𝕡 n is-true) ,
          quasidecidable-closed-under-ω-joins
            (λ n → 𝕡 n is-true)
            (λ n → being-true-is-quasidecidable (𝕡 n))

   private ∧-is-idempotent : (𝕡 : 𝓠) → 𝕡 ∧ 𝕡 ≡ 𝕡
   ∧-is-idempotent (P , i) = γ
    where
     i' : is-prop P
     i' = quasidecidable-types-are-props P i
     a : P × P ≡ P
     a = pe₀ (×-is-prop i' i') i' pr₁ (λ p → (p , p))
     γ : ((P × P) , _) ≡ (P , _)
     γ = to-subtype-≡ being-quasidecidable-is-prop a

   private ∧-is-commutative : (𝕡 𝕢 : 𝓠) → 𝕡 ∧ 𝕢 ≡ 𝕢 ∧ 𝕡
   ∧-is-commutative (P , i) (Q , j) = γ
    where
     i' : is-prop P
     i' = quasidecidable-types-are-props P i
     j' : is-prop Q
     j' = quasidecidable-types-are-props Q j
     a : P × Q ≡ Q × P
     a = pe₀ (×-is-prop i' j')
             (×-is-prop j' i')
             (λ (p , q) → (q , p))
             (λ (q , p) → (p , q))
     γ : ((P × Q) , _) ≡ ((Q × P) , _)
     γ = to-subtype-≡ being-quasidecidable-is-prop a

   private ∧-is-associative : (𝕡 𝕢 𝕣 : 𝓠) → 𝕡 ∧ (𝕢 ∧ 𝕣) ≡ (𝕡 ∧ 𝕢) ∧ 𝕣
   ∧-is-associative (P , i) (Q , j) (R , k) = γ
    where
     i' : is-prop P
     i' = quasidecidable-types-are-props P i
     j' : is-prop Q
     j' = quasidecidable-types-are-props Q j
     k' : is-prop R
     k' = quasidecidable-types-are-props R k
     a : P × (Q × R) ≡ (P × Q) × R
     a = pe₀ (×-is-prop i' (×-is-prop j' k'))
             (×-is-prop (×-is-prop i' j') k')
             (λ (p , (q , r)) → ((p , q) , r))
             (λ ((p , q) , r) → (p , (q , r)))
     γ : ((P × (Q × R)) , _) ≡ (((P × Q) × R) , _)
     γ = to-subtype-≡ being-quasidecidable-is-prop a

   private ⊥-is-minimum : (𝕡 : 𝓠) → ⊥ ∧ 𝕡 ≡ ⊥
   ⊥-is-minimum (P , i) = γ
    where
     i' : is-prop P
     i' = quasidecidable-types-are-props P i
     a : 𝟘 × P ≡ 𝟘
     a = pe₀ (×-is-prop 𝟘-is-prop i')
             𝟘-is-prop
             pr₁
             unique-from-𝟘
     γ : ((𝟘 × P) , _) ≡ (𝟘 , _)
     γ = to-subtype-≡ being-quasidecidable-is-prop a

   private ⊤-is-maximum : (𝕡 : 𝓠) → 𝕡 ∧ ⊤ ≡ 𝕡
   ⊤-is-maximum (P , i) = γ
    where
     i' : is-prop P
     i' = quasidecidable-types-are-props P i
     a : P × 𝟙 ≡ P
     a = pe₀ (×-is-prop i' 𝟙-is-prop)
             i'
             (λ (p , _) → p)
             (λ p → (p , *))
     γ : ((P × 𝟙) , _) ≡ (P , _)
     γ = to-subtype-≡ being-quasidecidable-is-prop a

   private _≤_ : 𝓠 → 𝓠 → 𝓤₁ ̇
   𝕡 ≤ 𝕢 = 𝕡 ∧ 𝕢 ≡ 𝕡

   private ≤-is-prop-valued : (𝕡 𝕢 : 𝓠) → is-prop (𝕡 ≤ 𝕢)
   ≤-is-prop-valued 𝕡 𝕢 = 𝓠-is-set {𝕡 ∧ 𝕢} {𝕡}

   private ≤-characterization→ : {𝕡 𝕢 : 𝓠} → 𝕡 ≤ 𝕢 → (𝕡 is-true → 𝕢 is-true)
   ≤-characterization→ {P , i} {Q , j} l p = γ
    where
     a : P × Q ≡ P
     a = ap (_is-true) l
     g : P → P × Q
     g = idtofun P (P × Q) (a ⁻¹)
     γ : Q
     γ = pr₂ (g p)

   private ≤-characterization← : {𝕡 𝕢 : 𝓠} → (𝕡 is-true → 𝕢 is-true) → 𝕡 ≤ 𝕢
   ≤-characterization← {P , i} {Q , j} f = γ
    where
     i' : is-prop P
     i' = quasidecidable-types-are-props P i
     j' : is-prop Q
     j' = quasidecidable-types-are-props Q j
     a : P × Q ≡ P
     a = pe₀ (×-is-prop i' j') i' pr₁ (λ p → (p , f p))
     γ : ((P × Q) , _) ≡ (P , _)
     γ = to-subtype-≡ being-quasidecidable-is-prop a

   private ≤-characterization : {𝕡 𝕢 : 𝓠} → (𝕡 ≤ 𝕢) ≃ (𝕡 is-true → 𝕢 is-true)
   ≤-characterization {𝕡} {𝕢} = logically-equivalent-props-are-equivalent
                                (≤-is-prop-valued 𝕡 𝕢)
                                (Π-is-prop fe₀ (λ _ → being-true-is-prop 𝕢))
                                (≤-characterization→ {𝕡} {𝕢})
                                (≤-characterization← {𝕡} {𝕢})

\end{code}

NB. We can't conclude equality above because the lhs and rhs live in different universes and hence in different types.

\begin{code}

   private distributivity : (𝕡 : 𝓠) (𝕢 : ℕ → 𝓠) → 𝕡 ∧ (⋁ 𝕢) ≡ ⋁ (n ↦ (𝕡 ∧ 𝕢 n))
   distributivity (P , i) 𝕢 = γ
    where
     Q : ℕ → 𝓤₀ ̇
     Q n = 𝕢 n is-true
     j : (n : ℕ) → is-quasidecidable (Q n)
     j n = being-true-is-quasidecidable (𝕢 n)
     a : P × (∃ n ꞉ ℕ , Q n) ≡ (∃ n ꞉ ℕ , P × Q n)
     a = quasidecidable-σ-frame pe₀ P i Q j
     γ : ((P × (∃ n ꞉ ℕ , Q n)) , _) ≡ ((∃ n ꞉ ℕ , P × Q n) , _)
     γ = to-subtype-≡ being-quasidecidable-is-prop a

   private ⋁-is-lub : (𝕡 : ℕ → 𝓠)
            → ((n : ℕ) → 𝕡 n ≤ ⋁ 𝕡)
            × ((𝕦 : 𝓠) → ((n : ℕ) → 𝕡 n ≤ 𝕦) → ⋁ 𝕡 ≤ 𝕦 )
   ⋁-is-lub 𝕡 = a , b
    where
     a : (n : ℕ) → 𝕡 n ≤ ⋁ 𝕡
     a n = ≤-characterization← (λ p → ∣ n , p ∣)
     b : (𝕦 : 𝓠) → ((n : ℕ) → 𝕡 n ≤ 𝕦) → ⋁ 𝕡 ≤ 𝕦
     b (U , i) φ = ≤-characterization← d
      where
       c : (Σ n ꞉ ℕ , 𝕡 n is-true) → U
       c (n , p) = ≤-characterization→ (φ n) p
       d : (∃ n ꞉ ℕ , 𝕡 n is-true) → U
       d = ∥∥-rec (quasidecidable-types-are-props U i) c

   open σ-frame

   QD : σ-Frame 𝓤₁
   QD = 𝓠 ,
       (⊤ , _∧_ , ⊥ , ⋁) ,
       (𝓠-is-set ,
        ∧-is-idempotent ,
        ∧-is-commutative ,
        ∧-is-associative ,
        ⊥-is-minimum ,
        ⊤-is-maximum ,
        distributivity ,
        ⋁-is-lub)
\end{code}

To be continued. Next we show that QD is the initial σ-frame:

\begin{code}
{-
   QD-is-initial-σ-Frame : (𝓐 : σ-Frame 𝓤)
     → ∃! f ꞉ (⟨ QD ⟩ → ⟨ 𝓐 ⟩), is-σ-frame-homomorphism QD 𝓐 f
   QD-is-initial-σ-Frame (A , (⊤' , _∧'_ , ⊥' , ⋁') , axioms) = (f , h) , c
    where
     𝓐 = (A , (⊤' , _∧'_ , ⊥' , ⋁') , axioms)
     f : 𝓠 → A
     f = {!!}
     h : is-σ-frame-homomorphism QD 𝓐 f
     h = {!!}
     c : ((g , k) : Σ g ꞉ (⟨ QD ⟩ → ⟨ 𝓐 ⟩), is-σ-frame-homomorphism QD 𝓐 g) → ((f , h) ≡ (g , k))
     c = {!!}
-}
\end{code}
