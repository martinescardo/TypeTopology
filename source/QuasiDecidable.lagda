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
open import UF-PropTrunc
open import UF-Equiv
open import UF-Equiv-FunExt
open import UF-Univalence
open import UF-UA-FunExt
open import UF-EquivalenceExamples
open import UF-Yoneda
open import UF-SIP
open import UF-SIP-Examples

module QuasiDecidable where

\end{code}

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

We assume that it exists in the following:

\begin{code}

 module _ (is-quasidecidable : 𝓤₀ ̇ → 𝓤₀ ̇ )
          (being-quasidecidable-is-prop : ∀ P → is-prop (is-quasidecidable P))
          (𝟘-𝟙-ω-closure : 𝟘-𝟙-ω-closed is-quasidecidable)
          (quasidecidable-induction : ∀ {𝓤} (A : 𝓤₀ ̇ → 𝓤 ̇ ) → 𝟘-𝟙-ω-closed A → (P : 𝓤₀ ̇ ) → is-quasidecidable P → A P)
      where

  𝟘-is-quasidecidable : is-quasidecidable 𝟘
  𝟘-is-quasidecidable = pr₁ 𝟘-𝟙-ω-closure

  𝟙-is-quasi-decidable : is-quasidecidable 𝟙
  𝟙-is-quasi-decidable = pr₁ (pr₂ 𝟘-𝟙-ω-closure)

  quasidecidable-closed-under-ω-joins : ((P : ℕ → 𝓤₀ ̇ ) → ((n : ℕ) → is-quasidecidable (P n)) → is-quasidecidable (∃ n ꞉ ℕ , P n))
  quasidecidable-closed-under-ω-joins = pr₂ (pr₂ 𝟘-𝟙-ω-closure)

  quasidecidable-types-are-props : ∀ P → is-quasidecidable P → is-prop P
  quasidecidable-types-are-props = quasidecidable-induction is-prop (𝟘-is-prop , 𝟙-is-prop , λ P φ → ∃-is-prop)

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
      γ : is-quasidecidable ((∃ n ꞉ ℕ , P n) × Q)
      γ = transport is-quasidecidable (pe ∃-is-prop (×-prop-criterion ((λ _ → ∃-is-prop) , (λ e → quasidecidable-types-are-props Q (φ e)))) c d) b

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

In summary, the quasidecidable properties form a dominance, assuming
propositional extensionality:

\begin{code}

  quasidecidability-is-dominance : propext 𝓤₀ → is-dominance is-quasidecidable
  quasidecidability-is-dominance pe = being-quasidecidable-is-prop ,
                                      quasidecidable-types-are-props ,
                                      𝟙-is-quasi-decidable ,
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
           → (∃ n ꞉ ℕ , P × Q n) ≡ P × ∃ Q
  quasidecidable-σ-frame pe P i Q φ = pe ∃-is-prop
                                         (×-is-prop (quasidecidable-types-are-props P i)
                                                    (quasidecidable-types-are-props (∃ Q)
                                                    (quasidecidable-closed-under-ω-joins Q φ)))
                                         (quasidecidable-σ-frame-non-trivial P i Q φ)
                                         (quasidecidable-σ-frame-trivial P i Q φ)
\end{code}

We now define σ-frames. A σ-frame is a poset with countable joins and
finite meets such that binary meets distribute over countable joins.

We denote the empty meet (a top element) by ⊤, the binary meet by ∧,
and the countable join by ⋁. These are unary, binary and ℕ-ary
operations.

\begin{code}

σ-frame-structure : 𝓤 ̇ → 𝓤 ̇
σ-frame-structure X = X × (X → X → X) × ((ℕ → X) → X)

σ-frame-axioms : (X : 𝓤 ̇ ) → σ-frame-structure X → 𝓤 ̇
σ-frame-axioms {𝓤} X (⊤ , _∧_ , ⋁) = I × II × III × IV × V × VI × VII
 where
  I   = is-set X
  II  = (x : X) → x ∧ x ≡ x
  III = (x y : X) → x ∧ y ≡ y ∧ x
  IV  = (x y z : X) → x ∧ (y ∧ z) ≡ (x ∧ y) ∧ z
  V   = (x : X) → x ∧ ⊤ ≡ x
  VI  = (x : X) (𝕪 : ℕ → X) → x ∧ (⋁ 𝕪) ≡ ⋁ (i ↦ (x ∧ 𝕪 i))
  _≤_ : X → X → 𝓤 ̇
  x ≤ y = x ∧ y ≡ x
  VII = (𝕪 : ℕ → X)
      → ((i : ℕ) → 𝕪 i ≤ ⋁ 𝕪)
      × ((u : X) → ((i : ℕ) → 𝕪 i ≤ ⋁ 𝕪) → ⋁ 𝕪 ≤ u)
\end{code}

Axioms I-IV say that (X , ⊤ , ∧) is a bounded semilattice, axiom VII
says that ⋁ gives least upper bounds w.r.t. the induced partial order,
and axiom VI says that binary meets distribute over countable joins.

\begin{code}

σ-frame-axioms-is-prop : funext 𝓤 𝓤 → funext 𝓤₀ 𝓤
                       → (X : 𝓤 ̇ ) (s : σ-frame-structure X)
                       → is-prop (σ-frame-axioms X s)
σ-frame-axioms-is-prop fe fe₀ X (⊤ , _∧_ , ⋁) = prop-criterion δ
 where
  δ : σ-frame-axioms X (⊤ , _∧_ , ⋁) → is-prop (σ-frame-axioms X (⊤ , _∧_ , ⋁))
  δ (i , ii , iii , iv , v , vi) =
    ×-is-prop (being-set-is-prop fe)
   (×-is-prop (Π-is-prop fe (λ x →                                                   i {x ∧ x} {x}))
   (×-is-prop (Π-is-prop fe (λ x → Π-is-prop fe (λ y →                               i {x ∧ y} {y ∧ x})))
   (×-is-prop (Π-is-prop fe (λ x → Π-is-prop fe (λ y → Π-is-prop fe (λ z →           i {x ∧ (y ∧ z)} {(x ∧ y) ∧ z}))))
   (×-is-prop (Π-is-prop fe (λ x →                                                   i {x ∧ ⊤} {x}))
   (×-is-prop (Π-is-prop fe (λ x → Π-is-prop fe (λ y →                               i {x ∧ ⋁ y} {⋁ (i ↦ x ∧ y i)})))
              (Π-is-prop fe λ 𝕪 → ×-is-prop (Π-is-prop fe₀ (λ n →                    i {𝕪 n ∧ ⋁ 𝕪} {𝕪 n}))
                                            (Π-is-prop fe (λ x → Π-is-prop fe (λ _ → i {⋁ 𝕪 ∧ x} {⋁ 𝕪})))))))))

σ-Frame : (𝓤 : Universe) → 𝓤 ⁺ ̇
σ-Frame 𝓤 = Σ A ꞉ 𝓤 ̇ , Σ s ꞉ σ-frame-structure A , σ-frame-axioms A s

_≅[σ-Frame]_ : σ-Frame 𝓤 → σ-Frame 𝓤 → 𝓤 ̇
(A , (⊤ , _∧_ , ⋁) , _) ≅[σ-Frame] (A' , (⊤' , _∧'_ , ⋁') , _) =

                        Σ f ꞉ (A → A')
                            , is-equiv f
                            × (f ⊤ ≡ ⊤')
                            × ((λ a b → f (a ∧ b)) ≡ (λ a b → f a ∧' f b))
                            × ((λ 𝕒 → f (⋁ 𝕒)) ≡ (λ 𝕒 → ⋁' (i ↦ f (𝕒 i))))
\end{code}

TODO: is-univalent 𝓤 implies funext 𝓤₀ 𝓤 because funext 𝓤 𝓤 implies
funext 𝓤₀ 𝓤 (see MGS lecture notes for a proof). Hence the assumption
funext 𝓤₀ 𝓤 is superfluous in the following.

\begin{code}

characterization-of-σ-Frame-≡ : is-univalent 𝓤
                              → funext 𝓤₀ 𝓤
                              → (A B : σ-Frame 𝓤)
                              → (A ≡ B) ≃ (A ≅[σ-Frame] B)
characterization-of-σ-Frame-≡ ua fe₀ =
  sip.characterization-of-≡ ua
   (sip-with-axioms.add-axioms
      σ-frame-axioms
      (σ-frame-axioms-is-prop (univalence-gives-funext ua) fe₀)
     (sip-join.join
       pointed-type-identity.sns-data
     (sip-join.join
       ∞-magma-identity.sns-data
      (∞-bigmagma-identity.sns-data ℕ))))
\end{code}

To be continued. The first thing to do is to define the σ-frame of
quasidecidable propositions, and show that it is the homotopy initial
one.
