Todd Waugh Ambridge and Martin Escardo, 2nd March 2020.

We formalize, in univalent mathematics in Agda, some definitions in

M.H. Escardo and A. Simpson. A universal characterization of the
closed Euclidean interval (extended abstract). Proceedings of the 16th
Annual IEEE Symposium on Logic in Computer Science,
pp.115--125. Boston, Massachusetts, June 16-19, 2001.

https://www.cs.bham.ac.uk/~mhe/papers/lics2001-revised.pdf
https://www.cs.bham.ac.uk/~mhe/papers/interval.pdf
https://www.cs.bham.ac.uk/~mhe/.talks/map2011/

TODO. (Important.) The "double" stuff is not included yet.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Escardo-Simpson-LICS2001 where

open import SpartanMLTT
open import UF-Subsingletons

mid-point-algebra-axioms : (A : 𝓤 ̇ ) → (A → A → A) → 𝓤 ̇
mid-point-algebra-axioms {𝓤} A _⊕_ = is-set A × idempotency × commutativity × transposition
 where
  idempotency   = (x : A) → x ⊕ x ≡ x
  commutativity = (x y : A) → x ⊕ y ≡ y ⊕ x
  transposition = (x y u v : A) → (x ⊕ y) ⊕ (u ⊕ v) ≡ (x ⊕ u) ⊕ (y ⊕ v)

cancellative : {A : 𝓤 ̇ } → (A → A → A) → 𝓤 ̇
cancellative _⊕_ = ∀ x y z → x ⊕ z ≡ y ⊕ z → x ≡ y

iterative : {A : 𝓤 ̇ } → (A → A → A) → 𝓤 ̇
iterative {𝓤} {A} _⊕_ = Σ M ꞉ ((ℕ → A) → A) , ((a : ℕ → A) → M a ≡ a 0 ⊕ M (a ∘ succ))
                                            × ((a x : ℕ → A) → ((i : ℕ) → a i ≡ x i ⊕ a (succ i))
                                                             → a 0 ≡ M x)

\end{code}

We probably won't need the definition of Mid-point-algebra, but here
it is, for the record:

\begin{code}

Mid-point-algebra : (𝓤 : Universe) → 𝓤 ⁺ ̇
Mid-point-algebra 𝓤 = Σ A ꞉ 𝓤 ̇ , Σ _⊕_ ꞉ (A → A → A) , (mid-point-algebra-axioms A _⊕_)

Convex-body : (𝓤 : Universe) → 𝓤 ⁺ ̇
Convex-body 𝓤 = Σ A ꞉ 𝓤 ̇ , Σ _⊕_ ꞉ (A → A → A) , (mid-point-algebra-axioms A _⊕_)
                                                 × (cancellative _⊕_)
                                                 × (iterative _⊕_)

⟨_⟩ : Convex-body 𝓤 → 𝓤 ̇
⟨ A , _ ⟩ = A

mid-point-operation : (𝓐 : Convex-body 𝓤) → ⟨ 𝓐 ⟩ → ⟨ 𝓐 ⟩ → ⟨ 𝓐 ⟩
mid-point-operation (A , _⊕_ , _) = _⊕_

syntax mid-point-operation 𝓐 x y = x ⊕⟨ 𝓐 ⟩ y


is-interval-object : (𝓘 : Convex-body 𝓤) → ⟨ 𝓘 ⟩ → ⟨ 𝓘 ⟩ → 𝓤ω
is-interval-object {𝓤} 𝓘 u v =

     {𝓥 : Universe} (𝓐 : Convex-body 𝓥) (a b : ⟨ 𝓐 ⟩)
   → ∃! h ꞉ (⟨ 𝓘 ⟩ → ⟨ 𝓐 ⟩) , (h u ≡ a)
                            × (h v ≡ b)
                            × ((x y : ⟨ 𝓘 ⟩) → h (x ⊕⟨ 𝓘 ⟩ y) ≡ h x ⊕⟨ 𝓐 ⟩ h y)


record interval-object-exists (𝓤 : Universe) : 𝓤ω where
 field
  𝕀 : 𝓤 ̇
  _⊕_ : 𝕀 → 𝕀 → 𝕀
  u v : 𝕀
  mpaa : mid-point-algebra-axioms 𝕀 _⊕_
  ca : cancellative _⊕_
  ia : iterative _⊕_
  universal-property : is-interval-object (𝕀 , _⊕_ , mpaa , ca , ia) u v

\end{code}

TODO. being-interval-object-is-prop.

TODO. We need to axiomatize the existence of double (page 33 and
onwards of the slides).

\begin{code}

module basic-interval-object-development {𝓤 : Universe} (io : interval-object-exists 𝓤) where

\end{code}

To be continued.

In this submodule, we should develop the basic theory of the interval
object, with the constructions and theorems of the slides.

  * affine (page 11)

  * M (given in the iteration axiom)
    (By the way, we should prove that M is unique.)

  * Equational logic of M in page 16.

  * A homomorphism of _⊕_ is automatically an M homomorphism (page 17)

  * Adopt convention u = -1 and v = 1 for the following.

  * Definability of 1 - x and xy (multiplication) (page 19 uses the
    convention u = 0 and v = 1 so we should use page 24).

  * Medial power series (page 20 and 21).

  * Page 24: not only the definitions, but the fact that we get
    commutativity and associativity.

  * Page 25.

  * Page 35.

  * Page 42.
