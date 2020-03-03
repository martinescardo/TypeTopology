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

 𝕀 = interval-object-exists.𝕀 io
 _⊕_ = interval-object-exists._⊕_ io
 u = interval-object-exists.u io
 v = interval-object-exists.v io
 
 mpaa = interval-object-exists.mpaa io
 ia = interval-object-exists.ia io
 
 ⊕-idem : (x : 𝕀) → x ⊕ x ≡ x
 ⊕-idem = pr₁ (pr₂ mpaa)

 ⊕-comm : (x y : 𝕀) → x ⊕ y ≡ y ⊕ x
 ⊕-comm = pr₁ (pr₂ (pr₂ mpaa))

 ⊕-tran : (x y u v : 𝕀) → (x ⊕ y) ⊕ (u ⊕ v) ≡ (x ⊕ u) ⊕ (y ⊕ v)
 ⊕-tran = pr₂ (pr₂ (pr₂ mpaa))

 ⊕-canc : (x y z : 𝕀) → x ⊕ z ≡ y ⊕ z → x ≡ y
 ⊕-canc = interval-object-exists.ca io

 𝓘 : Convex-body 𝓤
 𝓘 = 𝕀 , _⊕_ , mpaa , ⊕-canc , ia

 universal-property : {𝓥 : Universe} (𝓐 : Convex-body 𝓥) (a b : ⟨ 𝓐 ⟩)
   → ∃! h ꞉ (𝕀 → ⟨ 𝓐 ⟩) , (h u ≡ a)
                        × (h v ≡ b)
                        × ((x y : 𝕀) → h (x ⊕ y) ≡ h x ⊕⟨ 𝓐 ⟩ h y)
 universal-property = interval-object-exists.universal-property io

\end{code}

To be continued.

In this submodule, we should develop the basic theory of the interval
object, with the constructions and theorems of the slides.

  * affine (page 11)

\begin{code}

 affine : 𝕀 → 𝕀 → 𝕀 → 𝕀
 affine x y = ∃!-witness (universal-property 𝓘 x y)

 h-prop₁ : ∀ (x y : 𝕀) → affine x y u ≡ x
 h-prop₁ x y = pr₁ (∃!-is-witness (universal-property 𝓘 x y))

 h-prop₂ : ∀ (x y : 𝕀) → affine x y v ≡ y
 h-prop₂ x y = pr₁ (pr₂ (∃!-is-witness (universal-property 𝓘 x y)))

 h-prop₃ : ∀ (x y : 𝕀) → (a b : 𝕀) → affine x y (a ⊕ b) ≡ affine x y a ⊕ affine x y b
 h-prop₃ x y = pr₂ (pr₂ (∃!-is-witness (universal-property 𝓘 x y)))

 h-prop₄ : (x : 𝕀) → affine u v x ≡ x
 h-prop₄ x = {!!}

 h-prop₅ : (x y : 𝕀) → affine x x y ≡ y
 h-prop₅ x y = {!!}

\end{code}

  * M (given in the iteration axiom)
    (By the way, we should prove that M is unique.)

  * Equational logic of M in page 16.

\begin{code}

 M : (ℕ → 𝕀) → 𝕀
 M = pr₁ ia

 M-prop₁ : (a : ℕ → 𝕀) → M a ≡ a 0 ⊕ (M (a ∘ succ))
 M-prop₁ = pr₁ (pr₂ ia)

 M-prop₂ : (a x : ℕ → 𝕀) → ((i : ℕ) → a i ≡ x i ⊕ a (succ i)) → a 0 ≡ M x
 M-prop₂ = pr₂ (pr₂ ia)

 M-idem : ∀ (x : 𝕀) → M (λ _ → x) ≡ x
 M-idem x = M-prop₂ (λ _ → x) (λ _ → x) (λ _ → ⊕-idem x ⁻¹) ⁻¹

 M-symm : ∀ (x : ℕ → ℕ → 𝕀) → M (λ i → (M λ j → x i j)) ≡ M (λ i → M (λ j → x j i))
 M-symm x = M-prop₂ {!M (λ i → M (λ j → x j i))!} (λ i → M (x i)) {!!} ⁻¹

 M-homo : ∀ x y → (M x ⊕ M y) ≡ M (λ i → x i ⊕ y i)
 M-homo x y = {!!}

 M-homo× : ∀ x y → (M x ⊕ M y) ≡ M (λ i → x i ⊕ y i)
 M-homo× x y = ap (M x ⊕_) (M-prop₁ y)
            ∙ ap (_⊕ (y 0 ⊕ M (y ∘ succ))) (M-prop₁ x)
            ∙ ⊕-tran (x 0) (M (x ∘ succ)) (y 0) (M (y ∘ succ))
            ∙ ap ((x 0 ⊕ y 0) ⊕_) (M-homo× (λ z → x (succ z)) (λ z → y (succ z)))
            ∙ M-prop₁ (λ i → x i ⊕ y i) ⁻¹

-- (x y u v : 𝕀) → (x ⊕ y) ⊕ (u ⊕ v) ≡ (x ⊕ u) ⊕ (y ⊕ v)

\end{code}

  * A homomorphism of _⊕_ is automatically an M homomorphism (page 17)

\begin{code}

 M-homo' : (x y : 𝕀) (z : ℕ → 𝕀) → affine x y (M z) ≡
                           (affine x y (z 0) ⊕ affine x y (M (λ n → z (succ n))))
 M-homo' x y z = (ap (affine x y) (M-prop₁ z))
                       ∙ (h-prop₃ x y (z 0) (M (z ∘ succ)))

 affine-M-homo : (x y : 𝕀) → ∀ (z : ℕ → 𝕀) → affine x y (M z) ≡ M (λ n → affine x y (z n))
 affine-M-homo x y z = M-homo' x y z
                       ∙ {!!}
                       ∙ M-prop₁ (λ n → affine x y (z n)) ⁻¹


-- ∀ (x y : 𝕀) → (a b : 𝕀) → affine x y (a ⊕ b) ≡ affine x y a ⊕ affine x y b
-- 

\end{code}

  * Adopt convention u = -1 and v = 1 for the following.

  * Definability of 1 - x and xy (multiplication) (page 19 uses the
    convention u = 0 and v = 1 so we should use page 24).

\begin{code}

 ₋₁ ₀₀ ₊₁ : 𝕀
 ₋₁ = u
 ₊₁ = v
 ₀₀  = ₋₁ ⊕ ₊₁

 −_ : 𝕀 → 𝕀
 − x = affine ₊₁ ₋₁ x

 −-prop₁ : (− ₋₁) ≡ ₊₁ 
 −-prop₁ = h-prop₁ ₊₁ ₋₁

 −-prop₂ : (− ₊₁) ≡ ₋₁
 −-prop₂ = h-prop₂ ₊₁ ₋₁

 mul : 𝕀 → 𝕀 → 𝕀
 mul x y = affine (− x) x y 

 mul-prop₁ : (y : 𝕀) → mul ₋₁ y ≡ − y
 mul-prop₁ y = ap (λ - → affine - ₋₁ y) −-prop₁

 mul-prop₂ : (y : 𝕀) → mul ₊₁ y ≡ y
 mul-prop₂ y = ap (λ - → affine - ₊₁ y) −-prop₂ ∙ h-prop₄ y

 infixl 10 _*_

 𝕀-cases : (x : 𝕀) → (u ≡ x) + (v ≡ x) + (Σ \a → (Σ \b → (a ⊕ b) ≡ x))
 𝕀-cases x = inr (inr (x , x , (⊕-idem x)))

 *-comm : (x y : 𝕀) → affine (− x) x y ≡ affine (− y) y x
 *-comm x y = {!!}

 *-commu2 : (x y : 𝕀) → mul x u ≡ mul u x
 *-commu2 x y = h-prop₁ (− x) x ∙ ap (λ - → affine - u x) (−-prop₁ ⁻¹)

 *-commu3 : (x a b : 𝕀) → mul x (a ⊕ b) ≡ mul (a ⊕ b) x
 *-commu3 x a b = γ where
   γ : affine (− x) x (a ⊕ b) ≡ affine (− (a ⊕ b)) (a ⊕ b) x
   γ = h-prop₃ (− x) x a b
       ∙ {!!}


-- mul x y = affine (− x) x y 

\end{code}

  * Medial power series (page 20 and 21).

  * Page 24: not only the definitions, but the fact that we get
    commutativity and associativity.

  * Page 25.

  * Page 35.

  * Page 42.

\begin{code}

 ⊕-assoc : (x y z : 𝕀) → x ⊕ (y ⊕ z) ≡ (x ⊕ y) ⊕ z
 ⊕-assoc x y z = {!!}
