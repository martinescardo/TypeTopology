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
                                            × ((a x : ℕ → A)
                                               → ((i : ℕ) → a i ≡ x i ⊕ a (succ i))
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

is-homomorphism : (𝓐 : Convex-body 𝓤) (𝓑 : Convex-body 𝓥)
                → (⟨ 𝓐 ⟩ → ⟨ 𝓑 ⟩) → 𝓤 ⊔ 𝓥 ̇
is-homomorphism 𝓐 𝓑 h = (x y : ⟨ 𝓐 ⟩) → h (x ⊕⟨ 𝓐 ⟩ y) ≡ h x ⊕⟨ 𝓑 ⟩ h y

id-is-homomorphism : (𝓐 : Convex-body 𝓤) → is-homomorphism 𝓐 𝓐 id
id-is-homomorphism 𝓐 x y = refl

⊕-is-homomorphism-r : (𝓐 : Convex-body 𝓤)
                    → (a : ⟨ 𝓐 ⟩) → is-homomorphism 𝓐 𝓐 (λ y → a ⊕⟨ 𝓐 ⟩ y)
⊕-is-homomorphism-r (𝓐 , _⊕_ , (_ , ⊕-idem , _ , ⊕-tran) , _) a x y
 =    a    ⊕ (x ⊕ y) ≡⟨ ap (_⊕ (x ⊕ y)) (⊕-idem a ⁻¹) ⟩
   (a ⊕ a) ⊕ (x ⊕ y) ≡⟨ ⊕-tran a a x y ⟩
   (a ⊕ x) ⊕ (a ⊕ y) ∎

⊕-is-homomorphism-l : (𝓐 : Convex-body 𝓤)
                    → (b : ⟨ 𝓐 ⟩) → is-homomorphism 𝓐 𝓐 (λ x → x ⊕⟨ 𝓐 ⟩ b)
⊕-is-homomorphism-l (𝓐 , _⊕_ , (_ , ⊕-idem , _ , ⊕-tran) , _) b x y
 = (x ⊕ y) ⊕    b    ≡⟨ ap ((x ⊕ y) ⊕_) (⊕-idem b ⁻¹) ⟩
   (x ⊕ y) ⊕ (b ⊕ b) ≡⟨ ⊕-tran x y b b ⟩
   (x ⊕ b) ⊕ (y ⊕ b) ∎

homomorphism-composition : (𝓐 : Convex-body 𝓤) (𝓑 : Convex-body 𝓥) (𝓒 : Convex-body 𝓦)
                          → (h₁ : ⟨ 𝓐 ⟩ → ⟨ 𝓑 ⟩) → (h₂ : ⟨ 𝓑 ⟩ → ⟨ 𝓒 ⟩)
                          → is-homomorphism 𝓐 𝓑 h₁ → is-homomorphism 𝓑 𝓒 h₂
                          → is-homomorphism 𝓐 𝓒 (h₂ ∘ h₁)
homomorphism-composition {𝓤} {𝓥} {𝓦} 𝓐 𝓑 𝓒 h₁ h₂ i₁ i₂ x y
 = (h₂ ∘ h₁) (x ⊕⟨ 𝓐 ⟩ y)                       ≡⟨ ap h₂ (i₁ x y) ⟩
         h₂  ((h₁ x) ⊕⟨ 𝓑 ⟩ (h₁ y))             ≡⟨ i₂ (h₁ x) (h₁ y) ⟩
             ((h₂ ∘ h₁) x) ⊕⟨ 𝓒 ⟩ ((h₂ ∘ h₁) y) ∎

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

 open interval-object-exists io public

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

\end{code}

To be continued.

In this submodule, we should develop the basic theory of the interval
object, with the constructions and theorems of the slides.

  * affine (page 11)

\begin{code}

 affine : 𝕀 → 𝕀 → 𝕀 → 𝕀
 affine x y = ∃!-witness (universal-property 𝓘 x y)

 affine-equation-l : (x y : 𝕀) → affine x y u ≡ x
 affine-equation-l x y = pr₁ (∃!-is-witness (universal-property 𝓘 x y))

 affine-equation-r : (x y : 𝕀) → affine x y v ≡ y
 affine-equation-r x y = pr₁ (pr₂ (∃!-is-witness (universal-property 𝓘 x y)))

 affine-is-homomorphism : (x y : 𝕀) (a b : 𝕀)
                        → affine x y (a ⊕ b) ≡ affine x y a ⊕ affine x y b
 affine-is-homomorphism x y = pr₂ (pr₂ (∃!-is-witness (universal-property 𝓘 x y)))

 affine-uniqueness : (f : 𝕀 → 𝕀) (a b : 𝕀)
                   → f u ≡ a
                   → f v ≡ b
                   → is-homomorphism 𝓘 𝓘 f
                   → affine a b ≡ f
 affine-uniqueness f a b l r i
  = ap pr₁ (∃!-uniqueness' (universal-property 𝓘 a b) (f , l , r , i))

 affine-uniqueness· : (f : 𝕀 → 𝕀) (a b : 𝕀)
                   → f u ≡ a
                   → f v ≡ b
                   → is-homomorphism 𝓘 𝓘 f
                   → affine a b ∼ f
 affine-uniqueness· f a b l r i x = ap (λ - → - x) (affine-uniqueness f a b l r i)

 affine-uv-involutive : affine u v ∼ id
 affine-uv-involutive = affine-uniqueness· id u v refl refl (id-is-homomorphism 𝓘)

 affine-single-point : (a : 𝕀) (x : 𝕀) → affine a a x ≡ a
 affine-single-point a = affine-uniqueness· (λ _ → a) a a refl refl (λ _ _ → ⊕-idem a ⁻¹)

\end{code}

  * M (given in the iteration axiom)
    (By the way, we should prove that M is unique.)

  * Equational logic of M in page 16.

  * A homomorphism of _⊕_ is automatically an M homomorphism (page 17)

\begin{code}

 _+ℕ_ : ℕ → ℕ → ℕ
 x +ℕ zero = x
 x +ℕ succ y = succ (x +ℕ y)

 M : (ℕ → 𝕀) → 𝕀
 M = pr₁ ia
 
 M-prop₁ : (a : ℕ → 𝕀) → M a ≡ a 0 ⊕ (M (a ∘ succ))
 M-prop₁ = pr₁ (pr₂ ia)

 M-prop₂ : (a x : ℕ → 𝕀) → ((i : ℕ) → a i ≡ x i ⊕ a (succ i)) → a 0 ≡ M x
 M-prop₂ = pr₂ (pr₂ ia)
 
 M-idem : ∀ (x : 𝕀) → M (λ _ → x) ≡ x
 M-idem x = M-prop₂ (λ _ → x) (λ _ → x) (λ _ → ⊕-idem x ⁻¹) ⁻¹

 -- Apologies for these awkward helper functions...
 δ₁ : (i : ℕ) → 0 +ℕ i ≡ i
 δ₁ zero = refl
 δ₁ (succ i) = ap succ (δ₁ i)
 δ₂ : (z' : ℕ → 𝕀) (i : ℕ) → (M (λ n → z' (succ n +ℕ i))) ≡ (M (λ n → z' (succ (n +ℕ i))))
 δ₂ z' zero = refl
 δ₂ z' (succ i) = δ₂ (z' ∘ succ) i

 M-symm : (x : ℕ → ℕ → 𝕀) → M (λ i → (M (x i))) ≡ M (λ i → M (λ j → x j i))
 M-symm x = {!!}
 
 M-hom : (x y : ℕ → 𝕀) → (M x ⊕ M y) ≡ M (λ i → x i ⊕ y i)
 M-hom x y = M-prop₂ M' (λ i → x i ⊕ y i) γ where
   M' : ℕ → 𝕀
   M' i = M (λ n → x (n +ℕ i)) ⊕ M (λ n → y (n +ℕ i))
   γ : (i : ℕ) → M' i ≡ ((x i ⊕ y i) ⊕ M' (succ i))
   γ i = M (λ n → x (n +ℕ i)) ⊕ M (λ n → y (n +ℕ i))
             ≡⟨ ap (_⊕ M (λ n → y (n +ℕ i)))
                  (M-prop₁ (λ n → x (n +ℕ i))) ⟩
         (x (0 +ℕ i) ⊕ M (λ n → x (succ n +ℕ i))) ⊕ M (λ n → y (n +ℕ i))
             ≡⟨ ap ((x (0 +ℕ i) ⊕ M (λ n → x (succ n +ℕ i))) ⊕_)
                  (M-prop₁ (λ n → y (n +ℕ i))) ⟩
         (x (0 +ℕ i) ⊕ M (λ n → x (succ n +ℕ i))) ⊕ (y (0 +ℕ i) ⊕ M (λ n → y (succ n +ℕ i)))
             ≡⟨ ⊕-tran
                  (x (0 +ℕ i)) (M (λ n → x (succ n +ℕ i)))
                  (y (0 +ℕ i)) (M (λ n → y (succ n +ℕ i))) ⟩
         ((x (0 +ℕ i) ⊕ y (0 +ℕ i)) ⊕ (M (λ n → x (succ n +ℕ i)) ⊕ M (λ n → y (succ n +ℕ i))))
             ≡⟨ ap (λ - → (x - ⊕ y -)
                        ⊕ (M (λ n → x (succ n +ℕ i)) ⊕ M (λ n → y (succ n +ℕ i))))
                   (δ₁ i) ⟩
         ((x i ⊕ y i) ⊕ (M (λ n → x (succ n +ℕ i)) ⊕ M (λ n → y (succ n +ℕ i))))
             ≡⟨ ap (λ - → (x i ⊕ y i) ⊕ (- ⊕ M (λ n → y (succ n +ℕ i))))
                   (δ₂ x i) ⟩
         ((x i ⊕ y i) ⊕ (M (λ n → x (succ (n +ℕ i))) ⊕ M (λ n → y (succ n +ℕ i))))
             ≡⟨ ap (λ - → (x i ⊕ y i) ⊕ (M (λ n → x (succ (n +ℕ i))) ⊕ -))
                   (δ₂ y i) ⟩
         ((x i ⊕ y i) ⊕ M' (succ i)) ∎

 midpoints-homs-are-M-homs : (h : 𝕀 → 𝕀) → is-homomorphism 𝓘 𝓘 h
           → (z : ℕ → 𝕀) → h (M z) ≡ M (λ n → h (z n))
 midpoints-homs-are-M-homs h hom z = M-prop₂ M' (λ n → h (z n)) γ where
   M' : ℕ → 𝕀
   M' i = h (M (λ n → z (n +ℕ i)))
   γ : (i : ℕ) → M' i ≡ (h (z i) ⊕ M' (succ i))
   γ i = h (M (λ n → z (n +ℕ i)))
            ≡⟨ ap h (M-prop₁ (λ n → z (n +ℕ i))) ⟩
         h (z (0 +ℕ i) ⊕ M (λ n → z (succ n +ℕ i)))
            ≡⟨ hom (z (0 +ℕ i)) (M (λ n → z (succ n +ℕ i))) ⟩
         h (z (0 +ℕ i)) ⊕ h (M (λ n → z (succ n +ℕ i)))
            ≡⟨ ap (λ - → h (z -) ⊕ h (M (λ n → z (succ n +ℕ i)))) (δ₁ i) ⟩
         h (z i) ⊕ h (M (λ n → z (succ n +ℕ i)))
            ≡⟨ ap (λ - → h (z i) ⊕ h -) (δ₂ z i) ⟩ 
         h (z i) ⊕ M' (succ i)
            ∎
            
 affine-M-hom : (x y : 𝕀) (z : ℕ → 𝕀) → affine x y (M z) ≡ M (λ n → affine x y (z n))
 affine-M-hom x y z = midpoints-homs-are-M-homs (affine x y) (affine-is-homomorphism x y) z

\end{code}

  * Adopt conventfaion u = -1 and v = 1 for the following.

  * Definability of 1 - x and xy (multiplication) (page 19 uses the
    convention u = 0 and v = 1 so we should use page 24).

\begin{code}

 ₋₁ ₀₀ ₊₁ : 𝕀
 ₋₁ = u
 ₊₁ = v
 ₀₀  = ₋₁ ⊕ ₊₁

 −_ : 𝕀 → 𝕀
 − x = affine ₊₁ ₋₁ x

 ₋₁-inverse : (− ₋₁) ≡ ₊₁
 ₋₁-inverse = affine-equation-l ₊₁ ₋₁

 ₊₁-inverse : (− ₊₁) ≡ ₋₁
 ₊₁-inverse = affine-equation-r ₊₁ ₋₁

 ₋₁-neg-inv : (− (− ₋₁)) ≡ ₋₁
 ₋₁-neg-inv = − (− ₋₁) ≡⟨ ap −_ ₋₁-inverse ⟩
                 − ₊₁  ≡⟨ ₊₁-inverse ⟩
                   ₋₁  ∎

 ₊₁-neg-inv : (− (− ₊₁)) ≡ ₊₁
 ₊₁-neg-inv = − (− ₊₁) ≡⟨ ap −_ ₊₁-inverse ⟩
                 − ₋₁  ≡⟨ ₋₁-inverse ⟩
                   ₊₁  ∎

 −-is-homomorphism : (a b : 𝕀) → (− (a ⊕ b)) ≡ (− a) ⊕ (− b)
 −-is-homomorphism a b = affine-is-homomorphism ₊₁ ₋₁ a b

 negation-involutive : (x : 𝕀) → − (− x) ≡ x
 negation-involutive x =       − (− x) ≡⟨ negation-involutive' x ⁻¹ ⟩
                       affine ₋₁ ₊₁ x  ≡⟨ affine-uv-involutive x ⟩ 
                                    x  ∎
  where
   −−-is-homomorphism : is-homomorphism 𝓘 𝓘 (λ x → − (− x))
   −−-is-homomorphism = homomorphism-composition 𝓘 𝓘 𝓘 −_ −_
                        −-is-homomorphism −-is-homomorphism
   negation-involutive' : (x : 𝕀) → affine ₋₁ ₊₁ x ≡ − (− x)
   negation-involutive' = affine-uniqueness· (λ x → − (− x))
                          ₋₁ ₊₁ ₋₁-neg-inv ₊₁-neg-inv
                          −−-is-homomorphism
 
 mul : 𝕀 → 𝕀 → 𝕀
 mul x y = affine (− x) x y

 mul-gives-negation-r : (y : 𝕀) → mul ₋₁ y ≡ − y
 mul-gives-negation-r y = ap (λ - → affine - ₋₁ y) ₋₁-inverse

 mul-gives-negation-l : (y : 𝕀) → mul y ₋₁ ≡ − y
 mul-gives-negation-l y = affine-equation-l (− y) y

 mul-gives-id-r : (y : 𝕀) → mul ₊₁ y ≡ y
 mul-gives-id-r y = ap (λ - → affine - ₊₁ y) ₊₁-inverse ∙ affine-uv-involutive y

 mul-gives-id-l : (y : 𝕀) → mul y ₊₁ ≡ y
 mul-gives-id-l y = affine-equation-r (− y) y

 mul-hom-r : (a : 𝕀) → is-homomorphism 𝓘 𝓘 (mul a)
 mul-hom-r a x y = affine-is-homomorphism (− a) a x y

 mul-prop₄ : (x y : 𝕀) → mul x (− y) ≡ mul (− x) y
 mul-prop₄ x y = affine-uniqueness· (λ - → mul x (− -)) (− (− x)) (− x) l r i y ⁻¹
  where
   l =  mul x (− u) ≡⟨ ap (mul x) ₋₁-inverse ⟩
        mul x    v  ≡⟨ mul-gives-id-l x ⟩
            x       ≡⟨ negation-involutive x ⁻¹ ⟩
       − (− x)      ∎
   r =  mul x (− v) ≡⟨ ap (mul x) ₊₁-inverse ⟩
        mul x    u  ≡⟨ mul-gives-negation-l x ⟩
          − x       ∎
   i : (a b : ⟨ 𝓘 ⟩) → mul x (− (a ⊕ b)) ≡ mul x (− a) ⊕ mul x (− b)
   i a b = mul x  (− (a ⊕ b))         ≡⟨ ap (mul x) (−-is-homomorphism a b) ⟩
           mul x ((− a) ⊕ (− b))      ≡⟨ affine-is-homomorphism (− x) x (− a) (− b) ⟩
           mul x (− a)  ⊕ mul x (− b) ∎

 mul-prop₃ : (x y : 𝕀) → mul x y ≡ (− mul x (− y))
 mul-prop₃ x y = affine-uniqueness· (λ - → − mul x (− -) ) (− x) x l r i y
  where
   l = − mul x (− u) ≡⟨ ap (λ - → − mul x -) ₋₁-inverse ⟩
       − mul x    v  ≡⟨ ap −_ (mul-gives-id-l x) ⟩
       −     x       ∎
   r = − mul x (− v) ≡⟨ ap (λ - → − mul x -) ₊₁-inverse ⟩
       − mul x    u  ≡⟨ ap −_ (mul-gives-negation-l x) ⟩
       −  (− x)      ≡⟨ negation-involutive x ⟩
             x       ∎
   i : is-homomorphism 𝓘 𝓘 (λ - → − mul x (− -))
   i a b = − mul x  (− (a ⊕ b))
                ≡⟨ ap (λ - → − mul x -) (−-is-homomorphism a b) ⟩
           − mul x ((− a) ⊕ (− b))
                ≡⟨ ap −_ (affine-is-homomorphism (− x) x (− a) (− b)) ⟩
           − (mul x (− a) ⊕ mul x (− b))
                ≡⟨ affine-is-homomorphism ₊₁ ₋₁ (mul x (− a)) (mul x (− b)) ⟩
          (− mul x (− a)) ⊕ (− mul x (− b))
                ∎
          
 mul-commutative : (x y : 𝕀) → mul x y ≡ mul y x
 mul-commutative x = γ
  where
   j : (a b : 𝕀) → is-homomorphism 𝓘 𝓘 (λ x → mul a x ⊕ mul b x)
   j a b x y
       = ap (_⊕ mul b (x ⊕ y)) (affine-is-homomorphism (− a) a x y)
       ∙ ap ((mul a x ⊕ mul a y) ⊕_) (affine-is-homomorphism (− b) b x y)
       ∙ ⊕-tran (mul a x) (mul a y) (affine (− b) b x) (affine (− b) b y)
   i : is-homomorphism 𝓘 𝓘 (λ y → mul y x)
   i y z = p
    where
     p : mul (y ⊕ z) x ≡ (mul y x ⊕ mul z x)
     p = affine-uniqueness· (λ x → mul y x ⊕ mul z x) (− (y ⊕ z)) (y ⊕ z)
         (ap (_⊕ mul z u) (mul-gives-negation-l y)
         ∙ ap ((− y) ⊕_) (mul-gives-negation-l z)
         ∙ affine-is-homomorphism ₊₁ ₋₁ y z ⁻¹)
         (ap (_⊕ mul z v) (mul-gives-id-l y)
         ∙ ap (y ⊕_) (mul-gives-id-l z))
         (j y z) x
   γ : mul x ∼ (λ y → mul y x)
   γ = affine-uniqueness· (λ y → mul y x)
       (− x) x (mul-gives-negation-r x) (mul-gives-id-r x)
       i

 mul-assoc : (x y z : 𝕀) → mul x (mul y z) ≡ mul (mul x y) z
 mul-assoc x y z = γ z ⁻¹
  where
   l =      mul x (mul y ₋₁) ≡⟨ ap (mul x) (mul-gives-negation-l y) ⟩
            mul x   (− y)    ≡⟨ negation-involutive (mul x (− y)) ⁻¹ ⟩
       − (− mul x   (− y))   ≡⟨ ap −_ (mul-prop₃ x y ⁻¹) ⟩
          − mul x      y     ∎
   r = mul x (mul y ₊₁) ≡⟨ ap (mul x) (mul-gives-id-l y) ⟩
       mul x      y     ∎
   i : is-homomorphism 𝓘 𝓘 (λ z → mul x (mul y z))
   i a b = mul x (mul y (a ⊕ b))
                ≡⟨ ap (mul x) (mul-hom-r y a b) ⟩
           mul x (mul y a ⊕ mul y b)
                ≡⟨ affine-is-homomorphism (− x) x (mul y a) (mul y b) ⟩
           mul x (mul y a) ⊕ mul x (mul y b)
                ∎
   γ : (λ z → mul (mul x y) z) ∼ (λ z → mul x (mul y z)) 
   γ = affine-uniqueness· (λ z → mul x (mul y z)) (− mul x y) (mul x y) l r i

\end{code}

  * Medial power series (page 20 and 21).

  * Page 24: not only the definitions, but the fact that we get
    commutativity and associativity.

  * Page 25.

  * Page 35.

  * Page 42.

\begin{code}
