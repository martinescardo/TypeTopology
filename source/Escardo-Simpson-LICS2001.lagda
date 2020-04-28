Todd Waugh Ambridge, 27th April 2020.

We formalize, in univalent mathematics in Agda, some definitions in

M.H. Escardo and A. Simpson. A universal characterization of the
closed Euclidean interval (extended abstract). Proceedings of the 16th
Annual IEEE Symposium on Logic in Computer Science,
pp.115--125. Boston, Massachusetts, June 16-19, 2001.

https://www.cs.bham.ac.uk/~mhe/papers/lics2001-revised.pdf
https://www.cs.bham.ac.uk/~mhe/papers/interval.pdf
https://www.cs.bham.ac.uk/~mhe/.talks/map2011/

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UF-FunExt
open import SpartanMLTT renaming (* to ⋆)
open import NaturalsAddition renaming (_+_ to _+ℕ_)
open import UF-Subsingletons

module Escardo-Simpson-LICS2001 (fe : FunExt) where

\end{code}

First we give basic properties on binary functions,
as well as a specific property about equality of streams under some arithmetic

\begin{code}

associative commutative idempotent transpositional : {X : 𝓤 ̇} → (X → X → X) → 𝓤 ̇
associative     _∙_ = ∀ a b c   → a ∙ (b ∙ c)       ≡ (a ∙ b) ∙ c
commutative     _∙_ = ∀ a b     → a ∙ b             ≡ b ∙ a
idempotent      _∙_ = ∀ a       → a ∙ a             ≡ a
transpositional _∙_ = ∀ a b c d → (a ∙ b) ∙ (c ∙ d) ≡ (a ∙ c) ∙ (b ∙ d)


seq-add-push : {A : 𝓤 ̇ } (α : ℕ → A) (i : ℕ)
             → (λ (n : ℕ) → α (succ n +ℕ i)) ≡ (λ (n : ℕ) → α (succ (n +ℕ i)))
seq-add-push α 0 = refl
seq-add-push α (succ i) = seq-add-push (α ∘ succ) i

\end{code}

The initial structure we define is a Midpoint-algebra

\begin{code}

mid-point-algebra-axioms : (A : 𝓤 ̇ ) → (A → A → A) → 𝓤 ̇
mid-point-algebra-axioms A _⊕_ = is-set A
                               × idempotent _⊕_ × commutative _⊕_ × transpositional _⊕_

Midpoint-algebra : (𝓤 : Universe) → 𝓤 ⁺ ̇
Midpoint-algebra 𝓤 = Σ A ꞉ 𝓤 ̇ , Σ _⊕_ ꞉ (A → A → A) , (mid-point-algebra-axioms A _⊕_)

\end{code}

 We introduce two more properties on binary functions: cancellation and iteration
 For a particular type, the iterator is unique

\begin{code}

cancellative : {X : 𝓤 ̇} → (X → X → X) → 𝓤 ̇
cancellative  _∙_ = ∀ a b c → a ∙ c ≡ b ∙ c → a ≡ b

iterative : {A : 𝓤 ̇ } → (A → A → A) → 𝓤 ̇
iterative {𝓤} {A} _⊕_ = Σ M ꞉ ((ℕ → A) → A) , ((a : ℕ → A) → M a ≡ a 0 ⊕ M (a ∘ succ))
                                            × ((a x : ℕ → A)
                                               → ((i : ℕ) → a i ≡ x i ⊕ a (succ i))
                                               → a 0 ≡ M x)

iterative-uniqueness· : {A : 𝓤 ̇} → (_⊕_ : A → A → A)
                      → (F M : iterative _⊕_)
                      → pr₁ F ∼ pr₁ M
iterative-uniqueness· {𝓤} {𝕀} _⊕_ (F , p₁ , q₁) (M , p₂ , q₂) x = q₂ M' x γ
  where M' : ℕ → 𝕀
        M' i = F (λ n → x (n +ℕ i))
        γ : (i : ℕ) → M' i ≡ (x i ⊕ M' (succ i))
        γ i = p₁ (λ n → x (n +ℕ i))
            ∙ ap (λ - → x - ⊕ F (λ n → x (succ n +ℕ i))) (zero-left-neutral i)
            ∙ ap (λ - → x i ⊕ F -) (seq-add-push x i)

iterative-uniqueness : {A : 𝓤 ̇} → (_⊕_ : A → A → A)
                     → (F M : iterative _⊕_)
                     → pr₁ F ≡ pr₁ M
iterative-uniqueness {𝓤} _⊕_ F M = dfunext (fe 𝓤 𝓤) (iterative-uniqueness· _⊕_ F M)

\end{code}

 A Convex-body is a cancellative, iterative Midpoint-algebra

\begin{code}

Convex-body : (𝓤 : Universe) → 𝓤 ⁺ ̇
Convex-body 𝓤 = Σ A ꞉ 𝓤 ̇ , Σ _⊕_ ꞉ (A → A → A) , (mid-point-algebra-axioms A _⊕_)
                                                 × (cancellative _⊕_)
                                                 × (iterative _⊕_)
                                                 
⟨_⟩ : Convex-body 𝓤 → 𝓤 ̇
⟨ A , _ ⟩ = A

mid-point-operation : (𝓐 : Convex-body 𝓤) → ⟨ 𝓐 ⟩ → ⟨ 𝓐 ⟩ → ⟨ 𝓐 ⟩
mid-point-operation (A , _⊕_ , _) = _⊕_

syntax mid-point-operation 𝓐 x y = x ⊕⟨ 𝓐 ⟩ y

\end{code}

 Definition of a midpoint-homomorphism
 The identity function is a midpoint-hom
 The unary functions given by a constant midpoint are midpoint-homs
 The composition of two midpoint-homs is a midpoint-hom

\begin{code}

is-⊕-homomorphism : (𝓐 : Convex-body 𝓤) (𝓑 : Convex-body 𝓥)
                → (⟨ 𝓐 ⟩ → ⟨ 𝓑 ⟩) → 𝓤 ⊔ 𝓥 ̇
is-⊕-homomorphism 𝓐 𝓑 h = (x y : ⟨ 𝓐 ⟩) → h (x ⊕⟨ 𝓐 ⟩ y) ≡ h x ⊕⟨ 𝓑 ⟩ h y

id-is-⊕-homomorphism : (𝓐 : Convex-body 𝓤) → is-⊕-homomorphism 𝓐 𝓐 id
id-is-⊕-homomorphism 𝓐 x y = refl

⊕-is-⊕-homomorphism-r : (𝓐 : Convex-body 𝓤)
                    → (a : ⟨ 𝓐 ⟩) → is-⊕-homomorphism 𝓐 𝓐 (λ y → a ⊕⟨ 𝓐 ⟩ y)
⊕-is-⊕-homomorphism-r (𝓐 , _⊕_ , (_ , ⊕-idem , _ , ⊕-tran) , _) a x y
 =    a    ⊕ (x ⊕ y) ≡⟨ ap (_⊕ (x ⊕ y)) (⊕-idem a ⁻¹) ⟩
   (a ⊕ a) ⊕ (x ⊕ y) ≡⟨ ⊕-tran a a x y ⟩
   (a ⊕ x) ⊕ (a ⊕ y) ∎

⊕-is-⊕-homomorphism-l : (𝓐 : Convex-body 𝓤)
                    → (b : ⟨ 𝓐 ⟩) → is-⊕-homomorphism 𝓐 𝓐 (λ x → x ⊕⟨ 𝓐 ⟩ b)
⊕-is-⊕-homomorphism-l (𝓐 , _⊕_ , (_ , ⊕-idem , _ , ⊕-tran) , _) b x y
 = (x ⊕ y) ⊕    b    ≡⟨ ap ((x ⊕ y) ⊕_) (⊕-idem b ⁻¹) ⟩
   (x ⊕ y) ⊕ (b ⊕ b) ≡⟨ ⊕-tran x y b b ⟩
   (x ⊕ b) ⊕ (y ⊕ b) ∎

⊕-hom-composition : (𝓐 : Convex-body 𝓤) (𝓑 : Convex-body 𝓥) (𝓒 : Convex-body 𝓦)
                          → (h₁ : ⟨ 𝓐 ⟩ → ⟨ 𝓑 ⟩) → (h₂ : ⟨ 𝓑 ⟩ → ⟨ 𝓒 ⟩)
                          → is-⊕-homomorphism 𝓐 𝓑 h₁ → is-⊕-homomorphism 𝓑 𝓒 h₂
                          → is-⊕-homomorphism 𝓐 𝓒 (h₂ ∘ h₁)
⊕-hom-composition {𝓤} {𝓥} {𝓦} 𝓐 𝓑 𝓒 h₁ h₂ i₁ i₂ x y
 = (h₂ ∘ h₁) (x ⊕⟨ 𝓐 ⟩ y)                       ≡⟨ ap h₂ (i₁ x y) ⟩
         h₂  ((h₁ x) ⊕⟨ 𝓑 ⟩ (h₁ y))             ≡⟨ i₂ (h₁ x) (h₁ y) ⟩
             ((h₂ ∘ h₁) x) ⊕⟨ 𝓒 ⟩ ((h₂ ∘ h₁) y) ∎

\end{code}

 The key structure of the axiomatisation: an interval object
 An interval object is defined by a Convex-body 𝓘 and two points u,v : ⟨𝓘⟩
 For every two points a,b : ⟨𝓐⟩ of a Convex-body 𝓐,
   there exists a unique h : ⟨𝓘⟩ → ⟨𝓐⟩ such that:
    * h u ≡ a
    * h v ≡ b
    * ∀ x,y : ⟨𝓘⟩. h (x ⊕⟨ 𝓘 ⟩ y) ≡ h x ⊕⟨ 𝓐 ⟩ h y)

\begin{code}

is-interval-object : (𝓘 : Convex-body 𝓤) → ⟨ 𝓘 ⟩ → ⟨ 𝓘 ⟩ → 𝓤ω
is-interval-object {𝓤} 𝓘 u v =
     {𝓥 : Universe} (𝓐 : Convex-body 𝓥) (a b : ⟨ 𝓐 ⟩) -- h = affine a b
   → ∃! h ꞉ (⟨ 𝓘 ⟩ → ⟨ 𝓐 ⟩) , (h u ≡ a)
                            × (h v ≡ b)
                            × ((x y : ⟨ 𝓘 ⟩) → h (x ⊕⟨ 𝓘 ⟩ y) ≡ h x ⊕⟨ 𝓐 ⟩ h y)

\end{code}

 The type of an interval object axiomatisation as a record

\begin{code}

record Interval-object (𝓤 : Universe) : 𝓤ω where
 field
  𝕀 : 𝓤 ̇
  _⊕_ : 𝕀 → 𝕀 → 𝕀
  u v : 𝕀
  mpaa : mid-point-algebra-axioms 𝕀 _⊕_
  ca : cancellative _⊕_
  ia : iterative _⊕_
  universal-property : is-interval-object (𝕀 , _⊕_ , mpaa , ca , ia) u v 

\end{code}

 The type of a doubling function axiomatisation

\begin{code}

has-double : (𝓥 : Universe) (io : Interval-object 𝓥) → 𝓥 ̇
has-double 𝓥 io = Σ double ꞉ (𝕀 → 𝕀)
                 , ((x : 𝕀) → double (x ⊕ (u ⊕ v)) ≡ x)
                 × ((x : 𝕀) → double (u ⊕ (u ⊕ x)) ≡ u)
                 × ((x : 𝕀) → double (v ⊕ (v ⊕ x)) ≡ v)
 where
   𝕀 = Interval-object.𝕀 io
   u = Interval-object.u io
   v = Interval-object.v io
   _⊕_ = Interval-object._⊕_ io

\end{code}

 We now prove things within a universe
 with an Interval-object and a doubling function

\begin{code}

module basic-interval-object-development {𝓤 : Universe}
 (io : Interval-object 𝓤) (hd : has-double 𝓤 io) where

\end{code}

 First we unpack all of the axioms from the Interval-object
 affine : 𝕀 → 𝕀 → 𝕀 → 𝕀 is given by the unique map h : 𝕀 → 𝕀

\begin{code}


 open Interval-object io public

 ⊕-idem : idempotent _⊕_
 ⊕-idem = pr₁ (pr₂ mpaa)

 ⊕-comm : commutative _⊕_
 ⊕-comm = pr₁ (pr₂ (pr₂ mpaa))

 ⊕-tran : transpositional _⊕_
 ⊕-tran = pr₂ (pr₂ (pr₂ mpaa))

 ⊕-canc : cancellative _⊕_
 ⊕-canc = Interval-object.ca io

 𝓘 : Convex-body 𝓤
 𝓘 = 𝕀 , _⊕_ , mpaa , ⊕-canc , ia

 affine : 𝕀 → 𝕀 → 𝕀 → 𝕀
 affine x y = ∃!-witness (universal-property 𝓘 x y)

 affine-equation-l : (x y : 𝕀) → affine x y u ≡ x
 affine-equation-l x y = pr₁ (∃!-is-witness (universal-property 𝓘 x y))

 affine-equation-r : (x y : 𝕀) → affine x y v ≡ y
 affine-equation-r x y = pr₁ (pr₂ (∃!-is-witness (universal-property 𝓘 x y)))

 affine-is-⊕-homomorphism : (x y : 𝕀) (a b : 𝕀)
                        → affine x y (a ⊕ b) ≡ affine x y a ⊕ affine x y b
 affine-is-⊕-homomorphism x y = pr₂ (pr₂ (∃!-is-witness (universal-property 𝓘 x y)))

 affine-uniqueness : (f : 𝕀 → 𝕀) (a b : 𝕀)
                   → f u ≡ a
                   → f v ≡ b
                   → is-⊕-homomorphism 𝓘 𝓘 f
                   → affine a b ≡ f
 affine-uniqueness f a b l r i
  = ap pr₁ (∃!-uniqueness' (universal-property 𝓘 a b) (f , l , r , i))

 affine-uniqueness· : (f : 𝕀 → 𝕀) (a b : 𝕀)
                   → f u ≡ a
                   → f v ≡ b
                   → is-⊕-homomorphism 𝓘 𝓘 f
                   → affine a b ∼ f
 affine-uniqueness· f a b l r i x = ap (λ - → - x) (affine-uniqueness f a b l r i)

\end{code}

 Many of the following proofs follow from the uniqueness of affine
 For example, affine u v is point-wise equivalent to the identity function

\begin{code}


 affine-uv-involutive : affine u v ∼ id
 affine-uv-involutive = affine-uniqueness· id u v refl refl (id-is-⊕-homomorphism 𝓘)

 affine-constant : (a : 𝕀) (x : 𝕀) → affine a a x ≡ a
 affine-constant a = affine-uniqueness· (λ _ → a) a a refl refl (λ _ _ → ⊕-idem a ⁻¹)

\end{code}

 The iterator is called M
 We prove that it is idempotent, symmetric and is a midpoint-hom

\begin{code}

 M : (ℕ → 𝕀) → 𝕀
 M = pr₁ ia
 
 M-prop₁ : (a : ℕ → 𝕀) → M a ≡ a 0 ⊕ (M (a ∘ succ))
 M-prop₁ = pr₁ (pr₂ ia)

 M-prop₂ : (a x : ℕ → 𝕀) → ((i : ℕ) → a i ≡ x i ⊕ a (succ i)) → a 0 ≡ M x
 M-prop₂ = pr₂ (pr₂ ia)

 M-idem : (x : 𝕀) → M (λ _ → x) ≡ x
 M-idem x = M-prop₂ (λ _ → x) (λ _ → x) (λ _ → ⊕-idem x ⁻¹) ⁻¹

{- 
 M-prop₁' : (a : ℕ → ℕ → 𝕀)
           → M (λ n → M (λ m → a n m))
           ≡ M (λ m → a 0 m) ⊕ M (λ n → M (λ m → a (succ n) m))
 M-prop₁' a = M-prop₁ (λ n → M (a n))

 M-prop₂' : (a x : ℕ → ℕ → 𝕀) → ((i : ℕ) → a 0 i ≡ x 0 i ⊕ a 0 (succ i)) → a 0 0 ≡ M (x 0)
 M-prop₂' a x q = M-prop₂ (a 0) (x 0) q

 M-prop₂'' : (a x : ℕ → ℕ → 𝕀) → ((i : ℕ) → a i 0 ≡ x i 0 ⊕ a (succ i) 0)
           → a 0 0 ≡ M (λ n → x n 0)
 M-prop₂'' a x q = M-prop₂ (λ n → a n 0) (λ n → x n 0) q

 M-symm : (x : ℕ → ℕ → 𝕀) → M (λ i → (M (λ j → x i j))) ≡ M (λ i → M (λ j → x j i))
 M-symm x = M-prop₂' M' Q γ where
   M' : ℕ → ℕ → 𝕀
   M' k l = M (λ i → M (λ j → x (i +ℕ l) (j +ℕ k))) 
   Q : ℕ → ℕ → 𝕀
   Q k i = M (λ j → x (j +ℕ k) i)
   extragoal : ∀ k → M (λ i → M (λ j → x (succ i +ℕ k) j))
             ≡ M (λ i → M (λ j → x (succ (i +ℕ k)) j))
   extragoal = {!!}
   γ : (k : ℕ) → M' 0 k ≡ (Q 0 k ⊕ M' 0 (succ k))
   γ k = M-prop₁' (λ i j → x (i +ℕ k) (j +ℕ 0))
       ∙ ap (λ - → M (λ j → x - j) ⊕ M (λ i → M (λ j → x (succ i +ℕ k) j))) (zero-left-neutral k)
       ∙ ap (M (λ j → x k j) ⊕_) (extragoal k)
       ∙ ap (_⊕ M' 0 (succ k))
           (M-prop₁ (λ j → x k j)
         ∙ {!!}) -}
 
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
                   (zero-left-neutral i) ⟩
         ((x i ⊕ y i) ⊕ (M (λ n → x (succ n +ℕ i)) ⊕ M (λ n → y (succ n +ℕ i))))
             ≡⟨ ap (λ - → (x i ⊕ y i) ⊕ (M - ⊕ M (λ n → y (succ n +ℕ i))))
                   (seq-add-push x i) ⟩
         ((x i ⊕ y i) ⊕ (M (λ n → x (succ (n +ℕ i))) ⊕ M (λ n → y (succ n +ℕ i))))
             ≡⟨ ap (λ - → (x i ⊕ y i) ⊕ (M (λ n → x (succ (n +ℕ i))) ⊕ M -))
                   (seq-add-push y i) ⟩
         (x i ⊕ y i) ⊕ M' (succ i) ∎

\end{code}

 Any midpoint-hom is automatically an M-hom
 Thus, M is an M-hom

\begin{code}

 ⊕-homs-are-M-homs : (h : 𝕀 → 𝕀) → is-⊕-homomorphism 𝓘 𝓘 h
           → (z : ℕ → 𝕀) → h (M z) ≡ M (λ n → h (z n))
 ⊕-homs-are-M-homs h hom z = M-prop₂ M' (λ n → h (z n)) γ where
   M' : ℕ → 𝕀
   M' i = h (M (λ n → z (n +ℕ i)))
   γ : (i : ℕ) → M' i ≡ (h (z i) ⊕ M' (succ i))
   γ i = h (M (λ n → z (n +ℕ i)))
            ≡⟨ ap h (M-prop₁ (λ n → z (n +ℕ i))) ⟩
         h (z (0 +ℕ i) ⊕ M (λ n → z (succ n +ℕ i)))
            ≡⟨ hom (z (0 +ℕ i)) (M (λ n → z (succ n +ℕ i))) ⟩
         h (z (0 +ℕ i)) ⊕ h (M (λ n → z (succ n +ℕ i)))
            ≡⟨ ap (λ - → h (z -) ⊕ h (M (λ n → z (succ n +ℕ i)))) (zero-left-neutral i) ⟩
         h (z i) ⊕ h (M (λ n → z (succ n +ℕ i)))
            ≡⟨ ap (λ - → h (z i) ⊕ h (M -)) (seq-add-push z i) ⟩ 
         h (z i) ⊕ M' (succ i)
            ∎

 affine-M-hom : (x y : 𝕀) (z : ℕ → 𝕀) → affine x y (M z) ≡ M (λ n → affine x y (z n))
 affine-M-hom x y z = ⊕-homs-are-M-homs (affine x y) (affine-is-⊕-homomorphism x y) z

\end{code}

 We adopt the convention u = −1 and v = +1 for the following

\begin{code}

 −1 O +1 : 𝕀
 −1 = u
 +1 = v
 O  = −1 ⊕ +1

\end{code}

 The negation function and related properties,
 culminating in proving negation is involutive

\begin{code}

 −_ : 𝕀 → 𝕀
 −_ = affine +1 −1

 infixl 100 −_

 −-is-⊕-homomorphism : (a b : 𝕀) → − (a ⊕ b) ≡ − a ⊕ − b
 −-is-⊕-homomorphism = affine-is-⊕-homomorphism +1 −1

 −1-inverse : − −1 ≡ +1
 −1-inverse = affine-equation-l +1 −1

 +1-inverse : − +1 ≡ −1
 +1-inverse = affine-equation-r +1 −1

 O-inverse : − O ≡ O
 O-inverse = −-is-⊕-homomorphism −1 +1
            ∙ ap (_⊕ − +1) −1-inverse
            ∙ ap (+1 ⊕_)   +1-inverse
            ∙ ⊕-comm +1 −1

 −1-neg-inv : − − −1 ≡ −1
 −1-neg-inv = − − −1 ≡⟨ ap −_ −1-inverse ⟩
                − +1 ≡⟨ +1-inverse ⟩
                  −1 ∎

 +1-neg-inv : − − +1 ≡ +1
 +1-neg-inv = − − +1 ≡⟨ ap −_ +1-inverse ⟩
                − −1 ≡⟨ −1-inverse ⟩
                  +1 ∎

 −-involutive : (x : 𝕀) → − − x ≡ x
 −-involutive x =         − − x ≡⟨ negation-involutive' x ⁻¹ ⟩
                 affine −1 +1 x ≡⟨ affine-uv-involutive x ⟩ 
                              x  ∎
  where
   −−-is-⊕-homomorphism : is-⊕-homomorphism 𝓘 𝓘 (λ x → − (− x))
   −−-is-⊕-homomorphism = ⊕-hom-composition 𝓘 𝓘 𝓘 −_ −_
                          −-is-⊕-homomorphism −-is-⊕-homomorphism
   negation-involutive' : (x : 𝕀) → affine −1 +1 x ≡ − (− x)
   negation-involutive' = affine-uniqueness· (λ x → − (− x))
                          −1 +1 −1-neg-inv +1-neg-inv
                          −−-is-⊕-homomorphism

\end{code}

 The "midpoint subtraction" function from midpoint and negation
 The midpoint subtraction of any x with itself is O

\begin{code}

 _⊖_ : 𝕀 → 𝕀 → 𝕀
 x ⊖ y = x ⊕ (− y)

 ⊖-zero : (x : 𝕀) → x ⊖ x ≡ O
 ⊖-zero x = ⊖-fact' ⁻¹ ∙ affine-constant O x where
   ⊖-fact' : affine O O x ≡ x ⊖ x
   ⊖-fact' = affine-uniqueness· f O O −1-⊖ +1-⊖ ⊖-hom x where
     −1-⊖ : −1 ⊖ −1 ≡ O
     −1-⊖ = ap (−1 ⊕_) −1-inverse
     +1-⊖ : +1 ⊖ +1 ≡ O
     +1-⊖ = ap (+1 ⊕_) +1-inverse ∙ ⊕-comm +1 −1
     f : 𝕀 → 𝕀
     f x = x ⊖ x
     ⊖-hom : is-⊕-homomorphism 𝓘 𝓘 (λ x → x ⊖ x)
     ⊖-hom x y = ap ((x ⊕ y) ⊕_) (−-is-⊕-homomorphism x y)
               ∙ ⊕-tran x y (− x) (− y)

\end{code}



\begin{code}

 _*_ : 𝕀 → 𝕀 → 𝕀
 x * y = affine (− x) x y
 mul = _*_

 *-gives-negation-l : (x : 𝕀) → x * −1 ≡ − x
 *-gives-negation-l x = affine-equation-l (− x) x

 *-gives-negation-r : (y : 𝕀) → −1 * y ≡ − y
 *-gives-negation-r y = ap (λ - → affine - −1 y) −1-inverse

 *-gives-id-l : (x : 𝕀) → x * +1 ≡ x
 *-gives-id-l x = affine-equation-r (− x) x

 *-gives-id-r : (y : 𝕀) → +1 * y ≡ y
 *-gives-id-r y = ap (λ - → affine - +1 y) +1-inverse ∙ affine-uv-involutive y

 *-is-⊕-homomorphism-l : (a : 𝕀) → is-⊕-homomorphism 𝓘 𝓘 (a *_)
 *-is-⊕-homomorphism-l a x y = affine-is-⊕-homomorphism (− a) a x y

 mul-commutative : commutative _*_
 mul-commutative x y = γ y
  where
   j : (a b : 𝕀) → is-⊕-homomorphism 𝓘 𝓘 (λ x → mul a x ⊕ mul b x)
   j a b x y
       = ap (_⊕ mul b (x ⊕ y)) (*-is-⊕-homomorphism-l a x y)
       ∙ ap ((mul a x ⊕ mul a y) ⊕_) (*-is-⊕-homomorphism-l b x y)
       ∙ ⊕-tran (mul a x) (mul a y) (affine (− b) b x) (affine (− b) b y)
   i : is-⊕-homomorphism 𝓘 𝓘 (λ y → mul y x)
   i y z = p
    where
     p : mul (y ⊕ z) x ≡ (mul y x ⊕ mul z x)
     p = affine-uniqueness· (λ x → mul y x ⊕ mul z x) (− (y ⊕ z)) (y ⊕ z)
         (ap (_⊕ mul z u) (*-gives-negation-l y)
         ∙ ap ((− y) ⊕_) (*-gives-negation-l z)
         ∙ affine-is-⊕-homomorphism +1 −1 y z ⁻¹)
         (ap (_⊕ mul z v) (*-gives-id-l y)
         ∙ ap (y ⊕_) (*-gives-id-l z))
         (j y z) x
   γ : (λ y → mul x y) ∼ (λ y → mul y x)
   γ = affine-uniqueness· (λ y → mul y x)
       (− x) x (*-gives-negation-r x) (*-gives-id-r x)
       i

 *-is-⊕-homomorphism-r : (b : 𝕀) → is-⊕-homomorphism 𝓘 𝓘 (_* b)
 *-is-⊕-homomorphism-r b x y = mul-commutative (x ⊕ y) b
                             ∙ *-is-⊕-homomorphism-l b x y
                             ∙ ap ((b * x) ⊕_) (mul-commutative b y)
                             ∙ ap (_⊕ (y * b)) (mul-commutative b x)

 mul-prop : (x y : 𝕀) → x * y ≡ − (x * − y)
 mul-prop x y = affine-uniqueness· (λ - → − (x * (− -))) (− x) x l r i y
  where
   l = − (x * (− −1)) ≡⟨ ap (λ - → − (x * -)) −1-inverse ⟩
       − (x *    +1 ) ≡⟨ ap −_ (*-gives-id-l x)          ⟩
       −  x           ∎
   r = − (x * (− +1)) ≡⟨ ap (λ - → − (x * -)) +1-inverse ⟩
       − (x *    −1 ) ≡⟨ ap −_ (*-gives-negation-l x)    ⟩
       −  (− x)       ≡⟨ −-involutive x                  ⟩
             x        ∎
   i : is-⊕-homomorphism 𝓘 𝓘 (λ - → − (x * (− -)))
   i a b = −  (x * (− (a ⊕ b)))
                ≡⟨ ap (λ - → − mul x -) (−-is-⊕-homomorphism a b) ⟩
           −  (x * ((− a) ⊕ (− b)))
                ≡⟨ ap −_ (affine-is-⊕-homomorphism (− x) x (− a) (− b)) ⟩
           − ((x * (− a)) ⊕ (x * (− b)))
                ≡⟨ affine-is-⊕-homomorphism +1 −1 (mul x (− a)) (mul x (− b)) ⟩
          (− mul x (− a)) ⊕ (− mul x (− b))
                ∎

 mul-assoc : (x y z : 𝕀) → mul x (mul y z) ≡ mul (mul x y) z
 mul-assoc x y z = γ z ⁻¹
  where
   l =      mul x (mul y −1) ≡⟨ ap (mul x) (*-gives-negation-l y) ⟩
            mul x   (− y)    ≡⟨ −-involutive (mul x (− y)) ⁻¹     ⟩
       − (− mul x   (− y))   ≡⟨ ap −_ (mul-prop x y ⁻¹)           ⟩
          − mul x      y     ∎
   r = mul x (mul y +1) ≡⟨ ap (mul x) (*-gives-id-l y) ⟩
       mul x      y     ∎
   i : is-⊕-homomorphism 𝓘 𝓘 (λ z → mul x (mul y z))
   i a b = mul x (mul y (a ⊕ b))
                ≡⟨ ap (mul x) (*-is-⊕-homomorphism-l y a b) ⟩
           mul x (mul y a ⊕ mul y b)
                ≡⟨ affine-is-⊕-homomorphism (− x) x (mul y a) (mul y b) ⟩
           mul x (mul y a) ⊕ mul x (mul y b)
                ∎
   γ : (λ z → mul (mul x y) z) ∼ (λ z → mul x (mul y z)) 
   γ = affine-uniqueness· (λ z → mul x (mul y z)) (− mul x y) (mul x y) l r i

\end{code}

  * Medial power series (page 20 and 21).

\begin{code}

 _**_ : 𝕀 → ℕ → 𝕀
 a ** 0      = +1
 a ** succ n = a * (a ** n)

 powerseries : (ℕ → 𝕀) → (𝕀 → 𝕀)
 powerseries a = λ x → M (λ n → (a n) * (x ** n))

\end{code}

  TODO. (Important.) The "double" stuff is not included yet.
  We need to axiomatize the existence of double (page 33 and
  onwards of the slides).

\begin{code}
  
 double : 𝕀 → 𝕀
 double = pr₁ hd

 double₁ : (x : 𝕀) → double (x ⊕ (u ⊕ v)) ≡ x
 double₁ = pr₁ (pr₂ hd)

 double₂ : (x : 𝕀) → double (u ⊕ (u ⊕ x)) ≡ u
 double₂ = pr₁ (pr₂ (pr₂ hd))

 double₃ : (x : 𝕀) → double (v ⊕ (v ⊕ x)) ≡ v
 double₃ = pr₂ (pr₂ (pr₂ hd))

 _/2 : 𝕀 → 𝕀
 _/2 = _⊕ O
 +1/2 = +1 /2
 −1/2 = −1 /2

 infixl 99 _/2

 factual : (x : 𝕀) → − (x /2) ≡ − x /2
 factual x = −-is-⊕-homomorphism x O ∙ ap (− x ⊕_) O-inverse

 O-half : O /2 ≡ O
 O-half = ⊕-idem O
 
 −1-half : − +1/2 ≡ −1/2
 −1-half = factual +1 ∙ ap _/2 +1-inverse

 +1-half : − −1/2 ≡ +1/2
 +1-half = factual −1 ∙ ap _/2 −1-inverse

 half-same : _* +1/2 ≡ _/2
 half-same = {!!}

 _+𝕀_ _−𝕀_ : 𝕀 → 𝕀 → 𝕀 -- Truncated addition and subtraction
 x +𝕀 y = double (x ⊕ y)
 x −𝕀 y = double (x ⊖ y)

 maxO : 𝕀 → 𝕀 -- max O x
 maxO x = (double (−1/2 +𝕀 x)) /2 +𝕀 +1/2

 O-midpoint-of-halves : −1/2 ⊕ +1/2 ≡ O
 O-midpoint-of-halves = ⊕-tran −1 O +1 O
                         ∙ ap (O ⊕_) (⊕-idem O)
                         ∙ ⊕-idem O
                         
 double-O-is-O : double O ≡ O
 double-O-is-O = ap double (⊕-idem O ⁻¹) ∙ double₁ O

 maxO-O-is-O : maxO O ≡ O
 maxO-O-is-O = one ∙ two ∙ three where
   one : maxO O ≡ (double −1/2) /2 +𝕀 +1/2
   one = ap (λ - → (double - /2) +𝕀 +1/2) (double₁ −1/2)
   two : (double −1/2) /2 +𝕀 +1/2 ≡ −1/2 +𝕀 +1/2
   two = ap (λ - → - /2 +𝕀 +1/2) (double₂ +1)
   three : double (−1/2 ⊕ +1/2) ≡ O
   three = ap double O-midpoint-of-halves ∙ double-O-is-O

 max _∨_ : 𝕀 → 𝕀 → 𝕀
 max x y = double ((x /2) +𝕀 maxO (y ⊖ x))
 _∨_ = max

 max-idem : idempotent _∨_
 max-idem a = first ∙ second ∙ third where
   first : double ((a /2) +𝕀 maxO (a ⊖ a)) ≡ double ((a /2) +𝕀 O)
   first = ap (λ - → double ((a /2) +𝕀 -))
          (ap maxO (⊖-zero a) ∙ maxO-O-is-O)
   second : double ((a /2) +𝕀 O) ≡ double ((a /2))
   second = ap double (double₁ (a /2))
   third : double (a /2) ≡ a
   third = double₁ a

 max-comm : commutative _∨_
 max-comm = {!!}

 max-assoc : associative _∨_
 max-assoc = {!!}
 
 min : 𝕀 → 𝕀 → 𝕀
 min x y = − (max (− x) (− y))

 abs : 𝕀 → 𝕀
 abs x = max (− x) x


\end{code}
  * max (_∨_) is a semilattice -- assoc, comm, idem
    - derive order from this semilattice

  * Pull request goes here

  * TODO. being-interval-object-is-prop. -- in another file

  * Page 42. - Prove the limit *is* the limit, as above

----

  * Implement the axioms

(ℕ      →      ℕ          →           𝕀)
numerator     denominator   numer/denom
                            (binary expansion stream applied to M)
