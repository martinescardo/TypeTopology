Todd Waugh Ambridge, January 2024

M.H. Escardo and A. Simpson. A universal characterization of the
closed Euclidean interval (extended abstract). Proceedings of the 16th
Annual IEEE Symposium on Logic in Computer Science,
pp.115--125. Boston, Massachusetts, June 16-19, 2001.

https://doi.org/10.1109/LICS.2001.932488

# Formalisation of the Escardo-Simpson interval object

\begin{code}
{-# OPTIONS --without-K --safe #-}

open import UF.FunExt
open import MLTT.Spartan
open import Naturals.Addition renaming (_+_ to _+ℕ_)
open import UF.Subsingletons
open import UF.Sets

module TWA.Thesis.Chapter5.IntervalObject (fe : FunExt) where

open import Naturals.Sequence fe
\end{code}

## Midpoint algebras

\begin{code}
idempotent transpositional : {X : 𝓤 ̇ } → (X → X → X) → 𝓤 ̇
idempotent       _∙_
 = ∀ a       → a ∙ a             ＝ a
transpositional  _∙_
 = ∀ a b c d → (a ∙ b) ∙ (c ∙ d) ＝ (a ∙ c) ∙ (b ∙ d)

seq-add-push : {A : 𝓤 ̇ } (α : ℕ → A) (n : ℕ)
             → (λ i → α (succ i +ℕ n)) ＝ (λ i → α (succ (i +ℕ n)))
seq-add-push α 0 = refl
seq-add-push α (succ n) = seq-add-push (α ∘ succ) n

midpoint-algebra-axioms : (A : 𝓤 ̇ ) → (A → A → A) → 𝓤 ̇
midpoint-algebra-axioms {𝓤} A _⊕_
 = is-set A × idempotent _⊕_ × commutative _⊕_ × transpositional _⊕_

Midpoint-algebra : (𝓤 : Universe) → 𝓤 ⁺ ̇
Midpoint-algebra 𝓤
 = Σ A ꞉ 𝓤 ̇ , Σ _⊕_ ꞉ (A → A → A) , (midpoint-algebra-axioms A _⊕_)

cancellative : {X : 𝓤 ̇ } → (X → X → X) → 𝓤 ̇
cancellative  _∙_ = ∀ a b c → a ∙ c ＝ b ∙ c → a ＝ b
\end{code}

## Iteration property

\begin{code}
iterative : {A : 𝓤 ̇ } → (A → A → A) → 𝓤 ̇
iterative {𝓤} {A} _⊕_
 = Σ M ꞉ ((ℕ → A) → A) , ((a : ℕ → A) → M a ＝ a 0 ⊕ M (tail a))
                       × ((a x : ℕ → A)
                         → ((i : ℕ) → a i ＝ x i ⊕ a (succ i))
                         → a 0 ＝ M x)

iterative-uniqueness· : {A : 𝓤 ̇ } → (_⊕_ : A → A → A)
                      → (F M : iterative _⊕_)
                      → pr₁ F ∼ pr₁ M
iterative-uniqueness· {𝓤} {𝕀} _⊕_ (F , p₁ , q₁) (M , p₂ , q₂) x
 = q₂ M' x γ
 where M' : ℕ → 𝕀
       M' i = F (λ n → x (n +ℕ i))
       γ : (i : ℕ) → M' i ＝ (x i ⊕ M' (succ i))
       γ i = p₁ (λ n → x (n +ℕ i))
           ∙ ap (λ - → x - ⊕ F (λ n → x (succ n +ℕ i)))
                  (zero-left-neutral i)
           ∙ ap (λ - → x i ⊕ F -) (seq-add-push x i)

iterative-uniqueness : {A : 𝓤 ̇ } → (_⊕_ : A → A → A)
                     → (F M : iterative _⊕_)
                     → pr₁ F ＝ pr₁ M
iterative-uniqueness {𝓤} _⊕_ F M
 = dfunext (fe 𝓤 𝓤) (iterative-uniqueness· _⊕_ F M)
\end{code}

## Convex bodies

\begin{code}
convex-body-axioms : (A : 𝓤 ̇ ) → (A → A → A) → 𝓤 ̇
convex-body-axioms {𝓤} A _⊕_ = (midpoint-algebra-axioms A _⊕_)
                             × (cancellative _⊕_)
                             × (iterative _⊕_)

Convex-body : (𝓤 : Universe) → 𝓤 ⁺ ̇
Convex-body 𝓤
 = Σ A ꞉ 𝓤 ̇ , Σ _⊕_ ꞉ (A → A → A) , (convex-body-axioms A _⊕_)

⟨_⟩ : Convex-body 𝓤 → 𝓤 ̇
⟨ A , _ ⟩ = A
\end{code}

## Midpoint homomorphisms

\begin{code}
midpoint-operation : (𝓐 : Convex-body 𝓤) → ⟨ 𝓐 ⟩ → ⟨ 𝓐 ⟩ → ⟨ 𝓐 ⟩
midpoint-operation (A , _⊕_ , _) = _⊕_

syntax midpoint-operation 𝓐 x y = x ⊕⟨ 𝓐 ⟩ y

is-⊕-homomorphism : (𝓐 : Convex-body 𝓤) (𝓑 : Convex-body 𝓥)
                  → (⟨ 𝓐 ⟩ → ⟨ 𝓑 ⟩) → 𝓤 ⊔ 𝓥 ̇
is-⊕-homomorphism 𝓐 𝓑 h
 = (x y : ⟨ 𝓐 ⟩) → h (x ⊕⟨ 𝓐 ⟩ y) ＝ h x ⊕⟨ 𝓑 ⟩ h y

id-is-⊕-homomorphism : (𝓐 : Convex-body 𝓤) → is-⊕-homomorphism 𝓐 𝓐 id
id-is-⊕-homomorphism 𝓐 x y = refl

⊕-is-⊕-homomorphism-r : (𝓐 : Convex-body 𝓤)
                      → (a : ⟨ 𝓐 ⟩)
                      → is-⊕-homomorphism 𝓐 𝓐 (λ y → a ⊕⟨ 𝓐 ⟩ y)
⊕-is-⊕-homomorphism-r (𝓐 , _⊕_ , (_ , ⊕-idem , _ , ⊕-tran) , _) a x y
 =    a    ⊕ (x ⊕ y) ＝⟨ ap (_⊕ (x ⊕ y)) (⊕-idem a ⁻¹) ⟩
   (a ⊕ a) ⊕ (x ⊕ y) ＝⟨ ⊕-tran a a x y ⟩
   (a ⊕ x) ⊕ (a ⊕ y) ∎

⊕-is-⊕-homomorphism-l : (𝓐 : Convex-body 𝓤)
                      → (b : ⟨ 𝓐 ⟩)
                      → is-⊕-homomorphism 𝓐 𝓐 (λ x → x ⊕⟨ 𝓐 ⟩ b)
⊕-is-⊕-homomorphism-l (𝓐 , _⊕_ , (_ , ⊕-idem , _ , ⊕-tran) , _) b x y
 = (x ⊕ y) ⊕    b    ＝⟨ ap ((x ⊕ y) ⊕_) (⊕-idem b ⁻¹) ⟩
   (x ⊕ y) ⊕ (b ⊕ b) ＝⟨ ⊕-tran x y b b ⟩
   (x ⊕ b) ⊕ (y ⊕ b) ∎

⊕-hom-composition : (𝓐 : Convex-body 𝓤)
                    (𝓑 : Convex-body 𝓥)
                    (𝓒 : Convex-body 𝓦)
                  → (h₁ : ⟨ 𝓐 ⟩ → ⟨ 𝓑 ⟩) → (h₂ : ⟨ 𝓑 ⟩ → ⟨ 𝓒 ⟩)
                  → is-⊕-homomorphism 𝓐 𝓑 h₁
                  → is-⊕-homomorphism 𝓑 𝓒 h₂
                  → is-⊕-homomorphism 𝓐 𝓒 (h₂ ∘ h₁)
⊕-hom-composition {𝓤} {𝓥} {𝓦} 𝓐 𝓑 𝓒 h₁ h₂ i₁ i₂ x y
  = (h₂ ∘ h₁) (x ⊕⟨ 𝓐 ⟩ y)                       ＝⟨ ap h₂ (i₁ x y) ⟩
         h₂  ((h₁ x) ⊕⟨ 𝓑 ⟩ (h₁ y))             ＝⟨ i₂ (h₁ x) (h₁ y) ⟩
             ((h₂ ∘ h₁) x) ⊕⟨ 𝓒 ⟩ ((h₂ ∘ h₁) y) ∎
\end{code}

## Interval objects

\begin{code}
is-interval-object
 : (𝓘 : Convex-body 𝓤) (𝓥 : Universe) → ⟨ 𝓘 ⟩ → ⟨ 𝓘 ⟩ → 𝓤 ⊔ 𝓥 ⁺ ̇
is-interval-object 𝓘 𝓥 u v
 = (𝓐 : Convex-body 𝓥) (a b : ⟨ 𝓐 ⟩)
 → ∃! h ꞉ (⟨ 𝓘 ⟩ → ⟨ 𝓐 ⟩)
 , (h u ＝ a) × (h v ＝ b)
 × ((x y : ⟨ 𝓘 ⟩) → h (x ⊕⟨ 𝓘 ⟩ y) ＝ h x ⊕⟨ 𝓐 ⟩ h y)

record Interval-object (𝓤 : Universe) : 𝓤ω where
 field
  𝕀 : 𝓤 ̇
  _⊕_ : 𝕀 → 𝕀 → 𝕀
  u v : 𝕀
  mpaa : midpoint-algebra-axioms 𝕀 _⊕_
  ca : cancellative _⊕_
  ia : iterative _⊕_
  universal-property
   : is-interval-object (𝕀 , _⊕_ , mpaa , ca , ia) 𝓤 u v

module basic-interval-object-development {𝓤 : Universe}
 (io : Interval-object 𝓤) where

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
\end{code}

## Affine map

\begin{code}
 affine : 𝕀 → 𝕀 → 𝕀 → 𝕀
 affine x y = ∃!-witness (universal-property 𝓘 x y)

 affine-equation-l : (x y : 𝕀) → affine x y u ＝ x
 affine-equation-l x y
  = pr₁ (∃!-is-witness (universal-property 𝓘 x y))

 affine-equation-r : (x y : 𝕀) → affine x y v ＝ y
 affine-equation-r x y
  = pr₁ (pr₂ (∃!-is-witness (universal-property 𝓘 x y)))

 affine-is-⊕-homomorphism : (x y : 𝕀) (a b : 𝕀)
                          → affine x y (a ⊕ b)
                          ＝ affine x y a ⊕ affine x y b
 affine-is-⊕-homomorphism x y
  = pr₂ (pr₂ (∃!-is-witness (universal-property 𝓘 x y)))

 affine-uniqueness : (f : 𝕀 → 𝕀) (a b : 𝕀)
                   → f u ＝ a
                   → f v ＝ b
                   → is-⊕-homomorphism 𝓘 𝓘 f
                   → affine a b ＝ f
 affine-uniqueness f a b l r i
  = ap pr₁ (∃!-uniqueness' (universal-property 𝓘 a b) (f , l , r , i))

 affine-uniqueness· : (f : 𝕀 → 𝕀) (a b : 𝕀)
                   → f u ＝ a
                   → f v ＝ b
                   → is-⊕-homomorphism 𝓘 𝓘 f
                   → affine a b ∼ f
 affine-uniqueness· f a b l r i x
  = ap (λ - → - x) (affine-uniqueness f a b l r i)

 affine-uv-involutive : affine u v ∼ id
 affine-uv-involutive
  = affine-uniqueness· id u v refl refl (id-is-⊕-homomorphism 𝓘)

 affine-constant : (a : 𝕀) (x : 𝕀) → affine a a x ＝ a
 affine-constant a
  = affine-uniqueness· (λ _ → a) a a refl refl (λ _ _ → ⊕-idem a ⁻¹)
\end{code}

## M properties

\begin{code}
 M : (ℕ → 𝕀) → 𝕀
 M = pr₁ ia

 M-prop₁ : (a : ℕ → 𝕀) → M a ＝ a 0 ⊕ (M (a ∘ succ))
 M-prop₁ = pr₁ (pr₂ ia)

 M-prop₂ : (a x : ℕ → 𝕀)
         → ((i : ℕ) → a i ＝ x i ⊕ a (succ i))
         → a 0 ＝ M x
 M-prop₂ = pr₂ (pr₂ ia)

 M-idem : (x : 𝕀) → M (λ _ → x) ＝ x
 M-idem x = M-prop₂ (λ _ → x) (λ _ → x) (λ _ → ⊕-idem x ⁻¹) ⁻¹

 M-hom : (x y : ℕ → 𝕀) → (M x ⊕ M y) ＝ M (λ i → x i ⊕ y i)
 M-hom x y = M-prop₂ M' (λ i → x i ⊕ y i) γ where
   M' : ℕ → 𝕀
   M' i = M (λ n → x (n +ℕ i)) ⊕ M (λ n → y (n +ℕ i))
   γ : (i : ℕ) → M' i ＝ ((x i ⊕ y i) ⊕ M' (succ i))
   γ i = M (λ n → x (n +ℕ i)) ⊕ M (λ n → y (n +ℕ i))
             ＝⟨ ap (_⊕ M (λ n → y (n +ℕ i)))
                   (M-prop₁ (λ n → x (n +ℕ i))) ⟩
         (x (0 +ℕ i) ⊕ M (λ n → x (succ n +ℕ i)))
           ⊕ M (λ n → y (n +ℕ i))
             ＝⟨ ap ((x (0 +ℕ i) ⊕ M (λ n → x (succ n +ℕ i))) ⊕_)
                   (M-prop₁ (λ n → y (n +ℕ i))) ⟩
         (x (0 +ℕ i) ⊕ M (λ n → x (succ n +ℕ i)))
           ⊕ (y (0 +ℕ i) ⊕ M (λ n → y (succ n +ℕ i)))
             ＝⟨ ⊕-tran
                   (x (0 +ℕ i)) (M (λ n → x (succ n +ℕ i)))
                   (y (0 +ℕ i)) (M (λ n → y (succ n +ℕ i))) ⟩
         ((x (0 +ℕ i) ⊕ y (0 +ℕ i))
           ⊕ (M (λ n → x (succ n +ℕ i)) ⊕ M (λ n → y (succ n +ℕ i))))
             ＝⟨ ap (λ - → (x - ⊕ y -)
                           ⊕ (M (λ n → x (succ n +ℕ i))
                             ⊕ M (λ n → y (succ n +ℕ i))))
                   (zero-left-neutral i) ⟩
         ((x i ⊕ y i) ⊕ (M (λ n → x (succ n +ℕ i))
           ⊕ M (λ n → y (succ n +ℕ i))))
             ＝⟨ ap (λ - → (x i ⊕ y i)
                           ⊕ (M - ⊕ M (λ n → y (succ n +ℕ i))))
                   (seq-add-push x i) ⟩
         ((x i ⊕ y i)
           ⊕ (M (λ n → x (succ (n +ℕ i)))
             ⊕ M (λ n → y (succ n +ℕ i))))
             ＝⟨ ap (λ - → (x i ⊕ y i)
                           ⊕ (M (λ n → x (succ (n +ℕ i))) ⊕ M -))
                   (seq-add-push y i) ⟩
         (x i ⊕ y i) ⊕ M' (succ i) ∎

 M-prop₁-inner : (x : ℕ → ℕ → 𝕀)
               → M (λ i → M (λ j → x i j))
               ＝ M (λ i → x i 0 ⊕ M (λ j → x i (succ j)))
 M-prop₁-inner x = ap M (dfunext (fe 𝓤₀ 𝓤) (λ i → M-prop₁ (x i)))

 M-symm : (x : ℕ → ℕ → 𝕀)
        → M (λ i → M (λ j → x i j)) ＝ M (λ i → (M λ j → x j i))
 M-symm x = M-prop₂ M' (λ i → M (λ j → x j i)) γ where
   M' : ℕ → 𝕀
   M' n = M (λ i → M (λ j → x i (j +ℕ n)))
   γ : (i : ℕ) → M' i ＝ (pr₁ ia (λ j → x j i) ⊕ M' (succ i))
   γ n = M (λ i → M (λ j → x i (j +ℕ n)))
             ＝⟨ M-prop₁-inner (λ i j → x i (j +ℕ n)) ⟩
         M (λ i → x i (0 +ℕ n) ⊕ M (λ j → x i (succ j +ℕ n)))
             ＝⟨ M-hom (λ i → x i (0 +ℕ n))
                      (λ i → M (λ j → x i (succ j +ℕ n))) ⁻¹ ⟩
         M (λ i → x i (0 +ℕ n)) ⊕ M (λ i → M (λ j → x i (succ j +ℕ n)))
             ＝⟨ ap (λ - → M (λ i → x i -)
                    ⊕ M (λ i → M (λ j → x i (succ j +ℕ n))))
                   (zero-left-neutral n) ⟩
         M (λ i → x i n) ⊕ M (λ i → M (λ j → x i (succ j +ℕ n)))
             ＝⟨ ap (M (λ j → x j n) ⊕_) (seq-seq-add-push x n) ⟩
         M (λ j → x j n) ⊕ M' (succ n) ∎
     where
       seq-seq-add-push : (x : ℕ → ℕ → 𝕀) (n : ℕ)
                        → M (λ i → M (λ j → x i (succ j +ℕ n)))
                        ＝ M (λ i → M (λ j → x i (succ (j +ℕ n))))
       seq-seq-add-push x 0 = refl
       seq-seq-add-push x (succ n)
        = seq-seq-add-push (λ i j → x i (succ j)) n

 ⊕-homs-are-M-homs : (h : 𝕀 → 𝕀) → is-⊕-homomorphism 𝓘 𝓘 h
           → (z : ℕ → 𝕀) → h (M z) ＝ M (λ n → h (z n))
 ⊕-homs-are-M-homs h hom z = M-prop₂ M' (λ n → h (z n)) γ where
   M' : ℕ → 𝕀
   M' i = h (M (λ n → z (n +ℕ i)))
   γ : (i : ℕ) → M' i ＝ (h (z i) ⊕ M' (succ i))
   γ i = h (M (λ n → z (n +ℕ i)))
            ＝⟨ ap h (M-prop₁ (λ n → z (n +ℕ i))) ⟩
         h (z (0 +ℕ i) ⊕ M (λ n → z (succ n +ℕ i)))
            ＝⟨ hom (z (0 +ℕ i)) (M (λ n → z (succ n +ℕ i))) ⟩
         h (z (0 +ℕ i)) ⊕ h (M (λ n → z (succ n +ℕ i)))
            ＝⟨ ap (λ - → h (z -) ⊕ h (M (λ n → z (succ n +ℕ i))))
                  (zero-left-neutral i) ⟩
         h (z i) ⊕ h (M (λ n → z (succ n +ℕ i)))
            ＝⟨ ap (λ - → h (z i) ⊕ h (M -))
                  (seq-add-push z i) ⟩
         h (z i) ⊕ M' (succ i)
            ∎

 affine-M-hom : (x y : 𝕀) (z : ℕ → 𝕀)
              → affine x y (M z) ＝ M (λ n → affine x y (z n))
 affine-M-hom x y z
  = ⊕-homs-are-M-homs (affine x y) (affine-is-⊕-homomorphism x y) z
\end{code}

## Representing [-1,1]

\begin{code}
 −1 +1 : 𝕀
 −1 = u
 +1 = v

 O : 𝕀
 O  = −1 ⊕ +1
\end{code}

## Negation

\begin{code}
 −_ : 𝕀 → 𝕀
 −_ = affine +1 −1

 infixl 100 −_

 −-is-⊕-homomorphism : (a b : 𝕀) → − (a ⊕ b) ＝ − a ⊕ − b
 −-is-⊕-homomorphism = affine-is-⊕-homomorphism +1 −1

 −1-inverse : − −1 ＝ +1
 −1-inverse = affine-equation-l +1 −1

 +1-inverse : − +1 ＝ −1
 +1-inverse = affine-equation-r +1 −1

 O-inverse : − O ＝ O
 O-inverse =    − O      ＝⟨ −-is-⊕-homomorphism −1 +1 ⟩
             − −1 ⊕ − +1 ＝⟨ ap (_⊕ − +1) −1-inverse ⟩
               +1 ⊕ − +1 ＝⟨ ap (+1 ⊕_)   +1-inverse ⟩
               +1 ⊕ −1   ＝⟨ ⊕-comm +1 −1 ⟩
                  O      ∎

 −1-neg-inv : − − −1 ＝ −1
 −1-neg-inv = − − −1 ＝⟨ ap −_ −1-inverse ⟩
                − +1 ＝⟨ +1-inverse ⟩
                  −1 ∎

 +1-neg-inv : − − +1 ＝ +1
 +1-neg-inv = − − +1 ＝⟨ ap −_ +1-inverse ⟩
                − −1 ＝⟨ −1-inverse ⟩
                  +1 ∎

 −-involutive : (x : 𝕀) → − − x ＝ x
 −-involutive x =         − − x ＝⟨ negation-involutive' x ⁻¹ ⟩
                 affine −1 +1 x ＝⟨ affine-uv-involutive x ⟩
                              x  ∎
  where
   −−-is-⊕-homomorphism : is-⊕-homomorphism 𝓘 𝓘 (λ x → − (− x))
   −−-is-⊕-homomorphism = ⊕-hom-composition 𝓘 𝓘 𝓘 −_ −_
                          −-is-⊕-homomorphism −-is-⊕-homomorphism
   negation-involutive' : (x : 𝕀) → affine −1 +1 x ＝ − (− x)
   negation-involutive' = affine-uniqueness· (λ x → − (− x))
                          −1 +1 −1-neg-inv +1-neg-inv
                          −−-is-⊕-homomorphism

 _⊖_ : 𝕀 → 𝕀 → 𝕀
 x ⊖ y = x ⊕ (− y)

 ⊖-zero : (x : 𝕀) → x ⊖ x ＝ O
 ⊖-zero x = x ⊖ x        ＝⟨ ⊖-fact' ⁻¹ ⟩
            affine O O x ＝⟨ affine-constant O x ⟩
            O            ∎
   where
    ⊖-fact' : affine O O x ＝ x ⊖ x
    ⊖-fact' = affine-uniqueness· (λ x → x ⊖ x) O O
              (ap (−1 ⊕_) −1-inverse)
              (ap (+1 ⊕_) +1-inverse ∙ ⊕-comm +1 −1)
              (λ x y → ap ((x ⊕ y) ⊕_)
                          (−-is-⊕-homomorphism x y)
                     ∙ ⊕-tran x y (− x) (− y))
              x
\end{code}

## Multiplication

\begin{code}
 _*_ : 𝕀 → 𝕀 → 𝕀
 x * y = affine (− x) x y

 infixl 99 _*_

 *-gives-negation-l : (x : 𝕀) → x * −1 ＝ − x
 *-gives-negation-l x = affine-equation-l (− x) x

 *-gives-id-l : (x : 𝕀) → x * +1 ＝ x
 *-gives-id-l x = affine-equation-r (− x) x

 *-is-⊕-homomorphism-l : (a : 𝕀) → is-⊕-homomorphism 𝓘 𝓘 (a *_)
 *-is-⊕-homomorphism-l a x y = affine-is-⊕-homomorphism (− a) a x y

 *-gives-negation-r : (y : 𝕀) → −1 * y ＝ − y
 *-gives-negation-r y = ap (λ - → affine - −1 y) −1-inverse

 *-gives-id-r : (y : 𝕀) → +1 * y ＝ y
 *-gives-id-r y
  = ap (λ - → affine - +1 y) +1-inverse ∙ affine-uv-involutive y

 *-commutative : commutative _*_
 *-commutative x y = γ y
  where
   j : (a b : 𝕀) → is-⊕-homomorphism 𝓘 𝓘 (λ x → a * x ⊕ b * x)
   j a b x y
       = ap (_⊕ b * (x ⊕ y)) (*-is-⊕-homomorphism-l a x y)
       ∙ ap ((a * x ⊕ a * y) ⊕_) (*-is-⊕-homomorphism-l b x y)
       ∙ ⊕-tran (a * x) (a * y) (affine (− b) b x) (affine (− b) b y)
   i : is-⊕-homomorphism 𝓘 𝓘 (λ y → y * x)
   i y z = p
    where
     p : (y ⊕ z) * x ＝ (y * x ⊕ z * x)
     p = affine-uniqueness· (λ x → y * x ⊕ z * x) (− (y ⊕ z)) (y ⊕ z)
         (ap (_⊕ z * u) (*-gives-negation-l y)
         ∙ ap ((− y) ⊕_) (*-gives-negation-l z)
         ∙ affine-is-⊕-homomorphism +1 −1 y z ⁻¹)
         (ap (_⊕ z * v) (*-gives-id-l y)
         ∙ ap (y ⊕_) (*-gives-id-l z))
         (j y z) x
   γ : (λ y → x * y) ∼ (λ y → y * x)
   γ = affine-uniqueness· (λ y → y * x)
       (− x) x (*-gives-negation-r x) (*-gives-id-r x)
       i

 *-gives-zero-l : (x : 𝕀) → x * O ＝ O
 *-gives-zero-l x = *-is-⊕-homomorphism-l x u v
                  ∙ ap (_⊕ (x * v)) (*-gives-negation-l x)
                  ∙ ap (− x ⊕_) (*-gives-id-l x)
                  ∙ ⊕-comm (− x) x
                  ∙ ⊖-zero x

 *-gives-zero-r : (x : 𝕀) → O * x ＝ O
 *-gives-zero-r x = *-commutative O x ∙ *-gives-zero-l x

 *-is-⊕-homomorphism-r : (b : 𝕀) → is-⊕-homomorphism 𝓘 𝓘 (_* b)
 *-is-⊕-homomorphism-r b x y =
      (x ⊕ y) * b       ＝⟨ *-commutative (x ⊕ y) b ⟩
      b * (x ⊕ y)       ＝⟨ *-is-⊕-homomorphism-l b x y ⟩
      (b * x) ⊕ (b * y) ＝⟨ ap ((b * x) ⊕_) (*-commutative b y) ⟩
      (b * x) ⊕ (y * b) ＝⟨ ap (_⊕ (y * b)) (*-commutative b x) ⟩
      (x * b) ⊕ (y * b) ∎

 *-prop : (x y : 𝕀) → x * y ＝ − (x * − y)
 *-prop x y = affine-uniqueness· (λ - → − (x * (− -))) (− x) x l r i y
  where
   l = − (x * (− −1)) ＝⟨ ap (λ - → − (x * -)) −1-inverse ⟩
       − (x *    +1 ) ＝⟨ ap −_ (*-gives-id-l x) ⟩
       −  x           ∎
   r = − (x * (− +1)) ＝⟨ ap (λ - → − (x * -)) +1-inverse ⟩
       − (x *    −1 ) ＝⟨ ap −_ (*-gives-negation-l x) ⟩
       −  (− x)       ＝⟨ −-involutive x ⟩
             x        ∎
   i : is-⊕-homomorphism 𝓘 𝓘 (λ - → − (x * (− -)))
   i a b = −  (x * (− (a ⊕ b)))
                ＝⟨ ap (λ - → − (x * -)) (−-is-⊕-homomorphism a b) ⟩
           −  (x * (− a ⊕ − b))
                ＝⟨ ap −_ (affine-is-⊕-homomorphism (− x) x (− a) (− b)) ⟩
           − ((x * − a) ⊕ (x * − b))
                ＝⟨ affine-is-⊕-homomorphism +1 −1 (x * (− a)) (x * (− b)) ⟩
           − (x * − a) ⊕ − (x * − b) ∎

 *-assoc : (x y z : 𝕀) → x * (y * z) ＝ (x * y) * z
 *-assoc x y z = γ z ⁻¹
  where
   l =      x * (y * −1) ＝⟨ ap (x *_) (*-gives-negation-l y) ⟩
            x *  (− y)   ＝⟨ −-involutive (x * (− y)) ⁻¹ ⟩
     (− (− (x * − y)))   ＝⟨ ap −_ (*-prop x y ⁻¹) ⟩
         − (x * y)       ∎
   r = x * (y * +1) ＝⟨ ap (x *_) (*-gives-id-l y) ⟩
       x * y        ∎
   i : is-⊕-homomorphism 𝓘 𝓘 (λ z → x * (y * z))
   i a b = x * (y * (a ⊕ b))
                ＝⟨ ap (x *_) (*-is-⊕-homomorphism-l y a b) ⟩
           x * (y * a ⊕ y * b)
                ＝⟨ affine-is-⊕-homomorphism (− x) x (y * a) (y * b) ⟩
           x * (y * a) ⊕ x * (y * b) ∎
   γ : (λ z → (x * y) * z) ∼ (λ z → x * (y * z))
   γ = affine-uniqueness· (λ z → x * (y * z)) (− (x * y)) (x * y) l r i
\end{code}

## Halving

\begin{code}
 _/2 : 𝕀 → 𝕀
 _/2 = _⊕ O
 +1/2 = +1 /2
 −1/2 = −1 /2
\end{code}
