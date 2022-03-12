Martin Escardo, 12th September 2018.

We define arithmetic operations on ℕ∞ by corecursion as defined in the
module CoNaturals. The lack of pattern matching on Zero and Succ and
of some definitional equalities make some proofs lengthier than they
would be if we had used a built-in coinductive definition of ℕ∞.

We use the final coalgebra property of ℕ∞ for the functor 𝟙 + (-) to
both construct the functions and prove their properties (including
idempotency, commutativity and associativity of the minimum
operation).

NB. There are shorter constructions with more direct proofs of the
minimum function, e.g. take the pointwise minimum in 𝟚 (see the
module GenericConvergentSequence), but this module
serves as a good illustration of reasoning with the final coalgebra
property to both construct functions and prove their properties.

This file will grow on demand. The first operation we needed (for
codistances) is minimum.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import SpartanMLTT
open import UF-FunExt

module CoNaturalsArithmetic (fe : FunExt) where

private
 fe₀ : funext 𝓤₀ 𝓤₀
 fe₀ = fe 𝓤₀ 𝓤₀

open import Two-Properties
open import GenericConvergentSequence renaming (min to min')
open import CoNaturals fe
open import OrderNotation
open import CanonicalMapNotation
open import UF-Base

\end{code}

We consider a 𝟙 + (-) coalgebra κ on ℕ∞ × ℕ∞ so that min is the unique
homomorphism to the final coalgebra PRED : ℕ∞ → 𝟙 + ℕ∞ on ℕ∞.

\begin{code}

private
 κ-min : ℕ∞ × ℕ∞ → 𝟙 {𝓤₀} + ℕ∞ × ℕ∞
 κ-min (u , v) = 𝟚-Cases (positivity u)
                  (inl ⋆)
                  (𝟚-Cases (positivity v)
                    (inl ⋆)
                    (inr (Pred u , Pred v)))

min : ℕ∞ × ℕ∞ → ℕ∞
min = ℕ∞-corec κ-min

\end{code}

The defining equations of min thus are:

\begin{code}

min-eq₀ : ∀ v   → min (Zero , v) ≡ Zero
min-eq₁ : ∀ u   → min (Succ u , Zero) ≡ Zero
min-eq₂ : ∀ u v → min (Succ u , Succ v) ≡ Succ (min (u , v))

min-eq₀ = λ v   → Coalg-morphism-Zero κ-min (Zero , v) ⋆ refl
min-eq₁ = λ u   → Coalg-morphism-Zero κ-min (Succ u , Zero) ⋆ refl
min-eq₂ = λ u v → Coalg-morphism-Succ κ-min (Succ u , Succ v) (u , v) refl

\end{code}

Maximum (another version is defined in GenericConvergentSequence):

\begin{code}

private
 κ-max : ℕ∞ × ℕ∞ → 𝟙 {𝓤₀} + ℕ∞ × ℕ∞
 κ-max (u , v) = 𝟚-Cases (positivity u)
                   (𝟚-Cases (positivity v)
                      (inl ⋆)
                      (inr (Zero , Pred v)))
                   (𝟚-Cases (positivity v)
                      (inr (Pred u , Zero))
                      (inr (Pred u , (Pred v))))

max' : ℕ∞ × ℕ∞ → ℕ∞
max' = ℕ∞-corec κ-max

max-eq₀ :         max' (Zero , Zero) ≡ Zero
max-eq₁ : ∀ v   → max' (Zero , Succ v) ≡ Succ (max' (Zero , v))
max-eq₂ : ∀ u   → max' (Succ u , Zero) ≡ Succ (max' (u , Zero))
max-eq₃ : ∀ u v → max' (Succ u , Succ v) ≡ Succ (max' (u , v))

max-eq₀ =         Coalg-morphism-Zero κ-max (Zero , Zero) ⋆ refl
max-eq₁ = λ v   → Coalg-morphism-Succ κ-max (Zero , Succ v) (Zero , v) refl
max-eq₂ = λ u   → Coalg-morphism-Succ κ-max (Succ u , Zero) (u , Zero) refl
max-eq₃ = λ u v → Coalg-morphism-Succ κ-max (Succ u , Succ v) (u , v) refl

\end{code}

Addition:

\begin{code}

private
 κ-add : ℕ∞ × ℕ∞ → 𝟙 {𝓤₀} + ℕ∞ × ℕ∞
 κ-add (u , v) = 𝟚-Cases (positivity u)
                   (𝟚-Cases (positivity v)
                      (inl ⋆)
                      (inr (Zero , Pred v)))
                   (inr (Pred u , v))

add : ℕ∞ × ℕ∞ → ℕ∞
add = ℕ∞-corec κ-add

add-eq₀ :         add (Zero , Zero) ≡ Zero
add-eq₁ : ∀ v   → add (Zero , Succ v) ≡ Succ (add (Zero , v))
add-eq₂ : ∀ u v → add (Succ u , v) ≡ Succ (add (u , v))

add-eq₀ =         Coalg-morphism-Zero κ-add (Zero , Zero) ⋆ refl
add-eq₁ = λ v   → Coalg-morphism-Succ κ-add (Zero , Succ v) (Zero , v) refl
add-eq₂ = λ u v → Coalg-morphism-Succ κ-add (Succ u , v) (u , v) refl

\end{code}

We now prove properties of the minimum function using the
final-coalgebra property.

We already know that min (Zero , v) ≡ Zero, that is, Zero is
minimal. We next prove that ∞ is maximal, i.e., min (∞ , v) = v.

Using the equations min-eq₀ and min-eq₂, we have that the function
λ v → min (∞ , v) is an algebra homomorphism from PRED to PRED and
hence is equal to the identity function:


\begin{code}

min-unit : ∀ v → min (∞ , v) ≡ v
min-unit v = ap (λ - → - v) h-is-corec
 where
  h : ℕ∞ → ℕ∞
  h v = min (∞ , v)
  h-homomorphism : is-homomorphism PRED h
  h-homomorphism = dfunext fe₀ (λ v → φ v (Zero+Succ fe₀ v))
   where
    φ : (v : ℕ∞) → (v ≡ Zero) + (Σ t ꞉ ℕ∞ , v ≡ Succ t) → PRED (h v) ≡ 𝟙+ h (PRED v)
    φ v (inl refl) =
      PRED (min (∞ , Zero))        ≡⟨ ap PRED (min-eq₀ ∞) ⟩
      PRED Zero                    ≡⟨ refl ⟩
      𝟙+ h (PRED Zero)             ∎
    φ v (inr (t , refl)) =
      PRED (min (∞ , Succ t)) ≡⟨ ap (λ - → PRED (min (- , Succ t))) (Succ-∞-is-∞ fe₀ ⁻¹) ⟩
      PRED (min (Succ ∞ , Succ t)) ≡⟨ ap PRED (min-eq₂ ∞ t) ⟩
      PRED (Succ (min (∞ , t)))    ≡⟨ refl ⟩
      𝟙+ h (PRED (Succ t))         ∎
  h-is-corec : h ≡ id
  h-is-corec = homomorphism-uniqueness PRED h id h-homomorphism id-homomorphism

\end{code}

Using the equations min-eq₀ and min-eq₂, we have that the function
λ u → min (u , u) is an algebra homomorphism from PRED to PRED and
hence is equal to the identity function:

\begin{code}

min-idempotent : ∀ u → min (u , u) ≡ u
min-idempotent u = ap (λ - → - u) h-is-corec
 where
  h : ℕ∞ → ℕ∞
  h u = min (u , u)
  h-homomorphism : is-homomorphism PRED h
  h-homomorphism = dfunext fe₀ (λ u → φ (Zero+Succ fe₀ u))
   where
    φ : {u : ℕ∞} → (u ≡ Zero) + (Σ w ꞉ ℕ∞ , u ≡ Succ w) → PRED (h u) ≡ 𝟙+ h (PRED u)
    φ (inl refl) =
      PRED (min (Zero , Zero))     ≡⟨ ap PRED (min-eq₀ Zero) ⟩
      PRED Zero                    ≡⟨ refl ⟩
      𝟙+ h (PRED Zero)             ∎
    φ (inr (w , refl)) =
      PRED (min (Succ w , Succ w)) ≡⟨ ap PRED (min-eq₂ w w) ⟩
      PRED (Succ (min (w , w)))    ≡⟨ refl ⟩
      𝟙+ h (PRED (Succ w))         ∎
  h-is-corec : h ≡ id
  h-is-corec = homomorphism-uniqueness PRED h id h-homomorphism id-homomorphism

\end{code}

(Notice that the above argument actually shows that any function
f : ℕ∞ × ℕ∞ → ℕ∞ that satisfies f (Zero , Zero) ≡ Zero and
f (Succ w , Succ w) = Succ (f w) is idempotent, as it is the case of
the maximum function)

Similarly, to prove that min is commutative, we show that the function
λ (u , v) → min (v , u) satisfies the same "defining equations" as the
function min.

The following equation is derived from the above equations min-eq₀ and
min-eq₁ by cases on whether u is Zero or a Succ (Pred u).

\begin{code}

eq₃-from-eq₀-and-eq₁ : (h : ℕ∞ × ℕ∞ → ℕ∞)
                     → (∀ v → h (Zero , v) ≡ Zero)
                     → (∀ u → h (Succ u , Zero) ≡ Zero)
                     → (∀ u → h (u , Zero) ≡ Zero)
eq₃-from-eq₀-and-eq₁ h eq₀ eq₁ u = γ (Zero+Succ fe₀ u)
 where
  γ : (u ≡ Zero) + (Σ w ꞉ ℕ∞ , u ≡ Succ w) → h (u , Zero) ≡ Zero
  γ (inl refl)       = h (Zero , Zero)   ≡⟨ eq₀ Zero ⟩ Zero ∎
  γ (inr (w , refl)) = h (Succ w , Zero) ≡⟨ eq₁ w ⟩    Zero ∎

min-eq₃ : ∀ u → min (u , Zero) ≡ Zero
min-eq₃ = eq₃-from-eq₀-and-eq₁ min min-eq₀ min-eq₁

\end{code}

Conversely, if a function satisfies the above equations, then it is a
coalgebra homomorphism and hence is equal to ℕ∞-corec κ-min.

\begin{code}

min-equations-characterize-homomorphisms :
    (h : ℕ∞ × ℕ∞ → ℕ∞)
  → (∀ v   → h (Zero , v) ≡ Zero)
  → (∀ u   → h (Succ u , Zero) ≡ Zero)
  → (∀ u v → h (Succ u , Succ v) ≡ Succ (h (u , v)))
  → is-homomorphism κ-min h
min-equations-characterize-homomorphisms h eq₀ eq₁ eq₂ = dfunext fe₀ γ
  where
   γ : (w : ℕ∞ × ℕ∞) → PRED (h w) ≡ 𝟙+ h (κ-min w)
   γ (u , v) = φ (Zero+Succ fe₀ u) (Zero+Succ fe₀ v)
    where
     φ : (u ≡ Zero) + (Σ w ꞉ ℕ∞ , u ≡ Succ w)
       → (v ≡ Zero) + (Σ t ꞉ ℕ∞ , v ≡ Succ t)
       → PRED (h (u , v)) ≡ 𝟙+ h (κ-min (u , v))
     φ (inl refl) _  =
       PRED (h (Zero , v))            ≡⟨ ap PRED (eq₀ v) ⟩
       PRED Zero                      ≡⟨ refl ⟩
       𝟙+ h (κ-min (Zero , v))        ∎
     φ (inr (w , refl)) (inl refl) =
       PRED (h (Succ w , Zero))       ≡⟨ ap PRED (eq₁ w) ⟩
       PRED Zero                      ≡⟨ refl ⟩
       𝟙+ h (κ-min (Succ w , Zero))   ∎
     φ (inr (w , refl)) (inr (t , refl)) =
       PRED (h (Succ w , Succ t))     ≡⟨ ap PRED (eq₂ w t) ⟩
       PRED (Succ (h (w , t)))        ≡⟨ refl ⟩
       𝟙+ h (κ-min (Succ w , Succ t)) ∎

\end{code}

We can show that the min defined here is equivalent to that
given in GenericConvergentSequence:

\begin{code}

min'-eq₀ : ∀ v → uncurry min' (Zero , v) ≡ Zero
min'-eq₀ v = ℕ∞-to-ℕ→𝟚-lc (fe 𝓤₀ 𝓤₀) refl

min'-eq₁ : ∀ u → uncurry min' (Succ u , Zero) ≡ Zero
min'-eq₁ u = ℕ∞-to-ℕ→𝟚-lc  (fe 𝓤₀ 𝓤₀)
             (dfunext (fe 𝓤₀ 𝓤₀) (λ i → Lemma[min𝟚ab≡₀] (inr refl)))

min'-eq₂ : ∀ u v → uncurry min' (Succ u , Succ v) ≡ Succ (uncurry min' (u , v))
min'-eq₂ u v = ℕ∞-to-ℕ→𝟚-lc (fe 𝓤₀ 𝓤₀) (dfunext (fe 𝓤₀ 𝓤₀) γ)
 where γ : pr₁ (uncurry min' (Succ u , Succ v)) ∼ pr₁ (Succ (uncurry min' (u , v)))
       γ zero = refl
       γ (succ i) = refl

min≡ : min ≡ uncurry min'
min≡ = homomorphism-uniqueness κ-min min (uncurry min')
       (ℕ∞-corec-homomorphism κ-min)
       (min-equations-characterize-homomorphisms
        (uncurry min') min'-eq₀ min'-eq₁ min'-eq₂)

\end{code}

To prove that min is commutative, we show that the following function
h is also a coalgebra homomorphism and hence equal to ℕ∞-corec p:

\begin{code}

min-commutative : ∀ u v → min (u , v) ≡ min (v , u)
min-commutative u v = h (v , u)               ≡⟨ ap (λ - → - (v , u)) h-is-min ⟩
                      ℕ∞-corec κ-min (v , u) ∎
 where
  h : ℕ∞ × ℕ∞ → ℕ∞
  h (u , v) = min (v , u)
  h-homomorphism : is-homomorphism κ-min h
  h-homomorphism = min-equations-characterize-homomorphisms h h-eq₀ h-eq₁ h-eq₂
   where
    h-eq₀ : (v : ℕ∞) → min (v , Zero) ≡ Zero
    h-eq₀ v = min-eq₃ v
    h-eq₁ : (u : ℕ∞) → min (Zero , Succ u) ≡ Zero
    h-eq₁ u = min-eq₀ (Succ u)
    h-eq₂ : (u v : ℕ∞) → min (Succ v , Succ u) ≡ Succ (min (v , u))
    h-eq₂ u v = min-eq₂ v u
  h-is-min : h ≡ min
  h-is-min = homomorphism-uniqueness κ-min h (ℕ∞-corec κ-min)
              h-homomorphism (ℕ∞-corec-homomorphism κ-min)

\end{code}

Similarly, to prove that min is associative, we show that the two functions

   λ (u , v , w) → min (u , min (v , w))
   λ (u , v , w) → min (min (u , v) , w)

are homormorphisms from the same coalgebra on ℕ∞ × ℕ∞ × ℕ∞ to the
final coalgebra PRED.

\begin{code}

min-associative : (u v w : ℕ∞) → min (u , min (v , w)) ≡ min (min (u , v) , w)
min-associative u v w = ap (λ - → - (u , v , w)) p
 where
  f g : ℕ∞ × ℕ∞ × ℕ∞ → ℕ∞
  f (u , v , w) = min (u , min (v , w))
  g (u , v , w) = min (min (u , v) , w)
  κ : ℕ∞ × ℕ∞ × ℕ∞ → 𝟙 + ℕ∞ × ℕ∞ × ℕ∞
  κ (u , v , w) = 𝟚-Cases (positivity u)
                   (inl ⋆)
                   (𝟚-Cases (positivity v)
                     (inl ⋆)
                     (𝟚-Cases (positivity w)
                       (inl ⋆)
                       (inr (Pred u , Pred v , Pred w))))
  f-homomorphism : is-homomorphism κ f
  f-homomorphism = dfunext fe₀ γ
   where
    γ : (z : ℕ∞ × ℕ∞ × ℕ∞) → PRED (f z) ≡ 𝟙+ f (κ z)
    γ (u , v , w) = φ (Zero+Succ fe₀ u) (Zero+Succ fe₀ v) (Zero+Succ fe₀ w)
     where
      φ : (u ≡ Zero) + (Σ x ꞉ ℕ∞ , u ≡ Succ x)
       → (v ≡ Zero) + (Σ y ꞉ ℕ∞ , v ≡ Succ y)
       → (w ≡ Zero) + (Σ z ꞉ ℕ∞ , w ≡ Succ z)
       → PRED (f (u , v , w)) ≡ 𝟙+ f (κ (u , v , w))
      φ (inl refl) _ _ = ap PRED (min-eq₀ (min (v , w)))
      φ (inr (x , refl)) (inl refl) _ =
        PRED (min (Succ x , min (Zero , w)))        ≡⟨ ap (λ - → PRED (min (Succ x , -))) (min-eq₀ w) ⟩
        PRED (min (Succ x , Zero))                  ≡⟨ ap PRED (min-eq₃ u) ⟩
        PRED Zero                                   ≡⟨ ap PRED (min-eq₃ u) ⟩
        𝟙+ f (κ (Succ x , Zero , w))                ∎
      φ (inr (x , refl)) (inr (y , refl)) (inl refl) =
        PRED (min (Succ x , min (Succ y , Zero)))   ≡⟨ ap (λ - → PRED (min (Succ x , -))) (min-eq₃ (Succ y)) ⟩
        PRED (min (Succ x , Zero))                  ≡⟨ ap PRED (min-eq₃ (Succ x)) ⟩
        𝟙+ f (κ (Succ x , Succ y , Zero))           ∎
      φ (inr (x , refl)) (inr (y , refl)) (inr (z , refl)) =
        PRED (min (Succ x , min (Succ y , Succ z))) ≡⟨ ap (λ - → PRED (min (Succ x , -))) (min-eq₂ y z) ⟩
        PRED (min (Succ x , Succ (min (y , z))))    ≡⟨ ap PRED (min-eq₂ x (min (y , z))) ⟩
        𝟙+ f (κ (Succ x , Succ y , Succ z))         ∎
  g-homomorphism : is-homomorphism κ g
  g-homomorphism = dfunext fe₀ γ
   where
    γ : (z : ℕ∞ × ℕ∞ × ℕ∞) → PRED (g z) ≡ 𝟙+ g (κ z)
    γ (u , v , w) = φ (Zero+Succ fe₀ u) (Zero+Succ fe₀ v) (Zero+Succ fe₀ w)
     where
      φ : (u ≡ Zero) + (Σ x ꞉ ℕ∞ , u ≡ Succ x)
       → (v ≡ Zero) + (Σ y ꞉ ℕ∞ , v ≡ Succ y)
       → (w ≡ Zero) + (Σ z ꞉ ℕ∞ , w ≡ Succ z)
       → PRED (g (u , v , w)) ≡ 𝟙+ g (κ (u , v , w))
      φ (inl refl) _ _ = ap PRED (min-eq₀ (min (v , w)))
      φ (inr (x , refl)) (inl refl) _ =
        PRED (min (min (Succ x , Zero) , w))        ≡⟨ ap (λ - → PRED (min (- , w))) (min-eq₃ (Succ x)) ⟩
        PRED (min (Zero , w))                       ≡⟨ ap PRED (min-eq₀ w) ⟩
        PRED Zero                                   ≡⟨ refl ⟩
        𝟙+ g (κ (Succ x , Zero , w))                ∎
      φ (inr (x , refl)) (inr (y , refl)) (inl refl) =
        PRED (min (min (Succ x , Succ y) , Zero))   ≡⟨ ap PRED (min-eq₃ (min (Succ x , Succ y))) ⟩
        PRED Zero                                   ≡⟨ refl ⟩
        𝟙+ g (κ (Succ x , Succ y , Zero))           ∎
      φ (inr (x , refl)) (inr (y , refl)) (inr (z , refl)) =
        PRED (min (min (Succ x , Succ y) , Succ z)) ≡⟨ ap (λ - → PRED (min (- , Succ z))) (min-eq₂ x y) ⟩
        PRED (min (Succ (min (x , y)) , Succ z))    ≡⟨ ap PRED (min-eq₂ (min (x , y)) z) ⟩
        PRED (Succ (min (min (x , y) , z)))         ≡⟨ refl ⟩
        𝟙+ g (κ (Succ x , Succ y , Succ z))         ∎
  p : f ≡ g
  p = homomorphism-uniqueness κ f g f-homomorphism g-homomorphism

\end{code}

Thus, ℕ∞ equipped with (min , Zero, ∞) is a bounded semilattice with
bottom Zero and top ∞.

\begin{code}

min-is-bounded-semilattice :
   (∀ v     → min (Zero , v) ≡ Zero)
 × (∀ v     → min (∞ , v) ≡ v)
 × (∀ u     → min (u , u) ≡ u)
 × (∀ u v   → min (u , v) ≡ min (v , u))
 × (∀ u v w → min (u , min (v , w)) ≡ min (min (u , v) , w))
min-is-bounded-semilattice = min-eq₀ ,
                             min-unit ,
                             min-idempotent ,
                             min-commutative ,
                             min-associative

\end{code}

The following two facts invert the equations that characterize min:

\begin{code}

min-Zero : ∀ u v   → min (u , v) ≡ Zero → (u ≡ Zero) + (v ≡ Zero)
min-Succ : ∀ u v x → min (u , v) ≡ Succ x → (u ≡ Succ (Pred u))
                                          × (v ≡ Succ (Pred v))
                                          × (x ≡ min (Pred u , Pred v))

\end{code}

And here are their constructions:

\begin{code}

min-Zero u v r = h (Zero+Succ fe₀ u) (Zero+Succ fe₀ v)
 where
  h : (u ≡ Zero) + (Σ w ꞉ ℕ∞ , u ≡ Succ w) → (v ≡ Zero) + (Σ t ꞉ ℕ∞ , v ≡ Succ t) → _
  h (inl refl) _ = inl refl
  h (inr (w , refl)) (inl refl) = inr refl
  h (inr (w , refl)) (inr (t , refl)) = 𝟘-elim (Zero-not-Succ (r ⁻¹ ∙ min-eq₂ w t))


min-Succ u v x r = h (Zero+Succ fe₀ u) (Zero+Succ fe₀ v)
 where
  h : (u ≡ Zero) + (Σ w ꞉ ℕ∞ , u ≡ Succ w) → (v ≡ Zero) + (Σ t ꞉ ℕ∞ , v ≡ Succ t) → _
  h (inl refl) _ =
    𝟘-elim (Zero-not-Succ (Zero           ≡⟨ (min-eq₀ v)⁻¹ ⟩
                           min (Zero , v) ≡⟨ r ⟩
                           Succ x         ∎))
  h (inr (w , refl)) (inl refl) =
    𝟘-elim (Zero-not-Succ (Zero           ≡⟨ (min-eq₃ u)⁻¹ ⟩
                           min (u , v)    ≡⟨ r ⟩
                           Succ x         ∎))
  h (inr (w , refl)) (inr (t , refl)) = refl , refl ,
    Succ-lc (Succ x                       ≡⟨ r ⁻¹ ⟩
             min (Succ w , Succ t)        ≡⟨ min-eq₂ w t ⟩
             Succ (min (w , t))           ∎)

\end{code}

Relation of min with ≼ defined in the module GenericConvergentSequence.

\begin{code}

≼-min-l : (u v : ℕ∞) → min (u , v) ≼ u
≼-min-l u v zero p = γ
 where
  a : min (u , v) ≡ Succ (Pred (min (u , v)))
  a = positive-equal-Succ fe₀ (p ∶ zero ⊏ min (u , v))
  b : u ≡ Succ (Pred u)
  b = pr₁ (min-Succ u v (Pred (min (u , v))) a)
  γ : zero ⊏ u
  γ = ap (λ - → ι - zero) b
≼-min-l u v (succ n) p = γ
 where
  a : min (u , v) ≡ Succ (Pred (min (u , v)))
  a = positive-equal-Succ fe₀ (⊏-positive (succ n) (min (u , v)) p)
  b : (u ≡ Succ (Pred u))
    × (v ≡ Succ (Pred v))
    × (Pred (min (u , v)) ≡ min (Pred u , Pred v))
  b = min-Succ u v (Pred (min (u , v))) a
  q : n ⊏ Pred (min (u , v))
  q = p ∶ succ n ⊏ min (u , v)
  r : n ⊏ min (Pred u , Pred v)
  r = transport (λ - → n ⊏ -) (pr₂ (pr₂ b)) q
  IH : n ⊏ Pred u
  IH = ≼-min-l (Pred u) (Pred v) n r
  γ : succ n ⊏ u
  γ = IH

≼-min-r : (u v : ℕ∞) → min (u , v) ≼ v
≼-min-r u v n p = ≼-min-l v u n q
 where
  q : n ⊏ min (v , u)
  q = transport (λ - → n ⊏ -) (min-commutative u v) p

≼-from-min→ : (u v : ℕ∞) → min (u , v) ≡ u → u ≼ v
≼-from-min→ u v p = transport (λ - → - ≼ v) p (≼-min-r u v)

\end{code}
