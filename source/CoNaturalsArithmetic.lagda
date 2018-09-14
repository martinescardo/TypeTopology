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
function max in the module GenericconvergentSequence), but this module
serves as a good illustration of reasoning with the final coalgebra
property to both construct functions and prove their properties.

This file will grow on demand. The first operation we needed (for
codistances) is minimum.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-FunExt

module CoNaturalsArithmetic (fe : ∀ U V → funext U V) where

open import Two
open import GenericConvergentSequence
open import CoNaturals fe
open import UF-Base

fe₀ : funext U₀ U₀
fe₀ = fe U₀ U₀

\end{code}

We consider a 𝟙 + (-) coalgebra κ on ℕ∞ × ℕ∞ so that min is the unique
homomorphism to the final coalgebra PRED : ℕ∞ → 𝟙 + ℕ∞ on ℕ∞.

\begin{code}

private
 κ-min : ℕ∞ × ℕ∞ → 𝟙 {U₀} + ℕ∞ × ℕ∞
 κ-min (u , v) = 𝟚-Cases (positivity u)
                  (inl *)
                  (𝟚-Cases (positivity v)
                    (inl *)
                    (inr (Pred u , Pred v)))

min : ℕ∞ × ℕ∞ → ℕ∞
min = ℕ∞-corec κ-min

\end{code}

The defining equations of min thus are:

\begin{code}

min-eq₀ : ∀ v   → min (Zero , v) ≡ Zero
min-eq₁ : ∀ u   → min (Succ u , Zero) ≡ Zero
min-eq₂ : ∀ u v → min (Succ u , Succ v) ≡ Succ (min (u , v))

min-eq₀ = λ v   → Coalg-morphism-Zero κ-min (Zero , v) * refl
min-eq₁ = λ u   → Coalg-morphism-Zero κ-min (Succ u , Zero) * refl
min-eq₂ = λ u v → Coalg-morphism-Succ κ-min (Succ u , Succ v) (u , v) refl

\end{code}

Maximum (another version is defined in GenericConvergentSequence):

\begin{code}

private
 κ-max : ℕ∞ × ℕ∞ → 𝟙 {U₀} + ℕ∞ × ℕ∞
 κ-max (u , v) = 𝟚-Cases (positivity u)
                   (𝟚-Cases (positivity v)
                      (inl *)
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

max-eq₀ =         Coalg-morphism-Zero κ-max (Zero , Zero) * refl
max-eq₁ = λ v   → Coalg-morphism-Succ κ-max (Zero , Succ v) (Zero , v) refl
max-eq₂ = λ u   → Coalg-morphism-Succ κ-max (Succ u , Zero) (u , Zero) refl
max-eq₃ = λ u v → Coalg-morphism-Succ κ-max (Succ u , Succ v) (u , v) refl

\end{code}

We now prove properties of the minimum function using the
final-coalgebra property.

Using the equations min-eq₀ and min-eq₂, we have that the function λ u
→ min (u , u) is an algebra homomorphism from PRED to PRED and hence
is equal to the identity function:

\begin{code}

min-idempotent : ∀ u → min (u , u) ≡ u
min-idempotent u = ap (λ - → - u) h-is-corec
 where
  h : ℕ∞ → ℕ∞
  h u = min (u , u)
  h-homomorphism : is-homomorphism PRED h
  h-homomorphism = dfunext fe₀ (λ u → φ (Zero+Succ fe₀ u))
   where
    φ : {u : ℕ∞} → (u ≡ Zero) + (Σ \(w : ℕ∞) → u ≡ Succ w) → PRED (h u) ≡ 𝟙+ h (PRED u)
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
f (Succ w , Succ w) = Succ (f w) is idempotent, as would be the cases
of the maximum function)

Similarly, to prove that min is commutative, we show that the function
λ (u , v) → min (v , u) satisfies the same "defining equations" as the
function min.

The following equation is derived from the above equations min-eq₀ and
min-eq₁ by cases on whether u is Zero or a Succ(Pred u).

\begin{code}

eq₃-from-eq₀-and-eq₁ : (h : ℕ∞ × ℕ∞ → ℕ∞)
                    → (∀ v → h (Zero , v) ≡ Zero)
                    → (∀ u → h (Succ u , Zero) ≡ Zero)
                    → (∀ u → h (u , Zero) ≡ Zero)
eq₃-from-eq₀-and-eq₁ h eq₀ eq₁ u = γ (Zero+Succ fe₀ u)
 where
  γ : (u ≡ Zero) + (Σ \(w : ℕ∞) → u ≡ Succ w) → h (u , Zero) ≡ Zero
  γ (inl refl)       = h (Zero , Zero)   ≡⟨ eq₀ Zero ⟩ Zero ∎
  γ (inr (w , refl)) = h (Succ w , Zero) ≡⟨ eq₁ w ⟩    Zero ∎

min-eq₃ : ∀ u → min (u , Zero) ≡ Zero
min-eq₃ = eq₃-from-eq₀-and-eq₁ min min-eq₀ min-eq₁

\end{code}

Conversely, if a function satisfies the above equations, then it is a
coalgebra homomorphism and hence is equal to ℕ∞-corec κ-min.

\begin{code}

equations-characterize-homomorphisms :
    (h : ℕ∞ × ℕ∞ → ℕ∞)
  → (∀ v   → h (Zero , v) ≡ Zero)
  → (∀ u   → h (Succ u , Zero) ≡ Zero)
  → (∀ u v → h (Succ u , Succ v) ≡ Succ (h (u , v)))
  → is-homomorphism κ-min h
equations-characterize-homomorphisms h eq₀ eq₁ eq₂ = dfunext fe₀ γ
  where
   γ : (w : ℕ∞ × ℕ∞) → PRED (h w) ≡ 𝟙+ h (κ-min w)
   γ (u , v) = φ (Zero+Succ fe₀ u) (Zero+Succ fe₀ v)
    where
     φ : (u ≡ Zero) + (Σ \(w : ℕ∞) → u ≡ Succ w)
       → (v ≡ Zero) + (Σ \(t : ℕ∞) → v ≡ Succ t)
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

To prove that min is commutative, we show that the following function
h is also a coalgebra homomorphism and hence equal to ℕ∞-corec p:

\begin{code}

min-commutative : ∀ u v → min (u , v) ≡ min (v , u)
min-commutative u v = h (v , u)               ≡⟨ ap (λ - → - (v , u)) h-is-corec ⟩
                      ℕ∞-corec κ-min (v , u) ∎
 where
  h : ℕ∞ × ℕ∞ → ℕ∞
  h (u , v) = min (v , u)
  h-homomorphism : is-homomorphism κ-min h
  h-homomorphism = equations-characterize-homomorphisms h h-eq₀ h-eq₁ h-eq₂
   where
    h-eq₀ : (v : ℕ∞) → min (v , Zero) ≡ Zero
    h-eq₀ v = min-eq₃ v
    h-eq₁ : (u : ℕ∞) → min (Zero , Succ u) ≡ Zero
    h-eq₁ u = min-eq₀ (Succ u)
    h-eq₂ : (u v : ℕ∞) → min (Succ v , Succ u) ≡ Succ (min (v , u))
    h-eq₂ u v = min-eq₂ v u
  h-is-corec : h ≡ ℕ∞-corec κ-min
  h-is-corec = homomorphism-uniqueness κ-min h (ℕ∞-corec κ-min)
                h-homomorphism (ℕ∞-corec-homomorphism κ-min)

\end{code}

Similarly, to prove that min is associative, we show that the two functions

   λ (u , v , w) → min (u , min (v , w))
   λ (u , v , w) → min (min (u , v) , w)

are homormorphisms from the same coalgebra on ℕ∞ × ℕ∞ × ℕ∞ to the
final coalgebra PRED.

\begin{code}

min-assoc : (u v w : ℕ∞) → min (u , min (v , w)) ≡ min (min (u , v) , w)
min-assoc u v w = ap (λ - → - (u , v , w)) p
 where
  f g : ℕ∞ × ℕ∞ × ℕ∞ → ℕ∞
  f (u , v , w) = min (u , min (v , w))
  g (u , v , w) = min (min (u , v) , w)
  k : ℕ∞ × ℕ∞ × ℕ∞ → 𝟙 + ℕ∞ × ℕ∞ × ℕ∞
  k (u , v , w) = 𝟚-Cases (positivity u)
                   (inl *)
                   (𝟚-Cases (positivity v)
                     (inl *)
                     (𝟚-Cases (positivity w)
                       (inl *)
                       (inr (Pred u , Pred v , Pred w))))
  f-homomorphism : is-homomorphism k f
  f-homomorphism = dfunext fe₀ γ
   where
    γ : (z : ℕ∞ × ℕ∞ × ℕ∞) → PRED (f z) ≡ 𝟙+ f (k z)
    γ (u , v , w) = φ (Zero+Succ fe₀ u) (Zero+Succ fe₀ v) (Zero+Succ fe₀ w)
     where
      φ : (u ≡ Zero) + (Σ \(x : ℕ∞) → u ≡ Succ x)
       → (v ≡ Zero) + (Σ \(y : ℕ∞) → v ≡ Succ y)
       → (w ≡ Zero) + (Σ \(z : ℕ∞) → w ≡ Succ z)
       → PRED (f (u , v , w)) ≡ 𝟙+ f (k (u , v , w))
      φ (inl refl) _ _ = ap PRED (min-eq₀ (min (v , w)))
      φ (inr (x , refl)) (inl refl) _ =
        PRED (min (Succ x , min (Zero , w))) ≡⟨ ap (λ - → PRED (min (Succ x , -))) (min-eq₀ w) ⟩
        PRED (min (Succ x , Zero))           ≡⟨ ap PRED (min-eq₃ u) ⟩
        PRED Zero                            ≡⟨ ap PRED (min-eq₃ u) ⟩
        𝟙+ f (k (Succ x , Zero , w))         ∎
      φ (inr (x , refl)) (inr (y , refl)) (inl refl) =
        PRED (min (Succ x , min (Succ y , Zero))) ≡⟨ ap (λ - → PRED (min (Succ x , -))) (min-eq₃ (Succ y)) ⟩
        PRED (min (Succ x , Zero))                ≡⟨ ap PRED (min-eq₃ (Succ x)) ⟩
        𝟙+ f (k (Succ x , Succ y , Zero))         ∎
      φ (inr (x , refl)) (inr (y , refl)) (inr (z , refl)) =
        PRED (min (Succ x , min (Succ y , Succ z))) ≡⟨ ap (λ - → PRED (min (Succ x , -))) (min-eq₂ y z) ⟩
        PRED (min (Succ x , Succ (min (y , z))))    ≡⟨ ap PRED (min-eq₂ x (min (y , z))) ⟩
        𝟙+ f (k (Succ x , Succ y , Succ z))         ∎
  g-homomorphism : is-homomorphism k g
  g-homomorphism = dfunext fe₀ γ
   where
    γ : (z : ℕ∞ × ℕ∞ × ℕ∞) → PRED (g z) ≡ 𝟙+ g (k z)
    γ (u , v , w) = φ (Zero+Succ fe₀ u) (Zero+Succ fe₀ v) (Zero+Succ fe₀ w)
     where
      φ : (u ≡ Zero) + (Σ \(x : ℕ∞) → u ≡ Succ x)
       → (v ≡ Zero) + (Σ \(y : ℕ∞) → v ≡ Succ y)
       → (w ≡ Zero) + (Σ \(z : ℕ∞) → w ≡ Succ z)
       → PRED (g (u , v , w)) ≡ 𝟙+ g (k (u , v , w))
      φ (inl refl) _ _ = ap PRED (min-eq₀ (min (v , w)))
      φ (inr (x , refl)) (inl refl) _ =
        PRED (min (min (Succ x , Zero) , w)) ≡⟨ ap (λ - → PRED (min (- , w))) (min-eq₃ (Succ x)) ⟩
        PRED (min (Zero , w)) ≡⟨ ap PRED (min-eq₀ w) ⟩
        PRED Zero ≡⟨ refl ⟩
        𝟙+ g (k (Succ x , Zero , w)) ∎
      φ (inr (x , refl)) (inr (y , refl)) (inl refl) =
        PRED (min (min (Succ x , Succ y) , Zero)) ≡⟨ ap PRED (min-eq₃ (min (Succ x , Succ y))) ⟩
        PRED Zero ≡⟨ refl ⟩
        𝟙+ g (k (Succ x , Succ y , Zero)) ∎
      φ (inr (x , refl)) (inr (y , refl)) (inr (z , refl)) =
        PRED (min (min (Succ x , Succ y) , Succ z)) ≡⟨ ap (λ - → PRED (min (- , Succ z))) (min-eq₂ x y) ⟩
        PRED (min (Succ (min (x , y)) , Succ z)) ≡⟨ ap PRED (min-eq₂ (min (x , y)) z) ⟩
        PRED (Succ (min (min (x , y) , z))) ≡⟨ refl ⟩
        𝟙+ g (k (Succ x , Succ y , Succ z)) ∎
  p : f ≡ g
  p = homomorphism-uniqueness k f g f-homomorphism g-homomorphism

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
  h : (u ≡ Zero) + (Σ \(w : ℕ∞) → u ≡ Succ w) → (v ≡ Zero) + (Σ \(t : ℕ∞) → v ≡ Succ t) → _
  h (inl refl) _ = inl refl
  h (inr (w , refl)) (inl refl) = inr refl
  h (inr (w , refl)) (inr (t , refl)) = 𝟘-elim (Zero-not-Succ (r ⁻¹ ∙ min-eq₂ w t))


min-Succ u v x r = h (Zero+Succ fe₀ u) (Zero+Succ fe₀ v)
 where
  h : (u ≡ Zero) + (Σ \(w : ℕ∞) → u ≡ Succ w) → (v ≡ Zero) + (Σ \(t : ℕ∞) → v ≡ Succ t) → _
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

Relation of min with ≼.

\begin{code}

{-
min-≼-l : (u v : ℕ∞) → min (u , v) ≼ u
min-≼-l u = γ (Zero-or-Succ fe₀ u)
 where
  γ : (u ≡ Zero) + (u ≡ Succ (Pred u)) → (v : ℕ∞) → min (u , v) ≼ u
  γ (inl refl) v n p = transport (λ - → n ⊏ -) (min-eq₀ v) p
  γ (inr q) v zero p = ap positivity q
  γ (inr q) v (succ n) p = φ (Zero-or-Succ fe₀ v)
   where
    φ : (v ≡ Zero) + (v ≡ Succ (Pred v)) → incl u (succ n) ≡ ₁
    φ (inl refl) = 𝟘-elim (zero-is-not-one t)
     where
      t : ₀ ≡ ₁
      t = transport (λ - → incl - (succ n) ≡ ₁) (min-eq₃ u) p
    φ (inr r) = {!!}
     where
      IH : {!!}
      IH = {!!}

min-glb : (u v w : ℕ∞) → u ≼ v → u ≼ w → u ≼ min (v , w)
min-glb u v w = {!!}
-}

\end{code}
