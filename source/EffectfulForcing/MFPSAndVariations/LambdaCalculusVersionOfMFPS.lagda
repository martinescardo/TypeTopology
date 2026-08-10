Martin Escardo 22-24 May 2013

The MFPS paper https://doi.org/10.1016/j.entcs.2013.09.010 worked with
the combinatory version of system T. Here we work with the
lambda-calculus version. Moreover, the original version has the
iteration combinator, while here we work with the primitive recursion
combinator for system T.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module EffectfulForcing.MFPSAndVariations.LambdaCalculusVersionOfMFPS where

open import MLTT.Spartan hiding (rec ; _^_) renaming (⋆ to 〈〉)
open import MLTT.Fin
open import EffectfulForcing.MFPSAndVariations.Combinators
open import EffectfulForcing.MFPSAndVariations.Continuity
open import EffectfulForcing.MFPSAndVariations.Dialogue
open import EffectfulForcing.MFPSAndVariations.SystemT

\end{code}

Auxiliary interpretation of types:

\begin{code}

B〖_〗 : type → 𝓤₀ ̇
B〖 ι 〗     = B ℕ
B〖 σ ⇒ τ 〗 = B〖 σ 〗 → B〖 τ 〗

\end{code}

Generalized Kleisli extension (as in the original treatment):

\begin{code}

Kleisli-extension : {X : 𝓤₀ ̇ } {σ : type} → (X → B〖 σ 〗) → B X → B〖 σ 〗
Kleisli-extension {X} {ι}     = kleisli-extension
Kleisli-extension {X} {σ ⇒ τ} = λ g d s → Kleisli-extension {X} {τ} (λ x → g x s) d

\end{code}

The interpretation of the system T constants (again as in the original
development):

\begin{code}

zero' : B ℕ
zero' = η 0

succ' : B ℕ → B ℕ
succ' = B-functor succ

rec' : {σ : type} → (B ℕ → B〖 σ 〗 → B〖 σ 〗) → B〖 σ 〗 → B ℕ → B〖 σ 〗
rec' f x = Kleisli-extension(rec (f ∘ η) x)

\end{code}

The auxiliary interpretation of contexts (which were not present in
the original development):

\begin{code}

B【_】 : {n : ℕ} (Γ : Cxt n) → 𝓤₀ ̇
B【 Γ 】 = (i : Fin _) → B〖 (Γ [ i ]) 〗

⟪⟫ : B【 〈〉 】
⟪⟫ ()

_‚‚_ : {n : ℕ} {Γ : Cxt n} {σ : type} → B【 Γ 】 → B〖 σ 〗 → B【 Γ , σ 】
(xs ‚‚ x) 𝟎       = x
(xs ‚‚ x) (suc i) = xs i

infixl 6 _‚‚_

\end{code}

The auxiliary interpretation of system TΩ terms:

\begin{code}

B⟦_⟧ : {n : ℕ} {Γ : Cxt n} {σ : type} → T' Γ σ → B【 Γ 】 → B〖 σ 〗
B⟦ Ω     ⟧  _ = generic
B⟦ Zero  ⟧  _ = zero'
B⟦ Succ  ⟧  _ = succ'
B⟦ Rec   ⟧  _ = rec'
B⟦ ν i   ⟧ xs = xs i
B⟦ ƛ t   ⟧ xs = λ x → B⟦ t ⟧ (xs ‚‚ x)
B⟦ t · u ⟧ xs = (B⟦ t ⟧ xs) (B⟦ u ⟧ xs)

\end{code}

The dialogue tree of a closed term of type ((ι ⇒ ι) ⇒ ι):

\begin{code}

dialogue-tree : T₀ ((ι ⇒ ι) ⇒ ι) → B ℕ
dialogue-tree t = B⟦ embed t · Ω ⟧ ⟪⟫

\end{code}

The logical relation is the same as in the original development:

\begin{code}

R : {σ : type} → (Baire → 〖 σ 〗) → B〖 σ 〗 → 𝓤₀ ̇
R {ι}     n n' = (α : Baire) → n α ＝ decode α n'
R {σ ⇒ τ} f f' = (x  : Baire → 〖 σ 〗)
                 (x' : B〖 σ 〗)
               → R {σ} x x'
               → R {τ} (λ α → f α (x α)) (f' x')
\end{code}

The following lemma is again the same as in the original development,
by induction on types:

\begin{code}

R-kleisli-lemma : (σ : type)
                  (g  : ℕ → Baire → 〖 σ 〗)
                  (g' : ℕ → B〖 σ 〗)
                → ((k : ℕ) → R (g k) (g' k))
                → (n  : Baire → ℕ)
                  (n' : B ℕ)
                → R n n'
                → R (λ α → g (n α) α) (Kleisli-extension g' n')

R-kleisli-lemma ι g g' rg n n' rn = λ α →
 g (n α) α                          ＝⟨ rg (n α) α ⟩
 decode α (g' (n α))                ＝⟨ ap (λ k → decode α (g' k)) (rn α) ⟩
 decode α (g' (decode α n'))        ＝⟨ decode-kleisli-extension g' n' α ⟩
 decode α (kleisli-extension g' n') ∎

R-kleisli-lemma (σ ⇒ τ) g g' rg n n' rn =
 λ y y' ry → R-kleisli-lemma
              τ
              (λ k α → g k α (y α))
              (λ k → g' k y')
              (λ k → rg k y y' ry)
              n
              n'
              rn
\end{code}

The main lemma is a modification of the main lemma in the original
development, still by induction on terms. We don't have cases for the
combinators K and S anymore, but we need to add two cases for ν and ƛ,
and we need to modify the case for application _·_, which becomes more
difficult (in a routine way).  Additionally, we first need to extend R
to contexts (in the obvious way):

\begin{code}

Rs : {n : ℕ} {Γ : Cxt n} → (Baire → 【 Γ 】) → B【 Γ 】 → 𝓤₀ ̇
Rs {n} {Γ} xs ys = (i : Fin n) → R {Γ [ i ]} (λ α → xs α i) (ys i)

main-lemma : {n : ℕ} {Γ : Cxt n}
             {σ : type}
             (t : T' Γ σ)
             (xs : Baire → 【 Γ 】)
             (ys : B【 Γ 】)
           → Rs xs ys
           → R (λ α → ⟦ t ⟧' α (xs α)) (B⟦ t ⟧ ys)

main-lemma Ω xs ys cr = λ n n' rn α →
 α (n α)               ＝⟨ ap α (rn α) ⟩
 α (decode α n')       ＝⟨ generic-diagram α n' ⟩
 decode α (generic n') ∎

main-lemma Zero xs ys cr = λ α → refl

main-lemma Succ xs ys cr = λ n n' rn α  →
 succ (n α)          ＝⟨ ap succ (rn α) ⟩
 succ (decode α n')  ＝⟨ decode-α-is-natural succ n' α ⟩
 decode α (succ' n') ∎

main-lemma (Rec {_} {_} {σ}) _ _ _ = lemma
 where
  lemma : (f  : Baire → ℕ → 〖 σ 〗 → 〖 σ 〗)
          (f' : B ℕ → B〖 σ 〗 → B〖 σ 〗)
        → R {ι ⇒ σ ⇒ σ} f f'
        → (x  : Baire → 〖 σ 〗)
          (x' : B〖 σ 〗)
        → R {σ} x x'
        → (n  : Baire → ℕ)
          (n' : B ℕ) → R {ι} n n'
        → R {σ} (λ α → rec (f α) (x α) (n α))
                (Kleisli-extension(rec (f' ∘ η) x') n')
  lemma f f' rf x x' rx = R-kleisli-lemma σ g g' rg
   where
    g : ℕ → Baire → 〖 σ 〗
    g k α = rec (f α) (x α) k

    g' : ℕ → B〖 σ 〗
    g' k = rec (f' ∘ η) x' k

    rg : (k : ℕ) → R (g k) (g' k)
    rg 0        = rx
    rg (succ k) = rf (λ α → k) (η k) (λ α → refl) (g k) (g' k) (rg k)

main-lemma (ν i) xs ys cr = cr i

main-lemma {n} {Γ} {σ ⇒ τ} (ƛ t) xs ys cr = IH
 where
  IH : (x : Baire → 〖 σ 〗)
       (y : B〖 σ 〗)
      → R x y
      → R (λ α → ⟦ t ⟧' α (xs α ‚ x α)) (B⟦ t ⟧ (ys ‚‚ y))
  IH x y r = main-lemma t (λ α → xs α ‚ x α) (ys ‚‚ y) h
    where
     h : (i : Fin (succ n)) → R (λ α → (xs α ‚ x α) i) ((ys ‚‚ y) i)
     h 𝟎       = r
     h (suc i) = cr i

main-lemma (t · u) xs ys cr = IH-t (λ α → ⟦ u ⟧' α (xs α)) (B⟦ u ⟧ ys) IH-u
 where
  IH-t : (x  : Baire → 〖 _ 〗)
         (x' : B〖 _ 〗)
       → R x x'
       → R (λ α → ⟦ t ⟧' α (xs α) (x α))
           (B⟦ t ⟧ ys x')
  IH-t = main-lemma t xs ys cr

  IH-u : R (λ α → ⟦ u ⟧' α (xs α)) (B⟦ u ⟧ ys)
  IH-u = main-lemma u xs ys cr

\end{code}

Of course, all we are interested in is the ground case of the
main-lemma for closed terms, but we needed to prove the general case
to get that, using a logical relation to have a suitable induction
hypothesis, as usual.

\begin{code}

main-closed-ground : (t : T' 〈〉 ι) (α : Baire)
                   → ⟦ t ⟧' α ⟨⟩ ＝ decode α (B⟦ t ⟧ ⟪⟫)
main-closed-ground t = main-lemma t (λ α → ⟨⟩) ⟪⟫ (λ())

\end{code}

Then the correctness of the dialogue-tree function follows directly:

\begin{code}

dialogue-tree-correct : (t : T₀ ((ι ⇒ ι) ⇒ ι))
                        (α : Baire)
                      → ⟦ t ⟧₀ α ＝ decode α (dialogue-tree t)
dialogue-tree-correct t α =
 ⟦ t ⟧₀ α                       ＝⟨ ap (λ f → f ⟨⟩ α) (preservation t α) ⟩
 ⟦ embed t ⟧' α ⟨⟩ α            ＝⟨ main-closed-ground (embed t · Ω) α ⟩
 decode α (B⟦ embed t · Ω ⟧ ⟪⟫) ＝⟨refl⟩
 decode α (dialogue-tree t)     ∎

\end{code}

And the main theorem follows directly from this:

\begin{code}

eloquence-theorem : (f : Baire → ℕ)
                  → T-definable f
                  → eloquent f
eloquence-theorem f (t , r) =
 (dialogue-tree t ,
  λ α → dialogue (dialogue-tree t) α ＝⟨ (dialogue-tree-correct t α)⁻¹ ⟩
        ⟦ t ⟧₀ α                     ＝⟨ ap (λ - → - α) r ⟩
        f α                          ∎)

eloquence-corollary₀ : (f : Baire → ℕ)
                     → T-definable f
                     → is-continuous f
eloquence-corollary₀ f d = eloquent-functions-are-continuous
                            f
                            (eloquence-theorem f d)

eloquence-corollary₁ : (f : Baire → ℕ)
                     → T-definable f
                     → is-uniformly-continuous (C-restriction f)
eloquence-corollary₁ f d = eloquent-functions-are-UC
                            (C-restriction f)
                            (restriction-is-eloquent f
                            (eloquence-theorem f d))
\end{code}

Examples:

\begin{code}

module examples where

 open import MLTT.Athenian using (List)
 open List

 max : ℕ → ℕ → ℕ
 max 0        y        = y
 max (succ x) 0        = succ x
 max (succ x) (succ y) = succ (max x y)

 mod : List ℕ → ℕ
 mod []      = 0
 mod (x ∷ s) = max (succ x) (mod s)

 mod-cont : T₀ ((ι ⇒ ι) ⇒ ι) → Baire → ℕ
 mod-cont t α = mod (pr₁ (eloquence-corollary₀ ⟦ t ⟧₀ (t , refl) α))

 m₁ : (ℕ → ℕ) → ℕ
 m₁ = mod-cont (ƛ (ν₀ · numeral 17))

 m₁-explicitly : m₁ ＝ λ x → 18
 m₁-explicitly = refl

 example₁ : m₁ id ＝ 18
 example₁ = refl

 example₁' : m₁ (λ i → 0) ＝ 18
 example₁' = refl

 m₂ : (ℕ → ℕ) → ℕ
 m₂ = mod-cont (ƛ (ν₀ · (ν₀ · numeral 17)))

 m₂-explicitly : m₂ ＝ λ α → succ (max 17 (α 17))
 m₂-explicitly = refl

 example₂ : m₂ succ ＝ 19
 example₂ = refl

 example₂' : m₂ (λ i → 0) ＝ 18
 example₂' = refl

 example₂'' : m₂ id ＝ 18
 example₂'' = refl

 example₂''' : m₂ (succ ∘ succ) ＝ 20
 example₂''' = refl


 Add : {n : ℕ} {Γ : Cxt n} → T Γ (ι ⇒ ι ⇒ ι)
 Add = Rec · (ƛ Succ)

 t₃ : T₀ ((ι ⇒ ι) ⇒ ι)
 t₃ = ƛ (ν₀ · (ν₀ · (Add · (ν₀ · numeral 17) · (ν₀ · numeral 34))))

 add : ℕ → ℕ → ℕ
 add = rec (λ _ → succ)

 t₃-meaning : ⟦ t₃ ⟧₀ ＝ λ α → α (α (add (α 17) (α 34)))
 t₃-meaning = refl

 m₃ : (ℕ → ℕ) → ℕ
 m₃ = mod-cont t₃

 example₃ : m₃ succ ＝ 55
 example₃ = refl

 example₃' : m₃ id ＝ 52
 example₃' = refl

 example₃'' : m₃ (λ i → 0) ＝ 35
 example₃'' = refl

 example₃''' : m₃ (λ i → 300) ＝ 601
 example₃''' = refl

 example₃'''' : m₃ (λ i → add i i) ＝ 205
 example₃'''' = refl

 f : T₀ ((ι ⇒ ι) ⇒ ι)
 f = ƛ (ν₀ · (ν₀ · (ν₀ · numeral 17)))

 m₄ : (ℕ → ℕ) → ℕ
 m₄ = mod-cont f

 example₄ : m₄ id ＝ 18
 example₄ = refl

 example₄' : m₄ (λ i → 0) ＝ 18
 example₄' = refl

 example₄'' : m₄ succ ＝ 20
 example₄'' = refl

 example₄''' : m₄ (λ i → add i i) ＝ 69
 example₄''' = refl

 example₄'''' : ⟦ f ⟧₀ (λ i → add i i) ＝ 136
 example₄'''' = refl

\end{code}
