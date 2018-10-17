Martin Escardo, 5th September 2018.

On Lawvere's Fixed Point Theorem (LFPT).

 * http://tac.mta.ca/tac/reprints/articles/15/tr15abs.html
 * https://ncatlab.org/nlab/show/Lawvere%27s+fixed+point+theorem
 * http://arxiv.org/abs/math/0305282

We give an application to Cantor's theorem for the universe.

We begin with split surjections, or retractions, because they can be
formulated in MLTT, and then move to surjections, which need further
extensions of MLTT, or hypotheses, such as propositional truncation.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module LawvereFPT where

open import SpartanMLTT

\end{code}

The following pointwise weakening of split surjection is sufficient to
prove LFPT and allows us to avoid function extensionality in its
applications:

\begin{code}

open import UF-Retracts
open import UF-Equiv
open import UF-Miscelanea
open import UF-FunExt
open import Two

module retract-version where

\end{code}

We will use the decoration "·" for pointwise versions of notions and
constructions (for example, we can read "has-section· r" as saying
that r has a pointwise section).

\begin{code}

 has-section· : ∀ {U V} {A : U ̇} {X : V ̇} → (A → (A → X)) → U ⊔ V ̇
 has-section· r = Σ \(s : cod r → dom r) → ∀ g a → r (s g) a ≡ g a

 section-gives-section· : ∀ {U V} {A : U ̇} {X : V ̇} (r : A → (A → X))
                        → has-section r → has-section· r
 section-gives-section· r (s , rs) = s , λ g a → ap (λ - → - a) (rs g)

 section·-gives-section : ∀ {U V} {A : U ̇} {X : V ̇} (r : A → (A → X))
                        → funext U V
                        → has-section· r → has-section r
 section·-gives-section r fe (s , rs·) = s , λ g → dfunext fe (rs· g)

 LFPT· : ∀ {U V} {A : U ̇} {X : V ̇} (r : A → (A → X))
       → has-section· r
       → (f : X → X) → Σ \(x : X) → x ≡ f x
 LFPT· {U} {V} {A} {X} r (s , rs) f = x , p
  where
   g : A → X
   g a = f (r a a)
   a : A
   a = s g
   x : X
   x = r a a
   p : x ≡ f x
   p = x         ≡⟨ refl ⟩
       r (s g) a ≡⟨ rs g a ⟩
       g a       ≡⟨ refl ⟩
       f x       ∎

 LFPT : ∀ {U V} {A : U ̇} {X : V ̇}
      → retract (A → X) of A
      → (f : X → X) → Σ \(x : X) → x ≡ f x
 LFPT (r , h) = LFPT· r (section-gives-section· r h)

 LFPT-≃ : ∀ {U V} {A : U ⊔ V ̇} {X : U ̇}
        → A ≃ (A → X)
        → (f : X → X) → Σ \(x : X) → x ≡ f x
 LFPT-≃ p = LFPT (equiv-retract-r p)

 LFPT-≡ : ∀ {U V} {A : U ⊔ V ̇} {X : U ̇}
        → A ≡ (A → X)
        → (f : X → X) → Σ \(x : X) → x ≡ f x
 LFPT-≡ p = LFPT (Id-retract-r p)

 \end{code}

As a simple application, it follows that negation doesn't have fixed points:

 \begin{code}

 ¬-no-fp : ∀ {U} → ¬ Σ \(X : U ̇) → X ≡ ¬ X
 ¬-no-fp {U} (X , p) = pr₁(γ id)
  where
   γ : (f : 𝟘 → 𝟘) → Σ \(x : 𝟘) → x ≡ f x
   γ = LFPT-≡ p

 \end{code}

 We apply LFPT twice to get the following: first every function
 U ̇ → U ̇ has a fixed point, from which for any type X we get a type B
 with B ≡ (B → X), and hence with (B → X) a retract of B, for which we
 apply LFPT again to get that every X → X has a fixed point.

 \begin{code}

 cantor-theorem-for-universes :
     (U V : Universe) (A : V ̇) (r : A → (A → U ̇))
   → has-section· r
   → (X : U ̇) (f : X → X) → Σ \(x : X) → x ≡ f x
 cantor-theorem-for-universes U V A r h X = LFPT-≡ {U} {U} p
  where
   B : U ̇
   B = pr₁(LFPT· r h (λ B → B → X))
   p : B ≡ (B → X)
   p = pr₂(LFPT· r h (λ B → B → X))

 \end{code}

 Taking X to be 𝟘 we get a contradiction, i.e. an inhabitant of the
 empty type 𝟘 (in fact, we get an inhabitant of any type by considering
 the identity function):

 \begin{code}

 Cantor-theorem-for-universes :
     (U V : Universe) (A : V ̇)
   → (r : A → (A → U ̇)) → ¬(has-section· r)
 Cantor-theorem-for-universes U V A r h = 𝟘-elim(pr₁ (cantor-theorem-for-universes U V A r h 𝟘 id))

 \end{code}

 The original version of Cantor's theorem was for powersets, which
 here are types of maps into the subtype classifier Ω U of the universe U.

 Function extensionality is needed in order to define negation
 Ω U → Ω U, to show that P → 𝟘 is a proposition.

 \begin{code}

 open import UF-Subsingletons
 open import UF-Subsingletons-FunExt

 not-no-fp : ∀ {U} (fe : funext U U₀) → ¬ Σ \(P : Ω U) → P ≡ not fe P
 not-no-fp {U} fe (P , p) = ¬-no-fp (P holds , q)
  where
   q : P holds ≡ ¬(P holds)
   q = ap _holds p

 cantor-theorem : (U V : Universe) (A : V ̇)
                → funext U U₀ → (r : A → (A → Ω U)) → ¬(has-section· r)
 cantor-theorem U V A fe r (s , rs) = not-no-fp fe not-fp
  where
   not-fp : Σ \(B : Ω U) → B ≡ not fe B
   not-fp = LFPT· r (s , rs) (not fe)

\end{code}

The original LFPT has surjection, rather than retraction, as an
assumption. The retraction version can be formulated and proved in
pure MLTT. To formulate the original version we consider MLTT extended
with propositional truncation, or rather just MLTT with propositional
truncation as an assumption, given as a parameter for the following
module. This time a pointwise weakening of surjection is not enough.

\begin{code}

open import UF-PropTrunc
open import UF-ImageAndSurjection

module surjection-version (pt : PropTrunc) where

 open PropositionalTruncation pt
 open ImageAndSurjection pt

 LFPT : ∀ {U V} {A : U ̇} {X : V ̇} (φ : A → (A → X))
      → is-surjection φ
      → (f : X → X) → ∃ \(x : X) → x ≡ f x
 LFPT {U} {V} {A} {X} φ s f = ptfunct γ e
  where
   g : A → X
   g a = f (φ a a)
   e : ∃ \(a : A) → φ a ≡ g
   e = s g
   γ : (Σ \(a : A) → φ a ≡ g) → Σ \(x : X) → x ≡ f x
   γ (a , q) = x , p
    where
     x : X
     x = φ a a
     p : x ≡ f x
     p = x         ≡⟨ refl ⟩
         φ a a     ≡⟨ ap (λ - → - a) q ⟩
         g a       ≡⟨ refl ⟩
         f x       ∎

\end{code}

 So in this version of LFPT we have a weaker hypothesis for the
 theorem, but we need a stronger language to formulate and prove it,
 or else an additional hypothesis of the existence of propositional
 truncations.

 For the following theorem, we use both the surjection version and the
 retraction version of LFPT.

\begin{code}

 cantor-theorem-for-universes :
     (U V : Universe) (A : V ̇) (φ : A → (A → U ̇))
   → is-surjection φ
   → (X : U ̇) (f : X → X) → ∃ \(x : X) → x ≡ f x
 cantor-theorem-for-universes U V A φ s X f = ptfunct g t
  where
   t : ∃ \(B : U ̇) → B ≡ (B → X)
   t = LFPT φ s (λ B → B → X)
   g : (Σ \(B : U ̇) → B ≡ (B → X)) → Σ \(x : X) → x ≡ f x
   g (B , p) = retract-version.LFPT-≡ {U} {U} p f

 Cantor-theorem-for-universes :
     (U V : Universe) (A : V ̇)
   → (φ : A → (A → U ̇)) → ¬(is-surjection φ)
 Cantor-theorem-for-universes U V A r h = 𝟘-elim(ptrec 𝟘-is-prop pr₁ c)
  where
   c : ∃ \(x : 𝟘) → x ≡ x
   c = cantor-theorem-for-universes U V A r h 𝟘 id

 cantor-theorem :
     (U V : Universe) (A : V ̇)
   → funext U U₀ → (φ : A → (A → Ω U)) → ¬(is-surjection φ)
 cantor-theorem U V A fe φ s = ptrec 𝟘-is-prop (retract-version.not-no-fp fe) t
  where
   t : ∃ \(B : Ω U) → B ≡ not fe B
   t = LFPT φ s (not fe)

 \end{code}

 Another corollary is that the Cantor type (ℕ → 𝟚) and the Baire type
 (ℕ → ℕ) are uncountable:

 \begin{code}

 open import Two

 cantor-uncountable : ¬ Σ \(φ : ℕ → (ℕ → 𝟚)) → is-surjection φ
 cantor-uncountable (φ , s) = ptrec 𝟘-is-prop (uncurry complement-no-fp) t
  where
   t : ∃ \(n : 𝟚) → n ≡ complement n
   t = LFPT φ s complement

 baire-uncountable : ¬ Σ \(φ : ℕ → (ℕ → ℕ)) → is-surjection φ
 baire-uncountable (φ , s) = ptrec 𝟘-is-prop (uncurry succ-no-fp) t
  where
   t : ∃ \(n : ℕ) → n ≡ succ n
   t = LFPT φ s succ

\end{code}

I asked Ingo Blechschmidt whether he could prove that the universe is
uncountable, and he could (ask him for a proof).

Added 12 October 2018. The paper

 Thierry Coquand, The paradox of trees in type theory
 BIT Numerical Mathematics, March 1992, Volume 32, Issue 1, pp 10–14
 https://pdfs.semanticscholar.org/f2f3/30b27f1d7ca99c2550f96581a4400c209ef8.pdf

shows that U ̇ : U ̇ (aka type-in-type) is inconsistent if U is closed
under W types.

We adapt this method of proof to show that there is no type 𝕌 : U ̇
with U ̇ ≃ 𝕌, without assuming type-in-type.

The construction works in MLTT with empty type 𝟘, identity types, Σ
types, Π types, W types and a universe U closed under them. In
particular, extensionality and univalence are not needed. We again use
Lawvere's fixed point theorem.

NB. It should also be possible to replace the diagonal construction of
Lemma₀ by a second application of LFPT (todo).

\begin{code}

module Coquand where

 Lemma₀ : (U : Universe)
          (A : U ̇)
          (T : A → U ̇)
          (S : U ̇ → A)
          (ρ : {X : U ̇} → T (S X) → X)
          (σ : {X : U ̇} → X → T (S X))
          (η : {X : U ̇} (x : X) → ρ (σ x) ≡ x)
        → 𝟘
 Lemma₀ U A T S ρ σ η = pr₁ (γ 𝟘 id )
  where
   data 𝕎 : U ̇ where
    sup : {a : A} → (T a → 𝕎) → 𝕎

   α : 𝕎 → (𝕎 → U ̇)
   α (sup φ) = fiber φ

   module _ (X : U ̇) where
    H : 𝕎 → U ̇
    H w = α w w → X
    R : 𝕎
    R = sup {S (Σ H)} (pr₁ ∘ ρ)
    B : U ̇
    B = α R R
    r : B → (B → X)
    r (t , p) = transport H p (pr₂ (ρ t))
    s : (B → X) → B
    s f = σ (R , f) , ap pr₁ (η (R , f))
    rs : (f : B → X) → r (s f) ≡ f
    rs f = r (s f)
                   ≡⟨ refl ⟩
           transport H (ap pr₁ (η (R , f))) (pr₂ (ρ (σ {Σ H} (R , f))))
                   ≡⟨ (transport-ap H pr₁ (η (R , f)))⁻¹ ⟩
           transport (H ∘ pr₁) (η (R , f)) (pr₂ (ρ (σ {Σ H} (R , f))))
                   ≡⟨ apd pr₂ (η (R , f)) ⟩
           pr₂ ((R , f) ∶ Σ H)
                   ≡⟨ refl ⟩
           f       ∎
    γ : (f : X → X) → Σ \(x : X) → x ≡ f x
    γ = retract-version.LFPT (r , s , rs)

\end{code}

This can be rephrased as follows, where the use of 𝟘-elim is to
coerce the empty type in the universe U to the empty type in the
universe U₀, which is where our negations take values:

\begin{code}

 Lemma₁ : ∀ U (A : U ̇) (T : A → U ̇) (S : U ̇ → A)
        → ¬((X : U ̇) → retract X of (T (S X)))
 Lemma₁ U A T S retr = 𝟘-elim (Lemma₀ U A T S (λ {X} → pr₁(retr X))
                                              (λ {X} → pr₁(pr₂(retr X)))
                                              (λ {X} → pr₂(pr₂(retr X))))

\end{code}

Because equivalences are retractions, it follows that

\begin{code}

 Lemma₂ : ∀ U (A : U ̇) (T : A → U ̇) (S : U ̇ → A)
        → ¬((X : U ̇) → T (S X) ≃ X)
 Lemma₂ U A T S e = Lemma₁ U A T S (λ X → equiv-retract-r (e X))

\end{code}

And because identitities are equivalences, it follows that

\begin{code}

 Lemma₃ : ∀ U (A : U ̇) (T : A → U ̇) (S : U ̇ → A)
        → ¬((X : U ̇) → T (S X) ≡ X)
 Lemma₃ U A T S p = Lemma₂ U A T S (λ X → idtoeq (T (S X)) X (p X))

\end{code}

This means that a universe U cannot be a retract of any type in U:

\begin{code}

 Lemma₄ : ∀ U → ¬ Σ \(A : U ̇) → retract U ̇ of A
 Lemma₄ U (A , T , S , TS) = Lemma₃ U A T S TS

\end{code}

Therefore, because equivalences are retractions, no universe U can be
equivalent to a type in U:

\begin{code}

 Theorem : ∀ U → ¬ Σ \(𝕌 : U ̇) → U ̇ ≃ 𝕌
 Theorem U (𝕌 , e) = Lemma₄ U (𝕌 , equiv-retract-l e)

\end{code}
