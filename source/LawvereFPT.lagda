Martin Escardo, 5th September 2018.

On Lawvere's Fixed Point Theorem (LFPT).
http://tac.mta.ca/tac/reprints/articles/15/tr15abs.html

We give an application to Cantor's theorem for the universe.

We begin with split surjections, or retracts, because they can be
formulated in MLTT, and then move to surjections, which need further
extensions to MLTT, such as propositional truncation.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module LawvereFPT where

open import SpartanMLTT

\end{code}

The following pointwise weakening of split surjection is sufficient to
prove LFPT and allows us to avoid function extensionality in its
applications:

\begin{code}

module retract-version where

 open import UF-Retracts

 has-pt-section : ∀ {U V} {A : U ̇} {X : V ̇} → (A → (A → X)) → U ⊔ V ̇
 has-pt-section r = Σ \(s : cod r → dom r) → ∀ g a → r (s g) a ≡ g a

 section-gives-pt-section : ∀ {U V} {A : U ̇} {X : V ̇} (r : A → (A → X))
                         → has-section r → has-pt-section r
 section-gives-pt-section r (s , rs) = s , λ g a → ap (λ - → - a) (rs g)

 lfpt : ∀ {U V} {A : U ̇} {X : V ̇} (r : A → (A → X))
      → has-pt-section r
      → (f : X → X) → Σ \(x : X) → x ≡ f x
 lfpt {U} {V} {A} {X} r (s , rs) f = x , p
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

 \end{code}

 We apply the above version of LFPT twice to get the following: first
 every function U ̇ → U ̇ has a fixed point, from which for any type X we
 get a type B with B ≡ (B → X), and hence with (B → X) a retract of B,
 for which we apply LFPT again to get that every X → X has a fixed point.

 \begin{code}

 cantor-theorem-for-universes :
     (U V : Universe) (A : V ̇) (r : A → (A → U ̇))
  → has-pt-section r
  → (X : U ̇) (f : X → X) → Σ \(x : X) → x ≡ f x
 cantor-theorem-for-universes U V A r (s , rs) X = γ
  where
   open import UF-Equiv
   B : U ̇
   B = pr₁(lfpt r (s , rs) (λ B → B → X))
   p : B ≡ (B → X)
   p = pr₂(lfpt r (s , rs) (λ B → B → X))
   e : B ≃ (B → X)
   e = idtoeq B (B → X) p
   retr : retract (B → X) of B
   retr = equiv-retract-r e
   ρ : B → (B → X)
   ρ = pr₁ retr
   σ : (B → X) → B
   σ = pr₁ (section-gives-pt-section ρ (pr₂ retr))
   ρσ : (g : B → X) (b : B) → ρ (σ g) b ≡ g b
   ρσ = pr₂ (section-gives-pt-section ρ (pr₂ retr))
   γ : (f : X → X) → Σ \(x : X) → x ≡ f x
   γ = lfpt ρ (σ , ρσ)

 \end{code}

 Taking X to be 𝟘 we get a contradiction, i.e. an inhabitant of the
 empty type 𝟘 (in fact, we get an inhabitant of any type by considering
 the identity function):

 \begin{code}

 Cantor-theorem-for-universes :
     (U V : Universe) (A : V ̇)
  → (r : A → (A → U ̇)) → has-pt-section r → 𝟘
 Cantor-theorem-for-universes U V A r h = pr₁ (cantor-theorem-for-universes U V A r h 𝟘 id)

 \end{code}

 The original version of Cantor's theorem was for powersets, which
 here are maps into the subtype classifier. Function extensionality is
 needed in order to define negation Ω U → Ω U, to show that P → 𝟘 is a
 proposition.

 \begin{code}

 open import UF-Subsingletons
 open import UF-FunExt
 open import UF-Subsingletons-FunExt

 cantor-theorem : (U V : Universe) (A : V ̇)
               → funext U U₀ → (r : A → (A → Ω U)) → has-pt-section r → 𝟘
 cantor-theorem U V A fe r (s , rs) = pr₁ γ
  where
   open import UF-Equiv
   B : Ω U
   B = pr₁ (lfpt r (s , rs) (not fe))
   p : B ≡ not fe B
   p = pr₂ (lfpt r (s , rs) (not fe))
   P : U ̇
   P = pr₁ B
   q : P ≡ ¬ P
   q = ap pr₁ p
   e : P ≃ ¬ P
   e = idtoeq P (¬ P) q
   retr : retract (¬ P) of P
   retr = equiv-retract-r e
   ρ : P → ¬ P
   ρ = pr₁ retr
   σ : (¬ P) → P
   σ = pr₁ (section-gives-pt-section ρ (pr₂ retr))
   ρσ : (g : ¬ P) (b : P) → ρ (σ g) b ≡ g b
   ρσ = pr₂ (section-gives-pt-section ρ (pr₂ retr))
   γ : Σ \(x : 𝟘) → x ≡ x
   γ = lfpt ρ (σ , ρσ) id

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

 lfpt : ∀ {U V} {A : U ̇} {X : V ̇} (φ : A → (A → X))
       → is-surjection φ
       → (f : X → X) → ∃ \(x : X) → x ≡ f x
 lfpt {U} {V} {A} {X} φ s f = ptfunct γ e
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

 So in lfpto we have a weaker hypothesis for the theorem, but we need a
 stronger language for formulate and prove it, or else an additional
 hypothesis of the existence of propositional truncations.

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
   t = lfpt φ s (λ B → B → X)
   g : (Σ \(B : U ̇) → B ≡ (B → X)) → Σ \(x : X) → x ≡ f x
   g (B , p) = retract-version.lfpt ρ (σ , ρσ) f
    where
     open import UF-Equiv
     open import UF-Retracts
     e : B ≃ (B → X)
     e = idtoeq B (B → X) p
     retr : retract (B → X) of B
     retr = equiv-retract-r e
     ρ : B → (B → X)
     ρ = pr₁ retr
     σ : (B → X) → B
     σ = pr₁ (retract-version.section-gives-pt-section ρ (pr₂ retr))
     ρσ : (g : B → X) (b : B) → ρ (σ g) b ≡ g b
     ρσ = pr₂ (retract-version.section-gives-pt-section ρ (pr₂ retr))

 Cantor-theorem-for-universes :
     (U V : Universe) (A : V ̇)
  → (φ : A → (A → U ̇)) → is-surjection φ → 𝟘
 Cantor-theorem-for-universes U V A r h = ptrec 𝟘-is-prop pr₁ c
  where
   c : ∃ \(x : 𝟘) → x ≡ x
   c = cantor-theorem-for-universes U V A r h 𝟘 id

 cantor-theorem :
     (U V : Universe) (A : V ̇)
  → funext U U₀ → (φ : A → (A → Ω U)) → ¬(is-surjection φ)
 cantor-theorem U V A fe φ s = ptrec 𝟘-is-prop g t
  where
   t : ∃ \(B : Ω U) → B ≡ not fe B
   t = lfpt φ s (not fe)
   g : (Σ \(B : Ω U) → B ≡ not fe B) → 𝟘
   g ((P , i) , p) = pr₁ (retract-version.lfpt ρ (σ , ρσ) id)
    where
     open import UF-Equiv
     open import UF-Retracts
     q : P ≡ ¬ P
     q = ap pr₁ p
     e : P ≃ ¬ P
     e = idtoeq P (¬ P) q
     retr : retract (¬ P) of P
     retr = equiv-retract-r e
     ρ : P → (¬ P)
     ρ = pr₁ retr
     σ : (¬ P) → P
     σ = pr₁ (retract-version.section-gives-pt-section ρ (pr₂ retr))
     ρσ : (g : ¬ P) (b : P) → ρ (σ g) b ≡ g b
     ρσ = pr₂ (retract-version.section-gives-pt-section ρ (pr₂ retr))

\end{code}

This argument should be generalized to e.g. the universe of sets and
the universe of n-types for any n, as well as the universe of groups,
of topological spaces, etc.
