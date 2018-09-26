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
open import Two

module retract-version where


 has-pt-section : ∀ {U V} {A : U ̇} {X : V ̇} → (A → (A → X)) → U ⊔ V ̇
 has-pt-section r = Σ \(s : cod r → dom r) → ∀ g a → r (s g) a ≡ g a

 section-gives-pt-section : ∀ {U V} {A : U ̇} {X : V ̇} (r : A → (A → X))
                          → has-section r → has-pt-section r
 section-gives-pt-section r (s , rs) = s , λ g a → ap (λ - → - a) (rs g)

 LFPT : ∀ {U V} {A : U ̇} {X : V ̇} (r : A → (A → X))
     → has-pt-section r
     → (f : X → X) → Σ \(x : X) → x ≡ f x
 LFPT {U} {V} {A} {X} r (s , rs) f = x , p
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

 LFPTr : ∀ {U V} {A : U ̇} {X : V ̇}
       → retract (A → X) of A
       → (f : X → X) → Σ \(x : X) → x ≡ f x
 LFPTr (r , h) = LFPT r (section-gives-pt-section r h)

 LFPT-Id : ∀ {U V} {A : U ⊔ V ̇} {X : U ̇}
       → A ≡ (A → X)
       → (f : X → X) → Σ \(x : X) → x ≡ f x
 LFPT-Id p = LFPTr (Id-retract-r p)

 \end{code}

 We apply LFPT twice to get the following: first every function
 U ̇ → U ̇ has a fixed point, from which for any type X we get a type B
 with B ≡ (B → X), and hence with (B → X) a retract of B, for which we
 apply LFPT again to get that every X → X has a fixed point.

 \begin{code}

 cantor-theorem-for-universes :
     (U V : Universe) (A : V ̇) (r : A → (A → U ̇))
   → has-pt-section r
   → (X : U ̇) (f : X → X) → Σ \(x : X) → x ≡ f x
 cantor-theorem-for-universes U V A r h X = LFPT-Id {U} {U} p
  where
   B : U ̇
   B = pr₁(LFPT r h (λ B → B → X))
   p : B ≡ (B → X)
   p = pr₂(LFPT r h (λ B → B → X))

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
 here are types of maps into the subtype classifier Ω U of the universe U.

 Function extensionality is needed in order to define negation
 Ω U → Ω U, to show that P → 𝟘 is a proposition.

 \begin{code}

 open import UF-Subsingletons
 open import UF-FunExt
 open import UF-Subsingletons-FunExt

 not-no-fp : ∀ {U} (fe : funext U U₀) → (B : Ω U) → ¬(B ≡ not fe B)
 not-no-fp {U} fe B p = pr₁(γ id)
  where
   q : B holds ≡ ¬(B holds)
   q = ap _holds p
   γ : (f : 𝟘 → 𝟘) → Σ \(x : 𝟘) → x ≡ f x
   γ = LFPT-Id q

 cantor-theorem : (U V : Universe) (A : V ̇)
                → funext U U₀ → (r : A → (A → Ω U)) → has-pt-section r → 𝟘
 cantor-theorem U V A fe r (s , rs) = not-no-fp fe B p
  where
   B : Ω U
   B = pr₁ (LFPT r (s , rs) (not fe))
   p : B ≡ not fe B
   p = pr₂ (LFPT r (s , rs) (not fe))

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
   g (B , p) = retract-version.LFPT-Id {U} {U} p f

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
   t = LFPT φ s (not fe)
   g : (Σ \(B : Ω U) → B ≡ not fe B) → 𝟘
   g (B , p) = retract-version.not-no-fp fe B p

 \end{code}

 Another corollary is that the Cantor type (ℕ → 𝟚) and the Baire type
 (ℕ → ℕ) are uncountable:

 \begin{code}

 open import Two

 cantor-uncountable : (φ : ℕ → (ℕ → 𝟚)) → ¬(is-surjection φ)
 cantor-uncountable φ s = ptrec 𝟘-is-prop (uncurry complement-no-fp) t
  where
   t : ∃ \(n : 𝟚) → n ≡ complement n
   t = LFPT φ s complement

 baire-uncountable : (φ : ℕ → (ℕ → ℕ)) → ¬(is-surjection φ)
 baire-uncountable φ s = ptrec 𝟘-is-prop (uncurry succ-no-fp) t
  where
   t : ∃ \(n : ℕ) → n ≡ succ n
   t = LFPT φ s succ

\end{code}

The following proofs are originally due to Ingo Blechschmidt during
the Autumn School "Proof and Computation", Fischbachau, 2018, after I
posed the problem of showing that the universe is uncountable to
him. This version is an adaptation jointly developed by the two of us
to use LFTP, also extended to replace "discrete" by "set" at the cost
of "jumping" a universe.

\begin{code}

module universe-uncountable (pt : PropTrunc) where

 open PropositionalTruncation pt
 open ImageAndSurjection pt

 open import DiscreteAndSeparated

 Π-projection-has-section :
    ∀ {U V} {X : U ̇} {Y : X → V ̇} (x₀ : X)
  → isolated x₀
  → Π Y
  → has-section (λ (f : Π Y) → f x₀)
 Π-projection-has-section {U} {V} {X} {Y} x₀ i g = s , rs
  where
   s : Y x₀ → Π Y
   s y x = Cases (i x)
            (λ (p : x₀ ≡ x) → transport Y p y)
            (λ (_ : ¬(x₀ ≡ x)) → g x)
   rs : (y : Y x₀) → s y x₀ ≡ y
   rs y = ap (λ - → Cases - _ _) a
    where
     a : i x₀ ≡ inl refl
     a = isolated-inl x₀ i x₀ refl

 udr-lemma : ∀ {U V W} {A : U ̇} (X : A → V ̇) (B : W ̇)
             (a₀ : A)
           → isolated a₀
           → B
           → retract ((a : A) → X a → B) of X a₀
           → (f : B → B) → Σ \(b : B) → b ≡ f b
 udr-lemma X B a₀ i b retr = retract-version.LFPTr retr'
  where
   retr' : retract (X a₀ → B) of X a₀
   retr' = retracts-compose
            retr
            ((λ f → f a₀) , Π-projection-has-section a₀ i (λ a x → b))

 universe-discretely-regular' :
    (U V : Universe) (A : U ̇) (X : A → U ⊔ V ̇)
  → discrete A → Σ \(B : U ⊔ V ̇) → (a : A) → ¬(X a ≃ B)
 universe-discretely-regular' U V A X d  = B , φ
   where
    B : U ⊔ V ̇
    B = (a : A) → X a → 𝟚
    φ : (a : A) → ¬ (X a ≃ B)
    φ a p = uncurry complement-no-fp (γ complement)
     where
      retr : retract B of (X a)
      retr = equiv-retract-r p
      γ : (f : 𝟚 → 𝟚) → Σ \(b : 𝟚) → b ≡ f b
      γ = udr-lemma X 𝟚 a (d a) ₀ retr

 universe-discretely-regular :
    {U V : Universe} {A : U ̇} (X : A → U ⊔ V ̇)
  → discrete A → Σ \(B : U ⊔ V ̇) → (a : A) → ¬(X a ≡ B)
 universe-discretely-regular {U} {V} {A} X d =
   γ (universe-discretely-regular' U V A X d)
  where
   γ : (Σ \(B : U ⊔ V ̇) → (a : A) → ¬(X a ≃ B))
     → (Σ \(B : U ⊔ V ̇) → (a : A) → ¬(X a ≡ B))
   γ (B , φ) = B , (λ a → contrapositive (idtoeq (X a) B) (φ a))

 Universe-discretely-regular : {U V : Universe} {A : U ̇} (X : A → U ⊔ V ̇)
                             → discrete A → ¬(is-surjection X)
 Universe-discretely-regular {U} {V} {A} X d s = ptrec 𝟘-is-prop n e
  where
   B : U ⊔ V ̇
   B = pr₁(universe-discretely-regular {U} {V} {A} X d)
   φ : ∀ a → ¬(X a ≡ B)
   φ = pr₂(universe-discretely-regular {U} {V} {A} X d)
   e : ∥(Σ \a → X a ≡ B)∥
   e = s B
   n : (Σ \a → X a ≡ B) → 𝟘
   n (a , p) = φ a p

 Universe-uncountable : {U : Universe} (X : ℕ → U ̇) → ¬(is-surjection X)
 Universe-uncountable X = Universe-discretely-regular X ℕ-discrete

\end{code}

A variation:

\begin{code}

 Π-projection-has-section' :
    ∀ {U V W} {X : U ̇} {Y : X → V ̇}
  → funext V ((U ⊔ W)′) → funext (U ⊔ W) (U ⊔ W) → propext (U ⊔ W)
  → (x₀ : X) → is-h-isolated x₀ → has-section (λ (f : (x : X) → Y x → Ω (U ⊔ W)) → f x₀)
 Π-projection-has-section' {U} {V} {W} {X} {Y} fe fe' pe x₀ ish = s , rs

  where
   s : (Y x₀ → Ω (U ⊔ W)) → ((x : X) → Y x → Ω (U ⊔ W))
   s φ x y = ∥(Σ \(p : x ≡ x₀) → φ (transport Y p y) holds)∥ , ptisp
   rs : (φ : Y x₀ → Ω (U ⊔ W)) → s φ x₀ ≡ φ
   rs φ = dfunext fe γ
    where
     a : (y₀ : Y x₀) → (∥(Σ \(p : x₀ ≡ x₀) → φ (transport Y p y₀) holds)∥ , ptisp) ≡ ⊤ → φ y₀ ≡ ⊤
     a y₀ q = ptrec (Ω-is-set fe' pe) d c
      where
       c : ∥(Σ \(p : x₀ ≡ x₀) → φ (transport Y p y₀) holds)∥
       c = equal-⊤-is-true _ ptisp q
       d : (Σ \(p : x₀ ≡ x₀) → φ (transport Y p y₀) holds) → φ y₀ ≡ ⊤
       d (p , h) = true-is-equal-⊤ pe fe' (φ y₀ holds) (holds-is-prop (φ y₀)) (transport (λ - → - holds) t h)
        where
         r : p ≡ refl
         r = ish p refl
         t : φ (transport Y p y₀) ≡ φ y₀
         t = ap (λ - → φ(transport Y - y₀)) r
     b : (y₀ : Y x₀) → φ y₀ ≡ ⊤ → (∥(Σ \(p : x₀ ≡ x₀) → φ (transport Y p y₀) holds)∥ , ptisp) ≡ ⊤
     b y₀ q = true-is-equal-⊤ pe fe' _ ptisp ∣ refl , c ∣
      where
       c : φ y₀ holds
       c = equal-⊤-is-true _ (holds-is-prop _) q
     γ : (y₀ : Y x₀) → (∥(Σ \(p : x₀ ≡ x₀) → φ (transport Y p y₀) holds)∥ , ptisp) ≡ φ y₀
     γ y₀ = Ω-ext pe fe' (a y₀) (b y₀)

 udr-lemma' : ∀ {U V W} {A : U ̇} (X : A → V ̇)
           → funext V ((U ⊔ W)′) → funext (U ⊔ W) (U ⊔ W) → propext (U ⊔ W)
           → (a₀ : A)
           → is-h-isolated a₀
           → retract ((a : A) → X a → Ω (U ⊔ W)) of X a₀
           → (f : Ω (U ⊔ W) → Ω (U ⊔ W)) → Σ \(b : Ω (U ⊔ W)) → b ≡ f b
 udr-lemma' {U} {V} {W} {A} X fe fe' pe a₀ i retr = retract-version.LFPTr retr'
  where
   retr' : retract (X a₀ → Ω (U ⊔ W)) of X a₀
   retr' = retracts-compose
            retr
            ((λ f → f a₀) , Π-projection-has-section' {U} {V} {W} fe fe' pe a₀ i)

 universe-set-regular' :
    (U : Universe) (A : U ̇) (X : A → U ′ ̇)
  → funext (U ′) (U ′) → funext U U → funext U U₀ → propext U
  → is-set A → Σ \(B : U ′ ̇) → (a : A) → ¬(X a ≃ B)
 universe-set-regular' U A X fe' fe fe₀ pe iss  = B , φ
   where
    B : U ′ ̇
    B = (a : A) → X a → Ω U
    φ : (a : A) → ¬(X a ≃ B)
    φ a p = retract-version.not-no-fp fe₀ (pr₁ (γ (not fe₀))) (pr₂ (γ (not fe₀)))
     where
      retr : retract B of (X a)
      retr = equiv-retract-r p
      γ : (f : Ω U → Ω U) → Σ \(p : Ω U) → p ≡ f p
      γ = udr-lemma' {U} {U ′} {U} {A} X fe' fe pe a iss retr

 universe-set-regular :
    {U : Universe} {A : U ̇} (X : A → U ′ ̇)
  → funext (U ′) (U ′) → funext U U → funext U U₀ → propext U
  → is-set A → Σ \(B : U ′ ̇) → (a : A) → ¬(X a ≡ B)
 universe-set-regular {U} {A} X fe' fe fe₀ pe iss =
   γ (universe-set-regular' U A X fe' fe fe₀ pe iss)
  where
   γ : (Σ \(B : U ′ ̇) → (a : A) → ¬(X a ≃ B))
     → (Σ \(B : U ′ ̇) → (a : A) → ¬(X a ≡ B))
   γ (B , φ) = B , (λ a → contrapositive (idtoeq (X a) B) (φ a))

 Universe-set-regular : {U : Universe} {A : U ̇} (X : A → U ′ ̇)
    → funext (U ′) (U ′) → funext U U → funext U U₀ → propext U
    → is-set A → ¬(is-surjection X)
 Universe-set-regular {U} {A} X fe' fe fe₀ pe iss s = ptrec 𝟘-is-prop n e
  where
   B : U ′ ̇
   B = pr₁ (universe-set-regular X fe' fe fe₀ pe iss)
   φ : ∀ a → ¬(X a ≡ B)
   φ = pr₂ (universe-set-regular X fe' fe fe₀ pe iss)
   e : ∥(Σ \a → X a ≡ B)∥
   e = s B
   n : (Σ \a → X a ≡ B) → 𝟘
   n (a , p) = φ a p

\end{code}
