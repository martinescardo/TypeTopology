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

The following proofs are originally due to Ingo Blechschmidt during
the Autumn School "Proof and Computation", Fischbachau, 2018, after I
posed the problem of showing that the universe is uncountable to
him. This version is an adaptation jointly developed by the two of us
to use LFTP, also extended to replace "discrete" by "set" at the cost
of "jumping" a universe.

\begin{code}

module Blechschmidt (pt : PropTrunc) where

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
 udr-lemma X B a₀ i b retr = retract-version.LFPT retr'
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
   n : ¬(Σ \a → X a ≡ B)
   n = uncurry φ

 Universe-uncountable : {U : Universe} → ¬ Σ \(X : ℕ → U ̇) → is-surjection X
 Universe-uncountable (X , s) = Universe-discretely-regular X ℕ-discrete s

\end{code}

A variation, replacing discreteness by set-hood, at the cost of
"jumping a universe level".

\begin{code}

module Blechschmidt' (pt : PropTrunc) where

 open PropositionalTruncation pt
 open ImageAndSurjection pt
 open import DiscreteAndSeparated

 Π-projection-has-section :
    ∀ {U V W} {A : U ̇} {X : A → V ̇}
  → funext V ((U ⊔ W)′) → funext (U ⊔ W) (U ⊔ W) → propext (U ⊔ W)
  → (a₀ : A) → is-h-isolated a₀ → has-section (λ (f : (a : A) → X a → Ω (U ⊔ W)) → f a₀)
 Π-projection-has-section {U} {V} {W} {A} {X} fe fe' pe a₀ ish = s , rs
  where
   s : (X a₀ → Ω (U ⊔ W)) → ((a : A) → X a → Ω (U ⊔ W))
   s φ a x = ∥(Σ \(p : a ≡ a₀) → φ (transport X p x) holds)∥ , ptisp
   rs : (φ : X a₀ → Ω (U ⊔ W)) → s φ a₀ ≡ φ
   rs φ = dfunext fe γ
    where
     a : (x₀ : X a₀) → ∥(Σ \(p : a₀ ≡ a₀) → φ (transport X p x₀) holds)∥ → φ x₀ holds
     a x₀ = ptrec (holds-is-prop (φ x₀)) f
      where
       f : (Σ \(p : a₀ ≡ a₀) → φ (transport X p x₀) holds) → φ x₀ holds
       f (p , h) = transport _holds t h
        where
         r : p ≡ refl
         r = ish p refl
         t : φ (transport X p x₀) ≡ φ x₀
         t = ap (λ - → φ(transport X - x₀)) r
     b : (x₀ : X a₀) → φ x₀ holds → ∥(Σ \(p : a₀ ≡ a₀) → φ (transport X p x₀) holds)∥
     b x₀ h = ∣ refl , h ∣
     γ : (x₀ : X a₀) → (∥(Σ \(p : a₀ ≡ a₀) → φ (transport X p x₀) holds)∥ , ptisp) ≡ φ x₀
     γ x₀ = to-Σ-≡ (pe ptisp (holds-is-prop (φ x₀)) (a x₀) (b x₀) ,
                     is-prop-is-prop fe' (holds-is-prop _) (holds-is-prop (φ x₀)))

 usr-lemma : ∀ {U V W} {A : U ̇} (X : A → V ̇)
           → funext V ((U ⊔ W)′) → funext (U ⊔ W) (U ⊔ W) → propext (U ⊔ W)
           → (a₀ : A)
           → is-h-isolated a₀
           → retract ((a : A) → X a → Ω (U ⊔ W)) of X a₀
           → (f : Ω (U ⊔ W) → Ω (U ⊔ W)) → Σ \(p : Ω (U ⊔ W)) → p ≡ f p
 usr-lemma {U} {V} {W} {A} X fe fe' pe a₀ i retr = retract-version.LFPT retr'
  where
   retr' : retract (X a₀ → Ω (U ⊔ W)) of X a₀
   retr' = retracts-compose
            retr
            ((λ f → f a₀) , Π-projection-has-section {U} {V} {W} fe fe' pe a₀ i)
\end{code}

We now work with the following assumptions:

\begin{code}

 module _
   (U V : Universe)
   (fe' : funext (U ′ ⊔ V) (U ′))
   (fe  : funext U U)
   (fe₀ : funext U U₀)
   (pe  : propext U)
   (A   : U ̇)
   (X   : A → U ′ ⊔ V ̇)
   (iss : is-set A)
   where

\end{code}

NB. If V is U or U', then X : A → U ′ ̇.

\begin{code}

  universe-set-regular' : Σ \(B : U ′ ⊔ V ̇) → (a : A) → ¬(X a ≃ B)
  universe-set-regular' = B , φ
    where
     B : U ′ ⊔ V ̇
     B = (a : A) → X a → Ω U
     φ : (a : A) → ¬(X a ≃ B)
     φ a p = retract-version.not-no-fp fe₀ (γ (not fe₀))
      where
       retr : retract B of (X a)
       retr = equiv-retract-r p
       γ : (f : Ω U → Ω U) → Σ \(p : Ω U) → p ≡ f p
       γ = usr-lemma {U} {V ⊔ U ′} {U} {A} X fe' fe pe a iss retr

  universe-set-regular : Σ \(B : U ′ ⊔ V ̇) → (a : A) → ¬(X a ≡ B)
  universe-set-regular = γ universe-set-regular'
   where
    γ : (Σ \(B : U ′ ⊔ V ̇) → (a : A) → ¬(X a ≃ B))
      → (Σ \(B : U ′ ⊔ V ̇) → (a : A) → ¬(X a ≡ B))
    γ (B , φ) = B , (λ a → contrapositive (idtoeq (X a) B) (φ a))

  Universe-set-regular : ¬(is-surjection X)
  Universe-set-regular s = ptrec 𝟘-is-prop (uncurry φ) e
   where
    B : U ′ ⊔ V ̇
    B = pr₁ universe-set-regular
    φ : ∀ a → ¬(X a ≡ B)
    φ = pr₂ universe-set-regular
    e : ∥(Σ \a → X a ≡ B)∥
    e = s B

\end{code}

See also http://www.cs.bham.ac.uk/~mhe/agda-new/Type-in-Type-False.html

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

module GeneralizedCoquand where

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

Starting from Lemma₀, we get weaker and weaker statements, of which
the weakest, but probably the most meaningful, is the Theorem.
