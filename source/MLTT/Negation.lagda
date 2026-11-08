Martin Escardo, original date unknown.

Negation (and emptiness).

\begin{code}

{-# OPTIONS --safe --without-K #-}

module MLTT.Negation where

open import MLTT.Empty
open import MLTT.Id
open import MLTT.Pi
open import MLTT.Plus
open import MLTT.Sigma

private
 _↔_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
 A ↔ B = (A → B) × (B → A)

¬_ : 𝓤 ̇ → 𝓤 ̇
¬ A = A → 𝟘 {𝓤₀}

\end{code}

Notice that decidability is not a univalent proposition in general,
but nevertheless we use "is" in our chosen terminology, against a
convention adopted in some quarters that says that "is" should be used
only for concepts that are propositions.

\begin{code}

is-decidable : 𝓤 ̇ → 𝓤 ̇
is-decidable A = A + ¬ A

_≠_ : {X : 𝓤 ̇ } → (x y : X) → 𝓤 ̇
x ≠ y = ¬ (x ＝ y)

has-two-distinct-points : 𝓤 ̇ → 𝓤 ̇
has-two-distinct-points X = Σ (x , y) ꞉ X × X , (x ≠ y)

has-three-distinct-points : 𝓤 ̇ → 𝓤 ̇
has-three-distinct-points X = Σ (x , y , z) ꞉ X × X × X
                            , (x ≠ y) × (y ≠ z) × (z ≠ x)

≠-sym : {X : 𝓤 ̇ } → {x y : X} → x ≠ y → y ≠ x
≠-sym u r = u (r ⁻¹)

is-empty : 𝓤 ̇ → 𝓤 ̇
is-empty = ¬_

¬¬_ : 𝓤 ̇ → 𝓤 ̇
¬¬ A = ¬ (¬ A)

¬¬¬_ : 𝓤 ̇ → 𝓤 ̇
¬¬¬ A = ¬ (¬¬ A)

is-nonempty : 𝓤 ̇ → 𝓤 ̇
is-nonempty = ¬¬_

dual : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (R : 𝓦 ̇ ) → (X → Y) → (Y → R) → (X → R)
dual R f p = p ∘ f

contrapositive : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → (A → B) → ¬ B → ¬ A
contrapositive = dual _

double-contrapositive : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → (A → B) → ¬¬ A → ¬¬ B
double-contrapositive = contrapositive ∘ contrapositive

¬¬-functor : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → (A → B) → ¬¬ A → ¬¬ B
¬¬-functor = double-contrapositive

¬¬-kleisli : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → (A → ¬¬ B) → ¬¬ A → ¬¬ B
¬¬-kleisli f ϕ h = ϕ (λ a → f a h)

¬¬-intro : {A : 𝓤 ̇ } → A → ¬¬ A
¬¬-intro x u = u x

≠-is-irrefl : {X : 𝓤 ̇ } (x : X) → ¬ (x ≠ x)
≠-is-irrefl x = ¬¬-intro refl

three-negations-imply-one : {A : 𝓤 ̇ } → ¬¬¬ A → ¬ A
three-negations-imply-one = contrapositive ¬¬-intro

dne' : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → (A → B) → (¬¬ B → B) → ¬¬ A → B
dne' f h ϕ = h (λ g → ϕ (λ a → g (f a)))

dne : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → (A → ¬ B) → ¬¬ A → ¬ B
dne f ϕ b = ϕ (λ a → f a b)

double-negation-unshift : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
                        → ¬¬ ((x : X) → A x)
                        → (x : X) → ¬¬ (A x)
double-negation-unshift f x g = f (λ h → g (h x))

dnu : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → ¬¬ (A × B) → ¬¬ A × ¬¬ B
dnu φ = (¬¬-functor pr₁ φ) , (¬¬-functor pr₂ φ)

und : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → ¬¬ A × ¬¬ B → ¬¬ (A × B)
und (φ , γ) w = γ (λ y → φ (λ x → w (x , y)))

¬¬-stable : 𝓤 ̇ → 𝓤 ̇
¬¬-stable A = ¬¬ A → A

is-negative-type : 𝓤 ̇ → 𝓤 ⁺ ̇
is-negative-type {𝓤} A = Σ B ꞉ 𝓤 ̇ , (A ↔ ¬ B)

¬¬-stable-types-are-negative : (A : 𝓤 ̇ ) → ¬¬-stable A → is-negative-type A
¬¬-stable-types-are-negative A s = (¬ A) , ¬¬-intro , s

negative-types-are-¬¬-stable : (A : 𝓤 ̇ ) → is-negative-type A → ¬¬-stable A
negative-types-are-¬¬-stable A (B , f , g) = III
 where
  I : A → ¬ B
  I a b = 𝟘-elim (f a b)

  II : ¬ B → A
  II ν = g (λ b → 𝟘-elim (ν b))

  III : ¬¬ A → A
  III = II ∘ three-negations-imply-one ∘ ¬¬-functor I

¬-is-¬¬-stable : {A : 𝓤 ̇ } → ¬¬-stable (¬ A)
¬-is-¬¬-stable = three-negations-imply-one

Π-is-¬¬-stable : {A : 𝓤 ̇ } {B : A → 𝓥 ̇ }
               → ((a : A) → ¬¬-stable (B a))
               → ¬¬-stable (Π B)
Π-is-¬¬-stable f ϕ a = f a (λ v → ϕ (λ g → v (g a)))

→-is-¬¬-stable : {A : 𝓤 ̇ } {B : 𝓥 ̇ }
               → ¬¬-stable B
               → ¬¬-stable (A → B)
→-is-¬¬-stable f = Π-is-¬¬-stable (λ _ → f)

×-is-¬¬-stable : {A : 𝓤 ̇ } {B : 𝓥 ̇ }
               → ¬¬-stable A
               → ¬¬-stable B
               → ¬¬-stable (A × B)
×-is-¬¬-stable f g ϕ = f (λ v → ϕ (λ (a , b) → v a)) ,
                       g (λ v → ϕ (λ (a , b) → v b))

negation-of-implication :  {A : 𝓤 ̇ } {B : 𝓥 ̇ }
                        → ¬ (A → B)
                        → ¬¬ A × ¬ B
negation-of-implication u = (λ v → u (λ a → 𝟘-elim (v a))) ,
                            (λ b → u (λ a → b))

negation-of-implication-converse :  {A : 𝓤 ̇ } {B : 𝓥 ̇ }
                                 → ¬¬ A × ¬ B
                                 → ¬ (A → B)
negation-of-implication-converse (u , v) f = u (λ a → v (f a))

Double-negation-of-implication← : {A : 𝓤 ̇ } {B : 𝓥 ̇ }
                                  {R : 𝓦 ̇ } {S : 𝓣 ̇ } {T : 𝓣' ̇ }
                                → (((A → B) → T) → S)
                                → (((A → S) → R) × (B → T)) → R
Double-negation-of-implication← f g = pr₁ g (λ a → f (λ h → pr₂ g (h a)))

Double-negation-of-implication→ : {A : 𝓤 ̇ } {B : 𝓥 ̇ }
                                  (R : 𝓦 ̇ ) {S : 𝓣 ̇ } {T : 𝓣' ̇ } {U : 𝓣' ̇ }
                                → (S → B)
                                → ((((A → S) → T) × (B → T)) → U)
                                → ((A → B) → T) → U
Double-negation-of-implication→ R k f g = f ((λ h → g (λ a → k (h a))) ,
                                             (λ b → g (λ a → b)))

double-negation-of-implication← : {A : 𝓤 ̇ } {B : 𝓥 ̇ }
                                → ¬¬ (A → B)
                                → ¬ (¬¬ A × ¬ B)
double-negation-of-implication← = Double-negation-of-implication←

double-negation-of-implication→ : {A : 𝓤 ̇ } {B : 𝓥 ̇ }
                                → ¬ (¬¬ A × ¬ B)
                                → ¬¬ (A → B)
double-negation-of-implication→ f g =
 Double-negation-of-implication→ (𝟘 {𝓤₀}) 𝟘-elim f g

double-negation-elimination-inside-double-negation : (X : 𝓤 ̇ ) → ¬¬ (¬¬ X → X)
double-negation-elimination-inside-double-negation X = II
 where
  I : ¬ (¬¬ (¬¬ X) × ¬ X)
  I (h₁ , h₂) = h₁ (¬¬-intro h₂)

  II : ¬¬ (¬¬ X → X)
  II = double-negation-of-implication→ I

\end{code}

The following is the particular case of Lawvere's fixed-point
combinator defined in the module Various.LawvereFPT, but we can't use
it here as that module imports this one.

\begin{code}

not-equivalent-to-own-negation' : {A : 𝓤 ̇ } {R : 𝓥 ̇ } → (A ↔ (A → R)) → R
not-equivalent-to-own-negation' (f , g) = f (g (λ a → f a a)) (g (λ a → f a a))

not-equivalent-to-own-negation : {A : 𝓤 ̇ } → ¬ (A ↔ ¬ A)
not-equivalent-to-own-negation = not-equivalent-to-own-negation'

not-Σ-implies-Π-not : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
                    → ¬ (Σ x ꞉ X , A x)
                    → (x : X) → ¬ (A x)
not-Σ-implies-Π-not = curry

Π-not-implies-not-Σ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
                    → ((x : X) → ¬ (A x))
                    → ¬ (Σ x ꞉ X , A x)
Π-not-implies-not-Σ = uncurry

Π-implies-not-Σ-not : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
                    → ((x : X) → A x)
                    → ¬ (Σ x ꞉ X , ¬ (A x))
Π-implies-not-Σ-not f (x , ν) = ν (f x)

not-Π-not-not-implies-not-not-Σ-not : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
                                    → ¬ ((x : X) → ¬¬ (A x))
                                    → ¬¬ (Σ x ꞉ X , ¬ (A x))
not-Π-not-not-implies-not-not-Σ-not = contrapositive not-Σ-implies-Π-not

not-Π-implies-not-not-Σ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
                        → ((x : X) → ¬¬-stable (A x))
                        → ¬ ((x : X) → A x)
                        → ¬¬ (Σ x ꞉ X , ¬ (A x))
not-Π-implies-not-not-Σ f g h = g (λ x → f x (λ u → h (x , u)))

\end{code}

Notation to try to make proofs readable:

\begin{code}

contradiction : 𝓤₀ ̇
contradiction = 𝟘

have_which-is-impossible-by_ : {A : 𝓤 ̇ } {B : 𝓦 ̇ }
                             → A → (A → 𝟘 {𝓤₀}) → B
have a which-is-impossible-by ν = 𝟘-elim (ν a)


have_which-contradicts_ : {A : 𝓤 ̇ } {B : 𝓦 ̇ }
                        → (A → 𝟘 {𝓤₀}) → A → B
have ν which-contradicts a = 𝟘-elim (ν a)

\end{code}

Fixities:

\begin{code}

infix  50 ¬_
infix  50 ¬¬_
infix  50 ¬¬¬_
infix  0 _≠_

\end{code}
