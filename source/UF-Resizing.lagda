Martin Escardo, 24th January 2019.

Voedvodsky (Types'2011) considered resizing rules for a type theory
for univalent foundations. These rules govern the syntax of the formal
system, and hence are of a meta-mathematical nature.

Here we instead formulate, in our type theory without such rules, a
mathematical resizing principle. This principle is provable in the
system with Voevodsky's rules. But we don't postulate this principle
as an axiom. Instead, we use it an assumption, when needed, or as a
conclusion, when it follows from stronger principles, such as excluded
middle.

The consistency of the resizing rules is an open problem at the time
of writing (30th January 2018), but the resizing principle is
consistent relative to ZFC with Grothendieck universes, because it
follows from excluded middle, which is known to be validated by the
simplicial-set model (assuming classical logic in its development).

We develop some consequences of propositional resizing here, such as
the fact that every universe is a retract of any higher universe,
where the section is an embedding (its fibers are all propositions).

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module UF-Resizing where

open import SpartanMLTT
open import UF-Base
open import UF-FunExt
open import UF-Subsingletons
open import UF-Subsingletons-FunExt
open import UF-Equiv
open import UF-Equiv-FunExt
open import UF-Retracts
open import UF-Embeddings
open import UF-EquivalenceExamples
open import UF-ExcludedMiddle
open import UF-Univalence
open import UF-UA-FunExt
open import UF-UniverseEmbedding
open import UF-PropIndexedPiSigma
open import UF-PropTrunc

\end{code}

We say that a type X has size 𝓥 if it is equivalent to a type in the
universe 𝓥:

\begin{code}

_has-size_ : 𝓤 ̇ → (𝓥 : Universe) → 𝓥 ⁺  ⊔ 𝓤 ̇
X has-size 𝓥 = Σ \(Y : 𝓥 ̇) → Y ≃ X

propositional-resizing : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥)⁺ ̇
propositional-resizing 𝓤 𝓥 = (P : 𝓤 ̇) → is-prop P → P has-size 𝓥

\end{code}

Propositional resizing from a universe to a higher universe just holds, of course:

\begin{code}

resize-up : (X : 𝓤 ̇) → X has-size (𝓤 ⊔ 𝓥)
resize-up {𝓤} {𝓥} X = lift 𝓥 X , lift-≃ 𝓥 X

resize-up-proposition : propositional-resizing 𝓤 (𝓤 ⊔ 𝓥)
resize-up-proposition {𝓤} {𝓥} P i = resize-up {𝓤} {𝓥} P

\end{code}

We use the following to work with propositional resizing more abstractly:

\begin{code}

resize           : propositional-resizing 𝓤 𝓥 → (P : 𝓤 ̇) (i : is-prop P) → 𝓥 ̇
resize-is-a-prop : (ρ : propositional-resizing 𝓤 𝓥) (P : 𝓤 ̇) (i : is-prop P) → is-prop (resize ρ P i)
to-resize        : (ρ : propositional-resizing 𝓤 𝓥) (P : 𝓤 ̇) (i : is-prop P) → P → resize ρ P i
from-resize      : (ρ : propositional-resizing 𝓤 𝓥) (P : 𝓤 ̇) (i : is-prop P) → resize ρ P i → P

resize         ρ P i   = pr₁ (ρ P i)
resize-is-a-prop ρ P i = equiv-to-prop (pr₂ (ρ P i)) i
to-resize      ρ P i   = eqtofun (≃-sym(pr₂ (ρ P i)))
from-resize    ρ P i   = eqtofun (pr₂ (ρ P i))

Propositional-resizing : 𝓤ω
Propositional-resizing = {𝓤 𝓥 : Universe} → propositional-resizing 𝓤 𝓥

\end{code}

Propositional resizing is consistent, because it is implied by
excluded middle, which is consistent (with or without univalence):

\begin{code}

EM-gives-PR : EM 𝓤 → propositional-resizing 𝓤 𝓥
EM-gives-PR {𝓤} {𝓥} em P i = Q (em P i) , e
 where
   Q : decidable P → 𝓥 ̇
   Q (inl p) = 𝟙
   Q (inr n) = 𝟘
   j : (d : decidable P) → is-prop (Q d)
   j (inl p) = 𝟙-is-prop
   j (inr n) = 𝟘-is-prop
   f : (d : decidable P) → P → Q d
   f (inl p) p' = *
   f (inr n) p  = 𝟘-elim (n p)
   g : (d : decidable P) → Q d → P
   g (inl p) q = p
   g (inr n) q = 𝟘-elim q
   e : Q (em P i) ≃ P
   e = logically-equivalent-props-are-equivalent (j (em P i)) i (g (em P i)) (f (em P i))

\end{code}

To show that the axiom of propositional resizing is itself a
proposition, we use univalence.

\begin{code}

has-size-is-a-prop : Univalence → (X : 𝓤 ̇) (𝓥 :  Universe)
                   → is-prop (X has-size 𝓥)
has-size-is-a-prop {𝓤} ua X 𝓥 = c
 where
  fe : FunExt
  fe = FunExt-from-Univalence ua
  a : (Y : 𝓥 ̇) → (Y ≃ X) ≃ (lift 𝓤 Y ≡ lift 𝓥 X)
  a Y = (Y ≃ X)                ≃⟨ Eq-Eq-cong fe (≃-sym (lift-≃ 𝓤 Y)) (≃-sym (lift-≃ 𝓥 X)) ⟩
        (lift 𝓤 Y ≃ lift 𝓥 X)  ≃⟨ ≃-sym (is-univalent-≃ (ua (𝓤 ⊔ 𝓥)) _ _) ⟩
        (lift 𝓤 Y ≡ lift 𝓥 X)  ■
  b : (Σ \(Y : 𝓥 ̇) → Y ≃ X) ≃ (Σ \(Y : 𝓥 ̇) → lift 𝓤 Y ≡ lift 𝓥 X)
  b = Σ-cong a
  c : is-prop (Σ \(Y : 𝓥 ̇) → Y ≃ X)
  c = equiv-to-prop b (lift-is-embedding ua (lift 𝓥 X))

propositional-resizing-is-a-prop : Univalence → is-prop (propositional-resizing 𝓤 𝓥)
propositional-resizing-is-a-prop {𝓤} {𝓥} ua =  Π-is-prop (fe (𝓤 ⁺) (𝓥 ⁺ ⊔ 𝓤))
                                                (λ P → Π-is-prop (fe 𝓤 (𝓥 ⁺ ⊔ 𝓤))
                                                (λ i → has-size-is-a-prop ua P 𝓥))
 where
  fe : FunExt
  fe = FunExt-from-Univalence ua

\end{code}

And here is a proof that the axiom of propositional resizing is itself
a proposition using propositional and functional extensionality
instead of univalence:

\begin{code}

prop-has-size-is-a-prop : PropExt
                        → FunExt
                        → (P : 𝓤 ̇)
                        → is-prop P
                        → (𝓥 :  Universe) → is-prop (P has-size 𝓥)
prop-has-size-is-a-prop {𝓤} pe fe P i 𝓥 = c
 where
  j : is-prop (lift 𝓥 P)
  j = equiv-to-prop (lift-≃ 𝓥 P) i
  a : (Y : 𝓥 ̇) → (Y ≃ P) ≃ (lift 𝓤 Y ≡ lift 𝓥 P)
  a Y = (Y ≃ P)                ≃⟨ Eq-Eq-cong fe (≃-sym (lift-≃ 𝓤 Y)) (≃-sym (lift-≃ 𝓥 P)) ⟩
        (lift 𝓤 Y ≃ lift 𝓥 P)  ≃⟨ ≃-sym (prop-univalent-≃ (pe (𝓤 ⊔ 𝓥)) (fe (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)) (lift 𝓤 Y) (lift 𝓥 P) j) ⟩
        (lift 𝓤 Y ≡ lift 𝓥 P)  ■
  b : (Σ \(Y : 𝓥 ̇) → Y ≃ P) ≃ (Σ \(Y : 𝓥 ̇) → lift 𝓤 Y ≡ lift 𝓥 P)
  b = Σ-cong a
  c : is-prop (Σ \(Y : 𝓥 ̇) → Y ≃ P)
  c = equiv-to-prop b (prop-fiber-lift pe fe (lift 𝓥 P) j)

propositional-resizing-is-a-prop' : PropExt → FunExt → is-prop (propositional-resizing 𝓤 𝓥)
propositional-resizing-is-a-prop' {𝓤} {𝓥} pe fe =  Π-is-prop (fe (𝓤 ⁺) (𝓥 ⁺ ⊔ 𝓤))
                                                     (λ P → Π-is-prop (fe 𝓤 (𝓥 ⁺ ⊔ 𝓤))
                                                     (λ i → prop-has-size-is-a-prop pe fe P i 𝓥))
\end{code}

Impredicativity. We begin with this strong notion, which says that the
type Ω 𝓤 of truth values in the universe 𝓤 has a copy in any successor
universe (i.e. in all universes except the first).

\begin{code}

is-impredicative+ : (𝓤 : Universe) → 𝓤ω
is-impredicative+ 𝓤 = (𝓥 : Universe) → (Ω 𝓤) has-size (𝓥 ⁺)

universes-are-impredicative+ : Propositional-resizing → PropExt → FunExt
                             → is-impredicative+ 𝓤
universes-are-impredicative+ {𝓤} ρ pe fe 𝓥 = Ω 𝓥 , qinveq φ (γ , γφ , φγ)
 where
  φ : Ω 𝓥 → Ω 𝓤
  φ (Q , j) = resize ρ Q j , resize-is-a-prop ρ Q j
  γ : Ω 𝓤 → Ω 𝓥
  γ (P , i) = resize ρ P i , resize-is-a-prop ρ P i
  φγ : (p : Ω 𝓤) → φ (γ p) ≡ p
  φγ (P , i) = Ω-ext (fe 𝓤 𝓤) (pe 𝓤)
               (from-resize ρ P i ∘ from-resize ρ (resize ρ P i) (resize-is-a-prop ρ P i))
               (to-resize ρ (resize ρ P i) (resize-is-a-prop ρ P i) ∘ to-resize ρ P i)
  γφ : (q : Ω 𝓥) → γ (φ q) ≡ q
  γφ (Q , j) = Ω-ext (fe 𝓥 𝓥) (pe 𝓥)
               (from-resize ρ Q j ∘ from-resize ρ (resize ρ Q j) (resize-is-a-prop ρ Q j))
               (to-resize ρ (resize ρ Q j) (resize-is-a-prop ρ Q j) ∘ to-resize ρ Q j)

\end{code}

A more standard notion of impredicativity is that the type Ω 𝓤 of
truth-values in the universe 𝓤 itself lives in 𝓤.

\begin{code}

is-impredicative : (𝓤 : Universe) → 𝓤 ⁺ ̇
is-impredicative 𝓤 = (Ω 𝓤) has-size 𝓤

\end{code}

Propositional resizing doesn't imply that the first universe 𝓤₀ is
impredicative, but it does imply that all other, successor, universes
𝓤 ⁺ are.

\begin{code}

successor-universes-are-impredicative : Propositional-resizing → PropExt → FunExt
                                      → is-impredicative (𝓤 ⁺)
successor-universes-are-impredicative {𝓤} ρ pe fe = universes-are-impredicative+ ρ pe fe 𝓤

\end{code}

But excluded middle does give the impredicativity of the first
universe, and of all other universes, of course:

\begin{code}

is-globally-impredicative : (𝓤 : Universe) → 𝓤ω
is-globally-impredicative 𝓤 = (𝓥 : Universe) → (Ω 𝓤) has-size 𝓥

universes-impredicative-from-EM : LEM 𝓤 → propext 𝓤 → funext 𝓤 𝓤
                                → is-globally-impredicative 𝓤
universes-impredicative-from-EM {𝓤} em pe fe 𝓥 =
 (𝟙 {𝓥} + 𝟙 {𝓥}) ,
 qinveq φ
 ((λ p → γ p (em p)) ,
  (λ z → γφ z (em (φ z))) ,
  (λ p → φγ p (em p)))
 where
  φ : 𝟙 + 𝟙 → Ω 𝓤
  φ (inl x) = ⊥
  φ (inr y) = ⊤
  γ : (p : Ω 𝓤) → decidable (p holds) → 𝟙 + 𝟙
  γ p (inl h) = inr *
  γ p (inr n) = inl *
  γφ : (z : 𝟙 + 𝟙) (d : decidable ((φ z) holds)) → γ (φ z) d ≡ z
  γφ (inl x) (inl h) = 𝟘-elim h
  γφ (inl x) (inr n) = ap inl (𝟙-is-prop * x)
  γφ (inr y) (inl h) = ap inr (𝟙-is-prop * y)
  γφ (inr y) (inr n) = 𝟘-elim (n *)
  φγ : (p : Ω 𝓤) (d : decidable (p holds)) → φ (γ p d) ≡ p
  φγ p (inl h) = (true-is-equal-⊤  pe fe (p holds) (holds-is-prop p) h)⁻¹
  φγ p (inr n) = (false-is-equal-⊥ pe fe (p holds) (holds-is-prop p) n)⁻¹

is-impredicative₀ : (𝓤 : Universe) → 𝓤 ⁺ ̇
is-impredicative₀ 𝓤 = (Ω 𝓤) has-size 𝓤₀

universes-impredicative-from-EM₀ : LEM 𝓤 → propext 𝓤 → funext 𝓤 𝓤
                                 → is-impredicative₀ 𝓤
universes-impredicative-from-EM₀ {𝓤} em pe fe = universes-impredicative-from-EM em pe fe 𝓤₀

\end{code}

What we get with propositional resizing is that all types of
propositions of any universe 𝓤 are equivalent to Ω 𝓤₀, which lives in
the second universe 𝓤₁:

\begin{code}

is-impredicative₁ : (𝓤 : Universe) → 𝓤 ⁺ ⊔ 𝓤₂ ̇
is-impredicative₁ 𝓤 = (Ω 𝓤) has-size 𝓤₁

all-universes-are-impredicative₁ : Propositional-resizing → PropExt → FunExt
                                 → is-impredicative₁ 𝓤
all-universes-are-impredicative₁ {𝓤} ρ pe fe = universes-are-impredicative+ ρ pe fe 𝓤₀

All-universes-are-impredicative₁ : Propositional-resizing → PropExt → FunExt
                                 → Ω 𝓤 ≃ Ω 𝓤₀
All-universes-are-impredicative₁ {𝓤} ρ pe fe = ≃-sym (pr₂ (all-universes-are-impredicative₁ {𝓤} ρ pe fe))

Ω-𝓤₀-lives-in-𝓤₁ : universe-of (Ω 𝓤₀) ≡ 𝓤₁
Ω-𝓤₀-lives-in-𝓤₁ = refl

\end{code}

With propositional resizing, we have that any universe is a retract of
any larger universe.

\begin{code}

lift-is-section : Univalence
                → Propositional-resizing
                → (𝓤 𝓥 : Universe)
                → is-section (lift {𝓤} 𝓥)
lift-is-section ua R 𝓤 𝓥 = (r , rs)
 where
  s : 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇
  s = lift 𝓥
  e : is-embedding s
  e = lift-is-embedding ua
  F : 𝓤 ⊔ 𝓥 ̇ → 𝓤 ̇
  F Y = resize R (fiber s Y) (e Y)
  f : (Y : 𝓤 ⊔ 𝓥 ̇) → F Y → fiber s Y
  f Y = from-resize R (fiber s Y) (e Y)
  r : 𝓤 ⊔ 𝓥 ̇ → 𝓤 ̇
  r Y = (p : F Y) → pr₁ (f Y p)
  rs : (X : 𝓤 ̇) → r (s X) ≡ X
  rs X = γ
   where
    g : (Y : 𝓤 ⊔ 𝓥 ̇) → fiber s Y → F Y
    g Y = to-resize R (fiber s Y) (e Y)
    u : F (s X)
    u = g (s X) (X , refl)
    v : fiber s (s X)
    v = f (s X) u
    i : (Y : 𝓤 ⊔ 𝓥 ̇) → is-prop (F Y)
    i Y = resize-is-a-prop R (fiber s Y) (e Y)
    X' : 𝓤 ̇
    X' = pr₁ v
    a : r (s X) ≃ X'
    a = prop-indexed-product (FunExt-from-Univalence ua 𝓤 𝓤) (i (s X)) u
    b : s X' ≡ s X
    b = pr₂ v
    c : X' ≡ X
    c = embedding-lc s e b
    d : r (s X) ≃ X
    d = transport (λ - → r (s X) ≃ -) c a
    γ : r (s X) ≡ X
    γ = eqtoid (ua 𝓤) (r (s X)) X d

\end{code}

We remark that for types that are not sets, sections are not
automatically embeddings (Shulman 2015, Logical Methods in Computer
Science, April 27, 2017, Volume 12, Issue 3,
https://lmcs.episciences.org/2027 , Theorem 3.10).

\begin{code}

universe-retract' : Univalence
                  → Propositional-resizing
                  → (𝓤 𝓥 : Universe)
                  → Σ \(ρ : retract 𝓤 ̇ of (𝓤 ⊔ 𝓥 ̇)) → is-embedding (section ρ)
universe-retract' ua R 𝓤 𝓥 = (pr₁ a , lift 𝓥 , pr₂ a) , lift-is-embedding ua
 where
  a : Σ \(lower : 𝓤 ⊔ 𝓥 ̇ → 𝓤 ̇) → lower ∘ lift 𝓥 ∼ id
  a = lift-is-section ua R 𝓤 𝓥

\end{code}

A more conceptual version of the above construction is in the module
InjectiveTypes (which was discovered first - this is just an unfolding
of that construction).

Question. If we assume that we have such a retraction, does weak
propositional resizing follow?

The following construction is due to Voevodsky, but we use the
resizing axiom rather than his rules (and we work with non-cumulative
universes).

\begin{code}

∥_∥⁺ : 𝓤 ̇ → 𝓤 ⁺ ̇
∥ X ∥⁺ = (P : universe-of X ̇) → is-prop P → (X → P) → P

∥∥⁺-is-a-prop : FunExt → {X : 𝓤 ̇} → is-prop (∥ X ∥⁺)
∥∥⁺-is-a-prop fe = Π-is-prop (fe _ _)
                   (λ P → Π-is-prop (fe _ _)
                           (λ i → Π-is-prop (fe _ _)
                                    (λ u → i)))

∣_∣⁺ : {X : 𝓤 ̇} → X → ∥ X ∥⁺
∣ x ∣⁺ = λ P i u → u x

∥∥⁺-rec : {X P : 𝓤 ̇} → is-prop P → (X → P) → ∥ X ∥⁺ → P
∥∥⁺-rec {𝓤} {X} {P} i u s = s P i u

resizing-truncation : FunExt → Propositional-resizing → propositional-truncations-exist
resizing-truncation fe R = record {
    ∥_∥          = λ {𝓤} X → resize R ∥ X ∥⁺ (∥∥⁺-is-a-prop fe)
  ; ∥∥-is-a-prop = λ {𝓤} {X} → resize-is-a-prop R ∥ X ∥⁺ (∥∥⁺-is-a-prop fe)
  ; ∣_∣          = λ {𝓤} {X} x → to-resize R ∥ X ∥⁺ (∥∥⁺-is-a-prop fe) ∣ x ∣⁺
  ; ∥∥-rec       = λ {𝓤} {𝓥} {X} {P} i u s → from-resize R P i
                                              (∥∥⁺-rec (resize-is-a-prop R P i)
                                                       (to-resize R P i ∘ u)
                                                       (from-resize R ∥ X ∥⁺ (∥∥⁺-is-a-prop fe) s))
  }

\end{code}

Images:

\begin{code}

module Image
        {𝓤 𝓥 : Universe}
        {X : 𝓤 ̇}
        {Y : 𝓥 ̇}
        (fe : FunExt)
        (R : Propositional-resizing)
       where

 open PropositionalTruncation (resizing-truncation fe R)

 image : (X → Y) → 𝓥 ̇
 image f = Σ \y → resize (R {𝓤 ⊔ 𝓥} {𝓥}) (∃ \x → f x ≡ y) ∥∥-is-a-prop

 restriction : (f : X → Y) → image f → Y
 restriction f (y , _) = y

 restriction-embedding : (f : X → Y) → is-embedding(restriction f)
 restriction-embedding f = pr₁-embedding (λ y → resize-is-a-prop R _ _)

 corestriction : (f : X → Y) → X → image f
 corestriction f x = f x , to-resize R _ _ ∣ x , refl ∣

\end{code}

TODO. Prove the properties / perform the constructions in
UF-ImageAndSurjection. Better: reorganize the code so that reproving
is not necessary.

\end{code}
