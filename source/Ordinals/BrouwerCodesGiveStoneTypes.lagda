Martin Escardo, 21st October 2026.

We show that the compact totally separated interpretation Κ of the
Brouwer ordinal codes, defined in the module
Ordinals.BrouwerCodesDiscreteAndCompactInterpretations, gives Stone
types, in the sense of the module TypeTopology.StoneTypes, assuming
that ¬ WLPO holds.

The hypothesis ¬ WLPO is used only for the limit constructor, and it
can't be dropped, because the code L (λ n → Z) is interpreted as a type
equivalent to ℕ∞, which is not a Stone type in a model of choice, as
discussed in the module TypeTopology.StoneTypes.

The successor constructor reduces to the binary sums of the above
module, and the finite part of the limit constructor is handled by its
criteria, which say when a homomorphism is an evaluation. Here we show
that the squashed sum of a family of compact pre-Stone types is a
Stone type if ¬ WLPO holds, which is the interpretation of the limit
constructor, where the hypothesis plays the same role as for ℕ∞, by
giving the ¬¬-existence of a modulus of continuity. That the clopens
form a discrete type, which a Stone type requires in addition, comes
from the compactness of the interpretation.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc

module Ordinals.BrouwerCodesGiveStoneTypes
        (fe : Fun-Ext)
        (pt : propositional-truncations-exist)
       where

private
 fe' : FunExt
 fe' 𝓤 𝓥 = fe

 fe₀ : funext₀
 fe₀ = fe

open import CoNaturals.Type
open import InjectiveTypes.Blackboard fe'
open import MLTT.Two-Properties
 renaming (max𝟚 to infixl 39 _∨₂_ ;
           min𝟚 to infixl 40 _∧₂_ ;
           complement to infix 41 ¬₂_)
open import Naturals.Order renaming (max to maxℕ)
open import Notation.CanonicalMap
open import Notation.Order
open import Taboos.WLPO
open import TypeTopology.CompactTypes
open import TypeTopology.StoneTypes fe pt
open import TypeTopology.WeaklyCompactTypes fe' pt using (_≤̇_)
open import UF.Base
open import UF.DiscreteAndSeparated
open import UF.Embeddings
open import UF.Equiv
open import UF.Subsingletons

\end{code}

We begin by considering the limit step. We work with the squashed sum
Σ¹ X of the module TypeTopology.SquashedSum, whose points are the
pairs (u , g) with u : ℕ∞ and with g assigning an element of the type
X (size ψ) to every finiteness witness ψ, so that the fiber over a
finite point ι k amounts to X k and the fiber over ∞ is a singleton.

\begin{code}

open import TypeTopology.SquashedSum fe'
open import UF.PropIndexedPiSigma

module _ (X : ℕ → 𝓤 ̇ )
         (κ : (n : ℕ) → is-compact∙ (X n))
         (δ : (n : ℕ) → is-pre-stone-type (X n))
       where

 private
  Y : ℕ∞ → 𝓤 ̇
  Y = X / ι

  ι-is-embedding : is-embedding ι
  ι-is-embedding = ℕ-to-ℕ∞-is-embedding fe₀

  Y-is-compact∙ : (u : ℕ∞) → is-compact∙ (Y u)
  Y-is-compact∙ = /ι-is-compact∙ X κ

  summands-are-pre-stone-types : (k : ℕ) → is-pre-stone-type (Y (ι k))
  summands-are-pre-stone-types k =
   equiv-to-pre-stone-type
    (Π-extension-property X ι ι-is-embedding k)
    (δ k)

  pullback : C ℕ∞ → C (Σ¹ X)
  pullback q = q ∘ Σ¹-base

\end{code}

Two points of the squashed sum with the same finite base are equal as
soon as their fibers agree at one witness of finiteness, because the
fiber over a finite point is a product indexed by a proposition.

\begin{code}

  Σ¹-＝-criterion : (v : ℕ∞) (k : ℕ) (e : ι k ＝ v) (g : Y v) (a : Y (ι k))
                  → g (k , e) ＝ a (k , refl)
                  → (v , g) ＝ (ι k , a)
  Σ¹-＝-criterion v k refl g a q = ap (λ - → (ι k , -)) I
   where
    I : g ＝ a
    I = equivs-are-lc
         (Π-proj (k , refl))
         (Π-extension-equivalence X ι ι-is-embedding k)
         q

\end{code}

The quantification of a clopen over a fiber is decidable, because the
fibers are compact, and so a clopen p of the squashed sum gives two
clopens of ℕ∞, namely all p, which says that p holds everywhere in the
fiber, and some p, which says that it holds somewhere in it. Over ∞
they agree with the value of p at the only point of the fiber.

\begin{code}

  private
   fiber-data : (p : C (Σ¹ X)) (u : ℕ∞) → 𝓤 ̇
   fiber-data p u = Σ y ꞉ Y u , (p (u , y) ＝ ₁ → (y' : Y u) → p (u , y') ＝ ₁)

   all' : (p : C (Σ¹ X)) (u : ℕ∞) → fiber-data p u → 𝟚
   all' p u (y , _) = p (u , y)

   data-at : (p : C (Σ¹ X)) (u : ℕ∞) → fiber-data p u
   data-at p u = Y-is-compact∙ u (λ y → p (u , y))

  all : C (Σ¹ X) → C ℕ∞
  all p u = all' p u (data-at p u)

  all-gives-all : (p : C (Σ¹ X)) (u : ℕ∞)
                → all p u ＝ ₁ → (y : Y u) → p (u , y) ＝ ₁
  all-gives-all p u = I (data-at p u)
   where
    I : (c : fiber-data p u) → all' p u c ＝ ₁ → (y : Y u) → p (u , y) ＝ ₁
    I (y , φ) = φ

  all-from-all : (p : C (Σ¹ X)) (u : ℕ∞)
               → ((y : Y u) → p (u , y) ＝ ₁)
               → all p u ＝ ₁
  all-from-all p u = I (data-at p u)
   where
    I : (c : fiber-data p u) → ((y : Y u) → p (u , y) ＝ ₁) → all' p u c ＝ ₁
    I (y , _) φ = φ y

  all-at-∞ : (p : C (Σ¹ X)) (y : Y ∞) → all p ∞ ＝ p (∞ , y)
  all-at-∞ p y = 𝟚-equality-cases I II
   where
    I : all p ∞ ＝ ₀ → all p ∞ ＝ p (∞ , y)
    I d = all p ∞   ＝⟨ d ⟩
          ₀         ＝⟨ IV ⁻¹ ⟩
          p (∞ , y) ∎
     where
      III : p (∞ , y) ＝ ₁ → (y' : Y ∞) → p (∞ , y') ＝ ₁
      III d y' = transport (λ - → p (∞ , -) ＝ ₁)
                  (singletons-are-props (ι-∞-is-singleton X) y y')
                  d

      IV : p (∞ , y) ＝ ₀
      IV = different-from-₁-equal-₀
            (λ (s : p (∞ , y) ＝ ₁)
               → equal-₀-different-from-₁ d (all-from-all p ∞ (III s)))

    II : all p ∞ ＝ ₁ → all p ∞ ＝ p (∞ , y)
    II d = all p ∞   ＝⟨ d ⟩
           ₁         ＝⟨ (all-gives-all p ∞ d y)⁻¹ ⟩
           p (∞ , y) ∎

  some : C (Σ¹ X) → C ℕ∞
  some p u = ¬₂ all (¬̇ p) u

  not-some-gives-none : (p : C (Σ¹ X)) (u : ℕ∞)
                      → some p u ＝ ₀ → (y : Y u) → p (u , y) ＝ ₀
  not-some-gives-none p u d y =
   complement-lc (p (u , y)) ₀
    (all-gives-all (¬̇ p) u (complement-lc (all (¬̇ p) u) ₁ d) y)

  some-at-∞ : (p : C (Σ¹ X)) (y : Y ∞) → some p ∞ ＝ p (∞ , y)
  some-at-∞ p y = some p ∞        ＝⟨refl⟩
                  ¬₂ all (¬̇ p) ∞  ＝⟨ ap ¬₂_ (all-at-∞ (¬̇ p) y) ⟩
                  ¬₂ ¬₂ p (∞ , y) ＝⟨ complement-involutive (p (∞ , y)) ⟩
                  p (∞ , y)       ∎

\end{code}

The following is the dependent density lemma for ℕ∞ applied to the
family of clopens of the fibers, whose members are ¬¬-separated.

\begin{code}

  Σ¹-density : (p : C (Σ¹ X))
             → ((n : ℕ) (y : Y (ι n)) → p (ι n , y) ＝ ₁)
             → ((y : Y ∞) → p (∞ , y) ＝ ₁)
             → (x : Σ¹ X) → p x ＝ ₁
  Σ¹-density p f g (v , y) = happly (ℕ∞-ddensity fe₀ I II III v) y
   where
    I : {u : ℕ∞} → is-¬¬-separated (Y u → 𝟚)
    I = Π-is-¬¬-separated fe (λ _ → 𝟚-is-¬¬-separated)

    II : (n : ℕ) → (λ (y : Y (ι n)) → p (ι n , y)) ＝ (λ _ → ₁)
    II n = dfunext fe (f n)

    III : (λ (y : Y ∞) → p (∞ , y)) ＝ (λ _ → ₁)
    III = dfunext fe g

\end{code}

Now let h be a homomorphism of the clopens of the squashed sum into
the booleans. Its composite with the pullback of the clopens of ℕ∞
is a homomorphism, which gives the base u of the only point at which h
can be the evaluation, together with the facts about u established in
the module TypeTopology.StoneTypes. The fiber component of the point
comes from the summands, which is possible because the fiber over u is
a product indexed by the witnesses that u is finite.

\begin{code}

  module _ (h : C (Σ¹ X) → 𝟚)
           (i : is-bhom h)
         where

   private
    open bhom-properties h i

    h₀ : C ℕ∞ → 𝟚
    h₀ = h ∘ pullback

    i₀ : is-bhom h₀
    i₀ = preserves-₀ ,
         preserves-₁ ,
         (λ q q' → preserves-∧ (pullback q) (pullback q')) ,
         (λ q q' → preserves-∨ (pullback q) (pullback q'))

    open bhom-on-ℕ∞ h₀ i₀

    σ : (k : ℕ) (x : Σ¹ X) → pullback (singleton k) x ＝ ₁ → Y (ι k)
    σ k (v , g) d = transport Y (singleton-property₀ k v d) g

    jσ : (k : ℕ) (x : Σ¹ X) (d : pullback (singleton k) x ＝ ₁)
       → (ι k , σ k x d) ＝ x
    jσ k (v , g) d = (to-Σ-＝ (singleton-property₀ k v d , refl))⁻¹

    summand : (k : ℕ)
            → u ＝ ι k
            → Σ a ꞉ Y (ι k) , ((p : C (Σ¹ X)) → h p ＝ p (ι k , a))
    summand k e = hom-is-evaluation-criterion
                   (pullback (singleton k))
                   (λ a → ι k , a)
                   (σ k)
                   (jσ k)
                   (summands-are-pre-stone-types k)
                   h i I
     where
      I : h (pullback (singleton k)) ＝ ₁
      I = h (pullback (singleton k)) ＝⟨ h-at-finite k e (singleton k) ⟩
          singleton k u              ＝⟨ ap (singleton k) e ⟩
          singleton k (ι k)          ＝⟨ singleton-property₁ k ⟩
          ₁                          ∎

    summand-point : (k : ℕ) → u ＝ ι k → Y (ι k)
    summand-point k e = pr₁ (summand k e)

    summand-evaluation : (k : ℕ) (e : u ＝ ι k)
                       → (p : C (Σ¹ X)) → h p ＝ p (ι k , summand-point k e)
    summand-evaluation k e = pr₂ (summand k e)

    point-fiber : Y u
    point-fiber ψ = summand-point (size ψ) ((size-property ψ)⁻¹) (size ψ , refl)

    point : Σ¹ X
    point = u , point-fiber

    finite-case : (k : ℕ) (e : u ＝ ι k) (p : C (Σ¹ X)) → h p ＝ p point
    finite-case k e p =
     h p                         ＝⟨ summand-evaluation k e p ⟩
     p (ι k , summand-point k e) ＝⟨ ap p (I ⁻¹) ⟩
     p point                     ∎
     where
      I : point ＝ (ι k , summand-point k e)
      I = Σ¹-＝-criterion u k (e ⁻¹) point-fiber (summand-point k e)
           (ap (λ - → summand-point k - (k , refl)) (⁻¹-involutive e))

\end{code}

In the case where the base is ∞, the homomorphism gives the value ₁ to
every pullback of an upper set, and then the value of h at p is decided
by a modulus of all p when p is ₁ at the point at infinity, and by a
modulus of some p when p is ₀ at that point. In both cases the density
of the finite points together with ∞ turns the information at those
points into an inequality of clopens.

\begin{code}

    ∞-case-₁ : u ＝ ∞
             → (p : C (Σ¹ X)) (m : ℕ)
             → m is-modulus-of all p
             → all p ∞ ＝ ₁
             → h p ＝ ₁
    ∞-case-₁ e p m φ r = ≤₂-criterion-converse
                          (monotone II)
                          (h-at-upper-sets e m)
     where
      I : (x : Σ¹ X) → (¬̇ pullback (↑ m) ∨̇ p) x ＝ ₁
      I = Σ¹-density (¬̇ pullback (↑ m) ∨̇ p) III IV
       where
        III : (n : ℕ) (y : Y (ι n)) → (¬̇ pullback (↑ m) ∨̇ p) (ι n , y) ＝ ₁
        III n y = 𝟚-equality-cases v vi
         where
          v : ι (ι n) m ＝ ₀ → (¬̇ pullback (↑ m) ∨̇ p) (ι n , y) ＝ ₁
          v s = max𝟚-lemma-converse (inl (ap ¬₂_ s))

          vi₀ : ι (ι n) m ＝ ₁ → all p (ι n) ＝ ₁
          vi₀ s = all p (ι n) ＝⟨ φ n (<-coarser-than-≤ m n (⊏-gives-< m n s)) ⟩
                  all p ∞     ＝⟨ r ⟩
                  ₁           ∎

          vi : ι (ι n) m ＝ ₁ → (¬̇ pullback (↑ m) ∨̇ p) (ι n , y) ＝ ₁
          vi s = max𝟚-lemma-converse
                  (inr (all-gives-all p (ι n) (vi₀ s) y))

        IV : (y : Y ∞) → (¬̇ pullback (↑ m) ∨̇ p) (∞ , y) ＝ ₁
        IV y = max𝟚-lemma-converse (inr (all-gives-all p ∞ r y))

      II : pullback (↑ m) ≤̇ p
      II x = ≤₂-criterion III
       where
        III : pullback (↑ m) x ＝ ₁ → p x ＝ ₁
        III s = p x                        ＝⟨refl⟩
                ₀ ∨₂ p x                   ＝⟨ ap (λ - → ¬₂ - ∨₂ p x) (s ⁻¹) ⟩
                ¬₂ pullback (↑ m) x ∨₂ p x ＝⟨ I x ⟩
                ₁                          ∎

    ∞-case-₀ : u ＝ ∞
             → (p : C (Σ¹ X)) (m : ℕ)
             → m is-modulus-of some p
             → some p ∞ ＝ ₀
             → h p ＝ ₀
    ∞-case-₀ e p m φ r = ₀-minimal (transport (λ - → h p ≤ -) III (monotone II))
     where
      I : (x : Σ¹ X) → (¬̇ p ∨̇ ¬̇ pullback (↑ m)) x ＝ ₁
      I = Σ¹-density (¬̇ p ∨̇ ¬̇ pullback (↑ m)) IV V
       where
        IV : (n : ℕ) (y : Y (ι n)) → (¬̇ p ∨̇ ¬̇ pullback (↑ m)) (ι n , y) ＝ ₁
        IV n y = 𝟚-equality-cases v vi
         where
          v : ι (ι n) m ＝ ₀ → (¬̇ p ∨̇ ¬̇ pullback (↑ m)) (ι n , y) ＝ ₁
          v s = max𝟚-lemma-converse (inr (ap ¬₂_ s))

          vi₀ : ι (ι n) m ＝ ₁ → some p (ι n) ＝ ₀
          vi₀ s = some p (ι n) ＝⟨ φ n (<-coarser-than-≤ m n (⊏-gives-< m n s)) ⟩
                  some p ∞     ＝⟨ r ⟩
                  ₀            ∎

          vi : ι (ι n) m ＝ ₁ → (¬̇ p ∨̇ ¬̇ pullback (↑ m)) (ι n , y) ＝ ₁
          vi s = max𝟚-lemma-converse
                  (inl (ap ¬₂_ (not-some-gives-none p (ι n) (vi₀ s) y)))

        V : (y : Y ∞) → (¬̇ p ∨̇ ¬̇ pullback (↑ m)) (∞ , y) ＝ ₁
        V y = max𝟚-lemma-converse
               (inl (ap ¬₂_ (not-some-gives-none p ∞ r y)))

      II : p ≤̇ ¬̇ pullback (↑ m)
      II x = ≤₂-criterion IV
       where
        IV : p x ＝ ₁ → ¬₂ pullback (↑ m) x ＝ ₁
        IV s = ¬₂ pullback (↑ m) x           ＝⟨refl⟩
               ₀ ∨₂ ¬₂ pullback (↑ m) x      ＝⟨ ap (λ - → ¬₂ - ∨₂ _) (s ⁻¹) ⟩
               ¬₂ p x ∨₂ ¬₂ pullback (↑ m) x ＝⟨ I x ⟩
               ₁                             ∎

      III : h (¬̇ pullback (↑ m)) ＝ ₀
      III = h (¬̇ pullback (↑ m))    ＝⟨ preserves-complement (pullback (↑ m)) ⟩
            ¬₂ (h (pullback (↑ m))) ＝⟨ ap ¬₂_ (h-at-upper-sets e m) ⟩
            ¬₂ ₁                    ＝⟨refl⟩
            ₀                       ∎

    ∞-case : u ＝ ∞
           → (p : C (Σ¹ X)) (m m' : ℕ)
           → m is-modulus-of all p
           → m' is-modulus-of some p
           → h p ＝ p point
    ∞-case e p m m' φ φ' = 𝟚-equality-cases II III
     where
      y : Y ∞
      y = transport Y e point-fiber

      I : p point ＝ all p ∞
      I = p point   ＝⟨ ap p (to-Σ-＝ (e , refl)) ⟩
          p (∞ , y) ＝⟨ (all-at-∞ p y)⁻¹ ⟩
          all p ∞   ∎

      II : all p ∞ ＝ ₀ → h p ＝ p point
      II r = h p     ＝⟨ ∞-case-₀ e p m' φ' IV ⟩
             ₀       ＝⟨ r ⁻¹ ⟩
             all p ∞ ＝⟨ I ⁻¹ ⟩
             p point ∎
       where
        IV : some p ∞ ＝ ₀
        IV = some p ∞  ＝⟨ some-at-∞ p y ⟩
             p (∞ , y) ＝⟨ (all-at-∞ p y)⁻¹ ⟩
             all p ∞   ＝⟨ r ⟩
             ₀         ∎

      III : all p ∞ ＝ ₁ → h p ＝ p point
      III r = h p     ＝⟨ ∞-case-₁ e p m φ r ⟩
              ₁       ＝⟨ r ⁻¹ ⟩
              all p ∞ ＝⟨ I ⁻¹ ⟩
              p point ∎

   h-is-an-evaluation : ¬ WLPO → Σ v ꞉ Σ¹ X , ((p : C (Σ¹ X)) → h p ＝ p v)
   h-is-an-evaluation nwlpo = point , I
    where
     I : (p : C (Σ¹ X)) → h p ＝ p point
     I p = 𝟚-is-¬¬-separated (h p) (p point) II
      where
       II : ¬¬ (h p ＝ p point)
       II ν = ¬WLPO-gives-¬¬-has-modulus nwlpo (all p) IV
        where
         III : u ＝ ∞
         III = not-finite-is-∞ fe₀ (λ k e → ν (finite-case k e p))

         IV : ¬ has-modulus (all p)
         IV (m , φ) = ¬WLPO-gives-¬¬-has-modulus nwlpo (some p) V
          where
           V : ¬ has-modulus (some p)
           V (m' , φ') = ν (∞-case III p m m' φ φ')

 Σ¹-is-stone-type : ¬ WLPO → is-stone-type (Σ¹ X)
 Σ¹-is-stone-type nwlpo =
  stone-criterion
   (Π-compact-gives-discrete-clopen-algebra
     (compact-types-are-Π-compact
       (compact∙-types-are-compact (Σ¹-compact∙ X κ))))
   (Σ¹-is-totally-separated X
     (λ n → pre-stone-types-are-totally-separated (δ n)))
   (λ h i → h-is-an-evaluation h i nwlpo)

\end{code}

The sum of a family over the two-point type, which is the form that a
binary sum takes in ordinal arithmetic, is a binary sum, and so the
successor step is a corollary of the binary sums of the module
TypeTopology.StoneTypes. The library function alternative-+ does this
for families over 𝟚 rather than over 𝟙 + 𝟙, and the change of variable
would be longer than the equivalence given here.

\begin{code}

Σ-over-two-is-stone-type
 : (A : 𝟙 {𝓤} + 𝟙 {𝓥} → 𝓦 ̇ )
 → is-stone-type (A (inl ⋆))
 → is-stone-type (A (inr ⋆))
 → is-stone-type (Σ A)
Σ-over-two-is-stone-type A ζ₀ ζ₁
 = equiv-to-stone-type I (+-is-stone-type ζ₀ ζ₁)
 where
  f : Σ A → A (inl ⋆) + A (inr ⋆)
  f (inl ⋆ , z) = inl z
  f (inr ⋆ , z) = inr z

  g : A (inl ⋆) + A (inr ⋆) → Σ A
  g (inl z) = inl ⋆ , z
  g (inr z) = inr ⋆ , z

  gf : g ∘ f ∼ id
  gf (inl ⋆ , z) = refl
  gf (inr ⋆ , z) = refl

  fg : f ∘ g ∼ id
  fg (inl z) = refl
  fg (inr z) = refl

  I : Σ A ≃ A (inl ⋆) + A (inr ⋆)
  I = qinveq f (g , gf , fg)

\end{code}

The underlying type of a successor is a sum of a family over the
two-point type, and that of a limit is the squashed sum. So the two
steps above, together with that for the one-point type of the module
TypeTopology.StoneTypes, give by induction on Brouwer codes that the Κ
interpretation produces Stone types.

\begin{code}

open import Ordinals.BrouwerCodes
open import Ordinals.BrouwerCodesDiscreteAndCompactInterpretations fe'
open import Ordinals.ToppedArithmetic fe'
open import Ordinals.ToppedType fe'
open import Ordinals.Underlying

Κ-is-stone-type : ¬ WLPO → (b : B) → is-stone-type ⟨ Κ b ⟩
Κ-is-stone-type nwlpo Z     = 𝟙-is-stone-type
Κ-is-stone-type nwlpo (S b) =
 Σ-over-two-is-stone-type
  (λ x → ⟨ cases (λ _ → Κ b) (λ _ → 𝟙ᵒ) x ⟩)
  (Κ-is-stone-type nwlpo b)
  𝟙-is-stone-type
Κ-is-stone-type nwlpo (L b) =
 Σ¹-is-stone-type
  (λ n → ⟨ Κ (b n) ⟩)
  (λ n → Κ-compact∙ (b n))
  (λ n → stone-types-are-pre-stone-types (Κ-is-stone-type nwlpo (b n)))
  nwlpo

\end{code}
