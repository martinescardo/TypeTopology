Martin Escardo 25th October 2018.

The type of partial elements of a type (or lifting).

Cf. my former student Cory Knapp's PhD thesis and our CSL'2017 paper
https://www.cs.bham.ac.uk/~mhe/papers/partial-elements-and-recursion.pdf
But there are also new results and observations here, as well as
different approaches.

Under development.

\begin{code}

{-# OPTIONS --without-K --exact-split #-}

module PartialElements where

open import SpartanMLTT
open import UF-Base
open import UF-Subsingletons hiding (⊥)
open import UF-Subsingletons-FunExt
open import UF-Subsingletons-Equiv
open import UF-Retracts
open import UF-Embedding
open import UF-Equiv
open import UF-Equiv-FunExt
open import UF-EquivalenceExamples
open import UF-FunExt
open import UF-Univalence
open import UF-UA-FunExt
open import UF-StructureIdentityPrinciple

\end{code}

We discuss the type 𝓛 X of partial elements of a type X, also called
the lifting of X.  The domain of definition of a partial element is
taken to be in an arbitrary, fixed universe 𝓣.

\begin{code}

module lifting (𝓣 : Universe) where

 𝓛 : 𝓤 ̇ → 𝓤 ⊔ 𝓣 ⁺ ̇
 𝓛 X = Σ \(P : 𝓣 ̇) → (P → X) × is-prop P

 is-defined : {X : 𝓤 ̇} → 𝓛 X → 𝓣 ̇

 is-defined (P , i , φ) = P

 being-defined-is-a-prop : {X : 𝓤 ̇} (l : 𝓛  X) → is-prop (is-defined l)
 being-defined-is-a-prop (P , φ , i) = i

 value : {X : 𝓤 ̇} (l : 𝓛  X) → is-defined l → X
 value (P , φ , i) = φ

\end{code}

The "total" elements of 𝓛 X:

\begin{code}

 η : {X : 𝓤 ̇} → X → 𝓛 X
 η x = 𝟙 , (λ _ → x) , 𝟙-is-prop

\end{code}

Its "undefined" element:

\begin{code}

 ⊥ : {X : 𝓤 ̇} → 𝓛 X
 ⊥ = 𝟘 , unique-from-𝟘 , 𝟘-is-prop

\end{code}

##

Our strategy to show that η is an embedding (has subsingleton fibers)
is to exhibit it as the composite of two embeddings (the first of
which is actually an equivalence).

A perhaps better, and much shorter, proof is given later (added 7th
Dec 2018), but the following original proof is still interesting (and
assumes functional and propositional extensionality rather than full
univalence).

\begin{code}

 𝓚 : 𝓤 ̇ → 𝓤 ⊔ 𝓣 ⁺ ̇
 𝓚 X = Σ \(P : 𝓣 ̇) → (P → X) × is-singleton P

 κ : {X : 𝓤 ̇} → X → 𝓚 X
 κ x = 𝟙 , (λ _ → x) , 𝟙-is-singleton

 ζ : (X : 𝓤 ̇) (P : 𝓣 ̇) → (P → X) × is-singleton P → (P → X) × is-prop P
 ζ X P (φ , i) = φ , singletons-are-props i

 𝓚→𝓛 : (X : 𝓤 ̇) → 𝓚 X → 𝓛 X
 𝓚→𝓛 X = NatΣ (ζ X)

 η-composite : funext 𝓣 𝓣 → funext 𝓤 (𝓣 ⁺ ⊔ 𝓤)
             → {X : 𝓤 ̇} → η ≡ 𝓚→𝓛 X ∘ κ
 η-composite fe fe' {X} = dfunext fe' h
  where
   h : (x : X) → (𝟙 , (λ _ → x) , 𝟙-is-prop)
               ≡ (𝟙 , (λ _ → x) , singletons-are-props (𝟙-is-singleton))
   h x = to-Σ-≡ (refl , to-×-≡ refl (being-a-prop-is-a-prop fe _ _))

\end{code}

The fact that 𝓚→𝓛 is an embedding can be proved by obtaining it as
a combination of maps that we already know to be embeddings, using
×-embedding, maps-of-props-are-embeddings, id-is-embedding, and
NatΣ-embedding.:

\begin{code}

 ζ-is-embedding : funext 𝓣 𝓣 → (X : 𝓤 ̇) (P : 𝓣 ̇) → is-embedding (ζ X P)
 ζ-is-embedding fe X P = ×-embedding
                           id
                           singletons-are-props
                           id-is-embedding
                           (maps-of-props-are-embeddings
                             singletons-are-props
                             (being-a-singleton-is-a-prop fe)
                             (being-a-prop-is-a-prop fe))

 𝓚→𝓛-is-embedding : funext 𝓣 𝓣
                   → (X : 𝓤 ̇) → is-embedding (𝓚→𝓛 X)
 𝓚→𝓛-is-embedding fe X = NatΣ-is-embedding
                           (λ P → (P → X) × is-singleton P)
                           (λ P → (P → X) × is-prop P)
                           (ζ X)
                           (ζ-is-embedding fe X)

\end{code}

That κ is an equivalence corresponds to the fact that the lifting of a
type X with respect to the dominance "is-singleton" is equivalent to X
itself.

\begin{code}

 κ-is-equiv : propext 𝓣 → funext 𝓣 𝓣 → funext 𝓣 𝓤
            → {X : 𝓤 ̇} → is-equiv (κ {𝓤} {X})
 κ-is-equiv {𝓤} pe fe fe' {X} = qinvs-are-equivs κ (ρ , (ρκ , κρ))
  where
   ρ : {X : 𝓤 ̇} → 𝓚 X → X
   ρ (P , φ , i) = φ (singleton-types-are-pointed i)
   ρκ : {X : 𝓤 ̇} (x : X) → ρ (κ x) ≡ x
   ρκ x = refl
   κρ : (m : 𝓚 X) → κ (ρ m) ≡ m
   κρ (P , φ , i) = u
    where
     t : 𝟙 ≡ P
     t = pe 𝟙-is-prop (singletons-are-props i)
                      (λ _ → singleton-types-are-pointed i)
                      unique-to-𝟙
     s : (t : 𝟙 ≡ P)
       → transport (λ - → (- → X) × is-singleton -)
                   t ((λ _ → φ (singleton-types-are-pointed i)),
         𝟙-is-singleton)
       ≡ φ , i
     s refl = to-×-≡ a b
      where
       a : (λ x → φ (singleton-types-are-pointed i)) ≡ φ
       a = dfunext fe' (λ x → ap φ (𝟙-is-prop (singleton-types-are-pointed i) x))
       b : 𝟙-is-singleton ≡ i
       b = (singletons-are-props (pointed-props-are-singletons
                                    𝟙-is-singleton (being-a-singleton-is-a-prop fe))
                                  𝟙-is-singleton i)
     u : 𝟙 , (λ _ → φ (singleton-types-are-pointed i)) , 𝟙-is-singleton ≡ P , φ , i
     u = to-Σ-≡ (t , s t)

 κ-is-embedding : propext 𝓣 → funext 𝓣 𝓣 → funext 𝓣 𝓤
                → {X : 𝓤 ̇} → is-embedding (κ {𝓤} {X})
 κ-is-embedding pe fe fe' = equivs-are-embeddings κ (κ-is-equiv pe fe fe')

\end{code}

Finally, η is an embedding because it is equal to the composition of
two embeddings:

\begin{code}

 η-is-embedding : propext 𝓣 → funext 𝓣 𝓣 → funext 𝓣 𝓤 → funext 𝓤 (𝓣 ⁺ ⊔ 𝓤)
                → {X : 𝓤 ̇} → is-embedding (η {𝓤} {X})
 η-is-embedding pe fe fe' fe'' {X} =
   back-transport
    is-embedding
    (η-composite fe fe'')
    (comp-embedding (κ-is-embedding pe fe fe') (𝓚→𝓛-is-embedding fe X))
\end{code}

Alternative proof that η is an embedding (added 7th December 2018),
using a version of the "structure of identity principle" (SIP), and
assuming univalence rather than just propositional extensionality
(because of the generality of the principle):

\begin{code}

 module _ {𝓤 : Universe} {X : 𝓤 ̇} where

  _⋍_ : 𝓛 X → 𝓛 X → 𝓣 ⊔ 𝓤 ̇
  l ⋍ m = Σ \(e : is-defined l ≃ is-defined m) → value l ≡ value m ∘ eqtofun e

  𝓛-Id : is-univalent 𝓣 → (l m : 𝓛 X) → (l ≡ m) ≃ (l ⋍ m)
  𝓛-Id ua = ≡-is-≃ₛ'
   where
    open gsip-with-axioms'
          𝓣 (𝓣 ⊔ 𝓤) (𝓣 ⊔ 𝓤) 𝓣 ua
          (λ P → P → X)
          (λ P s → is-prop P)
          (λ P s → being-a-prop-is-a-prop (funext-from-univalence ua))
          (λ {l m (f , e) → pr₂ l ≡ pr₂ m ∘ f})
          (λ l → refl)
          (λ P ε δ → id)
          (λ A τ υ → refl-left-neutral)

  η-is-embedding' : is-univalent 𝓣 → funext 𝓣 𝓤 → is-embedding (η {𝓤} {X})
  η-is-embedding' ua fe = embedding-criterion' η c
   where
    a = (𝟙 ≃ 𝟙) ≃⟨ ≃-sym (is-univalent-≃ ua 𝟙 𝟙) ⟩
        (𝟙 ≡ 𝟙) ≃⟨ 𝟙-≡-≃ 𝟙 (funext-from-univalence ua)
                           (propext-from-univalence ua) 𝟙-is-prop ⟩
        𝟙       ■

    b = λ x y → ((λ _ → x) ≡ (λ _ → y)) ≃⟨ ≃-funext fe (λ _ → x) (λ _ → y) ⟩
                (𝟙 → x ≡ y)             ≃⟨ ≃-sym (𝟙→ fe) ⟩
                (x ≡ y)                 ■

    c = λ x y → (η x ≡ η y)                       ≃⟨ 𝓛-Id ua (η x) (η y) ⟩
                (𝟙 ≃ 𝟙) × ((λ _ → x) ≡ (λ _ → y)) ≃⟨ ×-cong a (b x y) ⟩
                𝟙 × (x ≡ y)                       ≃⟨ 𝟙-lneutral ⟩
                (x ≡ y)                           ■

\end{code}

When dealing with functions it is often more convenient to work with
pointwise equality, and hence we also consider:

\begin{code}

  _⋍·_ : 𝓛 X → 𝓛 X → 𝓣 ⊔ 𝓤 ̇
  l ⋍· m = Σ \(e : is-defined l ≃ is-defined m) → value l ∼ value m ∘ eqtofun e

  𝓛-Id· : is-univalent 𝓣 → funext 𝓣 𝓤
        → (l m : 𝓛 X) → (l ≡ m) ≃ (l ⋍· m)
  𝓛-Id· ua fe l m = ≃-trans (𝓛-Id ua l m)
                            (Σ-cong (λ e → ≃-funext fe (value l) (value m ∘ eqtofun e)))

\end{code}

The type 𝓛 X forms a univalent precategory with hom types l ⊑ m.

\begin{code}

  _⊑_ : 𝓛 X → 𝓛 X → 𝓤 ⊔ 𝓣 ̇
  l ⊑ m = Σ \(f : is-defined l → is-defined m) → value l ∼ value m ∘ f

  dom : {l m : 𝓛 X} → l ⊑ m → 𝓛 X
  dom {l} {m} α = l

  cod : {l m : 𝓛 X} → l ⊑ m → 𝓛 X
  cod {l} {m} α = m

  𝓛-id : (l : 𝓛 X) → l ⊑ l
  𝓛-id l = id , (λ x → refl)

  𝓛-Id-to-arrow : (l m : 𝓛 X) → l ≡ m → l ⊑ m
  𝓛-Id-to-arrow l .l refl = 𝓛-id l

  𝓛-comp : (l m n : 𝓛 X) → l ⊑ m → m ⊑ n → l ⊑ n
  𝓛-comp l m n (f , δ) (g , ε) = g ∘ f , (λ p → δ p ∙ ε (f p))

  𝓛-comp-unit-right : (l m : 𝓛 X) (α : l ⊑ m) → 𝓛-comp l m m α (𝓛-id m) ≡ α
  𝓛-comp-unit-right l m α = refl

  𝓛-comp-unit-left : funext 𝓣 𝓤 → (l m : 𝓛 X) (α : l ⊑ m) → 𝓛-comp l l m (𝓛-id l) α ≡ α
  𝓛-comp-unit-left fe l m α = to-Σ-≡ (refl , dfunext fe λ p → refl-left-neutral)

  𝓛-comp-assoc : funext 𝓣 𝓤 → {l m n o : 𝓛 X} (α : l ⊑ m) (β : m ⊑ n) (γ : n ⊑ o)
               →  𝓛-comp l n o (𝓛-comp l m n α β) γ ≡ 𝓛-comp l m o α (𝓛-comp m n o β γ)
  𝓛-comp-assoc fe (f , δ) (g , ε) (h , ζ) =
     to-Σ-≡ (refl , dfunext fe (λ p → assoc (δ p) (ε (f p)) (ζ (g (f p)))))

\end{code}

Thus, the associativity law in this precategory is that of function
composition in the first component (where it hence holds
definitionally) and that of path composition in the first
component. (Hence this precategory should qualify as an ∞-category,
with all coherence laws satisfied automatically, except that there is
at present no definition of ∞-category in univalent type theory.)

It follows that if X is a set, then _⊑_ is a partial order:

\begin{code}

  ⊑-prop-valued : funext 𝓣 𝓣 → funext 𝓣 𝓤
                → is-set X → (l m : 𝓛 X) → is-prop (l ⊑ m)
  ⊑-prop-valued fe fe' s l m (f , δ) (g , ε) =
    to-Σ-≡ (dfunext fe (λ p → being-defined-is-a-prop m (f p) (g p)) ,
            Π-is-prop fe' (λ d → s) _ ε)

\end{code}

TODO. This order is directed complete (easy). We should also do least
fixed points of continuous maps.

Next we show that for any l : 𝓛 X,

 fiber η l ≃ is-defined l,

using the fact that the fiber is a proposition by virtue of η being an
embedding.

\begin{code}

  ⊑-anti-lemma : propext 𝓣 → funext 𝓣 𝓣 → funext 𝓣 𝓤
               → {l m : 𝓛 X} → l ⊑ m → (is-defined m → is-defined l) → l ≡ m
  ⊑-anti-lemma pe fe fe' {Q , ψ , j} {P , φ , i} (f , δ) g = e
   where
    ε : (p : P) → ψ (g p) ≡ φ p
    ε p = δ (g p) ∙ ap φ (i (f (g p)) p)
    a : Q ≡ P
    a = pe j i f g
    b : Idtofun (a ⁻¹) ≡ g
    b = dfunext fe (λ p → j (Idtofun (a ⁻¹) p) (g p))
    c : transport (λ - → (- → X) × is-prop -) a (ψ , j)
      ≡ (transport (λ - → - → X) a ψ , transport is-prop a j)
    c = transport-× (λ - → - → X) is-prop a
    d = pr₁ (transport (λ - → (- → X) × is-prop -) a (ψ , j)) ≡⟨ ap pr₁ c ⟩
        transport (λ - → - → X) a ψ                           ≡⟨ transport-is-pre-comp a ψ ⟩
        ψ ∘ Idtofun (a ⁻¹)                                    ≡⟨ ap (λ - → ψ ∘ -) b ⟩
        ψ ∘ g                                                 ≡⟨ dfunext fe' ε ⟩
        φ     ∎
    e : Q , ψ , j ≡ P , φ , i
    e = to-Σ-≡ (a , to-×-≡ d (being-a-prop-is-a-prop fe _ i))

  ⊑-anti : propext 𝓣 → funext 𝓣 𝓣 → funext 𝓣 𝓤
         → {l m : 𝓛 X} → (l ⊑ m) × (m ⊑ l) → l ≡ m
  ⊑-anti pe fe fe' ((f , δ) , (g , ε)) = ⊑-anti-lemma pe fe fe' (f , δ) g

\end{code}

We can now establish the promised fact:

\begin{code}

  η-fiber-same-as-is-defined : propext 𝓣 → funext 𝓣 𝓣 → funext 𝓣 𝓤 → funext 𝓤 (𝓣 ⁺ ⊔ 𝓤)
                             → (l : 𝓛 X) → (Σ \(x : X) → η x ≡ l) ≃ is-defined l
  η-fiber-same-as-is-defined pe fe fe' fe'' l = qinveq (f l) (g l , gf , fg)
   where
    f : (l : 𝓛 X) → fiber η l → is-defined l
    f (.𝟙 , .(λ _ → x) , .𝟙-is-prop) (x , refl) = *
    g : (l : 𝓛 X) → is-defined l → fiber η l
    g (P , φ , i) p = φ p , ⊑-anti pe fe fe' (a , b)
     where
      a : η (φ p) ⊑ (P , φ , i)
      a = (λ _ → p) , (λ _ → refl)
      b : (P , φ , i) ⊑ η (φ p)
      b = (λ _ → *) , (λ q → ap φ (i q p))
    fg : (d : is-defined l) → f l (g l d) ≡ d
    fg d = being-defined-is-a-prop l (f l (g l d)) d
    gf : (z : fiber η l) → g l (f l z) ≡ z
    gf z = η-is-embedding pe fe fe' fe'' l (g l (f l z)) z

\end{code}

They can't be equal, in the absence of cumulativity (and propositional
resizing), as the lhs lives in a universe higher than the rhs, and
equality is well-typed only for elements of the same type (here of the
same universe). This can be seen by adding type annotations to the
formulation of the above equivalence:

\begin{code}

  private
   η-fiber-same-as-is-defined' : propext 𝓣 → funext 𝓣 𝓣 → funext 𝓣 𝓤 → funext 𝓤 (𝓣 ⁺ ⊔ 𝓤)
                               → (l : 𝓛 X) → (fiber η l    ∶ 𝓣 ⁺ ⊔ 𝓤 ̇)
                                           ≃ (is-defined l ∶ 𝓣 ̇)
   η-fiber-same-as-is-defined' = η-fiber-same-as-is-defined

\end{code}

For no choice of universes 𝓤 and 𝓣 can we have 𝓣 ⁺ ⊔ 𝓤 to coincide
with 𝓣. However, for some dominances other than is-prop, it is possible to
have the equality between the fiber of l and the definedness of l.


The following simplified proof of ⊑-anti uses the SIP.

\begin{code}

  ⊑-anti-sip : is-univalent 𝓣 → funext 𝓣 𝓤
             → {l m : 𝓛 X} → (l ⊑ m) × (m ⊑ l) → l ≡ m
  ⊑-anti-sip ua fe {Q , ψ , j} {P , φ , i} ((f , δ) , (g , ε)) =
   eqtofun (≃-sym (𝓛-Id· ua fe (Q , ψ , j) (P , φ , i))) γ
   where
    e : Q ≃ P
    e = f , ((g , (λ p → i (f (g p)) p)) , (g , (λ q → j (g (f q)) q)))
    γ : (Q , ψ , j) ⋍· (P , φ , i)
    γ = e , δ

\end{code}

Could the map (anti l m) be an equivalence? No. instead have an
equivalence (l ⊑ m) × (m ⊑ l) → (l ≡ m) × (l ≡ m), reflecting the fact
that there were two candidate proofs for the equality.

\begin{code}

  to-⋍· : (l m : 𝓛 X) → (l ⊑ m) × (is-defined m → is-defined l) → (l ⋍· m)
  to-⋍· (Q , ψ , j) (P , φ , i) ((f , δ) , g) =
    (f , ((g , (λ p → i (f (g p)) p)) , (g , (λ q → j (g (f q)) q)))) , δ

  from-⋍· : (l m : 𝓛 X) → (l ⋍· m) → (l ⊑ m) × (is-defined m → is-defined l)
  from-⋍· l m ((f , δ) , g) = (f , g) , pr₁ (pr₁ δ)

  from-to : (l m : 𝓛 X) →  from-⋍· l m ∘ to-⋍· l m ∼ id
  from-to l m e = refl

  to-from : funext 𝓣 𝓣 → (l m : 𝓛 X) → to-⋍· l m ∘ from-⋍· l m ∼ id
  to-from fe l m ((f , δ) , g) = b
   where
    δ' : is-equiv f
    δ' = pr₂ (pr₁ (to-⋍· l m (from-⋍· l m ((f , δ) , g))))
    a : δ' ≡ δ
    a = being-equiv-is-a-prop'' fe f δ' δ
    b : (f , δ') , g ≡ (f , δ) , g
    b = ap (λ - → (f , -) , g) a

  ⊑-anti-equiv-lemma'' : funext 𝓣 𝓣 → (l m : 𝓛 X) → is-equiv (to-⋍· l m)
  ⊑-anti-equiv-lemma'' fe l m = qinvs-are-equivs
                                 (to-⋍· l m)
                                 (from-⋍· l m , from-to l m , to-from fe l m)

  ⊑-anti-equiv-lemma' : funext 𝓣 𝓣
                     → (l m : 𝓛 X)
                     → (l ⊑ m) × (is-defined m → is-defined l) ≃ (l ⋍· m)
  ⊑-anti-equiv-lemma' fe l m = to-⋍· l m , ⊑-anti-equiv-lemma'' fe l m

  ⊑-anti-equiv-lemma : is-univalent 𝓣 → funext 𝓣 𝓤
                     → (l m : 𝓛 X)
                     → (l ⊑ m) × (is-defined m → is-defined l) ≃ (l ≡ m)
  ⊑-anti-equiv-lemma ua fe l m =
    ≃-trans (⊑-anti-equiv-lemma' (funext-from-univalence ua) l m)
            (≃-sym (𝓛-Id· ua fe l m))

  ⊑-anti-equiv : is-univalent 𝓣 → funext 𝓣 𝓤
               → (l m : 𝓛 X)
               → (l ⊑ m) × (m ⊑ l) ≃ (l ≡ m) × (m ≡ l)
  ⊑-anti-equiv ua fe l m = ≃-trans γ (×-cong (⊑-anti-equiv-lemma ua fe l m)
                                             (⊑-anti-equiv-lemma ua fe m l))
   where
    A = (l ⊑ m) × (m ⊑ l)
    B = ((l ⊑ m) × (is-defined m → is-defined l))
      × ((m ⊑ l) × (is-defined l → is-defined m))
    γ : A ≃ B
    γ = qinveq u (v , vu , uv)
      where
       u : A → B
       u ((f , δ) , (g , ε)) = ((f , δ) , g) , ((g , ε) , f)
       v : B → A
       v (((f , δ) , h) , ((g , ε) , k)) = (f , δ) , (g , ε)
       vu : (a : A) → v (u a) ≡ a
       vu a = refl
       uv : (b : B) → u (v b) ≡ b
       uv (((f , δ) , h) , ((g , ε) , k)) = t
        where
         r : g ≡ h
         r = dfunext (funext-from-univalence ua)
                     (λ p → being-defined-is-a-prop l (g p) (h p))
         s : f ≡ k
         s = dfunext (funext-from-univalence ua)
                     (λ p → being-defined-is-a-prop m (f p) (k p))
         t : ((f , δ) , g) , (g , ε) , f ≡ ((f , δ) , h) , (g , ε) , k
         t = ap₂ (λ -₀ -₁ → ((f , δ) , -₀) , (g , ε) , -₁) r s

\end{code}

Next we show that (l ⊑ m) ≃ (is-defined l → l ≡ m), so that elements
of l ⊑ m can be seen as partial elements of the identity type l ≡ m.

We begin with the following auxiliary construction, which shows that
the type l ⊑ m is modal for the open modality induced by the
proposition "is-defined l" (and gave me a headache):

\begin{code}

  ⊑-open : funext 𝓣 𝓣 → funext 𝓣 𝓤 → funext 𝓣 (𝓣 ⊔ 𝓤)
         → (l m : 𝓛 X) → (l ⊑ m) ≃ (is-defined l → l ⊑ m)
  ⊑-open fe fe' fe'' (Q , ψ , j) (P , φ , i) = qinveq π (ρ , ρπ , πρ)
   where
    l = (Q , ψ , j)
    m = (P , φ , i)
    π : l ⊑ m → (is-defined l → l ⊑ m)
    π α d = α
    ρ : (is-defined l → l ⊑ m) → l ⊑ m
    ρ h = (λ d → pr₁ (h d) d) , (λ d → pr₂ (h d) d)
    ρπ : ρ ∘ π ∼ id
    ρπ α = refl
    ρ-lemma : (h : is-defined l → l ⊑ m) (q : is-defined l) → ρ h ≡ h q
    ρ-lemma h q = γ
     where
      remark = h q  ≡⟨ refl ⟩  (λ d → pr₁ (h q) d) , (λ d → pr₂ (h q) d) ∎
      k : (d : Q) → pr₁ (h d) d ≡ pr₁ (h q) d
      k d = ap (λ - → pr₁ (h -) d) (j d q)
      a : (λ d → pr₁ (h d) d) ≡ pr₁ (h q)
      a = dfunext fe k
      u : (d : Q) {f g : Q → P} (k : f ∼ g)
        → ap (λ (- : Q → P) → φ (- d)) (dfunext fe k)
        ≡ ap φ (k d)
      u d {f} {g} k = ap-funext f g φ k fe d
      v : (d : Q) → pr₂ (h d) d ∙ ap (λ - → φ (- d)) a
                  ≡ pr₂ (h q) d
      v d = pr₂ (h d) d ∙ ap (λ - → φ (- d)) a                  ≡⟨ using-u ⟩
            pr₂ (h d) d ∙ ap φ (ap (λ - → pr₁ (h -) d) (j d q)) ≡⟨ ap-ap-is-ap-of-∘ ⟩
            pr₂ (h d) d ∙ ap (λ - → φ (pr₁ (h -) d)) (j d q)    ≡⟨ by-naturality ⟩
            ap (λ _ → ψ d) (j d q) ∙ pr₂ (h q) d                ≡⟨ ap-const-is-refl ⟩
            refl ∙ pr₂ (h q) d                                  ≡⟨ refl-left-neutral ⟩
            pr₂ (h q) d                                         ∎
       where
        using-u = ap (λ - → pr₂ (h d) d ∙ -) (u d k)
        ap-ap-is-ap-of-∘ = ap (λ - → pr₂ (h d) d ∙ -) (ap-ap (λ - → pr₁ (h -) d) φ (j d q))
        by-naturality = homotopies-are-natural
                         (λ _ → ψ d) (λ - → φ (pr₁ (h -) d)) (λ - → pr₂ (h -) d)
                         {d} {q} {j d q}
        ap-const-is-refl = ap (λ - → - ∙ pr₂ (h q) d) (ap-const (ψ d) (j d q))

      t : {f g : Q → P} (r : f ≡ g) (h : ψ ∼ φ ∘ f)
        → transport (λ - → ψ ∼ φ ∘ -) r h
        ≡ λ q → h q ∙ ap (λ - → φ (- q)) r
      t refl h = refl

      b = transport (λ - → ψ ∼ φ ∘ -) a (λ d → pr₂ (h d) d) ≡⟨ t a (λ d → pr₂ (h d) d) ⟩
          (λ d → pr₂ (h d) d ∙ ap (λ - → φ (- d)) a)        ≡⟨ dfunext fe' v ⟩
          pr₂ (h q)                                         ∎

      γ : (λ d → pr₁ (h d) d) , (λ d → pr₂ (h d) d) ≡ h q
      γ = to-Σ-≡ (a , b)

    πρ :  π ∘ ρ ∼ id
    πρ h = dfunext fe'' (ρ-lemma h)

\end{code}

Using this we have the following, as promised:

\begin{code}

  ⊑-in-terms-of-≡ : is-univalent 𝓣 → funext 𝓣 𝓤 → funext 𝓣 (𝓣 ⁺ ⊔ 𝓤) → funext 𝓣 (𝓣 ⊔ 𝓤)
                  → (l m : 𝓛 X) → (l ⊑ m) ≃ (is-defined l → l ≡ m)
  ⊑-in-terms-of-≡ ua fe₀ fe₁ fe₂ l m =
   l ⊑ m                                                                 ≃⟨ a ⟩
   (is-defined l → l ⊑ m)                                                ≃⟨ b ⟩
   ((is-defined l → l ⊑ m) × 𝟙)                                          ≃⟨ c ⟩
   (is-defined l → l ⊑ m) × (is-defined l → is-defined m → is-defined l) ≃⟨ d ⟩
   (is-defined l → (l ⊑ m) × (is-defined m → is-defined l))              ≃⟨ e ⟩
   (is-defined l → l ≡ m)                                                ■
   where
    fe : funext 𝓣 𝓣
    fe = funext-from-univalence ua
    s : (is-defined l → is-defined m → is-defined l) ≃ 𝟙 {𝓤}
    s = singleton-≃-𝟙 ((λ d e → d) ,
                       Π-is-prop fe
                         (λ d → Π-is-prop fe
                                  (λ e → being-defined-is-a-prop l)) (λ d e → d))

    a = ⊑-open fe fe₀ fe₂ l m
    b =  ≃-sym 𝟙-rneutral
    c = ×-cong (≃-refl _) (≃-sym s)
    d = ≃-sym ΠΣ-distr-≃
    e = →-cong fe₁ fe₂ (≃-refl (is-defined l)) (⊑-anti-equiv-lemma ua fe₀ l m)

  ⊑-lift : is-univalent 𝓣 → funext 𝓣 𝓤 → funext 𝓣 (𝓣 ⁺ ⊔ 𝓤) → funext 𝓣 (𝓣 ⊔ 𝓤)
         → (l m : 𝓛 X) → l ⊑ m → 𝓛 (l ≡ m)
  ⊑-lift ua fe₀ fe₁ fe₂ l m α = is-defined l ,
                                eqtofun (⊑-in-terms-of-≡ ua fe₀ fe₁ fe₂ l m) α ,
                                being-defined-is-a-prop l


\end{code}

We now show that the pre-category 𝓛 X is univalent if the universe 𝓣
is univalent and we have enough function extensionality for 𝓣 and 𝓤.

\begin{code}

  𝓛-pre-comp-with : (l m : 𝓛 X) → l ⊑ m → (n : 𝓛 X) → m ⊑ n → l ⊑ n
  𝓛-pre-comp-with l m α n = 𝓛-comp l m n α

  is-𝓛-equiv : (l m : 𝓛 X) → l ⊑ m → 𝓣 ⁺ ⊔ 𝓤 ̇
  is-𝓛-equiv l m α = (n : 𝓛 X) → is-equiv (𝓛-pre-comp-with l m α n)

  being-𝓛-equiv-is-a-prop : funext (𝓣 ⁺ ⊔ 𝓤) (𝓣 ⊔ 𝓤) → funext (𝓣 ⊔ 𝓤) (𝓣 ⊔ 𝓤)
                          → (l m : 𝓛 X) (α : l ⊑ m) → is-prop (is-𝓛-equiv l m α)
  being-𝓛-equiv-is-a-prop fe fe' l m α =
   Π-is-prop fe (λ n → being-equiv-is-a-prop'' fe' (𝓛-pre-comp-with l m α n))

  is-𝓛-equiv→ : (l m : 𝓛 X) (α : l ⊑ m) → is-𝓛-equiv l m α → is-equiv (pr₁ α)
  is-𝓛-equiv→ l m α e = qinvs-are-equivs (pr₁ α)
                                         (pr₁ β ,
                                          (λ p → being-defined-is-a-prop l (pr₁ β (pr₁ α p)) p) ,
                                          (λ q → being-defined-is-a-prop m (pr₁ α (pr₁ β q)) q))
   where
    u : m ⊑ l → l ⊑ l
    u = 𝓛-pre-comp-with l m α l
    β : m ⊑ l
    β = inverse u (e l) (𝓛-id l)

  is-𝓛-equiv← : propext 𝓣 → funext 𝓣 𝓣 → funext 𝓣 𝓤
              → (l m : 𝓛 X) (α : l ⊑ m) → is-equiv (pr₁ α) → is-𝓛-equiv l m α
  is-𝓛-equiv← pe fe fe' l m α e = γ
   where
    r : l ≡ m
    r = ⊑-anti-lemma pe fe fe' α (inverse (pr₁ α) e)

    π : (l n : 𝓛 X) (α : l ⊑ l) → pr₁ α ≡ id
      → Σ \(δ : (q : is-defined l) → value l q ≡ value l q)
              → 𝓛-pre-comp-with l l α n
              ∼ λ β → pr₁ β , (λ q → δ q ∙ pr₂ β q)
    π l n (.id , δ) refl = δ , λ β → refl

    ρ : (l : 𝓛 X) (α : l ⊑ l) → is-equiv (pr₁ α) → is-𝓛-equiv l l α
    ρ l α e n = equiv-closed-under-∼ u (𝓛-pre-comp-with l l α n) i h
     where
      s : pr₁ α ≡ id
      s = dfunext fe (λ q → being-defined-is-a-prop l (pr₁ α q) q)
      δ : (q : is-defined l) → value l q ≡ value l q
      δ = pr₁ (π l n α s)
      u : l ⊑ n → l ⊑ n
      u β = pr₁ β , λ q → δ q ∙ pr₂ β q
      h : 𝓛-pre-comp-with l l α n ∼ u
      h = pr₂ (π l n α s)
      v : l ⊑ n → l ⊑ n
      v γ = pr₁ γ , (λ p → (δ p)⁻¹ ∙ pr₂ γ p)
      vu : v ∘ u ∼ id
      vu (g , ε) = to-Σ-≡ (refl , a)
       where
        a = dfunext fe' (λ q →  (δ q)⁻¹ ∙ (δ q ∙ ε q)  ≡⟨ (assoc ((δ q)⁻¹) (δ q) (ε q))⁻¹ ⟩
                               ((δ q)⁻¹ ∙ δ q) ∙ ε q   ≡⟨ ap (λ - → - ∙ ε q) ((sym-is-inverse (δ q))⁻¹)⟩
                                 refl ∙ ε q            ≡⟨ refl-left-neutral ⟩
                                 ε q                   ∎)
      uv : u ∘ v ∼ id
      uv (g , ε) = to-Σ-≡ (refl , a)
       where
        a = dfunext fe' (λ q →  δ q ∙ ((δ q)⁻¹ ∙ ε q)  ≡⟨ (assoc (δ q) ((δ q)⁻¹) (ε q))⁻¹ ⟩
                               (δ q ∙ ((δ q)⁻¹)) ∙ ε q ≡⟨ ap (λ - → - ∙ ε q) ((sym-is-inverse' (δ q))⁻¹)⟩
                                refl ∙ ε q             ≡⟨ refl-left-neutral ⟩
                                ε q                    ∎)
      i : is-equiv u
      i = qinvs-are-equivs u (v , vu , uv)

    σ : (l m : 𝓛 X)  → l ≡ m → (α : l ⊑ m) → is-equiv (pr₁ α) → is-𝓛-equiv l m α
    σ l .l refl = ρ l

    γ : is-𝓛-equiv l m α
    γ = σ l m r α e

\end{code}

With this and Yoneda we can now easily derive the univalence of the
pre-category 𝓛 X.

The univalence of 𝓣 is more than we need in the
following. Propositional extensionality for propositions in 𝓣
suffices, but the what we proved this using a general SIP relies on
univalence (we could prove a specialized version of the SIP, but this
is probably not worth the trouble (we'll see)).

\begin{code}

  module univalence-of-𝓛 (ua : is-univalent 𝓣)
                         (fe : ∀ {𝓤 𝓥} → funext 𝓤 𝓥)
         where

   pe : propext 𝓣
   pe = propext-from-univalence ua

   is-𝓛-equiv-charac : (l m : 𝓛 X) (α : l ⊑ m)
                     → is-𝓛-equiv l m α ≃ (is-defined m → is-defined l)
   is-𝓛-equiv-charac l m α = is-𝓛-equiv l m α              ≃⟨ a ⟩
                             is-equiv (pr₁ α)              ≃⟨ b ⟩
                             (is-defined m → is-defined l) ■
    where
     a = logically-equivalent-props-are-equivalent
          (being-𝓛-equiv-is-a-prop fe fe l m α)
          (being-equiv-is-a-prop'' fe (pr₁ α))
          (is-𝓛-equiv→ l m α)
          (is-𝓛-equiv← pe fe fe l m α)

     b = logically-equivalent-props-are-equivalent
          (being-equiv-is-a-prop'' fe (pr₁ α))
          (Π-is-prop fe (λ p → being-defined-is-a-prop l))
          (inverse (pr₁ α))
          (λ g → qinvs-are-equivs (pr₁ α)
                                  (g , (λ q → being-defined-is-a-prop l (g (pr₁ α q)) q) ,
                                       (λ p → being-defined-is-a-prop m (pr₁ α (g p)) p)))

   _≃⟨𝓛⟩_ : 𝓛 X → 𝓛 X → 𝓣 ⁺ ⊔ 𝓤 ̇
   l ≃⟨𝓛⟩ m = Σ \(α : l ⊑ m) → is-𝓛-equiv l m α

   ≃⟨𝓛⟩-charac : (l m : 𝓛 X)
               → (l ≃⟨𝓛⟩ m) ≃ (l ⊑ m) × (is-defined m → is-defined l)
   ≃⟨𝓛⟩-charac l m = Σ-cong (is-𝓛-equiv-charac l m)

   ≃⟨𝓛⟩-is-Id : (l m : 𝓛 X)
              → (l ≃⟨𝓛⟩ m) ≃ (l ≡ m)
   ≃⟨𝓛⟩-is-Id l m = ≃-trans (≃⟨𝓛⟩-charac l m)
                            (⊑-anti-equiv-lemma ua fe l m)

   𝓛-is-univalent' : (l : 𝓛 X) → ∃! \(m : 𝓛 X) → (l ≃⟨𝓛⟩ m)
   𝓛-is-univalent' l = equiv-to-singleton e (singleton-types-are-singletons l)
    where
      e : (Σ \(m : 𝓛 X) → l ≃⟨𝓛⟩ m) ≃ (Σ \(m : 𝓛 X) → l ≡ m)
      e = Σ-cong (≃⟨𝓛⟩-is-Id l)

   𝓛-id-is-𝓛-equiv : (l : 𝓛 X) → is-𝓛-equiv l l (𝓛-id l)
   𝓛-id-is-𝓛-equiv l n = (id , h) , (id , h)
    where
     h : 𝓛-pre-comp-with l l (𝓛-id l) n ∼ id
     h (f , δ) = to-Σ-≡ (refl , dfunext fe (λ p → refl-left-neutral))

   𝓛-refl : (l : 𝓛 X) → l ≃⟨𝓛⟩ l
   𝓛-refl l = 𝓛-id l , 𝓛-id-is-𝓛-equiv l

   Id-to-𝓛-eq : (l m : 𝓛 X) → l ≡ m → l ≃⟨𝓛⟩ m
   Id-to-𝓛-eq l m r = transport (l ≃⟨𝓛⟩_) r (𝓛-refl l)

   𝓛-is-univalent : (l m : 𝓛 X) → is-equiv (Id-to-𝓛-eq l m)
   𝓛-is-univalent l = universality-equiv l (𝓛-refl l)
                        (unique-element-is-universal-element (l ≃⟨𝓛⟩_) (l , 𝓛-refl l)
                          (singletons-are-props (𝓛-is-univalent' l) (l , 𝓛-refl l)))
    where
     open import UF-Yoneda

 \end{code}

This completes the univalence submodule.

Yet another equivalence:

\begin{code}

  η-maximal : (x : X) (l : 𝓛 X) → η x ⊑ l → l ⊑ η x
  η-maximal x (P , ψ , i) (f , δ) = (λ p → *) , (λ p → ap ψ (i p (f *)) ∙ (δ *)⁻¹)

  ⊥-least : (l : 𝓛 X) → ⊥ ⊑ l
  ⊥-least l = unique-from-𝟘 , λ z → unique-from-𝟘 z

  ⊥-initial : funext 𝓣 𝓣 → funext 𝓣 𝓤 → (l : 𝓛 X) → is-singleton(⊥ ⊑ l)
  ⊥-initial fe fe' l = ⊥-least l ,
                       (λ α → to-Σ-≡ (dfunext fe (λ z → unique-from-𝟘 z) ,
                                      dfunext fe'(λ z → unique-from-𝟘 z)))

  η-≡-gives-⊑ : {x y : X} → x ≡ y → η x ⊑ η y
  η-≡-gives-⊑ {x} {y} p = id , (λ d → p)

  η-⊑-gives-≡ : {x y : X} → η x ⊑ η y → x ≡ y
  η-⊑-gives-≡ (f , δ) = δ *

  η-≡-gives-⊑-is-equiv : funext 𝓣 𝓣 → funext 𝓣 𝓤
                       → {x y : X} → is-equiv (η-≡-gives-⊑ {x} {y})
  η-≡-gives-⊑-is-equiv fe fe' {x} {y} =
   qinvs-are-equivs η-≡-gives-⊑ (η-⊑-gives-≡ , α , β)
   where
    α : {x y : X} (p : x ≡ y) →  η-⊑-gives-≡ (η-≡-gives-⊑ p) ≡ p
    α p = refl

    β : {x y : X} (q : η x ⊑ η y) → η-≡-gives-⊑ (η-⊑-gives-≡ q) ≡ q
    β (f , δ) = to-×-≡ (dfunext fe (λ x → 𝟙-is-prop x (f x)))
                       (dfunext fe' (λ x → ap δ (𝟙-is-prop * x)))

  Id-via-lifting : funext 𝓣 𝓣 → funext 𝓣 𝓤
                 → {x y : X} → (x ≡ y) ≃ (η x ⊑ η y)
  Id-via-lifting fe fe' = η-≡-gives-⊑ , η-≡-gives-⊑-is-equiv fe fe'

\end{code}

Added 7th November 2018. (Strong) 'Monad' structure on 𝓛.
(Again the proofs are simplified by the use of SIP.)

\begin{code}

 𝓛̇ : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (X → Y) → 𝓛 X → 𝓛 Y
 𝓛̇ f (P , φ , i) = P , f ∘ φ , i

 _♯ : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (X → 𝓛 Y) → (𝓛 X → 𝓛 Y)
 _♯ f (P , φ , i) = (Σ \(p : P) → is-defined (f (φ p))) ,
                     (λ σ → value (f (φ (pr₁ σ))) (pr₂ σ)) ,
                     Σ-is-prop i (λ p → being-defined-is-a-prop (f (φ p)))

 μ : {X : 𝓤 ̇} → 𝓛 (𝓛 X) → 𝓛 X
 μ = id ♯

\end{code}

Laws:

\begin{code}

 𝓛̇-id : {X : 𝓤 ̇} → 𝓛̇ id ≡ id
 𝓛̇-id {𝓤} {X} = refl {𝓤 ⊔ (𝓣 ⁺)} {𝓛 X → 𝓛 X}

 𝓛̇-∘ : {X : 𝓤 ̇} {Y : 𝓥 ̇} {Z : 𝓦 ̇} (f : X → Y) (g : Y → Z)
      → 𝓛̇ (g ∘ f) ≡ 𝓛̇ g ∘ 𝓛̇ f
 𝓛̇-∘ f g = refl

 η-natural : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y) → η ∘ f ≡ 𝓛̇ f ∘ η
 η-natural f = refl

 μ-natural : {X : 𝓤 ̇} {Y : 𝓤 ̇} (f : X → Y) → 𝓛̇ f ∘ μ ∼ μ ∘ 𝓛̇ (𝓛̇ f)
 μ-natural f _ = refl

 𝓛-unit-right : {X : 𝓤 ̇} (l : 𝓛 X) → μ (𝓛̇ η l) ⋍ l
 𝓛-unit-right (P , φ , i) = e , refl
  where
   e : P × 𝟙 ≃ P
   e = 𝟙-rneutral

 𝓛-unit-left : {X : 𝓤 ̇} (l : 𝓛 X) → μ (η l) ⋍ l
 𝓛-unit-left (P , φ) = e , refl
  where
   e : 𝟙 × P ≃ P
   e = 𝟙-lneutral

 𝓛-assoc : {X : 𝓤 ̇} (l : 𝓛 (𝓛 (𝓛 X))) → μ (μ l) ⋍ μ (𝓛̇ μ l)
 𝓛-assoc (P , φ) = Σ-assoc , refl

\end{code}

Strength:

\begin{code}

 𝓛-σ : {X : 𝓤 ̇} {Y : 𝓥 ̇} → X × 𝓛 Y → 𝓛 (X × Y)
 𝓛-σ (x , m) = 𝓛̇ (λ y → (x , y)) m

 𝓛-τ : {X : 𝓤 ̇} {Y : 𝓥 ̇} → 𝓛 X × Y → 𝓛 (X × Y)
 𝓛-τ (l , y) = 𝓛̇ (λ x → (x , y)) l

 𝓛-comm : {X : 𝓤 ̇} {Y : 𝓥 ̇} {l : 𝓛 X × 𝓛 Y}
        → μ (𝓛̇ 𝓛-σ (𝓛-τ l)) ⋍· μ (𝓛̇ 𝓛-τ (𝓛-σ l))
 𝓛-comm = ×-comm , (λ z → refl)

 𝓛-m : {X : 𝓤 ̇} {Y : 𝓥 ̇} → 𝓛 X × 𝓛 Y → 𝓛 (X × Y)
 𝓛-m (l , m) = ((λ x → curry 𝓛-σ x m)♯) l

\end{code}

TODO. Write down and prove the strength laws.

Or we can use the Kleisli-triple presentation of the monad, but the
proofs / constructions are essentially the same:

\begin{code}

 Kleisli-Law₀ : {X : 𝓤 ̇} (l : 𝓛 X) → (η ♯) l ⋍ l
 Kleisli-Law₀ (P , φ) = 𝟙-rneutral , refl

 Kleisli-Law₁ : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → 𝓛 Y) (x : X) → (f ♯) (η x) ⋍ f x
 Kleisli-Law₁ f x = 𝟙-lneutral , refl

 Kleisli-Law₂ : {X : 𝓥 ̇} {Y : 𝓦 ̇} {Z : 𝓣 ̇} (f : X → 𝓛 Y) (g : Y → 𝓛 Z) (l : 𝓛 X)
              → (g ♯ ∘ f ♯) l ⋍ ((g ♯ ∘ f)♯) l
 Kleisli-Law₂ f g l = Σ-assoc , refl

 𝓛̇' : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (X → Y) → 𝓛 X → 𝓛 Y
 𝓛̇' f = (η ∘ f)♯

 𝓛̇-agreement : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y) (l : 𝓛 X)
              → 𝓛̇' f l ⋍· 𝓛̇ f l
 𝓛̇-agreement {𝓤} {𝓥} {X} {Y} f (P , i , φ) = 𝟙-rneutral , λ _ → refl

\end{code}

Added 17th December 2018. This has a connection with injectivity.

We now have a look at 𝓛-algebras.

An element of 𝓛(𝓛 X) amounts to a family of partial elements of X
indexed by a proposition:

\begin{code}

 double-𝓛-charac : (X : 𝓤 ̇)
                 → 𝓛 (𝓛 X) ≃ Σ \(P : 𝓣 ̇)
                                    → (Σ \(Q : P → 𝓣 ̇) → ((p : P) → (Q p → X)) × ((p : P) → is-prop (Q p)))
                                    × is-prop P
 double-𝓛-charac X = Σ-cong (λ P → ×-cong (γ X P) (≃-refl (is-prop P)))
  where
   γ : (X : 𝓤 ̇) (P : 𝓣 ̇) → (P → 𝓛 X) ≃ (Σ \(Q : P → 𝓣 ̇) → ((p : P) → (Q p → X)) × ((p : P) → is-prop (Q p)))
   γ X P = (P → Σ \(Q : 𝓣 ̇) → (Q → X) × is-prop Q)                               ≃⟨ ΠΣ-distr-≃ ⟩
           (Σ \(Q : P → 𝓣 ̇) → (p : P) → ((Q p → X) × is-prop (Q p)))             ≃⟨ Σ-cong (λ Q → →×) ⟩
           (Σ \(Q : P → 𝓣 ̇) → ((p : P) → (Q p → X)) × ((p : P) → is-prop (Q p))) ■

\end{code}

The usual definition of algebra of a monad:

\begin{code}


 𝓛-algebra : 𝓤 ̇ → 𝓣 ⁺ ⊔ 𝓤 ̇
 𝓛-algebra X = Σ \(s : 𝓛 X → X) → (s ∘ η ∼ id) × (s ∘ 𝓛̇ s ∼ s ∘ μ)

\end{code}

Which we will describe in terms of "join" operations subject to two laws:

\begin{code}

 joinop : 𝓤 ̇ → 𝓣 ⁺ ⊔ 𝓤 ̇
 joinop X = {P : 𝓣 ̇} → is-prop P → (P → X) → X

 𝓛-alg-Law₀ : {X : 𝓤 ̇} → joinop X → 𝓤 ̇
 𝓛-alg-Law₀ {𝓤} {X} ∐ = (x : X) → ∐ 𝟙-is-prop (λ (p : 𝟙) → x) ≡ x

 𝓛-alg-Law₁ : {X : 𝓤 ̇} → joinop X → 𝓣 ⁺ ⊔ 𝓤 ̇
 𝓛-alg-Law₁ {𝓤} {X} ∐ = (P : 𝓣 ̇) (Q : P → 𝓣 ̇) (i : is-prop P) (j : (p : P) → is-prop (Q p)) (f : Σ Q → X)
                           → ∐ i (λ p → ∐ (j p) (λ q → f (p , q))) ≡ ∐ (Σ-is-prop i j) f

 𝓛-alg : 𝓤 ̇ → 𝓣 ⁺ ⊔ 𝓤 ̇
 𝓛-alg X = Σ \(∐ : joinop X) → 𝓛-alg-Law₀ ∐ × 𝓛-alg-Law₁ ∐

\end{code}

Before proving that we have an equivalence 𝓛-algebra X ≃ 𝓛-alg X, we
characterize the algebra morphisms in terms of joins (unfortunately
overloading is not available):

\begin{code}

 ⋁ : {X : 𝓤 ̇} → (𝓛 X → X) → joinop X
 ⋁ s {P} i f = s (P , f , i)

 ∐̇ : {X : 𝓤 ̇} → 𝓛-algebra X → joinop X
 ∐̇ (s , _) = ⋁ s

 ∐ : {X : 𝓤 ̇} → 𝓛-alg X → joinop X
 ∐ (∐ , κ , ι) = ∐


\end{code}

The algebra morphisms are the maps that preserve joins.

\begin{code}

 𝓛-morphism-charac : {X : 𝓤 ̇} {Y : 𝓥 ̇}
                     (s : 𝓛 X → X) (t : 𝓛 Y → Y)
                     (h : X → Y)

    → (h ∘ s ∼ t ∘ 𝓛̇ h) ≃ ({P : 𝓣 ̇} (i : is-prop P) (f : P → X) → h (⋁ s i f) ≡ ⋁ t i (λ p → h (f p)))
 𝓛-morphism-charac s t h = qinveq (λ H {P} i f → H (P , f , i))
                                  ((λ {π (P , f , i) → π {P} i f}) ,
                                  (λ _ → refl) ,
                                  (λ _ → refl))

\end{code}

We name the other two projections of 𝓛-alg:

\begin{code}

 𝓛-alg-const : {X : 𝓤 ̇} (A : 𝓛-alg X) → (x : X) → ∐ A 𝟙-is-prop (λ (p : 𝟙) → x) ≡ x
 𝓛-alg-const (∐ , κ , ι) = κ

 𝓛-alg-iterated : {X : 𝓤 ̇} (A : 𝓛-alg X)
                  (P : 𝓣 ̇) (Q : P → 𝓣 ̇) (i : is-prop P) (j : (p : P) → is-prop (Q p))
                  (f : Σ Q → X)
                → ∐ A i (λ p → ∐ A (j p) (λ q → f (p , q))) ≡ ∐ A (Σ-is-prop i j) f
 𝓛-alg-iterated (∐ , κ , ι) = ι

\end{code}

We could write a proof of the following characterization of the
𝓛-algebras by composing equivalences as above, but it seems more
direct, and just as clear, to write a direct proof, by construction of
the equivalence and its inverse. This also emphasizes that the
equivalence is definitional, in the sense that the two required
equations hold definitionally.

\begin{code}

 𝓛-algebra-gives-alg : {X : 𝓤 ̇} → 𝓛-algebra X → 𝓛-alg X
 𝓛-algebra-gives-alg (s , κ , l) = ⋁ s ,
                                   κ ,
                                   (λ P Q i j f → l (P , (λ p → Q p , (λ q → f (p , q)) , j p) , i))

 𝓛-alg-gives-algebra : {X : 𝓤 ̇} → 𝓛-alg X → 𝓛-algebra X
 𝓛-alg-gives-algebra {𝓤} {X} (∐ , κ , ι) = s , κ , algebra-Law
  where
   s : 𝓛 X → X
   s (P , f , i) = ∐ i f
   algebra-Law : (l : 𝓛 (𝓛 X)) → s (𝓛̇ s l) ≡ s (μ l)
   algebra-Law (P , g , i) = ι P (pr₁ ∘ g) i (λ p → pr₂ (pr₂ (g p))) (λ r → pr₁ (pr₂ (g (pr₁ r))) (pr₂ r))

 𝓛-alg-charac : {X : 𝓤 ̇} → 𝓛-algebra X ≃ 𝓛-alg X
 𝓛-alg-charac = qinveq 𝓛-algebra-gives-alg (𝓛-alg-gives-algebra , ((λ _ → refl) , (λ _ → refl)))


\end{code}

We now consider a non-dependent version of 𝓛-alg-Law₁, and show that it is
equivalent to 𝓛-alg-Law₁:

\begin{code}


 𝓛-alg-Law₁' : {X : 𝓤 ̇} → joinop X → 𝓣 ⁺ ⊔ 𝓤 ̇
 𝓛-alg-Law₁' {𝓤} {X} ∐ = (P Q : 𝓣 ̇) (i : is-prop P) (j : is-prop Q) (f : P × Q → X)
                              → ∐ i (λ p → ∐ j (λ q → f (p , q))) ≡ ∐ (×-is-prop i j) f


 𝓛-alg-Law₁-gives₁' : {X : 𝓤 ̇} (∐ : joinop X)
                    → 𝓛-alg-Law₁ ∐ → 𝓛-alg-Law₁' ∐
 𝓛-alg-Law₁-gives₁' {𝓤} {X} ∐ a P Q i j = a P (λ _ → Q) i (λ p → j)

\end{code}

To establish the converse we need the following lemma for joins, which
is interesting on its own right and also gives commutativity of joins:

\begin{code}

 change-of-variables-in-join : {X : 𝓤 ̇} (∐ : joinop X)
                               (P : 𝓣 ̇) (i : is-prop P)
                               (Q : 𝓣 ̇) (j : is-prop Q)
                               (h : P → Q) (k : Q → P) (f : P → X)
                             → is-univalent 𝓣
                             → ∐ i f ≡ ∐ j (f ∘ k)

 change-of-variables-in-join ∐ P i Q j h k f ua = cd (eqtoid ua Q P e) ∙ ap (λ - → ∐ j (f ∘ -)) a
  where
   cd : (r : Q ≡ P) → ∐ i f ≡ ∐ j (f ∘ Idtofun r)
   cd refl = ap (λ - → ∐ - f) (being-a-prop-is-a-prop (funext-from-univalence ua) i j)
   e : Q ≃ P
   e = qinveq k (h , ((λ q → j (h (k q)) q) , λ p → i (k (h p)) p))
   a : Idtofun (eqtoid ua Q P e) ≡ k
   a = ap eqtofun (idtoeq'-eqtoid ua Q P e)


 𝓛-alg-comm : {X : 𝓤 ̇} (∐ : joinop X)
              (P : 𝓣 ̇) (i : is-prop P)
              (Q : 𝓣 ̇) (j : is-prop Q)
            → is-univalent 𝓣
            → 𝓛-alg-Law₁' ∐
            → (f : P × Q → X) → ∐ i (λ p → ∐ j (λ q → f (p , q)))
                              ≡ ∐ j (λ q → ∐ i (λ p → f (p , q)))

 𝓛-alg-comm ∐ P i Q j ua l₁' f = ∐ i (λ p → ∐ j (λ q → f (p , q)))                     ≡⟨ a ⟩
                                 ∐ (Σ-is-prop i (λ p → j)) f                           ≡⟨ c ⟩
                                 ∐ (Σ-is-prop j (λ p → i)) (f ∘ (λ t → pr₂ t , pr₁ t)) ≡⟨(b ⁻¹)⟩
                                 ∐ j (λ q → ∐ i (λ p → f (p , q)))                     ∎
  where
   a = l₁' P Q i j f
   b = l₁' Q P j i (λ t → f (pr₂ t , pr₁ t))
   c = change-of-variables-in-join ∐ (P × Q) (Σ-is-prop i (λ p → j)) (Q × P) (Σ-is-prop j (λ p → i))
                                   (λ t → pr₂ t , pr₁ t) (λ t → pr₂ t , pr₁ t) f ua

 𝓛-alg-Law₁'-gives₁ : {X : 𝓤 ̇} (∐ : joinop X)
                     → is-univalent 𝓣 → funext 𝓣 𝓤
                     → 𝓛-alg-Law₁' ∐ → 𝓛-alg-Law₁ ∐
 𝓛-alg-Law₁'-gives₁ {𝓤} {X} ∐ ua fe a P Q i j f =
  ∐ {P} i (λ p → ∐ {Q p} (j p) (λ q → f (p , q)))                   ≡⟨ b ⟩
  ∐ {P} i (λ p → ∐ {Σ Q} (Σ-is-prop i j) ((λ σ → f (p , σ)) ∘ k p)) ≡⟨ c ⟩
  ∐ {P × Σ Q} (×-is-prop i (Σ-is-prop i j)) f'                      ≡⟨ d ⟩
  ∐ {Σ Q} (Σ-is-prop i j) (f' ∘ k')                                 ≡⟨ e ⟩
  ∐ {Σ Q} (Σ-is-prop i j) f ∎
  where
   h : (p : P) → Q p → Σ Q
   h p q = (p , q)
   k : (p : P) → Σ Q → Q p
   k p (p' , q) = transport Q (i p' p) q
   f' : P × Σ Q → X
   f' (p , p' , q) = f (p , k p (p' , q))
   k' : Σ Q → P × Σ Q
   k' (p , q) = p , p , q
   H : f' ∘ k' ∼ f
   H (p , q) = ap (λ - → f (p , -)) (j p _ _)
   b = ap (∐ {P} i) (dfunext fe (λ p → change-of-variables-in-join ∐ (Q p) (j p) (Σ Q) (Σ-is-prop i j)
                                                                  (h p) (k p) (λ σ → f (p , σ)) ua))
   c = a P (Σ Q) i (Σ-is-prop i j) (λ z → f (pr₁ z , k (pr₁ z) (pr₂ z)))
   d = change-of-variables-in-join ∐ (P × Σ Q) (×-is-prop i (Σ-is-prop i j)) (Σ Q) (Σ-is-prop i j) pr₂ k' f' ua
   e = ap (∐ {Σ Q} (Σ-is-prop i j)) (dfunext fe H)

\end{code}

Crucial examples for injectivity.

\begin{code}

 universe-is-algebra-Σ : is-univalent 𝓣 → 𝓛-alg (𝓣 ̇)
 universe-is-algebra-Σ ua = sum , k , ι
  where
   sum : {P : 𝓣 ̇} → is-prop P → (P → 𝓣 ̇) → 𝓣 ̇
   sum {P} i = Σ
   k : (X : 𝓣 ̇) → Σ (λ p → X) ≡ X
   k X = eqtoid ua (𝟙 × X) X 𝟙-lneutral
   ι : (P : 𝓣 ̇) (Q : P → 𝓣 ̇) (i : is-prop P)
       (j : (p : P) → is-prop (Q p)) (f : Σ Q → 𝓣 ̇)
     → Σ (λ p → Σ (λ q → f (p , q))) ≡ Σ f
   ι P Q i j f = (eqtoid ua _ _ Σ-assoc)⁻¹

 universe-is-algebra-Π : is-univalent 𝓣 → 𝓛-alg (𝓣 ̇)
 universe-is-algebra-Π ua = prod , k , ι
  where
   fe : funext 𝓣 𝓣
   fe = funext-from-univalence ua
   prod : {P : 𝓣 ̇} → is-prop P → (P → 𝓣 ̇) → 𝓣 ̇
   prod {P} i = Π
   k : (X : 𝓣 ̇) → Π (λ p → X) ≡ X
   k X = eqtoid ua (𝟙 → X) X (≃-sym (𝟙→ (funext-from-univalence ua)))
   ι : (P : 𝓣 ̇) (Q : P → 𝓣 ̇) (i : is-prop P)
       (j : (p : P) → is-prop (Q p)) (f : Σ Q → 𝓣 ̇)
     → Π (λ p → Π (λ q → f (p , q))) ≡ Π f
   ι P Q i j f = (eqtoid ua _ _ (curry-uncurry' fe fe fe))⁻¹

\end{code}

Remark. Another equivalent way to define μ, which has a different
universe level:

\begin{code}

module another-way-to-define-μ where

 open lifting

 𝓛* : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y) → is-embedding f → 𝓛 𝓣 Y → 𝓛 (𝓤 ⊔ 𝓥 ⊔ 𝓣) X
 𝓛* f e (Q , ψ , j) = (Σ \(q : Q) → fiber f (ψ q)) ,
                       (λ p → pr₁ (pr₂ p)) ,
                       Σ-is-prop j (e ∘ ψ)

 μ* : (𝓣 𝓣' : Universe) {X : 𝓤 ̇} → funext 𝓣 𝓣 → funext 𝓣' 𝓣' → funext 𝓣' 𝓤 → funext 𝓤 (𝓤 ⊔ (𝓣' ⁺)) → propext 𝓣'
   → 𝓛 𝓣 (𝓛 𝓣' X) → 𝓛 (𝓤 ⊔ 𝓣 ⊔ (𝓣' ⁺)) X
 μ* {𝓤} 𝓣 𝓣' {X} fe fe' fe'' fe''' pe = 𝓛* (η 𝓣') (η-is-embedding 𝓣' pe fe' fe'' fe''')

\end{code}
