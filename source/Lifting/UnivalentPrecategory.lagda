Martin Escardo December 2018.

The lifting of a type forms a univalent pre-∞-category with hom types
l ⊑ m, which is a partial order if the type is a set.

At the moment we don't have categories in this development, but this
doesn't prevent us from giving this particular example of a univalent
category.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan

module Lifting.UnivalentPrecategory
        (𝓣 : Universe)
        {𝓤 : Universe}
        (X : 𝓤 ̇ )
       where

open import Lifting.IdentityViaSIP 𝓣
open import Lifting.Lifting 𝓣
open import UF.Base
open import UF.Embeddings
open import UF.Equiv
open import UF.Equiv-FunExt
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.Lower-FunExt
open import UF.Sets
open import UF.StructureIdentityPrinciple
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.UA-FunExt
open import UF.Univalence

\end{code}

We define l ⊑ m to mean that if l is defined then so is m with the
same value:

\begin{code}

_⊑_ : 𝓛 X → 𝓛 X → 𝓤 ⊔ 𝓣 ̇
l ⊑ m = Σ f ꞉ (is-defined l → is-defined m) , value l ∼ value m ∘ f

dom : {l m : 𝓛 X} → l ⊑ m → 𝓛 X
dom {l} {m} α = l

cod : {l m : 𝓛 X} → l ⊑ m → 𝓛 X
cod {l} {m} α = m

𝓛-id : (l : 𝓛 X) → l ⊑ l
𝓛-id l = id , (λ x → refl)

𝓛-Id-to-arrow : (l m : 𝓛 X) → l ＝ m → l ⊑ m
𝓛-Id-to-arrow l .l refl = 𝓛-id l

𝓛-comp : (l m n : 𝓛 X) → l ⊑ m → m ⊑ n → l ⊑ n
𝓛-comp l m n (f , δ) (g , ε) = g ∘ f , (λ p → δ p ∙ ε (f p))

𝓛-comp-unit-right : (l m : 𝓛 X) (α : l ⊑ m) → 𝓛-comp l m m α (𝓛-id m) ＝ α
𝓛-comp-unit-right l m α = refl

𝓛-comp-unit-left : funext 𝓣 𝓤 → (l m : 𝓛 X) (α : l ⊑ m) → 𝓛-comp l l m (𝓛-id l) α ＝ α
𝓛-comp-unit-left fe l m α = to-Σ-＝ (refl , dfunext fe λ p → refl-left-neutral)

𝓛-comp-assoc : funext 𝓣 𝓤
             → {l m n o : 𝓛 X} (α : l ⊑ m) (β : m ⊑ n) (γ : n ⊑ o)
             →  𝓛-comp l n o (𝓛-comp l m n α β) γ ＝ 𝓛-comp l m o α (𝓛-comp m n o β γ)
𝓛-comp-assoc fe (f , δ) (g , ε) (h , ζ) =
 to-Σ-＝ (refl , dfunext fe (λ p → ∙assoc (δ p) (ε (f p)) (ζ (g (f p)))))

\end{code}

Thus, the associativity law in this pre-∞-category is that of function
composition in the first component (where it hence holds
definitionally) and that of path composition in the first
component. (Hence this pre-∞-category should qualify as an ∞-category,
with all coherence laws satisfied automatically, except that there is
at present no definition of ∞-category in univalent type theory.)

If X is a set, then _⊑_ is a partial order:

\begin{code}

⊑-prop-valued : funext 𝓣 𝓣
              → funext 𝓣 𝓤
              → is-set X
              → (l m : 𝓛 X) → is-prop (l ⊑ m)
⊑-prop-valued fe fe' s l m (f , δ) (g , ε) =
 to-Σ-＝ (dfunext fe (λ p → being-defined-is-prop m (f p) (g p)) ,
         Π-is-prop fe' (λ d → s) _ ε)

\end{code}

TODO. This order is directed complete (easy). We should also do least
fixed points of continuous maps.

This TODO was implemented by Tom de Jong in the file
DomainTheory.Lifting.LiftingSet.lagda.

Next we show that for any l : 𝓛 X,

 fiber η l ≃ is-defined l,

using the fact that the fiber is a proposition by virtue of η being an
embedding.

\begin{code}

⊑-anti-lemma : propext 𝓣
             → funext 𝓣 𝓣
             → funext 𝓣 𝓤
             → {l m : 𝓛 X} → l ⊑ m → (is-defined m → is-defined l) → l ＝ m
⊑-anti-lemma pe fe fe' {Q , ψ , j} {P , φ , i} (f , δ) g = e
 where
  ε : (p : P) → ψ (g p) ＝ φ p
  ε p = δ (g p) ∙ ap φ (i (f (g p)) p)

  a : Q ＝ P
  a = pe j i f g

  b : Idtofun (a ⁻¹) ＝ g
  b = dfunext fe (λ p → j (Idtofun (a ⁻¹) p) (g p))

  c : transport (λ - → (- → X) × is-prop -) a (ψ , j)
    ＝ (transport (λ - → - → X) a ψ , transport is-prop a j)
  c = transport-× (λ - → - → X) is-prop a

  d = pr₁ (transport (λ - → (- → X) × is-prop -) a (ψ , j)) ＝⟨ ap pr₁ c ⟩
      transport (λ - → - → X) a ψ                           ＝⟨ transport-is-pre-comp a ψ ⟩
      ψ ∘ Idtofun (a ⁻¹)                                    ＝⟨ ap (λ - → ψ ∘ -) b ⟩
      ψ ∘ g                                                 ＝⟨ dfunext fe' ε ⟩
      φ                                                     ∎

  e : Q , ψ , j ＝ P , φ , i
  e = to-Σ-＝ (a , to-×-＝ d (being-prop-is-prop fe _ i))

⊑-anti : propext 𝓣
       → funext 𝓣 𝓣
       → funext 𝓣 𝓤
       → {l m : 𝓛 X} → (l ⊑ m) × (m ⊑ l) → l ＝ m
⊑-anti pe fe fe' ((f , δ) , (g , ε)) = ⊑-anti-lemma pe fe fe' (f , δ) g

\end{code}

We can now establish the promised fact:

\begin{code}

open import Lifting.EmbeddingDirectly 𝓣

η-fiber-same-as-is-defined : propext 𝓣
                           → funext 𝓣 𝓣
                           → funext 𝓣 𝓤
                           → funext 𝓤 (𝓣 ⁺ ⊔ 𝓤)
                           → (l : 𝓛 X) → (Σ x ꞉ X , η x ＝ l) ≃ is-defined l
η-fiber-same-as-is-defined pe fe fe' fe'' l = qinveq (f l) (g l , gf , fg)
 where
  f : (l : 𝓛 X) → fiber η l → is-defined l
  f (.𝟙 , .(λ _ → x) , .𝟙-is-prop) (x , refl) = ⋆

  g : (l : 𝓛 X) → is-defined l → fiber η l
  g (P , φ , i) p = φ p , ⊑-anti pe fe fe' (a , b)
   where
    a : η (φ p) ⊑ (P , φ , i)
    a = (λ _ → p) , (λ _ → refl)

    b : (P , φ , i) ⊑ η (φ p)
    b = (λ _ → ⋆) , (λ q → ap φ (i q p))

  fg : (d : is-defined l) → f l (g l d) ＝ d
  fg d = being-defined-is-prop l (f l (g l d)) d

  gf : (z : fiber η l) → g l (f l z) ＝ z
  gf z = η-is-embedding pe fe fe' fe'' l (g l (f l z)) z

\end{code}

They can't be equal, in the absence of cumulativity (and propositional
resizing), as the lhs lives in a universe higher than the rhs, and
equality is well-typed only for elements of the same type (here of the
same universe). This can be seen by adding type annotations to the
formulation of the above equivalence:

\begin{code}

private
 η-fiber-same-as-is-defined' : propext 𝓣
                             → funext 𝓣 𝓣
                             → funext 𝓣 𝓤
                             → funext 𝓤 (𝓣 ⁺ ⊔ 𝓤)
                             → (l : 𝓛 X) → (fiber η l    ∶ 𝓣 ⁺ ⊔ 𝓤 ̇ )
                                         ≃ (is-defined l ∶ 𝓣 ̇ )
 η-fiber-same-as-is-defined' = η-fiber-same-as-is-defined

\end{code}

For no choice of universes 𝓤 and 𝓣 can we have 𝓣 ⁺ ⊔ 𝓤 to coincide
with 𝓣. However, for some dominances other than is-prop, it is possible to
have the equality between the fiber of l and the definedness of l.

The following simplified proof of ⊑-anti uses the SIP via the
construction of _⋍·_ in another module:

\begin{code}

⊑-anti-sip : is-univalent 𝓣
           → funext 𝓣 𝓤
           → {l m : 𝓛 X} → (l ⊑ m) × (m ⊑ l) → l ＝ m
⊑-anti-sip ua fe {Q , ψ , j} {P , φ , i} ((f , δ) , (g , ε)) =
 ⌜ 𝓛-Id· ua fe (Q , ψ , j) (P , φ , i) ⌝⁻¹ γ
 where
  e : Q ≃ P
  e = f , ((g , (λ p → i (f (g p)) p)) , (g , (λ q → j (g (f q)) q)))

  γ : (Q , ψ , j) ⋍· (P , φ , i)
  γ = e , δ

\end{code}

Could the map (anti l m) be an equivalence? No. We instead have an
equivalence (l ⊑ m) × (m ⊑ l) → (l ＝ m) × (l ＝ m), reflecting the
fact that there are two candidate proofs for the equality.

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

  a : δ' ＝ δ
  a = being-equiv-is-prop'' fe f δ' δ

  b : (f , δ') , g ＝ (f , δ) , g
  b = ap (λ - → (f , -) , g) a

⊑-anti-equiv-lemma'' : funext 𝓣 𝓣 → (l m : 𝓛 X) → is-equiv (to-⋍· l m)
⊑-anti-equiv-lemma'' fe l m = qinvs-are-equivs
                               (to-⋍· l m)
                               (from-⋍· l m , from-to l m , to-from fe l m)

⊑-anti-equiv-lemma' : funext 𝓣 𝓣
                   → (l m : 𝓛 X)
                   → (l ⊑ m) × (is-defined m → is-defined l) ≃ (l ⋍· m)
⊑-anti-equiv-lemma' fe l m = to-⋍· l m , ⊑-anti-equiv-lemma'' fe l m

⊑-anti-equiv-lemma : is-univalent 𝓣
                   → funext 𝓣 𝓤
                   → (l m : 𝓛 X)
                   → (l ⊑ m) × (is-defined m → is-defined l) ≃ (l ＝ m)
⊑-anti-equiv-lemma ua fe l m =
  (⊑-anti-equiv-lemma' (univalence-gives-funext ua) l m)
  ● (≃-sym (𝓛-Id· ua fe l m))

⊑-anti-equiv : is-univalent 𝓣
             → funext 𝓣 𝓤
             → (l m : 𝓛 X)
             → (l ⊑ m) × (m ⊑ l) ≃ (l ＝ m) × (m ＝ l)
⊑-anti-equiv ua fe l m = γ ● (×-cong (⊑-anti-equiv-lemma ua fe l m)
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

     vu : (a : A) → v (u a) ＝ a
     vu a = refl

     uv : (b : B) → u (v b) ＝ b
     uv (((f , δ) , h) , ((g , ε) , k)) = t
      where
       r : g ＝ h
       r = dfunext
            (univalence-gives-funext ua)
            (λ p → being-defined-is-prop l (g p) (h p))
       s : f ＝ k
       s = dfunext
            (univalence-gives-funext ua)
            (λ p → being-defined-is-prop m (f p) (k p))

       t : ((f , δ) , g) , (g , ε) , f ＝ ((f , δ) , h) , (g , ε) , k
       t = ap₂ (λ -₀ -₁ → ((f , δ) , -₀) , (g , ε) , -₁) r s

\end{code}

Next we show that (l ⊑ m) ≃ (is-defined l → l ＝ m), so that elements
of l ⊑ m can be seen as partial elements of the identity type l ＝ m.

We begin with the following auxiliary construction, which shows that
the type l ⊑ m is modal for the open modality induced by the
proposition "is-defined l" (and gave me a headache):

\begin{code}

⊑-open : funext 𝓣 𝓣
       → funext 𝓣 (𝓣 ⊔ 𝓤)
       → (l m : 𝓛 X) → (l ⊑ m) ≃ (is-defined l → l ⊑ m)
⊑-open fe fe'' (Q , ψ , j) (P , φ , i) = qinveq π (ρ , ρπ , πρ)
 where
  l = (Q , ψ , j)

  m = (P , φ , i)

  π : l ⊑ m → (is-defined l → l ⊑ m)
  π α d = α

  ρ : (is-defined l → l ⊑ m) → l ⊑ m
  ρ h = (λ d → pr₁ (h d) d) , (λ d → pr₂ (h d) d)

  ρπ : ρ ∘ π ∼ id
  ρπ α = refl

  ρ-lemma : (h : is-defined l → l ⊑ m) (q : is-defined l) → ρ h ＝ h q
  ρ-lemma h q = γ
   where
    remark = h q  ＝⟨ refl ⟩  (λ d → pr₁ (h q) d) , (λ d → pr₂ (h q) d) ∎

    k : (d : Q) → pr₁ (h d) d ＝ pr₁ (h q) d
    k d = ap (λ - → pr₁ (h -) d) (j d q)

    a : (λ d → pr₁ (h d) d) ＝ pr₁ (h q)
    a = dfunext fe k

    u : (d : Q) {f g : Q → P} (k : f ∼ g)
      → ap (λ (- : Q → P) → φ (- d)) (dfunext fe k)
      ＝ ap φ (k d)
    u d {f} {g} k = ap-funext f g φ k fe d

    v : (d : Q) → pr₂ (h d) d ∙ ap (λ - → φ (- d)) a
                ＝ pr₂ (h q) d
    v d = pr₂ (h d) d ∙ ap (λ - → φ (- d)) a                  ＝⟨ using-u ⟩
          pr₂ (h d) d ∙ ap φ (ap (λ - → pr₁ (h -) d) (j d q)) ＝⟨ ap-ap-is-ap-of-∘ ⟩
          pr₂ (h d) d ∙ ap (λ - → φ (pr₁ (h -) d)) (j d q)    ＝⟨ by-naturality ⟩
          ap (λ _ → ψ d) (j d q) ∙ pr₂ (h q) d                ＝⟨ ap-const-is-refl ⟩
          refl ∙ pr₂ (h q) d                                  ＝⟨ refl-left-neutral ⟩
          pr₂ (h q) d                                         ∎
     where
      using-u = ap (λ - → pr₂ (h d) d ∙ -) (u d k)
      ap-ap-is-ap-of-∘ = ap (λ - → pr₂ (h d) d ∙ -) (ap-ap (λ - → pr₁ (h -) d) φ (j d q))
      by-naturality = homotopies-are-natural
                       (λ _ → ψ d) (λ - → φ (pr₁ (h -) d)) (λ - → pr₂ (h -) d)
                       {d} {q} {j d q}
      ap-const-is-refl = ap (λ - → - ∙ pr₂ (h q) d) (ap-const (ψ d) (j d q))

    t : {f g : Q → P} (r : f ＝ g) (h : ψ ∼ φ ∘ f)
      → transport (λ - → ψ ∼ φ ∘ -) r h
      ＝ λ q → h q ∙ ap (λ - → φ (- q)) r
    t refl h = refl

    b = transport (λ - → ψ ∼ φ ∘ -) a (λ d → pr₂ (h d) d) ＝⟨ t a (λ d → pr₂ (h d) d) ⟩
        (λ d → pr₂ (h d) d ∙ ap (λ - → φ (- d)) a)        ＝⟨ dfunext (lower-funext 𝓣 𝓣 fe'') v ⟩
        pr₂ (h q)                                         ∎

    γ : (λ d → pr₁ (h d) d) , (λ d → pr₂ (h d) d) ＝ h q
    γ = to-Σ-＝ (a , b)

  πρ :  π ∘ ρ ∼ id
  πρ h = dfunext fe'' (ρ-lemma h)

\end{code}

Using this we have the following, as promised:

\begin{code}

⊑-in-terms-of-＝ : is-univalent 𝓣
                → funext 𝓣 (𝓣 ⁺ ⊔ 𝓤)
                → (l m : 𝓛 X) → (l ⊑ m) ≃ (is-defined l → l ＝ m)
⊑-in-terms-of-＝ ua fe⁺ l m =
 l ⊑ m                                                                 ≃⟨ a ⟩
 (is-defined l → l ⊑ m)                                                ≃⟨ b ⟩
 ((is-defined l → l ⊑ m) × 𝟙)                                          ≃⟨ c ⟩
 (is-defined l → l ⊑ m) × (is-defined l → is-defined m → is-defined l) ≃⟨ d ⟩
 (is-defined l → (l ⊑ m) × (is-defined m → is-defined l))              ≃⟨ e ⟩
 (is-defined l → l ＝ m)                                                ■
 where
  fe : funext 𝓣 𝓣
  fe = univalence-gives-funext ua
  s : (is-defined l → is-defined m → is-defined l) ≃ 𝟙 {𝓤}
  s = singleton-≃-𝟙
       ((λ d e → d) ,
        Π-is-prop fe
          (λ d → Π-is-prop fe
                   (λ e → being-defined-is-prop l)) (λ d e → d))

  a = ⊑-open fe (lower-funext 𝓣 ((𝓣 ⁺) ⊔ 𝓤) fe⁺) l m
  b =  ≃-sym 𝟙-rneutral
  c = ×-cong (≃-refl _) (≃-sym s)
  d = ≃-sym ΠΣ-distr-≃
  e = →cong fe⁺
       (lower-funext 𝓣 ((𝓣 ⁺) ⊔ 𝓤) fe⁺)
       (≃-refl (is-defined l))
       (⊑-anti-equiv-lemma ua (lower-funext 𝓣 ((𝓣 ⁺) ⊔ 𝓤) fe⁺) l m)

\end{code}

And we also get the promised map l ⊑ m → 𝓛 (l ＝ m) that regards
elements of hom-type l ⊑ m as partial element of identity the type l ＝ m.
(Conjectural conjecture: this map is an embedding.)

TODO. This map should be an embedding.

\begin{code}

⊑-lift : is-univalent 𝓣
       → funext 𝓣 (𝓣 ⁺ ⊔ 𝓤)
       → (l m : 𝓛 X) → l ⊑ m → 𝓛 (l ＝ m)
⊑-lift ua fe l m α = is-defined l ,
                     ⌜ ⊑-in-terms-of-＝ ua fe l m ⌝ α ,
                     being-defined-is-prop l
\end{code}

We now show that the pre-∞-category 𝓛 X is univalent if the universe 𝓣
is univalent and we have enough function extensionality for 𝓣 and 𝓤.

\begin{code}

𝓛-pre-comp-with : (l m : 𝓛 X) → l ⊑ m → (n : 𝓛 X) → m ⊑ n → l ⊑ n
𝓛-pre-comp-with l m α n = 𝓛-comp l m n α

is-𝓛-equiv : (l m : 𝓛 X) → l ⊑ m → 𝓣 ⁺ ⊔ 𝓤 ̇
is-𝓛-equiv l m α = (n : 𝓛 X) → is-equiv (𝓛-pre-comp-with l m α n)

being-𝓛-equiv-is-prop : funext (𝓣 ⁺ ⊔ 𝓤) (𝓣 ⊔ 𝓤)
                      → (l m : 𝓛 X) (α : l ⊑ m) → is-prop (is-𝓛-equiv l m α)
being-𝓛-equiv-is-prop fe l m α =
 Π-is-prop fe
  (λ n → being-equiv-is-prop''
          (lower-funext (𝓣 ⁺) 𝓤 fe)
          (𝓛-pre-comp-with l m α n))

is-𝓛-equiv→ : (l m : 𝓛 X) (α : l ⊑ m) → is-𝓛-equiv l m α → is-equiv (pr₁ α)
is-𝓛-equiv→ l m α e = qinvs-are-equivs
                       (pr₁ α)
                       (pr₁ β ,
                        (λ p → being-defined-is-prop l (pr₁ β (pr₁ α p)) p) ,
                        (λ q → being-defined-is-prop m (pr₁ α (pr₁ β q)) q))
 where
  u : m ⊑ l → l ⊑ l
  u = 𝓛-pre-comp-with l m α l
  β : m ⊑ l
  β = inverse u (e l) (𝓛-id l)

is-𝓛-equiv← : propext 𝓣
            → funext 𝓣 𝓣
            → funext 𝓣 𝓤
            → (l m : 𝓛 X) (α : l ⊑ m) → is-equiv (pr₁ α) → is-𝓛-equiv l m α
is-𝓛-equiv← pe fe fe' l m α e = γ
 where
  r : l ＝ m
  r = ⊑-anti-lemma pe fe fe' α (inverse (pr₁ α) e)

  π : (l n : 𝓛 X) (α : l ⊑ l) → pr₁ α ＝ id
    → Σ δ ꞉ ((q : is-defined l) → value l q ＝ value l q)
          , 𝓛-pre-comp-with l l α n
            ∼ λ β → pr₁ β , (λ q → δ q ∙ pr₂ β q)
  π l n (.id , δ) refl = δ , λ β → refl

  ρ : (l : 𝓛 X) (α : l ⊑ l) → is-equiv (pr₁ α) → is-𝓛-equiv l l α
  ρ l α e n = equiv-closed-under-∼ u (𝓛-pre-comp-with l l α n) i h
   where
    s : pr₁ α ＝ id
    s = dfunext fe (λ q → being-defined-is-prop l (pr₁ α q) q)

    δ : (q : is-defined l) → value l q ＝ value l q
    δ = pr₁ (π l n α s)

    u : l ⊑ n → l ⊑ n
    u β = pr₁ β , λ q → δ q ∙ pr₂ β q

    h : 𝓛-pre-comp-with l l α n ∼ u
    h = pr₂ (π l n α s)

    v : l ⊑ n → l ⊑ n
    v γ = pr₁ γ , (λ p → (δ p)⁻¹ ∙ pr₂ γ p)

    vu : v ∘ u ∼ id
    vu (g , ε) = to-Σ-＝ (refl , a)
     where
      a = dfunext fe' (λ q →  (δ q)⁻¹ ∙ (δ q ∙ ε q)  ＝⟨ (∙assoc ((δ q)⁻¹) (δ q) (ε q))⁻¹ ⟩
                             ((δ q)⁻¹ ∙ δ q) ∙ ε q   ＝⟨ ap (λ - → - ∙ ε q) ((sym-is-inverse (δ q))⁻¹)⟩
                               refl ∙ ε q            ＝⟨ refl-left-neutral ⟩
                               ε q                   ∎)

    uv : u ∘ v ∼ id
    uv (g , ε) = to-Σ-＝ (refl , a)
     where
      a = dfunext fe' (λ q →  δ q ∙ ((δ q)⁻¹ ∙ ε q)  ＝⟨ (∙assoc (δ q) ((δ q)⁻¹) (ε q))⁻¹ ⟩
                             (δ q ∙ ((δ q)⁻¹)) ∙ ε q ＝⟨ ap (λ - → - ∙ ε q) ((sym-is-inverse' (δ q))⁻¹)⟩
                              refl ∙ ε q             ＝⟨ refl-left-neutral ⟩
                              ε q                    ∎)
    i : is-equiv u
    i = qinvs-are-equivs u (v , vu , uv)

  σ : (l m : 𝓛 X)  → l ＝ m → (α : l ⊑ m) → is-equiv (pr₁ α) → is-𝓛-equiv l m α
  σ l .l refl = ρ l

  γ : is-𝓛-equiv l m α
  γ = σ l m r α e

\end{code}

With this and Yoneda we can now easily derive the univalence of the
pre-∞-category 𝓛 X.

The univalence of 𝓣 is more than we need in the
following. Propositional extensionality for propositions in 𝓣
suffices, but the way we proved this using a general SIP relies on
univalence (we could prove a specialized version of the SIP, but this
is probably not worth the trouble (we'll see)).

\begin{code}

module univalence-of-𝓛 (ua : is-univalent 𝓣)
                       (fe : Fun-Ext)
       where

 pe : propext 𝓣
 pe = univalence-gives-propext ua

 is-𝓛-equiv-charac : (l m : 𝓛 X) (α : l ⊑ m)
                   → is-𝓛-equiv l m α ≃ (is-defined m → is-defined l)
 is-𝓛-equiv-charac l m α = is-𝓛-equiv l m α              ≃⟨ a ⟩
                           is-equiv (pr₁ α)              ≃⟨ b ⟩
                           (is-defined m → is-defined l) ■
  where
   a = logically-equivalent-props-are-equivalent
        (being-𝓛-equiv-is-prop fe l m α)
        (being-equiv-is-prop'' fe (pr₁ α))
        (is-𝓛-equiv→ l m α)
        (is-𝓛-equiv← pe fe fe l m α)

   b = logically-equivalent-props-are-equivalent
        (being-equiv-is-prop'' fe (pr₁ α))
        (Π-is-prop fe (λ p → being-defined-is-prop l))
        (inverse (pr₁ α))
        (λ g → qinvs-are-equivs
                (pr₁ α)
                (g ,
                 (λ q → being-defined-is-prop l (g (pr₁ α q)) q) ,
                 (λ p → being-defined-is-prop m (pr₁ α (g p)) p)))

 _≃⟨𝓛⟩_ : 𝓛 X → 𝓛 X → 𝓣 ⁺ ⊔ 𝓤 ̇
 l ≃⟨𝓛⟩ m = Σ α ꞉ l ⊑ m , is-𝓛-equiv l m α

 ≃⟨𝓛⟩-charac : (l m : 𝓛 X)
             → (l ≃⟨𝓛⟩ m) ≃ (l ⊑ m) × (is-defined m → is-defined l)
 ≃⟨𝓛⟩-charac l m = Σ-cong (is-𝓛-equiv-charac l m)

 ≃⟨𝓛⟩-is-Id : (l m : 𝓛 X)
            → (l ≃⟨𝓛⟩ m) ≃ (l ＝ m)
 ≃⟨𝓛⟩-is-Id l m = (≃⟨𝓛⟩-charac l m) ● (⊑-anti-equiv-lemma ua fe l m)

 𝓛-is-univalent' : (l : 𝓛 X) → ∃! m ꞉ 𝓛 X , (l ≃⟨𝓛⟩ m)
 𝓛-is-univalent' l = equiv-to-singleton e (singleton-types-are-singletons l)
  where
    e : (Σ m ꞉ 𝓛 X , l ≃⟨𝓛⟩ m) ≃ (Σ m ꞉ 𝓛 X , l ＝ m)
    e = Σ-cong (≃⟨𝓛⟩-is-Id l)

 𝓛-id-is-𝓛-equiv : (l : 𝓛 X) → is-𝓛-equiv l l (𝓛-id l)
 𝓛-id-is-𝓛-equiv l n = (id , h) , (id , h)
  where
   h : 𝓛-pre-comp-with l l (𝓛-id l) n ∼ id
   h (f , δ) = to-Σ-＝ (refl , dfunext fe (λ p → refl-left-neutral))

 𝓛-refl : (l : 𝓛 X) → l ≃⟨𝓛⟩ l
 𝓛-refl l = 𝓛-id l , 𝓛-id-is-𝓛-equiv l

 Id-to-𝓛-eq : (l m : 𝓛 X) → l ＝ m → l ≃⟨𝓛⟩ m
 Id-to-𝓛-eq l m r = transport (l ≃⟨𝓛⟩_) r (𝓛-refl l)

 𝓛-is-univalent : (l m : 𝓛 X) → is-equiv (Id-to-𝓛-eq l m)
 𝓛-is-univalent l = universality-equiv l (𝓛-refl l)
                     (central-point-is-universal (l ≃⟨𝓛⟩_) (l , 𝓛-refl l)
                       (singletons-are-props (𝓛-is-univalent' l) (l , 𝓛-refl l)))
  where
   open import UF.Yoneda

 \end{code}

This completes the main goal of the module.

We have yet another equivalence, using the above techniques:

\begin{code}

η-maximal : (x : X) (l : 𝓛 X) → η x ⊑ l → l ⊑ η x
η-maximal x (P , ψ , i) (f , δ) = (λ p → ⋆) , (λ p → ap ψ (i p (f ⋆)) ∙ (δ ⋆)⁻¹)

⊥-least : (l : 𝓛 X) → ⊥ ⊑ l
⊥-least l = unique-from-𝟘 , λ z → unique-from-𝟘 z

⊥-initial : funext 𝓣 𝓣
          → funext 𝓣 𝓤
          → (l : 𝓛 X) → is-singleton (⊥ ⊑ l)
⊥-initial fe fe' l = ⊥-least l ,
                     (λ α → to-Σ-＝ (dfunext fe (λ z → unique-from-𝟘 z) ,
                                     dfunext fe'(λ z → unique-from-𝟘 z)))

η-＝-gives-⊑ : {x y : X} → x ＝ y → η x ⊑ η y
η-＝-gives-⊑ {x} {y} p = id , (λ d → p)

η-⊑-gives-＝ : {x y : X} → η x ⊑ η y → x ＝ y
η-⊑-gives-＝ (f , δ) = δ ⋆

η-＝-gives-⊑-is-equiv : funext 𝓣 𝓣
                     → funext 𝓣 𝓤
                     → {x y : X} → is-equiv (η-＝-gives-⊑ {x} {y})
η-＝-gives-⊑-is-equiv fe fe' {x} {y} =
 qinvs-are-equivs η-＝-gives-⊑ (η-⊑-gives-＝ , α , β)
 where
  α : {x y : X} (p : x ＝ y) →  η-⊑-gives-＝ (η-＝-gives-⊑ p) ＝ p
  α p = refl

  β : {x y : X} (q : η x ⊑ η y) → η-＝-gives-⊑ (η-⊑-gives-＝ q) ＝ q
  β (f , δ) = to-×-＝
               (dfunext fe (λ x → 𝟙-is-prop x (f x)))
               (dfunext fe' (λ x → ap δ (𝟙-is-prop ⋆ x)))

Id-via-lifting : funext 𝓣 𝓣
               → funext 𝓣 𝓤
               → {x y : X} → (x ＝ y) ≃ (η x ⊑ η y)
Id-via-lifting fe fe' = η-＝-gives-⊑ , η-＝-gives-⊑-is-equiv fe fe'

\end{code}
