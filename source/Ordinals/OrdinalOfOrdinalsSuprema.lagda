Tom de Jong, March 2022

We show that the ordinal of ordinals has small suprema. More precisely, given a
univalent universe 𝓤, the ordinal (Ordinal 𝓤) of ordinals in 𝓤 has suprema for
every family I → Ordinal 𝓤 with I : 𝓤.

We extend and formalize Lemma 10.3.22 of [Uni2013] where the given construction
is only claimed to be an upper bound. Our development also extends [Theorem 9,
KFX2021] where the least upper bound property is only shown for weakly increasing
ℕ-indexed families.

We also include an alternative construction of suprema due to Martín Escardó that
notably doesn't use set quotients.

[Uni2013] The Univalent Foundations Program.
          Homotopy Type Theory: Univalent Foundations of Mathematics.
          https://homotopytypetheory.org/book, Institute for Advanced Study, 2013.

[KFX2021] Nicolai Kraus, Fredrik Nordvall Forsberg and Chuangjie Xu.
          Connecting Constructive Notions of Ordinals in Homotopy Type Theory.
          In Filippo Bonchi and Simon J. Puglisi, editors, 46th International
          Symposium on Mathematical Foundations of Computer Science (MFCS 2021),
          volume 202 of Leibniz International Proceedings in Informatics
          (LIPIcs), pages: 70:1─70:16. Schloss Dagstuhl ─ Leibniz-Zentrum für
          Informatik, 2021. doi:10.4230/LIPIcs.MFCS.2021.70.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}


open import Quotient.Type
open import UF.Univalence

module Ordinals.OrdinalOfOrdinalsSuprema
        (ua : Univalence)
       where

open import MLTT.Spartan
open import Ordinals.Equivalence
open import Ordinals.Maps
open import Ordinals.Notions hiding (is-prop-valued)
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.Type
open import Ordinals.Underlying
open import Quotient.GivesPropTrunc
open import Quotient.GivesSetReplacement
open import UF.Base hiding (_≈_)
open import UF.Equiv
open import UF.FunExt
open import UF.PropTrunc
open import UF.Size
open import UF.SubtypeClassifier
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.UA-FunExt

private
 fe : FunExt
 fe = Univalence-gives-FunExt ua

 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

 pe : PropExt
 pe = Univalence-gives-PropExt ua

 pe' : Prop-Ext
 pe' {𝓤} = pe 𝓤

open import Ordinals.WellOrderTransport fe

\end{code}

The following defines what it means for the ordinal of ordinals in a universe to
have small suprema. A proof of this statement will be given at the end by
ordinal-of-ordinals-has-small-suprema.

(Although it is not needed at present, we prove for good measure that the
statement is a proposition.)

\begin{code}

Ordinal-Of-Ordinals-Has-Small-Suprema : (𝓤 : Universe) → 𝓤 ⁺ ̇
Ordinal-Of-Ordinals-Has-Small-Suprema 𝓤 =
   (I : 𝓤 ̇ ) (α : I → Ordinal 𝓤)
 → Σ β ꞉ Ordinal 𝓤 , ((i : I) → α i ⊴ β)
                   × ((γ : Ordinal 𝓤) → ((i : I) → α i ⊴ γ) → β ⊴ γ)

Ordinal-Of-Ordinals-Has-Small-Suprema-is-prop :
 is-prop (Ordinal-Of-Ordinals-Has-Small-Suprema 𝓤)
Ordinal-Of-Ordinals-Has-Small-Suprema-is-prop =
 Π₂-is-prop fe' h
  where
   h : (I : 𝓤 ̇ ) (α : I → Ordinal 𝓤)
     → is-prop (Σ β ꞉ Ordinal 𝓤 , ((i : I) → α i ⊴ β)
                                × ((γ : Ordinal 𝓤) → ((i : I) → α i ⊴ γ)
                                                   → β ⊴ γ))
   h I α (β , β-is-ub , β-is-lb) (β' , β'-is-ub , β'-is-lb) =
    to-subtype-＝ (λ β → ×-is-prop
                         (Π-is-prop  fe' (λ i   → ⊴-is-prop-valued (α i) β))
                         (Π₂-is-prop fe' (λ γ _ → ⊴-is-prop-valued β     γ)))
                 (⊴-antisym β β' (β-is-lb β' β'-is-ub) (β'-is-lb β β-is-ub))

module construction-using-quotient
        (sq : set-quotients-exist)
        {I : 𝓤 ̇ }
        (α : I → Ordinal 𝓤)
       where

 open general-set-quotients-exist sq

 private
  pt : propositional-truncations-exist
  pt = propositional-truncations-from-set-quotients sq fe'

 open extending-relations-to-quotient fe' pe'
 open PropositionalTruncation pt

\end{code}

Given a small family of ordinals α : I → Ordinal 𝓤, we construct the supremum
(following [Lemma 10.3.22, Uni2013]) as a (set) quotient of Σ i ꞉ I , ⟨ α i ⟩.

We only construct the quotient later, as a lot of the work is performed on the
unquotiented type Σ i ꞉ I , ⟨ α i ⟩.

\begin{code}
 private
  Σα : 𝓤 ̇
  Σα = Σ i ꞉ I , ⟨ α i ⟩

  _≈_ : Σα → Σα → 𝓤 ⁺ ̇
  (i , x) ≈ (j , y) = (α i ↓ x) ＝ (α j ↓ y)

  _≺_ : Σα → Σα → 𝓤 ⁺ ̇
  (i , x) ≺ (j , y) = (α i ↓ x) ⊲ (α j ↓ y)

  ≺-is-prop-valued : is-prop-valued _≺_
  ≺-is-prop-valued (i , x) (j , y) = ⊲-is-prop-valued (α i ↓ x) (α j ↓ y)

  ≺-is-transitive : transitive _≺_
  ≺-is-transitive (i , x) (j , y) (k , z) =
   ⊲-is-transitive (α i ↓ x) (α j ↓ y) (α k ↓ z)

  ≺-is-well-founded : is-well-founded _≺_
  ≺-is-well-founded = transfinite-induction-converse _≺_ wf
   where
    wf : is-Well-founded _≺_
    wf P IH (i , x) = lemma (α i ↓ x) i x refl
     where
      P̃ : Ordinal 𝓤 → 𝓤 ⁺ ̇
      P̃ β = (i : I) (x : ⟨ α i ⟩) → β ＝ (α i ↓ x) → P (i , x)
      lemma : (β : Ordinal 𝓤) → P̃ β
      lemma = transfinite-induction _⊲_ ⊲-is-well-founded P̃ claim
       where
        claim : (β : Ordinal 𝓤) → ((γ : Ordinal 𝓤) → γ ⊲ β → P̃ γ) → P̃ β
        claim β IH' i x refl = IH (i , x) subclaim
         where
          subclaim : ((j , y) : Σα) → (j , y) ≺ (i , x) → P (j , y)
          subclaim (j , y) (z , e) = IH' ((α i ↓ x) ↓ z) (z , refl) j y (e ⁻¹)

\end{code}

The following lemma makes it clear why we eventually pass to the quotient.

\begin{code}

  ≺-is-extensional-up-to-≈ : (p q : Σα)
                           → ((r : Σα) → r ≺ p → r ≺ q)
                           → ((r : Σα) → r ≺ q → r ≺ p)
                           → p ≈ q
  ≺-is-extensional-up-to-≈ (i , x) (j , y) hyp₁ hyp₂ = e
   where
    e : (α i ↓ x) ＝ (α j ↓ y)
    e = ⊲-is-extensional (α i ↓ x) (α j ↓ y) ⦅1⦆ ⦅2⦆
     where
      ⦅1⦆ : (β : Ordinal 𝓤) → β ⊲ (α i ↓ x) → β ⊲ (α j ↓ y)
      ⦅1⦆ β (p , refl) = u
       where
        u : ((α i ↓ x) ↓ p) ⊲ (α j ↓ y)
        u = transport⁻¹ (_⊲ (α j ↓ y)) claim₂ claim₁
         where
          x' : ⟨ α i ⟩
          x' = pr₁ p
          l : x' ≺⟨ α i ⟩ x
          l = pr₂ p
          claim₁ : (α i ↓ x') ⊲ (α j ↓ y)
          claim₁ = hyp₁ (i , x') (↓-preserves-order (α i) x' x l)
          claim₂ : ((α i ↓ x) ↓ p) ＝ (α i ↓ x')
          claim₂ = iterated-↓ (α i) x x' l
      ⦅2⦆ : (β : Ordinal 𝓤) → β ⊲ (α j ↓ y) → β ⊲ (α i ↓ x)
      ⦅2⦆ β (p , refl) = v
       where
        v : ((α j ↓ y) ↓ p) ⊲ (α i ↓ x)
        v = transport⁻¹ (_⊲ (α i ↓ x)) claim₂ claim₁
         where
          y' : ⟨ α j ⟩
          y' = pr₁ p
          l : y' ≺⟨ α j ⟩ y
          l = pr₂ p
          claim₁ : (α j ↓ y') ⊲ (α i ↓ x)
          claim₁ = hyp₂ (j , y') (↓-preserves-order (α j) y' y l)
          claim₂ : ((α j ↓ y) ↓ p) ＝ (α j ↓ y')
          claim₂ = iterated-↓ (α j) y y' l

\end{code}

The above suffies to prove that the quotient of Σα will be an ordinal. We now
prepare to prove that it will be the supremum of α.

\begin{code}

  ι : (i : I) → ⟨ α i ⟩ → Σα
  ι i x = (i , x)

  ι-is-order-preserving : (i : I) (x y : ⟨ α i ⟩)
                        → x ≺⟨ α i ⟩ y → ι i x ≺ ι i y
  ι-is-order-preserving i x y l = ↓-preserves-order (α i) x y l

  ι-is-initial-segment-up-to-≈ : (i : I) (x : ⟨ α i ⟩) ((j , y) : Σα)
                               → (j , y) ≺ ι i x
                               → Σ x' ꞉ ⟨ α i ⟩ , (x' ≺⟨ α i ⟩ x)
                                                × (ι i x' ≈ (j , y))
  ι-is-initial-segment-up-to-≈ i x (j , y) (p , e) = (x' , l , (eq ⁻¹))
   where
    x' : ⟨ α i ⟩
    x' = pr₁ p
    l : x' ≺⟨ α i ⟩ x
    l = pr₂ p
    eq : (α j ↓ y) ＝ (α i ↓ x')
    eq = (α j ↓ y)       ＝⟨ e ⟩
         ((α i ↓ x) ↓ p) ＝⟨ iterated-↓ (α i) x x' l ⟩
         (α i ↓ x')      ∎


  module lower-bound-of-upper-bounds-proof
          (β : Ordinal 𝓤)
          (β-is-upper-bound : (i : I) → α i ⊴ β)
         where

   f : (i : I) → ⟨ α i ⟩ → ⟨ β ⟩
   f i x = pr₁ (β-is-upper-bound i) x

   f-key-property : (i : I) (x : ⟨ α i ⟩) → α i ↓ x ＝ β ↓ (f i x)
   f-key-property i x =
    pr₂ (⊴-gives-≼ (α i) β (β-is-upper-bound i) (α i ↓ x) (x , refl))

   f̃ : Σα → ⟨ β ⟩
   f̃ (i , x) = f i x

   β-is-upper-bound-≼ : (i : I) → α i ≼ β
   β-is-upper-bound-≼ i = ⊴-gives-≼ (α i) β (β-is-upper-bound i)

   f̃-respects-≈ : {p q : Σα} → p ≈ q → f̃ p ＝ f̃ q
   f̃-respects-≈ {(i , x)} {(j , y)} e = ↓-lc β (f̃ (i , x)) (f̃ (j , y)) eq
    where
     eq = (β ↓ f̃ (i , x)) ＝⟨ (f-key-property i x) ⁻¹ ⟩
          (α i ↓ x)       ＝⟨ e ⟩
          (α j ↓ y)       ＝⟨ f-key-property j y ⟩
          (β ↓ f̃ (j , y)) ∎

   f̃-is-order-preserving : (p q : Σα) → p ≺ q → f̃ p ≺⟨ β ⟩ f̃ q
   f̃-is-order-preserving (i , x) (j , y) l =
    ↓-reflects-order β (f̃ (i , x)) (f̃ (j , y)) k
     where
      k : (β ↓ f̃ (i , x)) ⊲ (β ↓ f̃ (j , y))
      k = transport₂ _⊲_ (f-key-property i x) (f-key-property j y) l

   f̃-is-initial-segment : (p : Σα) (b : ⟨ β ⟩)
                        → b ≺⟨ β ⟩ f̃ p
                        → Σ q ꞉ Σα , (q ≺ p) × (f̃ q ＝ b)
   f̃-is-initial-segment (i , x) b l = (i , x') , u , v
    where
     lemma : Σ x' ꞉ ⟨ α i ⟩ , (x' ≺⟨ α i ⟩ x) × (f i x' ＝ b)
     lemma = simulations-are-initial-segments (α i) β
              (f i) (pr₂ (β-is-upper-bound i))
              x b l
     x' : ⟨ α i ⟩
     x' = pr₁ lemma
     x'-below-x : x' ≺⟨ α i ⟩ x
     x'-below-x = pr₁ (pr₂ lemma)

     u : (α i ↓ x') ⊲ (α i ↓ x)
     u = ↓-preserves-order (α i) x' x x'-below-x
     v : f̃ (i , x') ＝ b
     v = pr₂ (pr₂ lemma)

\end{code}

It is now time to pass to the quotient and prove that it is an ordinal with the
induced order on Σα.

\begin{code}

 ≋ : EqRel Σα
 ≋ = _≈_ , (λ _ _   → the-type-of-ordinals-is-a-set (ua 𝓤) fe')
         , (λ _     → refl)
         , (λ _ _   → _⁻¹)
         , (λ _ _ _ → _∙_)

 α/ : 𝓤 ⁺ ̇
 α/ = Σα / ≋

 private
  _≺[Ω]_ : Σα → Σα → Ω (𝓤 ⁺)
  p ≺[Ω] q = (p ≺ q , ≺-is-prop-valued p q)

  ≺-congruence : {p q p' q' : Σα} → p ≈ p' → q ≈ q'
               → (p ≺[Ω] q) ＝ (p' ≺[Ω] q')
  ≺-congruence {(i , x)} {(j , y)} {(i' , x')} {(j' , y')} e₁ e₂ =
   Ω-extensionality pe' fe' ⦅1⦆ ⦅2⦆
    where
     ⦅1⦆ : (α i ↓ x) ⊲ (α j ↓ y) → (α i' ↓ x') ⊲ (α j' ↓ y')
     ⦅1⦆ l = transport₂ _⊲_ e₁ e₂ l
     ⦅2⦆ : (α i' ↓ x') ⊲ (α j' ↓ y') → (α i ↓ x) ⊲ (α j ↓ y)
     ⦅2⦆ l = transport₂ _⊲_ (e₁ ⁻¹) (e₂ ⁻¹) l

  _≺/[Ω]_ : α/ → α/ → Ω (𝓤 ⁺)
  _≺/[Ω]_ = extension-rel₂ ≋ (λ x y → x ≺ y , ≺-is-prop-valued x y)
                                     ≺-congruence

  [_] : Σα → α/
  [_] = η/ ≋

 _≺/_ : α/ → α/ → 𝓤 ⁺ ̇
 x ≺/ y = (x ≺/[Ω] y) holds

 ≺/-＝-≺ : {p q : Σα} → [ p ] ≺/ [ q ] ＝ p ≺ q
 ≺/-＝-≺ {p} {q} = ap pr₁ (extension-rel-triangle₂ ≋ _≺[Ω]_ ≺-congruence p q)

 ≺/-to-≺ : {p q : Σα} → [ p ] ≺/ [ q ] → p ≺ q
 ≺/-to-≺ = Idtofun ≺/-＝-≺

 ≺-to-≺/ : {p q : Σα} → p ≺ q → [ p ] ≺/ [ q ]
 ≺-to-≺/ = Idtofun⁻¹ ≺/-＝-≺

 ≺/-is-prop-valued : is-prop-valued _≺/_
 ≺/-is-prop-valued x y = holds-is-prop (x ≺/[Ω] y)

 ≺/-is-transitive : transitive _≺/_
 ≺/-is-transitive = /-induction₃ fe' ≋ ρ γ
  where
   ρ : (x y z : α/) → is-prop (x ≺/ y → y ≺/ z → x ≺/ z)
   ρ x y z = Π₂-is-prop fe' (λ _ _ → ≺/-is-prop-valued x z)
   γ : (p q r : Σα) → [ p ] ≺/ [ q ] → [ q ] ≺/ [ r ] → [ p ] ≺/ [ r ]
   γ p q r k l = ≺-to-≺/ (≺-is-transitive p q r (≺/-to-≺ k) (≺/-to-≺ l))

 ≺/-is-extensional : is-extensional _≺/_
 ≺/-is-extensional = /-induction₂ fe' ≋
                      (λ x y → Π₂-is-prop fe' (λ _ _ → /-is-set ≋))
                      γ
  where
   γ : (p q : Σα)
     → ((z : α/) → z ≺/ [ p ] → z ≺/ [ q ])
     → ((z : α/) → z ≺/ [ q ] → z ≺/ [ p ])
     → [ p ] ＝ [ q ]
   γ p q u v = η/-identifies-related-points ≋ e
    where
     e : p ≈ q
     e = ≺-is-extensional-up-to-≈ p q u' v'
      where
       u' : (r : Σα) → r ≺ p → r ≺ q
       u' r l = ≺/-to-≺ (u [ r ] (≺-to-≺/ l))
       v' : (r : Σα) → r ≺ q → r ≺ p
       v' r l = ≺/-to-≺ (v [ r ] (≺-to-≺/ l))

 ≺/-is-well-founded : is-well-founded _≺/_
 ≺/-is-well-founded = γ
  where
   a : (x : α/) → is-prop (is-accessible _≺/_ x)
   a = accessibility-is-prop _≺/_ fe
   lemma : (p : Σα) → is-accessible _≺/_ [ p ]
   lemma = transfinite-induction _≺_ ≺-is-well-founded
            (λ p → is-accessible _≺/_ [ p ]) ϕ
    where
     ϕ : (p : Σα) → ((q : Σα) → q ≺ p → is-accessible _≺/_ [ q ])
       → is-accessible _≺/_ [ p ]
     ϕ p IH = acc IH'
      where
       IH' : (y : α/) → y ≺/ [ p ] → is-accessible _≺/_ y
       IH' = /-induction ≋ (λ q → Π-is-prop fe' (λ _ → a q))
              (λ q l → IH q (≺/-to-≺ l))
   γ : (x : α/) → is-accessible _≺/_ x
   γ = /-induction ≋ a lemma

 ≺/-is-well-order : is-well-order _≺/_
 ≺/-is-well-order =
  ≺/-is-prop-valued , ≺/-is-well-founded , ≺/-is-extensional , ≺/-is-transitive

 α/-Ord : Ordinal (𝓤 ⁺)
 α/-Ord = α/ , _≺/_ , ≺/-is-well-order

\end{code}

Next, we show that the quotient α/ is the least upper bound of α.

\begin{code}

 α/-is-upper-bound : (i : I) → α i ⊴ α/-Ord
 α/-is-upper-bound i = ([_] ∘ ι i , sim)
  where
   sim : is-simulation (α i) α/-Ord (λ x → [ i , x ])
   sim = simulation-unprime pt fe (α i) α/-Ord (λ x → [ i , x ])
          (init-seg , order-pres)
    where
     order-pres : is-order-preserving (α i) α/-Ord (λ x → [ i , x ])
     order-pres x y l = ≺-to-≺/ {i , x} {i , y} (ι-is-order-preserving i x y l)
     init-seg : is-initial-segment' pt fe (α i) α/-Ord (λ x → [ i , x ])
     init-seg x = /-induction ≋ (λ y → Π-is-prop fe' λ _ → ∃-is-prop) claim
      where
       claim : (p : Σα) → [ p ] ≺/ [ i , x ]
             → ∃ y ꞉ ⟨ α i ⟩ , (y ≺⟨ α i ⟩ x) × ([ i , y ] ＝ [ p ])
       claim p l = ∣ y , k , η/-identifies-related-points ≋ e ∣
        where
         abstract
          lem : Σ y ꞉ ⟨ α i ⟩ , (y ≺⟨ α i ⟩ x) × ((i , y) ≈ p)
          lem = ι-is-initial-segment-up-to-≈ i x p (≺/-to-≺ l)
          y : ⟨ α i ⟩
          y = pr₁ lem
          k : y ≺⟨ α i ⟩ x
          k = pr₁ (pr₂ lem)
          e : (i , y) ≈ p
          e = pr₂ (pr₂ lem)

 α/-is-lower-bound-of-upper-bounds : (β : Ordinal 𝓤)
                                   → ((i : I) → α i ⊴ β)
                                   → α/-Ord ⊴ β
 α/-is-lower-bound-of-upper-bounds β β-is-ub = f/ , f/-is-simulation
  where
   open lower-bound-of-upper-bounds-proof β β-is-ub
   f/ : α/ → ⟨ β ⟩
   f/ = mediating-map/ ≋ (underlying-type-is-set fe β) f̃ f̃-respects-≈
   f/-＝-f̃ : {p : Σα} → f/ [ p ] ＝ f̃ p
   f/-＝-f̃ {p} = universality-triangle/ ≋ (underlying-type-is-set fe β)
                 f̃ f̃-respects-≈ p
   f/-is-order-preserving : is-order-preserving α/-Ord β f/
   f/-is-order-preserving =
    /-induction₂ fe' ≋ prp ρ
     where
      prp : (x y : α/) → is-prop (x ≺/ y → f/ x ≺⟨ β ⟩ f/ y)
      prp x y = Π-is-prop fe' (λ _ → Prop-valuedness β (f/ x) (f/ y))
      ρ : (p q : Σα) → [ p ] ≺/ [ q ] → f/ [ p ] ≺⟨ β ⟩ f/ [ q ]
      ρ p q l = transport₂⁻¹ (λ -₁ -₂ → -₁ ≺⟨ β ⟩ -₂)
                 f/-＝-f̃ f/-＝-f̃
                 (f̃-is-order-preserving p q (≺/-to-≺ l))
   f/-is-simulation : is-simulation α/-Ord β f/
   f/-is-simulation = simulation-unprime pt fe α/-Ord β f/ σ
    where
     σ : is-simulation' pt fe α/-Ord β f/
     σ = init-seg , f/-is-order-preserving
      where
       init-seg : is-initial-segment' pt fe α/-Ord β f/
       init-seg = /-induction ≋ prp ρ
        where
         prp : (x : α/)
             → is-prop ((y : ⟨ β ⟩) → y ≺⟨ β ⟩ f/ x
                                    → ∃ x' ꞉ α/ , (x' ≺/ x) × (f/ x' ＝ y))
         prp x = Π₂-is-prop fe' (λ _ _ → ∃-is-prop)
         ρ : (p : Σα) (y : ⟨ β ⟩)
           → y ≺⟨ β ⟩ f/ [ p ]
           → ∃ x' ꞉ α/ , (x' ≺/ [ p ]) × (f/ x' ＝ y)
         ρ p y l = ∣ [ q ] , k , e ∣
          where
           abstract
            lem : Σ q ꞉ Σα , (q ≺ p) × (f̃ q ＝ y)
            lem = f̃-is-initial-segment p y
                   (transport (λ - → y ≺⟨ β ⟩ -) f/-＝-f̃ l)
            q : Σα
            q = pr₁ lem
            k : [ q ] ≺/ [ p ]
            k = ≺-to-≺/ {q} {p} (pr₁ (pr₂ lem))
            e : f/ [ q ] ＝ y
            e = f/ [ q ] ＝⟨ f/-＝-f̃ {q}    ⟩
                f̃    q   ＝⟨ pr₂ (pr₂ lem) ⟩
                y        ∎

\end{code}

In the above construction it is important to notice that α/ lives in the next
universe 𝓤 ⁺, so it does not prove that Ordinal 𝓤 has small suprema.

To prove this, we resize α/ down to an equivalent ordinal in 𝓤. The first step
in doing so, is proving that the order ≺ on α (which takes values in 𝓤 ⁺) is
equivalent to one with values in 𝓤.

\begin{code}

 private
  _≺⁻_ : Σα → Σα → 𝓤 ̇
  (i , x) ≺⁻ (j , y) = (α i ↓ x) ⊲⁻ (α j ↓ y)

  ≺-≃-≺⁻ : (p q : Σα) → (p ≺ q) ≃ (p ≺⁻ q)
  ≺-≃-≺⁻ (i , x) (j , y) = ⊲-is-equivalent-to-⊲⁻ (α i ↓ x) (α j ↓ y)

  ≺/-has-small-values : (x y : α/) → is-small (x ≺/ y)
  ≺/-has-small-values =
   /-induction₂ fe' ≋
    (λ x y → being-small-is-prop ua (x ≺/ y) 𝓤)
    (λ p q → p ≺⁻ q , (p ≺⁻ q         ≃⟨ ≃-sym (≺-≃-≺⁻ p q)     ⟩
                       p ≺ q          ≃⟨ idtoeq _ _ (≺/-＝-≺ ⁻¹) ⟩
                       [ p ] ≺/ [ q ] ■))

  _≺/⁻_ : α/ → α/ → 𝓤 ̇
  x ≺/⁻ y = pr₁ (≺/-has-small-values x y)

  ≺/-≃-≺/⁻ : {x y : α/} → x ≺/ y ≃ x ≺/⁻ y
  ≺/-≃-≺/⁻ {x} {y} = ≃-sym (pr₂ (≺/-has-small-values x y))

\end{code}

Next, we resize α/ using:
(1) The fact that, by univalence, (α i ↓ x) ＝ (α j ↓ y) is equivalent to
    (α i ↓ x) ≃ₒ (α j ↓ y), which means that ≈ is equivalent to a 𝓤-valued
    equivalence relation, yielding an equivalent quotient in 𝓤.
(2) Martín's machinery developed in OrdinalsWellOrderTransport to transport the
    well order along the equivalence of quotients.

\begin{code}

 ≋⁻ : EqRel Σα
 ≋⁻ = _≈⁻_ , ≈⁻p , ≈⁻r , ≈⁻s , ≈⁻t
  where
   _≈⁻_ : Σα → Σα → 𝓤 ̇
   (i , x) ≈⁻ (j , y) = (α i ↓ x) ≃ₒ (α j ↓ y)
   ≈⁻s : symmetric _≈⁻_
   ≈⁻s (i , x) (j , y) = ≃ₒ-sym (α i ↓ x) (α j ↓ y)
   ≈⁻t : transitive _≈⁻_
   ≈⁻t (i , x) (j , y) (k , z) = ≃ₒ-trans (α i ↓ x) (α j ↓ y) (α k ↓ z)
   ≈⁻r : reflexive _≈⁻_
   ≈⁻r (i , x) = ≃ₒ-refl (α i ↓ x)
   ≈⁻p : is-prop-valued _≈⁻_
   ≈⁻p (i , x) (j , y) = ≃ₒ-is-prop-valued fe' (α i ↓ x) (α j ↓ y)

 ≋-≃-≋⁻ : {p q : Σα} → p ≈[ ≋ ] q ↔ p ≈[ ≋⁻ ] q
 ≋-≃-≋⁻ {(i , x)} {(j , y)} = (idtoeqₒ (α i ↓ x) (α j ↓ y))
                            , (eqtoidₒ (ua 𝓤) fe' (α i ↓ x) (α j ↓ y))

 private
  α/⁻ : 𝓤 ̇
  α/⁻ = Σα / ≋⁻

  φ : α/ ≃ α/⁻
  φ = quotients-equivalent Σα ≋ ≋⁻ ≋-≃-≋⁻

  resize-ordinal : Σ s ꞉ OrdinalStructure α/⁻ , (α/⁻ , s) ≃ₒ α/-Ord
  resize-ordinal = transfer-structure α/⁻ α/-Ord (≃-sym φ)
                    (_≺/⁻_ , (λ x y → ≺/-≃-≺/⁻))

 α/⁻-Ord : Ordinal 𝓤
 α/⁻-Ord = α/⁻ , pr₁ resize-ordinal

 α/⁻-≃ₒ-α/ : α/⁻-Ord ≃ₒ α/-Ord
 α/⁻-≃ₒ-α/ = pr₂ resize-ordinal

 α/-≃ₒ-α/⁻ : α/-Ord ≃ₒ α/⁻-Ord
 α/-≃ₒ-α/⁻ = ≃ₒ-sym α/⁻-Ord α/-Ord α/⁻-≃ₒ-α/

 α/⁻-is-upper-bound : (i : I) → α i ⊴ α/⁻-Ord
 α/⁻-is-upper-bound i = ⊴-trans (α i) α/-Ord α/⁻-Ord
                         (α/-is-upper-bound i)
                         (≃ₒ-to-⊴ α/-Ord α/⁻-Ord α/-≃ₒ-α/⁻)

 α/⁻-is-lower-bound-of-upper-bounds : (β : Ordinal 𝓤)
                                    → ((i : I) → α i ⊴ β)
                                    → α/⁻-Ord ⊴ β
 α/⁻-is-lower-bound-of-upper-bounds β β-is-ub =
  ⊴-trans α/⁻-Ord α/-Ord β (≃ₒ-to-⊴ α/⁻-Ord α/-Ord α/⁻-≃ₒ-α/)
                           (α/-is-lower-bound-of-upper-bounds β β-is-ub)

\end{code}

Finally, the desired result follows under the assumption of (small) set
quotients).

\begin{code}

ordinal-of-ordinals-has-small-suprema :
 set-quotients-exist → ∀ {𝓤} → Ordinal-Of-Ordinals-Has-Small-Suprema 𝓤
ordinal-of-ordinals-has-small-suprema sq I α =
 (α/⁻-Ord , α/⁻-is-upper-bound , α/⁻-is-lower-bound-of-upper-bounds)
  where
   open construction-using-quotient sq α

\end{code}

This completes the formalization of the approach based on the HoTT Book
[Uni2013].

We now formalize an alternative construction due to Martín Escardó that doesn't
use set quotients, but instead relies on Set Replacement (as defined and
explained in UF.Size.lagda) to obtain a small ordinal at the end.

(As proved in Quotient.Type.lagda and UF-Quotient-Replacement.lagda, Set
Replacement is equivalent to having small set quotients.)

\begin{code}

open import UF.EquivalenceExamples

module construction-using-image
        (pt : propositional-truncations-exist)
        {I : 𝓤 ̇ }
        (α : I → Ordinal 𝓤)
       where

 open PropositionalTruncation pt
 open import UF.ImageAndSurjection pt

 σ : (Σ i ꞉ I , ⟨ α i ⟩) → Ordinal 𝓤
 σ (i , x) = α i ↓ x

 image-σ-≃ : image σ ≃ (Σ β ꞉ Ordinal 𝓤 , ∃ i ꞉ I , β ⊲ α i)
 image-σ-≃ = Σ-cong ϕ
  where
   ϕ : (β : Ordinal 𝓤) → β ∈image σ ≃ (∃ i ꞉ I , β ⊲ α i)
   ϕ β = ∥ Σ p ꞉ domain σ , σ p ＝ β ∥              ≃⟨ ∥∥-cong pt Σ-assoc ⟩
         ∥ Σ i ꞉ I , Σ x ꞉ ⟨ α i ⟩ , α i ↓ x ＝ β ∥ ≃⟨ ∥∥-cong pt ψ       ⟩
         (∃ i ꞉ I , β ⊲ α i)                       ■
    where
     ψ : (Σ i ꞉ I , Σ x ꞉ ⟨ α i ⟩ , α i ↓ x ＝ β) ≃ (Σ i ꞉ I , β ⊲ α i)
     ψ = Σ-cong (λ i → Σ-cong (λ x → ＝-flip))

\end{code}

We will construct the supremum of α as the image of σ, but we will use the
description above as it will be more convenient for us.

The ordinal structure on the image of σ will be the one induced from Ordinal 𝓤
(i.e. _⊲_).

\begin{code}

 α⁺ : 𝓤 ⁺ ̇
 α⁺ = Σ β ꞉ Ordinal 𝓤 , ∃ i ꞉ I , β ⊲ α i

 _≺_ : α⁺ → α⁺ → 𝓤 ⁺ ̇
 (β , _) ≺ (γ , _) = β ⊲ γ

 ≺-is-prop-valued : is-prop-valued _≺_
 ≺-is-prop-valued (β , _) (γ , _) = ⊲-is-prop-valued β γ

 ≺-is-transitive : transitive _≺_
 ≺-is-transitive (β , _) (γ , _) (δ , _) = ⊲-is-transitive β γ δ

 ≺-is-extensional : is-extensional _≺_
 ≺-is-extensional (β , s) (γ , t) u v = to-subtype-＝ (λ _ → ∃-is-prop) goal
  where
   goal : β ＝ γ
   goal = ⊲-is-extensional β γ u' v'
    where
     u' : (δ : Ordinal 𝓤) → δ ⊲ β → δ ⊲ γ
     u' δ l = ∥∥-rec (⊲-is-prop-valued δ γ) h s
      where
       h : (Σ i ꞉ I , β ⊲ α i) → δ ⊲ γ
       h (i , k) = u (δ , ∣ i , m ∣) l
        where
         m : δ ⊲ α i
         m = ⊲-is-transitive δ β (α i) l k
     v' : (δ : Ordinal 𝓤) → δ ⊲ γ → δ ⊲ β
     v' δ l = ∥∥-rec (⊲-is-prop-valued δ β) h t
      where
       h : (Σ i ꞉ I , γ ⊲ α i) → δ ⊲ β
       h (i , k) = v (δ , ∣ i , m ∣) l
        where
         m : δ ⊲ α i
         m = ⊲-is-transitive δ γ (α i) l k

 ≺-is-well-founded : is-well-founded _≺_
 ≺-is-well-founded = goal
  where
   lemma : (β : Ordinal 𝓤) (s : ∃ i ꞉ I , β ⊲ α i)
         → is-accessible _≺_ (β , s)
   lemma = transfinite-induction _⊲_ ⊲-is-well-founded _ ϕ
    where
     ϕ : (β : Ordinal 𝓤)
       → ((γ : Ordinal 𝓤) → γ ⊲ β
                          → (t : ∃ i ꞉ I , γ ⊲ α i)
                          → is-accessible _≺_ (γ , t))
       → (s : ∃ i ꞉ I , β ⊲ α i) → is-accessible _≺_ (β , s)
     ϕ β IH s = acc IH'
      where
       IH' : (γ : α⁺) → γ ≺ (β , s) → is-accessible _≺_ γ
       IH' (γ , t) l = IH γ l t
   goal : (β : α⁺) → is-accessible _≺_ β
   goal (β , s) = lemma β s

 ≺-is-well-order : is-well-order _≺_
 ≺-is-well-order =
  ≺-is-prop-valued , ≺-is-well-founded , ≺-is-extensional , ≺-is-transitive

 α⁺-Ord : Ordinal (𝓤 ⁺)
 α⁺-Ord = α⁺ , _≺_ , ≺-is-well-order

\end{code}

With the ordinal structure in place, we prove that α⁺ is the least upper bound of
the given family α.

\begin{code}

 α⁺-is-upper-bound : (i : I) → α i ⊴ α⁺-Ord
 α⁺-is-upper-bound i = f , f-is-initial-segment , f-is-order-preserving
  where
   f : ⟨ α i ⟩ → α⁺
   f x = α i ↓ x , ∣ i , x , refl ∣
   f-is-order-preserving : is-order-preserving (α i) α⁺-Ord f
   f-is-order-preserving x y l = goal
    where
     goal : (α i ↓ x) ⊲ (α i ↓ y)
     goal = (x , l) , ((iterated-↓ (α i) y x l) ⁻¹)
   f-is-initial-segment : is-initial-segment (α i) α⁺-Ord f
   f-is-initial-segment x (β , _) ((x' , l) , e) =
    (x' , l , to-subtype-＝ (λ _ → ∃-is-prop) (e' ⁻¹))
     where
      e' = β                      ＝⟨ e ⟩
           ((α i ↓ x) ↓ (x' , l)) ＝⟨ iterated-↓ (α i) x x' l ⟩
           (α i ↓ x')             ∎

\end{code}

Added 7 November 2022.

We record a surjectivity property w.r.t. the above simulation so that we can
later prove that initial segments of the supremum of α are given by initial
segments of some αᵢ.

\begin{code}

 private
  α⁺-is-upper-bound-surjectivity :
    (y : α⁺) → ∥ Σ i ꞉ I , Σ x ꞉ ⟨ α i ⟩ , pr₁ (α⁺-is-upper-bound i) x ＝ y ∥
  α⁺-is-upper-bound-surjectivity (β , s) = ∥∥-functor h s
   where
    h : (Σ i ꞉ I , β ⊲ α i)
      → Σ i ꞉ I , Σ x ꞉ ⟨ α i ⟩ , pr₁ (α⁺-is-upper-bound i) x ＝ (β , s)
    h (i , x , e) = i , x , to-subtype-＝ (λ _ → ∃-is-prop) (e ⁻¹)

 module lower-bound-of-upper-bounds-proof
         (β : Ordinal 𝓤)
         (β-is-upper-bound : (i : I) → α i ⊴ β)
        where

  private
   f : (i : I) → ⟨ α i ⟩ → ⟨ β ⟩
   f i x = pr₁ (β-is-upper-bound i) x

   f-key-property : (i : I) (x : ⟨ α i ⟩) → α i ↓ x ＝ β ↓ (f i x)
   f-key-property i x =
    pr₂ (⊴-gives-≼ (α i) β (β-is-upper-bound i) (α i ↓ x) (x , refl))

\end{code}

In proving that α⁺ is the *least* upper bound of α, it is helpful to consider an
auxiliary map where we have γ : Ordinal 𝓤 and an element of Σ i ꞉ I , γ ⊲ α i
(rather than only an element of ∃ i ꞉ I , γ ⊲ α i).

More precisely, the strategy is as follows. Given any γ : Ordinal 𝓤, the
canonical map

    f̃ : (Σ i ꞉ I , γ ⊲ α i) → ⟨ β ⟩
    f̃ (i , x , _) = f i x

is a constant map to a set and therefore by [Theorem 5.4, KECA2017] factors
through the truncation of its domain yielding a map

    f̅ : α⁺ ＝ (Σ γ : Ordinal 𝓤 , ∃ i ꞉ I , γ ⊲ α i) → ⟨ β ⟩

which can be shown to be a simulation by proving related properties of f̃.

[KECA2017] Nicolai Kraus, Martı́n Hötzel Escardó, Thierry Coquand, and Thorsten
           Altenkirch.
           Notions of anonymous existence in Martin-Löf Type Theory.
           Logical Methods in Computer Science, 13(1), 2017.
           doi:10.23638/LMCS-13(1:15)2017.

\begin{code}

  private
   module _ (γ : Ordinal 𝓤) where

    f̃ : (Σ i ꞉ I , γ ⊲ α i) → ⟨ β ⟩
    f̃ (i , x , _) = f i x

    f̃-is-constant : (p q : domain f̃) → f̃ p ＝ f̃ q
    f̃-is-constant (i , x , e) (i' , x' , e') = ↓-lc β (f i x) (f i' x') p
     where
      p = β ↓ f i x   ＝⟨ (f-key-property i x) ⁻¹ ⟩
          α i ↓ x     ＝⟨ e ⁻¹                    ⟩
          γ           ＝⟨ e'                      ⟩
          α i' ↓ x'   ＝⟨ f-key-property i' x'    ⟩
          β ↓ f i' x' ∎

   f̃-is-order-preserving : {γ γ' : Ordinal 𝓤}
                           (s  : Σ i ꞉ I , γ  ⊲ α i)
                           (s' : Σ j ꞉ I , γ' ⊲ α j)
                         → γ ⊲ γ'
                         → f̃ γ s ≺⟨ β ⟩ f̃ γ' s'
   f̃-is-order-preserving {γ} {γ'} (i , x , e) (i' , x' , e') l =
    ↓-reflects-order β (f i x) (f i' x') k
     where
      k : (β ↓ f i x) ⊲ (β ↓ f i' x')
      k = transport₂ _⊲_ (e ∙ f-key-property i x) (e' ∙ f-key-property i' x') l

   f̃-is-initial-segment : {γ : Ordinal 𝓤} (s : Σ i ꞉ I , γ ⊲ α i) (y : ⟨ β ⟩)
                        → y ≺⟨ β ⟩ f̃ γ s
                        → Σ γ' ꞉ Ordinal 𝓤 , Σ s' ꞉ (Σ j ꞉ I , γ' ⊲ α j)
                                           , (γ' ⊲ γ) × (f̃ γ' s' ＝ y)
   f̃-is-initial-segment {γ} (i , x , e) y l =
    (β ↓ y , (i , x' , e₁) , transport⁻¹ ((β ↓ y) ⊲_) e m , (e₂ ⁻¹))
     where
      k : (β ↓ y) ⊲ (β ↓ f i x)
      k = ↓-preserves-order β y (f i x) l
      m : (β ↓ y) ⊲ (α i ↓ x)
      m = transport⁻¹ ((β ↓ y) ⊲_) (f-key-property i x) k
      x' : ⟨ α i ⟩
      x' = pr₁ (pr₁ m)
      e₁ : β ↓ y ＝ α i ↓ x'
      e₁ = pr₂ m ∙ iterated-↓ (α i) x x' (pr₂ (pr₁ m))
      e₂ : y ＝ f i x'
      e₂ = ↓-lc β y (f i x')
            (β   ↓ y      ＝⟨ e₁ ⟩
             α i ↓ x'     ＝⟨ f-key-property i x' ⟩
             β   ↓ f i x' ∎)

   f̅-setup : (γ : Ordinal 𝓤)
           → Σ f̅ ꞉ ((∃ i ꞉ I , γ ⊲ α i) → ⟨ β ⟩) , f̃ γ ∼ f̅ ∘ ∣_∣
   f̅-setup γ = wconstant-map-to-set-factors-through-truncation-of-domain
                (underlying-type-is-set fe β) (f̃ γ) (f̃-is-constant γ)

  f̅ : α⁺ → ⟨ β ⟩
  f̅ (γ , s) = pr₁ (f̅-setup γ) s

  f̅-key-property : (γ : Ordinal 𝓤) (s : Σ i ꞉ I , γ ⊲ α i)
                   (t : ∃ i ꞉ I , γ ⊲ α i)
                 → f̃ γ s ＝ f̅ (γ , t)
  f̅-key-property γ s t =
   f̃ γ s         ＝⟨ pr₂ (f̅-setup γ) s                        ⟩
   f̅ (γ , ∣ s ∣) ＝⟨ ap (λ - → f̅ (γ , -)) (∃-is-prop ∣ s ∣ t) ⟩
   f̅ (γ , t)     ∎

  f̅-is-order-preserving : is-order-preserving α⁺-Ord β f̅
  f̅-is-order-preserving (γ , s) (γ' , s') l =
   ∥∥-rec₂ (Prop-valuedness β (f̅ (γ , s)) (f̅ (γ' , s'))) h s s'
    where
     h : (Σ i ꞉ I , γ ⊲ α i) → (Σ j ꞉ I , γ' ⊲ α j)
       → f̅ (γ , s) ≺⟨ β ⟩ f̅ (γ' , s')
     h (i , u) (j , v) = transport₂ (λ -₁ -₂ → -₁ ≺⟨ β ⟩ -₂)
                                    (f̅-key-property γ  (i , u) s )
                                    (f̅-key-property γ' (j , v) s')
                                    (f̃-is-order-preserving (i , u) (j , v) l)

  f̅-is-initial-segment : is-initial-segment α⁺-Ord β f̅
  f̅-is-initial-segment (γ , s) y l = (β ↓ y , t) , k , e
   where
    claim : 𝓤 ⁺ ̇
    claim = ((β ↓ y) ⊲ γ) × (Σ r ꞉ (∃ i ꞉ I , (β ↓ y) ⊲ α i)
                                            , f̅ ((β ↓ y) , r) ＝ y)
    claim-is-prop : is-prop claim
    claim-is-prop = ×-is-prop (⊲-is-prop-valued (β ↓ y) γ)
                              (Σ-is-prop ∃-is-prop
                                         (λ k → underlying-type-is-set fe β))
    proof-of-claim : ((β ↓ y) ⊲ γ) × (Σ r ꞉ (∃ i ꞉ I , (β ↓ y) ⊲ α i)
                                                     , f̅ ((β ↓ y) , r) ＝ y)
    proof-of-claim = ∥∥-rec claim-is-prop h s
     where
      h : (Σ i ꞉ I , γ ⊲ α i) → claim
      h u = pr₁ (pr₂ lem) , ∣ v ∣ , e'
       where
        lem : Σ v ꞉ (Σ j ꞉ I , (β ↓ y) ⊲ α j)
                             , ((β ↓ y) ⊲ γ) × (f̃ (β ↓ y) v ＝ y)
        lem = pr₂ (f̃-is-initial-segment u y l')
         where
          l' : y ≺⟨ β ⟩ f̃ γ u
          l' = transport⁻¹ (λ - → y ≺⟨ β ⟩ -) (f̅-key-property γ u s) l
        v : Σ j ꞉ I , (β ↓ y) ⊲ α j
        v = pr₁ lem
        e' : f̅ ((β ↓ y) , ∣ v ∣) ＝ y
        e' = (f̅-key-property (β ↓ y) v ∣ v ∣) ⁻¹ ∙ pr₂ (pr₂ lem)
    t : ∃ i ꞉ I , (β ↓ y) ⊲ α i
    t = pr₁ (pr₂ proof-of-claim)
    k : (β ↓ y) ⊲ γ
    k = pr₁ proof-of-claim
    e : f̅ ((β ↓ y) , t) ＝ y
    e = pr₂ (pr₂ proof-of-claim)

  f̅-behaviour : (i : I) (x : ⟨ α i ⟩)
              → f̅ ([ α i , α⁺-Ord ]⟨ α⁺-is-upper-bound i ⟩ x) ＝ f i x
  f̅-behaviour i x =
   f̅ ([ α i , α⁺-Ord ]⟨ α⁺-is-upper-bound i ⟩ x) ＝⟨ e ⟩
   f̃ (α i ↓ x) (i , x , refl)                    ＝⟨refl⟩
   f i x                                         ∎
    where
     e = (f̅-key-property (α i ↓ x) (i , (x , refl)) ∣ i , x , refl ∣) ⁻¹

 α⁺-is-lower-bound-of-upper-bounds : (β : Ordinal 𝓤)
                                   → ((i : I) → α i ⊴ β)
                                   → α⁺-Ord ⊴ β
 α⁺-is-lower-bound-of-upper-bounds β β-is-ub = f̅ , f̅-is-initial-segment
                                                 , f̅-is-order-preserving
  where
   open lower-bound-of-upper-bounds-proof β β-is-ub

 α⁺-is-lower-bound-of-upper-bounds-behaviour
  : (β : Ordinal 𝓤) (f : (i : I) → α i ⊴ β) (i : I)
  → [ α⁺-Ord , β ]⟨ α⁺-is-lower-bound-of-upper-bounds β f ⟩
      ∘ [ α i , α⁺-Ord ]⟨ α⁺-is-upper-bound i ⟩
    ∼ [ α i , β ]⟨ f i ⟩
 α⁺-is-lower-bound-of-upper-bounds-behaviour β f i x =
  lower-bound-of-upper-bounds-proof.f̅-behaviour β f i x

\end{code}

In the above construction it is important to notice that α⁺ lives in the next
universe 𝓤 ⁺, so it does not prove that Ordinal 𝓤 has small suprema.

To prove this, we resize α⁺ down to an equivalent ordinal in 𝓤. The first step
in doing so, is proving that the order ≺ on α⁺ (which takes values in 𝓤 ⁺) is
equivalent to one with values in 𝓤.

\begin{code}

 private
  _≺⁻_ : α⁺ → α⁺ → 𝓤 ̇
  (β , _) ≺⁻ (γ , _) = β ⊲⁻ γ

  ≺-≃-≺⁻ : (x y : α⁺) → (x ≺ y) ≃ (x ≺⁻ y)
  ≺-≃-≺⁻ (β , _) (γ , _) = ⊲-is-equivalent-to-⊲⁻ β γ

\end{code}

Next, we resize α⁺ using:
(1) Set Replacement, as defined and explained in UF.Size.lagda.
(2) Martín's machinery developed in OrdinalsWellOrderTransport to transport the
    well order along the supposed equivalence.

\begin{code}

 module _ (replacement : Set-Replacement pt) where

  private
   small-image : is-small (image σ)
   small-image = replacement σ ((Σ i ꞉ I , ⟨ α i ⟩) , ≃-refl _)
                               (λ β γ → (β ≃ₒ γ) , ≃-sym (UAₒ-≃ (ua 𝓤) fe' β γ))
                               (the-type-of-ordinals-is-a-set (ua 𝓤) fe')
   α⁻ : 𝓤 ̇
   α⁻ = pr₁ small-image

   φ : α⁻ ≃ α⁺
   φ = α⁻      ≃⟨ pr₂ small-image ⟩
       image σ ≃⟨ image-σ-≃       ⟩
       α⁺      ■

   resize-ordinal : Σ s ꞉ OrdinalStructure α⁻ , (α⁻ , s) ≃ₒ α⁺-Ord
   resize-ordinal = transfer-structure α⁻ α⁺-Ord φ (_≺⁻_ , ≺-≃-≺⁻)

  α⁻-Ord : Ordinal 𝓤
  α⁻-Ord = α⁻ , pr₁ resize-ordinal

  α⁻-≃ₒ-α⁺ : α⁻-Ord ≃ₒ α⁺-Ord
  α⁻-≃ₒ-α⁺ = pr₂ resize-ordinal

  α⁺-≃ₒ-α⁻ : α⁺-Ord ≃ₒ α⁻-Ord
  α⁺-≃ₒ-α⁻ = ≃ₒ-sym α⁻-Ord α⁺-Ord α⁻-≃ₒ-α⁺

  α⁻-is-upper-bound : (i : I) → α i ⊴ α⁻-Ord
  α⁻-is-upper-bound i = ⊴-trans (α i) α⁺-Ord α⁻-Ord
                       (α⁺-is-upper-bound i)
                        (≃ₒ-to-⊴ α⁺-Ord α⁻-Ord α⁺-≃ₒ-α⁻)

\end{code}

Added 7 November 2022.

As above, we record a surjectivity property w.r.t. the above simulation (but for
the resized α⁻ this time) so that we can later prove that initial segments of
the supremum of α are given by initial segments of some αᵢ.

\begin{code}

  α⁻-is-upper-bound-surjectivity :
     (y : α⁻)
   → ∥ Σ i ꞉ I , Σ x ꞉ ⟨ α i ⟩ , pr₁ (α⁻-is-upper-bound i) x ＝ y ∥
  α⁻-is-upper-bound-surjectivity y =
   ∥∥-functor h (α⁺-is-upper-bound-surjectivity (⌜ φ ⌝ y))
   where
    h : (Σ i ꞉ I , Σ x ꞉ ⟨ α i ⟩ , pr₁ (α⁺-is-upper-bound i) x ＝ ⌜ φ ⌝ y)
      → (Σ i ꞉ I , Σ x ꞉ ⟨ α i ⟩ , pr₁ (α⁻-is-upper-bound i) x ＝ y)
    h (i , x , e) = (i , x , e')
     where
      e' = pr₁ (α⁻-is-upper-bound i) x           ＝⟨refl⟩
           ⌜ φ ⌝⁻¹ (pr₁ (α⁺-is-upper-bound i) x) ＝⟨ ⦅1⦆ ⟩
           ⌜ φ ⌝⁻¹ (⌜ φ ⌝ y)                     ＝⟨ ⦅2⦆ ⟩
           y                                     ∎
       where
        ⦅1⦆ = ap ⌜ φ ⌝⁻¹ e
        ⦅2⦆ = inverses-are-retractions ⌜ φ ⌝ (⌜⌝-is-equiv φ) y

  α⁻-is-lower-bound-of-upper-bounds : (β : Ordinal 𝓤)
                                    → ((i : I) → α i ⊴ β)
                                    → α⁻-Ord ⊴ β
  α⁻-is-lower-bound-of-upper-bounds β β-is-ub =
   ⊴-trans α⁻-Ord α⁺-Ord β (≃ₒ-to-⊴ α⁻-Ord α⁺-Ord α⁻-≃ₒ-α⁺)
                           (α⁺-is-lower-bound-of-upper-bounds β β-is-ub)

  α⁻-is-lower-bound-of-upper-bounds-behaviour
   : (β : Ordinal 𝓤) (f : (i : I) → α i ⊴ β) (i : I)
   → [ α⁻-Ord , β ]⟨ α⁻-is-lower-bound-of-upper-bounds β f ⟩
       ∘ [ α i , α⁻-Ord ]⟨ α⁻-is-upper-bound i ⟩
     ∼ [ α i , β ]⟨ f i ⟩
  α⁻-is-lower-bound-of-upper-bounds-behaviour β f i x =
   (h ∘ g) x            ＝⟨refl⟩
   (h⁺ ∘ ϕ ∘ g) x       ＝⟨refl⟩
   (h⁺ ∘ ϕ ∘ ψ ∘ g⁺) x  ＝⟨ e₁ ⟩
   (h⁺ ∘ g⁺) x          ＝⟨ e₂ ⟩
   [ α i , β ]⟨ f i ⟩ x ∎
    where
     h = [ α⁻-Ord , β ]⟨ α⁻-is-lower-bound-of-upper-bounds β f ⟩
     h⁺ = [ α⁺-Ord , β ]⟨ α⁺-is-lower-bound-of-upper-bounds β f ⟩
     g = [ α i , α⁻-Ord ]⟨ α⁻-is-upper-bound i ⟩
     g⁺ = [ α i , α⁺-Ord ]⟨ α⁺-is-upper-bound i ⟩
     ϕ = ≃ₒ-to-fun _ _ α⁻-≃ₒ-α⁺
     ψ = ≃ₒ-to-fun _ _ α⁺-≃ₒ-α⁻
     e₁ = ap h⁺
          (inverses-are-sections ϕ
            (≃ₒ-to-fun-is-equiv _ _ α⁻-≃ₒ-α⁺)
            ([ α i , α⁺-Ord ]⟨ α⁺-is-upper-bound i ⟩ x))
     e₂ = α⁺-is-lower-bound-of-upper-bounds-behaviour β f i x

\end{code}

Finally, the desired result follows (under the assumption of Set Replacement).

\begin{code}

module _ (pt : propositional-truncations-exist) where

 ordinal-of-ordinals-has-small-suprema' :
  Set-Replacement pt → ∀ {𝓤} → Ordinal-Of-Ordinals-Has-Small-Suprema 𝓤
 ordinal-of-ordinals-has-small-suprema' R I α =
  (α⁻-Ord R , α⁻-is-upper-bound R
            , α⁻-is-lower-bound-of-upper-bounds R)
   where
    open construction-using-image pt α

\end{code}

As proved in Quotient.Type.lagda and UF-Quotient-Replacement.lagda, Set
Replacement is equivalent to having small set quotients, so it follows
immediately that (just as above) Ordinal 𝓤 has small suprema if we assume the
existence of (small) set quotients.

\begin{code}

ordinal-of-ordinals-has-small-suprema'' :
 set-quotients-exist → ∀ {𝓤} → Ordinal-Of-Ordinals-Has-Small-Suprema 𝓤
ordinal-of-ordinals-has-small-suprema'' sq =
 ordinal-of-ordinals-has-small-suprema' pt R
  where
   open general-set-quotients-exist sq
   pt : propositional-truncations-exist
   pt = propositional-truncations-from-set-quotients sq fe'
   R : Set-Replacement pt
   R = set-replacement-from-set-quotients-and-prop-trunc sq pt

\end{code}

We repackage the above for convenient use.

\begin{code}

module suprema
        (pt : propositional-truncations-exist)
        (sr : Set-Replacement pt)
       where

 open PropositionalTruncation pt
 open import UF.ImageAndSurjection pt

 module _ {I : 𝓤 ̇ } (α : I → Ordinal 𝓤) where

  open construction-using-image pt α

  sum-to-ordinals : (Σ i ꞉ I , ⟨ α i ⟩) → Ordinal 𝓤
  sum-to-ordinals (i , x) = α i ↓ x

  abstract
   sup : Ordinal 𝓤
   sup = pr₁ (ordinal-of-ordinals-has-small-suprema' pt sr I α)

   sup-is-least-upper-bound : ((i : I) → α i ⊴ sup)
                            × ((β : Ordinal 𝓤) → ((i : I) → α i ⊴ β) → sup ⊴ β)
   sup-is-least-upper-bound =
    pr₂ (ordinal-of-ordinals-has-small-suprema' pt sr I α)

   sup-is-upper-bound : (i : I) → α i ⊴ sup
   sup-is-upper-bound = pr₁ (sup-is-least-upper-bound)

   private
    q : (i : I) → ⟨ α i ⟩ → ⟨ sup ⟩
    q i = pr₁ (sup-is-upper-bound i)

    q-surj : (y : ⟨ sup ⟩) → ∃ i ꞉ I , Σ x ꞉ ⟨ α i ⟩ , q i x ＝ y
    q-surj = α⁻-is-upper-bound-surjectivity sr

   sup-is-upper-bound-jointly-surjective :
      (y : ⟨ sup ⟩)
    → ∃ i ꞉ I , Σ x ꞉ ⟨ α i ⟩ , [ α i , sup ]⟨ sup-is-upper-bound i ⟩ x ＝ y
   sup-is-upper-bound-jointly-surjective = q-surj

   sup-is-lower-bound-of-upper-bounds : (β : Ordinal 𝓤)
                                      → ((i : I) → α i ⊴ β)
                                      → sup ⊴ β
   sup-is-lower-bound-of-upper-bounds = pr₂ (sup-is-least-upper-bound)

   sup-is-lower-bound-of-upper-bounds-behaviour
    : (β : Ordinal 𝓤) (f : (i : I) → α i ⊴ β)
      (i : I) (x : ⟨ α i ⟩)
    → [ sup , β ]⟨ sup-is-lower-bound-of-upper-bounds β f ⟩ (q i x)
      ＝ [ α i , β ]⟨ f i ⟩ x
   sup-is-lower-bound-of-upper-bounds-behaviour =
    α⁻-is-lower-bound-of-upper-bounds-behaviour sr

   induced-simulation-from-sup-is-surjection :
      (β : Ordinal 𝓤) (f : (i : I) → α i ⊴ β)
    → ((y : ⟨ β ⟩) → ∃ i ꞉ I , Σ x ꞉ ⟨ α i ⟩ , [ α i , β ]⟨ f i ⟩ x ＝ y)
    → is-surjection ([ sup , β ]⟨ sup-is-lower-bound-of-upper-bounds β f ⟩)
   induced-simulation-from-sup-is-surjection β f s y =
    ∥∥-functor
     (λ (i , x , p) → q i x ,
                      (sup-is-lower-bound-of-upper-bounds-behaviour β f i x ∙ p))
     (s y)

   sup-is-image-of-sum-to-ordinals : ⟨ sup ⟩ ≃ image sum-to-ordinals
   sup-is-image-of-sum-to-ordinals =
    ⟨ sup ⟩  ≃⟨ ≃ₒ-gives-≃ sup α⁺-Ord (α⁻-≃ₒ-α⁺ sr) ⟩
    α⁺       ≃⟨ ≃-sym image-σ-≃ ⟩
    image σ  ■

   sum-to-sup : (Σ i ꞉ I , ⟨ α i ⟩) → ⟨ sup ⟩
   sum-to-sup = ⌜ ≃-sym sup-is-image-of-sum-to-ordinals ⌝ ∘ corestriction σ

   sum-to-sup-is-surjection : is-surjection sum-to-sup
   sum-to-sup-is-surjection = ∘-is-surjection
                               (corestrictions-are-surjections σ)
                               (equivs-are-surjections
                                 (⌜⌝-is-equiv
                                    (≃-sym sup-is-image-of-sum-to-ordinals)))

   sup-is-image-of-sum : ⟨ sup ⟩ is-image-of (Σ i ꞉ I , ⟨ α i ⟩)
   sup-is-image-of-sum = sum-to-sup , sum-to-sup-is-surjection

   initial-segment-of-sup-at-component :
      (i : I) (x : ⟨ α i ⟩)
    → sup ↓ [ α i , sup ]⟨ sup-is-upper-bound i ⟩ x ＝ α i ↓ x
   initial-segment-of-sup-at-component i x =
    (simulations-preserve-↓ (α i) sup (sup-is-upper-bound i) x) ⁻¹

   initial-segment-of-sup-is-initial-segment-of-some-component :
     (y : ⟨ sup ⟩) → ∥ Σ i ꞉ I , Σ x ꞉ ⟨ α i ⟩ , sup ↓ y ＝ α i ↓ x ∥
   initial-segment-of-sup-is-initial-segment-of-some-component y =
    ∥∥-functor h (α⁻-is-upper-bound-surjectivity sr y)
     where
      h : (Σ i ꞉ I , Σ x ꞉ ⟨ α i ⟩ , [ α i , sup ]⟨ sup-is-upper-bound i ⟩ x ＝ y)
        → Σ i ꞉ I , Σ x ꞉ ⟨ α i ⟩ , sup ↓ y ＝ α i ↓ x
      h (i , x , e) = (i , x , e')
       where
        e' : sup ↓ y ＝ α i ↓ x
        e' = sup ↓ y  ＝⟨ ap (sup ↓_) (e ⁻¹)                         ⟩
             sup ↓ y' ＝⟨ initial-segment-of-sup-at-component i x ⟩
             α i ↓ x  ∎
         where
          y' : ⟨ sup ⟩
          y' = [ α i , sup ]⟨ sup-is-upper-bound i ⟩ x

 sup-composition-⊴ : {I J : 𝓤 ̇  } (ρ : I → J) (α : J → Ordinal 𝓤)
                   → sup (α ∘ ρ) ⊴ sup α
 sup-composition-⊴ ρ α =
  sup-is-lower-bound-of-upper-bounds
   (α ∘ ρ)
   (sup α)
   (λ i → sup-is-upper-bound α (ρ i))

 sup-monotone : {I : 𝓤 ̇ } (α β : I → Ordinal 𝓤)
              → ((i : I) → α i ⊴ β i)
              → sup α ⊴ sup β
 sup-monotone α β l = sup-is-lower-bound-of-upper-bounds α (sup β)
                       (λ i → ⊴-trans
                               (α i) (β i) (sup β)
                               (l i) (sup-is-upper-bound β i))

\end{code}

Conjecture (Martin Escardo, August 2018 originally in the file
OrdinalOfOrdinals, moved here 30th March 2022). We have bounded
joins constructed by taking the joint image in any upper bound.

In this way we avoid both small quotients and small images. Moreover,
the results of the second part of this file are a particular case of
this taking Ord 𝓤 as an upper bound.

Moved here on 5 December 2024 by Tom de Jong and Fredrik Nordvall Forsberg, but
developed in February 2024 in collaboration with Nicolai Kraus and Chuangjie Xu.

\begin{code}

 is-continuous : (Ordinal 𝓤 → Ordinal 𝓤) → 𝓤 ⁺ ̇
 is-continuous {𝓤} F =
    {I : 𝓤 ̇  }
  → ∥ I ∥
  → (γ : I → Ordinal 𝓤)
  → F (sup γ) ＝ sup (F ∘ γ)

 is-continuous-generalized : (Ordinal 𝓤 → Ordinal (𝓤 ⊔ 𝓥)) → (𝓤 ⊔ 𝓥) ⁺ ̇
 is-continuous-generalized {𝓤} {𝓥} F =
    {I : 𝓤 ̇  }
  → ∥ I ∥
  → (γ : I → Ordinal 𝓤)
  → F (sup γ) ＝ sup (λ (i : Lift 𝓥 I) → F (γ (lower i)))
  where
   open import UF.UniverseEmbedding

 is-monotone-if-continuous-generalized : (F : Ordinal 𝓤 → Ordinal (𝓤 ⊔ 𝓥))
                                       → is-continuous-generalized F
                                       → is-monotone (OO 𝓤) (OO (𝓤 ⊔ 𝓥)) F
 is-monotone-if-continuous-generalized {𝓤} {𝓥} F F-cont α β l = IV
  where
   open import UF.UniverseEmbedding
   γ : 𝟙{𝓤} + 𝟙{𝓤} → Ordinal 𝓤
   γ (inl _) = α
   γ (inr _) = β

   β-is-upper-bound : (i : 𝟙 + 𝟙) → γ i ⊴ β
   β-is-upper-bound (inl _) = ≼-gives-⊴ α β l
   β-is-upper-bound (inr _) = ⊴-refl β

   I : F (sup γ) ＝ sup (F ∘ γ ∘ lower)
   I = F-cont ∣ inl ⋆ ∣ γ

   II : sup γ ＝ β
   II = ⊴-antisym (sup γ) β
         (sup-is-lower-bound-of-upper-bounds γ β β-is-upper-bound)
         (sup-is-upper-bound γ (inr ⋆))

   III : F α ⊴ sup (F ∘ γ ∘ lower)
   III = sup-is-upper-bound (F ∘ γ ∘ lower) (lift 𝓥 (inl ⋆))

   IV : F α ≼ F β
   IV = ⊴-gives-≼ (F α) (F β) (transport (F α ⊴_) (I ⁻¹ ∙ ap F II) III)

 to-is-continuous-generalized : (F : Ordinal 𝓤 → Ordinal 𝓤)
                              → is-continuous F
                              → is-continuous-generalized {𝓤} {𝓤} F
 to-is-continuous-generalized {𝓤} F F-cont {S} S-inh γ =
  transport⁻¹
   (_＝ sup (F ∘ γ ∘ lower))
   (F-cont S-inh γ)
   (⊴-antisym (sup (F ∘ γ)) (sup (F ∘ γ ∘ lower)) I II)
   where
    open import UF.UniverseEmbedding
    I : sup (F ∘ γ) ⊴ sup (F ∘ γ ∘ lower)
    I = sup-composition-⊴ (lift 𝓤) (F ∘ γ ∘ lower)
    II : sup (F ∘ γ ∘ lower) ⊴ sup (F ∘ γ)
    II = sup-composition-⊴ lower (F ∘ γ)

 is-monotone-if-continuous : (F : Ordinal 𝓤 → Ordinal 𝓤)
                           → is-continuous F
                           → is-monotone (OO 𝓤) (OO 𝓤) F
 is-monotone-if-continuous {𝓤} F F-cont =
  is-monotone-if-continuous-generalized F (to-is-continuous-generalized F F-cont)

\end{code}
