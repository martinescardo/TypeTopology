Martin Escardo 1st May 2020.

This is ported from the Midlands Graduate School 2019 lecture notes

 https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html
 https://github.com/martinescardo/HoTT-UF-Agda-Lecture-Notes

\begin{code}

{-# OPTIONS --safe --without-K #-}

module MGS.Embeddings where

open import MGS.More-FunExt-Consequences public

is-embedding : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
is-embedding f = (y : codomain f) → is-subsingleton (fiber f y)

being-embedding-is-subsingleton : global-dfunext
                                → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                                → is-subsingleton (is-embedding f)

being-embedding-is-subsingleton fe f =
 Π-is-subsingleton fe
  (λ x → being-subsingleton-is-subsingleton fe)

pr₂-embedding : (A : 𝓤 ̇ ) (X : 𝓥 ̇ )
              → is-subsingleton A
              → is-embedding (λ (z : A × X) → pr₂ z)

pr₂-embedding A X i x ((a , x) , refl x) ((b , x) , refl x) = p
 where
  p : ((a , x) , refl x) ＝ ((b , x) , refl x)
  p = ap (λ - → ((- , x) , refl x)) (i a b)

pr₁-is-embedding : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
                 → ((x : X) → is-subsingleton (A x))
                 → is-embedding (λ (σ : Σ A) → pr₁ σ)

pr₁-is-embedding i x ((x , a) , refl x) ((x , a') , refl x) = γ
 where
  p : a ＝ a'
  p = i x a a'

  γ : (x , a) , refl x ＝ (x , a') , refl x
  γ = ap (λ - → (x , -) , refl x) p

equivs-are-embeddings : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                        (f : X → Y)
                      → is-equiv f
                      → is-embedding f

equivs-are-embeddings f i y = singletons-are-subsingletons (fiber f y) (i y)

id-is-embedding : {X : 𝓤 ̇ } → is-embedding (𝑖𝑑 X)
id-is-embedding {𝓤} {X} = equivs-are-embeddings id (id-is-equiv X)

∘-embedding : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
              {f : X → Y} {g : Y → Z}
            → is-embedding g
            → is-embedding f
            → is-embedding (g ∘ f)

∘-embedding {𝓤} {𝓥} {𝓦} {X} {Y} {Z} {f} {g} d e = h
 where
  A : (z : Z) → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
  A z = Σ (y , p) ꞉ fiber g z , fiber f y

  i : (z : Z) → is-subsingleton (A z)
  i z = Σ-is-subsingleton (d z) (λ w → e (pr₁ w))

  φ : (z : Z) → fiber (g ∘ f) z → A z
  φ z (x , p) = (f x , p) , x , refl (f x)

  γ : (z : Z) → A z → fiber (g ∘ f) z
  γ z ((_ , p) , x , refl _) = x , p

  η : (z : Z) (t : fiber (g ∘ f) z) → γ z (φ z t) ＝ t
  η _ (x , refl _) = refl (x , refl ((g ∘ f) x))

  h : (z : Z) → is-subsingleton (fiber (g ∘ f) z)
  h z
   = lc-maps-reflect-subsingletons
      (φ z)
      (sections-are-lc (φ z) (γ z , η z))
      (i z)

embedding-lemma : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                → ((x : X) → is-singleton (fiber f (f x)))
                → is-embedding f

embedding-lemma f φ = γ
 where
  γ : (y : codomain f) (u v : fiber f y) → u ＝ v
  γ y (x , p) v = j (x , p) v
   where
    q : fiber f (f x) ＝ fiber f y
    q = ap (fiber f) p

    i : is-singleton (fiber f y)
    i = transport is-singleton q (φ x)

    j : is-subsingleton (fiber f y)
    j = singletons-are-subsingletons (fiber f y) i

embedding-criterion : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                    → ((x x' : X) → (f x ＝ f x') ≃ (x ＝ x'))
                    → is-embedding f

embedding-criterion f e = embedding-lemma f b
 where
  X = domain f

  a : (x : X) → (Σ x' ꞉ X , f x' ＝ f x) ≃ (Σ x' ꞉ X , x' ＝ x)
  a x = Σ-cong (λ x' → e x' x)

  a' : (x : X) → fiber f (f x) ≃ singleton-type x
  a' = a

  b : (x : X) → is-singleton (fiber f (f x))
  b x = equiv-to-singleton (a' x) (singleton-types-are-singletons X x)

ap-is-equiv-gives-embedding : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                            → ((x x' : X) → is-equiv (ap f {x} {x'}))
                            → is-embedding f

ap-is-equiv-gives-embedding f i = embedding-criterion f
                                   (λ x' x → ≃-sym (ap f {x'} {x} , i x' x))

embedding-gives-ap-is-equiv : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                            → is-embedding f
                            → (x x' : X) → is-equiv (ap f {x} {x'})

embedding-gives-ap-is-equiv {𝓤} {𝓥} {X} f e = γ
 where
  d : (x' : X) → (Σ x ꞉ X , f x' ＝ f x) ≃ (Σ x ꞉ X , f x ＝ f x')
  d x' = Σ-cong (λ x → ⁻¹-≃ (f x') (f x))

  s : (x' : X) → is-subsingleton (Σ x ꞉ X , f x' ＝ f x)
  s x' = equiv-to-subsingleton (d x') (e (f x'))

  γ : (x x' : X) → is-equiv (ap f {x} {x'})
  γ x = singleton-equiv-lemma x (λ x' → ap f {x} {x'})
         (pointed-subsingletons-are-singletons
           (Σ x' ꞉ X , f x ＝ f x') (x , (refl (f x))) (s x))

embedding-criterion-converse : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                             → is-embedding f
                             → ((x' x : X) → (f x' ＝ f x) ≃ (x' ＝ x))

embedding-criterion-converse f e x' x = ≃-sym
                                         (ap f {x'} {x} ,
                                          embedding-gives-ap-is-equiv f e x' x)

embeddings-are-lc : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                  → is-embedding f
                  → left-cancellable f

embeddings-are-lc f e {x} {y} = ⌜ embedding-criterion-converse f e x y ⌝

lc-maps-into-sets-are-embeddings : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                                 → left-cancellable f
                                 → is-set Y
                                 → is-embedding f
lc-maps-into-sets-are-embeddings {𝓤} {𝓥} {X} {Y} f lc i y = γ
 where
  γ : is-subsingleton (Σ x ꞉ X , f x ＝ y)
  γ (x , p) (x' , p') = to-subtype-＝ j q
   where
    j : (x : X) → is-subsingleton (f x ＝ y)
    j x = i (f x) y

    q : x ＝ x'
    q = lc (f x  ＝⟨ p     ⟩
            y    ＝⟨ p' ⁻¹ ⟩
            f x' ∎)

embedding-with-section-is-equiv : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                                → is-embedding f
                                → has-section f
                                → is-equiv f
embedding-with-section-is-equiv f i (g , η) y
 = pointed-subsingletons-are-singletons
    (fiber f y) (g y , η y) (i y)

NatΠ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {B : X → 𝓦 ̇ } → Nat A B → Π A → Π B
NatΠ τ f x = τ x (f x)

NatΠ-is-embedding : hfunext 𝓤 𝓥
                  → hfunext 𝓤 𝓦
                  → {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {B : X → 𝓦 ̇ }
                  → (τ : Nat A B)
                  → ((x : X) → is-embedding (τ x))
                  → is-embedding (NatΠ τ)

NatΠ-is-embedding v w {X} {A} τ i = embedding-criterion (NatΠ τ) γ
 where
  γ : (f g : Π A) → (NatΠ τ f ＝ NatΠ τ g) ≃ (f ＝ g)
  γ f g = (NatΠ τ f ＝ NatΠ τ g) ≃⟨ hfunext-≃ w (NatΠ τ f) (NatΠ τ g) ⟩
          (NatΠ τ f ∼ NatΠ τ g) ≃⟨ b                                 ⟩
          (f ∼ g)               ≃⟨ ≃-sym (hfunext-≃ v f g)           ⟩
          (f ＝ g)               ■

   where
    a : (x : X) → (NatΠ τ f x ＝ NatΠ τ g x) ≃ (f x ＝ g x)
    a x = embedding-criterion-converse (τ x) (i x) (f x) (g x)

    b : (NatΠ τ f ∼ NatΠ τ g) ≃ (f ∼ g)
    b = Π-cong (hfunext-gives-dfunext w) (hfunext-gives-dfunext v) a

triangle-lemma
 : dfunext 𝓦 (𝓤 ⊔ 𝓥)
 → {Y : 𝓤 ̇ } {A : 𝓥 ̇ } (g : Y → A)
 → is-embedding g
 → {X : 𝓦 ̇ } (f : X → A) → is-subsingleton (Σ h ꞉ (X → Y) , g ∘ h ∼ f)

triangle-lemma fe {Y} {A} g i {X} f = iv
 where
  ii : (x : X) → is-subsingleton (Σ y ꞉ Y , g y ＝ f x)
  ii x = i (f x)

  iii : is-subsingleton (Π x ꞉ X , Σ y ꞉ Y , g y ＝ f x)
  iii = Π-is-subsingleton fe ii

  iv : is-subsingleton (Σ h ꞉ (X → Y) , g ∘ h ∼ f)
  iv = equiv-to-subsingleton (≃-sym ΠΣ-distr-≃) iii


postcomp-is-embedding : dfunext 𝓦 (𝓤 ⊔ 𝓥) → hfunext 𝓦 𝓥
                      → {Y : 𝓤 ̇ } {A : 𝓥 ̇ } (g : Y → A)
                      → is-embedding g
                      → (X : 𝓦 ̇ ) → is-embedding (λ (h : X → Y) → g ∘ h)

postcomp-is-embedding fe hfe {Y} {A} g i X = γ
 where
  γ : (f : X → A) → is-subsingleton (Σ h ꞉ (X → Y) , g ∘ h ＝ f)
  γ f = equiv-to-subsingleton u (triangle-lemma fe g i f)
   where
    u : (Σ h ꞉ (X → Y) , g ∘ h ＝ f) ≃ (Σ h ꞉ (X → Y) , g ∘ h ∼ f)
    u = Σ-cong (λ h → hfunext-≃ hfe (g ∘ h) f)

_↪_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
X ↪ Y = Σ f ꞉ (X → Y), is-embedding f

Emb→fun : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X ↪ Y) → (X → Y)
Emb→fun (f , i) = f

\end{code}
