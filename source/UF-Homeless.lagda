This file should be eventually removed, after we have found a home for
everything that is here.

\begin{code}

{-# OPTIONS --without-K --exact-split #-}

module UF-Homeless where

open import UF-Base
open import UF-Subsingletons
open import UF-Yoneda
open import UF-Retracts
open import UF-Subsingletons-Retracts
open import UF-Equiv
open import UF-LeftCancellable
open import UF-FunExt
open import UF-Univalence
open import UF-Embedding
open import UF-Subsingletons-FunExt
open import UF-Prop
open import UF-PropTrunc

pt-pf-equiv : ∀ {U} {X : U ̇} (x : X) → Σ \(f : paths-from x → paths-to x) → isEquiv f
pt-pf-equiv {U} {X} x = f , ((g , fg) , (g , gf))
 where
  f : paths-from x → paths-to x
  f (y , p) = y , (p ⁻¹) 
  g : paths-to x → paths-from x
  g (y , p) = y , (p ⁻¹) 
  fg : f ∘ g ∼ id
  fg (y , p) = ap (λ p → y , p) (⁻¹-involutive p)
  gf : g ∘ f ∼ id
  gf (y , p) = ap (λ p → y , p) (⁻¹-involutive p)
  
paths-to-contractible : ∀ {U} {X : U ̇} (x : X) → isSingleton(paths-to x)
paths-to-contractible x = retract-of-singleton
                                  (pr₁(pt-pf-equiv x))
                                  (pr₁(pr₂((pt-pf-equiv x))))
                                  (paths-from-contractible x)

paths-to-isProp : ∀ {U} {X : U ̇} (x : X) → isProp(paths-to x)
paths-to-isProp x = isSingleton-isProp (paths-to-contractible x)

\end{code}

The following has a proof from function extensionality (see e.g. HoTT
Book), but it has a more direct proof from univalence (we also give a
proof without univalence later):

\begin{code}

isEquiv-isVoevodskyEquiv' : ∀ {U} → isUnivalent U → {X Y : U ̇} (f : X → Y)
                         → isEquiv f → isVoevodskyEquiv f
isEquiv-isVoevodskyEquiv' {U} ua {X} {Y} f ise = g Y (f , ise)
 where
  A : (Y : U ̇) → X ≃ Y → U ̇
  A Y (f , ise) = isVoevodskyEquiv f
  b : A X (ideq X)
  b = paths-to-contractible
  g :  (Y : U ̇) (e : X ≃ Y) → A Y e
  g = JEq ua X A b

\end{code}

We next consider sums and products of families of left-cancellable
maps, which again give left-cancellable maps.

\begin{code}

NatΣ : ∀ {U V W} {X : U ̇} {A : X → V ̇} {B : X → W ̇} → Nat A B → Σ A → Σ B
NatΣ ζ (x , a) = (x , ζ x a)

NatΣ-equiv : ∀ {U V W} (X : U ̇) (A : X → V ̇) (B : X → W ̇) (ζ : Nat A B)
           → ((x : X) → isEquiv(ζ x)) → isEquiv(NatΣ ζ)
NatΣ-equiv X A B ζ ise = ((s , ζs), (r , rζ)) 
 where
  s : Σ B → Σ A
  s (x , b) = x , pr₁ (pr₁ (ise x)) b
  ζs : (β : Σ B) → (NatΣ ζ ∘ s) β ≡ β
  ζs (x , b) = ap (λ b → (x , b)) (pr₂ (pr₁ (ise x)) b)
  r : Σ B → Σ A
  r (x , b) = x , (pr₁ (pr₂ (ise x)) b)
  rζ : (α : Σ A) → (r ∘ NatΣ ζ) α ≡ α
  rζ (x , a) = ap (λ a → (x , a)) (pr₂ (pr₂ (ise x)) a)

NatΣ-lc : ∀ {U V W} (X : U ̇) (A : X → V ̇) (B : X → W ̇) (ζ : Nat A B)
        → ((x : X) → left-cancellable(ζ x)) → left-cancellable(NatΣ ζ)
NatΣ-lc X A B ζ ζ-lc {(x , a)} {(y , b)} pq = g
  where
    p : x ≡ y
    p = pr₁ (from-Σ-Id B pq)
    η : Nat (Id x) B
    η = yoneda-nat B (ζ x a)
    q : η y p ≡ ζ y b
    q = pr₂ (from-Σ-Id B pq)
    θ : Nat (Id x) A
    θ = yoneda-nat A a
    η' : Nat (Id x) B
    η' y p = ζ y (θ y p)
    r : η' ≈ η
    r = yoneda-elem-lc η' η (idp (ζ x a)) 
    r' : ζ y (θ y p) ≡ η y p
    r' = r y p
    s : ζ y (θ y p) ≡ ζ y b
    s = r' ∙ q
    t : θ y p ≡ b
    t = ζ-lc y s
    g : x , a ≡ y , b
    g = to-Σ-Id A (p , t)

NatΠ : ∀ {U V W} {X : U ̇} {A : X → V ̇} {B : X → W ̇} → Nat A B → Π A → Π B
NatΠ f g x = f x (g x) -- (S combinator from combinatory logic!)

NatΠ-lc : ∀ {U V W} {X : U ̇} {A : X → V ̇} {B : X → W ̇} (f : Nat A B)
    → ((x : X) → left-cancellable(f x))
    → {g g' : Π A} → NatΠ f g ≡ NatΠ f g' → g ∼ g'
NatΠ-lc f flc {g} {g'} p x = flc x (happly p x)

-- We don't need this anymore if we reorder the code:
ip-ie-idtofun : ∀ {U} (fe : FunExt U U) (X Y : U ̇) (p : X ≡ Y) → isProp(isEquiv(idtofun X Y p))
ip-ie-idtofun {U} fe X = Jbased X B go
 where
   B : (Y : U ̇) → X ≡ Y → U ̇
   B Y p = isProp(isEquiv(idtofun X Y p))
   A = Σ \(f : X → X) → f ≡ id
   a : isProp A
   a = isSingleton-isProp (paths-to-contractible id)
   A' = Σ \(f : X → X) → f ∼ id
   η : (f : X → X) → f ∼ id → f ≡ id
   η f = funext fe
   η-lc : (f : X → X) → left-cancellable(η f)
   η-lc f = funext-lc fe f id
   h : A' → A
   h = NatΣ η
   h-lc : left-cancellable h
   h-lc = NatΣ-lc (X → X) (λ f → f ∼ id) (λ f → f ≡ id) η η-lc
   b : isProp A'
   b = left-cancellable-reflects-isProp h h-lc a
   go : isProp(A' × A')
   go = props-closed-× b b

-- Or this:
jip : ∀ {U} → isUnivalent U → FunExt U U → {X Y : U ̇} 
   → (f : X → Y) → isProp(isEquiv f) 
jip {U} ua fe {X} {Y} f ije = h ije
  where
    e : X ≃ Y
    e = (f , ije)
    p : X ≡ Y
    p = eqtoid ua X Y e
    f' : X → Y
    f' = idtofun X Y p
    h' : isProp(isEquiv f')
    h' = ip-ie-idtofun fe X Y p
    ije' : isEquiv f'
    ije' = idtofun-isEquiv X Y p
    e' : X ≃ Y
    e' = f' , ije'
    q : e' ≡ e
    q = idtoeq-eqtoid ua X Y e
    q₁ : f' ≡ f
    q₁ = ap pr₁ q
    h : isProp(isEquiv f)
    h = yoneda-nat (λ f → isProp(isEquiv f)) h' f q₁

\end{code}

What we proved above using univalence also follows from K:

\begin{code}

\end{code}

The map eqtofun is left-cancellable assuming univalence (and function
extensionality, which is a consequence of univalence, but we don't
bother):

\begin{code}

eqtofun-lc : ∀ {U} → isUnivalent U → FunExt U U 
           → (X Y : U ̇) → left-cancellable(eqtofun X Y)
eqtofun-lc ua fe X Y {f , jef} {g , jeg} p = go
 where
  q : yoneda-nat isEquiv jef g p ≡ jeg
  q = jip ua fe g (yoneda-nat isEquiv jef g p) jeg
  go : f , jef ≡ g , jeg
  go = to-Σ-Id isEquiv (p , q)
  
\end{code}

The map idtofun is left-cancellable assuming univalence (and funext):

\begin{code}

isUnivalent-idtofun-lc : ∀ {U} → isUnivalent U → FunExt U U → (X Y : U ̇) 
                       → left-cancellable(idtofun X Y)
isUnivalent-idtofun-lc  ua fe X Y = left-cancellable-closed-under-∘
                                        (idtoeq X Y)
                                        (eqtofun X Y)
                                        (isUnivalent-idtoeq-lc ua X Y) (eqtofun-lc ua fe X Y)

\end{code}

We have the following characterization of univalence from the Yoneda
machinery:

\begin{code}

univalence-via-contractibility : ∀ {U} → isUnivalent U ⇔ ((X : U ̇) → isSingleton (Σ \(Y : U ̇) → X ≃ Y))
univalence-via-contractibility {U} = (f , g)
 where
  f : isUnivalent U → (X : U ̇) → isSingleton (Σ (Eq X))
  f ua X = repr-is-contr (X , (idtoeq X , ua X))

  g : ((X : U ̇) → isSingleton (Σ (Eq X))) → isUnivalent U
  g φ X = universality-equiv X (ideq X) (unique-element-is-universal-element (Eq X) (X , ideq X) (isSingleton-isProp (φ X) (X , ideq X)))

\end{code}

The fact that this is the case was announced on 5th August
2014 with the techniques of the HoTT Book
(https://groups.google.com/forum/#!msg/homotopytypetheory/HfCB_b-PNEU/Ibb48LvUMeUJ)),
and the proof given here via Yoneda was announced on 12th May 2015
(http://www.cs.bham.ac.uk/~mhe/yoneda/yoneda.html).

\begin{code}

id-isEmbedding : ∀ {U} {X : U ̇} → isEmbedding (id {U} {X})
id-isEmbedding = paths-to-isProp

idtofun' : ∀ {U} (X : U ̇) → Nat (Id X) (λ Y → X → Y)
idtofun' X = yoneda-nat (λ Y → X → Y) id

idtofun-agree : ∀ {U} (X : U ̇) → idtofun X ≈ idtofun' X
idtofun-agree X = yoneda-elem-lc (idtofun X) (idtofun' X) (idp id)

\end{code}
