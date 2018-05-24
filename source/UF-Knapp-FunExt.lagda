From Cory Knapp's PhD thesis (Chapter 2.4).

Transcribed to Agda by Martin Escardo and Cory 9th April and 24th May
2018.

Function extensionality follows from a generalization of univalence.

\begin{code}

{-# OPTIONS --without-K --exact-split #-}

module UF-Knapp-FunExt where

open import UF-Base
open import UF-Subsingletons
open import UF-Subsingletons-FunExt
open import UF-Equiv
open import UF-Equiv-FunExt
open import UF-Univalence
open import UF-FunExt
open import UF-FunExt-from-Naive-FunExt
open import UF-Yoneda

\end{code}

We first define when a map is a path-induced equivalence, and the type
of path-induced equivalences.

\begin{code}

isPIE : ∀ {U} {X Y : U ̇} → (X → Y) → U ′ ̇
isPIE {U} {X} {Y} = fiber (idtofun X Y)

isPIE-remark : ∀ {U} {X Y : U ̇} (f : X → Y) → isPIE f ≡ Σ \(p : X ≡ Y) → idtofun X Y p ≡ f
isPIE-remark f = refl

_⋍_ : ∀ {U} → U ̇ → U ̇ → U ′ ̇
X ⋍ Y = Σ \(f : X → Y) → isPIE f

idtopie : ∀ {U} {X Y : U ̇} → X ≡ Y → X ⋍ Y
idtopie p = (idtofun _ _ p , p , refl)

pietofun : ∀ {U} {X Y : U ̇} → X ⋍ Y → X → Y
pietofun (f , (p , q)) = f

pietoid : ∀ {U} {X Y : U ̇} → X ⋍ Y → X ≡ Y
pietoid (f , (p , q)) = p

pietofun-factors-through-idtofun : ∀ {U} {X Y : U ̇}
                                 → (e : X ⋍ Y) → idtofun X Y (pietoid e) ≡ pietofun e
pietofun-factors-through-idtofun (f , (p , q)) = q

pietoid-idtopie : ∀ {U} {X Y : U ̇} (p : X ≡ Y) → pietoid (idtopie p) ≡ p
pietoid-idtopie refl = refl

idtopie-pietoid : ∀ {U} {X Y : U ̇} (e : X ⋍ Y) → idtopie (pietoid e) ≡ e
idtopie-pietoid (_ , refl , refl) = refl

PIE-induction : ∀ {U V} {X : U ̇} (A : {Y : U ̇} → (X → Y) → V ̇)
              → A (id {U} {X}) → {Y : U ̇} (f : X → Y) → isPIE f → A f
PIE-induction {U} {V} {X} A g {Y} f (p , q) = transport A r (φ p)
  where
   φ : {Y : U ̇} (p : X ≡ Y) → A (idtofun _ _ p)
   φ refl = g
   r : idtofun _ _ p ≡ f
   r = ap pr₁ (idtopie-pietoid (f , p , q))

isPIE-lc : ∀ {U} {X Y : U ̇} (f : X → Y) → isPIE f → left-cancellable f
isPIE-lc = PIE-induction left-cancellable (λ {x} {x'} (p : id x ≡ id x') → p)

\end{code}

The following maps are considered in the original proof that
univalence implies function extensionality by Voevodsky as presented
by Gambino, Kapulkin and Lumsdaine in
http://www.math.uwo.ca/faculty/kapulkin/notes/ua_implies_fe.pdf:

\begin{code}

Δ : ∀ {U} → U ̇ → U ̇
Δ X = Σ \(x : X) → Σ \(y : X) → x ≡ y

δ : ∀ {U} {X : U ̇} → X → Δ X
δ x = (x , x , refl)

π₁ : ∀ {U} {X : U ̇} → Δ X → X
π₁ (x , _ , _) = x

π₂ : ∀ {U} {X : U ̇} → Δ X → X
π₂ (_ , y , _) = y

πδ : ∀ {U} (X : U ̇) → π₁ ∘ δ ≡ π₂ ∘ δ
πδ {U} X = refl {U} {X → X}

\end{code}

We now give Cory Knapp's criterion for (naive and hence proper)
function extensionality:

\begin{code}

knapps-funext-criterion : {U : Universe}
            → (∀ {X Y : U ̇} {f : X → Y} {g : X → Y} → isPIE f → f ∼ g → isPIE g)
            → (∀ {X : U ̇} → isPIE (δ {U} {X}))
            → ∀ {V} → naive-funext V U 
knapps-funext-criterion {U} H D {V} {X} {Y} {f₁} {f₂} h = γ
 where
  transport-isPIE : ∀ {U V} {X : U ̇} {A : X → V ̇} {x y : X} (p : x ≡ y) → isPIE (transport A p)
  transport-isPIE refl = refl , refl

  back-transport-isPIE : ∀ {U V} {X : U ̇} {A : X → V ̇} {x y : X} (p : x ≡ y) → isPIE (back-transport A p)
  back-transport-isPIE p = transport-isPIE (p ⁻¹)

  back-transport-is-pre-comp'' : ∀ {U} {X X' Y : U ̇} (e : X ⋍ X') (g : X' → Y)
                              → back-transport (λ Z → Z → Y) (pietoid e) g ≡ g ∘ pr₁ e 
  back-transport-is-pre-comp'' {U} {X} {X'} e g = back-transport-is-pre-comp (pietoid e) g ∙ q ∙ r
   where
    φ : ∀ {U} (X Y : U ̇) (p : X ≡ Y) → Idtofun p ≡ pr₁ (idtopie p)
    φ X .X refl = refl
    q : g ∘ Idtofun (pietoid e) ≡ g ∘ pr₁ (idtopie (pietoid e))
    q = ap (λ h → g ∘ h) (φ X X' (pr₁ (pr₂ e)))
    r : g ∘ pr₁ (idtopie (pietoid e)) ≡ g ∘ pr₁ e
    r = ap (λ h → g ∘ h) (ap pr₁ (idtopie-pietoid e))

  preComp-isPIE : {X X' Y : U ̇} (e : X ⋍ X') → isPIE (λ (g : X' → Y) → g ∘ (pr₁ e))
  preComp-isPIE {X} {X'} e = H (back-transport-isPIE (pietoid e)) (back-transport-is-pre-comp'' e)

  π₁-equals-π₂ : {X : U ̇} → π₁ ≡ π₂
  π₁-equals-π₂ {X} = isPIE-lc (λ(g : Δ X → X) → g ∘ δ) (preComp-isPIE (δ , D)) (πδ X)

  γ : f₁ ≡ f₂ 
  γ = f₁                               ≡⟨ refl ⟩
      (λ x → f₁ x)                    ≡⟨ refl ⟩ 
      (λ x → π₁ (f₁ x , f₂ x , h x))  ≡⟨ ap (λ π x → π (f₁ x , f₂ x , h x)) π₁-equals-π₂ ⟩
      (λ x → π₂ (f₁ x , f₂ x , h x))  ≡⟨ refl ⟩
      (λ x → f₂ x)                    ≡⟨ refl ⟩ 
      f₂                               ∎

knapps-funext-Criterion : {U : Universe}
            → (∀ {X Y : U ̇} {f : X → Y} {g : X → Y} → isPIE f → f ∼ g → isPIE g)
            → (∀ {X : U ̇} → isPIE (δ {U} {X}))
            → funext U U
knapps-funext-Criterion H D = naive-funext-gives-funext (knapps-funext-criterion H D)

\end{code}

Clearly, if univalence holds, then every equivalence is path induced@

\begin{code}

UA-is-equiv-isPIE : ∀ {U} → is-univalent U → {X Y : U ̇} (f : X → Y) → is-equiv f → isPIE f
UA-is-equiv-isPIE ua f ise = (eqtoid ua _ _ (f , ise) , ap pr₁ (idtoeq-eqtoid ua _ _ (f , ise)))

\end{code}

Next, we show that, conversely, if every equivalence is path induced,
then univalence holds.

\begin{code}

δ-is-equiv : ∀ {U} {X : U ̇} → is-equiv (δ {U} {X})
δ-is-equiv {U} {X} = (π₁ , η) , (π₁ , ε)
 where
  η : (d : Δ X) → δ (π₁ d) ≡ d
  η (x , .x , refl) = refl
  ε : (x : X) → π₁ (δ x) ≡ x
  ε x = refl

isPIE-is-equiv : ∀ {U} {X Y : U ̇} (f : X → Y) → isPIE f → is-equiv f
isPIE-is-equiv = PIE-induction is-equiv (pr₂ (ideq _))

is-equiv-isPIE-UA : ∀ {U} → ({X Y : U ̇} (f : X → Y) → is-equiv f → isPIE f) → is-univalent U
is-equiv-isPIE-UA {U} φ X = γ
 where
  H : ∀ {X Y : U ̇} {f : X → Y} {g : X → Y} → isPIE f → f ∼ g → isPIE g
  H {X} {Y} {f} {g} isp h = φ g (equiv-closed-under-∼ f g (isPIE-is-equiv f isp) λ x → (h x)⁻¹)
  D : ∀ {X : U ̇} → isPIE (δ {U} {X})
  D = φ δ δ-is-equiv
  k : funext U U
  k = knapps-funext-Criterion {U} H D
  s : (Y : U ̇) → X ≃ Y → X ≡ Y
  s Y (f , ise) = pietoid (f , φ f ise)
  η : {Y : U ̇} (e : X ≃ Y) → idtoeq X Y (s Y e) ≡ e
  η {Y} (f , ise) = to-Σ-≡'' (p , is-prop-is-equiv'' k f _ _)
   where
    p : pr₁ (idtoeq X Y (s Y (f , ise))) ≡ f
    p = pietofun-factors-through-idtofun (f , φ f ise)
  γ : (Y : U ̇) → is-equiv (idtoeq X Y)
  γ = nat-retraction-is-equiv X (idtoeq X) (λ Y → (s Y) , η)

\end{code}

We get the following characterization of univalence, where, as we can
see from the proof, we can replace qinv by is-equiv:

\begin{code}

UA-characterization : ∀ {U}
                   → ({X Y : U ̇} (f : X → Y) → qinv f → Σ \(p : X ≡ Y) → transport id p ≡ f)
                   ⇔ is-univalent U 
UA-characterization {U} = (forth , back)
 where
  forth : ({X Y : U ̇} (f : X → Y) → qinv f → Σ \(p : X ≡ Y) → transport id p ≡ f) → is-univalent U
  forth γ  = is-equiv-isPIE-UA φ
   where
    φ : {X Y : U ̇} (f : X → Y) → is-equiv f → isPIE f
    φ {X} {Y} f ise = p , r
     where
      p : X ≡ Y
      p = pr₁ (γ f (is-equiv-qinv f ise))
      q : transport id p ≡ f
      q = pr₂ (γ f (is-equiv-qinv f ise))
      r : idtofun X Y p ≡ f
      r = idtofun-agreement X Y p ∙ q
  back : is-univalent U → ({X Y : U ̇} (f : X → Y) → qinv f → Σ \(p : X ≡ Y) → transport id p ≡ f)
  back ua {X} {Y} f q = p , s
   where
    σ : Σ \(p : X ≡ Y) → idtofun X Y p ≡ f
    σ = UA-is-equiv-isPIE ua f (qinv-is-equiv f q)
    p : X ≡ Y
    p = pr₁ σ
    r : idtofun X Y p ≡ f
    r = pr₂ σ
    s : Idtofun p ≡ f
    s = (idtofun-agreement X Y p)⁻¹ ∙ r

\end{code}

TODO: Show that for any U, the type

  ({X Y : U ̇} (f : X → Y) → qinv f → Σ \(p : X ≡ Y) → transport id p ≡ f)

is a proposition. Or give a counter-example or counter-model.

\end{code}
