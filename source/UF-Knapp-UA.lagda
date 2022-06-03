From Cory Knapp's PhD thesis (Chapter 2.4).

Transcribed to Agda by Martin Escardo and Cory 9th April and 24th May
2018.

Function extensionality follows from a generalization of
univalence. Using this, we formulate a condition equivalent to
the univalence of the universe U, namely

 (X Y : 𝓤 ̇ ) (f : X → Y) → qinv f → Σ p ꞉ X ≡ Y , transport id p ≡ f

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module UF-Knapp-UA where

open import SpartanMLTT
open import UF-Base
open import UF-Subsingletons
open import UF-Subsingletons-FunExt
open import UF-Equiv
open import UF-Equiv-FunExt
open import UF-Univalence
open import UF-FunExt
open import UF-FunExt-Properties
open import UF-Yoneda

\end{code}

We first define when a map is a path-induced equivalence, and the type
of path-induced equivalences.

\begin{code}

isPIE : {X Y : 𝓤 ̇ } → (X → Y) → 𝓤 ⁺ ̇
isPIE {𝓤} {X} {Y} = fiber (idtofun X Y)

isPIE-remark : {X Y : 𝓤 ̇ } (f : X → Y) → isPIE f ≡ (Σ p ꞉ X ≡ Y , idtofun X Y p ≡ f)
isPIE-remark f = refl

_⋍_ : 𝓤 ̇ → 𝓤 ̇ → 𝓤 ⁺ ̇
X ⋍ Y = Σ f ꞉ (X → Y) , isPIE f

idtopie : {X Y : 𝓤 ̇ } → X ≡ Y → X ⋍ Y
idtopie p = (idtofun _ _ p , p , refl)

pietofun : {X Y : 𝓤 ̇ } → X ⋍ Y → X → Y
pietofun (f , (p , q)) = f

pietoid : {X Y : 𝓤 ̇ } → X ⋍ Y → X ≡ Y
pietoid (f , (p , q)) = p

pietofun-factors-through-idtofun : {X Y : 𝓤 ̇ } (e : X ⋍ Y) → idtofun X Y (pietoid e) ≡ pietofun e
pietofun-factors-through-idtofun (f , (p , q)) = q

pietoid-idtopie : {X Y : 𝓤 ̇ } (p : X ≡ Y) → pietoid (idtopie p) ≡ p
pietoid-idtopie refl = refl

idtopie-pietoid : {X Y : 𝓤 ̇ } (e : X ⋍ Y) → idtopie (pietoid e) ≡ e
idtopie-pietoid (_ , refl , refl) = refl

PIE-induction : {X : 𝓤 ̇ } (A : {Y : 𝓤 ̇ } → (X → Y) → 𝓥 ̇ )
              → A id → {Y : 𝓤 ̇ } (f : X → Y) → isPIE f → A f
PIE-induction {𝓤} {𝓥} {X} A g {Y} f (p , q) = transport A r (φ p)
  where
   φ : {Y : 𝓤 ̇ } (p : X ≡ Y) → A (idtofun _ _ p)
   φ refl = g
   r : idtofun _ _ p ≡ f
   r = ap pr₁ (idtopie-pietoid (f , p , q))

isPIE-lc : {X Y : 𝓤 ̇ } (f : X → Y) → isPIE f → left-cancellable f
isPIE-lc = PIE-induction left-cancellable (λ {x} {x'} (p : id x ≡ id x') → p)

\end{code}

The following maps are considered in the original proof that
univalence implies function extensionality by Voevodsky as presented
by Gambino, Kapulkin and Lumsdaine in
http://www.math.uwo.ca/faculty/kapulkin/notes/ua_implies_fe.pdf:

\begin{code}

Δ : 𝓤 ̇ → 𝓤 ̇
Δ X = Σ x ꞉ X , Σ y ꞉ X , x ≡ y

δ : {X : 𝓤 ̇ } → X → Δ X
δ x = (x , x , refl)

π₁ : {X : 𝓤 ̇ } → Δ X → X
π₁ (x , _ , _) = x

π₂ : {X : 𝓤 ̇ } → Δ X → X
π₂ (_ , y , _) = y

πδ : (X : 𝓤 ̇ ) → π₁ ∘ δ ≡ π₂ ∘ δ
πδ {𝓤} X = refl {𝓤} {X → X}

\end{code}

We now give Cory Knapp's criterion for (naive and hence proper)
function extensionality:

\begin{code}

knapps-funext-criterion :
              ({X Y : 𝓤 ̇ } {f : X → Y} {g : X → Y} → isPIE f → f ∼ g → isPIE g)
            → ({X : 𝓤 ̇ } → isPIE (δ {𝓤} {X}))
            → ∀ {𝓥} → naive-funext 𝓥 𝓤
knapps-funext-criterion {𝓤} H D {𝓥} {X} {Y} {f₁} {f₂} h = γ
 where
  transport-isPIE : ∀ {𝓤 𝓥} {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {x y : X} (p : x ≡ y) → isPIE (transport A p)
  transport-isPIE refl = refl , refl

  back-transport-isPIE : ∀ {𝓤 𝓥} {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {x y : X} (p : x ≡ y)
                       → isPIE (transport⁻¹ A p)
  back-transport-isPIE p = transport-isPIE (p ⁻¹)

  back-transport-is-pre-comp'' : ∀ {𝓤} {X X' Y : 𝓤 ̇ } (e : X ⋍ X') (g : X' → Y)
                               → transport⁻¹ (λ - → - → Y) (pietoid e) g ≡ g ∘ pr₁ e
  back-transport-is-pre-comp'' {𝓤} {X} {X'} e g = transport⁻¹-is-pre-comp (pietoid e) g ∙ q ∙ r
   where
    φ : ∀ {𝓤} (X Y : 𝓤 ̇ ) (p : X ≡ Y) → Idtofun p ≡ pr₁ (idtopie p)
    φ X .X refl = refl
    q : g ∘ Idtofun (pietoid e) ≡ g ∘ pr₁ (idtopie (pietoid e))
    q = ap (λ - → g ∘ -) (φ X X' (pr₁ (pr₂ e)))
    r : g ∘ pr₁ (idtopie (pietoid e)) ≡ g ∘ pr₁ e
    r = ap (λ - → g ∘ -) (ap pr₁ (idtopie-pietoid e))

  preComp-isPIE : {X X' Y : 𝓤 ̇ } (e : X ⋍ X') → isPIE (λ (g : X' → Y) → g ∘ (pr₁ e))
  preComp-isPIE {X} {X'} e = H (back-transport-isPIE (pietoid e)) (back-transport-is-pre-comp'' e)

  π₁-equals-π₂ : {X : 𝓤 ̇ } → π₁ ≡ π₂
  π₁-equals-π₂ {X} = isPIE-lc (λ(g : Δ X → X) → g ∘ δ) (preComp-isPIE (δ , D)) (πδ X)

  γ : f₁ ≡ f₂
  γ = f₁                               ≡⟨ refl ⟩
      (λ x → f₁ x)                     ≡⟨ refl ⟩
      (λ x → π₁ (f₁ x , f₂ x , h x))   ≡⟨ ap (λ π x → π (f₁ x , f₂ x , h x)) π₁-equals-π₂ ⟩
      (λ x → π₂ (f₁ x , f₂ x , h x))   ≡⟨ refl ⟩
      (λ x → f₂ x)                     ≡⟨ refl ⟩
      f₂                               ∎

knapps-funext-Criterion :
              ({X Y : 𝓤 ̇ } {f : X → Y} {g : X → Y} → isPIE f → f ∼ g → isPIE g)
            → ({X : 𝓤 ̇ } → isPIE (δ {𝓤} {X}))
            → funext 𝓤 𝓤
knapps-funext-Criterion H D = naive-funext-gives-funext (knapps-funext-criterion H D)

\end{code}

Clearly, if univalence holds, then every equivalence is path induced:

\begin{code}

UA-is-equiv-isPIE : is-univalent 𝓤 → {X Y : 𝓤 ̇ } (f : X → Y) → is-equiv f → isPIE f
UA-is-equiv-isPIE ua f i = (eqtoid ua _ _ (f , i) , ap pr₁ (idtoeq-eqtoid ua _ _ (f , i)))

\end{code}

Next, we show that, conversely, if every equivalence is path induced,
then univalence holds.

\begin{code}

δ-is-equiv : {X : 𝓤 ̇ } → is-equiv (δ {𝓤} {X})
δ-is-equiv {𝓤} {X} = (π₁ , η) , (π₁ , ε)
 where
  η : (d : Δ X) → δ (π₁ d) ≡ d
  η (x , .x , refl) = refl
  ε : (x : X) → π₁ (δ x) ≡ x
  ε x = refl

isPIE-is-equiv : {X Y : 𝓤 ̇ } (f : X → Y) → isPIE f → is-equiv f
isPIE-is-equiv = PIE-induction is-equiv (pr₂ (≃-refl _))

is-equiv-isPIE-UA : ({X Y : 𝓤 ̇ } (f : X → Y) → is-equiv f → isPIE f) → is-univalent 𝓤
is-equiv-isPIE-UA {𝓤} φ X = γ
 where
  H : {X Y : 𝓤 ̇ } {f : X → Y} {g : X → Y} → isPIE f → f ∼ g → isPIE g
  H {X} {Y} {f} {g} isp h = φ g (equiv-closed-under-∼ f g (isPIE-is-equiv f isp) λ x → (h x)⁻¹)
  D : {X : 𝓤 ̇ } → isPIE (δ {𝓤} {X})
  D = φ δ δ-is-equiv
  k : funext 𝓤 𝓤
  k = knapps-funext-Criterion {𝓤} H D
  s : (Y : 𝓤 ̇ ) → X ≃ Y → X ≡ Y
  s Y (f , i) = pietoid (f , φ f i)
  η : {Y : 𝓤 ̇ } (e : X ≃ Y) → idtoeq X Y (s Y e) ≡ e
  η {Y} (f , i) = to-Σ-≡ (p , being-equiv-is-prop'' k f _ _)
   where
    p : pr₁ (idtoeq X Y (s Y (f , i))) ≡ f
    p = pietofun-factors-through-idtofun (f , φ f i)
  γ : (Y : 𝓤 ̇ ) → is-equiv (idtoeq X Y)
  γ = nats-with-sections-are-equivs X (idtoeq X) (λ Y → (s Y) , η)

\end{code}

We get the following characterization of univalence, where, as we can
see from the proof, we can replace qinv by is-equiv:

\begin{code}

UA-characterization :
                     ((X Y : 𝓤 ̇ ) (f : X → Y) → qinv f → fiber (transport id) f)
                   ⇔ is-univalent 𝓤
UA-characterization {𝓤} = (forth , back)
 where
  forth : ((X Y : 𝓤 ̇ ) (f : X → Y) → qinv f → Σ p ꞉ X ≡ Y , transport id p ≡ f) → is-univalent 𝓤
  forth γ = is-equiv-isPIE-UA (λ {X} {Y} → φ X Y)
   where
    φ : (X Y : 𝓤 ̇ ) (f : X → Y) → is-equiv f → isPIE f
    φ X Y f i = p , r
     where
      p : X ≡ Y
      p = pr₁ (γ X Y f (equivs-are-qinvs f i))
      q : transport id p ≡ f
      q = pr₂ (γ X Y f (equivs-are-qinvs f i))
      r : idtofun X Y p ≡ f
      r = idtofun-agreement X Y p ∙ q
  back : is-univalent 𝓤 → ((X Y : 𝓤 ̇ ) (f : X → Y) → qinv f → Σ p ꞉ X ≡ Y , transport id p ≡ f)
  back ua X Y f q = p , s
   where
    σ : Σ p ꞉ X ≡ Y , idtofun X Y p ≡ f
    σ = UA-is-equiv-isPIE ua f (qinvs-are-equivs f q)
    p : X ≡ Y
    p = pr₁ σ
    r : idtofun X Y p ≡ f
    r = pr₂ σ
    s : Idtofun p ≡ f
    s = (idtofun-agreement X Y p)⁻¹ ∙ r

\end{code}

TODO: Show that for any U, the type

  ({X Y : 𝓤 ̇ } (f : X → Y) → qinv f →  fiber (transport id) f))

is a proposition. Or give a counter-example or counter-model.

\end{code}
