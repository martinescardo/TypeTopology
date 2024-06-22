Martin Escardo, Vincent Rahli, Bruno da Rocha Paiva, Ayberk Tosun 20 May 2023

We prove the correctness of the internal translation.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module EffectfulForcing.Internal.Correctness where

open import MLTT.Spartan hiding (rec ; _^_) renaming (⋆ to 〈〉)
open import EffectfulForcing.MFPSAndVariations.Combinators
open import EffectfulForcing.MFPSAndVariations.Continuity
open import EffectfulForcing.MFPSAndVariations.Dialogue
open import EffectfulForcing.MFPSAndVariations.SystemT using (type ; ι ; _⇒_ ; 〖_〗)
open import EffectfulForcing.MFPSAndVariations.LambdaCalculusVersionOfMFPS
                              using (B〖_〗 ; Kleisli-extension ; zero' ; succ' ; rec')
open import EffectfulForcing.MFPSAndVariations.Church
                              hiding (B⋆【_】 ; ⟪⟫⋆ ; _‚‚⋆_ ; B⋆⟦_⟧ ; dialogue-tree⋆)
open import EffectfulForcing.Internal.Internal hiding (B⋆⟦_⟧ ; dialogue-tree⋆)
open import EffectfulForcing.Internal.External
open import EffectfulForcing.Internal.SystemT
open import EffectfulForcing.Internal.Subst
open import EffectfulForcing.Internal.ExtensionalEquality
open import UF.Base using (transport₂ ; transport₃ ; ap₂ ; ap₃)

\end{code}

Using a logical relation we show that the the internal, church-encoded dialogue
translation of a System T term coincides with its external, inductive dialogue
translation.

From this result and the main-lemma we can derive an internal result of
strong continuity in System T.


We say that an inductive dialogue tree is the dialogue tree for a family of
System T Church-encoded dialogue trees if they are extensionally equal for
all possible instantiations.

\begin{code}

is-dialogue-for : B ℕ → ({A : type} → T₀ (B-type〖 ι 〗 A)) → Type
is-dialogue-for d t = {A : type} → ⟦ t ⟧₀ ≡[ ⌜B⌝ ι A ] church-encode d

\end{code}

The logical relation Rnorm is defined as the hereditary extension of
`is-dialogue-for`, and `Rnorms` is defined as the pointwise extension
of `Rnorm` to contexts.

\begin{code}

Rnorm : {σ : type} (d : B〖 σ 〗) (t : {A : type} → T₀ (B-type〖 σ 〗 A)) → Type
Rnorm {ι}     d t = is-dialogue-for d t
Rnorm {σ ⇒ τ} d t = (u : B〖 σ 〗) (u' : {A : type}
                  → T₀ (B-type〖 σ 〗 A))
                  → Rnorm u u'
                  → Rnorm (d u) (t · u')

\end{code}

TODO. Move this into Subst?

\begin{code}

IB【_】 : Cxt → type → Type
IB【 Γ 】 A = Sub₀ (B-context【 Γ 】 A)

Rnorms : {Γ : Cxt} → B【 Γ 】 → ({A : type} → IB【 Γ 】 A) → Type
Rnorms {Γ} xs ys = {σ : type} (i : ∈Cxt σ Γ) → Rnorm (xs i) (ys (∈Cxt-B-type i))


\end{code}

In this development we avoid the operational semantics of System T by instead
reasoning with the Agda functions the System T terms present. As a result,
instead of showing that the logical relation `Rnorm` is preserved by
the evaluation of functions, we show that it is preserved by extensional
equality.

\begin{code}

Rnorm-respects-≡ : {σ : type} {d : B〖 σ 〗} {t u : {A : type} → T₀ (B-type〖 σ 〗 A)}
                 → ({A : type} → ⟦ t ⟧₀ ≡[ (B-type〖 σ 〗 A) ] ⟦ u ⟧₀)
                 → Rnorm d t
                 → Rnorm d u
Rnorm-respects-≡ {ι} {d} {t} {u} t≡u Rnorm-d-t {A} =
 ⟦ u ⟧₀          ≡⟨ ≡-symm {⌜B⌝ ι A} t≡u ⟩
 ⟦ t ⟧₀          ≡＝⟨ Rnorm-d-t {A} ⟩
 church-encode d ∎
Rnorm-respects-≡ {σ ⇒ τ} {d} {t} {u} t≡u Rnorm-t v₁ v₂ Rnorm-vs =
 Rnorm-respects-≡ (t≡u (≡-refl₀ v₂)) (Rnorm-t v₁ v₂ Rnorm-vs)

\end{code}

We prove the fundamental theorem of the `Rnorm` logical relation in
`Rnorm-lemma`, which relates the inductive dialogue tree translation and the
Church-encoded dialogue tree translation for all System T terms.

TODO. This should be moved to the definition of numeral?

\begin{code}

⟦numeral⟧ : {Γ : Cxt} (γ : 【 Γ 】) (n : ℕ) → ⟦ numeral n ⟧ γ ≡ n
⟦numeral⟧ γ  zero    = refl
⟦numeral⟧ γ (succ n) = ap succ (⟦numeral⟧ γ n)

⟦numeral⟧₀ : (n : ℕ) → ⟦ numeral n ⟧₀ ＝ n
⟦numeral⟧₀  n = ⟦numeral⟧ ⟨⟩ n

Rnorm-η : (n : ℕ) → Rnorm (η n) (⌜η⌝ · numeral n)
Rnorm-η n η₁≡η₂ β₁≡β₂ = η₁≡η₂ (⟦numeral⟧₀ n)

Rnorm-η-implies-≡ : {n₁ : ℕ} {n₂ : T₀ ι}
                  → Rnorm (η n₁) (⌜η⌝ · n₂)
                  → ⟦ numeral n₁ ⟧₀ ≡ ⟦ n₂ ⟧₀
Rnorm-η-implies-≡ {n₁} {n₂} Rnorm-ns =
 ⟦ numeral n₁ ⟧₀ ≡⟨ ⟦numeral⟧₀ n₁ ⟩
 n₁              ≡⟨ ≡-symm (Rnorm-ns η₁≡η₁ β₁≡β₁) ⟩
 ⟦ n₂ ⟧₀         ∎
 where
  η₁ : ℕ → ℕ
  η₁ n = n

  η₁≡η₁ : η₁ ≡ η₁
  η₁≡η₁ n₁＝n₂ = n₁＝n₂

  β₁ : (ℕ → ℕ) → ℕ → ℕ
  β₁ ϕ n = 0

  β₁≡β₁ : β₁ ≡ β₁
  β₁≡β₁ ϕ₁≡ϕ₂ n₁≡n₂ = refl

\end{code}

TODO. Give this a better name and move it probably.

\begin{code}

η-type : type → type
η-type A = ι ⇒ A

β-type : type → type
β-type A = (ι ⇒ A) ⇒ ι ⇒ A

\end{code}

The System T term `Rec` is interpreted by the dialogue tree semantics using
`Kleisli-extension`, so when proving `Rnorm-lemma` we will need to know that
`Kleisli-extension` and `⌜Kleisli-extension⌝` will preserve functions related
by `Rnorm`.

TODO. Could probably generalise to extensionally equal dialogue trees d.

\begin{code}

church-encode-kleisli-extension : {A : type} (d : B ℕ)
                                → (f₁ : ℕ → B ℕ) (f₂ : {A : type} → T₀ (ι ⇒ ⌜B⌝ ι A))
                                → ((i : ℕ) → Rnorm (f₁ i) (f₂ · numeral i))
                                → church-encode (kleisli-extension f₁ d)
                                  ≡[ ⌜B⌝ ι A ] kleisli-extension⋆ ⟦ f₂ ⟧₀ (church-encode d)
church-encode-kleisli-extension {A} (η n) f₁ f₂ f₁≡f₂ =
 church-encode (f₁ n)                             ≡⟨ ≡-symm {⌜B⌝ ι A} (f₁≡f₂ n) ⟩
 ⟦ f₂ ⟧₀ ⟦ numeral n ⟧₀                           ≡＝⟨ ≡-refl₀ f₂ (⟦numeral⟧₀ n) ⟩
 kleisli-extension⋆ ⟦ f₂ ⟧₀ (church-encode (η n)) ∎
church-encode-kleisli-extension {A} (β ϕ n) f₁ f₂ f₁≡f₂ {η₁} {η₂} η₁≡η₂ {β₁} {β₂} β₁≡β₂ =
 β₁≡β₂ ϕ₁≡ϕ₂ refl
 where
  ϕ₁ : ℕ → 〖 A 〗
  ϕ₁ i = church-encode (kleisli-extension f₁ (ϕ i)) η₁ β₁

  ϕ₂ : ℕ → 〖 A 〗
  ϕ₂ i = kleisli-extension⋆ ⟦ f₂ ⟧₀ (church-encode (ϕ i)) η₂ β₂

  ϕ₁≡ϕ₂ : ϕ₁ ≡ ϕ₂
  ϕ₁≡ϕ₂ {i} {.i} refl = church-encode-kleisli-extension (ϕ i) f₁ f₂ f₁≡f₂ η₁≡η₂ β₁≡β₂

\end{code}

TODO. Maybe move this?

\begin{code}

⟦⌜Kleisli-extension⌝⟧ : {X A σ : type} {Γ Δ : Cxt} (xs : 【 Γ 】) (ys : 【 Δ 】)
                      → ⟦ ⌜Kleisli-extension⌝ {X} {A} {σ} ⟧ xs
                        ≡ ⟦ ⌜Kleisli-extension⌝ {X} {A} {σ} ⟧ ys
⟦⌜Kleisli-extension⌝⟧ {X} {A} {ι} {Γ} {Δ} xs ys d₁≡d₂ f₁≡f₂ η₁≡η₂ β₁≡β₂ =
 f₁≡f₂ (λ x₁≡x₂ → d₁≡d₂ x₁≡x₂ η₁≡η₂ β₁≡β₂) β₁≡β₂
⟦⌜Kleisli-extension⌝⟧ {X} {A} {σ ⇒ τ} {Γ} {Δ} xs ys g₁≡g₂ f₁≡f₂ x₁≡x₂ =
 ⟦⌜Kleisli-extension⌝⟧ _ _ (λ y₁≡y₂ → g₁≡g₂ y₁≡y₂ x₁≡x₂) f₁≡f₂

Rnorm-kleisli-lemma : {σ : type}

                      (f₁ : ℕ → B〖 σ 〗)
                      (f₂ : {A : type} → T₀ (ι ⇒ B-type〖 σ 〗 A))
                    → ((x : ℕ) → Rnorm (f₁ x) (f₂ · numeral x))

                    → (n₁ : B ℕ)
                      (n₂ : {A : type} → T₀ (⌜B⌝ ι A))
                    → Rnorm n₁ n₂

                    → Rnorm (Kleisli-extension f₁ n₁) (⌜Kleisli-extension⌝ · f₂ · n₂)
Rnorm-kleisli-lemma {ι} f₁ f₂ Rnorm-fs n₁ n₂ Rnorm-ns {A} =
 ⟦ ⌜kleisli-extension⌝ · f₂ · n₂ ⟧₀            ≡⟨ I ⟩
 kleisli-extension⋆ ⟦ f₂ ⟧₀ (church-encode n₁) ≡＝⟨ ≡-symm {⌜B⌝ ι A} II ⟩
 church-encode (kleisli-extension f₁ n₁)       ∎
 where
  I : ⟦ ⌜kleisli-extension⌝ · f₂ · n₂ ⟧₀ ≡ kleisli-extension⋆ ⟦ f₂ ⟧₀ (church-encode n₁)
  I = ≡-refl₀ (⌜kleisli-extension⌝ · f₂) Rnorm-ns

  II : church-encode (kleisli-extension f₁ n₁) ≡ kleisli-extension⋆ ⟦ f₂ ⟧₀ (church-encode n₁)
  II = church-encode-kleisli-extension n₁ f₁ f₂ Rnorm-fs

Rnorm-kleisli-lemma {σ ⇒ τ} f₁ f₂ Rnorm-fs n₁ n₂ Rnorm-ns u₁ u₂ Rnorm-us =
 Rnorm-respects-≡ I IH
 where

\end{code}

We perform some computation steps using the semantics.

\begin{code}

  I : {A : type}
    → ⟦ ⌜Kleisli-extension⌝ · ƛ (weaken₀ f₂ · ν₀ · weaken₀ u₂) · n₂ ⟧₀
      ≡[ B-type〖 τ 〗 A ] ⟦ ƛ (ƛ (ƛ (⌜Kleisli-extension⌝ · ƛ (ν₃ · ν₀ · ν₁) · ν₁))) · f₂ · n₂ · u₂ ⟧₀
  I = ⟦⌜Kleisli-extension⌝⟧ ⟨⟩ (⟨⟩ ‚ ⟦ f₂ ⟧₀ ‚ ⟦ n₂ ⟧₀ ‚ ⟦ u₂ ⟧₀)
       (λ x₁≡x₂ → ⟦weaken₀⟧ f₂ _ x₁≡x₂ (⟦weaken₀⟧ u₂ _))
       (≡-refl₀ n₂)

  II : (x : ℕ) {A : type}
     → ⟦ ƛ (weaken₀ f₂ · ν₀ · weaken₀ u₂) · numeral x ⟧₀
       ≡[ B-type〖 τ 〗 A ] ⟦ f₂ · numeral x · u₂ ⟧₀
  II x = ⟦weaken₀⟧ f₂ (⟨⟩ ‚ ⟦ numeral x ⟧ ⟨⟩) refl (⟦weaken₀⟧ u₂ (⟨⟩ ‚ ⟦ numeral x ⟧₀))

\end{code}

In the recursive case, Kleisli-extension calls Kleisli-extension at
the codomain type with the following new fs'.

\begin{code}

  f₁' : ℕ → B〖 τ 〗
  f₁' x = f₁ x u₁

  f₂' : {A : type} → T₀ (ι ⇒ B-type〖 τ 〗 A)
  f₂' = ƛ (weaken₀ f₂ · ν₀ · weaken₀ u₂)

\end{code}

Crucially, these fs' are still related by Rnorm, so we can use them to
get the inductive hypothesis IH.

\begin{code}

  Rnorm-fs' : (x : ℕ) → Rnorm (f₁' x) (f₂' · numeral x)
  Rnorm-fs' x = Rnorm-respects-≡ (≡-symm (II x)) (Rnorm-fs x u₁ u₂ Rnorm-us)

  IH : Rnorm (Kleisli-extension f₁' n₁) (⌜Kleisli-extension⌝ · f₂' · n₂)
  IH = Rnorm-kleisli-lemma f₁' f₂' Rnorm-fs' n₁ n₂ Rnorm-ns


\end{code}

TODO. this should be derivable from Rnorm-kleisli-lemma or
church-encode-kleisli-extension.

\begin{code}

church-encode-is-natural : {g₁ g₂ :  ℕ → ℕ} (d : B ℕ)
                         → g₁ ≡ g₂
                         → {A : type}
                         → B⋆-functor g₁ (church-encode d)
                           ≡[ ⌜B⌝ ι A ] church-encode (B-functor g₂ d)
church-encode-is-natural (η n) g₁≡g₂ {A} η₁≡η₂ β₁≡β₂ = η₁≡η₂ (g₁≡g₂ refl)
church-encode-is-natural {g₁} {g₂} (β ϕ n) g₁≡g₂ {A} {η₁} {η₂} η₁≡η₂ {β₁} {β₂} β₁≡β₂ =
 β₁≡β₂ ϕ₁≡ϕ₂ refl
 where
  ϕ₁ : ℕ → 〖 A 〗
  ϕ₁ i = B⋆-functor g₁ (church-encode (ϕ i)) η₁ β₁

  ϕ₂ : ℕ → 〖 A 〗
  ϕ₂ i = church-encode (B-functor g₂ (ϕ i)) η₂ β₂

  ϕ₁≡ϕ₂ : ϕ₁ ≡ ϕ₂
  ϕ₁≡ϕ₂ {i} {.i} refl = church-encode-is-natural (ϕ i) g₁≡g₂ η₁≡η₂ β₁≡β₂

\end{code}

TODO. Consider moving the compute lemmas to somewhere else?

\begin{code}

compute-Rec-Zero : {A σ : type} {Γ : Cxt}
                   (a : T (Γ ,, ι) (ι ⇒ B-type〖 σ ⇒ σ 〗 A))
                   (b : T Γ (B-type〖 σ 〗 A))
                   (s : Sub₀ Γ)
                 → ⟦ (close (ƛ (Rec a (weaken, ι b) ν₀)) s) · Zero ⟧₀
                   ≡ ⟦ close b s ⟧₀
compute-Rec-Zero {A} {σ} {Γ} a b s =
 ⟦ (close (ƛ (Rec a (weaken, ι b) ν₀)) s) · Zero ⟧₀
  ＝≡⟨ refl ⟩
 ⟦ close (weaken, ι b) (Subƛ s) ⟧ (⟨⟩ ‚ zero)
  ＝≡⟨ ap (λ k → ⟦ k ⟧ (⟨⟩ ‚ zero)) (close-weaken b (⊆, Γ ι) (Subƛ s)) ⟩
 ⟦ close b (⊆Sub (∈CxtS ι) (Subƛ s)) ⟧ (⟨⟩ ‚ zero)
  ≡⟨ ⟦close⟧ b (⊆Sub (∈CxtS ι) (Subƛ s)) _ _ (【≡】-is-refl‚ _ _ (λ ()) refl) (【≡】-【Sub】-⊆Sub' s) ⟩
 ⟦ b ⟧ (【Sub】 (⊆Sub (∈CxtS ι) (Subƛ s)) (⟨⟩ ‚ zero))
  ≡⟨ ≡-refl b (【≡】-【Sub】-⊆Sub s) ⟩
 ⟦ b ⟧ (【Sub₀】 s)
  ≡＝⟨ ≡-symm (⟦close⟧ b s _ _ (λ ()) (【≡】-is-refl-【Sub₀】 s)) ⟩
 ⟦ close b s ⟧₀
  ∎

compute-Rec-Succ
  : {A σ : type} {Γ : Cxt}
    (a : T Γ (B-type〖 ι ⇒ σ ⇒ σ 〗 A))
    (b : T Γ (B-type〖 σ 〗 A))
    (n : T₀ ι)
    (s : Sub₀ Γ)
  → ⟦ close (ƛ (Rec (ƛ (weaken, ι (weaken, ι a) · (⌜η⌝ · ν₀))) (weaken, ι b) ν₀)) s · Succ n ⟧₀
  ≡ ⟦ close a s · (⌜η⌝ · n) · Rec (ƛ (weaken, ι (close a s) · (⌜η⌝ · ν₀))) (close b s) n ⟧₀
compute-Rec-Succ {A} {σ} {Γ} a b n s =
 ⟦ close (ƛ (Rec (ƛ (weaken, ι (weaken, ι a) · (⌜η⌝ · ν₀))) (weaken, ι b) ν₀)) s · Succ n ⟧₀
  ＝≡⟨ refl ⟩
 ⟦ close (weaken, ι (weaken, ι a)) (Subƛ (Subƛ s)) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ ⟦ n ⟧₀)
  (η⋆ ⟦ n ⟧₀)
  (rec (λ x → ⟦ close (weaken, ι (weaken, ι a) · (⌜η⌝ · ν₀)) (Subƛ (Subƛ s)) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ x))
       (⟦ close (weaken, ι b) (Subƛ s) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀))
       ⟦ n ⟧₀)
  ≡＝⟨ e1 (λ z _ → z refl) e2 ⟩
 ⟦ close a s ⟧₀
  (η⋆ ⟦ n ⟧₀)
  (rec ⟦ ƛ (weaken, ι (close a s) · (⌜η⌝ · ν₀)) ⟧₀ ⟦ close b s ⟧₀ ⟦ n ⟧₀)
  ＝⟨ refl ⟩
 ⟦ close a s · (⌜η⌝ · n) · Rec (ƛ (weaken, ι (close a s) · (⌜η⌝ · ν₀))) (close b s) n ⟧₀
  ∎
 where
  e0 : {τ : type} (i : ∈Cxt τ Γ)
     → ⟦ weaken, ι (weaken, ι (s i)) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ ⟦ n ⟧₀)
     ≡ ⟦ s i ⟧₀
  e0 {τ} i =
   ⟦ weaken, ι (weaken, ι (s i)) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ ⟦ n ⟧₀)
    ≡＝⟨ ⟦weaken,-weaken,⟧ ⟨⟩ (succ ⟦ n ⟧₀) ⟦ n ⟧₀ (s i) refl (λ ()) ⟩
   ⟦ s i ⟧₀
    ∎

  e4 : {τ : type} (i : ∈Cxt τ Γ)
     → ⟦ weaken, ι (s i) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀)
     ≡ ⟦ s i ⟧₀
  e4 {τ} i = ⟦weaken,⟧ (s i) ι _ _ (λ ())

  e1 : ⟦ close (weaken, ι (weaken, ι a)) (Subƛ (Subƛ s)) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ ⟦ n ⟧₀)
     ≡ ⟦ close a s ⟧₀
  e1 =
   ⟦ close (weaken, ι (weaken, ι a)) (Subƛ (Subƛ s)) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ ⟦ n ⟧₀)
    ≡⟨ ⟦close⟧ (weaken, ι (weaken, ι a))
               (Subƛ (Subƛ s))
               _ _
               (【≡】-is-refl‚ _ _ (【≡】-is-refl‚ _ _ (λ ()) refl) refl)
               (【≡】-【Sub】-Subƛ' _ _ _ refl refl) ⟩
   ⟦ weaken, ι (weaken, ι a) ⟧ (【Sub】 (Subƛ (Subƛ s)) (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ ⟦ n ⟧₀))
    ≡⟨ ≡-refl (weaken, ι (weaken, ι a)) (【≡】-【Sub】-Subƛ2 s (succ ⟦ n ⟧₀) ⟦ n ⟧₀ refl refl) ⟩
   ⟦ weaken, ι (weaken, ι a) ⟧ (【Sub₀】 s ‚ succ ⟦ n ⟧₀ ‚ ⟦ n ⟧₀)
    ≡⟨ ⟦weaken,-weaken,⟧ (【Sub₀】 s) (succ ⟦ n ⟧₀) ⟦ n ⟧₀ a refl (【≡】-is-refl-【Sub₀】 s) ⟩
   ⟦ a ⟧ (【Sub₀】 s)
    ≡＝⟨ ≡-symm {B-type〖 ι ⇒ σ ⇒ σ 〗 A} (⟦close⟧' a s) ⟩
   ⟦ close a s ⟧₀
    ∎

  e3 : ⟦ close (weaken, ι b) (Subƛ s) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀) ≡ ⟦ close b s ⟧₀
  e3 =
   ⟦ close (weaken, ι b) (Subƛ s) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀)
    ≡⟨ ⟦close⟧ (weaken, ι b)
               (Subƛ s)
               _ _
               (【≡】-is-refl‚ _ _ (λ ()) refl)
               (【≡】-【Sub】-Subƛ _ _ refl) ⟩
   ⟦ weaken, ι b ⟧ (【Sub】 (Subƛ s) (⟨⟩ ‚ succ ⟦ n ⟧₀))
    ≡⟨ ⟦weaken,⟧ b ι _ _ (【≡】-is-refl-【⊆】-⊆,-【Sub】-Subƛ s _ refl) ⟩
   ⟦ b ⟧ (【⊆】 (⊆, Γ ι) (【Sub】 (Subƛ s) (⟨⟩ ‚ succ ⟦ n ⟧₀)))
    ≡⟨ ≡-refl b e4 ⟩
   ⟦ b ⟧ (【Sub₀】 s)
    ≡＝⟨ ≡-symm (⟦close⟧' b s) ⟩
   ⟦ close b s ⟧₀
    ∎

  e6 : (i : ℕ) {τ : type} (j : ∈Cxt τ Γ)
     → ⟦ weaken, ι (weaken, ι (s j)) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ i)
     ≡ ⟦ s j ⟧₀
  e6 i {τ} j = ≡-trans (⟦weaken,-weaken,⟧-as-⟦weaken,⟧ ⟨⟩ i (succ ⟦ n ⟧₀) i (s j) refl (λ ()))
                       (⟦weaken,⟧ (s j) ι _ _ (λ ()))

  e5 : (i : ℕ) (u v : 〖 B-type〖 σ 〗 A 〗)
     → u ≡ v
     → ⟦ close (weaken, ι (weaken, ι a)) (Subƛ (Subƛ s)) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ i) (η⋆ i) u
     ≡ ⟦ weaken, ι (close a s) ⟧ (⟨⟩ ‚ i) (η⋆ i) v
  e5 i u v e =
   ⟦ close (weaken, ι (weaken, ι a)) (Subƛ (Subƛ s)) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ i) (η⋆ i) u
    ≡⟨ ⟦close⟧ (weaken, ι (weaken, ι a))
               (Subƛ (Subƛ s))
               (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ i)
               (【Sub】 (Subƛ (Subƛ s)) (⟨⟩ ‚ succ (⟦ n ⟧ ⟨⟩) ‚ i))
               ((【≡】-is-refl‚ _ _ (【≡】-is-refl‚ _ _ (λ ()) refl) refl))
               ((【≡】-【Sub】-Subƛ' _ _ _ refl refl)) (λ z _ → z refl) e ⟩
   ⟦ weaken, ι (weaken, ι a) ⟧ (【Sub】 (Subƛ (Subƛ s)) (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ i)) (η⋆ i) v
    ≡⟨ ≡-refl (weaken, ι (weaken, ι a))
              ((【≡】-【Sub】-Subƛ2 s (succ ⟦ n ⟧₀) i refl refl))
              (λ z _ → z refl) (≡ᵣ v e) ⟩
   ⟦ weaken, ι (weaken, ι a) ⟧ (【Sub₀】 s ‚ succ ⟦ n ⟧₀ ‚ i) (η⋆ i) v
    ≡⟨  ⟦weaken,-weaken,⟧ (【Sub₀】 s) (succ ⟦ n ⟧₀) i a refl (【≡】-is-refl-【Sub₀】 s) (η⋆≡η⋆ refl) (≡ᵣ v e) ⟩
   ⟦ a ⟧ (【Sub₀】 s ) (η⋆ i) v
    ≡⟨ ≡-symm {B-type〖 σ 〗 A}
              (⟦close⟧ a s (【⊆】 (∈CxtS ι) (⟨⟩ ‚ i))
                       (【Sub₀】 s) (λ ())
                       (【≡】-is-refl-【Sub₀】 s)
                       (η⋆≡η⋆ refl) (≡ᵣ v e)) ⟩
   ⟦ close a s ⟧ (【⊆】 (⊆, 〈〉 ι) (⟨⟩ ‚ i)) (η⋆ i) v
    ≡＝⟨ ≡-symm (⟦weaken,⟧ (close a s) ι _ _ (λ ()) (η⋆≡η⋆ refl) (≡ᵣ v e)) ⟩
   ⟦ weaken, ι (close a s) ⟧ (⟨⟩ ‚ i) (η⋆ i) v
    ∎

  e7 : {i j : ℕ} → i ＝ j → {u v : 〖 B-type〖 σ 〗 A 〗}
     → u ≡ v
     → ⟦ close (weaken, ι (weaken, ι a)) (Subƛ (Subƛ s)) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ i) (η⋆ i) u
     ≡ ⟦ weaken, ι (close a s) ⟧ (⟨⟩ ‚ j) (η⋆ j) v
  e7 {i} {.i} refl {u} {v} e = e5 i u v e

  e2 : rec (λ x → ⟦ close (weaken, ι (weaken, ι a) · (⌜η⌝ · ν₀)) (Subƛ (Subƛ s)) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ x))
        (⟦ close (weaken, ι b) (Subƛ s) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀))
        ⟦ n ⟧₀
     ≡ rec ⟦ ƛ (weaken, ι (close a s) · (⌜η⌝ · ν₀)) ⟧₀ ⟦ close b s ⟧₀ ⟦ n ⟧₀
  e2 = rec≡rec e7 e3 (≡-refl₀ n)

\end{code}

As opposed to compute-Rec-Succ, this one does not "reduce" as much.

\begin{code}

compute-Rec-Succ2
 : {A σ : type} {Γ : Cxt}
   (a : T Γ (B-type〖 ι ⇒ σ ⇒ σ 〗 A))
   (b : T Γ (B-type〖 σ 〗 A))
   (n : T₀ ι)
   (s : Sub₀ Γ)
 → ⟦ close (ƛ (Rec (ƛ (weaken, ι (weaken, ι a) · (⌜η⌝ · ν₀))) (weaken, ι b) ν₀)) s  · n ⟧₀
   ≡ ⟦ Rec (ƛ (weaken, ι (close a s) · (⌜η⌝ · ν₀))) (close b s) n ⟧₀
compute-Rec-Succ2 {A} {σ} {Γ} a b n s =
 rec (λ y → ⟦ close (weaken, ι (weaken, ι a)) (Subƛ (Subƛ s)) ⟧ (⟨⟩ ‚ ⟦ n ⟧₀ ‚ y) (η⋆ y))
     (⟦ close (weaken, ι b) (Subƛ s) ⟧ (⟨⟩ ‚ ⟦ n ⟧₀))
     ⟦ n ⟧₀
  ≡＝⟨ rec≡rec e5 e1 (≡-refl₀ n) ⟩
 rec (λ y → ⟦ weaken, ι (close a s) ⟧ (⟨⟩ ‚ y) (η⋆ y))
     ⟦ close b s ⟧₀
     ⟦ n ⟧₀
  ∎
 where
  e4 : (i : ℕ) {τ : type} (j : ∈Cxt τ Γ)
     → ⟦ weaken, ι (weaken, ι (s j)) ⟧ (⟨⟩ ‚ ⟦ n ⟧₀ ‚ i)
     ≡ ⟦ s j ⟧₀
  e4 i {τ} j = ⟦weaken,-weaken,⟧ ⟨⟩ ⟦ n ⟧₀ i (s j) refl (λ ())

  e3 : (i : ℕ) (u v : 〖 B-type〖 σ 〗 A 〗)
     → u ≡ v
     → ⟦ close (weaken, ι (weaken, ι a)) (Subƛ (Subƛ s)) ⟧ (⟨⟩ ‚ ⟦ n ⟧₀ ‚ i) (η⋆ i) u
     ≡ ⟦ weaken, ι (close a s) ⟧ (⟨⟩ ‚ i) (η⋆ i) v
  e3 i u v e =
   ⟦ close (weaken, ι (weaken, ι a)) (Subƛ (Subƛ s)) ⟧ (⟨⟩ ‚ ⟦ n ⟧₀ ‚ i) (η⋆ i) u
    ≡⟨ ⟦close⟧ (weaken, ι (weaken, ι a)) (Subƛ (Subƛ s)) (⟨⟩ ‚ ⟦ n ⟧₀ ‚ i)
        (【Sub】 (Subƛ (Subƛ s)) (⟨⟩ ‚ ⟦ n ⟧₀ ‚ i))
        (【≡】-is-refl‚ _ _ (【≡】-is-refl‚ _ _ (λ ()) refl) refl)
        (【≡】-【Sub】-Subƛ' _ _ _ refl refl)
        (η⋆≡η⋆ refl) e ⟩
   ⟦ weaken, ι (weaken, ι a) ⟧ (【Sub】 (Subƛ (Subƛ s)) (⟨⟩ ‚ ⟦ n ⟧₀ ‚ i)) (η⋆ i) v
    ≡⟨ ≡-refl (weaken, ι (weaken, ι a))
              (【≡】-【Sub】-Subƛ2 s (⟦ n ⟧₀) i refl refl)
              (η⋆≡η⋆ refl) (≡ᵣ v e) ⟩
   ⟦ weaken, ι (weaken, ι a) ⟧ (【Sub₀】 s ‚ ⟦ n ⟧₀ ‚ i) (η⋆ i) v
    ≡⟨ ⟦weaken,-weaken,⟧ (【Sub₀】 s) (⟦ n ⟧₀)
                         i a refl
                         (【≡】-is-refl-【Sub₀】 s)
                         (η⋆≡η⋆ refl) (≡ᵣ v e) ⟩
   ⟦ a ⟧ (【Sub₀】 s ) (η⋆ i) v
    ≡⟨ ≡-symm (⟦close⟧ a s (【⊆】 (∈CxtS ι) (⟨⟩ ‚ i))
                      (【Sub₀】 s) (λ ())
                      (【≡】-is-refl-【Sub₀】 s)
                      (η⋆≡η⋆ refl) (≡ᵣ v e)) ⟩
   ⟦ close a s ⟧ (【⊆】 (⊆, 〈〉 ι) (⟨⟩ ‚ i)) (η⋆ i) v
    ≡＝⟨ ≡-symm (⟦weaken,⟧ (close a s) ι _ _ (λ ()) (η⋆≡η⋆ refl) (≡ᵣ v e)) ⟩
   ⟦ weaken, ι (close a s) ⟧ (⟨⟩ ‚ i) (η⋆ i) v
    ∎

  e5 : {i j : ℕ} → i ＝ j → {u v : 〖 B-type〖 σ 〗 A 〗}
     → u ≡ v
     → ⟦ close (weaken, ι (weaken, ι a)) (Subƛ (Subƛ s)) ⟧ (⟨⟩ ‚ ⟦ n ⟧₀ ‚ i) (η⋆ i) u
     ≡ ⟦ weaken, ι (close a s) ⟧ (⟨⟩ ‚ j) (η⋆ j) v
  e5 {i} {.i} refl {u} {v} e = e3 i u v e

  e2 : {τ : type} (i : ∈Cxt τ Γ)
     → ⟦ weaken, ι (s i) ⟧ (⟨⟩ ‚ ⟦ n ⟧₀)
     ≡ ⟦ s i ⟧₀
  e2 {τ} i = ⟦weaken,⟧ (s i) ι _ _ (λ ())

  e1 : ⟦ close (weaken, ι b) (Subƛ s) ⟧ (⟨⟩ ‚ ⟦ n ⟧₀) ≡ ⟦ close b s ⟧₀
  e1 =
   ⟦ close (weaken, ι b) (Subƛ s) ⟧ (⟨⟩ ‚ ⟦ n ⟧₀)
    ≡⟨ ⟦close⟧ (weaken, ι b) (Subƛ s)
               _ _ (【≡】-is-refl‚ _ _ (λ ()) refl)
               (【≡】-【Sub】-Subƛ _ _ refl) ⟩
   ⟦ weaken, ι b ⟧ (【Sub】 (Subƛ s) (⟨⟩ ‚ ⟦ n ⟧₀))
    ≡⟨ ⟦weaken,⟧ b ι _ _ (【≡】-is-refl-【⊆】-⊆,-【Sub】-Subƛ s _ refl) ⟩
   ⟦ b ⟧ (【⊆】 (⊆, Γ ι) (【Sub】 (Subƛ s) (⟨⟩ ‚ ⟦ n ⟧₀)))
    ≡⟨ ≡-refl b e2 ⟩
   ⟦ b ⟧ (【Sub₀】 s)
    ≡＝⟨ ≡-symm (⟦close⟧' b s) ⟩
   ⟦ close b s ⟧₀
    ∎

⟦⌜Rec⌝⟧-aux : {A : type} {σ : type} {Γ : Cxt}
              (s : 【 B-context【 Γ 】 A 】)
              (a : T Γ (ι ⇒ σ ⇒ σ))
              (b : T Γ σ)
              (a₁ b₁ : ℕ)
            → a₁ ＝ b₁
            → 【≡】-is-refl s
            → rec (λ y → ⟦ ⌜ a ⌝ ⟧ s (η⋆ y)) (⟦ ⌜ b ⌝ ⟧ s) a₁
            ≡ rec (λ y → ⟦ weaken, ι (weaken, ι ⌜ a ⌝) ⟧ (s ‚ b₁ ‚ y) (η⋆ y))
                  (⟦ weaken, ι ⌜ b ⌝ ⟧ (s ‚ b₁))
                  b₁
⟦⌜Rec⌝⟧-aux {A} {σ} {Γ} s a b a₁ b₁ a≡₁ r =
 rec≡rec c (≡-symm (⟦weaken,⟧ ⌜ b ⌝ ι (s ‚ b₁) s r)) a≡₁
 where
  c : {a₂ b₂ : ℕ}
    → a₂ ＝ b₂
    → {a₃ b₃ : 〖 B-type〖 σ 〗 A 〗}
    → a₃ ≡ b₃
    → ⟦ ⌜ a ⌝ ⟧ s (η⋆ a₂) a₃
    ≡ ⟦ weaken, ι (weaken, ι ⌜ a ⌝) ⟧ (s ‚ b₁ ‚ b₂) (η⋆ b₂) b₃
  c a≡₂ a≡₃ =
   ≡-symm (⟦weaken,-weaken,⟧ s _ _ ⌜ a ⌝ refl r (η⋆≡η⋆ (≡-symm a≡₂)) (≡-symm a≡₃))

⟦⌜Rec⌝⟧ : {A : type} {σ : type} {Γ : Cxt}
          (s : 【 B-context【 Γ 】 A 】)
          (a : T Γ (ι ⇒ σ ⇒ σ))
          (b : T Γ σ)
          (c : T Γ ι)
        → 【≡】-is-refl s
        → ⟦ ⌜_⌝  {Γ} {σ} {A} (Rec a b c) ⟧ s
        ≡ ⟦ ⌜Kleisli-extension⌝ {ι} {A} {σ}
            · (ƛ (Rec (ƛ (weaken, ι (weaken, ι ⌜ a ⌝) · (⌜η⌝ · ν₀))) (weaken, ι ⌜ b ⌝) ν₀))
            · ⌜ c ⌝ ⟧ s
⟦⌜Rec⌝⟧ {A} {σ} {Γ} s a b c r =
 ⟦ ⌜_⌝  {Γ} {σ} {A} (Rec a b c) ⟧ s
  ＝≡⟨ refl ⟩
 ⟦ ⌜Kleisli-extension⌝ {ι} {A} {σ} ⟧ (s ‚ ⟦ ⌜ a ⌝ ⟧ s ‚ ⟦ ⌜ b ⌝ ⟧ s)
  (λ x → rec (λ y → ⟦ ⌜ a ⌝ ⟧ s (η⋆ y)) (⟦ ⌜ b ⌝ ⟧ s) x)
  (⟦ ⌜ c ⌝ ⟧ s)
  ≡＝⟨ ⟦⌜Kleisli-extension⌝⟧ (s ‚ ⟦ ⌜ a ⌝ ⟧ s ‚ ⟦ ⌜ b ⌝ ⟧ s) s
       (λ {a₁} {b₁} a≡ → ⟦⌜Rec⌝⟧-aux s a b a₁ b₁ a≡ r)
       (≡-refl ⌜ c ⌝ r) ⟩
 ⟦ ⌜Kleisli-extension⌝ {ι} {A} {σ}
   · (ƛ (Rec (ƛ (weaken, ι (weaken, ι ⌜ a ⌝) · (⌜η⌝ · ν₀))) (weaken, ι ⌜ b ⌝) ν₀))
   · ⌜ c ⌝ ⟧ s
  ∎

⟦close-⌜Rec⌝⟧ : {A : type} {σ : type} {Γ : Cxt}
                (s : IB【 Γ 】 A)
                (a : T Γ (ι ⇒ σ ⇒ σ))
                (b : T Γ σ)
                (c : T Γ ι)
              → ⟦ close (⌜_⌝  {Γ} {σ} {A} (Rec a b c)) s ⟧₀
              ≡ ⟦ ⌜Kleisli-extension⌝ {ι} {A} {σ}
                   · close (ƛ (Rec (ƛ (weaken, ι (weaken, ι ⌜ a ⌝) · (⌜η⌝ · ν₀))) (weaken, ι ⌜ b ⌝) ν₀)) s
                   · close ⌜ c ⌝ s ⟧₀
⟦close-⌜Rec⌝⟧ {A} {σ} {Γ} s a b c =
 ⟦ close (⌜_⌝  {Γ} {σ} {A} (Rec a b c)) s ⟧₀
  ≡⟨ ⟦close⟧' ⌜ Rec a b c ⌝ s ⟩
 ⟦ ⌜_⌝  {Γ} {σ} {A} (Rec a b c) ⟧ (【Sub₀】 s)
  ≡⟨ ⟦⌜Rec⌝⟧ (【Sub₀】 s) a b c (【≡】-is-refl-【Sub₀】 s) ⟩
 ⟦ ⌜Kleisli-extension⌝ {ι} {A} {σ}
   · (ƛ (Rec (ƛ (weaken, ι (weaken, ι ⌜ a ⌝) · (⌜η⌝ · ν₀))) (weaken, ι ⌜ b ⌝) ν₀))
   · ⌜ c ⌝ ⟧ (【Sub₀】 s)
  ≡＝⟨ ≡-symm (⟦close⟧' (⌜Kleisli-extension⌝ {ι} {A} {σ}
                        · (ƛ (Rec (ƛ (weaken, ι (weaken, ι ⌜ a ⌝) · (⌜η⌝ · ν₀))) (weaken, ι ⌜ b ⌝) ν₀))
                        · ⌜ c ⌝) s) ⟩
 ⟦ close ⌜Kleisli-extension⌝ s
   · close (ƛ (Rec (ƛ (weaken, ι (weaken, ι ⌜ a ⌝) · (⌜η⌝ · ν₀))) (weaken, ι ⌜ b ⌝) ν₀)) s
   · close ⌜ c ⌝ s ⟧₀
  ＝⟨ ap (λ k → ⟦ k · close (ƛ (Rec (ƛ (weaken, ι (weaken, ι ⌜ a ⌝) · (⌜η⌝ · ν₀))) (weaken, ι ⌜ b ⌝) ν₀)) s
                    · close ⌜ c ⌝ s ⟧₀)
         ((close-⌜Kleisli-extension⌝ s) ⁻¹) ⟩
 ⟦ ⌜Kleisli-extension⌝ {ι} {A} {σ}
   · close (ƛ (Rec (ƛ (weaken, ι (weaken, ι ⌜ a ⌝) · (⌜η⌝ · ν₀))) (weaken, ι ⌜ b ⌝) ν₀)) s
   · close ⌜ c ⌝ s ⟧₀
  ∎

\end{code}

TODO. Maybe move this too.

\begin{code}

Rnorm-Zero : Rnorm zero' ⌜zero⌝
Rnorm-Zero {A} η₁≡η₂ β₁≡β₂ = η₁≡η₂ refl

\end{code}

TODO. Move the following functions probably.

\begin{code}

succ≡succ : succ ≡ succ
succ≡succ = ap succ

B⋆-functor≡B⋆-functor : {A : type}
                      → B⋆-functor ≡[ (ι ⇒ ι) ⇒ ⌜B⌝ ι A ⇒ ⌜B⌝ ι A ] B⋆-functor
B⋆-functor≡B⋆-functor f₁≡f₂ η₁≡η₂ β₁≡β₂ = η₁≡η₂ (λ n₁≡n₂ → β₁≡β₂ (f₁≡f₂ n₁≡n₂))

Rnorm-lemma : {Γ : Cxt} {σ : type}
              (γ₁ : B【 Γ 】) (γ₂ : {A : type} → IB【 Γ 】 A)
              (t : T Γ σ)
            → Rnorms γ₁ γ₂
            → Rnorm (B⟦ t ⟧ γ₁) (close ⌜ t ⌝ γ₂)

Rnorm-lemma γ₁ γ₂ Zero Rnorm-γs = Rnorm-Zero

Rnorm-lemma γ₁ γ₂ (Succ t) Rnorm-γs =
 B⋆-functor succ ⟦ close ⌜ t ⌝ γ₂ ⟧₀         ≡⟨ I ⟩
 B⋆-functor succ (church-encode (B⟦ t ⟧ γ₁)) ≡＝⟨ II ⟩
 church-encode (B-functor succ (B⟦ t ⟧ γ₁))  ∎
 where
  I  = B⋆-functor≡B⋆-functor succ≡succ (Rnorm-lemma γ₁ γ₂ t Rnorm-γs)
  II = church-encode-is-natural (B⟦ t ⟧ γ₁) succ≡succ

Rnorm-lemma {Γ} {σ} γ₁ γ₂ (Rec t u v) Rnorm-γs =
  Rnorm-respects-≡ (≡-symm (⟦close-⌜Rec⌝⟧ γ₂ t u v)) c1
 where
  rt : (x  : B〖 ι 〗) (x' : {A : type} → T₀ (B-type〖 ι 〗 A)) (rx : Rnorm {ι} x x')
       (y  : B〖 σ 〗) (y' : {A : type} → T₀ (B-type〖 σ 〗 A)) (ry : Rnorm {σ} y y')
     → Rnorm (B⟦ t ⟧ γ₁ x y) (close ⌜ t ⌝ γ₂ · x' · y')
  rt = Rnorm-lemma γ₁ γ₂ t Rnorm-γs

  rn : ℕ → B〖 σ 〗
  rn n = rec (B⟦ t ⟧ γ₁ ∘ η) (B⟦ u ⟧ γ₁) n

  rn' : {A : type} → T₀ (ι ⇒ B-type〖 σ 〗 A)
  rn' = close (ƛ (Rec (ƛ (weaken, ι (weaken, ι ⌜ t ⌝) · (⌜η⌝ · ν₀))) (weaken, ι ⌜ u ⌝) ν₀)) γ₂

  rnn' : (n : ℕ) → Rnorm (rn n) (rn' · numeral n)
  rnn' zero = r
   where
    r : Rnorm (B⟦ u ⟧ γ₁) (rn' · Zero)
    r = Rnorm-respects-≡
         (≡-symm (compute-Rec-Zero (ƛ (weaken, ι (weaken, ι ⌜ t ⌝) · (⌜η⌝ · ν₀))) ⌜ u ⌝ γ₂))
         (Rnorm-lemma γ₁ γ₂ u Rnorm-γs)
  rnn' (succ n) = r
   where
    r : Rnorm (B⟦ t ⟧ γ₁ (η n) (rn n)) (rn' · Succ (numeral n))
    r = Rnorm-respects-≡
         (≡-symm (compute-Rec-Succ ⌜ t ⌝ ⌜ u ⌝ (numeral n) γ₂))
         (rt (η n) (⌜η⌝ · numeral n) (Rnorm-η n)
             (rn n) (Rec (ƛ (weaken, ι (close ⌜ t ⌝ γ₂) · (⌜η⌝ · ν₀))) (close ⌜ u ⌝ γ₂) (numeral n))
             (Rnorm-respects-≡
               (compute-Rec-Succ2 ⌜ t ⌝ ⌜ u ⌝ (numeral n) γ₂)
               (rnn' n)))

  rnn'' : (n : ℕ) (n' : T₀ ι) → Rnorm (η n) (⌜η⌝ · n') → Rnorm (rn n) (rn' · n')
  rnn'' n n' r =
   Rnorm-respects-≡ (≡-refl₀ rn' (Rnorm-η-implies-≡ {n} {n'} r)) (rnn' n)

  c1 : Rnorm (Kleisli-extension rn (B⟦ v ⟧ γ₁))
             (⌜Kleisli-extension⌝ · rn' · close ⌜ v ⌝ γ₂)
  c1 = Rnorm-kleisli-lemma rn rn' rnn' (B⟦ v ⟧ γ₁) (close ⌜ v ⌝ γ₂) (Rnorm-lemma γ₁ γ₂ v Rnorm-γs)

Rnorm-lemma γ₁ γ₂ (ν i) Rnorm-γs = Rnorm-γs i

Rnorm-lemma γ₁ γ₂ (ƛ t) Rnorm-γs u₁ u₂ Rnorm-us = Rnorm-respects-≡ I IH
 where

\end{code}

Using the semantics, we reduce application of a lambda to the appropriate
substitution, at which point we can use the inductive hypothesis.

\begin{code}

  I : {A : type} → ⟦ close ⌜ t ⌝ (Sub,, γ₂ u₂) ⟧₀ ≡[ B-type〖 _ 〗 A ] ⟦ ƛ (close ⌜ t ⌝ (Subƛ γ₂)) · u₂ ⟧₀
  I {A} =
   ⟦ close ⌜ t ⌝ (Sub,, γ₂ u₂) ⟧₀
    ≡⟨ ⟦close⟧' ⌜ t ⌝ (Sub,, γ₂ u₂) ⟩
   ⟦ ⌜ t ⌝ ⟧ (【Sub₀】 (Sub,, γ₂ u₂))
    ≡⟨ ≡-refl ⌜ t ⌝ (【≡】-【Sub】-Sub,, γ₂ u₂) ⟩
   ⟦ ⌜ t ⌝ ⟧ (【Sub】 (Subƛ γ₂) (⟨⟩ ‚ ⟦ u₂ ⟧₀))
    ≡＝⟨ ≡-symm (⟦close⟧ ⌜ t ⌝ (Subƛ γ₂) _ _ (【≡】-is-refl‚ _ _ (λ ()) (≡-refl₀ u₂)) (【≡】-【Sub】-Subƛ γ₂ _ (≡-refl₀ u₂))) ⟩
   ⟦ ƛ (close ⌜ t ⌝ (Subƛ γ₂)) · u₂ ⟧₀
    ∎

  Rnorm-γ,,us : Rnorms (γ₁ ‚‚ u₁) (Sub,, γ₂ u₂)
  Rnorm-γ,,us (∈Cxt0 _)   = Rnorm-us
  Rnorm-γ,,us (∈CxtS _ i) = Rnorm-γs i

  IH : Rnorm (B⟦ t ⟧ (γ₁ ‚‚ u₁)) (close ⌜ t ⌝ (Sub,, γ₂ u₂))
  IH = Rnorm-lemma (γ₁ ‚‚ u₁) (Sub,, γ₂ u₂) t Rnorm-γ,,us

Rnorm-lemma γ₁ γ₂ (t · u) Rnorm-γs = IH₁ (B⟦ u ⟧ γ₁) (close ⌜ u ⌝ γ₂) IH₂
 where
  IH₁ : Rnorm (B⟦ t ⟧ γ₁) (close ⌜ t ⌝ γ₂)
  IH₁ = Rnorm-lemma γ₁ γ₂ t Rnorm-γs

  IH₂ : Rnorm (B⟦ u ⟧ γ₁) (close ⌜ u ⌝ γ₂)
  IH₂ = Rnorm-lemma γ₁ γ₂ u Rnorm-γs

dialogue⋆≡dialogue⋆ : dialogue⋆ ≡[ ⌜B⌝ ι ((ι ⇒ ι) ⇒ ι) ⇒ (ι ⇒ ι) ⇒ ι ] dialogue⋆
dialogue⋆≡dialogue⋆ d₁≡d₂ =
 d₁≡d₂ dialogue⋆-η≡dialogue⋆-η dialogue⋆-β≡dialogue⋆-β
 where
  dialogue⋆-η : 〖 η-type ((ι ⇒ ι) ⇒ ι) 〗
  dialogue⋆-η z α = z

  dialogue⋆-η≡dialogue⋆-η : dialogue⋆-η ≡ dialogue⋆-η
  dialogue⋆-η≡dialogue⋆-η z₁≡z₂ α₁≡α₂ = z₁≡z₂

  dialogue⋆-β : 〖 β-type ((ι ⇒ ι) ⇒ ι) 〗
  dialogue⋆-β ϕ x α = ϕ (α x) α

  dialogue⋆-β≡dialogue⋆-β : dialogue⋆-β ≡ dialogue⋆-β
  dialogue⋆-β≡dialogue⋆-β ϕ₁≡ϕ₂ x₁≡x₂ α₁≡α₂ = ϕ₁≡ϕ₂ (α₁≡α₂ x₁≡x₂) α₁≡α₂

Rnorm-lemma₀ : {σ : type} (t : T₀ σ) → Rnorm B⟦ t ⟧₀ ⌜ t ⌝
Rnorm-lemma₀ {σ} t =
 Rnorm-respects-≡ (⟦closeν⟧ ⌜ t ⌝ _ (λ ())) (Rnorm-lemma ⟪⟫ ν t (λ ()))

\end{code}

TODO. Do we want to keep this? It seems a bit pointless to have this as a lemma.

\begin{code}

Rnorm-lemmaι : (t : T₀ ι)
             → dialogue⋆ ⟦ ⌜ t ⌝ ⟧₀ ≡ dialogue⋆ (church-encode B⟦ t ⟧₀)
Rnorm-lemmaι t = dialogue⋆≡dialogue⋆ (Rnorm-lemma₀ t)

\end{code}

Having proved the fundamental theorem of the Rnorm logical relation,
we can derive as a corollary the correctness of `⌜dialogue-tree⌝` as
building an internal dialogue tree for a System T term of type `
(ι ⇒ ι) ⇒ ι`. This is done by reducing to the correctness of the
external `dialogue-tree` function, shown correct by
`dialogue-tree-correct`.

\begin{code}

Rnorm-generic : Rnorm generic ⌜generic⌝
Rnorm-generic = Rnorm-kleisli-lemma {ι} (β η) (⌜β⌝ · ⌜η⌝) βη≡⌜βη⌝
 where
  βη≡⌜βη⌝ : (x : ℕ) → is-dialogue-for (β η x) (⌜β⌝ · ⌜η⌝ · numeral x)
  βη≡⌜βη⌝ x η₁≡η₂ β₁≡β₂ = β₁≡β₂ η₁≡η₂ (⟦numeral⟧₀ x)

dialogue-tree-agreement : (t : T₀ ((ι ⇒ ι) ⇒ ι)) {A : type}
                        → ⟦ ⌜dialogue-tree⌝ t ⟧₀
                           ≡[ ⌜B⌝ ι A ]
                          church-encode (dialogue-tree t)
dialogue-tree-agreement t = Rnorm-lemma₀ t generic ⌜generic⌝ Rnorm-generic

⌜dialogue-tree⌝-correct : (t : T₀ ((ι ⇒ ι) ⇒ ι))
                          (α : Baire)
                        → ⟦ t ⟧₀ α ＝ dialogue⋆ ⟦ ⌜dialogue-tree⌝ t ⟧₀ α
⌜dialogue-tree⌝-correct t α =
 ⟦ t ⟧₀ α                                      ≡⟨ dialogue-tree-correct t α ⟩
 dialogue (dialogue-tree t) α                  ≡⟨ dialogues-agreement (dialogue-tree t) α ⟩
 dialogue⋆ (church-encode (dialogue-tree t)) α ≡⟨ dialogue⋆≡dialogue⋆ I α≡α ⟩
 dialogue⋆ ⟦ ⌜dialogue-tree⌝ t ⟧₀ α            ∎
 where
  I = ≡-symm {⌜B⌝ ι ((ι ⇒ ι) ⇒ ι)} (dialogue-tree-agreement t)

  α≡α : α ≡ α
  α≡α = ap α

\end{code}

TODO. Should this be moved.

\begin{code}

⌜dialogue⌝ : {Γ : Cxt}
           → T (B-context【 Γ 】 ((ι ⇒ ι) ⇒ ι)) (⌜B⌝ ι ((ι ⇒ ι) ⇒ ι))
           → T (B-context【 Γ 】 ((ι ⇒ ι) ⇒ ι)) ((ι ⇒ ι) ⇒ ι)
⌜dialogue⌝ {Γ} t = t · ƛ (ƛ ν₁) · ƛ (ƛ (ƛ (ν₂ · (ν₀ · ν₁) · ν₀)))

\end{code}

Same as ⌜dialogue-tree⌝-correct but using an internal dialogue function.

\begin{code}

⌜dialogue-tree⌝-correct' : (t : T₀ ((ι ⇒ ι) ⇒ ι))
                           (α : Baire)
                         → ⟦ t ⟧₀ α ＝ ⟦ ⌜dialogue⌝ (⌜dialogue-tree⌝ t) ⟧₀ α
⌜dialogue-tree⌝-correct' t α = ⌜dialogue-tree⌝-correct t α

\end{code}
