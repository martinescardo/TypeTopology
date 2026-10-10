# Claude optimisations

This file records every change made by Claude that goes beyond layout and
formatting (whitespace, line breaks, renaming binders to patterns), so that
reviewers can check them separately. Each entry names the file, what was
repeated or redundant, what replaced it, and how the change was checked.

All entries below were checked by running `agda` on the changed file and on
the modules that import it. Proof terms were not changed: each replacement
is definitionally equal to the term it replaces (it unfolds to it).

## HeadExample.lagda

### 1. `eager-nat-id`: shared name for applying the identity on `ℕ` eagerly

* **Repeated term:**
  `pr₁ (eager-function-nat-helper env (lam nat (var 𝟎)) x) (0 , return 0)`
  appeared in the types of `nat-function-lemma`, `γ₁`, `γ₂` (in
  `eager-head-not-constant-time-lemma`), and `γ₄` to `γ₉` (in
  `eager-head-linear-time-big-o`), usually with a 4-line environment
  argument.
* **Replacement:** a top-level definition
  `eager-nat-id : (env : Envᵢ Γ) → (Σ t ꞉ ℕ , Thunk t ℕ) → Σ t ꞉ ℕ , Thunk t ℕ`
  placed just before `nat-function-lemma`, with a short comment. All the
  occurrences above now use it.

### 2. `tail-time`: local name in `eager-head-not-constant-time`

* **Repeated term:** a 7-line expression
  `pr₁ (pr₁ (eager-function-nat-helper ((0 , return (0 ∷ gen-naive-list m)) ∷Eᵢ env) …) (0 , return 0))`,
  written out about 14 times in the proof (once for each use of `C` and of
  `N₀` in the nested `≤-trans` calls).
* **Replacement:** a local definition `tail-time : ℕ → ℕ` in the `where`
  block, now written using `eager-nat-id` (entry 1). Both branches of `γ`
  call it. The implicit arguments `{_} {_} {list}` of `_∷Eᵢ_` were added,
  because the type of the extended environment cannot be inferred once the
  term stands alone.

### 3. `env'` and `rest`: local names in `eager-head-linear-time-big-o`

* **Repeated terms:** inside `γ₀ (succ n) env`, the extended environment
  `(_∷Eᵢ_ {_} {_} {list} (0 , return (0 ∷ 0 ∷ gen-naive-list n)) env)`
  was written out about 12 times, and the thunk
  `pr₁ (eager-function-nat-helper … (list-recᵢ … (gen-naive-list n) …)) (0 , return 0)`
  about 5 times (in `γ₄`, `γ₅`, `γ₉`, and as the argument passed to `γ₈`).
* **Replacement:** two local definitions in the `where` block:
  `env' : Envᵢ (list ∷ Γ)` and `rest : Σ t ꞉ ℕ , Thunk t ℕ`
  (`rest = eager-nat-id env' (list-recᵢ env' (gen-naive-list n) …)`).
  `γ₂` and `γ₄` to `γ₉` use them. `γ₄` and `γ₅` now read
  `succ (pr₁ rest) ≤ succ (2 + 3 * n)` and `pr₁ rest ≤ 2 + 3 * n`, and
  `γ₉` is just `γ₈ rest γ₅`.
* `rest` is not called `tail` because that clashes with `MLTT.Vector`.

### Not changed

* `lam nat (lam nat (var 𝟎))` (the step function of `head`) is repeated
  throughout the file. It is short and it is the term that actually appears
  in the unfolded goals, so it was left in place.
* The `γ₁` and `γ₆` wrappers around `nat-function-lemma` were kept: they fix
  the implicit `env`, which Agda cannot always infer at the use site.

## InsertionSortCorrectness.lagda

The file went from 762 to 528 lines. It typechecks with `agda`, and nothing
else imports it except `TGH/index.lagda`. All the public lemma names that
existed before (`concat-correctness`, `subtract-correctness`,
`insert-correctness`, `sort-correctness`, and so on) are still there with the
same statements, apart from the step names below which now appear inside the
`list-rec` statements (they unfold to the previous terms).

### 1. Named step functions (`concat-step`, `remove-greater-step`, `remove-less-step`, `insert-step`)

* **Repeated terms:** the step functions of the `lrec` in `concat`,
  `remove-greater-than-from-end`, `remove-less-than-from-start` and `sort`
  (for example
  `lam list (lam nat (if subtract ∙ (var 𝟐) ∙ (var 𝟎) then cons (var 𝟎) (var 𝟏) else var 𝟏))`)
  were written out in every lemma statement and in every step of every
  equational proof, often 5 to 10 times per proof.
* **Replacement:** four top-level `Term` definitions, with the definitions of
  `concat`, `remove-*`, `sort` rewritten to use them. These are
  definitionally equal to the old definitions.
* `remove-greater-step` and `remove-less-step` have the context `nat ∷ Γ`,
  which is the most general context their `var 𝟐` allows.

### 2. Unfolding lemmas `remove-less-than-from-start-cons` and `remove-greater-than-from-end-cons`

* **Problem:** `remove-less-than-from-start-env-lemma`,
  `remove-greater-than-from-end-env-lemma`, `remove-*-≤` and `remove-*-<`
  each contained a hand-unfolded equational proof, where the unfolded
  evaluation of `list-rec` (with the extended environments and the whole
  `subtract` call written out) was copied between 3 and 6 times. This was
  about 50 to 100 lines per lemma.
* **Replacement:** a new helper `if-then-else-cong` (congruence for
  `if' _ then' _ else' _`), and two lemmas that state, in terms of
  `(env [ f ]ₑ)`, that `f (x ∷ xs) y` is
  `if' (env [ subtract ]ₑ) y x then' … else' …`. They are proved in
  one expression each, from `subtract-env-lemma` and the `*-env-lemma`.
  The `env-lemma`s, `-≤` and `-<` lemmas now just rewrite with them, using
  the existing `subtract-lemma-I`, `subtract-lemma-II`, `if-then-else-ap`
  and `ite-second-branch`.
* The statements of the `-≤` and `-<` lemmas are unchanged.

### 3. `insert-unfold`

* **Problem:** `insert-lemma`, `insert-correctness` (second case) and
  `insert-env-lemma` each repeated a long chain unfolding `insert` into
  `concat`, `remove-greater-than-from-end` and `remove-less-than-from-start`
  in the extended environment `y ∷E xs ∷E env`.
* **Replacement:** one lemma
  `(env [ insert ]ₑ) xs y ＝ (env [ remove-greater-than-from-end ]ₑ) xs y ++ (y ∷ (env [ remove-less-than-from-start ]ₑ) xs y)`,
  proved once from `concat-correctness` and the two `*-env-lemma`s. The
  three proofs above now use it.

### 4. `sort-env-lemma` and `sort-correctness`

* **Problem:** the unfolded 25-line `insert` step function was repeated four
  times in `sort-env-lemma`, and `list-rec … insert-step` with its extended
  environment was repeated about 10 times in `sort-correctness`.
* **Replacement:** `r₁` and `r₂` (the recursive results) as `where`-bound
  names in `sort-env-lemma`, and `E`/`ins` (the extended environment and the
  call to `insert`) in `sort-correctness`. The proof steps are the same.

### 5. Small local changes

* `ℕ-subtract-lemma-I`: the two inline equational proofs inside the
  arguments of `transport` and `cosubtraction` are now `where`-bound `δ` and
  `ε`, with the same steps.
* Several lemma signatures that took `(xs : List ℕ) → (x y : ℕ)` as separate
  arrows are now `(xs : List ℕ) (x y : ℕ)`; the types are the same.
* `if-then-else-ap`, `ite-second-branch` and `≤-lemma` were moved before the
  lemmas that use them, since they are needed by the new unfolding lemmas.

### 6. Coverage errors fixed (not an optimisation)

As in `HeadExample`, the file had incomplete pattern matches that this
version of Agda rejects. Added absurd clauses to `ite-second-branch`
(`zero ()`), `less-than-implies-neq` (`n zero () _`),
`ℕ-subtract-lemma-II` (`zero m ()`) and its local `γ` (`zero (succ m) ()`).

## LastCorrectness.lagda, LastTimeListValueIndependent.lagda, LastLinearTimeEager.lagda

These three files were reformatted together because the last two import the
first. All three typecheck, and so do `PExamples` and `NP`, which import
them. Line counts: 208 to 166, 757 to 490, 629 to 380.

### LastCorrectness.lagda

* **Named step functions `length'-step` and `last-step`.** The step functions
  of the `lrec` in `length'`, `last` and `last-list` (for example
  `lam list (lam nat (if length' ∙ (var 𝟏) then cons (var 𝟎) nil else (var 𝟏)))`)
  were written out in every lemma statement and proof step, 12 or more times
  in `last-list-env-lemma` and `last-list-correctness`. They are now top-level
  terms and `length'`, `last`, `last-list` are defined using them (definitionally
  equal to the old definitions).
* **`last-list-env-lemma`.** The 25-line hand-unfolded equational proof is now
  `ap₂ (λ b z → if' b then' [ x ] else' z) γ (last-list-env-lemma l)`, with
  `γ` a three-line chain using `length'-env-lemma`. The old proof used
  function extensionality (`fe`) to change the environment of `length'`; the
  new one does not need it, since the change is only needed at one argument.
* **`last-list-correctness`.** The chain of seven `refl` steps that unfolded
  the evaluation of `last-list` (about 45 lines) is replaced by one `refl`
  step to `if' ((x ∷E r ∷E (x ∷ l) ∷E env) [ length' ]ₑ) r then' [ x ] else' r`,
  where `r` is a `where`-bound name for the recursive call. This is the only
  step that unfolds the semantics. The remaining steps are as before, except
  that `ap (λ z → …) (fe length'-correctness)` is now
  `ap (λ z → …) (length'-correctness r)`, again avoiding `fe`.

### LastTimeListValueIndependent.lagda

New top-level names (explained in a comment in the file):

* `length'-step-applied env l y`: the term
  `pr₁ (eager-function-nat-helper env (lam nat (suc (var 𝟏))) l) (0 , return y)`,
  which appeared in 14 places.
* `last-step-applied env l x`: the same for the step of `last-list`. This one
  was written out as a 9-line term about 20 times.
* `cons-branch x`, `else-branch l`: the two thunks passed to `thunk-if` in
  `recursive-call` (`3 , (√ (√ (√ return (x ∷ []))))` and `1 , (√ return l)`).
* `cond-time b` for `if' b then' 3 else' 1`.
* `length-call-env l x env` for the environment
  `(0 , return l) ∷Eᵢ (0 , return x) ∷Eᵢ (0 , return l) ∷Eᵢ env`.
* `recursive-call-time env r x` and `head-comp-time env L`: the times of
  `recursive-call` and `head-comp`, which are used again in
  `LastLinearTimeEager`.

Use of the names:

* The statements and proofs of `nat-helper-env-lemma`,
  `length'-comp-same-env`, `recursive-call-comp-same-env`,
  `eager-function-list-helper-env-lemma`, `last-list-same-env`,
  `length'-comp-lemma'`, `length'-comp-lemma`,
  `length'-list-value-independent` and `if-condition-lemma` were rewritten
  with them. The proofs have the same steps.
* **`recursive-call-list-value-independent`**: the 100-line chain, which
  repeated the unfolded `list-recᵢ` and `thunk-if` terms in every step, is now
  a six-step chain. Its steps are the same as before, in the same order.
* **`last-list-list-value-independent`**: the 75-line chain is now nine
  steps, with `env₁`, `env₂`, `r₁`, `r₂`, `r₁'`, `r₂'` as `where`-bound names.
* **`last-list-value-independent`**: the 50-line chain is now a ten-step chain
  using `E₁`, `E₂`, `semantics` and `head-comp-time`. The last step of the old
  chain, `(head-time-value-env-independent-eager …) ⁻¹`, was a conversion
  between two environments that are already equal at that point, so it is not
  needed and was dropped.
* `recursive-call-length-lemma` states its type with `last-step` instead of the
  fully unfolded step function.
* `thunk-if-lemma'` uses a pattern binder for `t`, as in the other files.
* Coverage errors (see `HeadExample`) fixed by absurd clauses in
  `last-list-length-lemma`, `length'-comp-lemma`,
  `length'-list-value-independent`, `list-rec-length-lemma` and
  `last-list-list-value-independent`. These were fixed in an earlier step.

### LastLinearTimeEager.lagda

* **`length'-linear-time`:** the term `length'-step-applied env₀ …` was written
  out 8 times in `γ₁` to `γ₈`. It is now `t₀`, `t₁` (with `env₀`, `env₁`) in
  the `where` block. Lemmas `γ₄` and `γ₅`, which were local and general,
  are now the top-level `length'-step-applied-time` and
  `length'-step-applied-time-succ`.
* **`recursive-call-linear-time`:** `len` (the recursive call of `length'`)
  and `cond` (the `thunk-if`) name the two terms that were written out
  about 20 times in `γ₁` to `γ₆`. The helper `fₗ`, which re-stated the
  linear-time bound of `length'` at one argument, was inlined into `γ₂`.
* **`last-list-linear-time`:** `E_y`, `E_x`, `r_y`, `r_x` name the two
  environments and the two recursive results, and the times use
  `last-step-applied` and `recursive-call-time`. The statements `γ₁` to
  `γ₁₀` went from 5 to 10 lines each to 1 to 3 lines each.
* **`last-linear-time`:** `E`, `L`, `ht`, `hct` name the environment, the
  result of `last-list`, the time of `head` and the time of `head-comp`.
  The statements `γ₁` to `γ₁₄` are now one or two lines each.
* The `Pi A (λ l → Pi B (λ env → …))` types of `f` and `f'` are now written
  with the `Π l ꞉ List ℕ , Π env ꞉ Envᵢ Γ , …` notation used in
  `ComplexityDefinitionsResults`.
* `last-comp` is defined using `last-step`.

## P.lagda, NP.lagda, PExamples.lagda, Language.lagda, PrototypeLanguage.lagda and small files

All of `TGH/index.lagda` typechecks after these changes. `P.lagda` went from
1016 to 648 lines. `NP.lagda` went from 168 to 170 and `PExamples.lagda`
from 98 to 105, and `Language.lagda` from 619 to 724 because every long
signature is now split one argument per line.

### P.lagda

* **`P-solver Γ decision`:** the type
  `Σ program ꞉ Term (list ∷ Γ) nat , ((env : Env Γ) → to-decision-solver env program ∼ decision) × general-list-polytime (inl refl) program`
  was written out in full as the type of `open-d`, `open-d₁`, `open-d₂`,
  `P-instance` (in `NP`) and in `_∈P`. It is now a definition, and `_∈P` is
  `Π n ꞉ ℕ , Π Γ ꞉ Ctx n , P-solver Γ decision`.
* **`timing₁`, `timing₂`, and the types of `timing'`:** these were the unfolded
  8-line `Σ … Pi … is-polytime …` type, written about ten times. They are now
  `general-list-polytime (inl refl) program₁` and so on, which they unfold to.
  The same goes for the 12-line result type `new-f`, which is now a `Π … , …`
  type of 3 lines.
* **`not-program`, `or-program`, `and-program`:** the three programs built in
  `P-closure₁`, `P-closure₂`, `P-closure₃` were written out in the statements
  of `correctness`, `timing'` and `new-f`, about 8 times each.
* **`env'`, `r₁`, `r₂`, `le₁`, `le₂`:** the term
  `((0 , return xs) ∷Eᵢ (0 , return xs) ∷Eᵢ env) [ pr₁ (d₁∈P (succ n) (list ∷ Γ)) ]ᵢ eager`
  (3 lines) was written out about 40 times in `P-closure₂` and
  `P-closure₃`. It is now `r₁`/`r₂`, defined in the `where` block with `env'`.
  The two proofs `N₀ ≤ length xs` built from `le`, repeated about 4 times
  each, are now `le₁` and `le₂`. `E` is the extended environment in the
  `correctness` proofs.
* **Arithmetic lemmas (new, top-level):** `one-≤-not-zero`, `one-≤-power`,
  `power-≤-left`, `power-≤-right`, `power-sum-bound`, `parallel-bound` and
  `shift-bound`. `P-closure₂` and `P-closure₃` each contained the same
  proofs of `V`, `VI`, `III`, `IV` (about 40 lines, copy-pasted with primes
  in `P-closure₃`) and the proof that `1 ≤ L ^ m`. The `shift-bound` lemma
  is the first case of `γ` in `P-closure₃`. The proofs are the same as before.
* In `P-closure₃`, the `I'`, `II'`, `III'`, `IV'`, `V'`, `VI'` duplicates of
  `P-closure₂`'s helpers are gone (replaced by the lemmas above).
  `II` and `III` in `P-closure₃` (about `max`) are specific to that proof
  and are kept.

### NP.lagda

* `P-instance` has type `P-solver (list ∷ Γ) decision`.
* In the proof of `P⊆NP`, the two terms
  `pr₁ (pr₁ (pr₁ (env [ lam list (lam list program) ]ᵢ eager) (0 , return c)) (0 , return l))`
  and
  `pr₁ (pr₁ (((0 , return c) ∷Eᵢ env) [ lam list program ]ᵢ eager) (0 , return l))`
  were written out in `I`, `II` and `f`. They are now the local
  functions `verifier-time` and `solver-time`.

### Language.lagda

* The proof in the four `lam` cases of `equivalent-semantics` (the same
  six lines with `lazy`, `nat`, `list` and `⇒`) is now
  `equivalent-lam-lemma`, and each case is `fe (equivalent-lam-lemma env term s)`.
  Termination is checked since `equivalent-lam-lemma` is in the same mutual
  block and `term` is structurally smaller in each call.
* Everything else in this file is layout only.

### PrototypeLanguage.lagda

Reduced from 1566 to 781 lines (the first request was to shorten it, following
Todd's comment at the top of the file). Coverage errors are also fixed by
absurd clauses (see `HeadExample`) in `if-then-else-equality`, the local `γ`
of `equivalent-semantics`, and the `γ`s in `double-time`, `nat-rec<2` and
`is-even-time`.

* **`NatThunk`:** `Σ t ꞉ ℕ , Thunk t ℕ` was written out in about 30
  signatures. `⟦ nat ⟧ᵢ`, `get-time`, `get-thunk`, `thunk-if`, `nat-recᵢ`,
  `rec-builder`, `inc-function`, `if-then-else-equality`, `equivalent-nrec`
  and others now use the synonym `NatThunk`. Also, the type
  `Σ f ꞉ (⟦ σ ⟧ᵢ → ⟦ τ ⟧ᵢ) , value-time-independent f` in `get-function`,
  `get-value-time-independent`, `change-function` and
  `application-equality` is written `⟦ σ ⇒ τ ⟧ᵢ`, which it is by definition.
* **`double-step` and `even-step`:** the step terms
  `lam nat (suc (suc (var 𝟎)))` and
  `lam nat (if var 𝟎 then suc zero else zero)` were written out in every
  statement and proof about `double` and `is-even` (about 60 times in
  total). `double` and `is-even` are defined using them.
* **`double-rec x n` and `even-rec x n`:** the term
  `nat-recᵢ {1} {nat ∷ []} ((0 , return x) ∷Eᵢ []) n zero (…)` (5 lines)
  was written out about 25 times in `double-time` and `is-even-time`.
* **`even-if r`:** the term
  `thunk-if r (2 , (√ (√ return 1))) (1 , (√ return 0))` was written out about
  35 times (up to three nested). `γ₃` of `is-even-time` went from about 140
  to 20 lines, and `γ₆` to `γ₁₁` and `goal` each from 15 to 40 lines to 2
  or 3 lines.
* **Layout:** short signatures are on one line (Todd's comment), and the
  `γ₀` chain in `double-correctness` and `γ₇` in `double-time` are
  shortened by merging the `γ` steps. The `succ^` helper uses one-space
  indentation.

### Other files

* `BigO.lagda`, `Strategy.lagda`: trailing whitespace removed.
* `Thunk.lagda`: double space after `_>>=_ :` removed.
* `PExamples.lagda`: equational proofs and long definitions re-laid out.
* `ComplexityDefinitionsResults.lagda` and `index.lagda` already follow
  the style and were not changed.

## AFP2024/

These files come from the AFP lecture notes (see the header of each file),
and were adapted. They keep that attribution header.

* `iso-utils.lagda` (162 to 152 lines): the five isomorphisms `id-iso`,
  `_∘ᵢ_`, `∔-unit-left-iso`, `∔-pair-iso`, `∔-assoc-iso`, `∔-left-swap-iso`
  each ended with the same five lines
  `f-is-bijection : is-bijection f; f-is-bijection = record { inverse = g ; η = gf ; ε = fg }`
  and the same `record { bijection = f ; bijectivity = … }`. They now use
  one new function `mk-iso f g gf fg`. `id-iso` is `mk-iso id id …` and
  the proofs `gf`, `fg` are unchanged. Reduces by 10 lines only because
  the other lines (the clauses of `f`, `g`, `gf`, `fg`) are needed.
* `InsertionSort.lagda`: `Trichotomy x y` is a new definition for
  `(x < y) ∔ (x ＝ y) ∔ (y < x)`, which was written out 7 times. The other
  changes are layout, plus `Set` replaced by `𝓤₀ ̇` in `data Sorted`, and the
  universe dot followed by a space before closing brackets (`𝓤₀ ̇ }`) as in
  CONTRIBUTING.md.
* `isomorphisms.lagda`: whitespace only.
