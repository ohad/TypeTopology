Martin Escardo, 2014, 21 March 2018, November-December 2019.

Fin n is a set with n elements. We investigate some of its basic
properties.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT

module Fin  where

Fin : ℕ → 𝓤₀ ̇
Fin 0        = 𝟘
Fin (succ n) = Fin n + 𝟙

\end{code}

We have zero and successor for finite sets, with the following types:

\begin{code}

𝟎 : {n : ℕ} → Fin (succ n)
𝟎 = inr *

suc : {n : ℕ} → Fin n → Fin (succ n)
suc = inl

Fin-induction : (P : (n : ℕ) → Fin n → 𝓤 ̇ )
              → ((n : ℕ) → P (succ n) 𝟎)
              → ((n : ℕ) (i : Fin n) → P n i → P (succ n) (suc i))
              →  (n : ℕ) (i : Fin n) → P n i
Fin-induction P β σ 0        i       = 𝟘-elim i
Fin-induction P β σ (succ n) (inr *) = β n
Fin-induction P β σ (succ n) (inl i) = σ n i (Fin-induction P β σ n i)

\end{code}

The left cancellability of Fin uses the non-trivial construction
+𝟙-cancellable defined in the module PlusOneLC.lagda.

\begin{code}

open import PlusOneLC
open import UF-Equiv

Fin-lc : (m n : ℕ) → Fin m ≃ Fin n → m ≡ n
Fin-lc 0           0       p = refl
Fin-lc (succ m)    0       p = 𝟘-elim (⌜ p ⌝ 𝟎)
Fin-lc 0          (succ n) p = 𝟘-elim (⌜ ≃-sym p ⌝ 𝟎)
Fin-lc (succ m)   (succ n) p = ap succ r
 where
  IH : Fin m ≃ Fin n → m ≡ n
  IH = Fin-lc m n
  remark : Fin m + 𝟙 ≃ Fin n + 𝟙
  remark = p
  q : Fin m ≃ Fin n
  q = +𝟙-cancellable p
  r : m ≡ n
  r = IH q

open import DiscreteAndSeparated

Fin-is-discrete : (n : ℕ) → is-discrete (Fin n)
Fin-is-discrete 0        = 𝟘-is-discrete
Fin-is-discrete (succ n) = +discrete (Fin-is-discrete n) 𝟙-is-discrete

open import UF-Subsingletons
open import UF-Miscelanea

Fin-is-set : (n : ℕ) → is-set (Fin n)
Fin-is-set n = discrete-types-are-sets (Fin-is-discrete n)

\end{code}

Added November 2019.

\begin{code}

open import CompactTypes

Fin-Compact : (n : ℕ) → Compact (Fin n) 𝓤
Fin-Compact 0        = 𝟘-Compact
Fin-Compact (succ n) = +-Compact (Fin-Compact n) 𝟙-Compact

\end{code}

Recall that X ↣ Y is the type of left cancellable maps from X to Y.

\begin{code}

open import Plus-Properties
open import Swap
open import UF-LeftCancellable

+𝟙-cancel-lemma : {X Y : 𝓤 ̇}
                → (𝒇 : X + 𝟙 ↣ Y + 𝟙)
                → ⌈ 𝒇 ⌉ (inr *) ≡ inr *
                → X ↣ Y
+𝟙-cancel-lemma {𝓤} {X} {Y} (f , l) p = g , m
 where
  g : X → Y
  g x = pr₁ (inl-preservation {𝓤} {𝓤} {𝓤} {𝓤} f p l x)

  a : (x : X) → f (inl x) ≡ inl (g x)
  a x = pr₂ (inl-preservation f p l x)

  m : left-cancellable g
  m {x} {x'} p = q
   where
    r = f (inl x)  ≡⟨ a x      ⟩
        inl (g x)  ≡⟨ ap inl p ⟩
        inl (g x') ≡⟨ (a x')⁻¹ ⟩
        f (inl x') ∎
    q : x ≡ x'
    q = inl-lc (l r)

+𝟙-cancel : {X Y : 𝓤 ̇}
          → is-discrete Y
          → X + 𝟙 ↣ Y + 𝟙
          → X ↣ Y
+𝟙-cancel {𝓤} {X} {Y} i (f , e) = a
 where
  h : Y + 𝟙 → Y + 𝟙
  h = swap (f (inr *)) (inr *) (+discrete i 𝟙-is-discrete (f (inr *))) new-point-is-isolated

  d : left-cancellable h
  d = equivs-are-lc h (swap-is-equiv (f (inr *)) (inr *)
                        (+discrete i 𝟙-is-discrete (f (inr *))) new-point-is-isolated)

  f' : X + 𝟙 → Y + 𝟙
  f' = h ∘ f

  e' : left-cancellable f'
  e' = left-cancellable-closed-under-∘ f h e d

  p : f' (inr *) ≡ inr *
  p = swap-equation₀ (f (inr *)) (inr *)
       (+discrete i 𝟙-is-discrete (f (inr *))) new-point-is-isolated

  a : X ↣ Y
  a = +𝟙-cancel-lemma (f' , e') p

open import NaturalsOrder
open import UF-EquivalenceExamples

↣-gives-≤ : (m n : ℕ) → (Fin m ↣ Fin n) → m ≤ n
↣-gives-≤ 0        n        e       = zero-minimal n
↣-gives-≤ (succ m) 0        (f , i) = 𝟘-elim (f 𝟎)
↣-gives-≤ (succ m) (succ n) e       = ↣-gives-≤ m n (+𝟙-cancel (Fin-is-discrete n) e)


canonical-Fin-inclusion : (m n : ℕ) → m ≤ n → (Fin m → Fin n)
canonical-Fin-inclusion 0        n        l = unique-from-𝟘
canonical-Fin-inclusion (succ m) 0        l = 𝟘-elim l
canonical-Fin-inclusion (succ m) (succ n) l = +functor IH unique-to-𝟙
 where
  IH : Fin m → Fin n
  IH = canonical-Fin-inclusion m n l

canonical-Fin-inclusion-lc : (m n : ℕ) (l : m ≤ n)
                           → left-cancellable (canonical-Fin-inclusion m n l)
canonical-Fin-inclusion-lc 0        n        l {x} {y}         p = 𝟘-elim x
canonical-Fin-inclusion-lc (succ m) 0        l {x} {y}         p = 𝟘-elim l
canonical-Fin-inclusion-lc (succ m) (succ n) l {inl x} {inl y} p = γ
 where
  IH : canonical-Fin-inclusion m n l x ≡ canonical-Fin-inclusion m n l y → x ≡ y
  IH = canonical-Fin-inclusion-lc m n l
  γ : inl x ≡ inl y
  γ = ap inl (IH (inl-lc p))
canonical-Fin-inclusion-lc (succ m) (succ n) l {inr *} {inr *} p = refl

≤-gives-↣ : (m n : ℕ) → m ≤ n → (Fin m ↣ Fin n)
≤-gives-↣ m n l = canonical-Fin-inclusion m n l , canonical-Fin-inclusion-lc m n l

\end{code}

An equivalent construction:

\begin{code}
≤-gives-↣' : (m n : ℕ) → m ≤ n → (Fin m ↣ Fin n)
≤-gives-↣' 0        n        l = unique-from-𝟘 , (λ {x} {x'} p → 𝟘-elim x)
≤-gives-↣' (succ m) 0        l = 𝟘-elim l
≤-gives-↣' (succ m) (succ n) l = g , j
 where
  IH : Fin m ↣ Fin n
  IH = ≤-gives-↣' m n l
  f : Fin m → Fin n
  f = pr₁ IH
  i : left-cancellable f
  i = pr₂ IH
  g : Fin (succ m) → Fin (succ n)
  g = +functor f unique-to-𝟙
  j : left-cancellable g
  j {inl x} {inl x'} p = ap inl (i (inl-lc p))
  j {inl x} {inr *}  p = 𝟘-elim (+disjoint  p)
  j {inr *} {inl y}  p = 𝟘-elim (+disjoint' p)
  j {inr *} {inr *}  p = refl

\end{code}

Added 9th December 2019. A version of the pigeonhole principle.

\begin{code}

pigeonhole : (m n : ℕ) (f : Fin m → Fin n)
           → m > n → Σ \(i : Fin m) → Σ \(j : Fin m) → (i ≢ j) × (f i ≡ f j)
pigeonhole m n f g = γ w
 where
  a : ¬ Σ (\(f : Fin m → Fin n) → left-cancellable f)
  a = contrapositive (↣-gives-≤ m n) (less-not-bigger-or-equal n m g)

  b : ¬ left-cancellable f
  b l = a (f , l)

  c : ¬((i j : Fin m) → f i ≡ f j → i ≡ j)
  c φ = b (λ {i} {j} → φ i j)

  u : (i j : Fin m) → decidable ((i ≢ j) × (f i ≡ f j))
  u i j = ×-preserves-decidability
           (¬-preserves-decidability (Fin-is-discrete m i j))
           (Fin-is-discrete n (f i) (f j))

  v : (i : Fin m) → decidable (Σ \(j : Fin m) → (i ≢ j) × (f i ≡ f j))
  v i = Fin-Compact m _ (u i)

  w : decidable (Σ \(i : Fin m) → Σ \(j : Fin m) → (i ≢ j) × (f i ≡ f j))
  w = Fin-Compact m _ v

  γ : decidable (Σ \(i : Fin m) → Σ \(j : Fin m) → (i ≢ j) × (f i ≡ f j))
    → Σ \(i : Fin m) → Σ \(j : Fin m) → (i ≢ j) × (f i ≡ f j)
  γ (inl σ) = σ
  γ (inr ψ) = 𝟘-elim (c δ)
   where
    ε : (i j : Fin m) → f i ≡ f j → ¬(i ≢ j)
    ε i j φ  q = ψ (i , j , q , φ)
    δ : (i j : Fin m) → f i ≡ f j → i ≡ j
    δ i j φ = ¬¬-elim (Fin-is-discrete m i j) (ε i j φ)

\end{code}

Added 2nd December 2019. An isomorphic copy of Fin n:

\begin{code}

Fin' : ℕ → 𝓤₀ ̇
Fin' n = Σ \(k : ℕ) → k < n

𝟎' : {n : ℕ} → Fin' (succ n)
𝟎' = 0 , *

suc' : {n : ℕ} → Fin' n → Fin' (succ n)
suc' (k , l) = succ k , l

Fin-unprime : (n : ℕ) → Fin' n → Fin n
Fin-unprime 0        (k , l)      = 𝟘-elim l
Fin-unprime (succ n) (0 , l)      = 𝟎
Fin-unprime (succ n) (succ k , l) = suc (Fin-unprime n (k , l))

Fin-prime : (n : ℕ) → Fin n → Fin' n
Fin-prime 0        i       = 𝟘-elim i
Fin-prime (succ n) (inl i) = suc' (Fin-prime n i)
Fin-prime (succ n) (inr *) = 𝟎'

ηFin : (n : ℕ) → Fin-prime n ∘ Fin-unprime n ∼ id
ηFin 0        (k , l)      = 𝟘-elim l
ηFin (succ n) (0 , *)      = refl
ηFin (succ n) (succ k , l) = ap suc' (ηFin n (k , l))

εFin : (n : ℕ) → Fin-unprime n ∘ Fin-prime n ∼ id
εFin 0        i       = 𝟘-elim i
εFin (succ n) (inl i) = ap suc (εFin n i)
εFin (succ n) (inr *) = refl

≃-Fin : (n : ℕ) → Fin n ≃ Fin' n
≃-Fin n = qinveq (Fin-prime n) (Fin-unprime n , εFin n , ηFin n)

\end{code}

Added 8th December 2019.

The following is structure rather than property. It amounts to the
type of finite linear orders on X.

\begin{code}

Finite : 𝓤 ̇ → 𝓤 ̇
Finite X = Σ \(n : ℕ) → X ≃ Fin n

\end{code}

Exercise: If X ≃ Fin n, the type Finite X has n! elements.

Hence one considers the following notion of finiteness, which is
property rather than structure:

\begin{code}

open import UF-PropTrunc

module finiteness (pt : propositional-truncations-exist) where

 open PropositionalTruncation pt public

 is-finite : 𝓤 ̇ → 𝓤 ̇
 is-finite X = Σ \(n : ℕ) → ∥ X ≃ Fin n ∥

 cardinality : (X : 𝓤 ̇ ) → is-finite X → ℕ
 cardinality X = pr₁

 cardinality-≃ : (X : 𝓤 ̇ ) (i : is-finite X) → ∥ X ≃ Fin (cardinality X i) ∥
 cardinality-≃ X = pr₂

 being-finite-is-a-prop : (X : 𝓤 ̇ ) → is-prop (is-finite X)
 being-finite-is-a-prop X (m , d) (n , e) = γ
  where
   a : (m n : ℕ) → X ≃ Fin m → X ≃ Fin n → m ≡ n
   a m n d e = Fin-lc m n (≃-sym d ● e)
   b : (m n : ℕ) → ∥ X ≃ Fin m ∥ → ∥ X ≃ Fin n ∥ → m ≡ n
   b m n = ∥∥-rec₂ ℕ-is-set (a m n)
   γ : m , d ≡ n , e
   γ = to-Σ-≡ (b m n d e , ∥∥-is-a-prop _ _)

\end{code}

Equivalently, we can define finiteness as follows:

\begin{code}

 is-finite' : 𝓤 ̇ → 𝓤 ̇
 is-finite' X = ∃ \(n : ℕ) → X ≃ Fin n

 being-finite'-is-a-prop : (X : 𝓤 ̇ ) → is-prop (is-finite' X)
 being-finite'-is-a-prop X = ∥∥-is-a-prop

 finite-unprime : (X : 𝓤 ̇ ) → is-finite' X → is-finite X
 finite-unprime X = ∥∥-rec (being-finite-is-a-prop X) γ
  where
   γ : (Σ \(n : ℕ) → X ≃ Fin n) → Σ \(n : ℕ) → ∥ X ≃ Fin n ∥
   γ (n , e) = n , ∣ e ∣

 finite-prime : (X : 𝓤 ̇ ) → is-finite X → is-finite' X
 finite-prime X (n , s) = ∥∥-rec ∥∥-is-a-prop (λ e → ∣ n , e ∣) s

 module _ (fe : FunExt) where

  open CompactTypesPT pt

  finite-∥Compact∥ : {X : 𝓤 ̇ } → is-finite X → ∥ Compact X 𝓥 ∥
  finite-∥Compact∥ {𝓤} {𝓥} {X} (n , α) =
   ∥∥-functor (λ (e : X ≃ Fin n) → Compact-closed-under-≃ (≃-sym e) (Fin-Compact n)) α

  finite-∃-compact : {X : 𝓤 ̇ } → is-finite X → ∃-Compact X 𝓥
  finite-∃-compact {𝓤} {X} i = ∥Compact∥-gives-∃-Compact fe (finite-∥Compact∥ i)

\end{code}
