Negation (and emptiness).

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module Negation where

open import Universes
open import Empty
open import Id
open import Pi
open import Plus
open import Sigma

private
 _⇔_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
 A ⇔ B = (A → B) × (B → A)

¬_ : 𝓤 ̇ → 𝓤 ̇
¬ A = A → 𝟘 {𝓤₀}
_≢_ : {X : 𝓤 ̇ } → (x y : X) → 𝓤 ̇
x ≢ y = ¬ (x ≡ y)

≢-sym : {X : 𝓤 ̇ } → {x y : X} → x ≢ y → y ≢ x
≢-sym u r = u (r ⁻¹)

is-empty : 𝓤 ̇ → 𝓤 ̇
is-empty = ¬_

¬¬_ : 𝓤 ̇ → 𝓤 ̇
¬¬ A = ¬ (¬ A)

¬¬¬_ : 𝓤 ̇ → 𝓤 ̇
¬¬¬ A = ¬ (¬¬ A)

is-nonempty : 𝓤 ̇ → 𝓤 ̇
is-nonempty = ¬¬_

dual : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (R : 𝓦 ̇ ) → (X → Y) → (Y → R) → (X → R)
dual R f p = p ∘ f

contrapositive : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → (A → B) → ¬ B → ¬ A
contrapositive = dual _

double-contrapositive : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → (A → B) → ¬¬ A → ¬¬ B
double-contrapositive = contrapositive ∘ contrapositive

¬¬-functor : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → (A → B) → ¬¬ A → ¬¬ B
¬¬-functor = double-contrapositive

¬¬-kleisli : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → (A → ¬¬ B) → ¬¬ A → ¬¬ B
¬¬-kleisli f ϕ h = ϕ (λ a → f a h)

decidable : 𝓤 ̇ → 𝓤 ̇
decidable A = A + ¬ A

map-decidable : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → (A → B) → (B → A) → decidable A → decidable B
map-decidable f g (inl x) = inl (f x)
map-decidable f g (inr h) = inr (λ y → h (g y))

map-decidable-corollary : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → (A ⇔ B) → (decidable A ⇔ decidable B)
map-decidable-corollary (f , g) = map-decidable f g , map-decidable g f

map-decidable' : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → (A → ¬ B) → (¬ A → B) → decidable A → decidable B
map-decidable' f g (inl x) = inr (f x)
map-decidable' f g (inr h) = inl (g h)

double-negation-intro : {A : 𝓤 ̇ } → A → ¬¬ A
double-negation-intro x u = u x

three-negations-imply-one : {A : 𝓤 ̇ } → ¬¬¬ A → ¬ A
three-negations-imply-one = contrapositive double-negation-intro

dne' : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → (A → B) → (¬¬ B → B) → ¬¬ A → B
dne' f h ϕ = h (λ g → ϕ (λ a → g (f a)))

dne : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → (A → ¬ B) → ¬¬ A → ¬ B
dne f ϕ b = ϕ (λ a → f a b)

double-negation-unshift : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } → ¬¬ ((x : X) → A x) → (x : X) → ¬¬ (A x)
double-negation-unshift f x g = f (λ h → g (h x))

dnu : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → ¬¬ (A × B) → ¬¬ A × ¬¬ B
dnu φ = (¬¬-functor pr₁ φ) , (¬¬-functor pr₂ φ)

und : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → ¬¬ A × ¬¬ B → ¬¬ (A × B)
und (φ , γ) w = γ (λ y → φ (λ x → w (x , y)))

¬¬-stable : 𝓤 ̇ → 𝓤 ̇
¬¬-stable A = ¬¬ A → A

¬-is-¬¬-stable : {A : 𝓤 ̇ } → ¬¬-stable (¬ A)
¬-is-¬¬-stable = three-negations-imply-one

Π-is-¬¬-stable : {A : 𝓤 ̇ } {B : A → 𝓥 ̇ }
               → ((a : A) → ¬¬-stable (B a))
               → ¬¬-stable (Π B)
Π-is-¬¬-stable f ϕ a = f a (λ v → ϕ (λ g → v (g a)))

→-is-¬¬-stable : {A : 𝓤 ̇ } {B : 𝓥 ̇ }
               → ¬¬-stable B
               → ¬¬-stable (A → B)
→-is-¬¬-stable f = Π-is-¬¬-stable (λ _ → f)

×-is-¬¬-stable : {A : 𝓤 ̇ } {B : 𝓥 ̇ }
               → ¬¬-stable A
               → ¬¬-stable B
               → ¬¬-stable (A × B)
×-is-¬¬-stable f g ϕ = f (λ v → ϕ (λ (a , b) → v a)) ,
                       g (λ v → ϕ (λ (a , b) → v b))

Double-negation-of-implication← : {A : 𝓤 ̇ } {B : 𝓥 ̇ }
                                  {R : 𝓦 ̇ } {S : 𝓣 ̇ } {T : 𝓣' ̇ }
                                → (((A → B) → T) → S)
                                → (((A → S) → R) × (B → T)) → R
Double-negation-of-implication← f g = pr₁ g (λ a → f (λ h → pr₂ g (h a)))

Double-negation-of-implication→ : {A : 𝓤 ̇ } {B : 𝓥 ̇ }
                                  (R : 𝓦 ̇ ) {S : 𝓣 ̇ } {T : 𝓣' ̇ } {U : 𝓣' ̇ }
                                → (S → B)
                                → ((((A → S) → T) × (B → T)) → U)
                                → ((A → B) → T) → U
Double-negation-of-implication→ R k f g = f ((λ h → g (λ a → k (h a))) ,
                                             (λ b → g (λ a → b)))

double-negation-of-implication← : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → ¬¬ (A → B) → ¬ (¬¬ A × ¬ B)
double-negation-of-implication← = Double-negation-of-implication←

double-negation-of-implication→ : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → ¬ (¬¬ A × ¬ B) → ¬¬ (A → B)
double-negation-of-implication→ f g = Double-negation-of-implication→ (𝟘 {𝓤₀}) 𝟘-elim f g

not-Σ-implies-Π-not : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
                    → ¬ (Σ x ꞉ X , A x)
                    → (x : X) → ¬ (A x)
not-Σ-implies-Π-not = curry

Π-not-implies-not-Σ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
                    → ((x : X) → ¬ (A x))
                    → ¬ (Σ x ꞉ X , A x)
Π-not-implies-not-Σ = uncurry

not-Π-implies-not-not-Σ' : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
                         → ¬ ((x : X) → ¬¬ (A x))
                         → ¬¬ (Σ x ꞉ X , ¬ (A x))
not-Π-implies-not-not-Σ' = contrapositive not-Σ-implies-Π-not

not-Π-implies-not-not-Σ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
                        → ((x : X) → ¬¬ (A x) → A x)
                        → ¬ ((x : X) → A x)
                        → ¬¬ (Σ x ꞉ X , ¬ (A x))
not-Π-implies-not-not-Σ f g h = g (λ x → f x (λ u → h (x , u)))

\end{code}

Notation to try to make proofs readable:

\begin{code}

contradiction : 𝓤₀ ̇
contradiction = 𝟘

have_which-is-impossible-by_ : {A : 𝓤 ̇ } {B : 𝓦 ̇ }
                             → A → (A → 𝟘 {𝓤₀}) → B
have a which-is-impossible-by ν = 𝟘-elim (ν a)


have_which-contradicts_ : {A : 𝓤 ̇ } {B : 𝓦 ̇ }
                        → (A → 𝟘 {𝓤₀}) → A → B
have ν which-contradicts a = 𝟘-elim (ν a)

\end{code}

Fixities:

\begin{code}

infix  50 ¬_
infix  50 ¬¬_
infix  50 ¬¬¬_
infix  0 _≢_

\end{code}
