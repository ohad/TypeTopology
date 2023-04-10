Andrew Sneap and Ohad Kammar

Additional properties from Univalent Foundations, that ought to
migrate somewhere.

\begin{code}
{-# OPTIONS --without-K --exact-split --no-sized-types --no-guardedness --auto-inline --lossy-unification --allow-unsolved-metas #-} --safe

-- TODO: remove unnecessary dependencies

open import MLTT.Spartan renaming (_+_ to _∔_)

open import Notation.CanonicalMap
open import Notation.Order
open import UF.PropTrunc
open import MLTT.Sigma
open import Notation.General

open import UF.Subsingletons
open import UF.FunExt
open import UF.Equiv
open import UF.Powerset
open import UF.UniverseEmbedding

-- ought to not be needed eventually
open import UF.Univalence

open import Rationals.Type
open import Rationals.Order
open import Integers.Type
open import Integers.Order

open import Groups.Type
open import Groups.GroupActions
open import Groups.Subgroups

open import MLTT.Id

module DedekindReals.Symmetry.UF where

data _≈_ {X : 𝓤 ̇} (x : X) : {Y : 𝓤 ̇} → (y : Y) → 𝓤 ⁺ ̇
    where
    NB:_since_and_ : forall {Y} (y : Y) →
      (prf : X ＝ Y) → transport id prf x ＝ y → x ≈ y

pr₁-eq : forall {X : 𝓤 ̇} {x₁ x₂}
  {Y : X → 𝓥 ̇} {y₁ : Y x₁} {y₂ : Y x₂} →
  (x₁ , y₁) ＝ (x₂ , y₂) → x₁ ＝ x₂
pr₁-eq = ap pr₁

pr₂-eq : forall {X : 𝓤 ̇} {x₁ x₂}
  {Y : X → 𝓥 ̇} {y₁ : Y x₁} {y₂ : Y x₂} →
  (x₁ , y₁) ＝ (x₂ , y₂) → y₁ ≈ y₂
pr₂-eq {Y = Y} {y₁} {.y₁} refl = NB: y₁ since refl and refl

hetero-by-homo : {X : 𝓤 ̇} {x y : X} → x ＝ y → x ≈ y
hetero-by-homo refl = NB: _ since refl and refl

sigma-eq : forall {X : 𝓤 ̇} {x₁ x₂}
  {Y : X → 𝓥 ̇} {y₁ : Y x₁} {y₂ : Y x₂} →
  x₁ ＝ x₂ → y₁ ≈ y₂ → (x₁ , y₁) ＝ (x₂ , y₂)
sigma-eq refl (NB: _ since foo and refl) = {!!}

equiv-by-eq : forall {𝓤 𝓥 : Universe} {X : 𝓥 ̇} {A : X → 𝓤 ̇}
           {f g : (x : X) → A x} → f ＝ g →
            f ∼ g
equiv-by-eq refl x = refl

-- Must already exist somewhere
nfe-by-fe : {𝓤 𝓥 : Universe} → funext 𝓤 𝓥 → DN-funext 𝓤 𝓥
nfe-by-fe fe {f = f} {g = g} x = pr₁ (pr₁ (fe f g)) x

lift-is-prop : {X : 𝓤 ̇} → is-prop X → is-prop (Lift 𝓥 X)
lift-is-prop {𝓤} {𝓥} {X} X-is-prop lx ly =
  lx ＝⟨ (η-Lift 𝓥 lx)⁻¹ ⟩
  lift 𝓥 (lower lx) ＝⟨ ap (lift 𝓥)
                         (X-is-prop (lower lx) (lower ly)) ⟩
  lift 𝓥 (lower ly) ＝⟨ η-Lift 𝓥 ly ⟩
  ly ∎

prop-is-set : {𝓤 : Universe} →
  is-set (Ω 𝓤)
prop-is-set {𝓤} {P} {.P} refl foo = {!!}

prop-is-prop : {𝓤 : Universe} → (X : 𝓤 ̇) → (X-is-set : is-set X) →
  (fe : funext 𝓤 𝓤) →
  is-prop (is-prop X)
prop-is-prop {𝓤} X X-is-set fe prf1 prf2 = nfe-by-fe fe
  (λ x → nfe-by-fe fe
  (λ y → X-is-set (prf1 x y) (prf2 x y)))

sigma-is-set : {𝓤 : Universe} → {X : 𝓤 ̇} → {Y : X → 𝓤 ̇} →
  is-set X → ((x : X) → is-set (Y x)) → is-set (Sigma X Y)
-- short-cut, ought to use dependent ap for this
sigma-is-set {X} {Y} Xset Yset refl foo = {!!}

_∧Ω_ : Ω 𝓤 → Ω 𝓤 → Ω 𝓤
a ∧Ω b = (⟨ a ⟩ × ⟨ b ⟩)
       , (×-is-prop (holds-is-prop a) (holds-is-prop b))

_∧_ : {𝓤 𝓥 : Universe} {X : 𝓤 ̇} → 𝓟' X → 𝓟' X → 𝓟' {𝓤} {𝓥} X
P ∧ Q = λ x → P x ∧Ω Q x

infixr 4 _∧_

𝓟contra-map : {𝓤 𝓥 : Universe } {X Y : 𝓤 ̇} →
  (Y → X) → 𝓟' {𝓥 = 𝓥} X → 𝓟' {𝓤} {𝓥} Y
𝓟contra-map f P = P ∘ f

lift-Ω : {𝓥 𝓥' : Universe}  →
  Ω 𝓥 → Ω (𝓥 ⊔ 𝓥')
lift-Ω {𝓥' = 𝓥'} P = Lift 𝓥' ⟨ P ⟩ , lift-is-prop (holds-is-prop P)

lift-pred : {𝓤 𝓥 𝓥' : Universe} {X : 𝓤 ̇} →
  𝓟' {𝓤} {𝓥} X → 𝓟' {𝓤} {𝓥 ⊔ 𝓥'} X
lift-pred {𝓥' = 𝓥'} = lift-Ω ∘_

-- not sure whether I'm actually using these

transport2 : {X Y : 𝓤 ̇ } (A : X → Y → 𝓥 ̇ ) {x1 x2 : X} {y1 y2 : Y}
          → x1 ＝ x2 → y1 ＝ y2 → A x1 y1 → A x2 y2
transport2 A refl refl x = x

ap2 : {X Y : 𝓤 ̇ } {Z : 𝓥 ̇} (f : X → Y → Z ) {x1 x2 : X} {y1 y2 : Y}
          → x1 ＝ x2 → y1 ＝ y2 → f x1 y1 ＝ f x2 y2
ap2 f refl refl = refl

ΣΣ : {𝓤 𝓥 𝓦 : Universe} {X : 𝓤 ̇} {Y : 𝓥 ̇} → (Z : X → Y → 𝓦 ̇) →
  𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
ΣΣ Z = Σ (λ x → Σ (λ y → Z x y))

ΣΣΣ : {𝓤 𝓥 𝓦 𝓡 : Universe} {X : 𝓤 ̇} {Y : 𝓥 ̇} {Z : 𝓦 ̇} →
  (R : X → Y → Z → 𝓡 ̇) →
  𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓡 ̇
ΣΣΣ R = Σ (λ x → Σ (λ y → Σ (λ z → R x y z)))


module SurelyThisExistsSomewhere
  (pe : Prop-Ext)
  (fe : Fun-Ext)
  where
  ptwise-is-prop : {X : 𝓤 ̇} → (F : X → 𝓤 ̇) →
     ((x : X) → is-prop (F x)) → is-prop ((x : X) → F x)
  ptwise-is-prop F ptwise f g =
     nfe-by-fe fe (λ x → ptwise x (f x) (g x))
  ptwise-is-prop' : {X : 𝓤 ̇} → {F : X → 𝓤 ̇} →
     ((x : X) → is-prop (F x)) → is-prop ((x : X) → F x)
  ptwise-is-prop' {F = F} = ptwise-is-prop F

  _⇒Ω_ : Ω 𝓤 → Ω 𝓤 → Ω 𝓤
  P ⇒Ω Q = (⟨ P ⟩ → ⟨ Q ⟩) , ptwise-is-prop (λ _ → ⟨ Q ⟩) (λ _ → holds-is-prop Q)

  _⇔Ω_ : Ω 𝓤 → Ω 𝓤 → Ω 𝓤
  P ⇔Ω Q = (P ⇒Ω Q) ∧Ω (Q ⇒Ω P)

  _⇒_ : {𝓤 𝓥 : Universe}
     {X : 𝓤 ̇} → (x y : 𝓟' {𝓤} {𝓥} X) →  𝓟' {𝓤} {𝓥} X
  _⇒_ {𝓤} {X} U V
     = λ x → U x ⇒Ω V x

  _⟺_ : {𝓤 𝓥 : Universe}
     {X : 𝓤 ̇} → (x y : 𝓟' {𝓤} {𝓥} X) →  𝓟' {𝓤} {𝓥} X
  P ⟺ Q = (P ⇒ Q) ∧ (Q ⇒ P)

  infixr 3 _⇒_ _⇒Ω_

  prop-eq : {𝓤 𝓥 : Universe}
     {X : 𝓤 ̇} → (X-is-set : is-set X) → (P Q : 𝓟' {𝓤} {𝓥} X) →
     ((x : X) → ⟨ (P ⇒ Q) x ⟩ × ⟨ (Q ⇒ P) x ⟩) → P ＝ Q
  prop-eq {X = X} X-is-set P Q ptwise = nfe-by-fe fe (λ x → sigma-eq
     (foo x)
     (NB: pr₂ (Q x) since (ap is-prop (foo x))
      and prop-is-prop (pr₁ (Q x))
          (props-are-sets (pr₂ (Q x)))
          -- what a mess
          fe (transport id
             (transport (λ y → is-prop (pr₁ (P x)) ＝ is-prop y)
             (pe (pr₂ (P x)) (pr₂ (Q x)) (pr₁ (ptwise x)) (pr₂ (ptwise x)))
             refl)
             (pr₂ (P x))) (pr₂ (Q x))))
     where
       foo : (x : X) → pr₁ (P x) ＝ pr₁ (Q x)
       foo x = (pe (pr₂ (P x)) (pr₂ (Q x))
              (pr₁ (ptwise x)) (pr₂ (ptwise x)))


\end{code}
