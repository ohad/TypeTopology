\begin{code}
{-# OPTIONS --without-K --exact-split --no-sized-types --no-guardedness --auto-inline #-} --safe

module DedekindReals.Symmetry.Transitive where

open import MLTT.Universes

open import MLTT.Id
open import DedekindReals.Symmetry.UF

-- TODO: duplicate of Ordinals.Notions --- refactor to common parent
is-transitive : {𝓤 𝓥 : Universe} {X : 𝓤 ̇} →
  (_<_ : X → X → 𝓥 ̇) → 𝓤 ⊔ 𝓥 ̇
is-transitive {X = X} _<_ = (x y z : X) → x < y → y < z → x < z

_≺⟨_,_∣_⟩_ : {X : 𝓤 ̇ } (x : X) (R : X → X → 𝓥 ̇) →
  is-transitive R →
  {y z : X} → R x y → R y z → R x z
x ≺⟨ R , trans ∣ justification ⟩ rest = trans x _ _ justification rest

trans-equality : {X : 𝓤 ̇ } (x : X) →
  {x' : X} → (x ＝ x') → (R : X → X → 𝓥 ̇) →
  {y z : X} → R x' y → y ＝ z → R x z
trans-equality x {x'} x=x' R {y} {z} x'Ry y=z
  = transport2 R (x=x' ⁻¹) (y=z) x'Ry

trans-equality-right-refl : {X : 𝓤 ̇ } (x : X) →
  {x' : X} → (x ＝ x') → (R : X → X → 𝓥 ̇) →
  {y : X} → R x' y → R x y
trans-equality-right-refl x {x'} x=x' R {y} x'Ry =
  trans-equality x {x'} x=x' R {y} x'Ry refl


trans-equality-left-refl : {X : 𝓤 ̇ } (x : X) →
  (R : X → X → 𝓥 ̇) →
  {y z : X} → R x y → y ＝ z → R x z
trans-equality-left-refl x R {y} {z} x'Ry y=z =
  trans-equality x refl R x'Ry y=z


syntax trans-equality x {x'} x=x' R {y} {z} justification eq =
  x ＝⟨ x=x' ⟩ x' ≺⟨ R ∣ justification ⟩ y ＝⟨ eq ⟩ z ∎

syntax trans-equality-right-refl
  x {x'} x=x' R {y} justification =
  x ＝[ x=x' ] x' ≺⟨ R ∣ justification ⟩ y ∎

syntax trans-equality-left-refl x R {y} {z} justification eq =
  x ≺⟨ R ∣ justification ⟩ y ＝[ eq ] z ∎

FinalStep : {X : 𝓤 ̇ } (x y : X) {R : X → X → 𝓥 ̇} →
  R x y → R x y
FinalStep _ _ x<y = x<y
syntax FinalStep x y {R} x<y = x ≺⟨ x<y ⟩ y ∎[ R ]


infixr 0 _≺⟨_,_∣_⟩_



\end{code}
