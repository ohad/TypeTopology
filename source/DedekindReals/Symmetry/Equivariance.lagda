Andrew Sneap and Ohad Kammar

Includes results about equivariance and invariance
Ought to move under Groups eventually

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

open import DedekindReals.Symmetry.UF
open import DedekindReals.Symmetry.IndexedAction
open import DedekindReals.Symmetry.ActionsConstructions

module DedekindReals.Symmetry.Equivariance where

is-dep-equivariant-wrt : (G : Group 𝓤) → (A : Action' {𝓥 = 𝓥} G) →
    ((⟨B⟩ , structure) : ⟨_∣_⟩-indexed-action {𝓦 = 𝓦} G A) →
    (f : (a : ⟨ A ⟩) → ⟨B⟩ a) → (g : ⟨ G ⟩ ) → 𝓥 ⊔ 𝓦 ⁺ ̇
is-dep-equivariant-wrt G A B f g = (a : ⟨ A ⟩) →
    (f (g ◂⟨ G ∣ A ⟩ a)) ≈ (g ◃⟨ G ∣ A ∣ B ⟩ (f a))

is-dep-equivariant : (G : Group 𝓤) → (A : Action' {𝓥 = 𝓥} G) →
    ((⟨B⟩ , structure) : ⟨_∣_⟩-indexed-action {𝓦 = 𝓦} G A) →
    (f : (a : ⟨ A ⟩) → ⟨B⟩ a) → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺ ̇
is-dep-equivariant G A B f
    = (g : ⟨ G ⟩ ) → is-dep-equivariant-wrt G A B f g

invariant : (G : Group 𝓤) → (A : Action' {𝓥 = 𝓥} G) →
    (⟨B⟩ : 𝓦 ̇) → is-set ⟨B⟩ →
    (f : ⟨ A ⟩ → ⟨B⟩) → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺ ̇
invariant G A ⟨B⟩ ⟨B⟩set f =
    is-dep-equivariant G A (const-action G A ⟨B⟩ ⟨B⟩set) f

invariant-wrt : (G : Group 𝓤) → (A : Action' {𝓥 = 𝓥} G) →
    (⟨B⟩ : 𝓦 ̇) → is-set ⟨B⟩ →
    (f : ⟨ A ⟩ → ⟨B⟩) → (g : ⟨ G ⟩ ) → 𝓥 ⊔ 𝓦 ̇
invariant-wrt G A ⟨B⟩ ⟨B⟩set f g =
  (a : ⟨ A ⟩) → ((f (g ◂⟨ G ∣ A ⟩ a)) ＝ (f a))

invariant' : (G : Group 𝓤) → (A : Action' {𝓥 = 𝓥} G) →
    (⟨B⟩ : 𝓦 ̇) → is-set ⟨B⟩ →
    (f : ⟨ A ⟩ → ⟨B⟩) → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
invariant' G A ⟨B⟩ ⟨B⟩set f =
    (g : ⟨ G ⟩ ) →
    invariant-wrt G A ⟨B⟩ ⟨B⟩set f g

invariant-by-invariant' :
    (G : Group 𝓤) → (A : Action' {𝓥 = 𝓥} G) →
    (⟨B⟩ : 𝓦 ̇) → (⟨B⟩set : is-set ⟨B⟩) →
    (f : ⟨ A ⟩ → ⟨B⟩) → invariant' G A ⟨B⟩ ⟨B⟩set f →
    invariant G A ⟨B⟩ ⟨B⟩set f
invariant-by-invariant' G A ⟨B⟩ ⟨B⟩set f inv' g a =
    hetero-by-homo (inv' g a)

invariant'-by-invariant :
    (G : Group 𝓤) → (A : Action' {𝓥 = 𝓥} G) →
    (⟨B⟩ : 𝓦 ̇) → (⟨B⟩set : is-set ⟨B⟩) →
    (f : ⟨ A ⟩ → ⟨B⟩) → invariant G A ⟨B⟩ ⟨B⟩set f →
    invariant' G A ⟨B⟩ ⟨B⟩set f
invariant'-by-invariant G A ⟨B⟩ ⟨B⟩set f invar g a
    with invar g a
... | NB: .(f a) since arefl and prf = {!!} --prf


open DedekindReals.Symmetry.UF.SurelyThisExistsSomewhere

-- For propositions, we can get therefore get invariance more easily

prop-is-invariant-wrt-at :
  (G : Group 𝓤 ) → (A : Action' {𝓥 = 𝓥} G) →
    (P : ⟨ A ⟩ → Ω 𝓦) → (g : ⟨ G ⟩) → (a : ⟨ A ⟩) → 𝓦 ̇
prop-is-invariant-wrt-at G A P g a =
  ⟨ P a ⟩ → ⟨ P (g ◂⟨ G ∣ A ⟩ a) ⟩

prop-is-invariant-wrt : (G : Group 𝓤 ) → (A : Action' {𝓥 = 𝓥} G) →
    (P : ⟨ A ⟩ → Ω 𝓦) → (g : ⟨ G ⟩) → 𝓥 ⊔ 𝓦 ̇
prop-is-invariant-wrt G A P g =
  (a : ⟨ A ⟩) → prop-is-invariant-wrt-at G A P g a

prop-is-invariant :
    (G : Group 𝓤 ) → (A : Action' {𝓥 = 𝓥} G) →
    (P : ⟨ A ⟩ → Ω 𝓦) → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
prop-is-invariant G A P =
  (g : ⟨ G ⟩) → prop-is-invariant-wrt G A P g

invariant-proposition :
    (pe : Prop-Ext) (fe : Fun-Ext)
    (G : Group 𝓤 ) → (A : Action' {𝓥 = 𝓥} G) →
    (P : ⟨ A ⟩ → Ω 𝓦) →
    prop-is-invariant G A P →
    invariant {𝓦 = 𝓦 ⁺} G A (Ω 𝓦) prop-is-set P
invariant-proposition {𝓤 = 𝓤} {𝓦 = 𝓦} pe fe G A P prf =
  invariant-by-invariant'
    G A (Ω 𝓦) prop-is-set P λ g →
    equiv-by-eq
    (prop-eq pe fe
    (carrier-is-set G A) (P ∘ (λ a → g ◂⟨ G ∣ A ⟩ a)) P
      λ a → (λ ⟨Pga⟩ →
      transport (λ b → ⟨ P b ⟩)
        (inv G g ◂⟨ G ∣ A ⟩ (g ◂⟨ G ∣ A ⟩ a)
          ＝⟨ (action-assoc G A (inv G g) g a) ⁻¹ ⟩
        (inv G g ·⟨ G ⟩ g)     ◂⟨ G ∣ A ⟩ a
          ＝⟨ ap (λ h → h ◂⟨ G ∣ A ⟩ a )
                 (inv-left G g) ⟩
        unit G ◂⟨ G ∣ A ⟩ a
          ＝⟨  action-unit G A a ⟩
        a ∎)
        (prf (inv G g) (g ◂⟨ G ∣ A ⟩ a) ⟨Pga⟩))
      ,
      λ ⟨Pa⟩ → prf g a ⟨Pa⟩)

invariant-proposition-prop-is-invariant :
    (G : Group 𝓤) → (A : Action' {𝓥 = 𝓥} G) →
    (P : ⟨ A ⟩ → Ω 𝓦) →
    invariant G A (Ω 𝓦) prop-is-set P →
    prop-is-invariant G A P
invariant-proposition-prop-is-invariant G A P invar g a ⟨Pa⟩
  = transport ⟨_⟩
    ((invariant'-by-invariant G A (Ω _) prop-is-set
      P invar g a)⁻¹)
    ⟨Pa⟩
