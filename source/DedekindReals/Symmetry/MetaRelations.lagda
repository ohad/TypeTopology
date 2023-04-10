Andrew Sneap and Ohad Kammar

Properties of relations as 2nd-order relations and their invariance

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
open import DedekindReals.Symmetry.Equivariance
open import DedekindReals.Symmetry.Transport

module DedekindReals.Symmetry.MetaRelations
     (pe : Prop-Ext)
     (pt : propositional-truncations-exist)
     (fe : Fun-Ext)
     {𝓤₀ : Universe}
     (X : 𝓤₀ ̇) (Xset : is-set X) where

     open DedekindReals.Symmetry.UF.SurelyThisExistsSomewhere pe fe
     open PropositionalTruncation pt

     PreRel : 𝓤₀ ⁺ ̇
     PreRel = X × X → 𝓤₀ ̇

     Rel : 𝓤₀ ⁺ ̇
     Rel = 𝓟 (X × X)

     pointwise-prop : PreRel → 𝓤₀ ̇
     pointwise-prop R = (x y : X) → is-prop (R (x , y))

     transitive-rel : 𝓟 {𝓤 = 𝓤₀ ⁺} Rel
     transitive-rel R =
      Lift (𝓤₀ ⁺)
        ((x y z : X) → ⟨ R (x , y) ⟩ → ⟨ R (y , z) ⟩ →
          ⟨ R (x , z) ⟩)
      , lift-is-prop (
        ptwise-is-prop' λ x →
        ptwise-is-prop' (λ y →
        ptwise-is-prop' (λ z →
        ptwise-is-prop' (λ x-R-y →
        ptwise-is-prop' (λ y-R-z →
        holds-is-prop (R (x , z)))))))

     irreflexive-rel : 𝓟 {𝓤 = 𝓤₀ ⁺} Rel
     irreflexive-rel R =
       Lift (𝓤₀ ⁺)
         ((x : X) → ¬ (⟨ R (x , x) ⟩))
       , lift-is-prop (
         ptwise-is-prop' λ x →
           -- I want to use ptwise-is-prop' again, but cannot
           -- for some reason
           λ prf1 prf2 → nfe-by-fe fe (λ xRx →
             𝟘-is-prop (prf1 xRx) (prf2 xRx)) )

     trichotomous-rel : (R : Rel) →
       ⟨ irreflexive-rel R ⟩ →
       ⟨ transitive-rel  R ⟩ → Ω (𝓤₀ ⁺)
     trichotomous-rel R ir tr =
       Lift (𝓤₀ ⁺)
         ((x y : X) → (⟨ R (x , y) ⟩) ∔ (x ＝ y) ∔ (⟨ R (y , x)⟩))
       , lift-is-prop (
         ptwise-is-prop' λ x →
         ptwise-is-prop' λ y →
         +-is-prop (holds-is-prop (R (x , y))) (
         +-is-prop Xset
                   (holds-is-prop (R (y , x)))
           -- discharge disjointness assumptions
           (λ {refl → lower ir x}))
           λ { xRy (inl refl) → lower ir x xRy
             ; xRy (inr yRx ) → lower ir x
                               (lower tr x y x
                                xRy yRx)}
           )


     𝓟∋Sigma : {𝓤 𝓥 : Universe} → {X : 𝓤 ̇} → (Y : X → 𝓤 ̇) → 𝓟' {𝓤} {𝓥} (Sigma X Y) → 𝓟' {𝓤} {𝓤 ⊔ 𝓥} X
     𝓟∋Sigma Y P x
       = (∃ y ꞉ Y x , ⟨ P (x , y) ⟩)
       , ∃-is-prop

     -- A simply typed variant
     s𝓟∋Sigma : {𝓤 𝓥 : Universe} → {X : 𝓤 ̇} → (Y : 𝓤 ̇) → 𝓟' {𝓤} {𝓥} (X × Y) → 𝓟' {𝓤} {𝓤 ⊔ 𝓥} X
     s𝓟∋Sigma Y P x
       = (∃ y ꞉ Y , ⟨ P (x , y) ⟩)
       , ∃-is-prop

     -- a closed variant
     c𝓟∋Sigma : {𝓤 𝓥 : Universe} → (Y : 𝓤 ̇) → 𝓟' {𝓤} {𝓥} (Y) → Ω (𝓤 ⊔ 𝓥)
     c𝓟∋Sigma Y P
       = (∃ y ꞉ Y , ⟨ P y ⟩)
       , ∃-is-prop

     𝓟∋Pi : {𝓤 𝓥 : Universe} → {X : 𝓤 ̇} → (Y : X → 𝓤 ̇) → 𝓟' {𝓤} {𝓥} (Sigma X Y) → 𝓟' {𝓤} {𝓤 ⊔ 𝓥} X
     𝓟∋Pi Y P x
       = ((y : Y x) → ⟨ P (x , y) ⟩)
       -- for some reason I can't use pntwise-is-prop
       , λ f g → nfe-by-fe fe (λ y → holds-is-prop
           (P (x , y)) (f y) (g y))

     -- a simply typed variant
     s𝓟∋Pi : {𝓤 𝓥 : Universe} → {X : 𝓤 ̇} → (Y : 𝓤 ̇) → 𝓟' {𝓤} {𝓥} (X × Y) → 𝓟' {𝓤} {𝓤 ⊔ 𝓥} X
     s𝓟∋Pi Y P x
       = ((y : Y) → ⟨ P (x , y) ⟩)
       -- for some reason I can't use pntwise-is-prop
       , λ f g → nfe-by-fe fe (λ y → holds-is-prop
           (P (x , y)) (f y) (g y))

     c𝓟∋Pi : {𝓤 𝓥 : Universe} → (Y : 𝓤 ̇) → 𝓟' {𝓤} {𝓥} (Y) → Ω (𝓤 ⊔ 𝓥)
     c𝓟∋Pi Y P
       = ((y : Y) → ⟨ P y ⟩)
       -- for some reason I can't use pntwise-is-prop
       , λ f g → nfe-by-fe fe (λ y → holds-is-prop
           (P y) (f y) (g y))


\end{code}
