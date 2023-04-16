Andrew Sneap and Ohad Kammar

Relate S2 symmetries to the collection of relations

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
open import DedekindReals.Symmetry.S2

module DedekindReals.Symmetry.Relations-S2
     (pe : Prop-Ext)
     (pt : propositional-truncations-exist)
     (fe : Fun-Ext) where
  module SetConstructions-S2
     {𝓤₀ : Universe}
     (X : 𝓤₀ ̇) (Xset : is-set X) where

     open import DedekindReals.Symmetry.MetaRelations pe pt fe
     open SetConstructions X Xset
     open import DedekindReals.Symmetry.Subactions pe fe
     open import DedekindReals.Symmetry.Transport pe fe

     opposite : Rel → Rel
     opposite R xy =
       R (flip ◂⟨ S₂ ∣ Flip X Xset  ⟩ xy)

     _◂⟨S₂∣Rel⟩_ : action-structure S₂ Rel
     id∈S₂ ◂⟨S₂∣Rel⟩ R = R
     flip  ◂⟨S₂∣Rel⟩ R = opposite R

     assoc-Rel : is-assoc S₂ _◂⟨S₂∣Rel⟩_
     assoc-Rel id∈S₂ h x = refl
     assoc-Rel flip id∈S₂ x = refl
     assoc-Rel flip flip x = refl

     unital-Rel : is-unital S₂ _◂⟨S₂∣Rel⟩_
     unital-Rel x = refl

     RelIsSet : is-set Rel
     RelIsSet = 𝓟-is-set' fe pe

     S₂onRel : Action-structure S₂ Rel
     S₂onRel = _◂⟨S₂∣Rel⟩_
             , RelIsSet
             , assoc-Rel
             , unital-Rel

     S₂∣Rel : Action' {𝓥 = 𝓤₀ ⁺} S₂
     S₂∣Rel = Rel , S₂onRel

     transitive-is-invariant : invariant
       S₂ S₂∣Rel
       (Ω (𝓤₀ ⁺)) prop-is-set
       transitive-rel
     transitive-is-invariant =
       invariant-proposition pe fe S₂ S₂∣Rel
       transitive-rel
       lemma
       where
         lemma : (g : ⟨ S₂ ⟩) → (a : ⟨ S₂∣Rel ⟩) →
                 ⟨ transitive-rel a ⟩ →
                 ⟨ transitive-rel
                    (g ◂⟨ S₂ ∣ S₂∣Rel ⟩ a) ⟩
         lemma id∈S₂ a tr = tr
         lemma flip  a tr = lift _ λ x y z xRy yRz →
                                lower tr z y x yRz xRy

     irreflexive-is-invariant : invariant
       S₂ S₂∣Rel
       (Ω (𝓤₀ ⁺)) prop-is-set
       irreflexive-rel
     irreflexive-is-invariant =
       invariant-proposition pe fe S₂ S₂∣Rel
       irreflexive-rel
       lemma
       where
         lemma : (g : ⟨ S₂ ⟩) → (R : ⟨ S₂∣Rel ⟩) →
                 ⟨ irreflexive-rel R ⟩ →
                 ⟨ irreflexive-rel
                    (g ◂⟨ S₂ ∣ S₂∣Rel ⟩ R) ⟩
         lemma id∈S₂ a ir  = ir
         lemma flip  a ir  = lift _ λ x prf → lower ir x prf
     S₂∣Quasi-Ordering : Action' {𝓥 = 𝓤₀ ⁺ } S₂
     S₂∣Quasi-Ordering =
       subaction
         S₂ S₂∣Rel
         (irreflexive-rel ∧ transitive-rel)
         (∧-invariant S₂ S₂∣Rel irreflexive-rel transitive-rel
         (invariant-proposition-prop-is-invariant
           S₂ S₂∣Rel irreflexive-rel irreflexive-is-invariant)
         (invariant-proposition-prop-is-invariant
           S₂ S₂∣Rel transitive-rel transitive-is-invariant))


     trichotomous-is-invariant : invariant
       S₂ S₂∣Quasi-Ordering
       (Ω (𝓤₀ ⁺)) prop-is-set
       (λ { (R , ir , tr) → trichotomous-rel R ir tr})
     trichotomous-is-invariant = invariant-proposition pe fe
       S₂ S₂∣Quasi-Ordering
       (λ { (R , ir , tr) → trichotomous-rel R ir tr})
       lemma
       where
         lemma : prop-is-invariant S₂ S₂∣Quasi-Ordering
           λ { (R , ir , tr) → trichotomous-rel R ir tr } --
         lemma id∈S₂  R prf = prf
         lemma flip   R prf = lift _ λ x y →
           Cases (lower prf y x)
             (λ yRx → inl yRx)
             (cases (λ y＝x → inr (inl ((y＝x)⁻¹)))
                    λ xRy → inr (inr xRy))


  module GroupConstructions
     {𝓤₀ : Universe}
     (G : Group 𝓤₀)  where
    open import DedekindReals.Symmetry.Transport pe fe
    open SetConstructions-S2
    RelLiftAction : (A : Action' {𝓥 = 𝓥} G) →
      Action' {𝓥 = 𝓥 ⁺} ( G ᵒᵖ)
    RelLiftAction A
      = 𝓟 ⟨ A ⟩
      , (λ g P a → P (g ◂⟨ G ∣ A ⟩ a ))
      , 𝓟-is-set' fe pe
      , (λ g h P → nfe-by-fe fe λ a → ap P
          (action-assoc G A (h) (g) a ))
      , λ P → nfe-by-fe fe λ a → ap P
          (action-unit G A a)

    -- Since we don't ave (G ᵒᵖ)ᵒᵖ = G judgementally, here's a DIY
    RelLiftActionᵒᵖ : (A : Action' {𝓥 = 𝓥} (G ᵒᵖ)) →
      Action' {𝓥 = 𝓥 ⁺} G
    RelLiftActionᵒᵖ A
      = 𝓟 ⟨ A ⟩
      , (λ g P a → P (g ◂⟨ G ᵒᵖ ∣ A ⟩ a ))
      , 𝓟-is-set' fe pe
      , (λ g h P → nfe-by-fe fe λ a → ap P
          (action-assoc (G ᵒᵖ) A (h) (g) a ))
      , λ P → nfe-by-fe fe λ a → ap P
          (action-unit (G ᵒᵖ) A a)

\end{code}
