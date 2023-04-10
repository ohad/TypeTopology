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
open import DedekindReals.Symmetry.Transport
open import DedekindReals.Symmetry.S2

module DedekindReals.Symmetry.Relations-S2
     (pe : Prop-Ext)
     (pt : propositional-truncations-exist)
     (fe : Fun-Ext)
     {𝓤₀ : Universe}
     (X : 𝓤₀ ̇) (Xset : is-set X) where

     open import DedekindReals.Symmetry.MetaRelations pe pt fe X Xset
     open import DedekindReals.Symmetry.Subactions pe fe

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
     RelIsSet {R} {.R} refl arefl = {!!} --refl

     S₂onRel : Action-structure S₂ Rel
     S₂onRel = _◂⟨S₂∣Rel⟩_
             , RelIsSet
             , assoc-Rel
             , unital-Rel

     S₂∣Rel : Action (S₂ {𝓤 = 𝓤₀ ⁺})
     S₂∣Rel = Rel , S₂onRel

     S₂' : Group (𝓤₀ ⁺⁺)
     S₂' = Lift-group pe fe (S₂ {𝓤₀ ⁺})

     S₂'∣Rel' : Action S₂'
     S₂'∣Rel' = Lift-action pe fe S₂ S₂∣Rel

     Rel'IsSet : is-set ⟨ S₂'∣Rel' ⟩
     Rel'IsSet = Lift-is-set (𝓤₀ ⁺⁺) Rel RelIsSet

     transitive-is-invariant : invariant
       S₂' S₂'∣Rel'
       (Ω (𝓤₀ ⁺)) prop-is-set
       (transitive-rel ∘ lower)
     transitive-is-invariant =
       invariant-proposition pe fe S₂' S₂'∣Rel'
       (transitive-rel ∘ lower)
       lemma
       where
         lemma : (g : ⟨ S₂' ⟩) → (a : ⟨ S₂'∣Rel' ⟩) →
                 ⟨ transitive-rel (lower a) ⟩ →
                 ⟨ transitive-rel
                    (lower g ◂⟨ S₂ ∣ S₂∣Rel ⟩ lower a) ⟩
         lemma g a tr with lower g
         lemma _ a tr | id∈S₂ = tr
         lemma _ a tr | flip  = lift _ λ x y z xRy yRz →
                                lower tr z y x yRz xRy

     irreflexive-is-invariant : invariant
       S₂' S₂'∣Rel'
       (Ω (𝓤₀ ⁺)) prop-is-set
       (irreflexive-rel ∘ lower)
     irreflexive-is-invariant =
       invariant-proposition pe fe S₂' S₂'∣Rel'
       (irreflexive-rel ∘ lower)
       lemma
       where
         lemma : (g : ⟨ S₂' ⟩) → (R : ⟨ S₂'∣Rel' ⟩) →
                 ⟨ irreflexive-rel (lower R) ⟩ →
                 ⟨ irreflexive-rel
                    (lower g ◂⟨ S₂ ∣ S₂∣Rel ⟩ lower R) ⟩
         lemma g a ir with lower g
         lemma g a ir | id∈S₂ = ir
         lemma g a ir | flip  = lift _ λ x prf → lower ir x prf
     S₂∣Quasi-Ordering : Action (S₂ {𝓤₀ ⁺})
     S₂∣Quasi-Ordering = subaction
       (S₂ {𝓤₀ ⁺})
       S₂∣Rel
       (irreflexive-rel ∧ transitive-rel)
       (∧-invariant S₂ S₂∣Rel irreflexive-rel transitive-rel
         (invariant-proposition-prop-is-invariant
           S₂' S₂'∣Rel' (irreflexive-rel ∘ lower)
           irreflexive-is-invariant)
         (invariant-proposition-prop-is-invariant
           S₂' S₂'∣Rel' (transitive-rel ∘ lower)
           transitive-is-invariant))

     S₂'∣Quasi-Ordering' : Action S₂'
     S₂'∣Quasi-Ordering' = Lift-action
       pe fe S₂ S₂∣Quasi-Ordering

     trichotomous-is-invariant : invariant
       S₂' S₂'∣Quasi-Ordering'
       (Ω (𝓤₀ ⁺)) prop-is-set
       ((λ { (R , ir , tr) → trichotomous-rel R ir tr}) ∘ lower)
     trichotomous-is-invariant = invariant-proposition pe fe
       S₂' S₂'∣Quasi-Ordering'
       ((λ { (R , ir , tr) → trichotomous-rel R ir tr}) ∘ lower)
       lemma
       where
         lemma : prop-is-invariant S₂' S₂'∣Quasi-Ordering'
           ((λ { (R , ir , tr) → trichotomous-rel R ir tr })
            ∘ lower)
         lemma g R prf with lower g
         ... | id∈S₂ = prf
         ... | flip = lift _ λ x y →
           Cases (lower prf y x)
             (λ yRx → inl yRx)
             (cases (λ y＝x → inr (inl ((y＝x)⁻¹)))
                    λ xRy → inr (inr xRy))

\end{code}
