Andrew Sneap and Ohad Kammar

The Groups.Subgroups module uses univalence to define and induce
subgroups. That's fine, but since we only postulate univalence,
computation jams on the subgroup, which leads to more sophisticated
reasoning. In this module we reproduce this functionality while
retaining the computational 'content'.

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

module DedekindReals.Symmetry.Subgroups
         (pe : Prop-Ext)
         (pt : propositional-truncations-exist)
         (fe : Fun-Ext)
         {𝓤 : Universe}
         (G : Group 𝓤)
       where

    open DedekindReals.Symmetry.UF.SurelyThisExistsSomewhere pe fe
    open import DedekindReals.Symmetry.MetaRelations pe pt fe

    group-closed' : 𝓟 (𝓟 ⟨ G ⟩)
    group-closed' 𝓐
      = lift-pred 𝓐 (unit G)
      ∧Ω ({!s𝓟∋Pi ⟨ G ⟩ λ x →  ?!}
      -- s𝓟∋Pi ⟨ G ⟩ λ y →
      ∧Ω {!!})
    {-𝓐 (unit G) -}
                 {-𝓟∋Pi ((x y : ⟨ G ⟩) → 𝓐 x → 𝓐 y → 𝓐 (x · y)) -}
                 {- ((x : ⟨ G ⟩) → 𝓐 x → 𝓐 (inv G x))-}

    --foo : Subgroups {!!} {!!} {!!}

\end{code}
