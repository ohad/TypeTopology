Andrew Sneap and Ohad Kammar

Use predicates to carve out subactions

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

module DedekindReals.Symmetry.Subactions
         (pe : Prop-Ext)
         (fe : Fun-Ext)
         {𝓤 𝓥 : Universe}
         (G : Group 𝓤) (A : Action' {𝓥 = 𝓥} G)
       where

    open DedekindReals.Symmetry.UF.SurelyThisExistsSomewhere pe fe

    subaction : (P : 𝓟' {𝓥 = 𝓦} ⟨ A ⟩) →
      prop-is-invariant G A P  →
      Action' {𝓥 = 𝓥 ⊔ 𝓦} G
    subaction P invar
      = (Sigma ⟨ A ⟩ λ a → P a holds)
      , (λ {g (a , Pa) → (g ◂⟨ G ∣ A ⟩ a)
                       , invar g a Pa})
      , sigma-is-set (carrier-is-set G A)
                     (λ a → props-are-sets (holds-is-prop (P a))  )
      , (λ {g h (a , Pa) → to-subtype-＝ (holds-is-prop ∘ P)
             ((g ·⟨ G ⟩ h) ◂⟨ G ∣ A ⟩ a
                 ＝⟨ action-assoc G A g h a ⟩
              g ◂⟨ G ∣ A ⟩ (h ◂⟨ G ∣ A ⟩ a) ∎)
           })
      -- similarly
      , λ x →
        to-subtype-＝ (holds-is-prop ∘ P)
          (action-unit G A (pr₁ x))

    ∧-invariant : (P Q : 𝓟' {𝓥 = 𝓦} ⟨ A ⟩) →
      prop-is-invariant G A P →
      prop-is-invariant G A Q →
      prop-is-invariant G A (P ∧ Q)
    ∧-invariant P Q pInv qInv g a (⟨Pa⟩ , ⟨Qa⟩)
      = pInv g a ⟨Pa⟩ , qInv g a ⟨Qa⟩
\end{code}
