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
open import DedekindReals.Symmetry.Subgroups

module DedekindReals.Symmetry.Subactions
         (pe : Prop-Ext)
         (fe : Fun-Ext) where
module Basic
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
open Basic public

subgroups-commute :
      {𝓤 𝓥 𝓦 : Universe}
      (pt : propositional-truncations-exist) →
      (G : Group 𝓤) → (H : Group 𝓥) → {X : 𝓦 ̇} →
      (A-struct : Action-structure {𝓥 = 𝓦} G X) →
      (B-struct : Action-structure {𝓥 = 𝓦} H X) →
      (G-closed : Subgroups' pe pt fe G) →
      (H-closed : Subgroups' pe pt fe H) →
      let G' = induced-group' pe pt fe G G-closed
          H' = induced-group' pe pt fe H H-closed
          A = X , A-struct
          B = X , B-struct
      in
      actions-commute G H A B →
      actions-commute G' H'
        (induced-action pe pt fe G G-closed A )
        (induced-action pe pt fe H H-closed B)
subgroups-commute pt G H A-struct B-struct G-closed H-closed
  A-B-commute g h = A-B-commute (pr₁ g) (pr₁ h)


subactions-commute :
      {𝓦 : Universe}
      (G : Group 𝓤) → (H : Group 𝓥) → {X : 𝓦 ̇} →
      (A-struct : Action-structure {𝓥 = 𝓦} G X) →
      (B-struct : Action-structure {𝓥 = 𝓦} H X) →
      let A = X , A-struct
          B = X , B-struct
      in (P : 𝓟 X) →
      (invar-A : prop-is-invariant G A P) →
      (invar-B : prop-is-invariant H B P) →
      actions-commute G H A B →
      actions-commute G H
        (subaction G A P invar-A)
        (subaction H B P invar-B)
subactions-commute G H A-struct B-struct P invar-A invar-B
  A-B-commute g h x = to-subtype-＝
     (holds-is-prop ∘ P)
     (A-B-commute g h (pr₁ x))

\end{code}
