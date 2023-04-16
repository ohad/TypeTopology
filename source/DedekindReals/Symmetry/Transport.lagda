Andrew Sneap and Ohad Kammar

Transport structure (Group, Action) along an equivalence
Use it to lift structure to a larger universe

TODO: actually transport the structure

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

module DedekindReals.Symmetry.Transport
       (pe : Prop-Ext)
       (fe : Fun-Ext)
       where
  -- Since we refactored GroupAction to mix universes, this might no
  -- longer be necessary
  Lift-group : {𝓤 𝓥 : Universe} →
               Group 𝓤 → Group (𝓤 ⊔ 𝓥)
  Lift-group {𝓤} {𝓥} G
     = Lift 𝓥 ⟨ G ⟩
     , (λ x y → lift 𝓥 (lower x ·⟨ G ⟩ lower y))
     , (Lift-is-set 𝓥 ⟨ G ⟩ (group-is-set G))
     , (λ x y z → ap (lift 𝓥)
         (assoc G (lower x) (lower y) (lower z)))
     , lift 𝓥 (unit G)
     , (λ x → ap (lift 𝓥)
         (unit-left G (lower x)))
     , (λ x → ap (lift 𝓥)
         (unit-right G (lower x)))
     , λ x → (lift 𝓥 (inv G (lower x)))
     , ap (lift 𝓥) (inv-left G (lower x))
     , ap (lift 𝓥) (inv-right G (lower x))
  Lift-action : {𝓤 𝓥 𝓦 : Universe} →
               (G : Group 𝓤) → Action' {𝓥 = 𝓥 } G →
                                Action' {𝓥 = 𝓥 ⊔ 𝓦 } G
  Lift-action {𝓥 = 𝓥} {𝓦} G A
     = Lift 𝓦 ⟨ A ⟩
     , (λ x a → lift 𝓦 ( x ◂⟨ G ∣ A ⟩ lower a ))
     , (Lift-is-set 𝓦 ⟨ A ⟩ (carrier-is-set G A))
     , (λ g h x → ap (lift 𝓦)
         (action-assoc G A g h (lower x)))
     , λ x → ap (lift 𝓦)
         (action-unit G A (lower x))

\end{code}
