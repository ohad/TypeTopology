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
       {𝓥 : Universe}
       (pe : Prop-Ext)
       (fe : Fun-Ext)
       where
  Lift-group : Group 𝓤 → Group (𝓤 ⊔ 𝓥)
  Lift-group G
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
  Lift-action : (G : Group 𝓤) → Action G →
     Action (Lift-group G)
  Lift-action G A
     = Lift 𝓥 ⟨ A ⟩
     , (λ x a → lift 𝓥 ( lower x ◂⟨ G ∣ A ⟩ lower a ))
     , (Lift-is-set 𝓥 ⟨ A ⟩ (carrier-is-set G A))
     , (λ g h x → ap (lift 𝓥)
         (action-assoc G A (lower g) (lower h) (lower x)))
     , λ x → ap (lift 𝓥)
         (action-unit G A (lower x))

\end{code}
