Andrew Sneap and Ohad Kammar

Additional properties of groups. Will eventually migrate to a
Groups subdirectory
\begin{code}
{-# OPTIONS --without-K --exact-split  --no-sized-types --no-guardedness --auto-inline --lossy-unification --allow-unsolved-metas #-} --safe

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

module DedekindReals.Symmetry.GroupProperties where

inv-involutive : (G : Group 𝓤) → (g : ⟨ G ⟩) → inv G (inv G g) ＝ g
inv-involutive g = {!!} -- fun to be had here

\end{code}
