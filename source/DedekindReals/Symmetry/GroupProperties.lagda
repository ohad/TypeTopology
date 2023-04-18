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
inv-involutive G g = one-left-inv
  G (inv G g) g (inv-right G g) ⁻¹

inv-reverses-multiplication : (G : Group 𝓤) → (g h : ⟨ G ⟩) →
  inv G (g ·⟨ G ⟩ h) ＝ (inv G h) ·⟨ G ⟩ (inv G g)
inv-reverses-multiplication G@(_ , _·_ , _) g h =
  one-left-inv
  G (g · h) ((inv G h) · (inv G g))
    (((inv G h) · (inv G g)) · (g · h)
      ＝⟨ assoc G (inv G h) (inv G g) (g · h) ⟩
     (inv G h) · ((inv G g) · ((g · h)))
      ＝⟨ ap (inv G h ·_)
         (assoc G (inv G g) g h ⁻¹) ⟩
     ((inv G h) · (((inv G g) · g)· h))
      ＝⟨ ap (λ x → (inv G h · (x · h)))
         (inv-left G g) ⟩
     ((inv G h) · ((unit G)· h))
      ＝⟨ ap (inv G h ·_)
         (unit-left G h) ⟩
     ((inv G h) · h)
      ＝⟨ inv-left G h ⟩
     unit G ∎) ⁻¹

inv-unit-unit : (G : Group 𝓤) → inv G (unit G) ＝ unit G
inv-unit-unit G = one-left-inv G (unit G) (unit G)
  (unit-right G (unit G)) ⁻¹

\end{code}
