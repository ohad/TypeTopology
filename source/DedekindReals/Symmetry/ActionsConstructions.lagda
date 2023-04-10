Andrew Sneap and Ohad Kammar

Ought to move under Groups eventually

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

module DedekindReals.Symmetry.ActionsConstructions
  {𝓤 : Universe} where

  ptwise : {X Y Z U V W : 𝓤 ̇} → (X → Y → Z) → (U → V → W) → (X × U → Y × V → Z × W)
  ptwise f g (x , u) (y , v) = (f x y) , (g u v)

  ptwise-group-structure : (G H : Group 𝓤) → group-structure (⟨ G ⟩ × ⟨ H ⟩)
  ptwise-group-structure G H  = ptwise (multiplication G) (multiplication H)

  assoc-ptwise : (G H : Group 𝓤) →  associative (ptwise-group-structure G H)
  assoc-ptwise G H x y z = ap2 _,_ (assoc G (pr₁ x) (pr₁ y) (pr₁ z))
                                   (assoc H (pr₂ x) (pr₂ y) (pr₂ z))
  left-neutral-ptwise : (G H : Group 𝓤) →
    left-neutral (unit G , unit H) (ptwise-group-structure G H)
  left-neutral-ptwise G H x = ap2 _,_ (unit-left G (pr₁ x))
                                      (unit-left H (pr₂ x))

  right-neutral-ptwise : (G H : Group 𝓤) →
    right-neutral (unit G , unit H) (ptwise-group-structure G H)
  right-neutral-ptwise G H x = ap2 _,_ (unit-right G (pr₁ x))
                                       (unit-right H (pr₂ x))
  _⊗_ : (G H : Group 𝓤) → Group 𝓤
  G ⊗ H = (⟨ G ⟩ × ⟨ H ⟩) , (ptwise-group-structure G H
        , ×-is-set (group-is-set G) (group-is-set H)
        , (assoc-ptwise G H
        , ((unit G , unit H)
        , (left-neutral-ptwise G H
        , (right-neutral-ptwise G H
        , (λ {x → (inv G (pr₁ x) , inv H (pr₂ x))
               , ((ap2 _,_ (inv-left G (pr₁ x)) (inv-left H (pr₂ x)))
               ,  (ap2 _,_ (inv-right G (pr₁ x)) (inv-right H (pr₂ x))))}))))))

  ∣_×_ : {G H : Group 𝓤} → (A : Action G) → (B : Action H) →
    Action (G ⊗ H)
  ∣_×_ {G} {H} A B
    = (⟨ A ⟩ × ⟨ B ⟩)
      , ((ptwise (action-op G A) (action-op H B))
      , (×-is-set (carrier-is-set G A) (carrier-is-set H B))
      , (λ x y w → ap2 _,_ (action-assoc G A (pr₁ x) (pr₁ y) (pr₁ w))
                           (action-assoc H B (pr₂ x) (pr₂ y) (pr₂ w)))
      , λ w → ap2 _,_ (action-unit G A  (pr₁ w))
                      (action-unit H B (pr₂ w)))

  -- Every constant set has an indexed action:
  const-action : (G : Group 𝓤) → (A : Action G) →
    (⟨B⟩ : 𝓤 ̇) → is-set ⟨B⟩ → indexed-action G A
  const-action G A ⟨B⟩ ⟨B⟩set
    = (λ _ → ⟨B⟩)
    , (λ g b → b)
    , (λ a → ⟨B⟩set)
    , (λ g h b → NB: b since refl and refl)
    , λ b → NB: b since refl and refl


\end{code}
