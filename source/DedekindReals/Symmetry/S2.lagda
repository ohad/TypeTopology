Andrew Sneap and Ohad Kammar

Facts on the symmetric group over 2 elements

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

module DedekindReals.Symmetry.S2 {𝓤 : Universe} where

  data ⟨S₂⟩ : 𝓤 ̇  where
    id∈S₂  flip : ⟨S₂⟩

  _﹔_ : (x y : ⟨S₂⟩) → ⟨S₂⟩
  id∈S₂ ﹔ y = y
  flip ﹔ id∈S₂ = flip
  flip ﹔ flip = id∈S₂

  assoc-﹔ : associative _﹔_
  assoc-﹔ id∈S₂ id∈S₂ z = refl
  assoc-﹔ id∈S₂ flip id∈S₂ = refl
  assoc-﹔ id∈S₂ flip flip = refl
  assoc-﹔ flip id∈S₂ id∈S₂ = refl
  assoc-﹔ flip id∈S₂ flip = refl
  assoc-﹔ flip flip id∈S₂ = refl
  assoc-﹔ flip flip flip = refl

  left-neutral-﹔ : left-neutral id∈S₂ _﹔_
  left-neutral-﹔ x = refl

  right-neutral-﹔ : right-neutral id∈S₂ _﹔_
  right-neutral-﹔ id∈S₂ = refl
  right-neutral-﹔ flip = refl

  inv-S₂ : ⟨S₂⟩ → ⟨S₂⟩
  inv-S₂ x = x

  inv-left-﹔ : (x : ⟨S₂⟩) → (inv-S₂ x) ﹔ x ＝ id∈S₂
  inv-left-﹔ id∈S₂ = refl
  inv-left-﹔ flip = refl

  inv-right-﹔ : (x : ⟨S₂⟩) → x ﹔ (inv-S₂ x)  ＝ id∈S₂
  inv-right-﹔ id∈S₂ = refl
  inv-right-﹔ flip = refl


  S₂ : Group (𝓤)
  S₂ = ⟨S₂⟩ , (_﹔_
            , (λ {refl arefl → {!refl!}})
            , (assoc-﹔
            , (id∈S₂
            , left-neutral-﹔
            , right-neutral-﹔
            , λ x → inv-S₂ x
                  , inv-left-﹔ x
                  , inv-right-﹔ x
                  )))

  _◂⟨S₂∣_²⟩_ : (π : ⟨S₂⟩) → (a : 𝓤 ̇) → a × a → a × a
  id∈S₂ ◂⟨S₂∣ a ²⟩ xy = xy
  flip  ◂⟨S₂∣ a ²⟩ (x , y) = y , x

  assoc-⟨S₂∣_²⟩ : (a : 𝓤 ̇) → is-assoc S₂ _◂⟨S₂∣ a ²⟩_
  assoc-⟨S₂∣ a ²⟩ id∈S₂ h x = refl
  assoc-⟨S₂∣ a ²⟩ flip id∈S₂ x = refl
  assoc-⟨S₂∣ a ²⟩ flip flip x = refl

  unital-⟨S₂∣_²⟩ : (a : 𝓤 ̇) → is-unital S₂ _◂⟨S₂∣ a ²⟩_
  unital-⟨S₂∣ a ²⟩ x = refl

  Flip : (a : 𝓤 ̇) → (is-set a) → Action S₂
  Flip a aSet = (a × a) , (_◂⟨S₂∣ a ²⟩_)
         , ×-is-set aSet aSet
         , assoc-⟨S₂∣ a ²⟩
         , unital-⟨S₂∣ a ²⟩





\end{code}
