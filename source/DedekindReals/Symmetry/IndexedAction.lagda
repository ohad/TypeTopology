Andrew Sneap and Ohad Kammar

Will eventually migrate to Groups.IndexedAction

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

module DedekindReals.Symmetry.IndexedAction where

module GroupExplicit
      {𝓤 : Universe} (G : Group 𝓤) (A : Action G) where
  -- heterogeneous equality

  indexed-action-structure-over : (⟨B⟩ : ⟨ A ⟩ → 𝓤 ̇) → 𝓤 ̇
  indexed-action-structure-over ⟨B⟩ =
    (g : ⟨ G ⟩) → {x : ⟨ A ⟩} → ⟨B⟩ x → ⟨B⟩ (g ◂⟨ G ∣ A ⟩ x)

  indexed-action-axioms : (⟨B⟩ : ⟨ A ⟩ → 𝓤 ̇) →
    indexed-action-structure-over ⟨B⟩ → 𝓤 ⁺ ̇
  indexed-action-axioms ⟨B⟩ _·_ =
      ((a : ⟨ A ⟩) → is-set (⟨B⟩ a))
    × ((g h : ⟨ G ⟩){a : ⟨ A ⟩}(b : ⟨B⟩ a) →
        ((g ·⟨ G ⟩ h) · b) ≈ (g · (g · b))  )
    × ({a : ⟨ A ⟩} → (b : ⟨B⟩ a) → (unit G · b) ≈ b)

  indexed-action-over : (⟨B⟩ : ⟨ A ⟩ → 𝓤 ̇) → 𝓤 ⁺ ̇
  indexed-action-over ⟨B⟩ = Σ (indexed-action-axioms ⟨B⟩)

  indexed-action : 𝓤 ⁺ ̇
  indexed-action = Σ indexed-action-over

  indexed-action-op : ((⟨B⟩ , structure) : indexed-action) →
    indexed-action-structure-over ⟨B⟩
  indexed-action-op (⟨B⟩ , _◃⟨B⟩_ , axioms) = _◃⟨B⟩_

  -- The point: an indexed action is an action on the Σ-type that
  -- lives over A

  as-action : {⟨B⟩ : ⟨ A ⟩ → 𝓤 ̇ } →
    indexed-action-over ⟨B⟩ → Action-structure G (Σ ⟨B⟩)
  as-action (_·_ , axioms)
    = (λ g → λ { (a , b) → (g ◂⟨ G ∣ A ⟩ a)  , (g · b)})
    , {!!} -- lots of HoTT fun to be had here

  inv-act-inverse-left : (g : ⟨ G ⟩) → (a : ⟨ A ⟩) →
    (inv G g) ◂⟨ G ∣ A ⟩ (g ◂⟨ G ∣ A ⟩ a) ＝ a
  inv-act-inverse-left g a =
     ((g ⁱⁿᵛ) · (g · a)    ＝⟨ action-assoc G A (g ⁱⁿᵛ) g a  ⁻¹ ⟩
     ((g ⁱⁿᵛ) ·⟨ G ⟩ g) · a ＝⟨ ap (_· a) (inv-left G g) ⟩
     (unit G) · a          ＝⟨ action-unit G A a ⟩
     a ∎)
    where _ⁱⁿᵛ : ⟨ G ⟩ → ⟨ G ⟩
          _ⁱⁿᵛ = inv G
          _·_ : ⟨ G ⟩ → ⟨ A ⟩ → ⟨ A ⟩
          _·_ = action-op G A

  inv-act-inverse-right : (g : ⟨ G ⟩) → (a : ⟨ A ⟩) →
    g ◂⟨ G ∣ A ⟩ ((inv G g) ◂⟨ G ∣ A ⟩ a) ＝ a
  inv-act-inverse-right g a = {!!} -- fun to be had here

open GroupExplicit public


⟨_∣_⟩-indexed-action : (G : Group 𝓤) → (A : Action G) → 𝓤 ⁺ ̇
⟨ A ∣ G ⟩-indexed-action = Σ (indexed-action-over A G)

⟨_⟩-indexed-action : {G : Group 𝓤} → (A : Action G) → 𝓤 ⁺ ̇
⟨_⟩-indexed-action {G = G} A = ⟨ G ∣ A ⟩-indexed-action

indexed-action-op-syntax : (G : Group 𝓤) (A : Action G) →
    ((⟨B⟩ , rest) : ⟨ G ∣ A ⟩-indexed-action) →
    indexed-action-structure-over G A  ⟨B⟩
indexed-action-op-syntax {𝓤} G A B = indexed-action-op G A B
syntax indexed-action-op-syntax G A B g y = g ◃⟨ G ∣ A ∣ B ⟩ y


\end{code}
