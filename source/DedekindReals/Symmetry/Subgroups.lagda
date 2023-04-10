Andrew Sneap and Ohad Kammar

The Groups.Subgroups module uses univalence to define and induce
subgroups. That's fine, but since we only postulate univalence,
computation jams on the subgroup, which leads to more sophisticated
reasoning. In this module we reproduce this functionality while
retaining the computational 'content'.

\begin{code}
{-# OPTIONS -vimpossible:70 --without-K --exact-split --no-sized-types --no-guardedness --auto-inline --lossy-unification --allow-unsolved-metas #-} --safe

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
    open import DedekindReals.Symmetry.MetaRelations pe pt fe ⟨ G ⟩ (group-is-set G)

    is-unit-closed' : 𝓟 (𝓟 ⟨ G ⟩)
    is-unit-closed' = (λ 𝓐 → lift-pred 𝓐 (unit G))

    is-mult-closed' : 𝓟 (𝓟 ⟨ G ⟩)
    is-mult-closed' =
      (s𝓟∋Pi (Lift _ ⟨ G ⟩) (s𝓟∋Pi (Lift _ ⟨ G ⟩) λ ((𝓐 , lx) , ly) →
          𝓐 (lower lx) ⇒Ω
          𝓐 (lower ly) ⇒Ω
          𝓐 (lower lx ·⟨ G ⟩ (lower ly))))

    is-inv-closed' : 𝓟 (𝓟 ⟨ G ⟩)
    is-inv-closed' = s𝓟∋Pi (Lift _ ⟨ G ⟩) λ (𝓐 , lx) →
          𝓐 (lower lx) ⇒Ω 𝓐 (inv G (lower lx))

    is-group-closed' : 𝓟 (𝓟 ⟨ G ⟩)
    is-group-closed'
      = is-unit-closed'
      ∧ is-mult-closed'
      ∧ is-inv-closed'

    Subgroups' : 𝓤 ⁺ ̇
    Subgroups' = Σ 𝓐 ꞉ 𝓟 ⟨ G ⟩  , ⟨ is-group-closed' 𝓐 ⟩

    _∋_ : Subgroups' → 𝓟 ⟨ G ⟩
    _∋_ (𝓐 , closure ) = 𝓐

    group-closed' : (H : Subgroups') → ⟨ is-group-closed' ( H ∋_) ⟩
    group-closed' = pr₂
    unit-closed' : (H : Subgroups') → ⟨ is-unit-closed' ( H ∋_) ⟩
    unit-closed' H = pr₁ (group-closed' H)
    mult-closed' : (H : Subgroups') → ⟨ is-mult-closed' ( H ∋_) ⟩
    mult-closed' H = pr₁ (pr₂ (group-closed' H))
    inv-closed' : (H : Subgroups') → ⟨ is-inv-closed' ( H ∋_) ⟩
    inv-closed' H = pr₂ (pr₂ (group-closed' H))

    induced-group' : Subgroups' → Group 𝓤
    induced-group' ( 𝓐 , (unit-closed , mult-closed , inv-closed))
      = (Σ g ꞉ ⟨ G ⟩ , ⟨ 𝓐 g ⟩)
      , (λ (g , ⟨𝓐g⟩) (h , ⟨𝓐h⟩) → g ·⟨ G ⟩ h
           , mult-closed (lift _ g) (lift _ h) ⟨𝓐g⟩ ⟨𝓐h⟩)
      , sigma-is-set (group-is-set G) (λ g → props-are-sets (holds-is-prop (𝓐 g)))
      , (λ (x , x∈𝓐) (y , y∈𝓐) (z , z∈𝓐) → to-subtype-＝ (holds-is-prop ∘ 𝓐)
        (assoc G x y z))
      , (unit G , lower unit-closed)
      , (λ (x , x∈𝓐) → to-subtype-＝ (holds-is-prop ∘ 𝓐) (unit-left  G x))
      , (λ (x , x∈𝓐) → to-subtype-＝ (holds-is-prop ∘ 𝓐) (unit-right G x))
      , λ (g , g∈𝓐) →
        (inv G g , inv-closed (lift _ g) (g∈𝓐))
      , to-subtype-＝ (holds-is-prop ∘ 𝓐) (inv-left  G g)
      , to-subtype-＝ (holds-is-prop ∘ 𝓐) (inv-right G g)

    induced-action :
      (G-closed : Subgroups') → Action G → Action (induced-group' G-closed)
    induced-action (𝓐 , _) A
      = ⟨ A ⟩
      , (λ g a →  pr₁ g  ◂⟨ G ∣ A ⟩ a)
      , carrier-is-set G A
      , (λ g h x → action-assoc G A (pr₁ g) (pr₁ h) x)
      , action-unit G A

\end{code}
